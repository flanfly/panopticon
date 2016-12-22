/*
 * Panopticon - A libre disassembler
 * Copyright (C) 2015, 2016  Panopticon authors
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

//! Loader for 32 and 64-bit ELF files.

use std::io::{Seek,SeekFrom,Read,Cursor};
use std::fs::File;
use std::path::Path;
use std::borrow::Cow;
use std::ops::Range;
use std::collections::HashMap;

use graph_algos::MutableGraphTrait;
use uuid::Uuid;
use goblin::elf::{self,program_header};

use {
    Program,
    CallTarget,
    Project,
    Layer,
    Region,
    Bound,
    Rvalue,
    Result,
};

/// CPU the ELF file is intended for.
#[derive(Clone,Copy,Debug)]
pub enum Machine {
    /// 8-bit AVR
    Avr,
    /// AMD64
    Amd64,
    /// Intel x86
    Ia32,
}

/// Initial ELF identifier section
#[derive(Debug)]
pub struct Ident {
    /// ELF magic number. Must be `ELF\177`
    pub magic: [u8; 4],
    /// Whenever ELF32 or ELF64
    pub class: u8,
    /// Endianess of the CPU
    pub data: u8,
    /// ELF version. Must be 0.
    pub version: usize,
    /// Application Binary Interface of the code inside. CPU depend.
    pub abi: u8,
    /// Version of the Application Binary Interface.
    pub abi_ver: usize,
    /// Padding bytes. Must be 0.
    pub pad: [u8; 7],
}

const EI_CLASS: usize = 4;
const EI_DATA: usize = 5;
const EI_VERSION: usize = 6;
const EI_OSABI: usize = 7;
const EI_ABIVERSION: usize = 8;
const EI_PAD: usize = 9;

impl Ident {
    /// Reads and sanity checks a ELF identifier section from `R`.
    pub fn read<R: Read>(strm: &mut R) -> Result<Ident> {
        let mut e_ident = [0u8; 16];

        if let Err(_) = strm.read(&mut e_ident) {
            return Err("Failed to read ident".into());
        }

        if e_ident[0..4] != [0x7f, 0x45, 0x4c, 0x46] {
            return Err("Invalid magic number".into());
        }

        if e_ident[EI_PAD..16].iter().any(|&x| x != 0) {
            return Err("Invalid padding".into());
        }

        if e_ident[EI_VERSION] != 1 {
            return Err("Invalid ELF version".into());
        }

        Ok(Ident{
            magic: [e_ident[0],e_ident[1],e_ident[2],e_ident[3]],
            class: e_ident[EI_CLASS],
            data: e_ident[EI_DATA],
            version: e_ident[EI_VERSION] as usize,
            abi: e_ident[EI_OSABI],
            abi_ver: e_ident[EI_ABIVERSION] as usize,
            pad: [
                  e_ident[EI_PAD+0],
                  e_ident[EI_PAD+1],
                  e_ident[EI_PAD+2],
                  e_ident[EI_PAD+3],
                  e_ident[EI_PAD+4],
                  e_ident[EI_PAD+5],
                  e_ident[EI_PAD+6]
            ],
        })
    }
}

macro_rules! load_impl {
    ($elf:expr, $fd:expr, $interp:expr, $entry:expr, $reg:expr) => {{
        info!("Soname: {:?} with interpreter: {:?}", $elf.soname, $elf.interpreter);
        info!("Libs: {:?}", $elf.libraries);

        for ph in $elf.program_headers {
            if ph.p_type == program_header::PT_LOAD {
                let mut buf = vec![0u8; ph.p_filesz as usize];

                info!("Load ELF {} bytes segment to {:#x}",ph.p_filesz,ph.p_vaddr);

                if $fd.seek(SeekFrom::Start(ph.p_offset as u64)).ok() == Some(ph.p_offset as u64) {
                    try!($fd.read_exact(&mut buf));
                    $reg.cover(Bound::new(ph.p_vaddr as u64, (ph.p_vaddr + ph.p_filesz) as u64), Layer::wrap(buf));
                } else {
                    return Err("Failed to read segment".into())
                }
            }
        }

        for rel in $elf.rela.iter() {
            info!("rela: {:?}",rel);
        }

        for rel in $elf.pltrela.iter() {
            info!("pltrela: {:?}",rel);
        }

        ($elf.entry,$elf.interpreter)
    }}
}

/// Load an ELF file from disk and creates a `Project` from it. Returns the `Project` instance and
/// the CPU its intended for.
pub fn load(p: &Path) -> Result<(Project,HashMap<Range<u64>,Cow<'static,str>>,Machine,Vec<(Uuid,u64,Cow<'static,str>,Option<Cow<'static,str>>)>)> {
    let mut fd = try!(File::open(p));
    // it seems more efficient to load all bytes into in-memory buffer and parse those...
    // for larger binaries we should perhaps let the elf parser read from the fd though
    let mut bytes = Vec::new();
    try!(fd.read_to_end(&mut bytes));
    let mut cursor = Cursor::new(&bytes);
    let binary = try!(elf::Elf::parse(&mut cursor));
    let entry = binary.entry;
    let (machine, mut reg) = match binary.header.e_machine() {
        elf::header::EM_X86_64 => {
            let reg = Region::undefined("RAM".to_string(), 0xFFFF_FFFF_FFFF_FFFF);
            (Machine::Amd64,reg)
        },
        elf::header::EM_386 => {
            let reg = Region::undefined("RAM".to_string(), 0x1_0000_0000);
            (Machine::Ia32,reg)
        },
        elf::header::EM_AVR => {
            let reg = Region::undefined("Flash".to_string(), 0x2_0000);
            (Machine::Avr,reg)
        },
        machine => return Err(format!("Unsupported machine: {}", machine).into())
    };

    for ph in binary.program_headers {
        if ph.p_type() == program_header::PT_LOAD {
            let mut buf = vec![0u8; ph.p_filesz() as usize];

            debug!("Load ELF {} bytes segment to {:#x}",ph.p_filesz(),ph.p_vaddr());

            if cursor.seek(SeekFrom::Start(ph.p_offset() as u64)).ok() == Some(ph.p_offset() as u64) {
                try!(cursor.read_exact(&mut buf));
                reg.cover(Bound::new(ph.p_vaddr() as u64, (ph.p_vaddr() + ph.p_filesz()) as u64), Layer::wrap(buf));
            } else {
                return Err("Failed to read segment".into())
            }
        }
    }

    let name =
        if let Some(soname) = binary.soname {
            soname.to_owned()
        } else {
            p.file_name()
                .map(|x| x.to_string_lossy().to_string())
                .unwrap_or("(encoding error)".to_string())
        };

    debug!("interpreter: {:?}", &binary.interpreter);

    let mut prog = Program::new("prog0".into());
    let mut proj = Project::new(name.clone(),reg);
    let mut todo = vec![];
    let mut symtbl = HashMap::<Range<u64>,Cow<'static,str>>::new();

    let dynstrtab = binary.dynstrtab;
    let dynsyms = binary.dynsyms.into_iter().collect::<Vec<_>>();
    for sym in dynsyms.iter() {
        let name = dynstrtab[sym.st_name() as usize].to_string();
        let addr = sym.st_value();
        debug!("{} @ 0x{:x}: {:?}", name, addr, sym);
        if sym.is_function() {
            if sym.is_import() {
                symtbl.insert((addr..addr+8),name.into());
            } else {
                todo.push((prog.uuid.clone(),addr,"RAM".into(),Some(name.into())));
            }
        }
    }
    for rel in binary.pltrela {
        debug!("rela: {:?}",rel);
        let sym = dynsyms[(*rel).r_sym() as usize].clone();
        let name = dynstrtab[sym.st_name() as usize].to_string();
        let addr = rel.r_offset();
        debug!("\tval: 0x{:x} = {} + {}",addr,name,rel.r_addend());
        symtbl.insert((addr..addr+8),name.into());
    }

    proj.comments.insert(("base".to_string(),entry),"main".to_string());
    todo.push((prog.uuid.clone(),entry,"RAM".into(),Some("main".into())));
    proj.code.push(prog);

    Ok((proj,symtbl,machine,todo))
}
