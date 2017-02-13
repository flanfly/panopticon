/*
 * Panopticon - A libre disassembler
 * Copyright (C) 2015  Panopticon authors
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

#[macro_use]
extern crate log;
extern crate env_logger;

extern crate panopticon;
extern crate qmlrs;
extern crate libc;
extern crate graph_algos;
extern crate uuid;
extern crate rustc_serialize;
extern crate cassowary;
extern crate tempdir;
extern crate byteorder;
extern crate chrono;
extern crate chrono_humanize;
extern crate goblin;
extern crate rayon;
extern crate parking_lot;

#[cfg(unix)]
extern crate xdg;

#[macro_use]
extern crate lazy_static;

mod controller;
mod project;
mod function;
mod sugiyama;
mod paths;
mod pipeline;

use qmlrs::{Variant};

use panopticon::result;
use panopticon::result::Result;

use controller::{
    create_singleton,
    Controller,
};

use paths::find_data_file;

fn main() {
    use std::path::Path;
    use std::env;

    env_logger::init().unwrap();
    rayon::initialize(
        rayon::Configuration::new().
        set_num_threads(1)
    ).unwrap();

    if cfg!(unix) {
        // workaround bug #165
        env::set_var("UBUNTU_MENUPROXY","");

        // workaround bug #183
        env::set_var("QT_QPA_PLATFORMTHEME","");
    }

    let title_screen = find_data_file(&Path::new("qml").join("Title.qml"));
    let main_window = find_data_file(&Path::new("qml").join("Window.qml"));

    match (title_screen,main_window) {
        (Ok(Some(title)),Ok(Some(window))) => {
            qmlrs::register_singleton_type(&"Panopticon",1,0,&"Panopticon",create_singleton);

            {
                let mut engine = qmlrs::Engine::new("Panopticon");
                engine.load_local_file(&format!("{}",title.display()));
                engine.exec();
            }

            if Controller::request().ok().unwrap_or(None).is_some() {
                let mut engine = qmlrs::Engine::new("Panopticon");
                engine.load_local_file(&format!("{}",window.display()));
                engine.exec();
            }
        },
        _ => {
            println!("Failed to open the QML files")
        },
    }
}
