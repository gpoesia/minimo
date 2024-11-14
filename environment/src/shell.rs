use std::sync::Arc;
use colored::Colorize;

use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
use rustyline::Editor;

use peano::universe::{Derivation, Term, load_context};

pub struct Shell {
    universe: Derivation,
}

impl Shell {
    pub fn new() -> Shell {
        Shell { universe: Derivation::new() }
    }

    pub fn load_path(&mut self, path: &str) -> Result<usize, String> {
        match load_context(path) {
            Err(err) => Err(err.to_string()),
            Ok(ctx) => {
                self.universe.incorporate(&ctx);
                Ok(ctx.insertion_order.len())
            }
        }
    }

    pub fn verify_all(&self) -> Result<(), String> {
        let mut successes = 0;
        let mut failures = 0;
        for name in self.universe.proofs() {
            if self.verify(name).is_ok() {
                successes += 1;
            } else {
                failures += 1;
            }
        }

        let total = successes + failures;
        if total == 0 {
            println!("{}", "No proofs found.".yellow());
        } else {
            println!("\nChecked {} proofs(s){}{}.",
                     total,
                     if successes > 0 { format!(", {}", format!("{} succeeded", successes).green()) }
                     else { format!("") },
                     if failures > 0 { format!(", {}", format!("{} failed", failures).red()) }
                     else { format!("") },
            );
        }

        if failures > 0 {
            return Err(String::from("At least one verification failed."));
        }
        Ok(())
    }

    pub fn verify(&self, proof_name: &String) -> Result<(), String> {
        print!("Verifying {}... ", proof_name);

        match self.universe.execute_proof(proof_name) {
            Ok(_) => {
                println!("{}", "ok".green());
                Ok(())
            },
            Err(e) => {
                println!("{}: {}", "error".red(), e);
                Err(e.to_string())
            }
        }
    }

    pub fn is_inhabited(&self, type_str: &str) -> Result<Option<String>, String> {
        match type_str.parse::<Term>() {
            Err(e) => Err(e.to_string()),
            Ok(t) => Ok(self.universe.inhabited(&Arc::new(t))),
        }
    }

    pub fn apply(&mut self, action: &str, rl: &mut Editor<(), DefaultHistory>) -> () {
        let defs = self.universe.application_results(&action.to_string(), &None, &vec![]);

        if defs.len() == 0 {
            println!("No results.");
        } else {
            for (i, def) in defs.iter().enumerate() {
                println!("{} - {} : {}",
                         i,
                         if let Some(v) = &def.value { v.to_string() } else { String::from("_") },
                         def.dtype);
            }

            match rl.readline("  Result to add: ") {
                Ok(line) => {
                    match line.parse::<usize>() {
                        Ok(idx) if idx < defs.len() => {
                            self.universe.define(String::from("r"), defs[idx].clone(), true);
                        },
                        _ => { println!("Nothing added.") }
                    }
                }
                _ => {}
            }
        }
    }

    pub fn repl(&mut self) {
        let mut rl = Editor::<(), DefaultHistory>::new().unwrap();

        loop {
            match rl.readline("> ") {
                Ok(line) => {
                    if line.starts_with("!") {
                        let line = line[1..].trim();
                        let (command, args) = match line.split_once(" ") {
                            Some((c, a)) => (c, a),
                            None => (line, ""),
                        };

                        if command == "context" {
                            println!("{}", self.universe.dump_context());
                        } else if command == "load" {
                            match self.load_path(args) {
                                Ok(n) => println!("{} definitions loaded.", n),
                                Err(err) => println!("Error loading {}: {}", args, err)
                            }
                        } else if command == "apply" {
                            self.apply(args, &mut rl);
                            println!("{}", self.universe.dump_context());
                        } else if command == "inhabited" {
                            match self.is_inhabited(&args) {
                                Err(err) => println!("Error: {}", err),
                                Ok(None) => println!("no"),
                                Ok(Some(witness)) => println!("yes ({})", witness),
                            }
                        } else if command == "actions" {
                            let actions: Vec<&String> = self.universe.actions().collect();
                            println!("{}", actions.iter().map(|x| x.as_str()).collect::<Vec<&str>>().join(" "));
                        } else {
                            println!("Unknown command {}", command);
                        }
                    }

                    rl.add_history_entry(line).unwrap();
                },
                Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => {
                    break;
                },
                Err(e) => {
                    println!("Error: {}", e);
                }
            }
        }
    }
}
