mod proof;
mod checker;
mod containers;
mod view;
mod polyfill;
mod solver;
mod trace;
mod display;
mod parser;
mod error;
mod matching;

use std::io;
use std::io::BufRead;
use std::process::{ExitCode, Command, Stdio, ChildStdout};
use std::collections::HashMap;
use std::fs;

use clap::{command, Parser};

use crate::error::Error;
use crate::parser::{parse_program, parse_term, parse_trace_event};
use crate::trace::{TraceValidator};

use crate::checker::{Program, Term, RuleId};

#[derive(Parser, Debug)]
#[command(long_about = None)]
struct Args {
    /// Prolog source file
    source: String,

    /// The main goal to be solved
    goal: String,

    /// Path to the SWI-Prolog binary
    #[clap(long, value_parser, num_args = 0.., value_delimiter = ' ', default_value = "swipl")]
    swipl_bin: String,

    /// Path to the meta interpreter
    #[clap(long, value_parser, num_args = 0.., value_delimiter = ' ', default_value = "prolog/meta.pl")]
    mi_path: String,

    /// Enable debug mode
    #[arg(long, default_value_t = false)]
    debug: bool,

    /// Only print out the parsed Prolog program and the command to be run
    #[arg(long, default_value_t = false)]
    dry: bool,
}

fn validate_trace(args: &Args, program: &Program, line_map: &HashMap<usize, RuleId>, goal: &Term, swipl_stdout: &mut ChildStdout) -> Result<(), Error> {
    let mut validator = TraceValidator::new(program);
    let mut last_event_id = 0;

    // For each line, check if it is a trace event;
    // if so, parse it and send it to the validator
    for line in io::BufReader::new(swipl_stdout).lines() {
        let line_str = line?;
        
        if args.debug {
            eprintln!("[debug] ==============================================================");
            eprintln!("[debug] event {}", &line_str);
        }

        match parse_trace_event(&line_str, &line_map) {
            Ok(event) => {
                last_event_id = event.id;
                let thm = validator.process_event(&program, &event, args.debug)?;
                if args.debug {
                    eprintln!("[debug] validated: {}", thm.stmt);
                }
            }
            Err(err) => {
                Err(Error::Other(format!("[error] failed to parse trace event \"{}\": {}", &line_str, err)))?
            }
        }
    }

    // Verify that the goal term is indeed proved
    if let Ok(thm) = validator.get_theorem(&program, last_event_id) {
        if thm.stmt.eq(&goal) {
            println!("validated goal: {}", &goal);
            Ok(())
        } else {
            Err(Error::Other(format!("unmatched final goal: expecting `{}`, got `{}`", &goal, &thm.stmt)))
        }
    } else {
        Err(Error::Other(format!("failed to validate a proof of the goal: {}", &goal)))
    }
}

fn main_args(mut args: Args) -> Result<(), Error> {
    // Parse the source file
    let source = fs::read_to_string(&args.source)?;
    let (program, line_map) = parse_program(source, &args.source)?;

    // Parse the goal term
    let goal = parse_term(&args.goal)?;

    if args.debug || args.dry {
        eprintln!("[debug] parsed program:");
        for rule in &program.rules {
            eprintln!("[debug]   {}", rule);
        }
    }

    // Run the main goal in swipl with the meta interpreter
    let mut swipl_cmd = Command::new(&args.swipl_bin);
    swipl_cmd
        .arg("-s").arg(&args.mi_path)
        .arg("-s").arg(&args.source)
        .arg("-g").arg(format!("prove({})", &args.goal))
        .arg("-g").arg("halt")
        .stdout(Stdio::piped());

    if args.debug || args.dry {
        eprintln!("[debug] running swipl command: {:?}", &swipl_cmd);
    }

    if args.dry {
        return Ok(());
    }

    let mut swipl = swipl_cmd.spawn()?;
    let mut swipl_stdout = swipl.stdout.take()
        .ok_or(Error::Other("failed to open swipl stdout".to_string()))?;
    
    match validate_trace(&args, &program, &line_map, &goal, &mut swipl_stdout) {
        Ok(()) => {
            if !swipl.wait()?.success() {
                Err(Error::Other("swipl exited with failure".to_string()))
            } else {
                Ok(())
            }
        }
        Err(err) => {
            // Consume and throw away rest of the stdout,
            // so that swipl doesn't block
            io::copy(&mut swipl_stdout, &mut io::sink())?;
            
            if !swipl.wait()?.success() {
                eprintln!("[error] {}", err);
                Err(Error::Other("swipl exited with failure".to_string()))
            } else {
                eprintln!("swipl exited successfully");
                Err(err)
            }
        }
    }
}

pub fn main() -> ExitCode {
    match main_args(Args::parse()) {
        Ok(..) => ExitCode::from(0),
        Err(err) => {
            eprintln!("{}", err);
            ExitCode::from(1)
        }
    }
}
