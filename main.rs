mod proof;
mod checker;
mod containers;
mod view;
mod polyfill;

use crate::containers::StringHashMap;
use crate::checker::*;

pub fn main() {
    let program = ProgramX::new(vec![
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("a"), TermX::constant("b") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("b"), TermX::constant("c") ]), vec![]),
        RuleX::new(TermX::app_str("connect", vec![ TermX::var_str("X"), TermX::var_str("Y") ]), vec![
            TermX::app_str("edge", vec![ TermX::var_str("X"), TermX::var_str("Y") ]),
        ]),
        RuleX::new(TermX::app_str("connect", vec![ TermX::var_str("X"), TermX::var_str("Z") ]), vec![
            TermX::app_str("edge", vec![ TermX::var_str("X"), TermX::var_str("Y") ]),
            TermX::app_str("connect", vec![ TermX::var_str("Y"), TermX::var_str("Z") ]),
        ]),
    ]);

    let empty_subst = Subst(StringHashMap::new());
    let mut subst1 = Subst(StringHashMap::new());
    let mut subst2 = Subst(StringHashMap::new());

    subst1.0.insert("X".to_string(), TermX::constant("b"));
    subst1.0.insert("Y".to_string(), TermX::constant("c"));

    subst2.0.insert("X".to_string(), TermX::constant("a"));
    subst2.0.insert("Y".to_string(), TermX::constant("b"));
    subst2.0.insert("Z".to_string(), TermX::constant("c"));
    
    let edge_ab = Theorem::apply_rule(&program, 0, &empty_subst, vec![]);
    let edge_bc = Theorem::apply_rule(&program, 1, &empty_subst, vec![]);

    if let (Some(edge_ab), Some(edge_bc)) = (edge_ab, edge_bc) {
        if let Some(connect_bc) = Theorem::apply_rule(&program, 2, &subst1, vec![ edge_bc ]) {
            if let Some(connect_ac) = Theorem::apply_rule(&program, 3, &subst2, vec![ edge_ab, connect_bc ]) {
                println!("thm: {:?}", connect_ac.stmt);
            } else {
                println!("failed connect_ac");
            }
        } else {
            println!("failed connect_bc");
        }
    } else {
        println!("failed edge");
    }
}
