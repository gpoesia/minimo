use std::option::Option;
use std::sync::Arc;
use std::collections::hash_set::{HashSet, Iter};
use std::collections::hash_map::HashMap;
use std::io;
use std::path::Path;

use num_rational::Rational64;
use smallset::SmallSet;

use super::term::{Context, Term, Definition, is_parameter_name, ProofResultNames};
use super::proof::{Proof, ProofError, ProofState, ProofAction};

pub type Scope = SmallSet<[String; 8]>;

