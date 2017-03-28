#[macro_use]
extern crate nom;
#[macro_use]
extern crate abomonation_derive;
extern crate abomonation;
extern crate timely;
extern crate differential_dataflow;

use timely::dataflow::*;
use timely::dataflow::operators::*;

use differential_dataflow::Collection;
use differential_dataflow::operators::*;
use differential_dataflow::lattice::Lattice;
use differential_dataflow::operators::Join;
use differential_dataflow::operators::Group;

use nom::{IResult, space, alpha, digit, Err};

use std::time::Instant;
use std::str;
use std::str::FromStr;
use std::fmt::{self, Formatter, Display};
use std::fs::File;
use std::io::BufReader;
use std::io::prelude::*;
use std::error::Error;
use std::collections::HashMap;
use std::collections::HashSet;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::cell::RefCell;
use std::mem;

//////////////////////////////
//                          //
//       TYPES GRAPH        //
//                          //
//////////////////////////////

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {    
    Attribute  (Attribute),
    Literal    (Literal),
    Label      (String),
    Add        (Box<Expr>, Box<Expr>),
    Sub        (Box<Expr>, Box<Expr>),
    Mul        (Box<Expr>, Box<Expr>),
    Div        (Box<Expr>, Box<Expr>),
    Modulo     (Box<Expr>, Box<Expr>),
    Equal      (Box<Expr>, Box<Expr>),
    NotEqual   (Box<Expr>, Box<Expr>),
    Greater    (Box<Expr>, Box<Expr>),
    GreaterEq  (Box<Expr>, Box<Expr>),
    Smaller    (Box<Expr>, Box<Expr>),
    SmallerEq  (Box<Expr>, Box<Expr>),
    Like       (Box<Expr>, Box<Expr>),
    And        (Box<Expr>, Box<Expr>),
    Or         (Box<Expr>, Box<Expr>),
    Not        (Box<Expr>),
    BuiltIn    (String, BuiltIn),
}


#[derive(Debug, PartialEq, Clone)]
pub struct Attribute { 
    name: String,
    field: String,
}


#[derive(Debug, Clone, PartialEq)]
pub struct Node{
    id: i32,
    label: Vec<String>,
    attribute_values: HashMap<String, Literal>,
}


#[derive(Debug, PartialEq)]
pub struct GraphEdge{
    source: i32,
    target: i32,
    label: String,    
    attribute_values: HashMap<String, Literal>,
}


#[derive(Debug)]
pub struct Graph{
    nodes: Vec <Node>,
    edges: Vec <GraphEdge>,
}

#[derive(PartialEq, Clone, Abomonation)]
pub enum Literal {
  Str(String),
  Float(f32),
  Boolean(bool),
}

impl fmt::Debug for Literal
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result
    {
        match *self {
            Literal::Str(ref value) => write!(f,"{}",value),
            Literal::Float(ref value) => write!(f,"{}",value),
            Literal::Boolean(ref value) => write!(f,"{}",value)
        }
    }
}

impl Literal {
    fn add(&self, other: Literal) -> Literal {
        match other {
            Literal::Float(value) => {
                match *self {
                    Literal::Float(ownvalue) => Literal::Float(value + ownvalue),
                    _ => panic!("Addition with non arithmetic value")
                }
            },
             _ => panic!("Addition with non arithmetic value") 
        }
    }

    fn sub(&self, other: Literal) -> Literal {
        match other {
            Literal::Float(value) => {
                match *self {
                    Literal::Float(ownvalue) => Literal::Float(value - ownvalue),
                    _ => panic!("Substraction with non arithmetic value")
                }
            },
             _ => panic!("Substraction with non arithmetic value") 
        }
    }

    fn mul(&self, other: Literal) -> Literal {
        match other {
            Literal::Float(value) => {
                match *self {
                    Literal::Float(ownvalue) => Literal::Float(value * ownvalue),
                    _ => panic!("Mulitplication with non arithmetic value")
                }
            },
             _ => panic!("Mulitplication with non arithmetic value") 
        }
    }

    fn div(&self, other: Literal) -> Literal {
        match other {
            Literal::Float(value) => {
                match *self {
                    Literal::Float(ownvalue) => Literal::Float(value / ownvalue),
                    _ => panic!("Division with non arithmetic value")
                }
            },
             _ => panic!("Division with non arithmetic value") 
        }
    }

    fn modulo(&self, other: Literal) -> Literal {
        match other {
            Literal::Float(value) => {
                match *self {
                    Literal::Float(ownvalue) => Literal::Float(value % ownvalue),
                    _ => panic!("Modulo with non arithmetic value")
                }
            },
             _ => panic!("Modulo with non arithmetic value") 
        }
    }

    fn greater(&self, other: Literal) -> Literal {
        match other {
            Literal::Float(value) => {
                match *self {
                    Literal::Float(ownvalue) => Literal::Boolean(value < ownvalue),
                    _ => panic!("Greater with own non arithmetic value")
                }
            },
             _ => panic!("Greater with other non arithmetic value") 
        }
    }

    fn greater_eq(&self, other: Literal) -> Literal {
        match other {
            Literal::Float(value) => {
                match *self {
                    Literal::Float(ownvalue) => Literal::Boolean(value <= ownvalue),
                    _ => panic!("GreaterEq with non arithmetic value")
                }
            },
             _ => panic!("GreaterEq with non arithmetic value") 
        }
    }

    fn smaller(&self, other: Literal) -> Literal {
        match other {
            Literal::Float(value) => {
                match *self {
                    Literal::Float(ownvalue) => Literal::Boolean(value > ownvalue),
                    _ => panic!("Smaller with non arithmetic value")
                }
            },
             _ => panic!("Smaller with non arithmetic value") 
        }
    }

    fn smaller_eq(&self, other: Literal) -> Literal {
        match other {
            Literal::Float(value) => {
                match *self {
                    Literal::Float(ownvalue) => Literal::Boolean(value >= ownvalue),
                    _ => panic!("SmallerEq with non arithmetic value")
                }
            },
             _ => panic!("SmallerEq with non arithmetic value") 
        }
    }

    fn and(&self, other: Literal) -> Literal {
        match other {
            Literal::Boolean(value) => {
                match *self {
                    Literal::Boolean(ownvalue) => Literal::Boolean(value && ownvalue),
                    _ => panic!("And with non boolean value")
                }
            },
             _ => panic!("And with non boolean value") 
        }
    }

    fn or(&self, other: Literal) -> Literal {
        match other {
            Literal::Boolean(value) => {
                match *self {
                    Literal::Boolean(ownvalue) => Literal::Boolean(value || ownvalue),
                    _ => panic!("Or with non boolean value")
                }
            },
             _ => panic!("Or with non boolean value") 
        }
    }

    fn not(&self) -> Literal {

        match *self {
            Literal::Boolean(ownvalue) => Literal::Boolean(!ownvalue),
            _ => panic!("Not with non boolean value")
        }
    }

    fn contains(&self, other: Literal) -> Literal {
        match other {
            Literal::Str(ref value) => {
                match *self {
                    Literal::Str(ref ownvalue) => Literal::Boolean(ownvalue.contains(value)),
                    _ => panic!("Contains with non String value")
                }
            },
             _ => panic!("Contains with non String value") 
        }
    }
    fn as_float(&self) -> f32{
        match *self {
            Literal::Float(value) => value,
            _ => panic!("No Float value found")
        }
    }
}
//////////////////////////////
//                          //
//      TYPES QUERY         //
//                          //
//////////////////////////////

#[derive(Debug)]
pub struct Query {
    select: Vec<SelectElem>,
    vvhere: Vec<Constraint>,
    paths: Option<Vec<(String, Connection)> >,
    sol_mod: Option<(GroupBy, OrderBy, (i32, i32))>,
}

#[derive(Debug,PartialEq)]
pub enum SelectElem {
    Star,
    Aggregation(Aggregation),
    Attribute(Attribute),
}

#[derive(Debug,PartialEq)]
pub enum Constraint{
    Expr(Expr),
    PathPattern(Vec<Connection>),
}


#[derive(Debug,PartialEq, Clone)]
pub struct Connection {
    source: Vertex,
    target: Vertex,
    edge: Edge,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Edge {
    name: String,
    inverted: bool,
    constraints: Vec<Expr>,
}

#[derive(Debug,PartialEq,Clone)]
pub struct Vertex {
    name: String,
    anonymous: bool,
    constraints: Vec<Expr>,
}

#[allow(dead_code)]
pub struct PathExpr {
    source: Vertex,
    target: Vertex,
    edge: Edge,
    min_occ: i32,
    max_occ: i32,
}

#[derive(Debug)]
pub enum QueryConnection {
    Edge(Edge),
    Path(RegularPath),
}

#[derive(Debug)]
pub struct RepeatablePath {
    min: i32,
    max: i32,
    path: RegularPath,
}


#[derive(Debug)]
pub enum RegularPath {
    Predefined(String),
    Alternative(Box<RegularPath>,Box<RegularPath>),
    Repeatable(Box<RepeatablePath>),
    Inverted(Box<RegularPath>),
}

#[derive(Debug)]
pub struct GroupBy {
    group: Vec<Expr>,
}

#[derive(Debug)]
pub struct OrderBy {
    order: Vec<OrderTerm>,
}

#[derive(Debug)]
pub struct OrderTerm {
    expr: Expr,
    asc: bool,
}

#[derive(Debug)]
pub enum Type {
    Str,
    Float,
    Boolean,
    Integer,
}

#[derive(Debug)]
pub enum QueryVariable {
    Vertex,
    Edge,
    Path,
    Expression,
}

#[derive(Debug,Clone)]
pub enum Oper {
    Add,
    Sub,
    Mul,
    Div,
    Modulo,
    Equal,
    NotEqual,
    Greater,
    GreaterEq,
    Smaller,
    SmallerEq,
    Like,
    And,
    Or,
    Not, 
}


#[derive(Debug, PartialEq, Clone)]
pub enum BuiltIn {
    Id,
    InDegree,
    Has(String),
    HasLabel(String),
    OutDegree,
    Labels,
    Label,
}

#[derive(Debug, PartialEq)]
pub enum Aggregation {
    Count(Attribute),
    Min(Attribute),
    Max(Attribute),
    Sum(Attribute),
    Avg(Attribute),
}



//////////////////////////////
//                          //
//      TYPES EVALUATION    //
//                          //
//////////////////////////////

#[derive(Debug)]
struct PhyPlan{
    name: Vec<String>,
    left: String,
    right: String,
    join_id: usize,
    join: bool,
    filter_id: usize,
    constraints: Vec<Expr>,
}

#[derive(Debug, Clone, Abomonation, Default)]
pub struct DifferentialVertex{
    id: i32,
    label: Vec<String>,
    attribute_values: Vec<(String, Literal)>,
}

impl DifferentialVertex{
    fn get(&self, attribute: &String) -> Option<&Literal>{        
        let mut result = None;
        for pair in &self.attribute_values {
            let &(ref key, ref value) = pair;
            if key.clone() == attribute.clone(){
                result = Some(value);
            }
        }
        (result)
    }
}

impl From<Node> for DifferentialVertex {
    fn from(data: Node) -> Self {
        DifferentialVertex {
            id: data.id,
            label: data.label,
            attribute_values: data.attribute_values.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
        }
    }
}

impl From<DifferentialVertex> for Node {
    fn from(data: DifferentialVertex) -> Self {
        let mut map = HashMap::new();
        for pair in data.attribute_values {
            let (key, value) = pair;
            map.insert(key, value);
        }
        Node {
            id: data.id,
            label: data.label,
            attribute_values: map,
        }
    }
}


impl PartialEq for DifferentialVertex {
    fn eq(&self, other: &DifferentialVertex) -> bool {
        self.id == other.id
    }
}

impl Hash for DifferentialVertex {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Eq for DifferentialVertex {
}

impl PartialOrd for DifferentialVertex {
    fn partial_cmp(&self, other: &DifferentialVertex) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DifferentialVertex{
    fn cmp(&self, other: &DifferentialVertex) -> Ordering {
        self.id.cmp(&other.id)
    }
}

macro_rules! try_option {
    ($expr:expr) => (match $expr {
        Some(val) => val,
        None => { return None }
    })
}

type DifferentialEdge = (i32, i32);

#[derive(Debug, Clone, PartialEq, Abomonation)]
pub struct DiffEdge{
    source: i32,
    target: i32,  
    label: String,    
    attribute_values: Vec<(String, Literal)>,
}

impl From<GraphEdge> for DiffEdge {
    fn from(data: GraphEdge) -> Self {
        DiffEdge {
            source: data.source,
            target: data.target,
            label: data.label,
            attribute_values: data.attribute_values.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
        }
    }
}

impl GraphEdge {
    fn trans(&self) -> DiffEdge {
        DiffEdge {
            source: self.source,
            target: self.target,
            label: self.label.clone(),
            attribute_values: self.attribute_values.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
        }
    }
    fn trans_rev(&self) -> DiffEdge {
        DiffEdge {
            source: self.target,
            target: self.source,
            label: self.label.clone(),
            attribute_values: self.attribute_values.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
        }
    }
}

impl From<DiffEdge> for GraphEdge {
    fn from(data: DiffEdge) -> Self {
        let mut map = HashMap::new();
        for pair in data.attribute_values {
            let (key, value) = pair;
            map.insert(key, value);
        }
        GraphEdge {
            source: data.source,
            target: data.target,
            label: data.label,
            attribute_values: map,
        }
    }
}

//////////////////////////////
//                          //
//          QUERY           //
//                          //
//////////////////////////////


/*
named!(pgql_query_complete<Query>,
    chain!(
        paths: opt!(path_clause) ~
        space ~
        select: select_clause ~
        space ~
        vvhere: where_clause  ~
        space ~     
        opt!(sol_mod: solution_modifier_clause),
        || Query { select: select, vvhere: vvhere, sol_mod: sol_mod, paths: paths}
    )
);*/

named!(pgql_query<(Vec<SelectElem>, Vec<Constraint>)>, 
    do_parse!(
        select: select_clause >>
        space >>
        vvhere: where_clause >>
        (select, vvhere)
    )
);


named!(path<(String, Connection)>,
    chain!( 
        tag_no_case_s!("path") ~
        space ~
        name: char_only ~
        opt!(space) ~
        tag!(":=") ~
        opt!(space) ~
        pattern: path_pattern,
        || (String::from(name),pattern[0].clone())
    )
);

named!(path_clause<Vec<(String, Connection)> >,
    many0!(
        chain!( 
            path: path ~
            opt!(space) ~
            tag!("\n"),
            || path
        )
    )
);
//////////////////////////////
//                          //
//          SELECT          //
//                          //
//////////////////////////////


named!(select_clause<Vec<SelectElem> >,
    chain!( 
        tag_no_case_s!("select") ~
        space ~
        select_elems: select_elems,
        || select_elems
    )
);

named!(select_elems<Vec<SelectElem> >,
    many1!(
        alt_complete!(
            do_parse!(
                elem: select_elem >>
                char!(',') >>
                opt!(space) >>
                (elem)
            )  |
            select_elem
        )
    )    
);

named!(select_elem<SelectElem>,
    alt_complete!(
                aggregate => {|aggregation| 
                            SelectElem::Aggregation(aggregation)} |
                variable_name => {|v| {let (name, field) = v;
                            let a = Attribute{name: name, field: field};
                            SelectElem::Attribute(a)}}
               
                | tag_s!("*") => {|_| SelectElem::Star}
            )          
);

//////////////////////////////
//                          //
//            WHERE         //
//                          //
//////////////////////////////


named!(where_clause< Vec<Constraint> >,
    chain!(
        tag_no_case_s!("where") ~
        space ~
        constraints: constraints,
        || constraints
    )
);

named!(constraints<Vec <Constraint> >,
    many1!(
        alt_complete!(
            do_parse!(
                constraints: constraint >>
                char!(',') >>
                opt!(space) >>
                (constraints)
            )  |
            constraint
        )
    )    
);


named!(constraint<Constraint>,
    alt!(
        path_pattern       => { |p| Constraint::PathPattern(p)             } |
        expression         => { |e| Constraint::Expr(e)        }
    )
);

//////////////////////////////
//                          //
//            PATH          //
//                          //
//////////////////////////////


/*named!(path_pattern< Connection >,
    chain!(
        source: query_vertex ~
        space ~ 
        edge: query_edge ~
        space ~
        target: query_vertex, 
        || Connection{source: source, target: target, edge: edge}
    )
);*/
named!(path_pattern<Vec<Connection> >,
    chain!(
        initial: query_vertex ~ 
        remainder: many1!(
            chain!(
                space ~ 
                edge: query_edge ~
                space ~
                target: query_vertex, 
                || (edge, target)
            )
        ), ||
    fold_connection(initial, remainder) 
    )
);

fn fold_connection(initial: Vertex, remainder: Vec<(Edge, Vertex)>) -> Vec<Connection> {
    let mut result = Vec::new();
    let mut previous = initial;
    for (edge, vertex) in remainder{
        result.push(Connection{source: previous, target: vertex.clone(), edge: edge});
        previous = vertex;
    }
    return result;
}

named!(query_vertex<Vertex>,
    delimited!(
        char!('('),
        do_parse!(
            vertex_name: opt!(char_only) >> 
            opt!(space) >>
            label: opt!(label_constraint) >>
            opt!(space) >>
            inlined: opt!(inlined_constraints) >>
            ({
                
                let mut constraints: Vec<Expr> = match inlined {
                    Some(value) => value,
                    None => Vec::new()
                };

                match label {
                    Some(value) => {constraints.push(value);},
                    None => {}
                }

                match vertex_name {
                    Some(name) => {Vertex{name: String::from(name), anonymous: false, constraints: constraints }},
                    None => Vertex{name: String::from(""), anonymous: true, constraints: constraints }
                }
            })                
        ),
        char!(')')
  )
);

named!(query_connection<QueryConnection>,
    alt_complete!(
        query_edge => {|edge| QueryConnection::Edge(edge)} |
        query_path => {|path| QueryConnection::Path(path)}
    )
);


named!(query_edge<Edge>,
        alt_complete!(
            tag!("-->") => { |_| Edge {name: String::from(""), inverted: false, constraints: Vec::new() } } |
            tag!("<--") => { |_| Edge {name: String::from(""), inverted: true, constraints: Vec::new() } } | 
            tag!("->") => { |_| Edge {name: String::from(""), inverted: false, constraints: Vec::new() } } | 
            tag!("<-") => { |_| Edge {name: String::from(""), inverted: true, constraints: Vec::new() } } | 
            delimited!(
                tag!("-["),
                do_parse!(
                    edge_name: opt!(char_only) >> 
                    opt!(space) >>
                    label: opt!(label_constraint) >>
                    opt!(space) >>
                    inlined: opt!(inlined_constraints) >>
                    ({
                        
                        let mut constraints: Vec<Expr> = match inlined {
                            Some(value) => value,
                            None => Vec::new()
                        };

                        match label {
                            Some(value) => {constraints.push(value);},
                            None => {}
                        }

                        match edge_name {
                            Some(name) => {Edge{name: String::from(name), inverted: false, constraints: constraints }},
                            None => Edge{name: String::from(""), inverted: false, constraints: constraints }
                        }
                    })                
                ),
                tag!("]->")
            ) |
            delimited!(
                tag!("<-["),
                do_parse!(
                    edge_name: opt!(char_only) >> 
                    opt!(space) >>
                    label: opt!(label_constraint) >>
                    opt!(space) >>
                    inlined: opt!(inlined_constraints) >>
                    ({
                        
                        let mut constraints: Vec<Expr> = match inlined {
                            Some(value) => value,
                            None => Vec::new()
                        };

                        match label {
                            Some(value) => {constraints.push(value);},
                            None => {}
                        }

                        match edge_name {
                            Some(name) => {Edge{name: String::from(name), inverted: true, constraints: constraints }},
                            None => Edge{name: String::from(""), inverted: true, constraints: constraints }
                        }
                    })                
                ),
                tag!("]-")
            )
        )
    
);


named!(query_path<RegularPath>,
    alt!(
        chain!(
            tag!("-/:") ~
            space? ~
            reg_path: regular_path_pattern ~
            space? ~
            tag!("/->"),
            || reg_path
        ) |
        chain!(
            tag!("<-/:") ~
            space? ~
            reg_path: regular_path_pattern ~
            space? ~
            tag!("/-"),
            || RegularPath::Inverted(Box::new(reg_path))
        )
    )
);

named!(regular_path_pattern<RegularPath>,
    alt_complete!(
        char_only => {|name| RegularPath::Predefined(String::from(name))} | //Label or Pathpattern
        repeatable_path => {|repeatable_path| RegularPath::Repeatable(Box::new(repeatable_path))} |
        alternative_path
    )
);

named!(repeatable_path<RepeatablePath>,
    do_parse!(
        reg_path: regular_path_pattern >>
        opt!(space) >>
        min: unsigned_int >>
        dots: opt!(tag!("..")) >>
        max: opt!(unsigned_int) >>
        ({
            if dots.is_some() {
                match max {
                    Some(value) => { RepeatablePath {min: min, max: value, path: reg_path} },
                    None => { RepeatablePath {min: min, max: 2147483647, path: reg_path} }
                }
            }
            else {
                RepeatablePath {min: min, max: min, path: reg_path}
            }
        })
    )
);

named!(alternative_path< RegularPath >,
        chain!(
            reg_path: regular_path_pattern ~
            space ~
            char!('|') ~
            space ~
            alternative: regular_path_pattern,
            || RegularPath::Alternative(Box::new(reg_path), Box::new(alternative))
        )
);


named!(label_constraint<Expr>,
    chain!(
        char!(':') ~
        opt!(space) ~
        label: char_only, // Label
        || Expr::Label(String::from(label))
    )
);

named!(inlined_constraints<Vec<Expr> >,
    chain!(
        tag_no_case_s!("with") ~
        space ~
        exprs: expressions,
        || exprs
    )
);

named!(expressions<Vec<Expr> >,
    many1!(
        alt_complete!(
            do_parse!(
                expr: expression >>
                char!(',') >>
                opt!(space) >>
                (expr)
            )  |
            expression
        )
    )
);


//////////////////////////////
//                          //
//     EXPRESSION           //
//                          //
//////////////////////////////



/*named!(operand<Expr>,
    do_parse!(
        negate: opt!(alt!(tag_no_case_s!("not")|tag!("!"))) >>
        opt!(space) >>
        a: alt!(
                literal => {|l| Expr::Literal(l) } |
                variable_name => {
                    |v| {
                        let (name, field) = v;
                        let a = Attribute{name: name, field: field};
                        Expr::Attribute(a) 
                    }
                }
                
            ) >>
        ({
            match negate {
                None => a,
                Some(_) => Expr::Not(Box::new(a))
            }
        })
    )
);*/

named!(operand<Expr>,
        alt_complete!(
                literal => {|l| Expr::Literal(l) } |
                do_parse!(
                    name: char_only >>
                    tag!(".") >>
                    func: builtin_function >> ({
                        Expr::BuiltIn(name.into(),func)
                    })
                ) |
                variable_name => {
                    |value| {
                        let (name, field) = value;
                        let attribute = Attribute{name: name, field: field};
                        Expr::Attribute(attribute) 
                    }
                }
                
            )
);

named!(expression< Expr >, chain!(
    initial: operand ~ 
    remainder: many0!(
            alt!(
                chain!(opt!(space) ~ tag!("+")  ~ opt!(space) ~ op: operand,   || (Oper::Add, op))       |
                chain!(opt!(space) ~ tag!("-")  ~ opt!(space) ~ op: operand,   || (Oper::Sub, op))       |
                chain!(opt!(space) ~ tag!("*")  ~ opt!(space) ~ op: operand,   || (Oper::Mul, op))       |
                chain!(opt!(space) ~ tag!("/")  ~ opt!(space) ~ op: operand,   || (Oper::Div, op))       |
                chain!(opt!(space) ~ tag!("%")  ~ opt!(space) ~ op: operand,   || (Oper::Modulo, op))    |
                chain!(opt!(space) ~ tag!("=")  ~ opt!(space) ~ op: operand,   || (Oper::Equal, op))     |
                chain!(opt!(space) ~ tag!("!=") ~ opt!(space) ~ op: operand,   || (Oper::NotEqual, op))  |
                chain!(opt!(space) ~ tag!(">")  ~ opt!(space) ~ op: operand,   || (Oper::Greater, op))   |
                chain!(opt!(space) ~ tag!(">=") ~ opt!(space) ~ op: operand,   || (Oper::GreaterEq, op)) |
                chain!(opt!(space) ~ tag!("<")  ~ opt!(space) ~ op: operand,   || (Oper::Smaller, op))   |
                chain!(opt!(space) ~ tag!("<=") ~ opt!(space) ~ op: operand,   || (Oper::SmallerEq, op)) |
                chain!(opt!(space) ~ tag!("=~") ~ opt!(space) ~ op: operand,   || (Oper::Like, op))      |
                chain!(opt!(space) ~ tag_no_case_s!("and") ~ opt!(space) ~ op: operand, || (Oper::And, op))       |
                chain!(opt!(space) ~ tag_no_case_s!("or") ~ opt!(space) ~ op: operand,  || (Oper::Or, op))    
             )
        ), ||
    fold_exprs(initial, remainder) 
    ) 
    
    
);



fn fold_exprs(initial: Expr, remainder: Vec<(Oper, Expr)>) -> Expr {
    remainder.into_iter().fold(initial, |acc, pair| {
        let (oper, expr) = pair;
        match oper {
            Oper::Add       => Expr::Add(Box::new(acc), Box::new(expr)),
            Oper::Sub       => Expr::Sub(Box::new(acc), Box::new(expr)),
            Oper::Mul       => Expr::Mul(Box::new(acc), Box::new(expr)),
            Oper::Div       => Expr::Div(Box::new(acc), Box::new(expr)),
            Oper::Modulo    => Expr::Modulo(Box::new(acc), Box::new(expr)),
            Oper::Equal     => Expr::Equal(Box::new(acc), Box::new(expr)),
            Oper::NotEqual  => Expr::NotEqual(Box::new(acc), Box::new(expr)),
            Oper::Greater   => Expr::Greater(Box::new(acc), Box::new(expr)),
            Oper::GreaterEq => Expr::GreaterEq(Box::new(acc), Box::new(expr)),
            Oper::Smaller   => Expr::Smaller(Box::new(acc), Box::new(expr)),
            Oper::SmallerEq => Expr::SmallerEq(Box::new(acc), Box::new(expr)),            
            Oper::Like      => Expr::Like(Box::new(acc), Box::new(expr)),
            Oper::And       => Expr::And(Box::new(acc), Box::new(expr)),
            Oper::Or        => Expr::Or(Box::new(acc), Box::new(expr)),
            Oper::Not       => Expr::Not(Box::new(acc)),
        }
    })
}




named!(aggregate<Aggregation>,
    alt_complete!(
        do_parse!(
            tag_no_case_s!("count(*)") >>
            ({
                let attribute = Attribute{name: "*".into(), field: "".into()};
                Aggregation::Count(attribute)
            })
            ) |
        do_parse!(
            tag_no_case_s!("count") >>
            variable_name: delimited!(tag!("("), variable_name, tag!(")")) >>
            ({
                let (name, field) = variable_name;
                let attribute = Attribute{name: name, field: field};
                Aggregation::Count(attribute)
            })
            ) |
        do_parse!(
            tag_no_case_s!("min") >>
            variable_name: delimited!(tag!("("), variable_name, tag!(")")) >>
            ({
                let (name, field) = variable_name;
                let attribute = Attribute{name: name, field: field};
                Aggregation::Min(attribute)
            })
            ) |
        do_parse!(
            tag_no_case_s!("max") >>
            variable_name: delimited!(tag!("("), variable_name, tag!(")")) >>
            ({
                let (name, field) = variable_name;
                let attribute = Attribute{name: name, field: field};
                Aggregation::Max(attribute)
            })
            ) |
        do_parse!(
            tag_no_case_s!("sum") >>
            variable_name: delimited!(tag!("("), variable_name, tag!(")")) >>
            ({
                let (name, field) = variable_name;
                let attribute = Attribute{name: name, field: field};
                Aggregation::Sum(attribute)
            })
            ) |
        do_parse!(
            tag_no_case_s!("avg") >>
            variable_name: delimited!(tag!("("), variable_name, tag!(")")) >>
            ({
                let (name, field) = variable_name;
                let attribute = Attribute{name: name, field: field};
                Aggregation::Avg(attribute)
            })
            ) 
    )
);

named!(builtin_function<BuiltIn>,
    alt_complete!(
        tag!("id()")        => { |_| BuiltIn::Id } |
        tag!("inDegree()")  => { |_| BuiltIn::InDegree } |
        tag!("outDegree()") => { |_| BuiltIn::OutDegree } |
        tag!("labels()")    => { |_| BuiltIn::Labels } |
        tag!("label()")     => { |_| BuiltIn::Label } 
    )
);


//////////////////////////////
//                          //
//    SOLUTION MODIFIER     //
//                          //
//////////////////////////////



named!(solution_modifier_clause<(GroupBy, OrderBy, (i32, i32))>,
    chain!(
        group: group_by ~
        space ~
        order: order_by ~
        space ~
        limit: limit_offset,
        || (group, order, limit)
    )
);


named!(order_by<OrderBy >,
    chain!(
        tag_no_case_s!("order") ~
        space ~
        tag_no_case_s!("by") ~
        space ~
        order_terms: many1!(
            chain!(
                order_term: order_term ~
                opt!(space) ~
                opt!(char!(',')),
                || order_term
                )
            ),
        || OrderBy{order: order_terms}
    )
);

named!(order_term<OrderTerm>,
    alt_complete!(
        chain!(
            expr: expression ~
            space ~
            asc: alt!(
                    tag_no_case_s!("asc") => { |_| true } |
                    tag_no_case_s!("desc") => { |_| false } |
                    tag!("") => { |_| true }
                ),
            || {OrderTerm {expr: expr, asc: asc}}
        ) |
        chain!(
            asc: alt!(
                tag_no_case_s!("asc") => { |_| true } |
                tag_no_case_s!("desc") => { |_| false } |
                tag!("") => { |_| true }
            ) ~
            space ~
            expr: expression,
        || {OrderTerm {expr: expr, asc: asc}}
        )
    )
);


named!(limit_offset<(i32, i32)>,
    alt!(
        chain!(
            tag_no_case_s!("limit") ~
            space ~
            limit: unsigned_int ~
            space ~
            tag_no_case_s!("offset") ~
            space ~
            offset: unsigned_int,
            || (limit, offset)
        ) |
        chain!(
            tag_no_case_s!("offset") ~
            space ~
            offset: unsigned_int ~
            space ~
            tag_no_case_s!("limit") ~
            space ~
            limit: unsigned_int,
            || (limit, offset)

        )
    )
);

named!(group_by<GroupBy>,
    chain!(
        tag_no_case_s!("group") ~
        space ~
        tag_no_case_s!("by") ~
        space ~
        expressions: many1!(
            chain!(
                expr: expression ~ 
                opt!(space) ~
                opt!(char!(',')),
                || expr
            )
        ),
        || GroupBy{ group: expressions}

    )
);

//////////////////////////////
//                          //
//            UTIL          //
//                          //
//////////////////////////////


named!(variable_name<(String,String)>,
    alt_complete!(            
            chain!(
                name: char_only ~
                char!('.') ~
                attribute: char_only,
                || (String::from(name), String::from(attribute))
            ) |
            char_only => {|attribute| (String::from(""), String::from(attribute))} 
    )

);


named!(literal<Literal>,
    alt_complete!(       
        float       => { |f| Literal::Float(f)             } |
        boolean     => { |b| Literal::Boolean(b)           } |
        string      => { |s| Literal::Str(String::from(s)) }             
    )
);

named!(unsigned_int<i32>,
    map_res!(
        map_res!(
            digit,
            str::from_utf8
        ),
        FromStr::from_str
    )
);

named!(unsigned_float<f32>, map_res!(
  map_res!(
    recognize!(
      alt_complete!(
        delimited!(
            digit,
            tag!("."),
            opt!(
                complete!(
                    digit
                )
            )
        ) |
        delimited!(
            opt!(
                digit
            ),
            tag!("."),
            digit
        ) | digit
      ) 
    ),
    str::from_utf8
  ),
  FromStr::from_str
));


named!(float<f32>, map!(
  pair!(
    opt!(alt!(tag!("+") | tag!("-"))),
    unsigned_float
  ),
  |(sign, value): (Option<&[u8]>, f32)| {
    sign.and_then(|s| if s[0] == ('-' as u8) { Some(-1.0) } else { None }).unwrap_or(1.0) * value
  }
));


named!(char_only<&str>,
    map_res!(alpha, std::str::from_utf8)
);


named!(string<&str>,
    map_res!(
        alt!(
          delimited!(
            char!('"'),
            is_not!("\""),
            char!('"')
          ) |
          delimited!(
            tag!("'"),
            is_not!("'"),
            tag!("'")
          )
        ),
        std::str::from_utf8
    )
);


named!(boolean<bool>,
    map_res!(
        map_res!(
            alt!(
                tag_s!("true".as_bytes()) |
                tag_s!("false".as_bytes())
            ),
            std::str::from_utf8
        ),
        FromStr::from_str
    )
);


named!(line_end, alt_complete!(tag!("\r\n") | tag!("\n")));


//////////////////////////////
//                          //
//            GRAPH         //
//                          //
//////////////////////////////


named!(graph_parser<Graph>,
    chain!(
        nodes: many1!(node) ~
        edges: many1!(edge),
        || Graph {nodes: nodes, edges: edges}
    )
);

named!(node<Node>,
    chain!(
        id: unsigned_int ~
        space ~
        char!('*') ~
        space ~
        labels: labels ~
        space ~
        attr: attributes ~
        line_end,
        || {
            let mut map = HashMap::with_capacity(attr.len());
            for elem in attr{
                let (name, value) = elem;
                map.insert(String::from(name), value);
            }
            Node {id: id, label: labels, attribute_values: map }            
        }
    )

);

named!(labels<Vec <String> >, 
    chain!(
        char!('{') ~
        space ~
        labels: many1!(
            chain!(
                s: string ~
                space,
                || String::from(s))
            ) ~ 
        char!('}'),
        || labels
    )
);

named!(edge<GraphEdge>,
    chain!(
        source: unsigned_int ~
        space ~
        target: unsigned_int ~
        space ~
        label: string ~
        space ~
        attr: attributes ~
        line_end,
        || {
            let mut map = HashMap::with_capacity(attr.len());
            for elem in attr{
                let (name, value) = elem;
                map.insert(String::from(name), value);
            }
            GraphEdge {source: source, target: target, label:String::from(label), attribute_values: map }
        }
    )

);

named!(attributes< Vec< (&str, Literal) > >,
    many0!(
        chain!(
            name: char_only ~
            opt!(space) ~
            char!(':') ~
            opt!(space) ~
            value: literal ~
            opt!(space),
            || (name, value)
        )
    )
);


fn string_to_static_str(s: String) -> &'static str {
    unsafe {
        let ret = mem::transmute(&s as &str);
        mem::forget(s);
        ret
    }
}

impl Display for Graph
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result
    {
        let mut string = String::new();
        string.push_str("Graph:\n");

        for num in &self.nodes[0..self.nodes.len()]
        {
            let s =  format!("{:?}",num);
            let s_slice: &str = &s[..];
            string.push_str(s_slice);
            string.push_str("\n");
        }

        string.push_str("\n");

        for num in &self.edges[0..self.edges.len()]
        {
            let s =  format!("{:?}",num);
            let s_slice: &str = &s[..];
            string.push_str(s_slice);
            string.push_str("\n");
        }

        write!(f, "{}", string)
    }
}


fn main() { 
    
    let graph_filepath: String = std::env::args().nth(1).unwrap();
    let st = string_to_static_str(graph_filepath);    
    let query_filepath: String = std::env::args().nth(2).unwrap();

    //Parse the Query
    let mut file = File::open(&query_filepath).unwrap();
    let mut reader = BufReader::new(&file);
    
    for line in reader.lines() {

        let query = line.unwrap();
        // define a new computational scope, in which to run the query
        timely::execute_from_args(std::env::args().skip(2), move |computation| {

            let timer = Instant::now();

            // logic goes here
            let (mut edges, mut vertices, probe) = computation.scoped(|scope| {

                // handle to push edges into the system
                let (vertex_input, vertices) = scope.new_input();

                // handle to push edges into the system
                let (edge_input, edges) = scope.new_input();

                let (probe, output) = evaluate(&Collection::new(edges), &query, &Collection::new(vertices)).unwrap().probe();
                (edge_input, vertex_input, probe)
            });
            
            if computation.index() == 0 { // this block will be executed by worker/thread 0
 
                let timer2 = Instant::now();
                
                // Load the Graph
                let mut file2 = File::open(st).unwrap();
                let mut string = String::new();
                 
                match file2.read_to_string(&mut string) {
                    Err(error) => panic!("Couldn't read file {}: {}", st,
                                                               error.description()),
                    Ok(_) => {println!("Graph File {} successfully opened\n", st)
                    },
                }
                
                let result = graph_parser(&string.as_bytes());

                match result {
                    IResult::Done(_, value) => {
                        
                        for elem in value.nodes{
                            vertices.send((elem.into(),1));
                        }

                        for elem in value.edges{
                            edges.send((elem.trans(),1));
                            edges.send((elem.trans_rev(),1));
                        }
                    }

                    IResult::Error( value) => {
                        match value {
                            Err::Position(parse, array) => {
                                println!("{:?} Parser failed\n", parse);
                                println!("Remaining Input: {:?}", std::str::from_utf8(array));
                            }
                            _ => println!("{:?}",value)
                        }
                    }
                    IResult::Incomplete( value) =>println!("{:?}", value)
                }
                println!("Graph Loading: {:?}\n\n", timer2.elapsed());

            }

            
            let timer3 = Instant::now();
            // advance epoch
            edges.advance_to(1);
            vertices.advance_to(1);
            // do the job
            computation.step_while(|| probe.lt(edges.time()));

                        

            if computation.index() == 0 {
                println!("Evaluation time: {:?}\n\n", timer3.elapsed());
                println!("Total Execution: {:?}\n\n", timer.elapsed());
            }

        }).unwrap();
    }

}


fn evaluate<G: Scope>(edges: &Collection<G, DiffEdge>, query_string: &String,
    vertices: &Collection<G, DifferentialVertex>) -> Option<Collection<G, Vec<DifferentialVertex> > > where G::Timestamp: Lattice {
    
    let query = pgql_query(query_string.as_bytes());
    
    match query {
        IResult::Done(_, (select,vvhere)) => {
            let mut connections = Vec::new();
            let mut selections : HashMap<String, Vec<Expr> > = HashMap::new();

            for constraint in &vvhere{
                match constraint {
                    &Constraint::PathPattern(ref vec) => {
                        for pattern in vec{
                        connections.push(pattern);}
                    },
                    &Constraint::Expr(ref expr) => {
                        let name = explore_expr((*expr).clone());
                        let mut new = false;
                        match selections.get_mut(&name) {
                            Some(vec) => vec.push((*expr).clone()),
                            None => new = true,
                        }
                        if new {
                            selections.insert(name, vec![(*expr).clone()]);
                        }
                    },
                }
            }

            let mut execution_plan = Vec::new();
            let mut used_fields= HashSet::new();
            let mut names = HashMap::new();
            let mut ids :usize = 0;

            for connection in connections {
                if !used_fields.contains(&connection.source.name) {
                    used_fields.insert(&connection.source.name);
                    used_fields.insert(&connection.target.name);
                    names.insert(&connection.source.name, ids);
                    ids = ids + 1;
                    names.insert(&connection.target.name, ids);
                    ids = ids + 1;

                    let mut new = false;
                    match selections.get_mut(&connection.source.name) {
                            Some(mut vec) => vec.append(& mut connection.source.constraints.clone()),
                            None => new = true,
                    }
                    if new {
                            selections.insert(connection.source.name.clone(), connection.source.constraints.clone());
                    }
                    new = false;
                    match selections.get_mut(&connection.target.name) {
                            Some(mut vec) => vec.append(& mut connection.target.constraints.clone()),
                            None => new = true,
                    }
                    if new {
                            selections.insert(connection.target.name.clone(), connection.target.constraints.clone());
                    }

                    execution_plan.push(
                        PhyPlan{ 
                            name: vec![connection.source.name.clone(), connection.target.name.clone()],
                            left: connection.source.name.clone(),
                            right: connection.target.name.clone(),
                            join_id: 0,
                            join: true,
                            filter_id: 100,
                            constraints: connection.edge.constraints.clone(),
                        }
                    );
                }
                else if !used_fields.contains(&connection.target.name) {
                    used_fields.insert(&connection.target.name);
                    names.insert(&connection.target.name, ids);
                    ids = ids + 1;

                    let mut new = false;
                    match selections.get_mut(&connection.target.name) {
                            Some(mut vec) => vec.append(& mut connection.target.constraints.clone()),
                            None => new = true,
                    }
                    if new {
                            selections.insert(connection.target.name.clone(), connection.target.constraints.clone());
                    }
                    execution_plan.push(
                        PhyPlan{ 
                            name: vec![connection.source.name.clone(), connection.target.name.clone()],
                            left: connection.source.name.clone(),
                            right: connection.target.name.clone(),
                            join_id: *names.get(&connection.source.name).unwrap(),
                            join: true,
                            filter_id: 100,
                            constraints: connection.edge.constraints.clone(),
                        }
                    );
                }
                else {
                    execution_plan.push(
                        PhyPlan{ 
                            name: vec![connection.source.name.clone(), connection.target.name.clone()],
                            left: connection.source.name.clone(),
                            right: connection.target.name.clone(),
                            join_id: *names.get(&connection.source.name).unwrap(),
                            join: false,
                            filter_id: *names.get(&connection.target.name).unwrap(),
                            constraints: connection.edge.constraints.clone(),
                        }
                    );
                }

            }

            let mut plans = HashMap::new();

            for (name, filter) in selections {
                let result = vertices.filter(move |x| {
                    check_node(&x, &filter)
                });

                plans.insert(name, result);
            }

            if execution_plan.len() == 0 {
                for projection in &select{
                                match projection {
                                    &SelectElem::Star => {
                                        for (ref key,ref plan) in &plans {
                                            plan.inspect(|&(ref x,_)| println!("{:?}", x));
                                            return Some(plan.map(|x| vec![x]));
                                        }
                                    },
                                    &SelectElem::Attribute(ref attr) => {
                                        let vertices = plans.get(&attr.name).unwrap();
                                        let field = string_to_static_str(attr.field.clone());
                                        vertices.inspect(move |&(ref x,_)| println!("{:?}", x.get(&field.into()).unwrap()));
                                       
                                    },
                                    &SelectElem::Aggregation(ref aggr) => {
                                        match aggr {
                                            &Aggregation::Count(ref attr) => {
                                                let plan = plans.get(&attr.name).unwrap();
                                                    (*plan).map(|x| (1, x)).group(|key, vals, output| {
                                                        let mut count = 0;
                                                        for _ in vals {
                                                            count = count + 1;
                                                        }                                                        
                                                        output.push(((),count));
                                                    }).inspect(|&(_, ref x)| println!("{:?}", x));
                                                    return Some(plan.map(|x| vec![x]));
                                                
                                            },
                                            &Aggregation::Max(ref attr) => {
                                                let plan = plans.get(&attr.name).unwrap();
                                                let field = string_to_static_str(attr.field.clone());
                                                (*plan).map(|x| (1, x)).group(move |key, vals, output| {
                                                    let mut max = vals.next().unwrap().0.get(&field.into()).unwrap().as_float();
                                                    for (val,_) in vals {
                                                        let value = val.get(&field.into()).unwrap().as_float();
                                                        if value > max{
                                                        max = value;}
                                                    }                                                
                                                    output.push(((), max as  i32));
                                                }).inspect(|&(_, ref x)| println!("{:?}", x));
                                            },
                                            &Aggregation::Min(ref attr) => {
                                                let plan = plans.get(&attr.name).unwrap();
                                                let field = string_to_static_str(attr.field.clone());
                                                (*plan).map(|x| (1, x)).group(move |key, vals, output| {
                                                    let mut min = vals.next().unwrap().0.get(&field.into()).unwrap().as_float();
                                                    for (val,_) in vals {
                                                        let value = val.get(&field.into()).unwrap().as_float();
                                                        if value < min{
                                                        min = value;}
                                                    }                                                
                                                    output.push(((), min as  i32));
                                                }).inspect(|&(_, ref x)| println!("{:?}", x));
                                            },
                                            &Aggregation::Sum(ref attr) => {
                                                let plan = plans.get(&attr.name).unwrap();                                            
                                                let field = string_to_static_str(attr.field.clone());
                                                (*plan).map(|x| (1, x)).group(move |key, vals, output| {
                                                    let mut sum = 0.0;
                                                    for (val,_) in vals {
                                                        sum = sum + val.get(&field.into()).unwrap().as_float();
                                                    }                                                
                                                    output.push(((),sum as i32));
                                                }).inspect(|&(_, ref x)| println!("{:?}", x));
                                            },
                                            &Aggregation::Avg(ref attr) => {
                                                let plan = plans.get(&attr.name).unwrap();                                            
                                                let field = string_to_static_str(attr.field.clone());
                                                (*plan).map(|x| (1, x)).group(move |key, vals, output| {
                                                    let mut count = 0;
                                                    let mut sum = 0.0;
                                                    for (val,_) in vals {
                                                        count = count + 1;
                                                        sum = sum + val.get(&field.into()).unwrap().as_float();
                                                    }                                                
                                                    output.push(((),sum as i32 /count ));
                                                }).inspect(|&(_, ref x)| println!("{:?}", x));
                                            }                             
                                        }
                                    },
                                }
                            }
            }

            else{
                let mut result = None;
                for step in execution_plan {
                    
                    if step.join && step.join_id == 0 {
                        let sources = match plans.get(&step.left){
                            None => vertices,
                            Some(list) => list,
                        };

                        let targets = match plans.get(&step.right){
                            Some(list) => list,
                            None => vertices,
                        };
                        result =    Some(sources.map(|x| (x.id, x))
                                    .join(&edges.filter(move |x| check_edge(&x, &step.constraints))
                                    .map(|x| (x.source,x.target)))
                                    .map(|(_,v1,v2)| (v2,v1))
                                    .join(&targets.map(|x| (x.id, x)))
                                    .map(|(_,v1,v2)| vec![v1,v2]));
                    }
                    else if !step.join {
                        let int = step.join_id;
                        let int2 = step.filter_id;
                        result = Some(result.unwrap().map(move |x| (x[int].id, x))
                                .join(&edges.filter(move |x| check_edge(&x, &step.constraints))
                                .map(|x| (x.source,x.target)))
                                .filter(move |x| {let &(ref key, ref vec, ref id) = x; vec[int2].id == *id})
                                .map(|(_,v1,_)| v1));

                    }
                    else {
                        let x = string_to_static_str(step.right.clone());
                        let y = step.join_id;                 
                        let targets = match plans.get(&x.to_string()){
                            Some(list) => list,
                            None => vertices,
                        };
                        result = Some(result.unwrap().map(move |vec| (vec[y].id, vec))
                                .join(&edges.filter(move |x| check_edge(&x, &step.constraints))
                                .map(|x| (x.source,x.target)))
                                .map(|(_,v1,v2)| (v2,v1))
                                .join(&targets.map(|x| (x.id, x)))
                                .map(|(_, mut v1,v2)| {v1.push(v2);v1}));   
                    }
                }

                match result {
                    Some(list) => {
                        let mut count = 0;
                        println!("Your Query {} returned the following result:\n", query_string);
          
                        for projection in &select{
                            match projection {
                                &SelectElem::Star => {
                                    list.inspect(|&(ref x,_)| println!("{:?}", x));
                                },
                                &SelectElem::Attribute(ref attr) => {
                                    let field = string_to_static_str(attr.field.clone());
                                    let id = *(names.get(&attr.name).unwrap());
                                    list.inspect(move |&(ref x,_)| println!("{:?}", x[id].get(&field.into()).unwrap()));
                                    
                                    
                                },
                                &SelectElem::Aggregation(ref aggr) => {
                                    match aggr {
                                        &Aggregation::Count(ref attr) => {
                                                list.map(move |x| (1, x)).group(move |key, vals, output| {
                                                        let mut count = 0;
                                                        for _ in vals {
                                                            count = count + 1;
                                                        }                                                        
                                                        output.push(((),count));
                                                    }).inspect(|&(_, ref x)| println!("{:?}", x));
                                                
                                            },
                                        &Aggregation::Sum(ref attr) => {
                                            let field = string_to_static_str(attr.field.clone());
                                            let id = *(names.get(&attr.name).unwrap());
                                            list.map(|x| (1, x)).group(move |key, vals, output| {
                                                let mut sum = 0.0;
                                                for (val,_) in vals {
                                                    sum = sum + val[id].get(&field.into()).unwrap().as_float();
                                                }                                                
                                                output.push(((),sum as i32));
                                            }).inspect(|&(_, ref x)| println!("{:?}", x));                                                
                                        },
                                        &Aggregation::Avg(ref attr) => {                                           
                                            let field = string_to_static_str(attr.field.clone());
                                            let id = *(names.get(&attr.name).unwrap());
                                            list.map(|x| (1, x)).group(move |key, vals, output| {
                                                let mut count = 0;
                                                let mut sum = 0.0;
                                                for (val,_) in vals {
                                                    count = count + 1;
                                                    sum = sum + val[id].get(&field.into()).unwrap().as_float();
                                                }                                                
                                                output.push(((),sum as i32 /count ));
                                            }).inspect(|&(_, ref x)| println!("{:?}", x));
                                        },
                                        &Aggregation::Max(ref attr) => {
                                            let field = string_to_static_str(attr.field.clone());
                                            let id = *(names.get(&attr.name).unwrap());
                                            list.map(|x| (1, x)).group(move |key, vals, output| {
                                                let mut max = vals.next().unwrap().0[0].get(&field.into()).unwrap().as_float();
                                                for (val,_) in vals {
                                                    let value = val[id].get(&field.into()).unwrap().as_float();
                                                    if value > max{
                                                    max = value;}
                                                }                                                
                                                output.push(((), max as  i32));
                                            }).inspect(|&(_, ref x)| println!("{:?}", x));
                                        },
                                        &Aggregation::Min(ref attr) => {
                                            let field = string_to_static_str(attr.field.clone());
                                            let id = *(names.get(&attr.name).unwrap());
                                            list.map(|x| (1, x)).group(move |key, vals, output| {
                                                let mut min = vals.next().unwrap().0[0].get(&field.into()).unwrap().as_float();
                                                for (val,_) in vals {
                                                    let value = val[id].get(&field.into()).unwrap().as_float();
                                                    if value < min{
                                                    min = value;}
                                                }                                                
                                                output.push(((), min as  i32));
                                            }).inspect(|&(_, ref x)| println!("{:?}", x));
                                        }
                                    }

                                },
                            }
                        }
                        return Some(list);
                        
                    },
                    None => {println!("No vertices match your criteria");
                    return  None;},
                }   
            }
        }

            IResult::Error(value) => {
                match value {
                    Err::Position(parse, array) => {
                        println!("{:?} Parser failed\n", parse);
                        println!("Remaining Input: {:?}", std::str::from_utf8(array));
                    }
                    _ => println!("{:?}",value)
                }

            }
            _ => println!("{:?}", query)            
        
    }
    return None;
}

fn check_edge (edge: &DiffEdge, constraints: &Vec<Expr>) -> bool {
    if constraints.len() == 0 {
        return true;
    }
    let mut result = true;
    let vertex = (*edge).clone().into();
    for constraint in constraints {
        let boolean = match evaluate_expr_edge((*constraint).clone(), &vertex) {
            Literal::Boolean(value) => value,
            _ => panic !("Non Boolean value found!")
        }; 
        result = result && boolean;
    }
    (result)
}


fn check_node (node: &DifferentialVertex, constraints: &Vec<Expr>) -> bool {
    if constraints.len() == 0 {
        return true;
    }
    let mut result = true;
    let vertex = (*node).clone().into();
    for constraint in constraints {
        let boolean = match evaluate_expr((*constraint).clone(), &vertex) {
            Literal::Boolean(value) => value,
            _ => panic !("Non Boolean value found!")
        }; 
        result = result && boolean;
    }
    (result)
}

fn evaluate_expr (constraint: Expr, node: &Node) -> Literal {
    match constraint{
        Expr::Equal(left, right)         => Literal::Boolean(evaluate_expr(*left, node) == evaluate_expr(*right, node)),
        Expr::NotEqual(left, right)      => Literal::Boolean(evaluate_expr(*left, node) != evaluate_expr(*right, node)),
        Expr::Smaller(left, right)       => evaluate_expr(*left, node).smaller(evaluate_expr(*right, node)),
        Expr::SmallerEq(left, right)     => evaluate_expr(*left, node).smaller_eq(evaluate_expr(*right, node)),
        Expr::Greater(left, right)       => evaluate_expr(*left, node).greater(evaluate_expr(*right, node)),
        Expr::GreaterEq(left, right)     => evaluate_expr(*left, node).greater_eq(evaluate_expr(*right, node)),
        Expr::Like(left, right)          => evaluate_expr(*left, node).contains(evaluate_expr(*right, node)),
        Expr::And(left, right)           => evaluate_expr(*left, node).and(evaluate_expr(*right, node)),
        Expr::Or(left, right)            => evaluate_expr(*left, node).or(evaluate_expr(*right, node)),
        Expr::Not(value)                 => evaluate_expr(*value, node).not(),
        Expr::Label(label)               => Literal::Boolean(node.label.contains(&label)),
        Expr::Add(left, right)           => evaluate_expr(*left, node).add(evaluate_expr(*right, node)),
        Expr::Sub(left, right)           => evaluate_expr(*left, node).sub(evaluate_expr(*right, node)),
        Expr::Mul(left, right)           => evaluate_expr(*left, node).mul(evaluate_expr(*right, node)),
        Expr::Div(left, right)           => evaluate_expr(*left, node).div(evaluate_expr(*right, node)),
        Expr::Modulo(left, right)        => evaluate_expr(*left, node).modulo(evaluate_expr(*right, node)),
        Expr::Literal(value)             => value,
        Expr::Attribute(attribute)       => {
            match node.attribute_values.get(&attribute.field) {
                Some(literal) => (*literal).clone(),
                None => Literal::Boolean(false),
                //panic!("Field {:?} does not exist!", &attribute.field) 
                }
            },
        Expr::BuiltIn(_, function) => {
            match function {
                BuiltIn::Label => Literal::Str(node.label[0].clone()),
                BuiltIn::Id => Literal::Float(node.id as f32),
                _ => panic!("Function {:?} not supported for nodes", function)
            }
        }
    }
}

fn evaluate_expr_edge (constraint: Expr, edge: &GraphEdge) -> Literal {
    match constraint {
        Expr::Equal(left, right)         => Literal::Boolean(evaluate_expr_edge(*left, edge) == evaluate_expr_edge(*right, edge)),
        Expr::NotEqual(left, right)      => Literal::Boolean(evaluate_expr_edge(*left, edge) != evaluate_expr_edge(*right, edge)),
        Expr::Smaller(left, right)       => evaluate_expr_edge(*left, edge).smaller(evaluate_expr_edge(*right, edge)),
        Expr::SmallerEq(left, right)     => evaluate_expr_edge(*left, edge).smaller_eq(evaluate_expr_edge(*right, edge)),
        Expr::Greater(left, right)       => evaluate_expr_edge(*left, edge).greater(evaluate_expr_edge(*right, edge)),
        Expr::GreaterEq(left, right)     => evaluate_expr_edge(*left, edge).greater_eq(evaluate_expr_edge(*right, edge)),
        Expr::Like(left, right)          => evaluate_expr_edge(*left, edge).contains(evaluate_expr_edge(*right, edge)),
        Expr::And(left, right)           => evaluate_expr_edge(*left, edge).and(evaluate_expr_edge(*right, edge)),
        Expr::Or(left, right)            => evaluate_expr_edge(*left, edge).or(evaluate_expr_edge(*right, edge)),
        Expr::Not(value)                 => evaluate_expr_edge(*value, edge).not(),
        Expr::Label(label)               => Literal::Boolean(edge.label == label),
        Expr::Add(left, right)           => evaluate_expr_edge(*left, edge).add(evaluate_expr_edge(*right, edge)),
        Expr::Sub(left, right)           => evaluate_expr_edge(*left, edge).sub(evaluate_expr_edge(*right, edge)),
        Expr::Mul(left, right)           => evaluate_expr_edge(*left, edge).mul(evaluate_expr_edge(*right, edge)),
        Expr::Div(left, right)           => evaluate_expr_edge(*left, edge).div(evaluate_expr_edge(*right, edge)),
        Expr::Modulo(left, right)        => evaluate_expr_edge(*left, edge).modulo(evaluate_expr_edge(*right, edge)),
        Expr::Literal(value)             => value,
        Expr::Attribute(attribute)       => {
            match edge.attribute_values.get(&attribute.field) {
                Some(literal) => (*literal).clone(),
                None => Literal::Boolean(false),
                //panic!("Field {:?} does not exist!", &attribute.field) 
                }
            },
        Expr::BuiltIn(_, function) => {
            match function {
                BuiltIn::Label => Literal::Str(edge.label.clone()),
                _ => panic!("Function {:?} not supported for edges", function)
            }
        }
    }
}


fn explore_expr(expr: Expr) -> String {
    let mut result:String = "".into();
    match expr {
        Expr::Attribute(attribute)       => result.push_str(&attribute.name),
        Expr::Equal(left, right)         => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},        
        Expr::NotEqual(left, right)      => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::Smaller(left, right)       => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::SmallerEq(left, right)     => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::Greater(left, right)       => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::GreaterEq(left, right)     => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::Like(left, right)          => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::And(left, right)           => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::Or(left, right)            => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::Not(value)                 => result.push_str(&explore_expr(*value)),
        Expr::Add(left, right)           => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::Sub(left, right)           => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::Mul(left, right)           => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::Div(left, right)           => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::Modulo(left, right)        => {result.push_str(&explore_expr(*left)); result.push_str(&explore_expr(*right));},
        Expr::BuiltIn(name, right)       => result.push_str(&name),
        _ => {}
    }
    result
}

//////////////////////////////
//                          //
//            TESTS         //
//                          //
//////////////////////////////

#[test]
fn util_test() {
    //Boolean
    assert_eq!(boolean("true".as_bytes()), IResult::Done(&b""[..], true));
    assert_eq!(boolean("false".as_bytes()), IResult::Done(&b""[..], false));

    //Integer
    assert_eq!(integer("10".as_bytes()), IResult::Done(&b""[..], 10));
    assert_eq!(integer("-1".as_bytes()), IResult::Done(&b""[..], -1));

    //Float
    assert_eq!(float("2.5".as_bytes()), IResult::Done(&b""[..], 2.5)); 
    assert_eq!(float("-3.14".as_bytes()), IResult::Done(&b""[..], -3.14));

    //String
    assert_eq!(string("'Hello World'".as_bytes()), IResult::Done(&b""[..], "Hello World"));
    assert_eq!(string("\"Special chars @#%?!\"".as_bytes()), IResult::Done(&b""[..], "Special chars @#%?!")); 
}

#[test]
fn query_test() {
    assert_eq!(pgql_query("select s.name where s.position = \"Access\"".as_bytes()), IResult::Done(&b""[..],
        Query{ 
            select: vec![Expr::Attribute(Attribute{name:"s".into(), field:"name".into()})],
            vvhere: vec![
                Expr::Equal(Box::new(Expr::Attribute(Attribute{name:"s".into(), field:"position".into()})),
                Box::new(Expr::Literal(Literal::Str("Access".into()))))
            ]}));

    assert_eq!(pgql_query("select s.name, s.status where s.age < 40".as_bytes()), IResult::Done(&b""[..],
        Query{ 
            select: vec![Expr::Attribute(Attribute{name:"s".into(), field:"name".into()}),
                         Expr::Attribute(Attribute{name:"s".into(), field:"status".into()})],
            vvhere: vec![
                Expr::Smaller(Box::new(Expr::Attribute(Attribute{name:"s".into(), field:"age".into()})),
                Box::new(Expr::Literal(Literal::Integer(40))))
            ]}));

    assert_eq!(pgql_query("select n.name, m.name where (n) -[e with e.type = \"Hosting\"]-> (m)".as_bytes()), IResult::Done(&b""[..],
        Query{ 
            select: vec![Expr::Attribute(Attribute{name:"n".into(), field:"name".into()}),
                         Expr::Attribute(Attribute{name:"m".into(), field:"name".into()})],
            vvhere: vec![Expr::PathPattern(Connection{
                source: Vertex{name:"n".into(), anonymous:false, constraints: vec![]},
                target: Vertex{name:"m".into(), anonymous:false, constraints: vec![]},
                edge: Edge{name:"e".into(), inverted: false, constraints: vec![
                    Expr::Equal(Box::new(Expr::Attribute(Attribute{name:"e".into(), field:"type".into()})),
                    Box::new(Expr::Literal(Literal::Str("Hosting".into()))))
                    ]}})]
            }));
}


#[test]
fn expr_test() {
    assert_eq!(expression("true and false".as_bytes()), IResult::Done(&b""[..],
        Expr::And(Box::new(Expr::Literal(Literal::Boolean(true))), Box::new(Expr::Literal(Literal::Boolean(false))))));

    assert_eq!(expression("false or true".as_bytes()), IResult::Done(&b""[..],
        Expr::Or(Box::new(Expr::Literal(Literal::Boolean(false))), Box::new(Expr::Literal(Literal::Boolean(true))))));

    assert_eq!(expression("10 + 5".as_bytes()), IResult::Done(&b""[..],
        Expr::Add(Box::new(Expr::Literal(Literal::Integer(10))), Box::new(Expr::Literal(Literal::Integer(5))))));

    assert_eq!(expression("10 - 5".as_bytes()), IResult::Done(&b""[..],
        Expr::Sub(Box::new(Expr::Literal(Literal::Integer(10))), Box::new(Expr::Literal(Literal::Integer(5))))));

    assert_eq!(expression("10 * 5".as_bytes()), IResult::Done(&b""[..],
        Expr::Mul(Box::new(Expr::Literal(Literal::Integer(10))), Box::new(Expr::Literal(Literal::Integer(5))))));

    assert_eq!(expression("10 / 5".as_bytes()), IResult::Done(&b""[..],
        Expr::Div(Box::new(Expr::Literal(Literal::Integer(10))), Box::new(Expr::Literal(Literal::Integer(5))))));

    assert_eq!(expression("10 % 5".as_bytes()), IResult::Done(&b""[..],
        Expr::Modulo(Box::new(Expr::Literal(Literal::Integer(10))), Box::new(Expr::Literal(Literal::Integer(5))))));

    assert_eq!(expression("10 > 5".as_bytes()), IResult::Done(&b""[..],
        Expr::Greater(Box::new(Expr::Literal(Literal::Integer(10))), Box::new(Expr::Literal(Literal::Integer(5))))));

    assert_eq!(expression("10.1 >= 5.1".as_bytes()), IResult::Done(&b""[..],
        Expr::GreaterEq(Box::new(Expr::Literal(Literal::Float(10.1))), Box::new(Expr::Literal(Literal::Float(5.1))))));
        
    assert_eq!(expression("5 < 10".as_bytes()), IResult::Done(&b""[..],
        Expr::Smaller(Box::new(Expr::Literal(Literal::Integer(5))), Box::new(Expr::Literal(Literal::Integer(10))))));
           
    assert_eq!(expression("5.1 <= 10.1".as_bytes()), IResult::Done(&b""[..],
        Expr::SmallerEq(Box::new(Expr::Literal(Literal::Float(5.1))), Box::new(Expr::Literal(Literal::Float(10.1))))));
                
    assert_eq!(expression("10 != 5".as_bytes()), IResult::Done(&b""[..],
        Expr::NotEqual(Box::new(Expr::Literal(Literal::Integer(10))), Box::new(Expr::Literal(Literal::Integer(5))))));

    
}

#[test]
fn vertex_test() {
    assert_eq!(query_vertex("()".as_bytes()), IResult::Done(&b""[..],
        Vertex {name: String::from(""), anonymous: true, constraints: Vec::new()} ));

    assert_eq!(query_vertex("(v)".as_bytes()), IResult::Done(&b""[..],
        Vertex {name: String::from("v"), anonymous: false, constraints: Vec::new()} ));
}

#[test]
fn edge_test() {
    assert_eq!(query_edge("->".as_bytes()), IResult::Done(&b""[..],
        Edge {name: String::from(""), inverted: false, constraints: Vec::new()} ));

    assert_eq!(query_edge("<-".as_bytes()), IResult::Done(&b""[..],
        Edge {name: String::from(""), inverted: true, constraints: Vec::new()} ));
}