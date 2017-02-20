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

use nom::{IResult, space, alpha, digit, Err};

use std::time::Instant;
use std::str;
use std::str::FromStr;
use std::fmt::{self, Formatter, Display};
use std::fs::File;
use std::io::prelude::*;
use std::error::Error;
use std::collections::HashMap;
use std::collections::HashSet;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

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
}


#[derive(Debug, PartialEq, Clone)]
pub struct Attribute { 
    name: String,
    variable: String,
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

#[derive(Debug,PartialEq, Clone, Abomonation)]
pub enum Literal {
  Str(String),
  Float(f32),
  Boolean(bool),
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
                    _ => panic!("Greater with non arithmetic value")
                }
            },
             _ => panic!("Greater with non arithmetic value") 
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
}
//////////////////////////////
//                          //
//      TYPES QUERY         //
//                          //
//////////////////////////////

#[derive(Debug)]
pub struct Query {
    select: Vec<Expr>,
    vvhere: Vec<Constraint>,
}

#[derive(Debug,PartialEq)]
pub enum Constraint{
    Expr(Expr),
    PathPattern(Connection),
}


#[derive(Debug,PartialEq)]
pub struct Connection {
    source: Vertex,
    target: Vertex,
    edge: Edge,
}

#[derive(Debug, PartialEq)]
pub struct Edge {
    name: String,
    inverted: bool,
    constraints: Vec<Expr>,
}

#[derive(Debug,PartialEq)]
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


#[derive(Debug)]
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
pub enum Aggregate {
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

#[derive(Debug, Clone)]
struct Plan {
   operator: Op,

   left: Option<Box<Plan> >,
   right: Option<Box<Plan> >,


   filter: Option<Vec<Expr> >,
   join_left: Option<String>,
   join_right: Option<String>,
   //elation_names: Vec<String>,
   map: Option<Attribute>,
}
#[derive(Debug,PartialEq,Clone)]
enum Op {
    Filter,
    Map,
    Join,
}
#[derive(Debug)]
struct PhyPlan{
    name: Vec<String>,
    left: String,
    right: String,
    join_id: usize,
    join: bool,
    filter_id: usize,
}

#[derive(Debug, Clone, Abomonation)]
pub struct DifferentialVertex{
    id: i32,
    label: Vec<String>,
    attribute_values: Vec<(String, Literal)>,
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

#[derive(Debug)]
pub struct DiffEdge{
    source: Node,
    target: Node,
    label: String,    
    attribute_values: HashMap<String, Literal>,
}

//////////////////////////////
//                          //
//          QUERY           //
//                          //
//////////////////////////////



/*named!(pgql_query<Query>,
    chain!(
        select: select_clause ~
        space ~
        vvhere: where_clause ,
        //opt!(solutionModifier),
        || Query { select: select, vvhere: vvhere}
    )
);*/

named!(pgql_query<Query>, 
    do_parse!(
        select: select_clause >>
        space >>
        vvhere: where_clause >>
        //opt!(solutionModifier),
        (Query { select: select, vvhere: vvhere})
    )
);

//////////////////////////////
//                          //
//          SELECT          //
//                          //
//////////////////////////////


named!(select_clause<Vec<Expr> >,
    chain!( 
        tag_no_case_s!("select") ~
        space ~
        a: select_elems,
        || a
    )
);


named!(select_elems<Vec<Expr> >,
    many1!(
        alt_complete!(
            /*aggregate => {|aggregation| 
                        Expr::Aggregation(aggregation)} |*/
            do_parse!(
                v: variable_name >>
                char!(',') >>
                opt!(space) >> ({
                    let (name, variable) = v;
                        let a = Attribute{name: name, variable: variable};
                        Expr::Attribute(a)})
            )  
            | variable_name => {|v| {let (name, variable) = v;
                        let a = Attribute{name: name, variable: variable};
                        Expr::Attribute(a)}}
           
            //| tag_s!("*")
        )
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


/*named!(pathPattern< Expr >,
    chain!(
        q: queryVertex ~
        space ~ 
        m: many0!(
            chain!(
                //qc: queryConnection ~
                qc: queryEdge ~
                space ~
                qv: queryVertex ~
                space?,
            || {Connection {source:q, target: qv}}
            )
        ), 
        || Expr::PathPattern(m)
    )
);*/

named!(path_pattern< Connection >,
    chain!(
        source: query_vertex ~
        space ~ 
        edge: query_edge ~
        space ~
        target: query_vertex, 
        || Connection{source: source, target: target, edge: edge}
    )
);



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
                        let (name, variable) = v;
                        let a = Attribute{name: name, variable: variable};
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
        alt!(
                literal => {|l| Expr::Literal(l) } |
                variable_name => {
                    |value| {
                        let (name, variable) = value;
                        let attribute = Attribute{name: name, variable: variable};
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




named!(aggregate<Aggregate>,
    alt_complete!(
        do_parse!(
            tag_no_case_s!("count") >>
            variable_name: delimited!(tag!("("), variable_name, tag!(")")) >>
            ({
                let (name, variable) = variable_name;
                let attribute = Attribute{name: name, variable: variable};
                Aggregate::Count(attribute)
            })
            ) |
        do_parse!(
            tag_no_case_s!("min") >>
            variable_name: delimited!(tag!("("), variable_name, tag!(")")) >>
            ({
                let (name, variable) = variable_name;
                let attribute = Attribute{name: name, variable: variable};
                Aggregate::Min(attribute)
            })
            ) |
        do_parse!(
            tag_no_case_s!("max") >>
            variable_name: delimited!(tag!("("), variable_name, tag!(")")) >>
            ({
                let (name, variable) = variable_name;
                let attribute = Attribute{name: name, variable: variable};
                Aggregate::Max(attribute)
            })
            ) |
        do_parse!(
            tag_no_case_s!("sum") >>
            variable_name: delimited!(tag!("("), variable_name, tag!(")")) >>
            ({
                let (name, variable) = variable_name;
                let attribute = Attribute{name: name, variable: variable};
                Aggregate::Sum(attribute)
            })
            ) |
        do_parse!(
            tag_no_case_s!("avg") >>
            variable_name: delimited!(tag!("("), variable_name, tag!(")")) >>
            ({
                let (name, variable) = variable_name;
                let attribute = Attribute{name: name, variable: variable};
                Aggregate::Avg(attribute)
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



named!(solution_modifier<(GroupBy, OrderBy, (i32, i32))>,
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

    let query_filepath: String = std::env::args().nth(2).unwrap();

    // define a new computational scope, in which to run the query
    timely::execute_from_args(std::env::args().skip(2), move |computation| {

        let timer = Instant::now();

        // logic goes here
        let (mut graph, mut query, mut vertices, probe) = computation.scoped(|scope| {

            // handle to push pgql queries
            let (query_input, query) = scope.new_input();

            let (vertex_input, vertices) = scope.new_input();

            // handle to push edges into the system
            let (edge_input, graph) = scope.new_input();

            let (probe, output) = evaluate(&Collection::new(graph), &Collection::new(query), &Collection::new(vertices)).probe();
            (edge_input, query_input, vertex_input, probe)
        });

        if computation.index() == 0 { // this block will be executed by worker/thread 0
            
            let mut file = File::open(&graph_filepath).unwrap();
            let mut string = String::new();
             
            match file.read_to_string(&mut string) {
                Err(error) => panic!("Couldn't read file {}: {}", graph_filepath,
                                                           error.description()),
                Ok(_) => println!("Graph File {} successfully opened\n", graph_filepath),
            }

            // Parse the input
            let result = graph_parser(string.as_bytes());

            file = File::open(&query_filepath).unwrap();
            let mut query_string = String::new();

            match file.read_to_string(&mut query_string) {
                Err(error) => panic!("Couldn't read file {}: {}", query_filepath,
                                                           error.description()),
                Ok(_) => println!("Query File {} successfully opened\n", query_filepath),
            }
            query.send((query_string,1));


            match result {
                IResult::Done(_, value) => {
                    
                    for elem in value.nodes{
                        vertices.send((elem.into(),1));
                    }

                    for elem in value.edges{
                        graph.send(((elem.source,elem.target),1));
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
                _ => println!("{:?}", result)
            }
        }

        // advance epoch
        query.advance_to(1);
        graph.advance_to(1);
        vertices.advance_to(1);
        // do the job
        computation.step_while(|| probe.lt(graph.time()));


        if computation.index() == 0 {
            println!("stable; elapsed: {:?}", timer.elapsed());
        }

    }).unwrap();


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
        _ => {}
    }
    result
}

/*fn transformAST (constraints: &Vec<Constraint>) -> Plan
{

    let mut selections: HashMap<String, Vec<Expr> > = HashMap::new();
    let mut plans = HashMap::new();
    let mut connections = Vec::new();

    for constraint in constraints{
        match constraint {
            &Constraint::PathPattern(ref pattern) => connections.push(pattern),
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

    for selection in selections.iter() {
        let (name, filter) = selection;
        let plan = create_selection((*filter).clone());
        plans.insert(name, plan);
    }

    let mut result = None;

    for connection in connections {
        //let name = vec![left, right];
        let left: Option<Box<Plan> > = match plans.get(&connection.source.name){
            Some(plan) => (*plan).clone(),
            None => None,
        };

        let right: Option<Box<Plan> > = match plans.get(&connection.target.name){
            Some(plan) => (*plan).clone(),
            None => None,
        };
        
        result = create_join(left, right);
    }

    (*(result.unwrap()))            
}


fn create_selection (constraints: Vec<Expr>) -> Option<Box<Plan> >{
    Some(
            Box::new(
                Plan {
                    operator: Op::Filter,
                    left: None,
                    right: None,
                    filter: Some(constraints),
                    join_left: None,
                    join_right: None,
                    map: None
                    }
                )
            )
}


fn create_join ( left: Option<Box<Plan> >, right: Option<Box<Plan> > ) -> Option<Box<Plan> >{
    Some(
        Box::new(
            Plan {
                operator: Op::Join,
                left: left,
                right: right,
                filter: None,
                join_left: None,
                join_right: None,
                map: None
                }
            )
        )
}*/

fn test(s:&[u8]) -> i32{1}


fn evaluate<G: Scope>(edges: &Collection<G, DifferentialEdge>,  queries: &Collection<G, String>,
    vertices: &Collection<G, DifferentialVertex>) -> Collection<G, DifferentialEdge> where G::Timestamp: Lattice {

/*let constraints = &vec![Constraint::PathPattern(
    Connection{source : Vertex {name: "v".into(), anonymous: false, constraints: vec![]},
target: Vertex {name: "u".into(), anonymous: false, constraints: vec![
]},edge: Edge { name: "".into(), inverted: false, constraints: vec![] }}),
Constraint::PathPattern(Connection{source : Vertex {name: "u".into(), anonymous: false, constraints: vec![]},

target: Vertex {name: "w".into(), anonymous: false, constraints: vec![
]},

edge: Edge { name: "".into(), inverted: false, constraints: vec![] }}),
Constraint::Expr(
Expr::Smaller(Box::new(Expr::Attribute(Attribute { name: "v".into(), variable: "ram".into() })),
    Box::new(Expr::Literal(Literal::Float(5.0))))),
Constraint::Expr(
Expr::Greater(Box::new(Expr::Attribute(Attribute { name: "u".into(), variable: "ram".into() })),
    Box::new(Expr::Literal(Literal::Float(10.0))))),
Constraint::Expr(
Expr::Greater(Box::new(Expr::Attribute(Attribute { name: "w".into(), variable: "ram".into() })),
    Box::new(Expr::Literal(Literal::Float(30.0)))))
];*/

    
/*let mut query = 1;
queries.inspect(move |&(ref x,_)| {
    let s = (*x).clone();
   query = test(s.as_bytes());
});*/
let query = pgql_query("SELECT v.name WHERE (v) -> (u), (u) -> (v), v.ram < 5, u.ram > 10".as_bytes());



    /*let mut string = String::new();
    queries.inspect(move |&(ref x,_)| {string = x.clone(); s_slice = &string[..];});
    let query = pgql_query("SELECT v.name WHERE (v) -> (u), v.ram < 5, u.ram > 10".as_bytes());*/
    match query {
        IResult::Done(_, value) => {
            let mut connections = Vec::new();
            let mut selections : HashMap<String, Vec<Expr> > = HashMap::new();

            for constraint in &value.vvhere{
                match constraint {
                    &Constraint::PathPattern(ref pattern) => connections.push(pattern),
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

            let mut plans = HashMap::new();

            for (name, filter) in selections {
                let result = vertices.filter(move |x| {
                    check_node(&x, &filter)
                });
                plans.insert(name, result);
            }

            let mut execution_plan = Vec::new();
            let mut used_variables= HashSet::new();
            let mut names = HashMap::new();
            let mut ids :usize = 0;

            for connection in connections {
                if !used_variables.contains(&connection.source.name) {
                    used_variables.insert(&connection.source.name);
                    used_variables.insert(&connection.target.name);
                    names.insert(&connection.source.name, ids);
                    ids = ids + 1;
                    names.insert(&connection.target.name, ids);
                    ids = ids + 1;
                    execution_plan.push(
                        PhyPlan{ 
                            name: vec![connection.source.name.clone(), connection.target.name.clone()],
                            left: connection.source.name.clone(),
                            right: connection.target.name.clone(),
                            join_id: 0,
                            join: true,
                            filter_id: 100,
                        }
                    );
                }
                else if !used_variables.contains(&connection.target.name) {
                    used_variables.insert(&connection.target.name);
                    names.insert(&connection.target.name, ids);
                    ids = ids + 1;
                    execution_plan.push(
                        PhyPlan{ 
                            name: vec![connection.source.name.clone(), connection.target.name.clone()],
                            left: connection.source.name.clone(),
                            right: connection.target.name.clone(),
                            join_id: *names.get(&connection.source.name).unwrap(),
                            join: true,
                            filter_id: 100,
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
                        }
                    );
                }

            }
            //println!("{:?}", execution_plan);
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
                        result =  Some(sources.map(|x| (x.id, x)).join(edges)
                                    .map(|(k,v1,v2)| (v2,v1))
                                    .join(&targets.map(|x| (x.id, x)))
                                    .map(|(k,v1,v2)| vec![v1,v2]));
                }
                else if !step.join {
                    let int = step.join_id;
                    let int2 = step.filter_id;
                    result = Some(result.unwrap().map(move |x| (x[int].id, x))
                            .join(edges)
                            .filter(move |x| {let &(ref key, ref vec, ref id) = x; vec[int2].id == *id})
                            .map(|(k,v1,v2)| v1));

                }
                else {                 
                    let targets = match plans.get(&step.right){
                        Some(list) => list,
                        None => vertices,
                    };
                    result = Some(result.unwrap().map(move |vec| (vec[step.join_id].id, vec))
                            .join(edges)
                            .map(|(k,v1,v2)| (v2,v1))
                            .join(&targets.map(|x| (x.id, x)))
                            .map(|(k, mut v1,v2)| {v1.push(v2);v1}));   
                }
            }
            result.unwrap().inspect(|x| println!("{:?}", x ));


            /*let mut result = None;
            let mut counter = 0;
            for connection in connections {

                if counter == 0 {
                    let sources = match plans.get(&connection.source.name){
                        None => vertices,
                        Some(list) => list,
                    };
                    counter = counter + 1;

                    let targets = match plans.get(&connection.target.name){
                        Some(list) => list,
                        None => vertices,
                    };
                        result =  Some(sources.map(|x| (x.id, x)).join(edges)
                                    .map(|(k,v1,v2)| (v2,v1))
                                    .join(&targets.map(|x| (x.id, x)))
                                    .map(|(k,v1,v2)| (k, vec![v1,v2])));
                }

                else if counter == 2 {
                    let left = 0;
                    result = Some(result.unwrap().join(edges)
                            .filter(move |x| {let &(ref key, ref vec, ref id) = x; vec[left].id == *id}).map(|(k,v1,v2)| (v2,v1)));
                }

                else {
                    let id = counter;
                    println!("\nCurrent counter {:?}\n", counter);
                    let targets = match plans.get(&connection.target.name){
                        Some(list) => list,
                        None => vertices,
                    };
                    result =  Some(result.unwrap().map(move |(_,vec)| (vec[counter].id, vec)).join(edges)
                                    .map(|(k,v1,v2)| (v2,v1))
                                    .join(&targets.map(|x| (x.id, x)))
                                    .map(|(k, mut v1,v2)| {v1.push(v2);(k,v1)}));

                    counter = counter + 1;                                    
                }
                
            }
            result.unwrap().inspect(|x| println!("{:?}", x )); */       
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
    
    };
    
    

/*
    let mut result = None;

    for connection in connections {
        //let name = vec![left, right];
        let left: Option<Box<Plan> > = match plans.get(&connection.source.name){
            Some(plan) => (*plan).clone(),
            None => None,
        };

        let right: Option<Box<Plan> > = match plans.get(&connection.target.name){
            Some(plan) => (*plan).clone(),
            None => None,
        };
        
        result = create_join(left, right);
    }*/


    /*let project = vec![Expr::Attribute(Attribute{name:"v".into(), variable:"name".into()}),
                     Expr::Attribute(Attribute{name:"v".into(), variable:"age".into()})];

    for attr in project {
            match attr {
                Expr::Attribute(attribute) => println!("{:?}", node.attribute_values.get(&attribute.variable)),
                _ => println!("failure")
            }*/

    edges.filter(|x| {
        true
        //let &(ref source, ref target) = x;
    })
}


fn check_node (node: &DifferentialVertex, constraints: &Vec<Expr>) -> bool {
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
            match node.attribute_values.get(&attribute.variable) {
                Some(literal) => (*literal).clone(),
                None => panic!("Field {:?} does not exist!", &attribute.variable) }
            }
    }
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
            select: vec![Expr::Attribute(Attribute{name:"s".into(), variable:"name".into()})],
            vvhere: vec![
                Expr::Equal(Box::new(Expr::Attribute(Attribute{name:"s".into(), variable:"position".into()})),
                Box::new(Expr::Literal(Literal::Str("Access".into()))))
            ]}));

    assert_eq!(pgql_query("select s.name, s.status where s.age < 40".as_bytes()), IResult::Done(&b""[..],
        Query{ 
            select: vec![Expr::Attribute(Attribute{name:"s".into(), variable:"name".into()}),
                         Expr::Attribute(Attribute{name:"s".into(), variable:"status".into()})],
            vvhere: vec![
                Expr::Smaller(Box::new(Expr::Attribute(Attribute{name:"s".into(), variable:"age".into()})),
                Box::new(Expr::Literal(Literal::Integer(40))))
            ]}));

    assert_eq!(pgql_query("select n.name, m.name where (n) -[e with e.type = \"Hosting\"]-> (m)".as_bytes()), IResult::Done(&b""[..],
        Query{ 
            select: vec![Expr::Attribute(Attribute{name:"n".into(), variable:"name".into()}),
                         Expr::Attribute(Attribute{name:"m".into(), variable:"name".into()})],
            vvhere: vec![Expr::PathPattern(Connection{
                source: Vertex{name:"n".into(), anonymous:false, constraints: vec![]},
                target: Vertex{name:"m".into(), anonymous:false, constraints: vec![]},
                edge: Edge{name:"e".into(), inverted: false, constraints: vec![
                    Expr::Equal(Box::new(Expr::Attribute(Attribute{name:"e".into(), variable:"type".into()})),
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