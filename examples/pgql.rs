
#[macro_use]
extern crate nom;
extern crate rand;
extern crate timely;
extern crate differential_dataflow;
#[macro_use]
extern crate abomonation;
#[macro_use] extern crate abomonation_derive;



use abomonation::{encode, decode, Abomonation};

use rand::{Rng, SeedableRng, StdRng};
use std::time::Instant;

use timely::dataflow::*;
use timely::dataflow::operators::*;

use differential_dataflow::Collection;
use differential_dataflow::operators::*;
use differential_dataflow::lattice::Lattice;

use nom::{IResult, space, alpha, digit, Err};
use std::str;
use std::str::FromStr;
use std::fmt::{self, Formatter, Display};
use std::fs::File;
use std::io::prelude::*;
use std::error::Error;
use std::collections::HashMap;
use std::cmp::Ordering;

//////////////////////////////
//                          //
//       QUERYTYPES         //
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

#[derive(Debug,PartialEq)]
pub enum Constraint{
    Expr(Expr),
    PathPattern(Connection),
}


#[derive(Debug,PartialEq)]
pub struct Connection {
    source: Vertex,
    target: Vertex,
    edge: Edge2,
}

#[derive(Debug, PartialEq)]
pub struct Edge2 {
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

#[derive(Debug)]
pub struct Query {
    select: Vec<Expr>,
    vvhere: Vec<Constraint>,
}

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

//////////////////////////////
//                          //
//            TYPES         //
//                          //
//////////////////////////////

#[derive(Debug, Clone, PartialEq)]
pub struct Node{
    id: i32,
    label: Vec<String>,
    attribute_values: HashMap<String, Literal>,
}

#[derive(Debug, Clone, Abomonation)]
pub struct TimelyNode{
    id: i32,
    label: Vec<String>,
    attribute_values: Vec<(String, Literal)>,
}

impl From<Node> for TimelyNode {
    fn from(data: Node) -> Self {
        TimelyNode {
            id: data.id,
            label: data.label,
            attribute_values: data.attribute_values.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
        }
    }
}

impl From<TimelyNode> for Node {
    fn from(data: TimelyNode) -> Self {
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

/*impl PartialEq for TimelyNode {
    fn eq(&self, other: &TimelyNode) -> bool {
        self.id == other.id
    }
}

impl PartialOrd for TimelyNode {
    fn partial_cmp(&self, other: &TimelyNode) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TimelyNode{
    fn cmp(&self, other: &TimelyNode) -> Ordering {
        self.id.cmp(&other.id)
    }
}*/

macro_rules! try_option {
    ($expr:expr) => (match $expr {
        Some(val) => val,
        None => { return None }
    })
}

type TimelyEdge = (i32, i32);


#[derive(Debug, PartialEq)]
pub struct Edge{
    source: i32,
    target: i32,
    label: String,    
    attribute_values: HashMap<String, Literal>,
}

#[derive(Debug)]
pub struct DiffEdge{
    source: Node,
    target: Node,
    label: String,    
    attribute_values: HashMap<String, Literal>,
}

#[derive(Debug)]
pub struct Graph{
    nodes: Vec <Node>,
    edges: Vec <Edge>,
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

    fn greaterEq(&self, other: Literal) -> Literal {
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

    fn smallerEq(&self, other: Literal) -> Literal {
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
//            UTIL          //
//                          //
//////////////////////////////


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

named!(edge<Edge>,
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
            Edge {source: source, target: target, label:String::from(label), attribute_values: map }
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

    //println!("{:?}", evaluate2());
    let edge_filepath: String = std::env::args().nth(1).unwrap();

    // define a new computational scope, in which to run BFS
    timely::execute_from_args(std::env::args().skip(1), move |computation| {

        let timer = Instant::now();

        // logic goes here
        let (mut graph, mut query, mut vertices, probe) = computation.scoped(|scope| {

            // handle to push pgql queries
            let (query_input, query) = scope.new_input();

            let (vertex_input, vertices) = scope.new_input();

            // handle to push edges into the system
            let (edge_input, graph) = scope.new_input();

/*

            let plan = transformAST(
&vec![Constraint::PathPattern(
Connection{source : Vertex {name: "u".into(), anonymous: false, constraints: vec![]},
target: Vertex {name: "v".into(), anonymous: false, constraints:vec![]},
edge: Edge2 { name: "".into(), inverted: false, constraints: vec![] }}),
Constraint::Expr(
Expr::Smaller(Box::new(Expr::Attribute(Attribute { name: "v".into(), variable: "age".into() })),
 Box::new(Expr::Literal(Literal::Float(30.0))))),
Constraint::Expr(
Expr::Greater(Box::new(Expr::Attribute(Attribute { name: "v".into(), variable: "age".into() })),
 Box::new(Expr::Literal(Literal::Float(10.0))))),
Constraint::Expr(
Expr::Smaller(Box::new(Expr::Attribute(Attribute { name: "u".into(), variable: "age".into() })),
 Box::new(Expr::Literal(Literal::Float(60.0))))),
Constraint::Expr(
Expr::Greater(Box::new(Expr::Attribute(Attribute { name: "u".into(), variable: "age".into() })),
 Box::new(Expr::Literal(Literal::Float(40.0)))))
]);
            println!("{:?}", plan); */
            
let cons = &vec![Constraint::PathPattern(Connection{source : Vertex {name: "u".into(), anonymous: false, constraints: vec![]},

target: Vertex {name: "v".into(), anonymous: false, constraints: vec![
]}
,
edge: Edge2 { name: "".into(), inverted: false, constraints: vec![] }}),Constraint::Expr(

Expr::Smaller(Box::new(Expr::Attribute(Attribute { name: "v".into(), variable: "age".into() })), Box::new(Expr::Literal(Literal::Float(30.0))))), Constraint::Expr(

Expr::Greater(Box::new(Expr::Attribute(Attribute { name: "u".into(), variable: "age".into() })), Box::new(Expr::Literal(Literal::Float(10.0)))))
];
/*let plan2 = exploreExpr(
    Expr::Equal(Box::new(
        Expr::Attribute(Attribute { name: "v".into(), variable: "age".into() })), Box::new(Expr::Literal(Literal::Float(30.0)))));
println!("{:?}", plan2);         */    



            let (probe, output) = evaluate(&Collection::new(graph), &Collection::new(query),
             &Collection::new(vertices), cons).probe();
            output.inspect(|&(ref x,_)| println!("{:?}", x));
            (edge_input, query_input, vertex_input, probe)
        });

        if computation.index() == 0 { // this block will be executed by worker/thread 0
            
            query.send(("select v.name".into(),1));
            let mut file = File::open(&edge_filepath).unwrap();
            let mut s = String::new();
             
            match file.read_to_string(&mut s) {
                Err(error) => panic!("Couldn't read file {}: {}", edge_filepath,
                                                           error.description()),
                Ok(_) => println!("{} successfully opened\n", edge_filepath),
            }


            // Parse the input
            let result = graph_parser(s.as_bytes());

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
            println!("loaded; elapsed: {:?}", timer.elapsed());
        }

        // advance epoch
        query.advance_to(1);
        graph.advance_to(1);
        vertices.advance_to(1);
        // do the job
        computation.step_while(|| probe.lt(graph.time()));


        //if computation.index() == 0 {
          //  println!("stable; elapsed: {:?}", timer.elapsed());
        //}

    }).unwrap();


}

fn exploreExpr(expr: Expr) -> String {
    let mut result:String = "".into();
    match expr {
        Expr::Attribute(attribute)       => result.push_str(&attribute.name),
        Expr::Equal(left, right)         => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},        
        Expr::NotEqual(left, right)      => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::Smaller(left, right)       => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::SmallerEq(left, right)     => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::Greater(left, right)       => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::GreaterEq(left, right)     => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::Like(left, right)          => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::And(left, right)           => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::Or(left, right)            => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::Not(value)                 => result.push_str(&exploreExpr(*value)),
        Expr::Add(left, right)           => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::Sub(left, right)           => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::Mul(left, right)           => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::Div(left, right)           => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        Expr::Modulo(left, right)        => {result.push_str(&exploreExpr(*left)); result.push_str(&exploreExpr(*right));},
        _ => {}
    }
    result
}

fn transformAST (constraints: &Vec<Constraint>) -> Plan
{

    let mut selections: HashMap<String, Vec<Expr> > = HashMap::new();
    let mut plans = HashMap::new();
    let mut connections = Vec::new();

    for constraint in constraints{
        match constraint {
            &Constraint::PathPattern(ref pattern) => connections.push(pattern),
            &Constraint::Expr(ref expr) => {
                let name = exploreExpr((*expr).clone());
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
}


fn evaluate<G: Scope>(edges: &Collection<G, TimelyEdge>,  queries: &Collection<G, String>, vertices: &Collection<G, TimelyNode>,
    constraints: &Vec<Constraint>) -> Collection<G, TimelyEdge> where G::Timestamp: Lattice {


    let mut selections : HashMap<String, Vec<Expr> > = HashMap::new();
    //let mut plans = HashMap::new();
    let mut connections = Vec::new();

    for constraint in constraints{
        match constraint {
            &Constraint::PathPattern(ref pattern) => connections.push(pattern),
            &Constraint::Expr(ref expr) => {
                let name = exploreExpr((*expr).clone());
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
        let myfilter= (*filter).clone();
        /*let plan = vertices.filter(move |x| {
            let s = (*x).clone();
            check_node(&(s.into()),  filter         )
        });
        plans.insert(name, plan);*/
    }
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

    /*let mut result;
    match plan.operator {
        Op::Filter => {result =  vertices.filter(|x| {
                                let s = (*x).clone();
                                check_node(&(s.into()), plan.filter.unwrap() )})},
        Op::Join => {},
        Op::Map => {},
    }*/

    //let &(ref source, ref target) = x;

    /*vec![Expr::Attribute(Attribute{name:"s".into(), variable:"name".into()}),
                     Expr::Attribute(Attribute{name:"s".into(), variable:"age".into()})],

    for attr in query.select {
            match attr {
                Expr::Attribute(attribute) => println!("{:?}", node.attribute_values.get(&attribute.variable)),
                _ => println!("failure")
            }*/

    edges.filter(|x| {
        let &(ref source, ref target) = x;
        true
        //(roots.contains(source) && destinations.contains(target))
    })
}



fn reach (){
    /*let roots =     vertices.filter(|x| {
        let s = (*x).clone();
        checkNode(&(s.into()), 
            vec![Expr::Smaller(Box::new(Expr::Attribute(Attribute{name:"s".into(), variable:"ram".into()})),
                Box::new(Expr::Literal(Literal::Float(5f32))))]
            )})//.map(|x| (x.id, x.id));
    
    let destinations = vertices.filter(|x| {
        let s = (*x).clone();
        checkNode(&(s.into()), 
            vec![Expr::Greater(Box::new(Expr::Attribute(Attribute{name:"s".into(), variable:"ram".into()})),
                Box::new(Expr::Literal(Literal::Float(10.5))))]
            )}).map(|x| (x.id, x.id));

    roots.iterate(|inner| {

        let edges = edges.enter(&inner.scope());
        let roots = roots.enter(&inner.scope());

        inner.join_map(&edges, |_k,&l,&d| (d, l))
             .concat(&roots)
             .distinct()
     })*/
}


fn check_node (node: &Node, constraints: &Vec<Expr>) -> bool {
    let mut result = true;
    for constraint in constraints {
        let boolean = match evaluate_expr((*constraint).clone(), node) {
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
        Expr::SmallerEq(left, right)     => evaluate_expr(*left, node).smallerEq(evaluate_expr(*right, node)),
        Expr::Greater(left, right)       => evaluate_expr(*left, node).greater(evaluate_expr(*right, node)),
        Expr::GreaterEq(left, right)     => evaluate_expr(*left, node).greaterEq(evaluate_expr(*right, node)),
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