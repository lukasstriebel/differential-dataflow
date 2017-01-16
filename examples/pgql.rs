#[macro_use]
extern crate nom;
extern crate rand;
extern crate timely;
extern crate differential_dataflow;
#[macro_use]
extern crate abomonation;

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

//////////////////////////////
//                          //
//       QUERYTYPES         //
//                          //
//////////////////////////////

#[derive(Debug)]
pub struct Query {
    select: Vec<Expr>,
    vvhere: Vec<Expr>,
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct Attribute { 
    name: String,
    variable: String,
}

//////////////////////////////
//                          //
//            TYPES         //
//                          //
//////////////////////////////

#[derive(Debug, Clone)]
pub struct Node{
    id: i32,
    label: Vec<String>,
    attribute_values: HashMap<String, Literal>,
}

#[derive(Debug, Clone)]
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

macro_rules! try_option {
    ($expr:expr) => (match $expr {
        Some(val) => val,
        None => { return None }
    })
}

type EdgeTest = (TimelyNode, TimelyNode);


#[derive(Debug)]
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

#[derive(Debug,PartialEq, Clone)]
pub enum Literal {
  Str(String),
  Float(f32),
  Boolean(bool),
  Integer(i32),
}


impl Abomonation for Literal {
    #[inline] unsafe fn embalm(&mut self) {
        if let &mut Literal::Integer(ref mut inner) = self {
            inner.embalm();
        }
        if let &mut Literal::Str(ref mut inner) = self {
            inner.embalm();
        }
        if let &mut Literal::Float(ref mut inner) = self {
            inner.embalm();
        }
        if let &mut Literal::Boolean(ref mut inner) = self {
            inner.embalm();
        }
    }

    #[inline] unsafe fn entomb(&self, bytes: &mut Vec<u8>) {
        if let &Literal::Integer(ref inner) = self {
            inner.entomb(bytes);
        }
        if let &Literal::Str(ref inner) = self {
            inner.entomb(bytes);
        }
        if let &Literal::Float(ref inner) = self {
            inner.entomb(bytes);
        }
        if let &Literal::Boolean(ref inner) = self {
            inner.entomb(bytes);
        }
    }

    #[inline] unsafe fn exhume<'a, 'b>(&'a mut self, mut bytes: &'b mut[u8]) -> Option<&'b mut [u8]> {
        if let &mut Literal::Integer(ref mut inner) = self {
            let tmp = bytes; bytes = try_option!(inner.exhume(tmp));
        }
        if let &mut Literal::Str(ref mut inner) = self {
            let tmp = bytes; bytes = try_option!(inner.exhume(tmp));
        }
        if let &mut Literal::Float(ref mut inner) = self {
            let tmp = bytes; bytes = try_option!(inner.exhume(tmp));
        }
        if let &mut Literal::Boolean(ref mut inner) = self {
            let tmp = bytes; bytes = try_option!(inner.exhume(tmp));
        }
        Some(bytes)
    }
}

unsafe_abomonate!(TimelyNode: id, label, attribute_values);


#[derive(PartialEq, Eq, Hash,Debug)]
pub enum Type {
    Str,
    Float,
    Boolean,
    Integer,
}


//////////////////////////////
//                          //
//            UTIL          //
//                          //
//////////////////////////////





named!(literal<Literal>,
    alt_complete!(       
        float       => { |f| Literal::Float(f)             } |
        integer     => { |i| Literal::Integer(i)           } | 
        boolean     => { |b| Literal::Boolean(b)           } |
        string      => { |s| Literal::Str(String::from(s)) } 
            
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
        )
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
    sign.and_then(|s| if s[0] == ('-' as u8) { Some(-1f32) } else { None }).unwrap_or(1f32) * value
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


named!(unsigned_int<i32>,
    map_res!(
        map_res!(
            digit,
            str::from_utf8
        ),
        FromStr::from_str
    )
);

named!(integer<i32>, map!(
  pair!(
    opt!(alt!(tag!("+") | tag!("-"))),
    unsigned_int
  ),
  |(sign, value): (Option<&[u8]>, i32)| {
    sign.and_then(|s| if s[0] == ('-' as u8) { Some(-1i32) } else { None }).unwrap_or(1i32) * value
  }
));

named!(line_end, alt!(tag!("\r\n") | tag!("\n")));


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


    let edge_filepath: String = std::env::args().nth(1).unwrap();

    // define a new computational scope, in which to run BFS
    timely::execute_from_args(std::env::args().skip(1), move |computation| {

        let timer = Instant::now();

        // logic goes here
        let (mut graph, mut query, probe) = computation.scoped(|scope| {

            // handle to push pgql queries
            let (query_input, query) = scope.new_input();

            // handle to push edges into the system
            let (edge_input, graph) = scope.new_input();

            let probe = evaluate(&Collection::new(graph), &Collection::new(query)).probe().0;
            
            (edge_input, query_input, probe)
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
                    
                    for elem in value.edges{
                        // Assemble actual Edges
                        let source:Node = value.nodes[elem.source as usize -1].clone();
                        let target:Node = value.nodes[elem.target as usize -1].clone();

                        //println!("{:?} -> \n {:?}\n",source,target); 
                        

                        graph.send(((source.into(),target.into()),1));
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
        // do the job
        computation.step_while(|| probe.lt(graph.time()));

        //if computation.index() == 0 {
          //  println!("stable; elapsed: {:?}", timer.elapsed());
        //}

    }).unwrap();


}

fn evaluate<G: Scope>(edges: &Collection<G, EdgeTest>, queries: &Collection<G, String>) -> Collection<G, EdgeTest>
where G::Timestamp: Lattice {


    edges.filter(|x| {true})

    // Step 0: translate query into a dataflow

    // Step 1: evaluate query on the graph

}

fn evaluate2<G: Scope>(edges: &Collection<G, EdgeTest>, queries: &Collection<G, String>) -> String
where G::Timestamp: Lattice {

    //FIXME: Use non-retarded way to access elements (if there is one, which seems unlikely.....)
    let x = queries.map(|query| {
        //println!("{:?}", query);
        (1)}
        );



    let query = Query{ 
            select: vec![Expr::Attribute(Attribute{name:"s".into(), variable:"name".into()}),
                         Expr::Attribute(Attribute{name:"s".into(), variable:"status".into()})],
            vvhere: vec![
                Expr::Smaller(Box::new(Expr::Attribute(Attribute{name:"s".into(), variable:"age".into()})),
                Box::new(Expr::Literal(Literal::Integer(40))))
            ]};

    
    for condition in query.vvhere {
        match condition{
            //Expr::Equal(x,y) => {f = |some| some == y;},
            _ => {}
        }
        //edges = edges.filter(|x|)
    }
    let mut result;
    edges.map(|x| {
        let (a,b) = x;
        let mut fulfills = true;
        for condition in query.vvhere {
        match condition{
            Expr::Equal(x,y) => {fulfills = a.attribute_values[0] == into_raw(y);},
            _ => {fulfills = false;}
        }
        if fulfills {
            result = a;
        }
        //edges = edges.filter(|x|)
    }
        (1)
    });
    "hi".into()

    // Step 0: translate query into a dataflow

    // Step 1: evaluate query on the graph

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