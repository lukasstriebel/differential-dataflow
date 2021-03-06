//! The `arrange` operator is used internally by differential to arrange a collection of (key,val)
//! data by key, and present an Rc<Trace<..>> to other operators that need the data ArrangedByKey this way.
//!
//! The intent is that multiple users of the same data can share the resources needed to arrange and 
//! maintain the data. 

use std::rc::Rc;
use std::cell::RefCell;
use std::default::Default;
use std::ops::DerefMut;

use linear_map::LinearMap;

use timely::dataflow::*;
use timely::dataflow::operators::{Map, Unary};
use timely::dataflow::channels::pact::Exchange;
use timely_sort::{LSBRadixSorter, Unsigned};

use ::{Data, Collection};
use lattice::Lattice;
use collection::{Lookup, Trace, TraceRef};
use collection::basic::{BasicTrace, Offset};
use collection::count::Count;
use collection::compact::Compact;

/// A collection of `(K,V)` values as a timely stream and shared trace.
///
/// An `Arranged` performs the task of arranging a keyed collection once, 
/// allowing multiple differential operators to use the same trace. This 
/// saves on computation and memory, in exchange for some cognitive overhead
/// in writing differential operators: each must pay enough care to signals
/// from the `stream` field to know the subset of `trace` it has logically 
/// received.
pub struct Arranged<G: Scope, T: Trace<Index=G::Timestamp>> 
    where 
        T::Key: Data, 
        T::Value: Data, 
        G::Timestamp: Lattice ,
        for<'a> &'a T: TraceRef<'a, T::Key, T::Index, T::Value> 
        {
    /// A stream containing arranged updates.
    ///
    /// This stream may be reduced to just the keys, with the expectation that looking up the
    /// updated values in the associated trace should be more efficient than cloning the values.
    /// Users who need the values can obviously use the original stream.
    pub stream: Stream<G, (Vec<<T as Trace>::Key>, Vec<u32>, Vec<(<T as Trace>::Value, i32)>)>,
    /// A shared trace, updated by the `Arrange` operator and readable by others.
    pub trace: Rc<RefCell<T>>,
}

impl<G: Scope, T: Trace<Index=G::Timestamp>> Arranged<G, T> 
    where 
        T::Key: Data, 
        T::Value: Data, 
        G::Timestamp: Lattice ,
        for<'a> &'a T: TraceRef<'a, T::Key, T::Index, T::Value> 
    {
    
    /// Flattens the stream into a `Collection`.
    ///
    /// This operator is not obviously more efficient than using the `Collection` that is input
    /// to the `Arrange` operator. However, this may be the only way to recover a collection from 
    /// only the `Arranged` type.
    pub fn as_collection(&self) -> Collection<G, (T::Key, T::Value)> {
        Collection::new(
            self.stream.flat_map(|(keys, cnts, vals)| {

                let keys = keys.into_iter();
                let cnts = cnts.into_iter();
                let vals = vals.into_iter();

                keys.zip(cnts)
                    .flat_map(|(k,c)| (0..c).map(move |_| k.clone()))
                    .zip(vals)
                    .map(|(k,(v,w))| ((k,v),w))
            })
        )
    }
}

/// Arranges something as `(Key,Val)` pairs. 
pub trait ArrangeByKey<G: Scope, K: Data, V: Data> where G::Timestamp: Lattice {
    /// Arranges a stream of `(Key, Val)` updates by `Key`.
    ///
    /// This operator arranges a stream of values into a shared trace, whose contents it maintains.
    /// This trace is current for all times completed by the output stream, which can be used to
    /// safely identify the stable times and values in the trace.
    fn arrange_by_key<
        U:     Unsigned+Default,
        KH:    Fn(&K)->U+'static,
        Look:  Lookup<K, Offset>+'static,
        LookG: Fn(u64)->Look,
    >(&self, key_h: KH, look: LookG) -> Arranged<G, BasicTrace<K,G::Timestamp,V,Look>>;
}

impl<G: Scope, K: Data, V: Data> ArrangeByKey<G, K, V> for Collection<G, (K, V)> where G::Timestamp: Lattice {
    fn arrange_by_key<
        U:     Unsigned+Default,
        KH:    Fn(&K)->U+'static,
        Look:  Lookup<K, Offset>+'static,
        LookG: Fn(u64)->Look,
    >
    (&self, key_h: KH, look: LookG) -> Arranged<G, BasicTrace<K,G::Timestamp,V,Look>> {

        let peers = self.scope().peers();
        let mut log_peers = 0;
        while (1 << (log_peers + 1)) <= peers {
            log_peers += 1;
        }

        // create a trace to share with downstream consumers.
        let trace = Rc::new(RefCell::new(BasicTrace::new(look(log_peers))));
        let source = Rc::downgrade(&trace);

        // A map from times to received (key, val, wgt) triples.
        let mut inputs = LinearMap::new();

        // create an exchange channel based on the supplied Fn(&D1)->u64.
        let part1 = Rc::new(key_h);
        let part2 = part1.clone();
        let exch = Exchange::new(move |&((ref k, _),_): &((K,V),i32)| part1(k).as_u64());

        let mut sorter = LSBRadixSorter::new();

        // fabricate a data-parallel operator using the `unary_notify` pattern.
        let stream = self.inner.unary_notify(exch, "ArrangeByKey", vec![], move |input, output, notificator| {

            // 1. read each input, and stash it in our staging area
            input.for_each(|time, data| {
                inputs.entry_or_insert(time.time(), || { notificator.notify_at(time); Vec::new() })
                      .push(::std::mem::replace(data.deref_mut(), Vec::new()));                
            });

            // 2. for each complete time, sort out the received input.
            notificator.for_each(|index, _count, _notificator| {
                
                // 2a. fetch any data associated with this time.
                if let Some(mut queue) = inputs.remove_key(&index) {
                    // sort things; radix if many, .sort_by if few.
                    let compact = if queue.len() > 1 {
                        for element in queue.into_iter() {
                            sorter.push_batch(element, &|x| part2(&(x.0).0));
                        }

                        let mut sorted = sorter.finish(&|x| part2(&(x.0).0));
                        let result = Compact::from_radix(&mut sorted, &|k| part2(k));
                        sorted.truncate(256);
                        sorter.recycle(sorted);
                        result
                    }
                    else {
                        let mut vec = queue.pop().unwrap();
                        vec.sort_by(|x,y| part2(&(x.0).0).cmp(&part2((&(y.0).0))));
                        Compact::from_radix(&mut vec![vec], &|k| part2(k))
                    };


                    if let Some(compact) = compact {
                        output.session(&index).give((compact.keys.clone(), compact.cnts.clone(), compact.vals.clone()));
                        if let Some(trace) = source.upgrade() {
                            trace.borrow_mut().set_difference(index.time(), compact);
                        }
                    }

                }
            });
        });

        Arranged { stream: stream, trace: trace }
    }
}


/// Arranges something as `(Key,())` pairs, logically by `Key`.
///
/// This trait provides an optimized implementation of `ArrangeByKey` in which
/// the underlying trace does not support dynamic numbers of values for each key,
/// which saves on computation and memory.
pub trait ArrangeBySelf<G: Scope, K: Data> {
    /// Arranges a stream of `(Key, ()))` updates by `Key`.
    ///
    /// This operator produces a stream of values, but more important shares a trace it maintains.
    /// This trace is current for all times completed by the output stream, which can be used to
    /// safely identify the stable times and values in the trace.
    fn arrange_by_self<
        U:     Unsigned+Default,
        KH:    Fn(&K)->U+'static,
        Look:  Lookup<K, ::collection::count::Offset>+'static,
        LookG: Fn(u64)->Look,
    >(&self, key_h: KH, look: LookG) -> Arranged<G, Count<K, G::Timestamp, Look>>
    where G::Timestamp: Lattice;
}

impl<G: Scope, K: Data> ArrangeBySelf<G, K> for Collection<G, K> where G::Timestamp: Lattice {

    fn arrange_by_self<
        U:     Unsigned+Default,
        KH:    Fn(&K)->U+'static,
        Look:  Lookup<K, ::collection::count::Offset>+'static,
        LookG: Fn(u64)->Look,
    >
    (&self, key_h: KH, look: LookG) -> Arranged<G, Count<K, G::Timestamp, Look>> 
    where G::Timestamp: Lattice {

        let peers = self.scope().peers();
        let mut log_peers = 0;
        while (1 << (log_peers + 1)) <= peers {
            log_peers += 1;
        }

        // create a trace to share with downstream consumers.
        let trace = Rc::new(RefCell::new(Count::new(look(log_peers))));
        let source = Rc::downgrade(&trace);

        // A map from times to received (key, val, wgt) triples.
        let mut inputs = LinearMap::new();

        // create an exchange channel based on the supplied Fn(&D1)->u64.
        let part1 = Rc::new(key_h);
        let part2 = part1.clone();
        let exch = Exchange::new(move |&(ref k,_): &(K,i32)| part1(k).as_u64());

        let mut sorter = LSBRadixSorter::new();

        // fabricate a data-parallel operator using the `unary_notify` pattern.
        let stream = self.inner.unary_notify(exch, "ArrangeBySelf", vec![], move |input, output, notificator| {

            // 1. read each input, and stash it in our staging area
            while let Some((time, data)) = input.next() {
                inputs.entry_or_insert(time.time(), || { notificator.notify_at(time); Vec::new() })
                      .push(::std::mem::replace(data.deref_mut(), Vec::new()));
            }

            // 2. for each complete time, sort out the received input.
            while let Some((index, _count)) = notificator.next() {

                if let Some(mut queue) = inputs.remove_key(&index) {

                    // sort things; radix if many, .sort_by if few.
                    let compact = if queue.len() > 1 {
                        for element in queue.into_iter() {
                            sorter.extend(element.into_iter().map(|(d,w)| ((d,()),w)), &|x| part2(&(x.0).0));
                        }
                        let mut sorted = sorter.finish(&|x| part2(&(x.0).0));
                        let result = Compact::from_radix(&mut sorted, &|k| part2(k));
                        sorted.truncate(256);
                        sorter.recycle(sorted);
                        result
                    }
                    else {
                        let mut vec = queue.pop().unwrap();
                        let mut vec = vec.drain(..).map(|(d,w)| ((d,()),w)).collect::<Vec<_>>();
                        vec.sort_by(|x,y| part2(&(x.0).0).cmp(&part2((&(y.0).0))));
                        Compact::from_radix(&mut vec![vec], &|k| part2(k))
                    };
                    if let Some(compact) = compact {
                        if let Some(trace) = source.upgrade() {
                            trace.borrow_mut().set_difference(index.time(), compact.clone());
                        }
                        output.session(&index).give((compact.keys, compact.cnts, compact.vals));
                    }
                }
            }
        });

        Arranged { stream: stream, trace: trace }
    }
}
