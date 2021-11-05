// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A version of the Naive datalog analysis using Infer.

#[allow(unused_imports)]
use datafrog::{Iteration, Relation, RelationLeaper};
use std::time::Instant;

use crate::facts::FactTypes;
use crate::output::{Context, Output};

#[inline]
fn relation_contains<T: Ord>(r: &Relation<T>, tuple: &T) -> bool {
    r.elements.binary_search(tuple).is_ok()
}


pub(super) fn compute<T: FactTypes>(
    ctx: &Context<'_, T>,
    result: &mut Output<T>,
) -> (
    Relation<(T::Loan, T::Point)>,
    Relation<(T::Origin, T::Origin, T::Point)>,
) {
    println!("starting InferNaive...");
    let timer = Instant::now();

    let (errors, subset_errors) = {
        // Static inputs
        let origin_live_on_entry_rel = &ctx.origin_live_on_entry;
        // let cfg_edge = &ctx.cfg_edge;
        let loan_killed_at = &ctx.loan_killed_at;
        let known_placeholder_subset = &ctx.known_placeholder_subset;
        let placeholder_origin = &ctx.placeholder_origin;

        // Create a new iteration context, ...
        // let mut iteration = Iteration::new();

        // .. some variables, ..
        // let subset = iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset");
        // let origin_contains_loan_on_entry =
        //     iteration.variable::<(T::Origin, T::Loan, T::Point)>("origin_contains_loan_on_entry");
        // let loan_live_at = iteration.variable::<((T::Loan, T::Point), ())>("loan_live_at");

        // `loan_invalidated_at` facts, stored ready for joins
        // let loan_invalidated_at = Relation::from_iter(
        //     ctx.loan_invalidated_at
        //         .iter()
        //         .map(|&(loan, point)| ((loan, point), ())),
        // );

        // different indices for `subset`.
        // let subset_o1p = iteration.variable_indistinct("subset_o1p");
        // let subset_o2p = iteration.variable_indistinct("subset_o2p");

        // different index for `origin_contains_loan_on_entry`.
        // let origin_contains_loan_on_entry_op =
        //     iteration.variable_indistinct("origin_contains_loan_on_entry_op");

        // Unfortunately, we need `origin_live_on_entry` in both variable and relation forms:
        // We need:
        // - `origin_live_on_entry` as a Relation for the leapjoins in rules 3 & 6
        // - `origin_live_on_entry` as a Variable for the join in rule 7
        //
        // The leapjoins use `origin_live_on_entry` as `(Origin, Point)` tuples, while the join uses
        // it as a `((O, P), ())` tuple to filter the `((Origin, Point), Loan)` tuples from
        // `origin_contains_loan_on_entry_op`.
        //
        // The regular join in rule 7 could be turned into a `filter_with` leaper but that would
        // result in a leapjoin with no `extend_*` leapers: a leapjoin that is not well-formed.
        // Doing the filtering via an `extend_with` leaper would be extremely inefficient.
        //
        // Until there's an API in datafrog to handle this use-case better, we do a slightly less
        // inefficient thing of copying the whole static input into a Variable to use a regular
        // join, even though the liveness information can be quite heavy (around 1M tuples
        // on `clap`).
        // This is the Naive variant so this is not a big problem, but needs an
        // explanation.
        
        // let origin_live_on_entry_var =
        //     iteration.variable::<((T::Origin, T::Point), ())>("origin_live_on_entry");
        // origin_live_on_entry_var.extend(
        //     origin_live_on_entry_rel
        //         .iter()
        //         .map(|&(origin, point)| ((origin, point), ())),
        // );

        // output relations: illegal accesses errors, and illegal subset relations errors
        // let errors = iteration.variable("errors");
        // let subset_errors = iteration.variable::<(T::Origin, T::Origin, T::Point)>("subset_errors");

        // load initial facts:

        // Rule 1: the initial subsets are the non-transitive `subset_base` static input.
        //
        // subset(Origin1, Origin2, Point) :-
        //   subset_base(Origin1, Origin2, Point).
        // subset.extend(ctx.subset_base.iter());

        // Rule 4: the issuing origins are the ones initially containing loans.
        //
        // origin_contains_loan_on_entry(Origin, Loan, Point) :-
        //   loan_issued_at(Origin, Loan, Point).
        // origin_contains_loan_on_entry.extend(ctx.loan_issued_at.iter());

        // let subset_base_rel: std::collections::HashSet<_> = ctx.subset_base.iter().cloned().collect();

        // .. and then start iterating rules!
        let res = infer_run! {
            struct InferNaiveProg<T: FactTypes>;

            relation subset(T::Origin, T::Origin, T::Point);
            subset(*o1, *o2, *p) <-- for (o1, o2, p) in ctx.subset_base.iter();

            relation cfg_edge(T::Point, T::Point);
            cfg_edge(*p1, *p2) <-- for (p1, p2) in ctx.cfg_edge.iter();

            // TODO potential perf improvements here...
            relation origin_live_on_entry(T::Origin, T::Point);
            origin_live_on_entry(*o, *p) <-- for (o, p) in origin_live_on_entry_rel.iter();
            
            relation origin_contains_loan_on_entry(T::Origin, T::Loan, T::Point);
            origin_contains_loan_on_entry(*o, *l, *p) <-- for (o, l, p) in ctx.loan_issued_at.iter();

            relation loan_live_at(T::Loan, T::Point);

            relation loan_invalidated_at(T::Loan, T::Point);
            loan_invalidated_at(*l, *p) <-- for (l, p) in ctx.loan_invalidated_at.iter();

            relation errors(T::Loan, T::Point);

            relation placeholder_origin(T::Origin);
            placeholder_origin(*o) <-- for (o, _) in placeholder_origin.iter();

            relation subset_error(T::Origin, T::Origin, T::Point);


        // while iteration.changed() {
            // Cleanup step: remove symmetries
            // - remove origins which are `subset`s of themselves
            //
            // FIXME: investigate whether is there a better way to do that without complicating
            // the rules too much, because it would also require temporary variables and
            // impact performance. Until then, the big reduction in tuples improves performance
            // a lot, even if we're potentially adding a small number of tuples
            // per round just to remove them in the next round.
            // subset
            //     .recent
            //     .borrow_mut()
            //     .elements
            //     .retain(|&(origin1, origin2, _)| origin1 != origin2);

            // Remap fields to re-index by keys, to prepare the data needed by the rules below.
            // subset_o1p.from_map(&subset, |&(origin1, origin2, point)| {
            //     ((origin1, point), origin2)
            // });
            // subset_o2p.from_map(&subset, |&(origin1, origin2, point)| {
            //     ((origin2, point), origin1)
            // });

            // origin_contains_loan_on_entry_op
            //     .from_map(&origin_contains_loan_on_entry, |&(origin, loan, point)| {
            //         ((origin, point), loan)
            //     });

            // Rule 1: done above, as part of the static input facts setup.

            // Rule 2: compute the subset transitive closure, at a given point.
            //
            // subset(Origin1, Origin3, Point) :-
            //   subset(Origin1, Origin2, Point),
            //   subset(Origin2, Origin3, Point).
            subset(*origin1, *origin3, *point) <--
                subset(origin1, origin2, point),
                subset(origin2, origin3, point),
                if origin1 != origin3;
            // subset.from_join(
            //     &subset_o2p,
            //     &subset_o1p,
            //     |&(_origin2, point), &origin1, &origin3| (origin1, origin3, point),
            // );
            // Rule 3: propagate subsets along the CFG, according to liveness.
            //
            // subset(Origin1, Origin2, Point2) :-
            //   subset(Origin1, Origin2, Point1),
            //   cfg_edge(Point1, Point2),
            //   origin_live_on_entry(Origin1, Point2),
            //   origin_live_on_entry(Origin2, Point2).
            // relation subset_inc(T::Origin, T::Origin, T::Point);
            // subset_inc(*origin1, *origin2, *point2),

            subset(*origin1, *origin2, *point2) <--
                subset(origin1, origin2, point1),
                cfg_edge(point1, point2),
                origin_live_on_entry(origin1, point2),
                origin_live_on_entry(origin2, point2);

            // subset.from_leapjoin(
            //     &subset,
            //     (
            //         cfg_edge.extend_with(|&(_origin1, _origin2, point1)| point1),
            //         origin_live_on_entry_rel.extend_with(|&(origin1, _origin2, _point1)| origin1),
            //         origin_live_on_entry_rel.extend_with(|&(_origin1, origin2, _point1)| origin2),
            //     ),
            //     |&(origin1, origin2, _point1), &point2| (origin1, origin2, point2),
            // );

            // Rule 4: done above as part of the static input facts setup.
            // TODO

            // Rule 5: propagate loans within origins, at a given point, according to subsets.
            //
            // origin_contains_loan_on_entry(Origin2, Loan, Point) :-
            //   origin_contains_loan_on_entry(Origin1, Loan, Point),
            //   subset(Origin1, Origin2, Point).
            origin_contains_loan_on_entry(*origin2, *loan, *point) <--
                origin_contains_loan_on_entry(origin1, loan, point),
                subset(origin1, origin2, point);
            // origin_contains_loan_on_entry.from_join(
            //     &origin_contains_loan_on_entry_op,
            //     &subset_o1p,
            //     |&(_origin1, point), &loan, &origin2| (origin2, loan, point),
            // );

            // Rule 6: propagate loans along the CFG, according to liveness.
            //
            // origin_contains_loan_on_entry(Origin, Loan, Point2) :-
            //   origin_contains_loan_on_entry(Origin, Loan, Point1),
            //   !loan_killed_at(Loan, Point1),
            //   cfg_edge(Point1, Point2),
            //   origin_live_on_entry(Origin, Point2).
            origin_contains_loan_on_entry(*origin, *loan, *point2) <--
                origin_contains_loan_on_entry(origin, loan, point1)
                if !relation_contains(&loan_killed_at, &(*loan, *point1)),
                cfg_edge(point1, point2),
                origin_live_on_entry(origin, point2);
            // origin_contains_loan_on_entry.from_leapjoin(
            //     &origin_contains_loan_on_entry,
            //     (
            //         loan_killed_at.filter_anti(|&(_origin, loan, point1)| (loan, point1)),
            //         cfg_edge.extend_with(|&(_origin, _loan, point1)| point1),
            //         origin_live_on_entry_rel.extend_with(|&(origin, _loan, _point1)| origin),
            //     ),
            //     |&(origin, loan, _point1), &point2| (origin, loan, point2),
            // );

            // Rule 7: compute whether a loan is live at a given point, i.e. whether it is
            // contained in a live origin at this point.
            //
            // loan_live_at(Loan, Point) :-
            //   origin_contains_loan_on_entry(Origin, Loan, Point),
            //   origin_live_on_entry(Origin, Point).
            loan_live_at(*loan, *point) <--
                origin_contains_loan_on_entry(origin, loan, point),
                origin_live_on_entry(origin, point);
            // loan_live_at.from_join(
            //     &origin_contains_loan_on_entry_op,
            //     &origin_live_on_entry_var,
            //     |&(_origin, point), &loan, _| ((loan, point), ()),
            // );

            // Rule 8: compute illegal access errors, i.e. an invalidation of a live loan.
            //
            // Here again, this join acts as a pure filter and could be a more efficient leapjoin.
            // However, similarly to the `origin_live_on_entry` example described above, the
            // leapjoin with a single `filter_with` leaper would currently not be well-formed.
            // We don't explictly need to materialize `loan_live_at` either, and that doesn't
            // change the well-formedness situation, so we still materialize it (since that also
            // helps in testing).
            //
            // errors(Loan, Point) :-
            //   loan_invalidated_at(Loan, Point),
            //   loan_live_at(Loan, Point).
            errors(*loan, *point) <--
                loan_invalidated_at(loan, point),
                loan_live_at(loan, point);
            // errors.from_join(
            //     &loan_live_at,
            //     &loan_invalidated_at,
            //     |&(loan, point), _, _| (loan, point),
            // );

            // Rule 9: compute illegal subset relations errors, i.e. the undeclared subsets
            // between two placeholder origins.
            // Here as well, WF-ness prevents this join from being a filter-only leapjoin. It
            // doesn't matter much, as `placeholder_origin` is single-value relation.
            //
            // subset_error(Origin1, Origin2, Point) :-
            //   subset(Origin1, Origin2, Point),
            //   placeholder_origin(Origin1),
            //   placeholder_origin(Origin2),
            //   !known_placeholder_subset(Origin1, Origin2).
            subset_error(*origin1, *origin2, *point) <--
                subset(origin1, origin2, point),
                placeholder_origin(origin1),
                placeholder_origin(origin2)
                if !relation_contains(known_placeholder_subset, &(*origin1, *origin2))
                if origin1 != origin2;
            // subset_errors.from_leapjoin(
            //     &subset,
            //     (
            //         placeholder_origin.extend_with(|&(origin1, _origin2, _point)| origin1),
            //         placeholder_origin.extend_with(|&(_origin1, origin2, _point)| origin2),
            //         known_placeholder_subset
            //             .filter_anti(|&(origin1, origin2, _point)| (origin1, origin2)),
            //         // remove symmetries:
            //         datafrog::ValueFilter::from(|&(origin1, origin2, _point), _| {
            //             origin1 != origin2
            //         }),
            //     ),
            //     |&(origin1, origin2, point), _| (origin1, origin2, point),
            // );
        // }
        };
        


        // Handle verbose output data
        if result.dump_enabled {
            let subset = &res.subset;
            assert!(
                subset
                    .iter()
                    .filter(|&(origin1, origin2, _)| origin1 == origin2)
                    .count()
                    == 0,
                "unwanted subset symmetries"
            );
            for &(origin1, origin2, location) in subset.iter() {
                result
                    .subset
                    .entry(location)
                    .or_default()
                    .entry(origin1)
                    .or_default()
                    .insert(origin2);
            }

            let origin_contains_loan_on_entry = &res.origin_contains_loan_on_entry;
            for &(origin, loan, location) in origin_contains_loan_on_entry.iter() {
                result
                    .origin_contains_loan_at
                    .entry(location)
                    .or_default()
                    .entry(origin)
                    .or_default()
                    .insert(loan);
            }

            let loan_live_at = &res.loan_live_at;
            for &(loan, location) in loan_live_at.iter() {
                result.loan_live_at.entry(location).or_default().push(loan);
            }
        }

        println!("rules:\n{}", res.summary());
        println!("res:\n{}", res.relation_sizes_summary());
        println!("scc times:\n{}", res.scc_times_summary());

        let errors_relation = Relation::from(res.errors);
        let subset_errors_relation = Relation::from(res.subset_error);
        (errors_relation, subset_errors_relation)
    };

    println!(
        "analysis done: {} `errors` tuples, {} `subset_errors` tuples, {:?}",
        errors.len(),
        subset_errors.len(),
        timer.elapsed()
    );

    (errors, subset_errors)
}
