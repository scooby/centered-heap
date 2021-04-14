#[macro_use]
extern crate enum_display_derive;

#[macro_use]
extern crate json;

use clap::{App, Arg};
use fmt::Display;
use json::JsonValue;
use rand::prelude::{thread_rng, Rng, SliceRandom};
use std::fmt;
use std::io;

use std::time::SystemTime;

/*
 * The left child in a centered heap is either center - 1, or twice the distance from center.
 * Uses usize::MAX for known out of bounds as we expect that will fail a bounds check.
 */
#[inline]
fn get_left_child(x: usize, c: usize) -> usize {
    if x == c {
        if c == 0 {
            usize::MAX
        } else {
            c - 1
        }
    } else if x > c {
        c + (x - c) * 2
    } else {
        let o = (c - x) * 2;
        if o > c {
            usize::MAX
        } else {
            c - o
        }
    }
}

/*
 * The right child in a centered heap is either center + 1, or twice the distance from center
 * plus one.
 * Uses usize::MAX for known out of bounds as we expect that will fail a bounds check.
 */
#[inline]
fn get_right_child(x: usize, c: usize) -> usize {
    if x == c {
        c + 1
    } else if x > c {
        (x - c) * 2 + 1 + c
    } else {
        let o = (c - x) * 2 + 1;
        if o > c {
            usize::MAX
        } else {
            c - o
        }
    }
}

/*
 * The parent node is half the distance from the center, rounded down.
 */
#[inline]
fn get_parent(x: usize, c: usize) -> usize {
    debug_assert!(x != c, "cheap-state: can't find parent of center node");
    if x > c {
        c + (x - c) / 2
    } else {
        c - (c - x) / 2
    }
}

/*
 * The recenter limit identifies where nodes must be sifted in order to fully recenter.
 * This is half the distance from the center, rounded up.
 */
#[inline]
fn get_recenter_limit(x: usize, c: usize) -> usize {
    if x > c {
        (x - c + 1) / 2 + c
    } else {
        c - (c - x + 1) / 2
    }
}

macro_rules! dbg_println {
    ($($arg:expr), *) => {
        #[cfg(debug_assertions)]
        eprintln!($($arg), *);
    };
}

macro_rules! dbg_show_call {
    ($self:ident, $($method:expr), *) => {
        #[cfg(debug_assertions)]
        show_call!($self, $($method), *);
    };
}

macro_rules! show_call {
    ($self:ident, $($method:expr), *) => {
        eprint!($($method), *);
        eprintln!("lo={}, c={}, hi={}) {:?}", $self.lo, $self.c, $self.hi, $self);
    }
}

trait Counter {
    fn count_compare(&mut self);
    fn count_swap(&mut self);
    fn copy_to(&self, tgt: &mut JsonValue);
}

#[derive(Debug)]
struct DummyCounter {}

impl Counter for DummyCounter {
    fn count_compare(&mut self) {}
    fn count_swap(&mut self) {}
    fn copy_to(&self, _tgt: &mut JsonValue) {}
}

#[derive(Debug)]
struct RealCounter {
    compares: u64,
    swaps: u64,
}

impl Counter for RealCounter {
    fn count_compare(&mut self) {
        self.compares += 1;
    }
    fn count_swap(&mut self) {
        self.swaps += 1;
    }
    fn copy_to(&self, tgt: &mut JsonValue) {
        tgt["compares"] = self.compares.into();
        tgt["swaps"] = self.swaps.into();
    }
}

struct Cheap<'a, E: PartialOrd + fmt::Debug, C: Counter + fmt::Debug> {
    a: &'a mut [E],
    lo: usize,
    c: usize,
    hi: usize,
    cnt: &'a mut C,
}

impl<'a, E: PartialOrd + fmt::Debug, C: Counter + fmt::Debug> Cheap<'a, E, C> {
    // Construct a c-heap oriented at the left end of the array.
    fn new_left(a: &'a mut [E], cnt: &'a mut C) -> Self {
        Cheap {
            a: a,
            lo: 0,
            c: 0,
            hi: 0,
            cnt: cnt,
        }
    }

    // Construct a c-heap oriented at the right end of the array.
    fn new_right(a: &'a mut [E], cnt: &'a mut C) -> Self {
        let i = a.len();
        Cheap {
            a: a,
            lo: i,
            c: i,
            hi: i,
            cnt: cnt,
        }
    }

    // Construct a c-heap spanning the whole array, centered at the left.
    fn new_spanleft(a: &'a mut [E], cnt: &'a mut C) -> Self {
        let i = a.len();
        Cheap {
            a: a,
            lo: 0,
            c: 0,
            hi: i,
            cnt: cnt,
        }
    }

    // Construct a c-heap spanning the whole array, centered at the left.
    #[allow(dead_code)]
    fn new_spanright(a: &'a mut [E], cnt: &'a mut C) -> Self {
        let i = a.len();
        Cheap {
            a: a,
            lo: 0,
            c: i - 1,
            hi: i,
            cnt: cnt,
        }
    }

    // Get the parameters as isizes for use in calculations.
    #[inline]
    fn params(&self) -> (usize, usize, usize) {
        (self.lo, self.c, self.hi)
    }

    #[inline]
    fn swap(&mut self, i: usize, j: usize) {
        self.cnt.count_swap();
        self.a.swap(i, j);
    }

    // Check if a[i] is "better than" a[j].
    #[inline]
    fn bt(&mut self, i: usize, j: usize) -> bool {
        self.cnt.count_compare();
        return self.a[i] <= self.a[j];
    }

    // Check if a[i] is "better than" a[j].
    #[inline]
    fn bt_nocount(&self, i: usize, j: usize) -> bool {
        return self.a[i] <= self.a[j];
    }

    // Check only the range invariants.
    #[allow(dead_code)]
    fn check_range(&self) {
        let (lo, c, hi) = self.params();
        assert!(
            /* 0 <= lo && */ hi <= self.a.len(),
            "c-heap state: markers outside array"
        );
        assert!(
            lo == c && c == hi || lo <= c && c <= hi,
            "c-heap state: markers invalid"
        );
    }

    // Do a full check of the invariants.
    #[allow(dead_code)]
    fn check(&self) {
        self.check_range();
        assert!(self.is_valid(), "c-heap state: heap invariant failed");
    }

    #[allow(dead_code)]
    fn is_valid(&self) -> bool {
        let (lo, c, hi) = self.params();
        for i in lo..hi {
            if i != c {
                let p = get_parent(i, c);
                let x = self.bt_nocount(p, i);
                if !x {
                    show_call!(
                        self,
                        "check: failed(a[{}]={:?} bt a[{}]={:?}, ",
                        p,
                        &self.a[p],
                        i,
                        &self.a[i]
                    );
                    return false;
                }
            }
        }
        return true;
    }

    fn is_empty(&self) -> bool {
        debug_assert!(self.lo <= self.hi, "c-heap state error: markers invalid");
        self.lo == self.hi
    }

    /**
     * Recentering initializes the heap at a range from lo to (but not including) hi
     * and with a center at c.
     *
     * After running this, a valid center heap exists as follows:
     *
     *     . . . [x, x, x, C, x, x, x] . . .
     *          lo^                    ^hi
     *
     * The best value (per bt) will be located at index c.
     *
     * Data outside the range [lo:hi] will be unaffected.
     */
    fn recenter(&mut self) {
        dbg_show_call!(self, "recenter-start(");
        #[cfg(debug_assertions)]
        self.check_range();
        let (lo, c, hi) = self.params();
        for i in get_recenter_limit(lo, c)..c {
            self.sift_out(i);
        }
        for i in (c..get_recenter_limit(hi, c)).rev() {
            self.sift_out(i);
        }
        #[cfg(debug_assertions)]
        self.check();
        dbg_show_call!(self, "recenter-end(");
    }

    /**
     * Move a root node towards a leaf.
     *
     *   leaf   leaf
     *       node
     *
     * We inspect each leaf, and if the leaf is "better than" the node, we'll swap them to preserve
     * the invariant.
     */
    fn sift_out(&mut self, ii: usize) {
        dbg_show_call!(self, "sift_out-start({}, ", ii);
        let mut vio = 0;
        let mut vio_found = true;
        let mut n = ii;
        let (lo, c, hi) = self.params();

        while vio_found {
            vio_found = false;

            let ch1 = get_left_child(n, c);
            if lo <= ch1 && ch1 < hi {
                if self.bt(ch1, n) {
                    vio = ch1;
                    vio_found = true;
                    dbg_println!("sift: left child {} is better than parent {}", ch1, n);
                } else {
                    dbg_println!("sift: parent {} is better than left child {}", n, ch1);
                }
            } else {
                dbg_println!("sift: left child {} is out of range", ch1);
            }

            let ch2 = get_right_child(n, c);
            if lo <= ch2 && ch2 < hi {
                if self.bt(ch2, n) {
                    dbg_println!("sift: right child {} is better than parent {}", ch2, n);
                    if !vio_found || self.bt(ch2, vio) {
                        dbg_println!("sift: and right child is better than left child");
                        vio_found = true;
                        vio = ch2;
                    }
                } else {
                    dbg_println!("sift: parent {} is better than right child {}", n, ch2);
                }
            } else {
                dbg_println!("sift: right child {} is out of range", ch2);
            }
            if vio_found {
                dbg_println!("sift: swap {} and {}", n, vio);
                self.swap(n, vio);
                n = vio;
            }
        }
        dbg_show_call!(self, "sift_out-end({}, ", ii);
    }

    /*
     * Move a leaf up towards the root.
     */
    fn sift_in(&mut self, i: usize) {
        dbg_show_call!(self, "sift_in-start({}, ", i);
        let mut p;
        let mut n = i;
        let c = self.c;
        while n != c {
            p = get_parent(n, c);
            if self.bt(n, p) {
                dbg_println!("sift_in: child {} better than parent {}", n, p);
                // Violation: child is "better than" parent.
                self.swap(n, p);
                n = p;
            } else {
                dbg_println!("sift_in: parent {} better than child {}, ending", p, n);
                break;
            }
        }
        dbg_show_call!(self, "sift_in-end({}, ", i);
    }

    /*
     * Given our range:
     *
     *      [x, x, C, x, x]
     *       ^lo
     *
     * Swap the center (best) value into lo and shrinks the range on the left.
     *
     *      C  [x, x, x, x]
     *
     * Side-effect: Adjust lo to be lo + 1.
     *
     * Side-effect: May re-center.
     */
    fn pop_left(&mut self) {
        #[cfg(debug_assertions)]
        self.check();

        assert!(!self.is_empty(), "c-heap error: pop when empty");

        let lop = self.lo + 1;
        if self.lo == self.c {
            if lop < self.hi {
                self.c = self.hi - 1;
                self.lo = lop;
                self.recenter();
            } else {
                self.lo = lop; // Now empty.
                self.c = lop;
            }
        } else {
            self.swap(self.c, self.lo);
            self.lo = lop;
            self.sift_out(self.c);
        }
        #[cfg(debug_assertions)]
        self.check();
    }

    /*
     * Given our range:
     *
     *      [x, x, C, x, x] . . .
     *                      ^hi
     *
     * Swap the center (best) value into hi - 1 and shrinks the range on the right.
     *
     *      [x, x, x, x] C . . .
     *                   ^hi
     *
     * Side-effect: Adjusts hi to be hi - 1.
     *
     * Side-effect: May re-center.
     */
    fn pop_right(&mut self) {
        #[cfg(debug_assertions)]
        self.check();
        assert!(!self.is_empty(), "c-heap error: pop when empty");
        let hip = self.hi - 1;
        if hip == self.c {
            self.c = self.lo;
            self.hi = hip;
            if self.lo < hip {
                self.recenter();
            } // else now empty.
        } else {
            self.a.swap(hip as usize, self.c as usize);
            self.hi = hip;
            self.sift_out(self.c);
        }
        #[cfg(debug_assertions)]
        self.check();
    }

    /*
     * Given our range:
     *
     *      L [x, x, x, x]
     *         ^lo
     *
     * Expand the range to absorb L and preserve invariants.
     *
     *     [x, x, x, L, x]
     *
     * Side-effect: adjust lo to lo - 1.
     *
     * Side-effect: may adjust center index when pushing into an empty container.
     */
    fn push_left(&mut self) {
        #[cfg(debug_assertions)]
        self.check();
        assert!(
            self.lo > 0,
            "c-heap error: attempt to push past array boundary"
        );

        let lop = self.lo - 1;
        if self.c == self.hi {
            debug_assert!(self.lo == self.c, "c-heap state: expected an empty c-heap");
            self.c = lop;
        }
        self.lo = lop;
        self.sift_in(lop);
        #[cfg(debug_assertions)]
        self.check();
    }

    #[allow(dead_code)]
    fn push_left_swap(&mut self, i: usize) {
        assert!(
            i < self.lo || i >= self.hi,
            "c-heap error: attempt to swap in value already inside c-heap"
        );
        self.swap(i, self.lo - 1);
        self.push_left();
    }

    fn push_right_swap(&mut self, i: usize) {
        assert!(
            i < self.lo || i >= self.hi,
            "c-heap error: attempt to swap in value already inside c-heap"
        );
        self.swap(i, self.hi);
        self.push_right();
    }

    /*
     * Given our range:
     *
     *     [x, x, x, x] R
     *                hi^
     *
     * Expand the range to absorb R and preserve invariants.
     *
     *     [x, R, x, x, x]
     *
     * Side-effect: adjust lo to lo - 1.
     *
     * Side-effect: may adjust center index when pushing into an empty container.
     */
    fn push_right(&mut self) {
        #[cfg(debug_assertions)]
        self.check();
        assert!(
            self.hi < self.a.len(),
            "c-heap error: attempt to push when c-heap full"
        );

        let hip = self.hi + 1;
        self.sift_in(self.hi);
        self.hi = hip;
        #[cfg(debug_assertions)]
        self.check();
    }

    /*
     * Given our range:
     *
     *      [x, x, C, x, x] . . . . i
     *
     * Swap the value at i with the value at C and preserve invariants.
     *
     *      [x, x, i, x, x] . . . . C
     *
     * This is equivalent to saving the value at index i, popping the best value into i,
     * and then pushing the saved value back into the heap.
     *
     * After this operation, the value at i will always be drawn from the c-heap.
     *
     * These semantics mean it does not work with an empty c-heap.
     *
     * Guarantees no change to the range.
     */
    fn poppush(&mut self, i: usize) {
        #[cfg(debug_assertions)]
        self.check();
        dbg_show_call!(self, "poppush(i={}, ", i);
        // We could do nothing, but the caller is expecting the best value from the c-heap.
        assert!(
            !self.is_empty(),
            "c-heap error: attempted to pop from an empty range"
        );
        assert!(
            i < self.lo || i >= self.hi,
            "c-heap error: attempted to push an index already inside c-heap"
        );
        self.swap(i, self.c);
        self.sift_out(self.c);
        #[cfg(debug_assertions)]
        self.check();
    }

    /*
     * Given our range:
     *
     *      [x, x, C, x, x] . . . . i
     *
     * Compare the values at C and i. If i is better than C, do nothing.
     *
     * Otherwise, swap the value at i with the value at C and preserve invariants.
     *
     *      [x, x, i, x, x] . . . . C
     *
     * This is equivalent to pushing i's value into the heap, and then popping the best value
     * from the heap.
     *
     * These semantics mean that nothing will happen if the c-heap is empty or if i is already
     * better than a value on the c-heap.
     *
     * Guarantees no change to the range.
     */
    #[allow(dead_code)]
    fn pushpop(&mut self, i: usize) {
        #[cfg(debug_assertions)]
        self.check();
        dbg_show_call!(self, "pushpop(i={}, ", i);
        assert!(
            i < self.lo || i >= self.hi,
            "c-heap error: attempted to push an index already inside c-heap"
        );
        if self.is_empty() || self.bt(i, self.c) {
            return;
        }
        self.swap(i, self.c);
        self.sift_out(self.c);
        #[cfg(debug_assertions)]
        self.check();
    }

    /*
     * Given our range:
     *
     *      [x, x, x, x, x] R
     *
     * Transfer the right-hand value over to the left:
     *
     *      R [x, x, x, x, x]
     *
     * Side-effect: adjusts lo and hi to be lo + 1 and hi + 1.
     *
     * Side-effect: may recenter the heap.
     */
    fn slide_right(&mut self) {
        #[cfg(debug_assertions)]
        self.check();
        assert!(
            self.hi < self.a.len(),
            "c-heap error: attempt to slide right past array bounds"
        );
        if self.is_empty() {
            self.lo += 1;
            self.c += 1;
            self.hi += 1;
        } else {
            let lop = self.lo + 1;
            let hip = self.hi + 1;
            self.swap(self.lo, self.hi);
            if self.c == self.lo {
                self.c = self.hi;
                self.lo = lop;
                self.hi = hip;
                self.recenter();
            } else {
                self.sift_in(self.hi);
                self.lo = lop;
                self.hi = hip;
            }
        }
        #[cfg(debug_assertions)]
        self.check();
    }

    /*
     * Given our range:
     *
     *      L [x, x, x, x, x]
     *
     * Transfer the left-hand value over to the right:
     *
     *      [x, x, x, x, x] L
     *
     * Side-effect: adjusts lo and hi to be lo - 1 and hi - 1.
     *
     * Side-effect: may recenter the heap.
     */
    #[allow(dead_code)]
    fn slide_left(&mut self) {
        #[cfg(debug_assertions)]
        self.check();
        assert!(
            self.lo > 0,
            "c-heap error: attempt to slide left past array bounds"
        );
        if self.is_empty() {
            self.lo -= 1;
            self.c -= 1;
            self.hi -= 1;
        } else {
            let lop = self.lo - 1;
            let hip = self.hi - 1;
            self.swap(lop, hip);
            if self.c == hip {
                self.c = self.lo;
                self.lo = lop;
                self.hi = hip;
                self.recenter();
            } else {
                self.sift_in(lop);
                self.lo = lop;
                self.hi = hip;
            }
        }
        #[cfg(debug_assertions)]
        self.check();
    }

    /*
     * Given lo:md is sorted and md:hi is sorted, merge them.
     *
     * Uses a centered heap.
     *
     * ---|------|------|-----|---
     *    lo   ch.lo  ch.hi  hi
     */
    fn merge(a: &mut [E], lo: usize, md: usize, hi: usize, cnt: &mut C) {
        dbg_println!("merge({}, {}, {})", lo, md, hi);
        let mut ch = Cheap {
            a: a,
            lo: md,
            c: md,
            hi: md,
            cnt: cnt,
        };
        debug_assert!(is_sorted(ch.a, lo, md), "merge(pre): lo to md not sorted");
        debug_assert!(is_sorted(ch.a, md, hi), "merge(pre): md to hi not sorted");

        for ix in lo..hi {
            if ix >= ch.hi {
                // Only one vector left, nothing to do.
                break;
            }

            let mut best = MC::None;

            if ix < ch.lo {
                best = MC::Lo(&ch.a[ix]);
            }
            if ch.lo < ch.hi {
                best = best.better(MC::Md(&ch.a[ch.c]), ch.cnt);
            }
            if ch.hi < hi {
                best = best.better(MC::Hi(&ch.a[ch.hi]), ch.cnt);
            }
            if let MC::None = best {
                panic!("merge: logic error");
            }
            if let MC::Lo(_) = best {
                dbg_println!("merge: output is in place");
                continue;
            } else if ix < ch.lo {
                if let MC::Md(_) = best {
                    // Pop the best value from ch into ix, and push the value that was at ix in.
                    dbg_println!("merge: poppush");
                    ch.poppush(ix);
                } else {
                    // Swap the right hand value into ix
                    dbg_println!("merge: push_right");
                    ch.push_right_swap(ix);
                }
            } else if ix == ch.lo {
                if let MC::Md(_) = best {
                    // We're in ch, so just pop a value in place.
                    dbg_println!("merge: pop_left");
                    ch.pop_left();
                } else {
                    // We just need to move the right hand value into place.
                    dbg_println!("merge: slide_right");
                    ch.slide_right();
                }
            } else {
                panic!("merge: ix is invalid!");
            }
        }
        debug_assert!(is_sorted(a, lo, hi), "merge(post): not sorted after merge");
    }
}

// Convenience for formatting a single entity.
macro_rules! one_ent {
    ($self: ident, $i: expr, $f:ident) => {
        $f.write_str(format!("{:?}", &$self.a[$i as usize]).as_str())?;
        let mut dot = ":";
        if $i == $self.lo {
            $f.write_str(":lo")?;
            dot = ".";
        }
        if $i == $self.c {
            $f.write_str(dot)?;
            $f.write_str("c")?;
            dot = ".";
        }
        if $i == $self.hi {
            $f.write_str(dot)?;
            $f.write_str("hi")?;
        }
    };
}

impl<'a, E: PartialOrd + fmt::Debug, C: Counter + fmt::Debug> fmt::Debug for Cheap<'a, E, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let a_len = self.a.len();

        if a_len < 1 {
            f.write_str("[]")?;
        } else if a_len < 100 {
            f.write_str("[")?;
            one_ent!(self, 0, f);
            for i in 1..a_len {
                f.write_str(" ")?;
                one_ent!(self, i, f);
            }
            f.write_str("]")?;
        } else {
            f.write_str("[")?;
            one_ent!(self, 0, f);
            for i in 1..40 {
                f.write_str(" ")?;
                one_ent!(self, i, f);
            }
            f.write_str(" ...")?;
            for i in a_len - 40..a_len {
                f.write_str(" ")?;
                one_ent!(self, i, f);
            }
            f.write_str("]")?;
        }
        Ok(())
    }
}

#[derive(Debug)]
enum MC<'a, E> {
    None,      // -1
    Lo(&'a E), // 0
    Md(&'a E), // 1
    Hi(&'a E), // 2
}

impl<'a, E: PartialOrd> MC<'a, E> {
    fn val(&self) -> Option<&'a E> {
        match self {
            MC::None => None,
            MC::Lo(v) => Some(v),
            MC::Md(v) => Some(v),
            MC::Hi(v) => Some(v),
        }
    }

    fn better<C: Counter>(self, other: Self, cnt: &mut C) -> Self {
        match (self.val(), other.val()) {
            (None, None) => MC::None,
            (Some(_), None) => self,
            (None, Some(_)) => other,
            (Some(a), Some(b)) => {
                cnt.count_compare();
                if a < b {
                    self
                } else {
                    other
                }
            }
        }
    }
}

fn small_sort<E: PartialOrd, C: Counter>(a: &mut [E], lo: usize, hi: usize, c: &mut C) {
    debug_assert!(
        /*0 <= lo && */ lo <= hi && hi <= a.len(),
        "small_sort(pre): length invariants"
    );

    for i in lo + 1..hi {
        let mut j = i;
        while j > lo && a[j] < a[j - 1] {
            c.count_compare();
            a.swap(j - 1, j);
            c.count_swap();
            j -= 1;
        }
        c.count_compare();
    }
    debug_assert!(is_sorted(a, lo, hi), "small_sort(post): not sorted");
}

fn is_sorted<E: PartialOrd>(a: &[E], lo: usize, hi: usize) -> bool {
    assert!(
        /*0 <= lo && */ lo <= hi && hi <= a.len(),
        "is_sorted(pre): length invariants"
    );

    let mut v = &a[lo];
    for i in lo + 1..hi {
        let vv = &a[i];
        if vv < v {
            return false;
        }
        v = vv;
    }
    return true;
}

fn merge_sort<E: PartialOrd + fmt::Debug, C: Counter + fmt::Debug>(
    a: &mut [E],
    lo: usize,
    hi: usize,
    merge: fn(&mut [E], lo: usize, md: usize, hi: usize, cnt: &mut C),
    cnt: &mut C,
) {
    debug_assert!(
        /*0 <= lo && */ lo <= hi && hi <= a.len(),
        "merge_sort(pre): length invariants"
    );
    if hi - lo <= 4 {
        small_sort(a, lo, hi, cnt);
        return;
    }

    let midpoint = (lo + hi) / 2;
    dbg_println!("merge_sort: lo={}, md={}, hi={}", lo, midpoint, hi);
    merge_sort(a, lo, midpoint, merge, cnt);
    merge_sort(a, midpoint, hi, merge, cnt);
    merge(a, lo, midpoint, hi, cnt);
    debug_assert!(is_sorted(a, lo, hi), "merge_sort(post): not sorted");
}

fn heap_sort_left<E: PartialOrd + fmt::Debug, C: Counter + fmt::Debug>(a: &mut [E], cnt: &mut C) {
    let mut c: Cheap<E, C> = Cheap::new_spanright(a, cnt);
    c.recenter();
    while !c.is_empty() {
        c.pop_left();
    }
}

fn heap_sort_right<E: PartialOrd + fmt::Debug, C: Counter + fmt::Debug>(a: &mut [E], cnt: &mut C) {
    let mut c: Cheap<E, C> = Cheap::new_spanleft(a, cnt);
    c.recenter();
    while !c.is_empty() {
        c.pop_right();
    }
    a.reverse();
}

/**
 * This running sort starts at the left, pushes from the right until it's `run` elements large,
 * then pops elements.
 */
fn running_sort_left<E: PartialOrd + fmt::Debug, C: Counter + fmt::Debug>(
    a: &mut [E],
    run: usize,
    cnt: &mut C,
) {
    let a_len = a.len();
    if a_len == 0 {
        return;
    }
    let mut c: Cheap<E, C> = Cheap::new_left(a, cnt);
    while c.lo < a_len {
        if c.hi < a_len {
            c.push_right();
        }
        if c.hi - c.lo >= run || c.hi == a_len {
            c.pop_left();
        }
        if a_len < 200 {
            show_call!(c, "running_left(");
        }
    }
}

/**
 * This running sort starts at the right, pushes from the left until it's `run` elements large,
 * then pops elements.
 */
fn running_sort_right<E: PartialOrd + fmt::Debug, C: Counter + fmt::Debug>(
    a: &mut [E],
    run: usize,
    cnt: &mut C,
) {
    let a_len = a.len();
    if a_len == 0 {
        return;
    }
    let mut c: Cheap<E, C> = Cheap::new_right(a, cnt);
    while c.hi > 0 {
        if c.lo > 0 {
            c.push_left();
        }
        if c.hi - c.lo >= run || c.lo == 0 {
            c.pop_right();
        }
        if a_len < 200 {
            show_call!(c, "running_right(");
        }
    }
}

#[derive(Display)]
enum Op {
    MergeSort,
    HeapSortLeft,
    HeapSortRight,
    RunningSortLeft,
    RunningSortRight,
    Sort,
    Unknown,
}

impl Op {
    fn from_str(op: Option<&str>) -> Self {
        match op {
            Some(op_str) => match op_str {
                "merge" => Op::MergeSort,
                "heap_left" => Op::HeapSortLeft,
                "heap_right" => Op::HeapSortRight,
                "run_left" => Op::RunningSortLeft,
                "run_right" => Op::RunningSortRight,
                "sort" => Op::Sort,
                _ => Op::Unknown,
            },
            None => Op::Unknown,
        }
    }

    fn does_sort(self) -> bool {
        match self {
            Op::Sort | Op::MergeSort | Op::HeapSortLeft | Op::HeapSortRight => true,
            _ => false,
        }
    }

    fn run<C: Counter + fmt::Debug, E: Ord + fmt::Debug>(
        &self,
        n: &mut [E],
        run_size: usize,
        cnt: &mut C,
    ) {
        let n_len = n.len();
        match self {
            Op::MergeSort => merge_sort(n, 0, n_len, Cheap::<E, C>::merge, cnt),
            Op::HeapSortLeft => heap_sort_left(n, cnt),
            Op::HeapSortRight => heap_sort_right(n, cnt),
            Op::Sort => n.sort(),
            Op::RunningSortLeft => running_sort_left(n, run_size, cnt),
            Op::RunningSortRight => running_sort_right(n, run_size, cnt),
            Op::Unknown => return usage("Unknown operation"),
        }
    }
}

#[derive(Display)]
enum ArrayCon {
    Shuffle,
    Random,
    Count,
    Reverse,
    Unknown,
}

impl ArrayCon {
    fn from_str(ac: Option<&str>) -> Self {
        match ac {
            Some(ac_str) => match ac_str {
                "shuffle" => ArrayCon::Shuffle,
                "random" => ArrayCon::Random,
                "count" => ArrayCon::Count,
                "reverse" => ArrayCon::Reverse,
                _ => ArrayCon::Unknown,
            },
            None => ArrayCon::Unknown,
        }
    }

    /*
     * Construct an array based on a string integer provided on the command line.
     */
    fn make_array(&self, num_elems: usize) -> Vec<i32> {
        let mut rng = thread_rng();
        let num_elems_i32 = num_elems as i32;

        let mut a: Vec<i32> = match self {
            ArrayCon::Shuffle | ArrayCon::Count | ArrayCon::Reverse => (0..num_elems_i32).collect(),
            ArrayCon::Random => Vec::with_capacity(num_elems),
            ArrayCon::Unknown => Vec::new(),
        };
        match self {
            ArrayCon::Shuffle => {
                a.shuffle(&mut rng);
            }
            ArrayCon::Random => {
                a.resize(num_elems, 0);
                for elem in a.iter_mut() {
                    *elem = rng.gen_range(0..num_elems_i32);
                }
            }
            ArrayCon::Reverse => {
                a.reverse();
            }
            _ => (),
        }
        return a;
    }
}

fn parse_int(so: Option<&str>, d: usize) -> usize {
    so.map(|s| s.parse::<usize>().ok()).flatten().unwrap_or(d)
}

fn usage(what: &str) {
    eprintln!("Inavlid usage: {}", what);
    eprintln!("Try cheap --help.");
}

fn failure(what: &str) {
    println!("");
    eprintln!("");
    eprintln!("Something went wrong unexpectedly: {}", what)
}

fn main() {
    let matches = App::new("cheap")
        .about("Demonstrate the centered heap data structure.")
        .arg(
            Arg::with_name("op")
                .help(concat!(
                    "Operation to test centered heap. `merge` implements an in-place merge sort ",
                    "using c-heap. `heap_`* performs a heap sort using c-heap from the left or ",
                    "right. `running_`* sorts only a window of RUN_SIZE elements. `sort` uses ",
                    "the standard Vec::sort method."
                ))
                .short("o")
                .long("op")
                .takes_value(true)
                .possible_values(&[
                    "merge",
                    "heap_left",
                    "heap_right",
                    "run_left",
                    "run_right",
                    "sort",
                ])
                .value_name("OPERATION")
                .default_value("merge"),
        )
        .arg(
            Arg::with_name("array")
                .help(concat!(
                    "Method to generate the test array. `shuffle` guarantees no duplicate ",
                    "values, while `random` may have them. `count` is counts from 0 to size - 1. ",
                    "`reverse` is a count from size - 1 to 0."
                ))
                .short("a")
                .long("array")
                .value_name("ARRAY")
                .takes_value(true)
                .possible_values(&["shuffle", "random", "count", "reverse"])
                .default_value("shuffle"),
        )
        .arg(
            Arg::with_name("size")
                .help("Size of the test array.")
                .short("s")
                .long("size")
                .takes_value(true)
                .value_name("SIZE")
                .default_value("40"),
        )
        .arg(
            Arg::with_name("run_size")
                .help("Size of the window for a running sort.")
                .short("r")
                .long("run-size")
                .takes_value(true)
                .value_name("RUN_SIZE")
                .default_value("16"),
        )
        .arg(
            Arg::with_name("count")
                .help("Count stats or not.")
                .short("c")
                .long("count-stats")
                .takes_value(false),
        )
        .get_matches();

    let op: Op = Op::from_str(matches.value_of("op"));
    let ac: ArrayCon = ArrayCon::from_str(matches.value_of("array"));
    match op {
        Op::Unknown => return usage("Unknown or unspecified operation."),
        _ => (),
    }
    let n_len = parse_int(matches.value_of("size"), 40);
    let run_size = parse_int(matches.value_of("run_size"), 16);

    let mut n: Vec<i32> = ac.make_array(n_len);

    let mut out = object! {
        "op"    => op.to_string(),
        "array" => ac.to_string(),
        "num_elems"     => n_len,
    };

    let now = SystemTime::now();
    if matches.is_present("count") {
        let mut cnt = RealCounter {
            swaps: 0,
            compares: 0,
        };
        op.run(&mut n, run_size, &mut cnt);
        cnt.copy_to(&mut out);
    } else {
        op.run(&mut n, run_size, &mut DummyCounter {});
    }
    match now.elapsed() {
        Ok(elapsed) => {
            out["elapsed"] = elapsed.as_secs_f64().into();
        }
        Err(_) => (),
    };

    if op.does_sort() {
        out["is_sorted"] = JsonValue::Boolean(is_sorted(&n, 0, n_len));
    }
    if out.write(&mut io::stdout()).is_err() {
        return failure("Can't write to stdout");
    }
    println!("");
}
