#![feature(test)]

extern crate rand;
extern crate test;

extern crate gidsort;

use rand::{thread_rng, Rng};
use std::mem;
use test::Bencher;


fn gen_ascending(len: usize) -> Vec<u64> {
    (0..len as u64).collect()
}

fn gen_descending(len: usize) -> Vec<u64> {
    (0..len as u64).rev().collect()
}

fn gen_random(len: usize) -> Vec<u64> {
    let mut rng = thread_rng();
    rng.gen_iter::<u64>().take(len).collect()
}

fn gen_mostly_ascending(len: usize) -> Vec<u64> {
    let mut rng = thread_rng();
    let mut v = gen_ascending(len);
    for _ in (0usize..).take_while(|x| x * x <= len) {
        let x = rng.gen::<usize>() % len;
        let y = rng.gen::<usize>() % len;
        v.swap(x, y);
    }
    v
}

fn gen_mostly_descending(len: usize) -> Vec<u64> {
    let mut rng = thread_rng();
    let mut v = gen_descending(len);
    for _ in (0usize..).take_while(|x| x * x <= len) {
        let x = rng.gen::<usize>() % len;
        let y = rng.gen::<usize>() % len;
        v.swap(x, y);
    }
    v
}

fn gen_short_runs(len: usize) -> Vec<u64> {
    // swap odds and evens to create many short runs
    // 7 2 1 4 3 6 5 0
    let mut v = gen_ascending(len);
    let last = v.len() - 1;
    v.swap(0, last);
    for i in 1 .. last {
        if i % 2 == 0 {
            v.swap(i - 1, i);
        }
    }
    v
}

fn gen_big_random(len: usize) -> Vec<[u64; 16]> {
    let mut rng = thread_rng();
    rng.gen_iter().map(|x| [x; 16]).take(len).collect()
}

fn gen_big_ascending(len: usize) -> Vec<[u64; 16]> {
    (0..len as u64).map(|x| [x; 16]).take(len).collect()
}

fn gen_big_descending(len: usize) -> Vec<[u64; 16]> {
    (0..len as u64).rev().map(|x| [x; 16]).take(len).collect()
}

macro_rules! sort_bench {
    ($name:ident, $gen:expr, $len:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            b.iter(|| $gen($len).sort());
            b.bytes = $len * mem::size_of_val(&$gen(1)[0]) as u64;
        }
    }
}

sort_bench!(small_random_3bcda48a3, gen_random, 10);
sort_bench!(small_ascending_3bcda48a3, gen_ascending, 10);
sort_bench!(small_descending_3bcda48a3, gen_descending, 10);

sort_bench!(small_big_random_3bcda48a3, gen_big_random, 10);
sort_bench!(small_big_ascending_3bcda48a3, gen_big_ascending, 10);
sort_bench!(small_big_descending_3bcda48a3, gen_big_descending, 10);

sort_bench!(medium_random_3bcda48a3, gen_random, 100);
sort_bench!(medium_ascending_3bcda48a3, gen_ascending, 100);
sort_bench!(medium_descending_3bcda48a3, gen_descending, 100);

sort_bench!(large_short_runs_3bcda48a3, gen_short_runs, 10000);
sort_bench!(large_random_3bcda48a3, gen_random, 10000);
sort_bench!(large_ascending_3bcda48a3, gen_ascending, 10000);
sort_bench!(large_descending_3bcda48a3, gen_descending, 10000);
sort_bench!(large_mostly_ascending_3bcda48a3, gen_mostly_ascending, 10000);
sort_bench!(large_mostly_descending_3bcda48a3, gen_mostly_descending, 10000);

sort_bench!(large_big_random_3bcda48a3, gen_big_random, 10000);
sort_bench!(large_big_ascending_3bcda48a3, gen_big_ascending, 10000);
sort_bench!(large_big_descending_3bcda48a3, gen_big_descending, 10000);

macro_rules! new_sort_bench {
    ($name:ident, $gen:expr, $len:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            b.iter(|| gidsort::sort(&mut $gen($len)));
            b.bytes = $len * mem::size_of_val(&$gen(1)[0]) as u64;
        }
    }
}

new_sort_bench!(small_random_gidsort, gen_random, 10);
new_sort_bench!(small_ascending_gidsort, gen_ascending, 10);
new_sort_bench!(small_descending_gidsort, gen_descending, 10);

new_sort_bench!(small_big_random_gidsort, gen_big_random, 10);
new_sort_bench!(small_big_ascending_gidsort, gen_big_ascending, 10);
new_sort_bench!(small_big_descending_gidsort, gen_big_descending, 10);

new_sort_bench!(medium_random_gidsort, gen_random, 100);
new_sort_bench!(medium_ascending_gidsort, gen_ascending, 100);
new_sort_bench!(medium_descending_gidsort, gen_descending, 100);

new_sort_bench!(large_short_runs_gidsort, gen_short_runs, 10000);
new_sort_bench!(large_random_gidsort, gen_random, 10000);
new_sort_bench!(large_ascending_gidsort, gen_ascending, 10000);
new_sort_bench!(large_descending_gidsort, gen_descending, 10000);
new_sort_bench!(large_mostly_ascending_gidsort, gen_mostly_ascending, 10000);
new_sort_bench!(large_mostly_descending_gidsort, gen_mostly_descending, 10000);

new_sort_bench!(large_big_random_gidsort, gen_big_random, 10000);
new_sort_bench!(large_big_ascending_gidsort, gen_big_ascending, 10000);
new_sort_bench!(large_big_descending_gidsort, gen_big_descending, 10000);
