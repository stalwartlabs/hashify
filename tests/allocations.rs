/*
 * SPDX-FileCopyrightText: 2025 Stalwart Labs LLC <hello@stalw.art>
 *
 * SPDX-License-Identifier: Apache-2.0 OR MIT
 */

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::hint::black_box;

struct CountingAllocator;

thread_local! {
    static ALLOCATIONS: Cell<usize> = const { Cell::new(0) };
}

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.with(|count| count.set(count.get() + 1));
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

fn switch_map(key: &[u8]) -> Option<&'static u32> {
    hashify::map! { key, u32, "get" => 1, "head" => 2, "post" => 3, "a long key of many bytes" => 4, }
}

fn flat_set(key: &[u8]) -> bool {
    hashify::set_ignore_case! { key,
        "a", "bb", "ccc", "dddd", "eeeee", "ffffff", "ggggggg", "hhhhhhhh", "iiiiiiiii",
        "jjjjjjjjjj", "kkkkkkkkkkk", "llllllllllll", "mmmmmmmmmmmmm", "nnnnnnnnnnnnnn",
        "ooooooooooooooo", "pppppppppppppppp", "qqqqqqqqqqqqqqqqq", "rrrrrrrrrrrrrrrrrr",
        "a key that is longer than sixteen bytes",
    }
}

fn hashed_fnc_map(key: &[u8]) -> u32 {
    hashify::fnc_map! { key,
        "key00" => 0, "key01" => 1, "key02" => 2, "key03" => 3, "key04" => 4, "key05" => 5,
        "key06" => 6, "key07" => 7, "key08" => 8, "key09" => 9, "key10" => 10, "key11" => 11,
        "key12" => 12, "key13" => 13, "key14" => 14, "key15" => 15, "key16" => 16,
        "key17" => 17, "key18" => 18, "key19" => 19, "key20" => 20, "key21" => 21,
        "key22" => 22, "key23" => 23, "key24" => 24, "key25" => 25, "key26" => 26,
        "key27" => 27, "key28" => 28, "key29" => 29, "key30" => 30, "key31" => 31,
        "key32" => 32, "key33" => 33, "key34" => 34, "key35" => 35, "key36" => 36,
        "key37" => 37, "key38" => 38, "key39" => 39, "key40" => 40, "key41" => 41,
        "key42" => 42, "key43" => 43, "key44" => 44, "key45" => 45, "key46" => 46,
        "key47" => 47, "key48" => 48, "key49" => 49, "key50" => 50, "key51" => 51,
        "key52" => 52, "key53" => 53, "key54" => 54, "key55" => 55, "key56" => 56,
        "key57" => 57, "key58" => 58, "key59" => 59, "key60" => 60, "key61" => 61,
        "key62" => 62, "key63" => 63, "key64" => 64, "key65" => 65, "key66" => 66,
        "key67" => 67, "key68" => 68, "key69" => 69, "a key that is longer than sixteen bytes" => 70,
        _ => u32::MAX
    }
}

#[test]
fn lookups_never_allocate() {
    let probes: [&[u8]; 8] = [
        b"get",
        b"GET",
        b"missing",
        b"hhhhhhhh",
        b"key42",
        b"key99",
        b"a key that is longer than sixteen bytes",
        b"",
    ];
    let before = ALLOCATIONS.with(Cell::get);
    for _ in 0..1000 {
        for probe in probes {
            black_box(switch_map(black_box(probe)));
            black_box(flat_set(black_box(probe)));
            black_box(hashed_fnc_map(black_box(probe)));
        }
    }
    assert_eq!(ALLOCATIONS.with(Cell::get), before);
    assert_eq!(hashed_fnc_map(b"key42"), 42);
    assert!(flat_set(b"HHHHHHHH"));
    assert_eq!(switch_map(b"head"), Some(&2));
}
