[![Crates.io](https://img.shields.io/crates/v/atone.svg)](https://crates.io/crates/atone)
[![Documentation](https://docs.rs/atone/badge.svg)](https://docs.rs/atone/)
[![Build Status](https://dev.azure.com/jonhoo/jonhoo/_apis/build/status/atone?branchName=master)](https://dev.azure.com/jonhoo/jonhoo/_build/latest?definitionId=28&branchName=master)
[![Coverage Status](https://codecov.io/gh/jonhoo/atone/branch/master/graph/badge.svg)](https://codecov.io/gh/jonhoo/atone)
![Maintenance](https://img.shields.io/badge/maintenance-experimental-blue.svg)

A `VecDeque` (and `Vec`) variant that spreads resize load across pushes.

Most vector-like implementations, such as `Vec` and `VecDeque`, must
occasionally "resize" the backing memory for the vector as the number of
elements grows. This means allocating a new vector (usually of twice the
size), and moving all the elements from the old vector to the new one.
As your vector gets larger, this process takes longer and longer.

For most applications, this behavior is fine — if some very small number
of pushes take longer than others, the application won't even notice.
And if the vector is relatively small anyway, even those "slow" pushes
are quite fast. Similarly, if your vector grow for a while, and then
_stops_ growing, the "steady state" of your application won't see any
resizing pauses at all.

Where resizing becomes a problem is in applications that use vectors to
keep ever-growing state where tail latency is important. At large scale,
it is simply not okay for one push to take 30 milliseconds when most
take double-digit **nano**seconds. Worse yet, these resize pauses can
compound to create [significant spikes] in tail latency.

This crate implements a technique referred to as "incremental resizing",
in contrast to the common "all-at-once" approached outlined above. At
its core, the idea is pretty simple: instead of moving all the elements
to the resized vector immediately, move a couple each time a push
happens. This spreads the cost of moving the elements so that _each_
push becomes a little slower until the resize has finished, instead of
_one_ push becoming a _lot_ slower.

This approach isn't free, however. While the resize is going on, the old
vector must be kept around (so memory isn't reclaimed immediately), and
iterators and other vector-wide operations must access both vectors,
which makes them slower. Only once the resize completes is the old
vector reclaimed and full performance restored.

To help you decide whether this implementation is right for you, here's
a handy reference for how this implementation compares to the standard
library vectors:

 - Pushes all take approximately the same time.
   After a resize, they will be slower for a while, but only by a
   relatively small factor.
 - Memory is not reclaimed immediately upon resize.
 - Access operations are marginally slower as they must check two
   vectors.
 - The incremental vector is slightly larger on the stack.
 - The "efficiency" of the resize is slightly lower as the all-at-once
   resize moves the items from the small vector to the large one in
   batch, whereas the incremental does a series of pushes.

Also, since this crate must keep two vectors, it cannot guarantee that
the elements are stored in one contiguous chunk of memory. Since it must
move elements between then without losing their order, it is backed by
`VecDeque`s, which means that this is the case even after the resize has
completed. For this reason, this crate presents an interface that
resembles `VecDeque` more so than `Vec`. Where possible though, it
provides `Vec`-like methods. If you need contiguous memory, there's no
good way to do incremental resizing without low-level memory mapping
magic that I'm aware of.

## Benchmarks

There is a silly, but illustrative benchmark in `benches/vroom.rs`. It
just runs lots of pushes back-to-back, and measures how long each one
takes. The problem quickly becomes apparent:

```console
$ cargo bench --bench vroom > vroom.dat
Vec max: 2.440556ms, mean: 25ns
VecDeque max: 4.512806ms, mean: 25ns
atone::Vc max: 25.789µs, mean: 26ns
```

You can see that the standard library implementations have some pretty
severe latency spikes. This is more readily visible through a timeline
latency plot (`misc/vroom.plt`):

![latency spikes on resize](https://raw.githubusercontent.com/jonhoo/atone/master/misc/vroom.png)

Resizes happen less frequently as the vector grows, but they also take
longer _when_ they occur. With atone, those spikes are mostly gone.

## A note on in-place resizing

Some memory allocators have an API for increasing the size of an
allocation _in-place_. This operation doesn't always succeed, in which
case it falls back to a regular allocation plus a `memcpy`, but when it
does, the resize is basically free. `Vec` and `VecDeque` are
occasionally able to take advantage of this kind of in-place resizing,
whereas `atone::Vc` is not.

In practice, you are unlikely to get in-place resizing for vectors that
fit the use-case for `atone::Vc`. If the running application continues
to allocate memory elsewhere, chances are _something_ will get allocated
in the space on the heap after the current backing memory for the
vector, in which case in-place reallocation isn't possible.

`Vec` specifically also has a further optimization (I'm not sure what
it's called), in which it can perform in-place resizing even when the
allocation is surrounded on the heap. I assume that this involves some
memory remapping trickery. This only works on particular allocators
though (it does not work with `jemalloc` for example).

## Implementation

atone is backed by two `VecDeque`s. One is the "current" vector, and one
holds any leftovers from the last resize. Logically, the leftovers are
treated as the head of the vector, and the current vector is treated as
the tail. The "incremental" piece on push is then implemented by popping
elements from the leftovers and pushing them onto the front of the
current vector. It's this shifting, combined with the need to support
`push`, that made me go with `VecDeque`, since with a `Vec`, pushing to
the front would have to shift all the elements.

atone aims to stick as closely to `Vec` and `VecDeque` as it can, both
in terms of code and API. `src/lib.rs` is virtually
identical to [`src/liballoc/collections/vec_deque.rs` in `std`][src] (I
encourage you to diff them!).

## Why "atone"?

We make the vector atone with more expensive pushes for the sin it committed by resizing..?

[significant spikes]: https://twitter.com/jonhoo/status/1277618908355313670
[src]: https://github.com/rust-lang/rust/blob/master/src/liballoc/collections/vec_deque.rs

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
