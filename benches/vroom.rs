use atone::Vc;
use std::collections::VecDeque;
use std::time::{Duration, Instant};

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

const N: u32 = 1 << 22;

fn main() {
    let mut prevent_realloc = Vec::<Box<[u8; 16]>>::new();
    {
        let mut vs = Vec::new();
        let mut mx = 0.0f64;
        let mut sum = Duration::new(0, 0);
        for i in 0..N {
            let t = Instant::now();
            vs.push(i);
            let took = t.elapsed();
            mx = mx.max(took.as_secs_f64());
            sum += took;
            println!("{} vec {} ms", i, took.as_secs_f64() * 1000.0);
            // keep allocate things to prevent in-place growth.
            // the new allocations need to be large enough so that they don't all fit in the old
            // memory that is now freed in case the allocator tries to be smart.
            prevent_realloc.push(Box::new([0; 16]));
        }
        eprintln!(
            "Vec max: {:?}, mean: {:?}",
            Duration::from_secs_f64(mx),
            sum / N
        );
    }

    prevent_realloc.truncate(0);
    prevent_realloc.shrink_to_fit();

    {
        let mut vs = VecDeque::new();
        let mut mx = 0.0f64;
        let mut sum = Duration::new(0, 0);
        for i in 0..N {
            let t = Instant::now();
            vs.push_back(i);
            let took = t.elapsed();
            mx = mx.max(took.as_secs_f64());
            sum += took;
            println!("{} vecdeque {} ms", i, took.as_secs_f64() * 1000.0);
            prevent_realloc.push(Box::new([0; 16]));
        }
        eprintln!(
            "VecDeque max: {:?}, mean: {:?}",
            Duration::from_secs_f64(mx),
            sum / N
        );
    }

    prevent_realloc.truncate(0);
    prevent_realloc.shrink_to_fit();

    {
        let mut vs = Vc::new();
        let mut mx = 0.0f64;
        let mut sum = Duration::new(0, 0);
        for i in 0..N {
            let t = Instant::now();
            vs.push_back(i);
            let took = t.elapsed();
            mx = mx.max(took.as_secs_f64());
            sum += took;
            println!("{} atone {} ms", i, took.as_secs_f64() * 1000.0);
            prevent_realloc.push(Box::new([0; 16]));
        }
        eprintln!(
            "atone::Vc max: {:?}, mean: {:?}",
            Duration::from_secs_f64(mx),
            sum / N
        );
    }

    prevent_realloc.truncate(0);
    prevent_realloc.shrink_to_fit();
}
