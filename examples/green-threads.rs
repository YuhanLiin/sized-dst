use core::future::poll_fn;
use core::future::Future;
use core::{
    pin::Pin,
    task::{Context, Poll},
};

use futures_executor::block_on;
use sized_dst::Dst;

// Put Unpin to make the code easier to write. The logic is still sound even without Unpin.
type Thread = Dst<dyn Future<Output = ()> + Unpin, 128>;

#[derive(Default)]
struct Join<const N: usize> {
    threads: heapless::Vec<(Thread, bool), N>,
}

impl<const N: usize> Join<N> {
    fn push(&mut self, th: Thread) -> Result<(), ()> {
        self.threads.push((th, false)).map_err(drop)
    }
}

impl<const N: usize> Future for Join<N> {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut all_finished = true;
        for (th, finished) in &mut self.get_mut().threads {
            if !*finished {
                match Pin::new(th).poll(cx) {
                    Poll::Ready(()) => *finished = true,
                    Poll::Pending => all_finished = false,
                }
            }
        }

        if all_finished {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}

fn lazy(mut n: u32) -> impl Future<Output = ()> {
    let cnt = n;
    poll_fn(move |cx| {
        if n == 0 {
            println!("{cnt}");
            Poll::Ready(())
        } else {
            n -= 1;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    })
}

fn main() {
    let mut join = Join::<8>::default();
    join.push(Dst::new(poll_fn(|_| {
        println!("Instant");
        Poll::Ready(())
    })))
    .unwrap();
    join.push(Dst::new(lazy(3))).unwrap();
    join.push(Dst::new(lazy(2))).unwrap();
    join.push(Dst::new(lazy(1))).unwrap();

    // Expect output to be:
    // Instant
    // 1
    // 2
    // 3
    block_on(join);
}
