## The centered heap

It had been bugging me that an in-place merge sort was so impractical.

So I wrote this up, went down the rabbit hole, and devised a way to make a movable heap. It does work, my numbers show it is reasonably scalable.

But I don't want to oversell it: *this is not better than a simple heap sort.*

What you get are in-place merges with constant memory requirements and amortized O(log n) operations. We'll get into the fine print of what "amortized" means below.

### Revisiting a standard heap

A standard heap is a binary tree:

               root
             /      \
        node          node
       /    \
    node   node   ---    ----

It then adds two constraints:

 * A parent node is always "better than" the children
 * Trailing nodes can be empty

Because all parent nodes are "better than" their children, the "best" node is always available
at the root of the heap.

Because trailing nodes can be empty, a heap can be stored in an array, and all heap operations can
be performed inline within the array.

But only the heap's tail can move:

    [     heap             |       other data               ]
     ^root                 ^tail

This is excellent for priority queues and heap sorts, since the array is dedicated solely to that
task.

### What a centered heap changes

A centered heap is still a binary tree, but we've changed the rules about trailing nodes:

              center
             /      \
        node          node
            \        /
    ----   node   node    ----

And we add three markers _low_, _center_ and _high_.

The center points at (is) the root, and the low and high markers note where the heap begins and ends.

Thus we have something like this:

    [  other data  |      heap         |    other data     ]
                low^        ^center    ^high

The rules for child nodes are a little different from heaps. We're adjusting our indices to treat the center as 0 and allowing for negative and positive children:

    -4 -3 -2 -1  0  1  2  3  4
                 c
              n     n
        n  n           n  n

We further expand the common pop and push to have left and right variants.

    Push left:
        . . I [       C     ] . . .
        . . [         C     ] . . .
    I is now pushed into the heap, and the low bound moves left.
    
    Push right:
        . . . [       C     ] I . .
        . . . [       C       ] . .
    I is now pushed into the heap, and the high bound moves right.
    
    Pop left:
        . . [         C     ] . . .
        . . C [       C'    ] . . .
    C is popped to the left, and the next best C' is now at the center.
    
    Pop right:
        . . . [       C       ] . .
        . . . [       C'    ] C . .
    C is popped to the right, and the next best C' is now at the center.

There are other functions combining pops and pushes and sliding the whole heap, but those are the
basics.

### Recentering and amortized performance

When you pop past the center, it's no longer valid. Thus we have to "recenter" the heap, which is
equivalent to the "heapify" function of standard heaps. (It issues a number of sift-down operations
if you're familiar with how heaps are implemented.)

For most algorithms, though, we can be smart about how we recenter. We've typically shown the center
to be in, well, the center, but there's no requirement for that. Consider:

    . . . P1 P2 P3 [C            ] . . . .

We've been popping to the left, and are about to invalidate our center. We should thus recenter all
the way to the right:

    . . . P1 P2 P3 P4 [         C] . . . .

If our c-heap has n elements, we'll run n log n sift-downs. If we're pushing and popping in the same
direction, we'll tend to recenter every n elements for the size of our window.

Thus after we amortize recentering for a c-heap that is typically n elements large, the cost is
about one sift-down (log n operations) per pop.

So a pop amortizes to log n operations for the recenter, plus the constant cost of log n operations
for the pop itself.

And a push never recenters, so it's log n operations for the push.

## The demo utility

Part of my motivation was to learn a bit of Rust, so I apologize for the beginner code. Hopefully
nothing here will frighten the horses.

It has a simple CLI that lets you build an array, then pick an operation, and you can gather stats
on compares and swaps if you like. You can also use `-o Sort` to compare how laughably slow it is
compared to the native `Vec.sort()` method.

The debug target spams a *lot* of information. It's also running many redundant invariant checks that `--release` turns off.

I haven't exercised all the methods of `Cheap` yet, so, except for the checks, those annotated with `#[allow(dead_code)]` are likely buggy.

If you've never used Rust, you'll need to install it, and you should be able to do a simple:

    cargo run -- --help
    cargo run --release -- --help

## Does it really scale?

I ran some tests with the merge sort and giving it a reversed array, which is a pretty good worst case.

The growth in the number of compares and swaps per element is trending downward, so I'm not sure if the overall complexity is strictly O(n log n), but it's also not unreasonable.

| Size     | Compares   | Swaps      | Compares / N | Swaps / N | Comp grow | Swap grow |
| -------- | ---------- | ---------- | ------------ | --------- | --------- | --------- |
| 4        | 9          | 6          | 2.25         | 1.5       | -         | -         |
| 8        | 32         | 22         | 4            | 2.75      | 1.778     | 1.833     |
| 16       | 118        | 74         | 7.38         | 4.63      | 1.845     | 1.684     |
| 32       | 402        | 230        | 12.56        | 7.19      | 1.702     | 1.553     |
| 64       | 1244       | 664        | 19.44        | 10.38     | 1.548     | 1.444     |
| 128      | 3594       | 1810       | 28.08        | 14.14     | 1.444     | 1.362     |
| 256      | 9840       | 4722       | 38.44        | 18.45     | 1.369     | 1.305     |
| 512      | 25771      | 11922      | 50.33        | 23.29     | 1.309     | 1.262     |
| 1024     | 65361      | 29320      | 63.83        | 28.63     | 1.268     | 1.229     |
| 2048     | 161603     | 70644      | 78.91        | 34.49     | 1.236     | 1.205     |
| 4096     | 391421     | 167500     | 95.56        | 40.89     | 1.211     | 1.186     |
| 8192     | 931695     | 391730     | 113.73       | 47.82     | 1.19      | 1.169     |
| 16384    | 2184531    | 904656     | 133.33       | 55.22     | 1.172     | 1.155     |
| 32768    | 5061357    | 2067486    | 154.46       | 63.09     | 1.158     | 1.143     |
| 65536    | 11608747   | 4684948    | 177.14       | 71.49     | 1.147     | 1.133     |
| 131072   | 26382571   | 10538678   | 201.28       | 80.4      | 1.136     | 1.125     |
| 262144   | 59484663   | 23540708   | 226.92       | 89.8      | 1.127     | 1.117     |
| 524288   | 133209364  | 52266700   | 254.08       | 99.69     | 1.12      | 1.11      |
| 1048576  | 296540917  | 115459604  | 282.8        | 110.11    | 1.113     | 1.105     |
| 2097152  | 656577504  | 253900734  | 313.08       | 121.07    | 1.107     | 1.1       |
| 4194304  | 1446238418 | 555798460  | 344.81       | 132.51    | 1.101     | 1.094     |
| 8388608  | 3171292780 | 1211666326 | 378.05       | 144.44    | 1.096     | 1.09      |
| 16777216 | 6926010907 | 2632056058 | 412.82       | 156.88    | 1.092     | 1.086     |

