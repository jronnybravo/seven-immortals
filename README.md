# Verification script for "Bounded Inbreeding in the Seven Immortals Problem: An Exact Threshold for n Founders"

Author: Jronny Amarante (independent researcher, Dumaguete City, Philippines)

`immortals.ts` reproduces every computational claim listed in the paper's Appendix:
the zero-inbreeding counts, Lemmas 1 and 2 on all pairs for n <= 6, the threshold
2^-n, the chain of Theorem 1 in exact arithmetic, and the frozen-semen comparison.

Run it with Node.js 22.18 or later, which runs TypeScript directly. No packages
are needed:

    node immortals.ts

It prints the computed values of the table in Section 6 and ends with
`All claims verified.` Any failed claim stops the run with a message naming it.
A run takes a few seconds.

To add the n = 7 row of that table (19873 nodes, about 197 million pairs), run:

    node immortals.ts --seven

That run needs about 3 GB of memory and takes about 20 seconds.

License: MIT (see `LICENSE`).
