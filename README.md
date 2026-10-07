# Verification script for "Bounded Inbreeding in the Seven Immortals Problem: An Exact Threshold for n Founders"

Author: Jronny Amarante (independent researcher, Dumaguete City, Philippines)

`immortals.ts` reproduces every computational claim listed in the paper's Appendix:
the zero-inbreeding counts, Lemmas 1 and 2 on all pairs for n <= 7, the threshold
2^-n, the chain of Theorem 1 in exact arithmetic, and the frozen-semen comparison.

Run it with Node.js 22.18 or later, which runs TypeScript directly. No packages
are needed:

    node immortals.ts

It prints the computed values of Table 2 (Section 6) and ends with
`All claims verified.` Any failed claim stops the run with a message naming it.
A run takes about 10 seconds and 2 GB of memory.

License: MIT (see `LICENSE`).
