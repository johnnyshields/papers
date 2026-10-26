# algebraic-combinatorics (vendored)

A copy of 47 of the 52 Lean modules of
[facebookresearch/algebraic-combinatorics](https://github.com/facebookresearch/algebraic-combinatorics),
a Lean 4 formalization of Darij Grinberg's textbook
[*An Introduction to Algebraic Combinatorics*](https://arxiv.org/abs/2506.00738), built on Mathlib.

## Attribution

- **Authors:** Fabian Gloeckle ([`faabian`](https://github.com/faabian)) and the AlgebraicCombinatorics
  contributors, Meta Platforms, Inc.  Copyright (c) Meta Platforms, Inc. and affiliates.
- **Source:** upstream `main` at
  [`b6022318`](https://github.com/facebookresearch/algebraic-combinatorics/commit/b6022318e986a0c20764569208ba8ebbe1c04dbf),
  as ported to Lean and Mathlib `v4.34.1` by pull requests
  [#9](https://github.com/facebookresearch/algebraic-combinatorics/pull/9) and
  [#10](https://github.com/facebookresearch/algebraic-combinatorics/pull/10).
- **Textbook:** D. Grinberg, *An Introduction to Algebraic Combinatorics*, arXiv:2506.00738.
- **Blueprint:** <https://faabian.github.io/algebraic-combinatorics/>

## License

This directory is licensed under the Creative Commons Attribution-NonCommercial 4.0 International
License (CC BY-NC 4.0); see `LICENSE`.  It is **not** covered by the MIT license of the surrounding
`Vendor` directory, and it is used here for non-commercial research only.

## Changes from the source

- The modules `DesnanotJacobi`, `Determinants/LGV1`, `Determinants/LGV2`,
  `SymmetricFunctions/PieriJacobiTrudi` and `SymmetricFunctions/SSYTEquiv` are omitted, because
  they contain or depend on a `sorry`.
- Imports are rewritten from `AlgebraicCombinatorics.*` to `Vendor.AlgebraicCombinatorics.*`.
- Each `native_decide` is replaced by `decide +kernel` and marked `-- vendored: was `native_decide``.
  Twenty small-value examples in `Partitions/Basics.lean` that `decide +kernel` cannot check are
  removed, with their docstrings.
- The upstream root file is replaced by `../AlgebraicCombinatorics.lean`, which records the full
  audit.

Nothing else is changed.
