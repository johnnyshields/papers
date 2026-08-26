/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Shields.Combinatorics.Young.SkewSchurPolynomial.Basic
import Shields.Combinatorics.Young.SkewSchurPolynomial.Super
import Shields.Combinatorics.Young.SkewSchurPolynomial.Index

/-!
# Skew Schur polynomials and the supersymmetric hook criterion

Mathlib has no skew Young diagram, no skew Schur polynomial, and no supersymmetric
(two-alphabet) Schur function, so there is no object for a hook criterion to be stated about.
This supplies the objects and proves the criterion.
`Shields.Combinatorics.Young.SchurPolynomial` carries the one-alphabet straight-shape theory
this builds on.

## Main definitions

* `Shields.skewCells`, `Shields.SkewSSYT`, `Shields.BoundedSkewSSYT`: the skew diagram
  `lam.cells \ mu.cells`, its semistandard fillings, and those with entries `< n`, with a
  `Fintype` instance.  A skew row and a skew column are each an interval, so both order
  conditions need only their endpoints: `mu` is a lower set, so `(i, j₁) ∉ mu` already gives
  `(i, j₂) ∉ mu` for `j₁ ≤ j₂`.
* `Shields.skewSchur`: the skew Schur polynomial `s_{λ/μ}(x_0, …, x_{n-1})`, the generating
  function of `BoundedSkewSSYT` weighted by `∏` over the skew cells.
* `Shields.SuperSkewSSYT`: a **super semistandard tableau** of shape `lam / mu` over `b` even
  and `a` odd letters, in the sense of Berele--Regev: weakly increasing in both directions, with
  an even letter allowed to repeat along a row but not down a column and an odd letter down a
  column but not along a row.  Letters are naturals, the even alphabet `< b` first.
* `Shields.superSkewSchur`: the supersymmetric skew Schur function, defined as the generating
  function of those tableaux.  The Berele--Regev branching sum over the interval
  `youngIcc mu lam` is a **theorem** about it, `superSkewSchur_eq_branching`, and needs
  `mu ≤ lam` -- without containment the branching sum is empty while tableaux still exist.
* `Shields.NoBigRect`: the skew shape `lam / mu` contains no block of `b+1` rows by `a+1`
  columns.
* `Shields.betaDiagram`, `Shields.belowCount`, `Shields.tailSet`, `Shields.BlockCondition`:
  the index dictionary, a self-contained statement about `Finset ℕ` and `YoungDiagram` that
  turns the hook condition into a packing rule on an index set.

## Main statements

* `Shields.skewSchur_pos_iff`: over `ℝ` with positive variables, `s_{λ/μ}` is positive exactly
  when every column of `lam/mu` has height at most `n`.  The witness for the positive half is
  `skewHighestWeight`, whose entry at `(i, j)` is `i - mu.colLen j`.  This is the hook
  criterion at zero odd variables.
* `Shields.skewColLen_transpose`: conjugation turns the column bound on
  `lam.transpose / nu.transpose` into the row bound on `lam / nu`, so the second factor of the
  branching sum needs no separate argument.
* `Shields.superSkewSchur_eq_branching`: **the Berele--Regev branching rule.**  A super tableau
  splits at the boundary between the two alphabets; the cells carrying an even letter form a
  skew shape `nu / mu`, which is the intermediate diagram of the sum.  The even half is an
  ordinary tableau of `nu / mu` and the odd half is one of the *conjugate* shape
  `lam' / nu'`, which is where the transpose in the second factor comes from.
* `Shields.superSkewSchur_pos_iff`: **the supersymmetric hook criterion.**  With `mu ≤ lam` and
  all variables positive, it is positive exactly when `NoBigRect`, equivalently
  `lam.rowLen (i + b) ≤ mu.rowLen i + a` for every `i`.  The vanishing half splits each `nu` by
  whether the lower-left corner of the block lies in it; the positive half evaluates at
  `ν_u = max(μ_u, λ_u - a)`, realized as `mu ⊔ dropCols lam a`.
* `Shields.superSkewSchur_bot_pos_iff`: the straight-shape form, `λ_{b+1} ≤ a`, i.e. `(b, a)`
  hook containment.
* `Shields.indexHook_iff_blockCondition`, `Shields.superSkewSchur_betaDiagram_pos_iff`: the
  index dictionary and its composite with the criterion — every window of `a - b` consecutive
  sites in `{b, …, n-1}` holds at least `k - b` points of the index set.

Not proved here: skew Jacobi--Trudi, which is what identifies a Toeplitz minor with
`superSkewSchur`.  It is asserted nowhere.  `adm_iff_blockCondition_of_superSkewSchur` and
`adm_iff_rowLen_of_superSkewSchur_pos` take it as an explicit hypothesis `hJT` in their own
types, so nothing downstream can consume it by accident.

## Implementation notes

This module is a re-export.  The content sits in three files, cut by the object each is about:
`SkewSchurPolynomial.Basic` (skew shapes, skew tableaux, the skew Schur polynomial, and the
interval of Young diagrams the branching sum runs over), `SkewSchurPolynomial.Super` (super
tableaux, the Berele--Regev branching rule, and the hook criterion read off it), and
`SkewSchurPolynomial.Index` (the dictionary that turns the criterion into a packing rule on a row
set, in which no tableau appears).  Importing this file gets all three.

## Tags

Schur polynomial, skew Schur, supersymmetric, Young diagram, semistandard tableau, hook
-/
