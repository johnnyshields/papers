/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/Setting.lean
import SkewRibbonCoarsenings.Defs

/-!
# The normalized setting and the support-separation statement

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:balance`
(`eq:uv`, `eq:FE`, `thm:support`, `prop:normalization`, `eq:mask`, `eq:mask-odd`).

`NormalizedSetting` is the setting the sections `sec:detector` and `sec:realization` retain
("the normalized cut functions `b, c`, comparison functions `u, v, w`, and divisors `e, d` from
`prop:normalization`").  Its hypothesis fields are the hypotheses of `thm:support` together with
the gcd normalization of `eq:gcd-normalization`; its conclusion fields are the conclusions of
`prop:normalization`.  The theorem producing a `NormalizedSetting` is proved in the balance
modules.
`SupportSeparation` is the statement of `thm:support`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

/-- A function on `ℤ/n` is odd. -/
def IsOdd {n : ℕ} (f : ZMod n → ℤ) : Prop := ∀ x, f (-x) = -f x

/-- `p` is a period of `f` on `ℤ/n`. -/
def IsPeriod {n : ℕ} (f : ZMod n → ℤ) (p : ℕ) : Prop := ∀ x : ZMod n, f (x + (p : ZMod n)) = f x

/-- `e` is the least period of `f` on `ℤ/n`: the least positive divisor of `n` that is a period. -/
def IsLeastPeriod {n : ℕ} (f : ZMod n → ℤ) (e : ℕ) : Prop :=
  0 < e ∧ e ∣ n ∧ IsPeriod f e ∧ ∀ p, 0 < p → p ∣ n → IsPeriod f p → e ≤ p

/-- `gcd(n, supp f)` of `eq:gcd-normalization`, computed on representatives in `{0, …, n-1}`. -/
def supportGcd {n : ℕ} (f : ZMod n → ℤ) : ℕ :=
  Nat.gcd n (((Finset.range n).filter fun k : ℕ => f (k : ZMod n) ≠ 0).gcd id)

/-- The odd function `u(x) = b(x) - c(-x)` of `eq:uv`. -/
def uFun (n : ℕ) (S S' : Finset ℕ) (x : ZMod n) : ℤ := cutInd n S x - cutInd n S' (-x)

/-- The function `v(x) = b(x) - c(x)` of `eq:uv`. -/
def vFun (n : ℕ) (S S' : Finset ℕ) (x : ZMod n) : ℤ := cutInd n S x - cutInd n S' x

/-- The functional equation `eq:FE` for a pair of functions on `ℤ/n`. -/
def FEq {n : ℕ} (u v : ZMod n → ℤ) : Prop :=
  ∀ x y, u x * v y + v x * u y = u (x + y) * (v x + v y) + v (x + y) * (u x + u y)

/-- The function `w` of `eq:w`: `u` off the `d`-grid and zero on it. -/
def wFun (n : ℕ) (S S' : Finset ℕ) (d : ℕ) (x : ZMod n) : ℤ :=
  if d ∣ x.val then 0 else uFun n S S' x

/-- The mask `𝓑_p` of `eq:mask`: the cut indicator with the `p`-grid zeroed. -/
def maskFun (n : ℕ) (S : Finset ℕ) (p : ℕ) (x : ZMod n) : ℤ :=
  if p ∣ x.val then 0 else cutInd n S x

/-- The statement of `thm:support` (`thm:support`): nonzero odd `u, v : ℤ/n → {-1,0,1}` with
`u v = 0` satisfying `eq:FE` have a support generating a proper subgroup of `ℤ/n`.  "Support of
`f` generates a proper subgroup" is `supportGcd f ≠ 1` (the subgroup generated is
`gcd(n, supp f) ℤ/n`). -/
def SupportSeparation : Prop :=
  ∀ (n : ℕ) (u v : ZMod n → ℤ), 2 ≤ n → (∀ x, u x ∈ ({-1, 0, 1} : Set ℤ)) →
    (∀ x, v x ∈ ({-1, 0, 1} : Set ℤ)) → u ≠ 0 → v ≠ 0 → IsOdd u → IsOdd v →
    (∀ x, u x * v x = 0) → FEq u v → supportGcd u ≠ 1 ∨ supportGcd v ≠ 1

/-- The normalized setting of `prop:normalization` for two compositions of weight `n` with cut
sets `S, S'`: two-block inventories equal, `u, v` nonzero (the originals are neither identical
nor reversed), `eq:FE`, and the orientation normalization `eq:gcd-normalization`, with the
conclusions of `prop:normalization` as fields.  Here `d = gcd(n, supp v)` and `e` is the least
period of `w`. -/
structure NormalizedSetting (n : ℕ) (S S' : Finset ℕ) (d e : ℕ) : Prop where
  cuts : IsCutSet n S
  cuts' : IsCutSet n S'
  tau_eq : ∀ x : ZMod n, cutInd n S x + cutInd n S (-x) = cutInd n S' x + cutInd n S' (-x)
  u_ne : uFun n S S' ≠ 0
  v_ne : vFun n S S' ≠ 0
  fe : FEq (uFun n S S') (vFun n S S')
  d_eq : d = supportGcd (vFun n S S')
  gu_dvd : supportGcd (uFun n S S') ∣ d
  gu_ne : supportGcd (uFun n S S') ≠ d
  w_ne : wFun n S S' d ≠ 0
  w_odd : IsOdd (wFun n S S' d)
  w_period : IsPeriod (wFun n S S' d) d
  e_least : IsLeastPeriod (wFun n S S' d) e
  three_le_e : 3 ≤ e
  e_dvd_d : e ∣ d
  d_lt : d < n
  three_le_ratio : 3 ≤ n / d
  mask_odd : ∀ p, e ∣ p → p ∣ d →
    ∀ x : ZMod n, maskFun n S p x - maskFun n S p (-x) = wFun n S S' d x

end SkewRibbonCoarsenings
