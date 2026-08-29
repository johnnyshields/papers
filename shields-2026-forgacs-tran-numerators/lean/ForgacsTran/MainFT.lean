/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.AngularDiscrepancyFT
import ForgacsTran.Main
import ForgacsTran.QuadraticDefect

/-!
# `thm:main` off the angular discrepancy

`Main.main_bound` and `Main.main_bound_interval` run on an `FTInputs`, whose
`interiorZeros` and `bulk_zero_count` fields are the analytic supply.  This
module builds that bundle instead of assuming it: the zero set is the one
`AngularWindow.exists_windowZeros` produces on the full angular interval
`(0,π/r)`, and the count is `eq:angular-distinct-lower` there.

That is `subsec:proof`'s own route to `thm:main` — "apply
`prop:angular-discrepancy` to the full angular interval `(0,π/r)`" — with the
canonical Laurent reduction between the two sequences: `lem:laurent-reduction`
identifies `P_m` with `F_{m-λ_N}` for large `m`
(`LaurentReduction.reduction_coeff_eventually`) and
`eq:exact-eventual-degree-shift` carries the degree bound across the shift.

## Main statements

* `exists_ftInputs_of_supply` — the analytic bundle, built.
* `main_bound_of_supply`, `main_bound_interval_of_supply` — `thm:main` clauses 1
  and 2, with **no interior-zero binder**: what is assumed is
  `FTPhaseSupply`, which is `thm:FT-geometry`, `lem:amplitude-divisor` and
  `thm:weighted-dominance`, and the zero set is a conclusion.
* `interior_distinct_count_of_supply` — clause 2(iii) off the same bundle.

## Implementation notes

**What the defect constant is.**  `Cbulk = ⌈C₀ + C₁ deg B_N⌉`, with `C₀` and `C₁`
the constants of `prop:angular-discrepancy` — so the eventual defect is at most
`C₀ + C₁ deg B_N`, which is `thm:main` clause 3's shape.  The ceiling is the
passage from the real bound the count gives to the `ℕ`-valued field
`FTInputs.Cbulk`, and it is where the manuscript's "after increasing the
denominator-only constant by one" goes.

**Why the count is taken at the reduced index.**  `FTPhaseSupply` is a statement
about `F_M`, and `thm:main` is about `P_m`; the two are the same polynomial only
for large `m`, so the zero set is defined by `dite` and is empty below the
threshold.  The `FTInputs` fields quantify over *every* index, and an empty set
discharges them there — the count field is the only one that is eventual, which
is exactly the asymmetry `thm:main` states between clause 1 (every index) and
clause 2 (eventual).

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Main theorem»
(`subsec:intro-main`, `thm:main`) off «Angular discrepancy and proof of the main
theorem» (`subsec:proof`, `prop:angular-discrepancy`) and «Canonical Laurent
reduction and eventual degree» (`sec:reduction`, `lem:laurent-reduction`,
`eq:exact-eventual-degree-shift`).

## Tags

main theorem, angular discrepancy, Laurent reduction, exceptional zero
-/

open Polynomial

namespace ForgacsTran

open Set Real

/-- The window over the whole angular interval sits on the positive ray, which is
`I_{Q,r} ⊆ (0,∞)` of `thm:FT-geometry`. -/
theorem ftWindow_subset_posRay {z : ℝ → ℝ} {r : ℕ}
    (hzpos : ∀ θ ∈ Ioo 0 (π / r), 0 < z θ) : ftWindow z 0 (π / r) ⊆ posRay :=
  Set.image_mono fun _ hy => by
    obtain ⟨θ, hθ, rfl⟩ := hy; exact hzpos θ hθ

/-- **The analytic bundle of `thm:main`, built rather than assumed.**  Every
field is discharged from `FTPhaseSupply` and the canonical Laurent reduction; no
zero set and no count is carried in.

`Cbulk = ⌈C₀ + C₁ deg B_N⌉`, and `C₀`, `C₁` are the constants of
`prop:angular-discrepancy`, built from `h`, `κ₀`, `κ₁` alone. -/
theorem exists_ftInputs_of_supply {Q : ℂ[X]} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) {N : (ℂ[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    (coeffPoly : ℕ → ℂ[X])
    (hP : ∀ m, denomConv (ftDenom Q r) coeffPoly m = (swapVars N).coeff m)
    {z τ : ℝ → ℝ}
    (hzmono : StrictMonoOn z (Ioo 0 (π / r))) (hzcont : ContinuousOn z (Ioo 0 (π / r)))
    (hτ : ∀ θ ∈ Ioo 0 (π / r), 0 < τ θ)
    (hzpos : ∀ θ ∈ Ioo 0 (π / r), 0 < z θ)
    (hsupply : ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply Q (laurentWeight Q r N) r z τ hcol κ₀ κ₁ M) :
    ∃ (C₀ C₁ : ℝ) (H : FTInputs), 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      H.coeffPoly = coeffPoly ∧ H.ftSet = ftWindow z 0 (π / r) ∧
      ((H.Cbulk : ℕ) : ℝ) ≤ C₀ + C₁ * ((laurentWeight Q r N).natDegree : ℝ) + 1 := by
  classical
  obtain ⟨hcol, κ₀, κ₁, hh, hκ₀, hκ₁, M₀, hM₀⟩ := hsupply
  have hπ : (0 : ℝ) < π := pi_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hπne : (π : ℝ) ≠ 0 := ne_of_gt hπ
  have hrne : ((r : ℕ) : ℝ) ≠ 0 := ne_of_gt hrR
  set B : ℂ[X] := laurentWeight Q r N with hB
  set defect : ℝ := ((4 * hcol + 1 + κ₀) / π + 2)
    + (κ₁ / π + 2) * (B.natDegree : ℝ) with hdefect
  have hdefectnn : 0 ≤ defect := by rw [hdefect]; positivity
  -- `eq:angular-distinct-lower` on the whole angular interval
  have key : ∀ M : ℕ, M₀ ≤ M → ∃ Z : Finset ℂ,
      ((M : ℝ) + 1) / r - defect ≤ (Z.card : ℝ) ∧
      (∀ w ∈ Z, (ftCoeffPoly Q B r M).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ ftWindow z 0 (π / r)) := by
    intro M hM
    obtain ⟨Z, hZc, hZr, hZm⟩ := exists_windowZeros_of_supply hh hκ₀ hκ₁ hzmono hzcont hτ
      (hM₀ M hM) (α := 0) (β := π / r) le_rfl (by positivity) le_rfl
    refine ⟨Z, ?_, hZr, hZm⟩
    have hrw : ((M : ℝ) + 1) * (π / r - 0) / π = ((M : ℝ) + 1) / r := by
      rw [sub_zero]
      field_simp
    rw [hrw] at hZc
    rw [hdefect]
    linarith
  choose Zbig hZc hZr hZm using key
  -- `lem:laurent-reduction`: `P_m = F_{m - λ_N}` for large `m`
  obtain ⟨m1, hred⟩ := reduction_coeff_eventually Q hr hQ0 hN hproper coeffPoly
    (ftCoeffPoly Q B r) hP (fun M => denomConv_ftCoeffPoly Q B hr hQ0 M)
  set sh : ℕ → ℕ := fun m => (((m : ℤ) - laurentShift Q r N).toNat) with hsh
  have hshdef : ∀ m, sh m = (((m : ℤ) - laurentShift Q r N).toNat) := fun _ => rfl
  set Zfun : ℕ → Finset ℂ := fun m =>
    if h : M₀ ≤ sh m ∧ m1 ≤ m then Zbig (sh m) h.1 else ∅ with hZfun
  have hZpos : ∀ m, ∀ h : M₀ ≤ sh m ∧ m1 ≤ m, Zfun m = Zbig (sh m) h.1 := by
    intro m h; rw [hZfun]; exact dif_pos h
  have hZneg : ∀ m, ¬(M₀ ≤ sh m ∧ m1 ≤ m) → Zfun m = ∅ := by
    intro m h; rw [hZfun]; exact dif_neg h
  have hroot : ∀ m, ∀ w ∈ Zfun m, (coeffPoly m).IsRoot w := by
    intro m w hw
    by_cases h : M₀ ≤ sh m ∧ m1 ≤ m
    · rw [hZpos m h] at hw
      rw [hred m h.2]
      exact hZr (sh m) h.1 w hw
    · rw [hZneg m h] at hw; simp at hw
  have hmem : ∀ m, ∀ w ∈ Zfun m, w ∈ ftWindow z 0 (π / r) := by
    intro m w hw
    by_cases h : M₀ ≤ sh m ∧ m1 ≤ m
    · rw [hZpos m h] at hw
      exact hZm (sh m) h.1 w hw
    · rw [hZneg m h] at hw; simp at hw
  have hcount : ∃ m0 : ℕ, ∀ m, m0 ≤ m → sh m / r - ⌈defect⌉₊ ≤ (Zfun m).card := by
    refine ⟨max m1 (M₀ + (laurentShift Q r N).toNat), fun m hm => ?_⟩
    have hm1 : m1 ≤ m := le_trans (le_max_left _ _) hm
    have hm2 : M₀ + (laurentShift Q r N).toNat ≤ m := le_trans (le_max_right _ _) hm
    have hshM : M₀ ≤ sh m := by
      have hcast : (M₀ : ℤ) + ((laurentShift Q r N).toNat : ℤ) ≤ (m : ℤ) := by
        exact_mod_cast hm2
      rw [hshdef]; omega
    have hZeq : Zfun m = Zbig (sh m) hshM := hZpos m ⟨hshM, hm1⟩
    have hcard := hZc (sh m) hshM
    have hdiv : ((sh m / r : ℕ) : ℝ) ≤ ((sh m : ℝ) + 1) / r := by
      refine le_trans Nat.cast_div_le ?_
      gcongr
      linarith
    have hceil : defect ≤ (⌈defect⌉₊ : ℝ) := Nat.le_ceil _
    have hreal : ((sh m / r : ℕ) : ℝ)
        ≤ ((Zbig (sh m) hshM).card : ℝ) + (⌈defect⌉₊ : ℝ) := by linarith
    have hnat : sh m / r ≤ (Zbig (sh m) hshM).card + ⌈defect⌉₊ := by exact_mod_cast hreal
    rw [hZeq]
    omega
  refine ⟨(4 * hcol + 1 + κ₀) / π + 2, κ₁ / π + 2,
    FTInputs.ofBivariateNumerator coeffPoly (ftCoeffPoly Q B r)
      (ftWindow z 0 (π / r)) (ftWindow_subset_posRay hzpos) Zfun ⌈defect⌉₊ hroot hmem
      Q r hr hQ0 N hN hproper hP (fun M => denomConv_ftCoeffPoly Q B hr hQ0 M) hcount,
    by positivity, by positivity, rfl, rfl, ?_⟩
  have hceil : (⌈defect⌉₊ : ℝ) < defect + 1 := Nat.ceil_lt_add_one hdefectnn
  simp only [FTInputs.ofBivariateNumerator]
  rw [hdefect] at hceil
  linarith

/-- **`thm:main` clause 1, off the discrepancy.**  A single constant bounds the
zeros of every nonzero `P_m` off the positive ray.  No interior-zero supply is
assumed: `FTPhaseSupply` is `thm:FT-geometry`, `lem:amplitude-divisor` and
`thm:weighted-dominance`, and the zeros are produced by the phase count. -/
theorem main_bound_of_supply {Q : ℂ[X]} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) {N : (ℂ[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    (coeffPoly : ℕ → ℂ[X])
    (hP : ∀ m, denomConv (ftDenom Q r) coeffPoly m = (swapVars N).coeff m)
    {z τ : ℝ → ℝ}
    (hzmono : StrictMonoOn z (Ioo 0 (π / r))) (hzcont : ContinuousOn z (Ioo 0 (π / r)))
    (hτ : ∀ θ ∈ Ioo 0 (π / r), 0 < τ θ)
    (hzpos : ∀ θ ∈ Ioo 0 (π / r), 0 < z θ)
    (hsupply : ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply Q (laurentWeight Q r N) r z τ hcol κ₀ κ₁ M) :
    ∃ C : ℕ, ∀ m, coeffPoly m ≠ 0 →
      (exceptionalRoots (coeffPoly m) posRay).card ≤ C := by
  obtain ⟨-, -, H, -, -, hc, -, -⟩ :=
    exists_ftInputs_of_supply hr hQ0 hN hproper coeffPoly hP hzmono hzcont hτ hzpos
      hsupply
  obtain ⟨C, hC⟩ := main_bound H
  rw [hc] at hC
  exact ⟨C, hC⟩

/-- **`thm:main` clause 2, off the discrepancy.**  For all large `m`, at most
`C ≤ C₀ + C₁deg B_N + 1` zeros of `P_m` outside the angular window
`z((0,π/r))` — which is `I_{Q,r}` — counted with multiplicity, together with at
least `deg P_m - C` **distinct** zeros inside it.  Both constants come from
`prop:angular-discrepancy`, so the defect is linear in `deg B_N`. -/
theorem main_bound_interval_of_supply {Q : ℂ[X]} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) {N : (ℂ[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    (coeffPoly : ℕ → ℂ[X])
    (hP : ∀ m, denomConv (ftDenom Q r) coeffPoly m = (swapVars N).coeff m)
    {z τ : ℝ → ℝ}
    (hzmono : StrictMonoOn z (Ioo 0 (π / r))) (hzcont : ContinuousOn z (Ioo 0 (π / r)))
    (hτ : ∀ θ ∈ Ioo 0 (π / r), 0 < τ θ)
    (hzpos : ∀ θ ∈ Ioo 0 (π / r), 0 < z θ)
    (hsupply : ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply Q (laurentWeight Q r N) r z τ hcol κ₀ κ₁ M) :
    ∃ (C₀ C₁ : ℝ) (C m0 : ℕ), 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (C : ℝ) ≤ C₀ + C₁ * ((laurentWeight Q r N).natDegree : ℝ) + 1 ∧
      ∀ m, m0 ≤ m →
        (coeffPoly m ≠ 0 →
          (exceptionalRoots (coeffPoly m) (ftWindow z 0 (π / r))).card ≤ C) ∧
        ∃ Z : Finset ℂ, (coeffPoly m).natDegree - C ≤ Z.card ∧
          (∀ w ∈ Z, (coeffPoly m).IsRoot w) ∧ (∀ w ∈ Z, w ∈ ftWindow z 0 (π / r)) := by
  obtain ⟨C₀, C₁, H, hC₀, hC₁, hc, hs, hCb⟩ :=
    exists_ftInputs_of_supply hr hQ0 hN hproper coeffPoly hP hzmono hzcont hτ hzpos
      hsupply
  obtain ⟨m1, h1⟩ := main_bound_interval H
  obtain ⟨m2, h2⟩ := interior_distinct_count H
  rw [hc, hs] at h1
  rw [hc, hs] at h2
  exact ⟨C₀, C₁, H.Cbulk, max m1 m2, hC₀, hC₁, hCb, fun m hm =>
    ⟨h1 m (le_trans (le_max_left _ _) hm), h2 m (le_trans (le_max_right _ _) hm)⟩⟩

/-- **`thm:main` clause 2(iii), off the discrepancy.**  For all large `m`, at
least `deg P_m - C` **distinct** zeros of `P_m` lie inside the angular window
`z((0,π/r))`, with `C ≤ C₀ + C₁deg B_N + 1` from `prop:angular-discrepancy`.

Unlike `Main.interior_distinct_count`, which returns the `Finset` its own
hypothesis handed it, the zero set here is a **conclusion**: no hypothesis names
it.  What is assumed is `FTPhaseSupply` — `thm:FT-geometry`,
`lem:amplitude-divisor` and `thm:weighted-dominance` — and the zeros are the
ones `AngularWindow.exists_windowZeros` produces from the phase count on
`(0,π/r)`.  That is the containment check `Main.interior_distinct_count` fails,
passed on the same route `MainClauses.interior_distinct_count_of_dominance`
takes from the dominance side.

Contained in `main_bound_interval_of_supply`, which states it alongside clause
2's multiplicity bound; it is stated alone because the paper states 2(iii)
alone. -/
theorem interior_distinct_count_of_supply {Q : ℂ[X]} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) {N : (ℂ[X])[X]} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    (coeffPoly : ℕ → ℂ[X])
    (hP : ∀ m, denomConv (ftDenom Q r) coeffPoly m = (swapVars N).coeff m)
    {z τ : ℝ → ℝ}
    (hzmono : StrictMonoOn z (Ioo 0 (π / r))) (hzcont : ContinuousOn z (Ioo 0 (π / r)))
    (hτ : ∀ θ ∈ Ioo 0 (π / r), 0 < τ θ)
    (hzpos : ∀ θ ∈ Ioo 0 (π / r), 0 < z θ)
    (hsupply : ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply Q (laurentWeight Q r N) r z τ hcol κ₀ κ₁ M) :
    ∃ (C₀ C₁ : ℝ) (C m0 : ℕ), 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (C : ℝ) ≤ C₀ + C₁ * ((laurentWeight Q r N).natDegree : ℝ) + 1 ∧
      ∀ m, m0 ≤ m → ∃ Z : Finset ℂ, (coeffPoly m).natDegree - C ≤ Z.card ∧
        (∀ w ∈ Z, (coeffPoly m).IsRoot w) ∧ (∀ w ∈ Z, w ∈ ftWindow z 0 (π / r)) := by
  obtain ⟨C₀, C₁, H, hC₀, hC₁, hc, hs, hCb⟩ :=
    exists_ftInputs_of_supply hr hQ0 hN hproper coeffPoly hP hzmono hzcont hτ hzpos
      hsupply
  obtain ⟨m0, hm0⟩ := interior_distinct_count H
  rw [hc, hs] at hm0
  exact ⟨C₀, C₁, H.Cbulk, m0, hC₀, hC₁, hCb, hm0⟩

end ForgacsTran
