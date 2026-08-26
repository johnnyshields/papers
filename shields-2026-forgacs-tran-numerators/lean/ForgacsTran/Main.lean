/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.Bridge
import ForgacsTran.EventualDegree

/-!
# The Fixed-numerator Forgács–Tran theorem

  `main_bound`          — a single constant `C` bounds the zeros of every nonzero
                          `P_m` off the positive ray `(0,∞)`.
  `main_bound_interval` — for all large `m`, `P_m` has at most `C = Cbulk` zeros
                          outside the Forgács–Tran interval `I_{Q,r}`.
  `main_bound_ofRecurrence`
                        — the same off-ray bound from leaner inputs: the `sec:reduction`
                          recurrence plus the phase count, with the degree bound
                          derived rather than assumed.

Both take the analytic inputs as an explicit `(H : FTInputs)` hypothesis, so the
proofs are unconditional given `H`: `#print axioms` on either reports only Lean's
standard three.  For large `m` the phase-count supply (`H.bulk_zero_count`) plus
the engine give the bound `H.Cbulk`; the finitely many smaller indices are
absorbed by the maximum degree over `range m0`.

## Implementation notes

Sorry-free.

## References

Assembles `../shields-2026-forgacs-tran-numerators.tex`, «Main theorem»
(`subsec:intro-main`, `thm:main`) and «Angular discrepancy and proof of the
main theorem» (`subsec:proof`).  The
exceptional-zero counting engine of `ZeroCount` consumes the analytic supply of
interior zeros bundled in `Bridge` as `FTInputs`:

## Tags

exceptional zero, fixed numerator, main theorem, positive ray
-/

open Polynomial

namespace ForgacsTran

open scoped Classical in
/-- **`thm:main`.**  For any analytic input bundle `H`, there is a constant `C`
such that every nonzero coefficient polynomial `P_m` has at most `C` zeros off
the positive ray `(0,∞)`, counted with multiplicity. -/
theorem main_bound (H : FTInputs) :
    ∃ C : ℕ, ∀ m, H.coeffPoly m ≠ 0 →
      (exceptionalRoots (H.coeffPoly m) posRay).card ≤ C := by
  obtain ⟨m0, hm0⟩ := H.bulk_zero_count
  refine ⟨max H.Cbulk ((Finset.range m0).sup (fun k => (H.coeffPoly k).natDegree)),
    fun m hm => ?_⟩
  by_cases hge : m0 ≤ m
  · -- Large `m`: the engine with the phase-count supply gives `Cbulk`.
    have hbound : (exceptionalRoots (H.coeffPoly m) posRay).card ≤ H.Cbulk := by
      refine exceptionalRoots_card_le hm (fun x hx => H.interiorZeros_root m x hx)
        (fun x hx => ?_) (hm0 m hge)
      exact H.ftSet_subset (H.interiorZeros_mem m x hx)
    exact le_trans hbound (le_max_left _ _)
  · -- Small `m`: at most `deg P_m ≤ sup` exceptional zeros.
    have hlt : m < m0 := not_le.mp hge
    have h1 : (exceptionalRoots (H.coeffPoly m) posRay).card ≤ (H.coeffPoly m).roots.card :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    have h2 : (H.coeffPoly m).roots.card ≤ (H.coeffPoly m).natDegree :=
      (H.coeffPoly m).card_roots'
    have h3 : (H.coeffPoly m).natDegree
        ≤ (Finset.range m0).sup (fun k => (H.coeffPoly k).natDegree) :=
      Finset.le_sup (f := fun k => (H.coeffPoly k).natDegree) (Finset.mem_range.mpr hlt)
    calc (exceptionalRoots (H.coeffPoly m) posRay).card
        ≤ (H.coeffPoly m).natDegree := le_trans h1 h2
      _ ≤ (Finset.range m0).sup (fun k => (H.coeffPoly k).natDegree) := h3
      _ ≤ max H.Cbulk ((Finset.range m0).sup (fun k => (H.coeffPoly k).natDegree)) :=
        le_max_right _ _

/-- **`thm:main` from the leaner inputs.**  The off-ray bound holds already under
the `sec:reduction` recurrence plus the `sec:dominance` phase count: the degree bound `deg P_m ≤
⌊m/r⌋` is
not assumed but derived (via `FTInputs.ofRecurrence`).  A single constant `C` bounds
the zeros of every nonzero `P_m` off the positive ray. -/
theorem main_bound_ofRecurrence
    (coeffPoly : ℕ → ℂ[X]) {ftSet : Set ℂ} (ftSet_subset : ftSet ⊆ posRay)
    (interiorZeros : ℕ → Finset ℂ) (Cbulk : ℕ)
    (interiorZeros_root : ∀ m, ∀ z ∈ interiorZeros m, (coeffPoly m).IsRoot z)
    (interiorZeros_mem : ∀ m, ∀ z ∈ interiorZeros m, z ∈ ftSet)
    (Q : ℂ[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) (b : ℕ → ℂ)
    (hrec : ∀ M, denomConv (ftDenom Q r) coeffPoly M = C (b M))
    (phase_count : ∃ m0 : ℕ, ∀ m, m0 ≤ m → m / r - Cbulk ≤ (interiorZeros m).card) :
    ∃ C : ℕ, ∀ m, coeffPoly m ≠ 0 →
      (exceptionalRoots (coeffPoly m) posRay).card ≤ C :=
  main_bound (FTInputs.ofRecurrence coeffPoly ftSet ftSet_subset interiorZeros Cbulk
    interiorZeros_root interiorZeros_mem Q r hr hQ0 b hrec phase_count)

/-- **`thm:main`, sharper interval form.**  For any analytic input bundle `H` and
all sufficiently large `m`, the coefficient polynomial `P_m` has at most `H.Cbulk`
zeros outside the Forgács–Tran interval `I_{Q,r}`, counted with multiplicity. -/
theorem main_bound_interval (H : FTInputs) :
    ∃ m0 : ℕ, ∀ m, m0 ≤ m → H.coeffPoly m ≠ 0 →
      (exceptionalRoots (H.coeffPoly m) H.ftSet).card ≤ H.Cbulk := by
  obtain ⟨m0, hm0⟩ := H.bulk_zero_count
  refine ⟨m0, fun m hge hm => ?_⟩
  exact exceptionalRoots_card_le hm (fun x hx => H.interiorZeros_root m x hx)
    (fun x hx => H.interiorZeros_mem m x hx) (hm0 m hge)

/-- **`thm:main` from the paper's own data.**  The off-ray bound, stated over a
general bivariate numerator `N` rather than over the reduced sequence: the
canonical Laurent reduction connects the two, so the degree bound crosses the
index shift `eq:exact-eventual-degree-shift` and only the phase count is assumed.

This is the algebraically leanest form the development reaches.  What separates
it from `main_bound_ofRecurrence` is that there `coeffPoly` satisfies the
recurrence of the *reduced* sequence and is thereby identified with it; here `N`
is an arbitrary proper bivariate numerator and `lem:laurent-reduction` does the
work. -/
theorem main_bound_ofBivariateNumerator
    (coeffPoly reduced : ℕ → ℂ[X]) {ftSet : Set ℂ} (ftSet_subset : ftSet ⊆ posRay)
    (interiorZeros : ℕ → Finset ℂ) (Cbulk : ℕ)
    (interiorZeros_root : ∀ m, ∀ z ∈ interiorZeros m, (coeffPoly m).IsRoot z)
    (interiorZeros_mem : ∀ m, ∀ z ∈ interiorZeros m, z ∈ ftSet)
    (Q : ℂ[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0)
    (N : (ℂ[X])[X]) (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom Q r) coeffPoly m = (swapVars N).coeff m)
    (hF : ∀ M, denomConv (ftDenom Q r) reduced M
      = Polynomial.C ((laurentWeight Q r N).coeff M))
    (phase_count : ∃ m0 : ℕ, ∀ m, m0 ≤ m →
      (((m : ℤ) - laurentShift Q r N).toNat) / r - Cbulk ≤ (interiorZeros m).card) :
    ∃ C : ℕ, ∀ m, coeffPoly m ≠ 0 →
      (exceptionalRoots (coeffPoly m) posRay).card ≤ C :=
  main_bound (FTInputs.ofBivariateNumerator coeffPoly reduced ftSet ftSet_subset
    interiorZeros Cbulk interiorZeros_root interiorZeros_mem Q r hr hQ0 N hN hproper
    hP hF phase_count)

/-- **`thm:main` clause 2, with the nonvanishing discharged.**  The interval
bound of `main_bound_interval` carries the hypothesis `P_m ≠ 0`, which is
clause 2's part (i).  Under the `sec:reduction` recurrence that part is not a
hypothesis at all: `eventual_ne_zero` derives it from the same top coefficient
that gives the attainment half of `lem:eventual-degree`, so for all large `m` the
conclusion holds outright.

This is the sharpest form of clause 2 the development reaches: parts (i) and
(ii) are both derived, and what remains assumed is the phase count alone. -/
theorem main_bound_interval_ofRecurrence
    (coeffPoly : ℕ → ℂ[X]) {ftSet : Set ℂ} (ftSet_subset : ftSet ⊆ posRay)
    (interiorZeros : ℕ → Finset ℂ) (Cbulk : ℕ)
    (interiorZeros_root : ∀ m, ∀ z ∈ interiorZeros m, (coeffPoly m).IsRoot z)
    (interiorZeros_mem : ∀ m, ∀ z ∈ interiorZeros m, z ∈ ftSet)
    (Q : ℂ[X]) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) (hQ1 : Q.coeff 1 ≠ 0)
    (b : ℕ → ℂ) (hb0 : b 0 ≠ 0)
    (hrec : ∀ M, denomConv (ftDenom Q r) coeffPoly M = C (b M))
    (phase_count : ∃ m0 : ℕ, ∀ m, m0 ≤ m → m / r - Cbulk ≤ (interiorZeros m).card) :
    ∃ m0 : ℕ, ∀ m, m0 ≤ m →
      (exceptionalRoots (coeffPoly m) ftSet).card ≤ Cbulk := by
  obtain ⟨m1, h1⟩ := main_bound_interval (FTInputs.ofRecurrence coeffPoly ftSet
    ftSet_subset interiorZeros Cbulk interiorZeros_root interiorZeros_mem Q r hr hQ0 b
    hrec phase_count)
  obtain ⟨m2, h2⟩ := eventual_ne_zero Q hr hQ0 hQ1 b hb0 coeffPoly hrec
  exact ⟨max m1 m2, fun m hm =>
    h1 m (le_trans (le_max_left _ _) hm) (h2 m (le_trans (le_max_right _ _) hm))⟩

/-- **`thm:main` clause 2, distinct-zero form.**  For all large `m` there are at
least `deg P_m - Cbulk` **distinct** zeros of `P_m` inside `I_{Q,r}` — the count the
paper's abstract and `prop:angular-discrepancy` state ("counting distinct zeros"), as opposed
to the multiplicity-counted complement bounded by `main_bound_interval`.

**Honest scope.**  This does not derive the distinct-zero content: it *restates* an
existing hypothesis.  `FTInputs.interiorZeros m` is a `Finset ℂ`, hence already a
set of pairwise-distinct points, and `bulk_zero_count` already asserts the
cardinality bound.  The corollary exists so that the Lean statement mirrors the
shape of the paper's claim; the analytic content that produces those zeros remains
assumed in `FTInputs`, exactly as for the other two theorems. -/
theorem interior_distinct_count (H : FTInputs) :
    ∃ m0 : ℕ, ∀ m, m0 ≤ m → ∃ Z : Finset ℂ,
      (H.coeffPoly m).natDegree - H.Cbulk ≤ Z.card ∧
      (∀ z ∈ Z, (H.coeffPoly m).IsRoot z) ∧ (∀ z ∈ Z, z ∈ H.ftSet) := by
  obtain ⟨m0, hm0⟩ := H.bulk_zero_count
  exact ⟨m0, fun m hge => ⟨H.interiorZeros m, hm0 m hge,
    H.interiorZeros_root m, H.interiorZeros_mem m⟩⟩

/-- **`thm:main` clause 2, distinct-zero form, derived from the sign pattern.**
The same conclusion as `interior_distinct_count`, but off the hypothesis set
`thm:weighted-dominance` actually delivers: a strictly increasing family of
`gaps m + 1` points of `I_{Q,r}` at which the real coefficient polynomial
alternates in sign.  The zeros are produced from that alternation by
`SignAlternation.exists_interiorZeros_of_alternating`, so the `Finset` in the
conclusion is constructed rather than assumed, and no hypothesis names the zero
set at all — the containment check that `interior_distinct_count` fails.

`hcount` bounds `deg P_m - C` by the number of *gaps*, which is a statement about
the supplied points; it is the intermediate-value argument that turns one gap
into one zero. -/
theorem interior_distinct_count_ofSignAlternation
    (Preal : ℕ → Polynomial ℝ) (a b : ℝ) (ha : 0 ≤ a) (Cbulk : ℕ)
    (gaps : ℕ → ℕ) (x : ∀ m, Fin (gaps m + 1) → ℝ)
    (hx : ∀ m, StrictMono (x m)) (hmem : ∀ m k, x m k ∈ Set.Ioo a b)
    (halt : ∀ m, ∀ k : Fin (gaps m),
      (Preal m).eval (x m k.castSucc) * (Preal m).eval (x m k.succ) < 0)
    (hcount : ∃ m0 : ℕ, ∀ m, m0 ≤ m →
      ((Preal m).map (algebraMap ℝ ℂ)).natDegree - Cbulk ≤ gaps m) :
    ∃ m0 : ℕ, ∀ m, m0 ≤ m → ∃ Z : Finset ℂ,
      ((Preal m).map (algebraMap ℝ ℂ)).natDegree - Cbulk ≤ Z.card ∧
      (∀ z ∈ Z, ((Preal m).map (algebraMap ℝ ℂ)).IsRoot z) ∧
      (∀ z ∈ Z, z ∈ ftInterval a b) :=
  interior_distinct_count
    (FTInputs.ofSignAlternation Preal a b ha Cbulk gaps x hx hmem halt hcount)

end ForgacsTran
