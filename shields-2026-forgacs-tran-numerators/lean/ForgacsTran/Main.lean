/-
# The Fixed-numerator Forgács–Tran theorem

Assembles `../shields-2026-forgacs-tran-numerators.tex`, §1 «Introduction»
(`thm:main`) and §5 «Proof of the fixed-numerator theorem» (`sec:proof`).  The
exceptional-zero counting engine of `ZeroCount` consumes the analytic supply of
interior zeros bundled in `Bridge` as `FTInputs`:

  `main_bound`          — a single constant `C` bounds the zeros of every nonzero
                          `P_m` off the positive ray `(0,∞)`.
  `main_bound_interval` — for all large `m`, `P_m` has at most `C = Cbulk` zeros
                          outside the Forgács–Tran interval `I_{Q,r}`.
  `main_bound_ofRecurrence`
                        — the same off-ray bound from leaner inputs: the §2
                          recurrence plus the phase count, with the degree bound
                          derived rather than assumed.

Both take the analytic inputs as an explicit `(H : FTInputs)` hypothesis, so the
proofs are unconditional given `H`: `#print axioms` on either reports only Lean's
standard three.  For large `m` the phase-count supply (`H.bulk_zero_count`) plus
the engine give the bound `H.Cbulk`; the finitely many smaller indices are
absorbed by the maximum degree over `range m0`.

Sorry-free.
-/
import ForgacsTran.Bridge

open Classical Polynomial

namespace ForgacsTran

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
the §2 recurrence plus the §4–§5 phase count: the degree bound `deg P_m ≤ ⌊m/r⌋` is
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

/-- **`thm:main` clause 2, distinct-zero form.**  For all large `m` there are at
least `deg P_m - Cbulk` **distinct** zeros of `P_m` inside `I_{Q,r}` — the count the
paper's abstract and `Corollary 6.2` state ("counting distinct zeros"), as opposed
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

end ForgacsTran
