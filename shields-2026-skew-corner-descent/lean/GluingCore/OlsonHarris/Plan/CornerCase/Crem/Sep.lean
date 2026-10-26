-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/Crem/Sep.lean
import GluingCore.CellSchurTableau
import GluingCore.Local

/-!
# Diagrams on separated diagonals

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the product formula for `s` over diagrams that lie on
diagonals at distance at least `2` from one another (edge-disjoint pieces of thesis Lemma 5.5.8,
`OlsonHarris2024HopfApplications`).

* `Sep A B`: the contents of cells of `A` and of `B` differ by at least `2`;
* `cellSchur_union_of_sep`, `cellSchur_biUnion_sep`: `s` is multiplicative over such unions;
* `exists_block`: every cell is `ω.cell (J q + a) r` with `0 ≤ a < q`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

namespace Rem

open MarkedInner

attribute [local instance 10] Classical.propDecidable

/-- The cells of `A` and `B` lie on diagonals at distance at least `2`. -/
def Sep (A B : Diagram) : Prop := ∀ x ∈ A, ∀ y ∈ B, 2 ≤ |content x - content y|

theorem Sep.symm {A B : Diagram} (h : Sep A B) : Sep B A := by
  intro x hx y hy
  have := h y hy x hx
  rwa [abs_sub_comm] at this

theorem Sep.disjoint {A B : Diagram} (h : Sep A B) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro x hx hxB
  have := h x hx x hxB
  simp at this

theorem Sep.not_adj {A B : Diagram} (h : Sep A B) : ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b := by
  intro a ha b hb hadj
  have := h a ha b hb
  rcases content_adj hadj with h1 | h1
  · rw [abs_of_nonpos (by omega)] at this
    omega
  · rw [abs_of_nonneg (by omega)] at this
    omega

theorem Sep.mono_left {A A' B : Diagram} (h : Sep A B) (hA : A' ⊆ A) : Sep A' B :=
  fun x hx y hy => h x (hA hx) y hy

theorem Sep.union_left {A B C : Diagram} (hA : Sep A C) (hB : Sep B C) : Sep (A ∪ B) C := by
  intro x hx y hy
  rcases Finset.mem_union.mp hx with h | h
  · exact hA x h y hy
  · exact hB x h y hy

theorem cellSchur_union_of_sep {A B : Diagram} (h : Sep A B) :
    cellSchur (A ∪ B) = cellSchur A * cellSchur B :=
  cellSchur_union h.disjoint h.not_adj

theorem sep_biUnion_right {ι : Type*} {s : Finset ι} {f : ι → Diagram} {A : Diagram}
    (h : ∀ i ∈ s, Sep A (f i)) : Sep A (s.biUnion f) := by
  intro x hx y hy
  obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hy
  exact h i hi x hx y hyi

theorem sep_biUnion_biUnion {ι κ : Type*} {s : Finset ι} {t : Finset κ} {f : ι → Diagram}
    {g : κ → Diagram} (h : ∀ i ∈ s, ∀ j ∈ t, Sep (f i) (g j)) :
    Sep (s.biUnion f) (t.biUnion g) := by
  intro x hx y hy
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
  exact sep_biUnion_right (fun j hj => (h i hi j hj)) x hxi y hy

theorem cellSchur_biUnion_sep {ι : Type*} (s : Finset ι) (f : ι → Diagram)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Sep (f i) (f j)) :
    cellSchur (s.biUnion f) = ∏ i ∈ s, cellSchur (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert ha,
      cellSchur_union_of_sep (sep_biUnion_right fun i hi =>
        h a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun e => ha (e ▸ hi))),
      ih fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
        hij]

theorem exists_block (ω : MarkedInner) (hq : 0 < ω.period) (x : ℤ × ℤ) :
    ∃ J a r : ℤ, 0 ≤ a ∧ a < ω.period ∧ x = ω.cell (J * ω.period + a) r := by
  obtain ⟨a', r, rfl⟩ := ω.exists_cell x
  refine ⟨a' / ω.period, a' % ω.period, r, Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq, ?_⟩
  have : a' / ω.period * ω.period + a' % ω.period = a' := by
    have := Int.mul_ediv_add_emod a' ω.period
    linarith
  rw [this]

end Rem

end Corner

end Plan

end GluingCore
