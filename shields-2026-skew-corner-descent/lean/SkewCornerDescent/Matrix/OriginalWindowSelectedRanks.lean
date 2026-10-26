/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalWindowSelectedEquiv
import SkewCornerDescent.FiniteWindowOrder

/-!
# Exact original ranks in literal end windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
Selected whole components have one common span. Complete end windows are initial and
final segments in the actual source enumeration, so their ordered matching has the exact
rank shift given by the complementary occurrence count. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Selected occurrences have the same actual geometric width, including span ties. -/
theorem originalSelected_maxContent {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    maxContent (interiorBlockCells P b.val.val) =
      minContent (interiorBlockCells P b.val.val) + (span D : ℤ) - 1 := by
  have hb := originalBlockSelected_nonempty P b.val b.property
  have hc := interiorBlockCells_connected P b.val.val hb
  have he := (dvd_originalBlock_iff (hD := hD) P b.val.val hb).mp b.property
  have hs := congrArg polynomialSpan he
  rw [polynomialSpan_cellSchur hD, polynomialSpan_cellSchur hc] at hs
  have hw := span_eq_of_isConnectedSkew hc
  rw [← hs] at hw
  omega

/-- Right endpoints, as well as left endpoints, strictly follow the actual source order. -/
theorem originalSelected_maxContent_strictAnti {n : ℕ} (P : Profile n) :
    StrictAnti (fun b : OriginalSelectedBlocks (hD := hD) P =>
      maxContent (interiorBlockCells P b.val.val)) := by
  intro b a hba
  have h := originalSelected_minContent_strictAnti P hba
  change maxContent (interiorBlockCells P a.val.val) <
    maxContent (interiorBlockCells P b.val.val)
  change minContent (interiorBlockCells P a.val.val) <
    minContent (interiorBlockCells P b.val.val) at h
  rw [originalSelected_maxContent P b, originalSelected_maxContent P a]
  omega

/-- All original selected cells lie in the complete normalized source content band. -/
theorem originalSelected_content_bounds {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) {x : ℤ × ℤ}
    (hx : x ∈ interiorBlockCells P b.val.val) : 0 ≤ content x ∧ content x < P.xi 0 := by
  have hb := originalBlockSelected_nonempty P b.val b.property
  have hI := component_subset (interiorBlockCells_mem_components P b.val.val hb) hx
  have hX : x ∈ P.cells := (Finset.mem_filter.mp hI).1
  have hlo := minContent_le (content_mem_contents hX)
  have hhi := le_maxContent (content_mem_contents hX)
  rw [Profile.minContent_cells] at hlo
  rw [Profile.maxContent_cells] at hhi
  omega

/-- A complete lower-content end window is a final segment of selected occurrences. -/
theorem originalWindow_prefix_upper {n : ℕ} (P : Profile n) (q : ℤ)
    (b a : OriginalSelectedBlocks (hD := hD) P) (hba : b ≤ a)
    (hb : ∀ x ∈ interiorBlockCells P b.val.val, 0 ≤ content x ∧ content x < P.xi 0 - q) :
    ∀ x ∈ interiorBlockCells P a.val.val, 0 ≤ content x ∧ content x < P.xi 0 - q := by
  have hm := (originalSelected_maxContent_strictAnti P).antitone hba
  have hc := interiorBlockCells_connected P b.val.val
    (originalBlockSelected_nonempty P b.val b.property)
  obtain ⟨y, hy, hcy⟩ := Finset.mem_image.mp (maxContent_mem hc.2.1)
  have hbound := (hb y hy).2
  rw [hcy] at hbound
  intro x hx
  exact ⟨(originalSelected_content_bounds P a hx).1,
    lt_of_le_of_lt ((le_maxContent (content_mem_contents hx)).trans hm) hbound⟩

/-- A complete upper-content end window is an initial segment of selected occurrences. -/
theorem originalWindow_suffix_lower {n : ℕ} (P : Profile n) (q : ℤ)
    (b a : OriginalSelectedBlocks (hD := hD) P) (hba : b ≤ a)
    (ha : ∀ x ∈ interiorBlockCells P a.val.val, q ≤ content x ∧ content x < P.xi 0) :
    ∀ x ∈ interiorBlockCells P b.val.val, q ≤ content x ∧ content x < P.xi 0 := by
  have hm := (originalSelected_minContent_strictAnti P).antitone hba
  have hc := interiorBlockCells_connected P a.val.val
    (originalBlockSelected_nonempty P a.val a.property)
  obtain ⟨y, hy, hcy⟩ := Finset.mem_image.mp (minContent_mem hc.2.1)
  have hbound := (ha y hy).1
  rw [hcy] at hbound
  intro x hx
  exact ⟨hbound.trans (hm.trans (minContent_le (content_mem_contents hx))),
    (originalSelected_content_bounds P b hx).2⟩

/-- Restrict the actual source enumeration to all whole occurrences in a window. -/
noncomputable def originalWindowEnumeration {n : ℕ} (P : Profile n) (lo hi : ℤ) :
    {i : Fin (originalSelectedCount (hD := hD) P) //
      ∀ x ∈ interiorBlockCells P
        (originalSelectedEnumeration (hD := hD) P i).val.val,
        lo ≤ content x ∧ content x < hi} ≃o OriginalWindowSelected (hD := hD) P lo hi := by
  let E := originalSelectedEnumeration (hD := hD) P
  exact
    { toFun := fun i => ⟨E i.val, i.property⟩
      invFun := fun a => ⟨E.symm a.val, by
        change ∀ x ∈ interiorBlockCells P (E (E.symm a.val)).val.val, _
        rw [E.apply_symm_apply]
        exact a.property⟩
      left_inv := by
        intro i
        apply Subtype.ext
        exact E.symm_apply_apply i.val
      right_inv := by
        intro a
        apply Subtype.ext
        exact E.apply_symm_apply a.val
      map_rel_iff' := by
        intro i j
        exact E.le_iff_le (x := i.val) (y := j.val) }

/-- Membership in the lower-content end window is exactly membership in the final
source-rank segment. No occurrence can be omitted from the window count. -/
theorem originalWindow_prefix_iff_rank {n : ℕ} (P : Profile n) (q : ℤ)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    (∀ x ∈ interiorBlockCells P (originalSelectedEnumeration (hD := hD) P i).val.val,
      0 ≤ content x ∧ content x < P.xi 0 - q) ↔
      originalSelectedCount (hD := hD) P -
        Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) ≤ i.val := by
  classical
  let E := originalSelectedEnumeration (hD := hD) P
  let p : Fin (originalSelectedCount (hD := hD) P) → Prop := fun j =>
    ∀ x ∈ interiorBlockCells P (E j).val.val, 0 ≤ content x ∧ content x < P.xi 0 - q
  have hup : ∀ i j, i ≤ j → p i → p j := by
    intro i j hij hi
    exact originalWindow_prefix_upper P q (E i) (E j) (E.monotone hij) hi
  have hr := fin_upper_window_ranks p hup i
  have hcard := Fintype.card_congr
    (originalWindowEnumeration (hD := hD) P 0 (P.xi 0 - q)).toEquiv
  rw [Fintype.card_subtype] at hcard
  rw [hcard] at hr
  exact hr

/-- The complete occurrence order forces the exact original rank shift. This helper takes
an already constructed order isomorphism; literal windows construct it in
`originalWindow_selected_orderIso`. -/
theorem originalWindow_selected_rank_shift {n : ℕ} (P : Profile n) (q : ℤ)
    (e : OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q) ≃o
      OriginalWindowSelected (hD := hD) P q (P.xi 0))
    (b : OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) :
    ((originalSelectedEnumeration (hD := hD) P).symm (e b).val).val +
        (originalSelectedCount (hD := hD) P -
          Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q))) =
      ((originalSelectedEnumeration (hD := hD) P).symm b.val).val := by
  classical
  let E := originalSelectedEnumeration (hD := hD) P
  let p : Fin (originalSelectedCount (hD := hD) P) → Prop := fun i =>
    ∀ x ∈ interiorBlockCells P (E i).val.val,
    0 ≤ content x ∧ content x < P.xi 0 - q
  let s : Fin (originalSelectedCount (hD := hD) P) → Prop := fun i =>
    ∀ x ∈ interiorBlockCells P (E i).val.val,
    q ≤ content x ∧ content x < P.xi 0
  let ep := originalWindowEnumeration (hD := hD) P 0 (P.xi 0 - q)
  let es := originalWindowEnumeration (hD := hD) P q (P.xi 0)
  have hup : ∀ i j, i ≤ j → p i → p j := by
    intro i j hij hi
    exact originalWindow_prefix_upper P q (E i) (E j) (E.monotone hij) hi
  have hdown : ∀ i j, i ≤ j → s j → s i := by
    intro i j hij hj
    exact originalWindow_suffix_lower P q (E i) (E j) (E.monotone hij) hj
  have hr := fin_end_windows_orderIso_rank p s hup hdown
    (ep.trans (e.trans es.symm)) (ep.symm b)
  have hcard := Fintype.card_congr ep.toEquiv
  rw [Fintype.card_subtype] at hcard
  rw [hcard] at hr
  dsimp only [OrderIso.trans_apply, ep, es, originalWindowEnumeration] at hr
  simp only [OrderIso.apply_symm_apply] at hr
  exact hr

end SkewCornerDescent.Matrix.SelectedCoordinate
