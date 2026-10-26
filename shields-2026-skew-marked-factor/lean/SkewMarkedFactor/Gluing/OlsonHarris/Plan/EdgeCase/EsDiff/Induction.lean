/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/EsDiff/Induction.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.EsDiff.Step

/-!
# Removing the key ribbons of a downset

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.4.3 and Lemma 5.4.6
(`OlsonHarris2024HopfApplications`), iterated over the cells of a downset in the northwest order.

The Schur function of the copies at `X` with the key ribbons of the cells of a downset `A`
removed is the Schur function of the copies at `X \ A` times a factor `s_W`, `s_{\overline W}`,
`s_{\overline O}` for each cell of `A` without a neighbor of `X` to the east, south, southeast
(`cellSchur_copies_sdiff_lift`).  The proof removes the cells of `A` one at a time, a cell of
`A` of least `i + j` having no cell of `X` to its northwest.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace EsDiff

open scoped Classical

open SkewMarkedFactor.Gluing.MarkedInner

variable {ω : MarkedInner} {X A : Diagram} {b : ℤ × ℤ}

theorem contentSep_mono {A A' B B' : Diagram} (h : Plan.MarkedInner.ContentSep A B)
    (hA : A' ⊆ A) (hB : B' ⊆ B) : Plan.MarkedInner.ContentSep A' B' :=
  fun x hx y hy => h x (hA hx) y (hB hy)

theorem contentSep_union_left {A A' B : Diagram} (h : Plan.MarkedInner.ContentSep A B)
    (h' : Plan.MarkedInner.ContentSep A' B) : Plan.MarkedInner.ContentSep (A ∪ A') B := by
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hx | hx
  · exact h x hx y hy
  · exact h' x hx y hy

theorem ite_empty_subset (p : Prop) [Decidable p] (P : Diagram) :
    (if p then (∅ : Diagram) else P) ⊆ P := by
  split_ifs
  · exact Finset.empty_subset _
  · exact subset_rfl

theorem cellSchur_ite_empty (p : Prop) [Decidable p] (P : Diagram) :
    cellSchur (if p then (∅ : Diagram) else P) = if p then 1 else cellSchur P := by
  split_ifs
  · exact cellSchur_empty
  · rfl

/-- **The Schur function of the pieces of the missing neighbors.** -/
theorem cellSchur_absent (hω : ω.IsLegal) (hc : ω.case = .a) :
    cellSchur (absentCells ω X b) =
      (if (b.1, b.2 + 1) ∈ X then 1 else cellSchur ω.W) *
        (if (b.1 + 1, b.2) ∈ X then 1 else cellSchur (hatMarkFin ω)) *
        (if (b.1 + 1, b.2 + 1) ∈ X then 1 else cellSchur (hatMiddleFin ω)) := by
  have hL := edgeLocal hω hc
  have cs1 : Plan.MarkedInner.ContentSep (pieceS ω) (pieceSE ω) := by
    intro x hx y hy
    have := hL.pieceS_content x hx
    have := hL.pieceSE_content y hy
    omega
  have cs2 : Plan.MarkedInner.ContentSep (pieceS ω ∪ pieceSE ω) (pieceE ω) := by
    refine contentSep_union_left ?_ ?_
    · intro x hx y hy
      have := hL.pieceS_content x hx
      have := hL.pieceE_content y hy
      have := hω.2.2.1.2
      omega
    · intro x hx y hy
      have := hL.pieceSE_content x hx
      have := hL.pieceE_content y hy
      omega
  have cs1' := contentSep_mono cs1 (ite_empty_subset ((b.1 + 1, b.2) ∈ X) _)
    (ite_empty_subset ((b.1 + 1, b.2 + 1) ∈ X) _)
  have cs2' := contentSep_mono cs2
    (Finset.union_subset_union (ite_empty_subset ((b.1 + 1, b.2) ∈ X) _)
      (ite_empty_subset ((b.1 + 1, b.2 + 1) ∈ X) _))
    (ite_empty_subset ((b.1, b.2 + 1) ∈ X) _)
  unfold absentCells
  rw [Plan.cellSchur_union cs2'.disjoint cs2'.nonAdjacent,
    Plan.cellSchur_union cs1'.disjoint cs1'.nonAdjacent, cellSchur_ite_empty, cellSchur_ite_empty,
    cellSchur_ite_empty]
  simp only [pieceS, pieceSE, pieceE, cellSchur_translate]
  ring

theorem isSkew_erase_min (hX : IsSkew X) (hmin : ∀ x ∈ X, x.1 ≤ b.1 → x.2 ≤ b.2 → x = b) :
    IsSkew (X.erase b) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨hxb, hxX⟩ := Finset.mem_erase.mp hx
  obtain ⟨hyb, hyX⟩ := Finset.mem_erase.mp hy
  simp only [Finset.mem_Icc] at hi hj
  refine Finset.mem_erase.mpr ⟨fun hij => hxb ?_, hX.mem hxX hyX h1 h2 hi.1 hi.2 hj.1 hj.2⟩
  apply hmin x hxX
  · rw [← hij]; exact hi.1
  · rw [← hij]; exact hj.1

theorem card_filter_step (hmin : ∀ x ∈ X, x.1 ≤ b.1 → x.2 ≤ b.2 → x = b) (hAX : A ⊆ X)
    (hbA : b ∈ A) (u : ℤ × ℤ) (hu1 : 0 ≤ u.1) (hu2 : 0 ≤ u.2) :
    (A.filter fun x => x + u ∉ X).card =
      ((A.erase b).filter fun x => x + u ∉ X.erase b).card + (if b + u ∈ X then 0 else 1) := by
  have hcongr : (A.erase b).filter (fun x => x + u ∉ X) =
      (A.erase b).filter (fun x => x + u ∉ X.erase b) := by
    refine Finset.filter_congr fun x hx => ?_
    obtain ⟨hxb, hxA⟩ := Finset.mem_erase.mp hx
    rw [Finset.mem_erase]
    constructor
    · intro h h'
      exact h h'.2
    · intro h h'
      refine h ⟨fun hxu => hxb ?_, h'⟩
      apply hmin x (hAX hxA)
      · rw [← hxu]; simp only [Prod.fst_add]; omega
      · rw [← hxu]; simp only [Prod.snd_add]; omega
  rw [← hcongr]
  have hins : A = insert b (A.erase b) := (Finset.insert_erase hbA).symm
  conv_lhs => rw [hins, Finset.filter_insert]
  by_cases hbu : b + u ∈ X
  · simp [hbu]
  · simp [hbu, Finset.card_insert_of_notMem]

theorem diff_eq_erase (hbA : b ∈ A) : X \ A = X.erase b \ A.erase b := by
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  by_cases hz : z = b
  · subst hz; simp [hbA]
  · simp [hz]

theorem mem_liftRibbon_org (hc : ω.case = .a) {z : ℤ × ℤ} :
    z ∈ liftRibbon ω X A ↔ ∃ b ∈ A, z ∈ translate (org ω b) (keyRibbon ω) := by
  rw [mem_liftRibbon]
  simp only [origin_eq hc]

theorem key_translate_subset (hL : EdgeLocal ω) (t : ℤ × ℤ) :
    translate t (keyRibbon ω) ⊆ translate t ω.E := by
  intro z hz
  rw [mem_translate] at hz ⊢
  exact hL.key_sub _ hz

theorem sdiff_union_eq {C L Eb Kb J : Diagram} (hJ : J = (Eb \ Kb) \ C) (hK : Disjoint Kb C)
    (hL : L ⊆ C) : (C ∪ Eb) \ (L ∪ Kb) = (C \ L) ∪ J := by
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_union, hJ]
  have h1 : z ∈ Kb → z ∈ C → False := fun a b => Finset.disjoint_left.mp hK a b
  have h2 : z ∈ L → z ∈ C := fun a => hL a
  by_cases a : z ∈ C <;> by_cases b : z ∈ Eb <;> by_cases c : z ∈ L <;> by_cases d : z ∈ Kb <;>
    simp_all

/-- **The key ribbons of a downset: the induction.** -/
theorem cellSchur_copies_sdiff_lift_aux (hω : ω.IsLegal) (hc : ω.case = .a) :
    ∀ n : ℕ, ∀ X A : Diagram, A.card = n → IsSkew X → IsDownsetIn X A →
      cellSchur (Plan.MarkedInner.copies ω X \ liftRibbon ω X A) =
        cellSchur (Plan.MarkedInner.copies ω (X \ A)) *
          cellSchur ω.W ^ (A.filter fun x => x + (0, 1) ∉ X).card *
          cellSchur (hatMarkFin ω) ^ (A.filter fun x => x + (1, 0) ∉ X).card *
          cellSchur (hatMiddleFin ω) ^ (A.filter fun x => x + eCell ∉ X).card := by
  have hL := edgeLocal hω hc
  intro n
  induction n with
  | zero =>
    intro X A hcard hX hA
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    have : liftRibbon ω X ∅ = ∅ := by unfold liftRibbon; simp
    simp [this]
  | succ n ih =>
    intro X A hcard hX hA
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b, hbA, hbmin⟩ := Finset.exists_min_image A (fun x => x.1 + x.2) hne
    have hbX : b ∈ X := hA.1 hbA
    have hmin : ∀ x ∈ X, x.1 ≤ b.1 → x.2 ≤ b.2 → x = b := by
      intro x hx h1 h2
      have hxA : x ∈ A := hA.2 x hx b hbA h1 h2
      have := hbmin x hxA
      exact Prod.ext (by omega) (by omega)
    have hX' : IsSkew (X.erase b) := isSkew_erase_min hX hmin
    have hA' : IsDownsetIn (X.erase b) (A.erase b) := by
      refine ⟨fun x hx => ?_, fun x hx y hy h1 h2 => ?_⟩
      · obtain ⟨hxb, hxA⟩ := Finset.mem_erase.mp hx
        exact Finset.mem_erase.mpr ⟨hxb, hA.1 hxA⟩
      · obtain ⟨hxb, hxX⟩ := Finset.mem_erase.mp hx
        obtain ⟨hyb, hyA⟩ := Finset.mem_erase.mp hy
        exact Finset.mem_erase.mpr ⟨hxb, hA.2 x hxX y hyA h1 h2⟩
    have hcard' : (A.erase b).card = n := by rw [Finset.card_erase_of_mem hbA]; omega
    have IH := ih (X.erase b) (A.erase b) hcard' hX' hA'
    -- the set equation
    have hlift : liftRibbon ω X A =
        liftRibbon ω (X.erase b) (A.erase b) ∪ translate (org ω b) (keyRibbon ω) := by
      ext z
      rw [Finset.mem_union, mem_liftRibbon_org hc, mem_liftRibbon_org hc]
      constructor
      · rintro ⟨b', hb', hz⟩
        by_cases hbb : b' = b
        · subst hbb; exact Or.inr hz
        · exact Or.inl ⟨b', Finset.mem_erase.mpr ⟨hbb, hb'⟩, hz⟩
      · rintro (⟨b', hb', hz⟩ | hz)
        · exact ⟨b', (Finset.mem_erase.mp hb').2, hz⟩
        · exact ⟨b, hbA, hz⟩
    have hLsub : liftRibbon ω (X.erase b) (A.erase b) ⊆
        Plan.MarkedInner.copies ω (X.erase b) := by
      intro z hz
      rw [mem_liftRibbon_org hc] at hz
      obtain ⟨b', hb', hz⟩ := hz
      rw [mem_copies_org hc]
      exact ⟨b', (hA'.1 hb'), key_translate_subset hL _ hz⟩
    have hset : Plan.MarkedInner.copies ω X \ liftRibbon ω X A =
        (Plan.MarkedInner.copies ω (X.erase b) \ liftRibbon ω (X.erase b) (A.erase b)) ∪
          translate (org ω b) (absentCells ω X b) := by
      rw [copies_insert hc hbX, hlift]
      exact sdiff_union_eq (step_sdiff hω hc hX hbX hmin).symm
        (step_key_disjoint hω hc hX hbX hmin) hLsub
    have hdisj : Disjoint (Plan.MarkedInner.copies ω (X.erase b) \
        liftRibbon ω (X.erase b) (A.erase b)) (translate (org ω b) (absentCells ω X b)) := by
      rw [← step_sdiff hω hc hX hbX hmin, Finset.disjoint_left]
      intro z hz hz'
      exact (Finset.mem_sdiff.mp hz').2 (Finset.mem_sdiff.mp hz).1
    have hnadj : NonAdjacent (Plan.MarkedInner.copies ω (X.erase b) \
        liftRibbon ω (X.erase b) (A.erase b)) (translate (org ω b) (absentCells ω X b)) :=
      ((step_nonAdjacent hω hc hX hbX hmin).symm).mono Finset.sdiff_subset subset_rfl
    have e1 : b + ((0 : ℤ), (1 : ℤ)) = (b.1, b.2 + 1) := Prod.ext (by simp) (by simp)
    have e2 : b + ((1 : ℤ), (0 : ℤ)) = (b.1 + 1, b.2) := Prod.ext (by simp) (by simp)
    have e3 : b + eCell = (b.1 + 1, b.2 + 1) := Prod.ext (by simp [eCell]) (by simp [eCell])
    have c1 := card_filter_step hmin hA.1 hbA (0, 1) (by simp) (by simp)
    have c2 := card_filter_step hmin hA.1 hbA (1, 0) (by simp) (by simp)
    have c3 := card_filter_step hmin hA.1 hbA eCell (by simp [eCell]) (by simp [eCell])
    rw [e1] at c1
    rw [e2] at c2
    rw [e3] at c3
    rw [hset, Plan.cellSchur_union hdisj hnadj, IH, cellSchur_translate, cellSchur_absent hω hc,
      diff_eq_erase hbA, c1, c2, c3]
    by_cases h1 : (b.1, b.2 + 1) ∈ X <;> by_cases h2 : (b.1 + 1, b.2) ∈ X <;>
      by_cases h3 : (b.1 + 1, b.2 + 1) ∈ X <;> simp [h1, h2, h3, pow_succ] <;> ring

/-- **Thesis Lemma 5.4.3, iterated** (`cellSchur_copies_sdiff_liftRibbon` of the plan): removing
the key ribbons of the cells of a downset `A` of a skew diagram `X` from the copies at `X` leaves
the copies at `X \ A`, with a copy of `W`, `\overline W`, `\overline O` for each cell of `A`
without a cell of `X` to the east, south, southeast. -/
theorem cellSchur_copies_sdiff_lift (hω : ω.IsLegal) (hc : ω.case = .a) (hX : IsSkew X)
    (hA : IsDownsetIn X A) :
    cellSchur (Plan.MarkedInner.copies ω X \ liftRibbon ω X A) =
      cellSchur (Plan.MarkedInner.copies ω (X \ A)) *
        cellSchur ω.W ^ (A.filter fun x => x + (0, 1) ∉ X).card *
        cellSchur (hatMarkFin ω) ^ (A.filter fun x => x + (1, 0) ∉ X).card *
        cellSchur (hatMiddleFin ω) ^ (A.filter fun x => x + eCell ∉ X).card :=
  cellSchur_copies_sdiff_lift_aux hω hc _ X A rfl hX hA

end EsDiff

end Plan

end SkewMarkedFactor.Gluing
