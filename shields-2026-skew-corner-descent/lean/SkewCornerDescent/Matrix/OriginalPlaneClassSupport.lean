/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClassSupportTransport
import SkewCornerDescent.Matrix.OriginalWindowActiveClasses

/-!
# The actual rational plane support is the literal unbalanced class support

Supports `shields-2026-skew-corner-descent.tex` (`lem:dual-identities`). The
original residue classifier and complete window restriction produce membership,
coverage, and exact signed weights in both class presentations. Every finite
weighted function of the responses has the same sum in the unchanged field.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

noncomputable local instance planeClassSupportRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The finite rational plane support carries exactly the literal actual class
weights, including arbitrary signed multiplicities and both coincident true caps. -/
theorem originalWindow_plane_class_support {n k m : ℕ}
    (P : Profile n) (W : Profile k) (Q : Profile m) (q : ℤ) (v z w : ℤ × ℤ)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hmaxW : ∀ C ∈ edgeComponents (diagramInterior W.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a d : ℕ) (had : d + a = b)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin k => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    let S := c.regularResidue (c.originalHessenbergResponse Q middle middle)
    let F := c.originalTrueCapProduct P
    ∃ ε : ℤ, ∃ support : Finset ℚ, ∃ e : ℚ → ℤ,
      (ε = 1 ∨ ε = -1) ∧ (∀ α, α ∈ support ↔ e α ≠ 0) ∧
      (∑ α ∈ support, e α) = (d : ℤ) ∧
      (∀ α, e α = c.originalResponseValueExponent P W a b (S - (α : OtherField c.top) * F)) ∧
      c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
        (ε : OtherField c.top) * ∏ α ∈ support, (S / F - (α : OtherField c.top)) ^ e α ∧
      ∀ H : OtherField c.top → OtherField c.top,
        (∑ X : c.OriginalResponseClass P,
          (c.originalResponseClassExponent P W a b X : OtherField c.top) * H X.val) =
          ∑ α ∈ support, (e α : OtherField c.top) * H (S - (α : OtherField c.top) * F) := by
  classical
  have hdata := c.originalWindow_active_classes P W Q q v z w hwindow hW hQ hcutq hcutLq
    hC hmax hmaxW Λ b a d had hKU hKW p₀ p₁ hpq hdep
  obtain ⟨oldlabel, hlabels⟩ := hdata.1
  obtain ⟨ε, support, e, _, hε, _, hdegree, hsupport, hcounts, hfactor, _⟩ := hdata.2
  obtain ⟨hB, _⟩ := c.originalWindow_true_cap_product P W q v z hwindow hW hcutq hcutLq hC
  have hcQ := originalHorizontalClosure_profile_selected_count (hD := hD) P Q w hQ
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by omega⟩
  let S := c.regularResidue (c.originalHessenbergResponse Q middle middle)
  let F := c.originalTrueCapProduct P
  let value := fun α : ℚ => S - (α : OtherField c.top) * F
  have hF : F ≠ 0 := c.originalTrueCapProduct_ne_zero P hB hmax
  have hinj : Function.Injective value := by
    have heval (α : ℚ) : (S - value α) / F = (α : OtherField c.top) := by
      dsimp only [value]
      field_simp [hF]
      ring
    intro α β he
    have hc := congrArg (fun x => (S - x) / F) he
    rw [heval α, heval β] at hc
    exact_mod_cast hc
  have hflipP (x : OtherField c.top) :
      (Finset.univ.filter fun i => x = c.originalInternalResidue P i).card =
        (Finset.univ.filter fun i => c.originalInternalResidue P i = x).card := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact eq_comm
  have hflipW (x : OtherField c.top) :
      (Finset.univ.filter fun i => x = c.originalInternalResidue W i).card =
        (Finset.univ.filter fun i => c.originalInternalResidue W i = x).card := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact eq_comm
  have hweight : ∀ α, e α = c.originalResponseValueExponent P W a b (value α) := by
    intro α
    rw [hcounts α]
    change (a : ℤ) * (Finset.univ.filter fun i => value α = c.originalInternalResidue P i).card -
      (b : ℤ) * (Finset.univ.filter fun i => value α = c.originalInternalResidue W i).card = _
    rw [hflipP, hflipW]
    rfl
  have hPmem (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
      c.originalInternalResidue P i ∈ c.originalResponseClasses P := by
    exact (c.originalResponseClassOf P ⟨i.val + 1, by have := i.isLt; omega⟩).property
  have hupper : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate (v + z) W.cells := by rw [hwindow, ← hW, SkewGluing.translate_translate]
  have hWupper : W.cells = translate (-(v + z))
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0) := by
    rw [hupper, SkewGluing.translate_translate, neg_add_cancel, SkewGluing.translate_zero]
  obtain ⟨hCW, hw⟩ := c.originalWindow_restriction_internal_word P W q (-(v + z)) hWupper
    hcutq (originalProfile_interior_boundary_gaps P).2
  have hWmem (i : Fin (originalSelectedCount (hD := hD) W - 1)) :
      c.originalInternalResidue W i ∈ c.originalResponseClasses P := by
    have he := congrArg c.regularResidue (hw i)
    change c.originalInternalResidue W i = c.originalInternalResidue P
      ⟨i.val, by have := i.isLt; omega⟩ at he
    rw [he]
    exact hPmem _
  have hmem : ∀ α ∈ support, ∃ X : c.OriginalResponseClass P, X.val = value α := by
    intro α hα
    have hval : value α ∈ c.originalResponseClasses P := by
      by_contra hnot
      have hPempty : (Finset.univ.filter fun i => c.originalInternalResidue P i = value α) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hnot ((Finset.mem_filter.mp hi).2 ▸ hPmem i)
      have hWempty : (Finset.univ.filter fun i => c.originalInternalResidue W i = value α) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hnot ((Finset.mem_filter.mp hi).2 ▸ hWmem i)
      have hz : e α = 0 := by
        rw [hweight α]
        unfold originalResponseValueExponent
        rw [hPempty, hWempty]
        simp only [Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero]
      exact ((hsupport α).mp hα) hz
    exact ⟨⟨value α, hval⟩, rfl⟩
  have hcover : ∀ X : c.OriginalResponseClass P,
      c.originalResponseClassExponent P W a b X ≠ 0 → ∃ α ∈ support, X.val = value α := by
    intro X hX
    have hne : a * (Finset.univ.filter fun i => X.val = c.originalInternalResidue P i).card ≠
        b * (Finset.univ.filter fun i => X.val = c.originalInternalResidue W i).card := by
      intro he
      have heZ := congrArg (fun x : ℕ => (x : ℤ)) he
      simp only [Nat.cast_mul, hflipP, hflipW] at heZ
      exact hX (sub_eq_zero.mpr heZ)
    have hold := hlabels (c.originalResponseClassIndex P X)
      (by rw [c.originalResponseClassIndex_spec P X]; exact hne)
    have hx : X.val = value (oldlabel (c.originalResponseClassIndex P X)) := by
      have he := hold.2
      rw [c.originalResponseClassIndex_spec P X] at he
      exact he
    let α := oldlabel (c.originalResponseClassIndex P X)
    have he : e α = c.originalResponseClassExponent P W a b X := by
      rw [hweight α]
      change c.originalResponseValueExponent P W a b (value α) =
        c.originalResponseValueExponent P W a b X.val
      rw [← hx]
    refine ⟨α, (hsupport α).mpr (by rw [he]; exact hX), hx⟩
  dsimp only
  refine ⟨ε, support, e, hε, hsupport, hdegree, hweight, hfactor, ?_⟩
  intro H
  exact c.originalResponseClass_sum_support P W a b support e value hinj hsupport
    (fun α _ => hweight α) hmem hcover H

end SkewCornerDescent.Matrix.SelectedCoordinate
