/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowResidueDependence
import SkewCornerDescent.Matrix.ResidueActiveFamily
import SkewCornerDescent.Matrix.TrueCapExposureTops
import SkewCornerDescent.Matrix.OriginalClosureCentralResponse
import SkewCornerDescent.Matrix.ResidueUnitNormalization
import SkewCornerDescent.Matrix.ResidueClassExponents

/-!
# Active classes of the actual complete-window source

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`). The
original parent residue equation produces full rational labels for every unbalanced
source response. Actual elimination supplies all polynomial representatives, while
literal windows and the actual closure supply their normalizations. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

noncomputable local instance windowActiveRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

set_option maxHeartbeats 600000 in
-- The assembled original-window theorem compares two dependent finite response inventories.
/-- Every unbalanced full original source class has the actual closure top and a rational
label against the entire central response and true cap product. The original residue ratio
has a rational linear-factor expansion with signed degree `d` and scalar exactly a fixed
determinant sign. Only standing geometry, corner powers, and original residue dependence enter. -/
theorem originalWindow_active_classes {n k m : ℕ}
    (P : Profile n) (W : Profile k) (H : Profile m) (q : ℤ) (v z h : ℤ × ℤ)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hH : originalHorizontalClosure P = translate h H.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hQ : ∀ C ∈ edgeComponents (diagramInterior W.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a d : ℕ) (hd : d + a = b)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin k => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (p t : Polynomial ℚ) (hpt : IsCoprime p t)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) t) :
    let middle : Fin (originalSelectedCount (hD := hD) H + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P H h hH]; omega⟩
    (∃ label : Fin (originalSelectedCount (hD := hD) P + 1) → ℚ, ∀ j,
      a * (Finset.univ.filter fun i =>
          c.regularResidue (c.originalHessenbergResponse P j j) =
            c.originalInternalResidue P i).card ≠
        b * (Finset.univ.filter fun i =>
          c.regularResidue (c.originalHessenbergResponse P j j) =
            c.originalInternalResidue W i).card →
      originalHessenbergDistance (hD := hD) P j j =
          originalHessenbergDistance (hD := hD) H middle middle ∧
        c.regularResidue (c.originalHessenbergResponse P j j) =
          c.regularResidue (c.originalHessenbergResponse H middle middle) -
            (label j : OtherField c.top) * c.originalTrueCapProduct P) ∧
      ∃ ε : ℤ, ∃ s : Finset ℚ, ∃ e : ℚ → ℤ,
        Transcendental ℚ (c.regularResidue
          (c.originalHessenbergResponse H middle middle) / c.originalTrueCapProduct P) ∧
        (ε = 1 ∨ ε = -1) ∧ (∀ α ∈ s, e α ≠ 0) ∧ (∑ α ∈ s, e α) = d ∧
        (∀ α, α ∈ s ↔ e α ≠ 0) ∧
        (∀ α, e α =
          (a : ℤ) * (Finset.univ.filter fun i =>
            c.regularResidue (c.originalHessenbergResponse H middle middle) -
                (α : OtherField c.top) * c.originalTrueCapProduct P =
              c.originalInternalResidue P i).card -
          (b : ℤ) * (Finset.univ.filter fun i =>
            c.regularResidue (c.originalHessenbergResponse H middle middle) -
                (α : OtherField c.top) * c.originalTrueCapProduct P =
              c.originalInternalResidue W i).card) ∧
        c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
          (ε : OtherField c.top) * ∏ α ∈ s,
            (c.regularResidue (c.originalHessenbergResponse H middle middle) /
              c.originalTrueCapProduct P - (α : OtherField c.top)) ^ e α ∧
        ∃ labelW : Fin (originalSelectedCount (hD := hD) W - 1) → ℚ, ∀ j,
          a * (Finset.univ.filter fun i =>
              c.originalInternalResidue W j = c.originalInternalResidue P i).card ≠
            b * (Finset.univ.filter fun i =>
              c.originalInternalResidue W j = c.originalInternalResidue W i).card →
          c.originalInternalResidue W j =
            c.regularResidue (c.originalHessenbergResponse H middle middle) -
              (labelW j : OtherField c.top) * c.originalTrueCapProduct P := by
  classical
  dsimp only
  obtain ⟨hB, _⟩ := c.originalWindow_true_cap_product P W q v z hwindow hW hcutq hcutLq hC
  have hBH : 0 < originalSelectedCount (hD := hD) H := by
    rw [originalHorizontalClosure_profile_selected_count P H h hH]
    omega
  let middle : Fin (originalSelectedCount (hD := hD) H + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by
      rw [originalHorizontalClosure_profile_selected_count P H h hH]; omega⟩
  obtain ⟨JP, BP, hfP⟩ := c.originalHessenberg_polynomial_family P hB hP
  obtain ⟨JW, BW, hfW⟩ := c.originalInternal_polynomial_family W hC hQ
  obtain ⟨JH, BH, hfH⟩ := c.originalHessenberg_polynomial_family H hBH
    (c.originalHorizontalClosure_profile_component_span P H h hH hP)
  let J := fun i : Fin (originalSelectedCount (hD := hD) P - 1) => JP ⟨i.val + 1, by omega⟩
  let B := fun i : Fin (originalSelectedCount (hD := hD) P - 1) => BP ⟨i.val + 1, by omega⟩
  have hf (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
      residueHigherEval c.top (X (J i) + B i) = c.originalInternalResidue P i :=
    (hfP ⟨i.val + 1, by omega⟩).2.1
  have hcentral := c.originalHorizontalClosure_central_distance P H h hH hB
  dsimp only at hcentral
  change originalHessenbergDistance (hD := hD) H middle middle = _ at hcentral
  rw [c.originalCompletedGap_last_eq_splice P hB,
    c.originalCapSpliceDistance_cap_sum] at hcentral
  have ht0 : JP 0 < JH middle := by
    have hp := (hfP 0).2.2
    have hh := (hfH middle).2.2
    rw [originalHessenbergDistance_first P hB] at hp
    have he := c.originalTrueCaps_below_closure P
      (originalSelectedEnumeration P ⟨0, hB⟩)
      (originalSelectedEnumeration P ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩)
    rw [c.originalCapSpliceDistance_cap_sum] at he
    exact_mod_cast (show ((JP 0).val : ℤ) < ((JH middle).val : ℤ) by omega)
  have ht1 : JP (Fin.last _) < JH middle := by
    have hp := (hfP (Fin.last _)).2.2
    have hh := (hfH middle).2.2
    rw [originalHessenbergDistance_last P hB] at hp
    have he := c.originalTrueCaps_below_closure P
      (originalSelectedEnumeration P ⟨0, hB⟩)
      (originalSelectedEnumeration P ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩)
    rw [c.originalCapSpliceDistance_cap_sum] at he
    exact_mod_cast (show ((JP (Fin.last _)).val : ℤ) < ((JH middle).val : ℤ) by omega)
  have hcorner : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det ^ a =
      (jtMatrix (fun j : Fin k => W.xi j.succ)
        (fun j => W.zeta j.castSucc)).det ^ b := by
    rw [hKU, hKW, ← pow_mul, ← pow_mul, Nat.mul_comm b a]
  obtain ⟨ε, hε, hratio⟩ := c.originalWindow_cap_normalized_ratio P W q v z hwindow hW
    hcutq hcutLq hC hP hQ b a d hd hcorner
  obtain ⟨p', t', hcop, hplane⟩ := c.originalHorizontalClosure_monic_dependence P H h hH
    hB hP _ p t hpt hdep
  have he := hratio.symm.trans hplane
  have hunit : IsUnit (C (ε : residueLowerField c.top c.top) : ResidueHigherPolynomial c.top) := by
    apply (Int.isUnit_iff.mpr hε).map
      ((MvPolynomial.C : residueLowerField c.top c.top →+* ResidueHigherPolynomial c.top).comp
        (Int.castRingHom _))
  let r := primeOrder (cellSchur D hD.1) Λ
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU, primeOrder_pow (irreducible_cellSchur hD).prime]
    exact Nat.mul_comm _ _
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW, primeOrder_pow (irreducible_cellSchur hD).prime]
    exact Nat.mul_comm _ _
  have hval : residueHigherEval c.top (X (JH middle)) +
      residueHigherEval c.top (BH middle) =
      c.regularResidue (c.originalHessenbergResponse H middle middle) := by
    rw [← map_add, (hfH middle).2.1]
  have he' : let F := (X (JP 0) + BP 0) * (X (JP (Fin.last _)) + BP (Fin.last _))
      residueHigherEval c.top (C (ε : residueLowerField c.top c.top)) *
          (residueHigherEval c.top (∏ i, (X (J i) + B i))) ^ a /
          ((residueHigherEval c.top (∏ i, (X (JW i) + BW i))) ^ b *
            (residueHigherEval c.top F) ^ d) =
        Polynomial.aeval ((residueHigherEval c.top (X (JH middle)) +
          residueHigherEval c.top (BH middle)) / residueHigherEval c.top F) p' /
        Polynomial.aeval ((residueHigherEval c.top (X (JH middle)) +
          residueHigherEval c.top (BH middle)) / residueHigherEval c.top F) t' := by
    simpa only [map_prod, map_mul, map_add, map_intCast, map_C, hf,
      fun i => (hfW i).2.1, (hfP 0).2.1, (hfP (Fin.last _)).2.1,
      hval, originalTrueCapProduct] using he
  obtain ⟨label, hlabel⟩ := actualResidue_active_family c.top Finset.univ Finset.univ J B JW BW
    (fun i _ => (hfP ⟨i.val + 1, by omega⟩).1) (fun i _ => (hfW i).1)
    JP BP (fun i => (hfP i).1) ht0 ht1 (BH middle) (BP 0) (BP (Fin.last _))
    (C (ε : residueLowerField c.top c.top)) (hfH middle).1 (hfP 0).1
    (hfP (Fin.last _)).1 hunit p' t' hcop r a b d
    (by simpa only [Finset.card_univ, Fintype.card_fin] using (by omega :
      originalSelectedCount (hD := hD) P - 1 + 1 = r * b))
    (by simpa only [Finset.card_univ, Fintype.card_fin] using (by omega :
      originalSelectedCount (hD := hD) W - 1 + 1 = r * a)) hd he'
  constructor
  · refine ⟨label, fun j hj => ?_⟩
    have hj' : a * (Finset.univ.filter fun i => residueHigherEval c.top (X (JP j) + BP j) =
        residueHigherEval c.top (X (J i) + B i)).card ≠
        b * (Finset.univ.filter fun i => residueHigherEval c.top (X (JP j) + BP j) =
          residueHigherEval c.top (X (JW i) + BW i)).card := by
      simpa only [(hfP j).2.1, hf, fun i => (hfW i).2.1] using hj
    obtain ⟨ht, hv⟩ := hlabel j hj'
    refine ⟨?_, ?_⟩
    · have hh := congrArg (fun x : ResidueHigherIndex c.top => (x.val : ℤ)) ht
      rw [(hfP j).2.2, (hfH middle).2.2] at hh
      exact hh
    · simpa only [(hfP j).2.1, (hfH middle).2.1, (hfP 0).2.1,
        (hfP (Fin.last _)).2.1, originalTrueCapProduct] using hv
  · have hs : (Finset.univ : Finset (Fin (originalSelectedCount (hD := hD) P - 1))).card +
        1 = r * b := by
      simpa only [Finset.card_univ, Fintype.card_fin] using (by omega :
        originalSelectedCount (hD := hD) P - 1 + 1 = r * b)
    have ht : (Finset.univ : Finset (Fin (originalSelectedCount (hD := hD) W - 1))).card +
        1 = r * a := by
      simpa only [Finset.card_univ, Fintype.card_fin] using (by omega :
        originalSelectedCount (hD := hD) W - 1 + 1 = r * a)
    have hfactor := actualResidue_rational_factorization c.top Finset.univ Finset.univ
      J B JW BW (fun i _ => (hfP ⟨i.val + 1, by omega⟩).1) (fun i _ => (hfW i).1)
      ht0 ht1 (BH middle) (BP 0) (BP (Fin.last _))
      (C (ε : residueLowerField c.top c.top)) (hfH middle).1 (hfP 0).1
      (hfP (Fin.last _)).1 hunit p' t' hcop r a b d hs ht hd he'
    have hunitScalar := actualResidue_unit_normalization c.top Finset.univ Finset.univ
      J B JW BW (fun i _ => (hfP ⟨i.val + 1, by omega⟩).1) (fun i _ => (hfW i).1)
      ht0 ht1 (BH middle) (BP 0) (BP (Fin.last _))
      (C (ε : residueLowerField c.top c.top)) (hfH middle).1 (hfP 0).1
      (hfP (Fin.last _)).1 hunit p' t' hcop r a b d hs ht hd he'
    have hscalar : p'.leadingCoeff / t'.leadingCoeff = (ε : ℚ) := by
      apply RingHom.injective (algebraMap ℚ (residueLowerField c.top c.top))
      simpa only [map_intCast] using (MvPolynomial.C_injective _ _ hunitScalar).symm
    have hcast (α : ℚ) : algebraMap ℚ (OtherField c.top) α = (α : OtherField c.top) := by
      simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ (OtherField c.top)) α
    let F := (X (JP 0) + BP 0) * (X (JP (Fin.last _)) + BP (Fin.last _))
    have hF : ∀ j ∈ F.vars, j < JH middle := by
      intro j hj
      rcases Finset.mem_union.mp (vars_mul _ _ hj) with hj | hj
      · exact monicTriangularPolynomial_vars_below ht0 (hfP 0).1 j hj
      · exact monicTriangularPolynomial_vars_below ht1 (hfP (Fin.last _)).1 j hj
    have hF0 : residueHigherEval c.top F ≠ 0 := by
      have hp : F ≠ 0 := mul_ne_zero (monicTriangularPolynomial_prime (hfP 0).1).ne_zero
        (monicTriangularPolynomial_prime (hfP (Fin.last _)).1).ne_zero
      intro hz
      apply hp
      exact residueHigherEval_injective c.top (hz.trans (map_zero _).symm)
    have htrans : Transcendental ℚ
        ((residueHigherEval c.top (X (JH middle)) +
          residueHigherEval c.top (BH middle)) / residueHigherEval c.top F) := by
      intro halg
      obtain ⟨α, hα⟩ := residueField_algebraic_constants c.top _ halg
      exact actualResidue_plane_not_rational c.top (hfH middle).1 hF hF0 α hα.symm
    have hactualTrans : Transcendental ℚ (c.regularResidue
        (c.originalHessenbergResponse H middle middle) / c.originalTrueCapProduct P) := by
      simpa only [F, map_mul, (hfP 0).2.1, (hfP (Fin.last _)).2.1,
        hval, originalTrueCapProduct] using htrans
    have hcounts (α : ℚ) := actualResidue_root_class_exponent c.top
      Finset.univ Finset.univ J B JW BW
      (fun i _ => (hfP ⟨i.val + 1, by omega⟩).1) (fun i _ => (hfW i).1)
      ht0 ht1 (BH middle) (BP 0) (BP (Fin.last _))
      (C (ε : residueLowerField c.top c.top)) (hfH middle).1 (hfP 0).1
      (hfP (Fin.last _)).1 hunit p' t' hcop r a b d hs ht hd he' α
    refine ⟨ε, splitActiveRoots p' t', splitRootExponent p' t', hactualTrans, hε,
      hfactor.2.1, hfactor.2.2.1, mem_splitActiveRoots_iff p' t', ?_, ?_, ?_⟩
    · intro α
      have hm := hcounts α
      dsimp only at hm
      rw [triangularClassCount_eq_source_count c.top Finset.univ J B
          (fun i _ => (hfP ⟨i.val + 1, by omega⟩).1) (JH middle) _
          (triangularPlaneRoot_lower (hfH middle).1 hF _),
        triangularClassCount_eq_source_count c.top Finset.univ JW BW
          (fun i _ => (hfW i).1) (JH middle) _
          (triangularPlaneRoot_lower (hfH middle).1 hF _)] at hm
      have hroot := actualResidue_active_identity c.top (JH middle) (BH middle)
        (BH middle - C (algebraMap ℚ (residueLowerField c.top c.top) α) * F) F α rfl
      rw [hroot] at hm
      symm
      simp only [F, middle, map_add, map_mul, hf, fun i => (hfW i).2.1,
        (hfP 0).2.1, (hfP (Fin.last _)).2.1, hval, originalTrueCapProduct] at hm ⊢
      convert hm using 1
      congr 2
    · rw [hratio]
      simpa only [map_prod, map_mul, map_add, map_intCast, map_C, hf,
        fun i => (hfW i).2.1, (hfP 0).2.1, (hfP (Fin.last _)).2.1,
        hval, originalTrueCapProduct, hscalar, hcast, Rat.cast_intCast] using hfactor.2.2.2
    · obtain ⟨labelW, hlabelW⟩ := actualResidue_active_family c.top
        Finset.univ Finset.univ J B JW BW
        (fun i _ => (hfP ⟨i.val + 1, by omega⟩).1) (fun i _ => (hfW i).1)
        JW BW (fun i => (hfW i).1) ht0 ht1 (BH middle) (BP 0) (BP (Fin.last _))
        (C (ε : residueLowerField c.top c.top)) (hfH middle).1 (hfP 0).1
        (hfP (Fin.last _)).1 hunit p' t' hcop r a b d hs ht hd he'
      refine ⟨labelW, ?_⟩
      intro j hj
      have hj' : a * (Finset.univ.filter fun i =>
          residueHigherEval c.top (X (JW j) + BW j) =
            residueHigherEval c.top (X (J i) + B i)).card ≠
        b * (Finset.univ.filter fun i =>
          residueHigherEval c.top (X (JW j) + BW j) =
            residueHigherEval c.top (X (JW i) + BW i)).card := by
        simpa only [(hfW j).2.1, hf, fun i => (hfW i).2.1] using hj
      simpa only [(hfW j).2.1, (hfH middle).2.1, (hfP 0).2.1,
        (hfP (Fin.last _)).2.1, originalTrueCapProduct] using (hlabelW j hj').2

end SkewCornerDescent.Matrix.SelectedCoordinate
