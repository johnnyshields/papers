/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassCaps
import SkewCornerDescent.Matrix.OriginalResponseClassRepresentatives
import SkewCornerDescent.Matrix.ActualTwoChambers

/-!
# Two regular chambers for the actual complete response-class family

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `lem:dual-identities`).
One collection of actual rational representatives gives both nonempty open
chambers. Every denominator is regular on each base assignment, and the two true
cap responses have positive product there. The actual active-class classifier
supplies the anchor premise in the matched-chart assembly. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual source family and literal closure top produce two common regular
chambers. No triangular family, cap sign, or source denominator is assumed. -/
theorem originalResponseClasses_two_chambers {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+)
    (hKeq : let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
      (K : ℤ) = originalHessenbergDistance (hD := hD) Q middle middle)
    (hanchor : ∃ a : c.OriginalResponseClass P, c.originalResponseClassTop P hB a = K) :
    let top := c.originalResponseClassTop P hB
    let left := c.originalResponseClassOf P 0
    let right := c.originalResponseClassOf P (Fin.last _)
    ∃ p q : c.OriginalResponseClass P → OtherPolynomial c.top,
      (∀ a j, j ∈ (realResiduePolynomial c.top (p a)).vars → j < (top a : ℕ)) ∧
      (∀ a j, j ∈ (realResiduePolynomial c.top (q a)).vars → j < (c.top : ℕ)) ∧
      (∀ a, a.val = residueGenerator c.top
          ⟨top a, ne_of_gt (c.originalResponseClassTop_gt P hB a)⟩ +
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (p a) /
          algebraMap (OtherPolynomial c.top) (OtherField c.top) (q a)) ∧
      ∀ positive : Bool,
        IsOpen (simultaneousActualChamber c.top K top p q positive) ∧
        (simultaneousActualChamber c.top K top p q positive).Nonempty ∧
        ∀ x ∈ simultaneousActualChamber c.top K top p q positive,
          (∀ a, MvPolynomial.eval x (realResiduePolynomial c.top (q a)) ≠ 0) ∧
          0 < rationalTriangularResponse (top left : ℕ)
            (realResiduePolynomial c.top (p left)) (realResiduePolynomial c.top (q left)) x *
            rationalTriangularResponse (top right : ℕ)
              (realResiduePolynomial c.top (p right))
              (realResiduePolynomial c.top (q right)) x := by
  classical
  let idx := c.originalResponseClassIndex P
  let top := c.originalResponseClassTop P hB
  let left := c.originalResponseClassOf P 0
  let right := c.originalResponseClassOf P (Fin.last _)
  have htop : ∀ a, c.top < top a := c.originalResponseClassTop_gt P hB
  have hindices : ∀ a,
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (originalHessenbergRows P (idx a)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (originalHessenbergCols P (idx a)))) =
        (top a : ℤ) := fun a => (c.originalHessenbergTop_coe P hB (idx a) (idx a) le_rfl).symm
  have hdistinct : ∀ a b : c.OriginalResponseClass P, top a = K → top b = K → a ≠ b →
      c.regularResidue (c.originalLocalResponse P (originalHessenbergRows P (idx a))
        (originalHessenbergCols P (idx a))) ≠
      c.regularResidue (c.originalLocalResponse P (originalHessenbergRows P (idx b))
        (originalHessenbergCols P (idx b))) := by
    intro a b _ _ hab
    change c.regularResidue (c.originalHessenbergResponse P (idx a) (idx a)) ≠
      c.regularResidue (c.originalHessenbergResponse P (idx b) (idx b))
    rw [c.originalResponseClassIndex_spec P a, c.originalResponseClassIndex_spec P b]
    exact fun h => hab (Subtype.ext h)
  obtain ⟨p, q, hp, hq, he, hchamber⟩ := c.originalResponses_simultaneous_chambers
    (fun _ => n) (fun _ => P) (fun a => originalHessenbergRows P (idx a))
    (fun a => originalHessenbergCols P (idx a)) top htop hindices (fun _ => hmax)
    K hanchor hdistinct
  have hrepresentation : ∀ a, a.val = residueGenerator c.top ⟨top a, ne_of_gt (htop a)⟩ +
      algebraMap (OtherPolynomial c.top) (OtherField c.top) (p a) /
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (q a) := by
    intro a
    have h := he a
    change c.regularResidue (c.originalHessenbergResponse P (idx a) (idx a)) = _ at h
    rw [c.originalResponseClassIndex_spec P a] at h
    exact h
  obtain ⟨a0, ha0⟩ := hanchor
  have hNK : c.top < K := ha0 ▸ htop a0
  have hNKnat : (c.top : ℕ) ≤ (K : ℕ) := hNK.le
  have hc := c.originalResponseClass_caps_below_closure P Q v hQ hB K hKeq
  have hl : top left < K := hc.1
  have hr : top right < K := hc.2
  dsimp only
  refine ⟨p, q, hp, hq, hrepresentation, ?_⟩
  intro positive
  refine ⟨(hchamber positive).1, (hchamber positive).2, ?_⟩
  intro x hx
  let anchor : {a : c.OriginalResponseClass P // top a = K} := ⟨a0, ha0⟩
  let y := anchorAssignment (K : ℕ)
    (rationalAnchorRoot (fun a => realResiduePolynomial c.top (p a.val))
      (fun a => realResiduePolynomial c.top (q a.val))) anchor x
  have hxy : ∀ j, j < (K : ℕ) → x j = y j := by
    intro j hj
    dsimp only [y, anchorAssignment]
    exact (Function.update_of_ne (ne_of_lt hj) _ _).symm
  have hqbase : ∀ a, MvPolynomial.eval x (realResiduePolynomial c.top (q a)) ≠ 0 := by
    intro a
    by_cases ha : top a = K
    · exact hx.1 ⟨a, ha⟩
    · have hy := (hx.2.2 anchor ⟨a, ha⟩).1
      have heq := eval_polynomial_eq_of_agree_below (realResiduePolynomial c.top (q a))
        (K : ℕ) (fun j hj => (hq a j hj).trans_le hNKnat) x y hxy
      rw [heq]
      exact hy
  have hresponse (a : c.OriginalResponseClass P) (ha : top a < K) :
      rationalTriangularResponse (top a : ℕ) (realResiduePolynomial c.top (p a))
          (realResiduePolynomial c.top (q a)) x =
        rationalTriangularResponse (top a : ℕ) (realResiduePolynomial c.top (p a))
          (realResiduePolynomial c.top (q a)) y := by
    unfold rationalTriangularResponse
    rw [hxy (top a : ℕ) ha,
      eval_polynomial_eq_of_agree_below (realResiduePolynomial c.top (p a)) (K : ℕ)
        (fun j hj => (hp a j hj).trans ha) x y hxy,
      eval_polynomial_eq_of_agree_below (realResiduePolynomial c.top (q a)) (K : ℕ)
        (fun j hj => (hq a j hj).trans_le hNKnat) x y hxy]
  refine ⟨hqbase, ?_⟩
  rw [hresponse left hl, hresponse right hr]
  exact (simultaneousActualChamber_cap_product_pos c.top K top p q positive left right
    (ne_of_lt hl) (ne_of_lt hr) x hx anchor).2.2

end SkewCornerDescent.Matrix.SelectedCoordinate
