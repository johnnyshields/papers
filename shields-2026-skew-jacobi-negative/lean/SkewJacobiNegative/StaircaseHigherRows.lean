/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.NegativeInvariants
import SkewJacobiNegative.SchurClasses
import SkewJacobiNegative.PositiveBorders
import SkewJacobiNegative.GeneralHessenberg
import SkewJacobiNegative.StaircaseFivePlacements
import SkewJacobiNegative.ConnectedBorderRigidity
import SkewJacobiNegative.NegativeRealizability

/-!
# Staircase classes and higher-row rigidity

The full negative mask and its unrestricted mate closure, the M1--M4
five-row classes, endpoint isolation, complete positive-border separation,
and arbitrary-mate higher-row rigidity for
`shields-2026-skew-jacobi-negative.tex`.  Common beta entries are retained
through the actual Gamma map and its parameter descent.
-/

namespace SkewJacobiNegative.StaircaseHigherRows

open Finset

/-- The actual six-site staircase, not a condition on the negative count alone. -/
def HasStaircase {n : ℕ} (D : BetaDiagram n) : Prop :=
  5 ≤ n ∧ ∀ i j, D.row i < D.col j ↔ j.val + (n - 3) ≤ i.val

/-- Every padded overlap part at a fixed order lies on the same side of the
negative threshold.  The zero parts are retained. -/
theorem overlap_threshold_iff {n : ℕ} {D : BetaDiagram n}
    (hD : HasStaircase D) {k v : ℕ} (hk : 2 ≤ k)
    (hv : v ∈ D.paddedRowOverlaps k) :
    v ≤ k - 2 ↔ n - 3 ≤ k - 1 := by
  change v ∈ (Finset.range (n - (k - 1))).val.map
    (D.toWeakRows.overlap (k - 1)) at hv
  obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hv
  have hj' : j < n - (k - 1) := Finset.mem_range.mp hj
  rw [D.overlap_negative_iff hk hj', hD.2]
  dsimp
  omega

/-- A staircase mask is reconstructed against a mate of arbitrary row count
from the actual all-order padded overlap invariant. -/
theorem staircase_mate_closure {n m : ℕ} {D : BetaDiagram n} {E : BetaDiagram m}
    (hD : HasStaircase D) (he : D.schur = E.schur) :
    n = m ∧ HasStaircase E := by
  have hn := D.row_count_of_schur_eq E he
  subst m
  refine ⟨rfl, hD.1, ?_⟩
  intro i j
  by_cases hij : j.val < i.val
  · let k := i.val - j.val + 1
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hj : j.val < n - (k - 1) := by dsimp [k]; have := i.isLt; omega
    have hi : (⟨j.val + (k - 1), by omega⟩ : Fin n) = i := by
      apply Fin.ext
      dsimp [k]
      omega
    have hv : E.toWeakRows.overlap (k - 1) j.val ∈ E.paddedRowOverlaps k := by
      change E.toWeakRows.overlap (k - 1) j.val ∈
        (Finset.range (n - (k - 1))).val.map (E.toWeakRows.overlap (k - 1))
      exact Multiset.mem_map.mpr ⟨j.val, Finset.mem_range.mpr hj, rfl⟩
    rw [← D.paddedRowOverlaps_eq_of_schur_eq E he k] at hv
    have hb := overlap_threshold_iff hD hk hv
    have htest := E.overlap_negative_iff hk hj
    rw [hi] at htest
    rw [← htest, hb]
    dsimp [k]
    omega
  · have hneg : ¬ E.row i < E.col j := by
      intro h
      exact hij (E.negative_below_diagonal h)
    have hbound : ¬ j.val + (n - 3) ≤ i.val := by
      have := hD.1
      omega
    exact iff_of_false hneg hbound

/-- No connectedness or sign assumption on the mate is needed for mask closure;
connected mates in particular have exactly the original six negative sites. -/
theorem staircase_connected_mate_closure {n m : ℕ}
    {D : BetaDiagram n} {E : BetaDiagram m}
    (hD : HasStaircase D) (_hE : E.Connected) (he : D.schur = E.schur) :
    n = m ∧ HasStaircase E := staircase_mate_closure hD he

/-- The three occupied southwest rows contain one, two, and three sites. -/
theorem staircase_negativeSites {n : ℕ} {D : BetaDiagram n}
    (hD : HasStaircase D) :
    negativeSites D =
      {(⟨n - 3, by have := hD.1; omega⟩, ⟨0, by have := hD.1; omega⟩),
       (⟨n - 2, by have := hD.1; omega⟩, ⟨0, by have := hD.1; omega⟩),
       (⟨n - 2, by have := hD.1; omega⟩, ⟨1, by have := hD.1; omega⟩),
       (⟨n - 1, by have := hD.1; omega⟩, ⟨0, by have := hD.1; omega⟩),
       (⟨n - 1, by have := hD.1; omega⟩, ⟨1, by have := hD.1; omega⟩),
       (⟨n - 1, by have := hD.1; omega⟩, ⟨2, by have := hD.1; omega⟩)} := by
  classical
  ext p
  obtain ⟨i, j⟩ := p
  have := hD.1
  simp only [negativeSites, mem_filter, mem_univ, true_and, hD.2,
    mem_insert, mem_singleton, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero]
  have := i.isLt
  have := j.isLt
  omega

/-- The six-negative count follows from the full actual mask at every order. -/
theorem staircase_negativeCount {n : ℕ} {D : BetaDiagram n}
    (hD : HasStaircase D) : negativeCount D = 6 := by
  classical
  have hn := hD.1
  rw [negativeCount, staircase_negativeSites hD]
  have h32 : n - 3 ≠ n - 2 := by omega
  have h31 : n - 3 ≠ n - 1 := by omega
  have h21 : n - 2 ≠ n - 1 := by omega
  simp [Fin.ext_iff, h32, h31, h21]

/-- Homogenization preserves the whole mask, not just its cardinality. -/
theorem staircase_gamma_iff {n : ℕ} (D : BetaDiagram n) :
    HasStaircase D.gamma ↔ HasStaircase D := by
  simp only [HasStaircase, D.gamma_negative_iff]

/-- A positive-row maximal cofactor has the staircase one order down. -/
theorem staircase_corner {n : ℕ} (D : BetaDiagram (n+1))
    (hD : HasStaircase D) (hn : 5 ≤ n) (hP : D.PositiveCorner) :
    HasStaircase (D.cornerDiagram hP) := by
  refine ⟨hn, ?_⟩
  intro i j
  change D.row i.succ < D.col j.castSucc ↔ _
  rw [hD.2]
  simp only [Fin.val_succ, Fin.val_castSucc]
  omega

/-- At least six rows make the maximal cofactor connected; no child rigidity
or literal cofactor-equality premise is used. -/
theorem staircase_corner_connected {n : ℕ} (D : BetaDiagram (n+1))
    (hD : HasStaircase D) (hn : 5 ≤ n) (hP : D.PositiveCorner) :
    (D.cornerDiagram hP).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  let k : Fin (n+1) := ⟨i.val+2, by omega⟩
  have hnot : ¬ D.row k < D.col i.castSucc := by
    rw [hD.2]
    dsimp [k]
    omega
  have hk : (⟨i.val+1, hi⟩ : Fin n).succ = k := by
    apply Fin.ext
    rfl
  change D.col i.castSucc ≤ D.row (⟨i.val+1, hi⟩ : Fin n).succ
  rw [hk]
  exact le_of_not_gt hnot

/-- The zero-free source gives the actual positive-row, connected staircase
cofactor required at the six-row induction boundary and every larger order. -/
theorem zeroFree_staircase_child {n : ℕ} (D : BetaDiagram (n+1))
    (hD : HasStaircase D) (hn : 5 ≤ n) (hC : D.Connected) (hZ : D.ZeroFree) :
    let hP := D.positiveCorner_of_connected_zeroFree hC hZ
    HasStaircase (D.cornerDiagram hP) ∧ (D.cornerDiagram hP).Connected := by
  dsimp only
  exact ⟨staircase_corner D hD hn _, staircase_corner_connected D hD hn _⟩

/-- At five rows the full staircase mask is intrinsic Hessenberg geometry in
the actual normalized profile. -/
theorem five_profile_hessenberg (D : BetaDiagram 5)
    (hD : HasStaircase D) (hC : D.Connected) :
    (D.toProfile hC).Hessenberg := by
  intro i j hij
  rw [D.toProfile_xi hC, D.toProfile_zeta hC]
  have hn : D.row i < D.col j := (hD.2 i j).mpr (by omega)
  dsimp only
  omega

/-- Thickness in the actual profile is produced from the complete mask. -/
theorem five_profile_thick (D : BetaDiagram 5)
    (hD : HasStaircase D) (hC : D.Connected) :
    Staircase.Thick (D.toProfile hC) :=
  GeneralHessenberg.hessenberg_thick _ (five_profile_hessenberg D hD hC)

/-- A zero-free connected full board has positive actual profile gaps. -/
theorem profile_gaps_pos_of_zeroFree {n : ℕ} (D : BetaDiagram (n+1))
    (hC : D.Connected) (hZ : D.ZeroFree) (j : Fin n) :
    0 < (D.toProfile hC).g j := by
  have hg := (D.toProfile hC).xi_succ_sub_zeta_castSucc j
  rw [D.toProfile_xi hC, D.toProfile_zeta hC] at hg
  have hz := hZ j.succ j.castSucc
  dsimp only at hg
  omega

/-- Arbitrary connected five-row mates of a zero-free staircase are in the
actual positive-gap thick domain; the domain is not an added hypothesis. -/
theorem five_mate_thick (D E : BetaDiagram 5)
    (hD : HasStaircase D) (hC : D.Connected) (hZ : D.ZeroFree)
    (hE : E.Connected) (he : D.schur = E.schur) :
    Staircase.Thick (E.toProfile hE) ∧ ∀ j, 0 < (E.toProfile hE).g j := by
  have hm := (staircase_mate_closure hD he).2
  have hz := D.zeroFree_of_schur_eq E hC hE hZ he
  exact ⟨five_profile_thick E hm hE, profile_gaps_pos_of_zeroFree E hE hz⟩

/-- Gamma supplies both thickness and positive gaps to a connected five-row
staircase with common betas, before any classification is applied. -/
theorem five_gamma_thick (D : BetaDiagram 5)
    (hD : HasStaircase D) (hC : D.Connected) :
    let hGC := D.gamma_connected_iff.mpr hC
    Staircase.Thick (D.gamma.toProfile hGC) ∧
      ∀ j, 0 < (D.gamma.toProfile hGC).g j := by
  dsimp only
  exact ⟨five_profile_thick D.gamma ((staircase_gamma_iff D).mpr hD) _,
    profile_gaps_pos_of_zeroFree D.gamma _ D.gamma_zeroFree⟩

/-- Zero-free endpoint isolation, with the complete five-row base and the
actual connected staircase cofactor at every induction step. -/
theorem zeroFree_endpoint_symmetry :
    ∀ (n : ℕ) (D : BetaDiagram (n+5)), HasStaircase D → D.Connected →
      D.ZeroFree → ∀ (t : ℤ) (ht : 0 < t),
      (D.extendTop t ht).schur = (D.extendBottom t ht).schur → D.Symmetric := by
  intro n
  induction n with
  | zero =>
    intro D hD hC hZ t ht he
    let P := D.toProfile hC
    have hP : Staircase.Thick P := five_profile_thick D hD hC
    have hg : ∀ j, 0 < P.g j := profile_gaps_pos_of_zeroFree D hC hZ
    have hnorm := StaircaseFivePlacements.normalized_endpoint_polynomials D hC t ht
    have heP : (P.toBetaDiagram.extendTop t ht).schur =
        (P.toBetaDiagram.extendBottom t ht).schur := by
      rw [hnorm.1, hnorm.2]
      exact he
    exact StaircaseFivePlacements.symmetric_of_profile_rotate D hC
      (StaircaseFivePlacements.five_endpoint_rotate P hP hg t ht heP)
  | succ n ih =>
    intro D hD hC hZ t ht he
    let hP := D.positiveCorner_of_connected_zeroFree hC hZ
    let C := D.cornerDiagram hP
    have hCM : HasStaircase C := staircase_corner D hD (by omega) hP
    have hCC : C.Connected := staircase_corner_connected D hD (by omega) hP
    have hCZ : C.ZeroFree := by
      intro i j
      exact hZ i.succ j.castSucc
    have hzero : D.endpointDifference t ht = 0 := sub_eq_zero.mpr he
    have hcoeff : D.endpointCoefficient = 0 := by
      have hd := D.endpointDifference_pderiv t ht
      rw [hzero, map_zero] at hd
      exact hd.symm
    have htie : D.topMargin = D.bottomMargin := by
      by_contra hn
      exact D.endpointCoefficient_ne_zero_untied hP hn hcoeff
    rw [D.endpointCoefficient_tied hP htie] at hcoeff
    have hchild : C.endpointDifference D.topMargin D.topMargin_pos = 0 :=
      (mul_eq_zero.mp hcoeff).resolve_left
        (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    have heChild : (C.extendTop D.topMargin D.topMargin_pos).schur =
        (C.extendBottom D.topMargin D.topMargin_pos).schur := sub_eq_zero.mp hchild
    exact D.symmetric_of_tied_corner hP htie
      (ih C hCM hCC hCZ D.topMargin D.topMargin_pos heChild)

/-- Endpoint isolation at every staircase order, with common beta entries
removed and restored by the faithful full-order Gamma map. -/
theorem staircase_endpoint_isolation_at (n : ℕ) (D : BetaDiagram (n+5))
    (hD : HasStaircase D) (hC : D.Connected) (t : ℤ) (ht : 0 < t) :
    (D.extendTop t ht).schur = (D.extendBottom t ht).schur ↔ D.Symmetric := by
  constructor
  · intro he
    have hΓ :=
      ((D.extendTop t ht).gamma_schur_eq_iff_same_order (D.extendBottom t ht)
        (D.extendTop_connected hC t ht) (D.extendBottom_connected hC t ht)).mpr he
    rw [StaircaseFivePlacements.gamma_top_extension_polynomial,
      StaircaseFivePlacements.gamma_bottom_extension_polynomial] at hΓ
    have hs : D.gamma.Symmetric := zeroFree_endpoint_symmetry n D.gamma
      ((staircase_gamma_iff D).mpr hD) (D.gamma_connected_iff.mpr hC)
      D.gamma_zeroFree (2*t) (by omega) hΓ
    exact (D.gamma_rotation_iff D).mp hs
  · intro hs
    exact sub_eq_zero.mp (D.endpointDifference_eq_zero_of_symmetric hs t ht)

/-- `lem:staircase-endpoint`, with no row bound beyond the staircase's five-row
lower endpoint and no zero-free or untied-margin hypothesis. -/
theorem staircase_endpoint_isolation {n : ℕ} (D : BetaDiagram (n+1))
    (hD : HasStaircase D) (hC : D.Connected) (t : ℤ) (ht : 0 < t) :
    (D.extendTop t ht).schur = (D.extendBottom t ht).schur ↔ D.Symmetric := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k+4 := ⟨n-4, by have := hD.1; omega⟩
  subst n
  exact staircase_endpoint_isolation_at k D hD hC t ht

/-- Independent orientations of an actual child's rotation orbit. -/
def oriented (D : BetaDiagram 5) (rev : Bool) : BetaDiagram 5 :=
  if rev then D.rotate else D

theorem oriented_connected (D : BetaDiagram 5) (hD : D.Connected) (rev : Bool) :
    (oriented D rev).Connected := by
  cases rev
  · exact hD
  · exact D.rotate_connected hD

theorem oriented_schur (D : BetaDiagram 5) (rev : Bool) :
    (oriented D rev).schur = D.schur := by
  cases rev <;> simp [oriented,BetaDiagram.rotate_schur]

/-- The sum of opposite extensions is invariant under rotating the core.
Both extension functions are the actual full beta determinants. -/
theorem oriented_endpoint_sum (D : BetaDiagram 5) (rev : Bool)
    (q : ℤ) (hq : 0 < q) :
    StaircaseFivePlacements.endpointSum (oriented D rev) q hq =
      StaircaseFivePlacements.endpointSum D q hq := by
  cases rev with
  | false => rfl
  | true =>
    have hR : D.rotate.RotationEquivalent D := by
      refine ⟨0,?_,?_⟩ <;> intro i <;> simp [BetaDiagram.rotate]
    have hR' : D.RotationEquivalent D.rotate := by
      refine ⟨0,?_,?_⟩ <;> intro i <;> simp [BetaDiagram.rotate]
    have htop := D.rotate.extendTop_schur_eq_extendBottom_of_rotation D hR q hq
    have hbottom := D.extendTop_schur_eq_extendBottom_of_rotation D.rotate hR' q hq
    change (D.rotate.extendTop q hq).schur+(D.rotate.extendBottom q hq).schur =
      (D.extendTop q hq).schur+(D.extendBottom q hq).schur
    rw [htop,← hbottom,add_comm]

/-- Equal tied positive borders of equal connected children have the same
margin and the same full endpoint sum.  Their marker equality is produced
from the actual largest-label reading. -/
theorem tied_border_endpoint_sum_eq (D E : BetaDiagram 5)
    (hD : D.Connected) (hE : E.Connected) (hcore : D.schur = E.schur)
    (q r : ℤ) (hq : 0 < q) (hr : 0 < r)
    (he : (D.positiveBorder q q hq hq).schur =
      (E.positiveBorder r r hr hr).schur) :
    q = r ∧ StaircaseFivePlacements.endpointSum D q hq =
      StaircaseFivePlacements.endpointSum E r hr := by
  have hspan := D.largestLabel_eq_of_schur_eq E hD hE hcore
  have hparent := (D.positiveBorder q q hq hq).largestLabel_eq_of_schur_eq
    (E.positiveBorder r r hr hr)
    (D.positiveBorder_connected q q hq hq) (E.positiveBorder_connected r r hr hr) he
  rw [BetaDiagram.positiveBorder_largestLabel,BetaDiagram.positiveBorder_largestLabel] at hparent
  have hqr : q = r := by omega
  subst r
  refine ⟨rfl,?_⟩
  let v : ℕ+ := ⟨(D.largestLabel+q).toNat,by have := D.largestLabel_pos; omega⟩
  have hvD : (v.val : ℤ) = D.largestLabel+q := by
    dsimp [v]; have := D.largestLabel_pos; omega
  have hvE : (v.val : ℤ) = E.largestLabel+q := by omega
  have hd := congrArg (MvPolynomial.pderiv v) he
  rw [StaircaseFivePlacements.tied_five_border_derivative D q hq v hvD,
    StaircaseFivePlacements.tied_five_border_derivative E q hr v hvE] at hd
  simpa only [StaircaseFivePlacements.endpointSum,add_comm] using hd

/-- Tied positive borders over the two B rotation orbits are unequal at every
pair of positive margins, including zero-gap child profiles. -/
theorem b_tied_border_separation (p m z w : ℤ)
    (hz : 0 ≤ z) (hw : 0 ≤ w) (hp : z+w < p) (hm : z+w < m) (hne : p ≠ m)
    (revF revH : Bool) (q r : ℤ) (hq : 0 < q) (hr : 0 < r) :
    ((oriented (StaircaseFivePlacements.bProfileF p m z w hz hw hp hm).toBetaDiagram revF).positiveBorder q q hq hq).schur ≠
    ((oriented (StaircaseFivePlacements.bProfileH p m z w hz hw hp hm).toBetaDiagram revH).positiveBorder r r hr hr).schur := by
  let F := (StaircaseFivePlacements.bProfileF p m z w hz hw hp hm).toBetaDiagram
  let H := (StaircaseFivePlacements.bProfileH p m z w hz hw hp hm).toBetaDiagram
  have hF : F.Connected := Gluing.Profile.toBetaDiagram_connected _
  have hH : H.Connected := Gluing.Profile.toBetaDiagram_connected _
  have hcore : (oriented F revF).schur = (oriented H revH).schur := by
    rw [oriented_schur,oriented_schur]
    exact StaircaseFivePlacements.b_profiles_schur_eq p m z w hz hw hp hm
  intro he
  obtain ⟨hqr,hsum⟩ := tied_border_endpoint_sum_eq
    (oriented F revF) (oriented H revH)
    (oriented_connected F hF revF) (oriented_connected H hH revH)
    hcore q r hq hr he
  subst r
  rw [oriented_endpoint_sum,oriented_endpoint_sum] at hsum
  exact StaircaseFivePlacements.b_endpoint_sum_ne p m z w hz hw hp hm hne q hq hsum

/-- The second row moment is read from the actual full row multiset. -/
theorem profile_row_squares_eq {n : ℕ} (P Q : Gluing.Profile n)
    (he : P.toBetaDiagram.schur = Q.toBetaDiagram.schur) :
    (∑ i, (P.r i : ℤ)^2) = ∑ i, (Q.r i : ℤ)^2 := by
  have he' : P.schur = Q.schur := by
    simpa only [Gluing.Profile.toBetaDiagram_schur] using he
  have hr := (Gluing.Profile.rows_eq_of_schur_eq he').2
  have hs := congrArg (fun M : Multiset ℕ => (M.map (fun x : ℕ => (x : ℤ)^2)).sum) hr
  simpa only [Gluing.Profile.rowMultiset,Finset.sum,Multiset.map_map,Function.comp_def] using hs

/-- The same invariant on arbitrary connected beta diagrams, with the actual
normalizing translation eliminated before taking the row moment. -/
theorem row_squares_eq_of_schur_eq {n : ℕ} (D E : BetaDiagram (n+1))
    (hD : D.Connected) (hE : E.Connected) (he : D.schur = E.schur) :
    (∑ i, D.rowLength i^2) = ∑ i, E.rowLength i^2 := by
  have hp : (D.toProfile hD).toBetaDiagram.schur =
      (E.toProfile hE).toBetaDiagram.schur := by
    rw [Gluing.Profile.toBetaDiagram_schur,Gluing.Profile.toBetaDiagram_schur,
      D.toProfile_schur hD,E.toProfile_schur hE]
    exact he
  have hs := profile_row_squares_eq (D.toProfile hD) (E.toProfile hE) hp
  have hrD (i : Fin (n+1)) : ((D.toProfile hD).r i : ℤ) = D.rowLength i := by
    have h := (D.toProfile hD).xi_sub_zeta i
    rw [D.toProfile_xi hD,D.toProfile_zeta hD] at h
    dsimp [BetaDiagram.rowLength]
    dsimp only at h
    omega
  have hrE (i : Fin (n+1)) : ((E.toProfile hE).r i : ℤ) = E.rowLength i := by
    have h := (E.toProfile hE).xi_sub_zeta i
    rw [E.toProfile_xi hE,E.toProfile_zeta hE] at h
    dsimp [BetaDiagram.rowLength]
    dsimp only at h
    omega
  simpa only [hrD,hrE] using hs

private theorem top_row_squares {n : ℕ} (D : BetaDiagram (n+1))
    (t : ℤ) (ht : 0 < t) :
    (∑ i, (D.extendTop t ht).rowLength i^2) =
      (∑ i, D.rowLength i^2)+2*t*D.rowLength 0+t^2 := by
  have hi (i : Fin (n+1)) :
      (D.extendTop t ht).rowLength i^2 =
      D.rowLength i^2+if i = 0 then 2*t*D.rowLength 0+t^2 else 0 := by
    by_cases h : i = 0
    · subst i; simp [BetaDiagram.rowLength,BetaDiagram.extendTop]; ring
    · simp [BetaDiagram.rowLength,BetaDiagram.extendTop,h]
  rw [Finset.sum_congr rfl (fun i _ => hi i),Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

private theorem bottom_row_squares {n : ℕ} (D : BetaDiagram (n+1))
    (t : ℤ) (ht : 0 < t) :
    (∑ i, (D.extendBottom t ht).rowLength i^2) =
      (∑ i, D.rowLength i^2)+2*t*D.rowLength (Fin.last n)+t^2 := by
  have hi (i : Fin (n+1)) :
      (D.extendBottom t ht).rowLength i^2 =
      D.rowLength i^2+if i = Fin.last n then 2*t*D.rowLength (Fin.last n)+t^2 else 0 := by
    by_cases h : i = Fin.last n
    · subst i; simp [BetaDiagram.rowLength,BetaDiagram.extendBottom]; ring
    · simp [BetaDiagram.rowLength,BetaDiagram.extendBottom,h]
  rw [Finset.sum_congr rfl (fun i _ => hi i),Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

/-- Opposite endpoint comparisons of equal cores recover the shifted endpoint
length itself.  No ordering or row-distinctness premise is needed. -/
theorem opposite_endpoint_rows_eq {n : ℕ} (D E : BetaDiagram (n+1))
    (hD : D.Connected) (hE : E.Connected) (hcore : D.schur = E.schur)
    (t : ℤ) (ht : 0 < t)
    (he : (D.extendTop t ht).schur = (E.extendBottom t ht).schur) :
    D.rowLength 0 = E.rowLength (Fin.last n) := by
  have hbase := row_squares_eq_of_schur_eq D E hD hE hcore
  have hext := row_squares_eq_of_schur_eq (D.extendTop t ht) (E.extendBottom t ht)
    (D.extendTop_connected hD t ht) (E.extendBottom_connected hE t ht) he
  rw [top_row_squares,bottom_row_squares,hbase] at hext
  have hp : t*(D.rowLength 0-E.rowLength (Fin.last n)) = 0 := by nlinarith [hext]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (ne_of_gt ht))

/-- Reversing a core preserves the row moment of its tied positive border. -/
private theorem oriented_tied_border_row_squares (D : BetaDiagram 5) (rev : Bool)
    (q : ℤ) (hq : 0 < q) :
    (∑ i, ((if rev then D.rotate else D).positiveBorder q q hq hq).rowLength i^2) =
      ∑ i, (D.positiveBorder q q hq hq).rowLength i^2 := by
  cases rev
  · rfl
  · change (∑ i, (D.rotate.positiveBorder q q hq hq).rowLength i^2) =
        ∑ i, (D.positiveBorder q q hq hq).rowLength i^2
    have hrot : (D.rotate.positiveBorder q q hq hq).RotationEquivalent
        (D.positiveBorder q q hq hq) := by
      refine ⟨0,?_,?_⟩
      · intro i
        cases i using Fin.cases with
        | zero =>
          simp only [BetaDiagram.positiveBorder_row_zero,Fin.rev_zero,
            BetaDiagram.positiveBorder_col_last,BetaDiagram.rotate,Fin.rev_last]
          ring
        | succ i =>
          simp only [BetaDiagram.positiveBorder_row_succ,Fin.rev_succ,
            BetaDiagram.positiveBorder_col_castSucc,BetaDiagram.rotate]
          ring
      · intro i
        cases i using Fin.lastCases with
        | last =>
          simp only [BetaDiagram.positiveBorder_col_last,Fin.rev_last,
            BetaDiagram.positiveBorder_row_zero,BetaDiagram.rotate,Fin.rev_zero]
          ring
        | cast i =>
          simp only [BetaDiagram.positiveBorder_col_castSucc,Fin.rev_castSucc,
            BetaDiagram.positiveBorder_row_succ,BetaDiagram.rotate]
          ring
    obtain ⟨c,hr,hc⟩ := hrot
    have hi (i : Fin 6) :
        (D.rotate.positiveBorder q q hq hq).rowLength i =
          (D.positiveBorder q q hq hq).rowLength i.rev := by
      simp only [BetaDiagram.rowLength,hr i,hc i]
      ring
    calc
      _ = ∑ i : Fin 6, (D.positiveBorder q q hq hq).rowLength i.rev^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hi]
      _ = _ := by
        refine Finset.sum_bij (fun i _ => i.rev) (by simp) ?_ ?_ (by intros; rfl)
        · intro i _ j _ hij
          have h := congrArg Fin.rev hij
          simpa only [Fin.rev_rev] using h
        · intro i _
          exact ⟨i.rev,by simp,by simp⟩

/-- Parent row moments force the unique tied margin in either contact family,
independently of both core orientations. -/
theorem contact_tied_margin_forced (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m)
    (revF revH : Bool) (q : ℤ) (hq : 0 < q)
    (he :
      ((oriented (StaircaseFivePlacements.contactProfileF second p m z hz hp hm).toBetaDiagram revF).positiveBorder q q hq hq).schur =
      ((oriented (StaircaseFivePlacements.contactProfileH second p m z hz hp hm).toBetaDiagram revH).positiveBorder q q hq hq).schur) :
    q = m-z := by
  have hs := row_squares_eq_of_schur_eq
    ((oriented (StaircaseFivePlacements.contactProfileF second p m z hz hp hm).toBetaDiagram revF).positiveBorder q q hq hq)
    ((oriented (StaircaseFivePlacements.contactProfileH second p m z hz hp hm).toBetaDiagram revH).positiveBorder q q hq hq)
    (BetaDiagram.positiveBorder_connected _ _ _ _ _) (BetaDiagram.positiveBorder_connected _ _ _ _ _) he
  dsimp only [oriented] at hs
  rw [oriented_tied_border_row_squares,oriented_tied_border_row_squares] at hs
  cases second
  all_goals
    simp [BetaDiagram.positiveBorder,BetaDiagram.rowLength,
      Gluing.Profile.toBetaDiagram,Gluing.Profile.xi,Gluing.Profile.zeta,
      Fin.sum_univ_succ,Fin.snoc,StaircaseFivePlacements.contactProfileF,StaircaseFivePlacements.contactProfileH,
      StaircaseFiveFamilies.aParameters,StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m3H,
      StaircaseFiveFamilies.m4F,StaircaseFiveFamilies.m4H,StaircaseFiveFamilies.profile_row,
      StaircaseFiveFamilies.profile_gap] at hs
    ring_nf at hs
    have hprod2 : (2 : ℤ)*((p-z)*(q-(m-z))) = 0 := by
      linear_combination hs
    have hprod : (p-z)*(q-(m-z)) = 0 :=
      (mul_eq_zero.mp hprod2).resolve_left two_ne_zero
    have heq := (mul_eq_zero.mp hprod).resolve_left (by omega)
    exact sub_eq_zero.mp heq

/-- All tied positive borders over A1/A2 cross-orbits are separated, including
zero-gap children, arbitrary positive margins, and independent rotations. -/
theorem contact_tied_border_separation (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m)
    (revF revH : Bool) (q r : ℤ) (hq : 0 < q) (hr : 0 < r) :
    ((oriented (StaircaseFivePlacements.contactProfileF second p m z hz hp hm).toBetaDiagram revF).positiveBorder q q hq hq).schur ≠
    ((oriented (StaircaseFivePlacements.contactProfileH second p m z hz hp hm).toBetaDiagram revH).positiveBorder r r hr hr).schur := by
  let F := (StaircaseFivePlacements.contactProfileF second p m z hz hp hm).toBetaDiagram
  let H := (StaircaseFivePlacements.contactProfileH second p m z hz hp hm).toBetaDiagram
  have hF : F.Connected := Gluing.Profile.toBetaDiagram_connected _
  have hH : H.Connected := Gluing.Profile.toBetaDiagram_connected _
  have hcore : (oriented F revF).schur = (oriented H revH).schur := by
    rw [oriented_schur,oriented_schur]
    exact StaircaseFivePlacements.contact_profiles_schur_eq second p m z hz hp hm
  intro he
  obtain ⟨hqr,hsum⟩ := tied_border_endpoint_sum_eq
    (oriented F revF) (oriented H revH)
    (oriented_connected F hF revF) (oriented_connected H hH revH)
    hcore q r hq hr he
  subst r
  have hforced := contact_tied_margin_forced second p m z hz hp hm revF revH q hq he
  rw [oriented_endpoint_sum,oriented_endpoint_sum] at hsum
  apply StaircaseFivePlacements.contact_endpoint_sum_ne second p m z hz hp hm
  simpa only [hforced] using hsum

/-- The actual directed endpoint extension; true selects the bottom endpoint. -/
def endpointExtension {n : ℕ} (D : BetaDiagram (n+1)) (bottom : Bool)
    (t : ℤ) (ht : 0 < t) : BetaDiagram (n+1) :=
  if bottom then D.extendBottom t ht else D.extendTop t ht

def endpointRow {n : ℕ} (D : BetaDiagram (n+1)) (bottom : Bool) : ℤ :=
  if bottom then D.rowLength (Fin.last n) else D.rowLength 0

theorem endpointExtension_connected {n : ℕ} (D : BetaDiagram (n+1))
    (hD : D.Connected) (bottom : Bool) (t : ℤ) (ht : 0 < t) :
    (endpointExtension D bottom t ht).Connected := by
  cases bottom
  · exact D.extendTop_connected hD t ht
  · exact D.extendBottom_connected hD t ht

private theorem endpointExtension_squares {n : ℕ} (D : BetaDiagram (n+1))
    (bottom : Bool) (t : ℤ) (ht : 0 < t) :
    (∑ i, (endpointExtension D bottom t ht).rowLength i^2) =
      (∑ i, D.rowLength i^2)+2*t*endpointRow D bottom+t^2 := by
  cases bottom
  · exact top_row_squares D t ht
  · exact bottom_row_squares D t ht

/-- The full row reading separates endpoint extensions whenever their selected
original endpoint lengths differ, in any pair of directions. -/
theorem directed_endpoint_rows_eq {n : ℕ} (D E : BetaDiagram (n+1))
    (hD : D.Connected) (hE : E.Connected) (hcore : D.schur = E.schur)
    (bottomD bottomE : Bool) (t : ℤ) (ht : 0 < t)
    (he : (endpointExtension D bottomD t ht).schur =
      (endpointExtension E bottomE t ht).schur) :
    endpointRow D bottomD = endpointRow E bottomE := by
  have hbase := row_squares_eq_of_schur_eq D E hD hE hcore
  have hext := row_squares_eq_of_schur_eq
    (endpointExtension D bottomD t ht) (endpointExtension E bottomE t ht)
    (endpointExtension_connected D hD bottomD t ht)
    (endpointExtension_connected E hE bottomE t ht) he
  rw [endpointExtension_squares,endpointExtension_squares,hbase] at hext
  have hp : t*(endpointRow D bottomD-endpointRow E bottomE) = 0 := by nlinarith [hext]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (ne_of_gt ht))

/-- Rotating a core reverses the direction of an endpoint extension. -/
theorem oriented_endpointExtension (D : BetaDiagram 5) (rev bottom : Bool)
    (t : ℤ) (ht : 0 < t) :
    (endpointExtension (oriented D rev) bottom t ht).schur =
      (endpointExtension D (if rev then !bottom else bottom) t ht).schur := by
  have hR : D.rotate.RotationEquivalent D := by
    refine ⟨0,?_,?_⟩ <;> intro i <;> simp [BetaDiagram.rotate]
  have hR' : D.RotationEquivalent D.rotate := by
    refine ⟨0,?_,?_⟩ <;> intro i <;> simp [BetaDiagram.rotate]
  cases rev <;> cases bottom
  · rfl
  · rfl
  · exact D.rotate.extendTop_schur_eq_extendBottom_of_rotation D hR t ht
  · exact (D.extendTop_schur_eq_extendBottom_of_rotation D.rotate hR' t ht).symm

/-- Every directed endpoint cross-comparison of the two B rotation orbits
is unequal at every positive shift. -/
theorem b_endpoint_orbits_separated (p m z w : ℤ)
    (hz : 0 ≤ z) (hw : 0 ≤ w) (hp : z+w < p) (hm : z+w < m) (hne : p ≠ m)
    (revF revH bottomF bottomH : Bool) (t : ℤ) (ht : 0 < t) :
    (endpointExtension
      (oriented (StaircaseFivePlacements.bProfileF p m z w hz hw hp hm).toBetaDiagram revF)
      bottomF t ht).schur ≠
    (endpointExtension
      (oriented (StaircaseFivePlacements.bProfileH p m z w hz hw hp hm).toBetaDiagram revH)
      bottomH t ht).schur := by
  rw [oriented_endpointExtension,oriented_endpointExtension]
  let F := (StaircaseFivePlacements.bProfileF p m z w hz hw hp hm).toBetaDiagram
  let H := (StaircaseFivePlacements.bProfileH p m z w hz hw hp hm).toBetaDiagram
  have hF : F.Connected := Gluing.Profile.toBetaDiagram_connected _
  have hH : H.Connected := Gluing.Profile.toBetaDiagram_connected _
  have hcore : F.schur = H.schur :=
    StaircaseFivePlacements.b_profiles_schur_eq p m z w hz hw hp hm
  have hsame := StaircaseFivePlacements.b_same_endpoint_extensions_ne p m z w hz hw hp hm t ht
  generalize hflagF : (if revF then !bottomF else bottomF) = f
  generalize hflagH : (if revH then !bottomH else bottomH) = h
  cases f <;> cases h
  · exact hsame.1
  · intro he
    have hr := directed_endpoint_rows_eq F H hF hH hcore false true t ht he
    simp [F,H,endpointRow,StaircaseFiveFamilies.profile_rowLength,
      StaircaseFivePlacements.bProfileF,StaircaseFivePlacements.bProfileH,
      StaircaseFiveFamilies.profile_row] at hr
    exact hne hr
  · intro he
    have hr := directed_endpoint_rows_eq F H hF hH hcore true false t ht he
    simp [F,H,endpointRow,StaircaseFiveFamilies.profile_rowLength,
      StaircaseFivePlacements.bProfileF,StaircaseFivePlacements.bProfileH,
      StaircaseFiveFamilies.profile_row] at hr
    exact hne hr.symm
  · exact hsame.2

private theorem contact_endpointRowF (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m) (bottom : Bool) :
    endpointRow (StaircaseFivePlacements.contactProfileF second p m z hz hp hm).toBetaDiagram bottom =
      if bottom then m+p-z else p := by
  cases second <;> cases bottom <;>
    simp [endpointRow,StaircaseFiveFamilies.profile_rowLength,
      StaircaseFivePlacements.contactProfileF,StaircaseFiveFamilies.aParameters,
      StaircaseFiveFamilies.m3F,StaircaseFiveFamilies.m4F,StaircaseFiveFamilies.profile_row] <;> omega

private theorem contact_endpointRowH (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m) (bottom : Bool) :
    endpointRow (StaircaseFivePlacements.contactProfileH second p m z hz hp hm).toBetaDiagram bottom =
      if bottom then m else p := by
  cases second <;> cases bottom <;>
    simp [endpointRow,StaircaseFiveFamilies.profile_rowLength,
      StaircaseFivePlacements.contactProfileH,StaircaseFiveFamilies.aParameters,
      StaircaseFiveFamilies.m3H,StaircaseFiveFamilies.m4H,StaircaseFiveFamilies.profile_row] <;> omega

/-- Every directed endpoint cross-comparison of either contact family's
rotation orbits is unequal, with common betas permitted. -/
theorem contact_endpoint_orbits_separated (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m)
    (revF revH bottomF bottomH : Bool) (t : ℤ) (ht : 0 < t) :
    (endpointExtension
      (oriented (StaircaseFivePlacements.contactProfileF second p m z hz hp hm).toBetaDiagram revF)
      bottomF t ht).schur ≠
    (endpointExtension
      (oriented (StaircaseFivePlacements.contactProfileH second p m z hz hp hm).toBetaDiagram revH)
      bottomH t ht).schur := by
  rw [oriented_endpointExtension,oriented_endpointExtension]
  let F := (StaircaseFivePlacements.contactProfileF second p m z hz hp hm).toBetaDiagram
  let H := (StaircaseFivePlacements.contactProfileH second p m z hz hp hm).toBetaDiagram
  have hF : F.Connected := Gluing.Profile.toBetaDiagram_connected _
  have hH : H.Connected := Gluing.Profile.toBetaDiagram_connected _
  have hcore : F.schur = H.schur :=
    StaircaseFivePlacements.contact_profiles_schur_eq second p m z hz hp hm
  generalize hflagF : (if revF then !bottomF else bottomF) = f
  generalize hflagH : (if revH then !bottomH else bottomH) = h
  cases f <;> cases h
  · exact StaircaseFivePlacements.contact_top_extensions_ne second p m z t hz hp hm ht
  · intro he
    have hr := directed_endpoint_rows_eq F H hF hH hcore false true t ht he
    rw [contact_endpointRowF,contact_endpointRowH] at hr
    simp only [Bool.false_eq_true,ite_false,ite_true] at hr
    omega
  · intro he
    have hr := directed_endpoint_rows_eq F H hF hH hcore true false t ht he
    rw [contact_endpointRowF,contact_endpointRowH] at hr
    simp only [Bool.false_eq_true,ite_false,ite_true] at hr
    omega
  · intro he
    have hr := directed_endpoint_rows_eq F H hF hH hcore true true t ht he
    rw [contact_endpointRowF,contact_endpointRowH] at hr
    simp only [ite_true] at hr
    omega

/-- Two equal positive borders of equal connected children have the same
unordered margins.  Both largest and second markers are actual readings. -/
theorem equal_core_border_margins (D E : BetaDiagram 5)
    (hD : D.Connected) (hE : E.Connected) (hcore : D.schur = E.schur)
    (u v a b : ℤ) (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b)
    (he : (D.positiveBorder u v hu hv).schur =
      (E.positiveBorder a b ha hb).schur) :
    (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  have hspan := D.largestLabel_eq_of_schur_eq E hD hE hcore
  have hparent := (D.positiveBorder u v hu hv).largestLabel_eq_of_schur_eq
    (E.positiveBorder a b ha hb)
    (D.positiveBorder_connected u v hu hv) (E.positiveBorder_connected a b ha hb) he
  simp only [BetaDiagram.positiveBorder_largestLabel] at hparent
  have hsum : u+v = a+b := by omega
  have hmin := (D.positiveBorder u v hu hv).border_minMargin_eq_of_schur_eq
    (E.positiveBorder a b ha hb)
    (D.positiveBorder_connected u v hu hv) (E.positiveBorder_connected a b ha hb)
    (D.positiveBorder_positiveCorner u v hu hv) (E.positiveBorder_positiveCorner a b ha hb)
    (by simpa using hD) (by simpa using hE) he
  simp only [BetaDiagram.positiveBorder_topMargin,BetaDiagram.positiveBorder_bottomMargin] at hmin
  by_cases huv : u ≤ v
  · rw [min_eq_left huv] at hmin
    by_cases hab : a ≤ b
    · rw [min_eq_left hab] at hmin
      exact Or.inl ⟨hmin,by omega⟩
    · rw [min_eq_right (le_of_not_ge hab)] at hmin
      exact Or.inr ⟨hmin,by omega⟩
  · rw [min_eq_right (le_of_not_ge huv)] at hmin
    by_cases hab : a ≤ b
    · rw [min_eq_left hab] at hmin
      exact Or.inr ⟨by omega,hmin⟩
    · rw [min_eq_right (le_of_not_ge hab)] at hmin
      exact Or.inl ⟨by omega,hmin⟩

/-- At unequal margins equality of two actual positive borders forces a
directed endpoint equality at the common smaller margin.  No endpoint or
marker certificate is an input. -/
theorem unequal_border_endpoint_eq (D E : BetaDiagram 5)
    (hD : D.Connected) (hE : E.Connected) (hcore : D.schur = E.schur)
    (u v a b : ℤ) (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b)
    (hne : u ≠ v)
    (he : (D.positiveBorder u v hu hv).schur =
      (E.positiveBorder a b ha hb).schur) :
    ∃ bottomD bottomE : Bool,
      (endpointExtension D bottomD (min u v) (lt_min hu hv)).schur =
        (endpointExtension E bottomE (min u v) (lt_min hu hv)).schur := by
  let P := D.positiveBorder u v hu hv
  let R := E.positiveBorder a b ha hb
  have hpair := equal_core_border_margins D E hD hE hcore u v a b hu hv ha hb he
  have habne : a ≠ b := by
    intro hab
    rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hspan := D.largestLabel_eq_of_schur_eq E hD hE hcore
  have hNspan := P.largestLabel_eq_of_schur_eq R
    (D.positiveBorder_connected u v hu hv) (E.positiveBorder_connected a b ha hb) he
  have hsum : u+v = a+b := by
    simp only [P,R,BetaDiagram.positiveBorder_largestLabel] at hNspan
    omega
  have hmin : min u v = min a b := by
    rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [h1,h2]
    · rw [h1,h2,min_comm]
  have hMspan : P.secondLabel = R.secondLabel := by
    simp only [P,R,BetaDiagram.positiveBorder_secondLabel]
    omega
  have hN : P.borderLargestGenerator = R.borderLargestGenerator := by
    apply Subtype.ext
    change P.largestLabel.toNat = R.largestLabel.toNat
    rw [hNspan]
  have hM : P.borderSecondGenerator = R.borderSecondGenerator := by
    apply Subtype.ext
    change P.secondLabel.toNat = R.secondLabel.toNat
    rw [hMspan]
  have hread := congrArg
    (fun s : CompleteRing => MvPolynomial.pderiv P.borderSecondGenerator
      (eraseGenerator P.borderLargestGenerator s)) he
  rcases lt_or_gt_of_ne hne with huv | hvu
  · rw [D.positiveBorder_top_coefficient u v hu hv huv] at hread
    rw [hN,hM] at hread
    rcases lt_or_gt_of_ne habne with hab | hba
    · rw [E.positiveBorder_top_coefficient a b ha hb hab] at hread
      have hshift : a = u := by
        rw [min_eq_left huv.le,min_eq_left hab.le] at hmin
        exact hmin.symm
      subst a
      refine ⟨false,false,?_⟩
      simpa [endpointExtension,min_eq_left huv.le] using hread
    · rw [E.positiveBorder_bottom_coefficient a b ha hb hba] at hread
      have hshift : b = u := by
        rw [min_eq_left huv.le,min_eq_right hba.le] at hmin
        exact hmin.symm
      subst b
      refine ⟨false,true,?_⟩
      simpa [endpointExtension,min_eq_left huv.le] using hread
  · rw [D.positiveBorder_bottom_coefficient u v hu hv hvu] at hread
    rw [hN,hM] at hread
    rcases lt_or_gt_of_ne habne with hab | hba
    · rw [E.positiveBorder_top_coefficient a b ha hb hab] at hread
      have hshift : a = v := by
        rw [min_eq_right hvu.le,min_eq_left hab.le] at hmin
        exact hmin.symm
      subst a
      refine ⟨true,false,?_⟩
      simpa [endpointExtension,min_eq_right hvu.le] using hread
    · rw [E.positiveBorder_bottom_coefficient a b ha hb hba] at hread
      have hshift : b = v := by
        rw [min_eq_right hvu.le,min_eq_right hba.le] at hmin
        exact hmin.symm
      subst b
      refine ⟨true,true,?_⟩
      simpa [endpointExtension,min_eq_right hvu.le] using hread

/-- All positive borders over the two B rotation orbits are unequal, in
both strict margin orders and at every tied-margin transition. -/
theorem b_border_separation (p m z w : ℤ)
    (hz : 0 ≤ z) (hw : 0 ≤ w) (hp : z+w < p) (hm : z+w < m) (hne : p ≠ m)
    (revF revH : Bool) (u v a b : ℤ)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b) :
    ((oriented (StaircaseFivePlacements.bProfileF p m z w hz hw hp hm).toBetaDiagram revF).positiveBorder u v hu hv).schur ≠
    ((oriented (StaircaseFivePlacements.bProfileH p m z w hz hw hp hm).toBetaDiagram revH).positiveBorder a b ha hb).schur := by
  let F := (StaircaseFivePlacements.bProfileF p m z w hz hw hp hm).toBetaDiagram
  let H := (StaircaseFivePlacements.bProfileH p m z w hz hw hp hm).toBetaDiagram
  have hF : (oriented F revF).Connected := oriented_connected F (Gluing.Profile.toBetaDiagram_connected _) revF
  have hH : (oriented H revH).Connected := oriented_connected H (Gluing.Profile.toBetaDiagram_connected _) revH
  have hcore : (oriented F revF).schur = (oriented H revH).schur := by
    rw [oriented_schur,oriented_schur]
    exact StaircaseFivePlacements.b_profiles_schur_eq p m z w hz hw hp hm
  intro he
  by_cases htie : u = v
  · have hpair := equal_core_border_margins (oriented F revF) (oriented H revH)
      hF hH hcore u v a b hu hv ha hb he
    have ha' : a = u := by rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    have hb' : b = u := by rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    subst v
    subst a
    subst b
    exact b_tied_border_separation p m z w hz hw hp hm hne revF revH u u hu hu he
  · obtain ⟨bottomF,bottomH,hext⟩ := unequal_border_endpoint_eq
      (oriented F revF) (oriented H revH) hF hH hcore u v a b hu hv ha hb htie he
    exact b_endpoint_orbits_separated p m z w hz hw hp hm hne
      revF revH bottomF bottomH (min u v) (lt_min hu hv) hext

/-- Complete all-margin, all-orientation positive-border separation for both
contact families, with zero child gaps and common betas permitted. -/
theorem contact_border_separation (second : Bool) (p m z : ℤ)
    (hz : 0 ≤ z) (hp : z < p) (hm : p+z < m)
    (revF revH : Bool) (u v a b : ℤ)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b) :
    ((oriented (StaircaseFivePlacements.contactProfileF second p m z hz hp hm).toBetaDiagram revF).positiveBorder u v hu hv).schur ≠
    ((oriented (StaircaseFivePlacements.contactProfileH second p m z hz hp hm).toBetaDiagram revH).positiveBorder a b ha hb).schur := by
  let F := (StaircaseFivePlacements.contactProfileF second p m z hz hp hm).toBetaDiagram
  let H := (StaircaseFivePlacements.contactProfileH second p m z hz hp hm).toBetaDiagram
  have hF : (oriented F revF).Connected := oriented_connected F (Gluing.Profile.toBetaDiagram_connected _) revF
  have hH : (oriented H revH).Connected := oriented_connected H (Gluing.Profile.toBetaDiagram_connected _) revH
  have hcore : (oriented F revF).schur = (oriented H revH).schur := by
    rw [oriented_schur,oriented_schur]
    exact StaircaseFivePlacements.contact_profiles_schur_eq second p m z hz hp hm
  intro he
  by_cases htie : u = v
  · have hpair := equal_core_border_margins (oriented F revF) (oriented H revH)
      hF hH hcore u v a b hu hv ha hb he
    have ha' : a = u := by rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    have hb' : b = u := by rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    subst v
    subst a
    subst b
    exact contact_tied_border_separation second p m z hz hp hm revF revH u u hu hu he
  · obtain ⟨bottomF,bottomH,hext⟩ := unequal_border_endpoint_eq
      (oriented F revF) (oriented H revH) hF hH hcore u v a b hu hv ha hb htie he
    exact contact_endpoint_orbits_separated second p m z hz hp hm
      revF revH bottomF bottomH (min u v) (lt_min hu hv) hext

-- TODO-COPIED:
--   skew-jacobi-negative/lean/SkewJacobiNegative/TenExceptionalContexts.lean
private theorem translation_symm {n : ℕ} {D E : BetaDiagram n}
    (h : D.TranslationEquivalent E) : E.TranslationEquivalent D := by
  obtain ⟨c,hr,hc⟩ := h
  refine ⟨-c,?_,?_⟩ <;> intro i
  · have := hr i
    omega
  · have := hc i
    omega

-- TODO-COPIED:
--   skew-jacobi-negative/lean/SkewJacobiNegative/TenExceptionalContexts.lean
private theorem translation_trans {n : ℕ} {D E F : BetaDiagram n}
    (h : D.TranslationEquivalent E) (h' : E.TranslationEquivalent F) :
    D.TranslationEquivalent F := by
  obtain ⟨c,hr,hc⟩ := h
  obtain ⟨d,hr',hc'⟩ := h'
  refine ⟨c+d,?_,?_⟩ <;> intro i
  · have := hr i
    have := hr' i
    omega
  · have := hc i
    have := hc' i
    omega

/-- Normalization is a common translation of the complete full-order board. -/
theorem translation_to_profile {n : ℕ} (D : BetaDiagram (n+1)) (hD : D.Connected) :
    D.TranslationEquivalent (D.toProfile hD).toBetaDiagram := by
  refine ⟨D.col (Fin.last n),?_,?_⟩
  · intro i
    change D.row i = (D.toProfile hD).xi i+D.col (Fin.last n)
    rw [D.toProfile_xi hD]
    ring
  · intro i
    change D.col i = (D.toProfile hD).zeta i+D.col (Fin.last n)
    rw [D.toProfile_zeta hD]
    ring

/-- The complete five-row base theorem.  Gamma first removes every unit;
the actual M1--M4 parameter congruences then descend its classification.
Neither a gap placement nor a zero-free mate is assumed. -/
theorem staircase_base_profiles (D E : BetaDiagram 5)
    (hD : HasStaircase D) (hC : D.Connected) (hE : E.Connected) :
    D.schur = E.schur ↔
      D.toProfile hC = E.toProfile hE ∨
      D.toProfile hC = (E.toProfile hE).rotate ∨
      ∃ X : StaircaseFivePlacements.Scheme,
        X.Member (D.toProfile hC) ∧ X.Member (E.toProfile hE) := by
  constructor
  · intro he
    have hEM := (staircase_mate_closure hD he).2
    have hDG := five_gamma_thick D hD hC
    have hEG := five_gamma_thick E hEM hE
    have hγ := (D.gamma_schur_eq_iff_same_order E hC hE).mpr he
    have hpoly :
        (D.gamma.toProfile (D.gamma_connected_iff.mpr hC)).toBetaDiagram.schur =
        (E.gamma.toProfile (E.gamma_connected_iff.mpr hE)).toBetaDiagram.schur := by
      simpa only [Gluing.Profile.toBetaDiagram_schur,
        D.gamma.toProfile_schur (D.gamma_connected_iff.mpr hC),
        E.gamma.toProfile_schur (E.gamma_connected_iff.mpr hE)] using hγ
    have h := (StaircaseFivePlacements.thick_five_scheme_class _ _
      hDG.1 hEG.1 hDG.2).mp hpoly
    rw [D.gamma_toProfile hC,E.gamma_toProfile hE] at h
    rcases h with h | h | ⟨X,hDX,hEX⟩
    · exact Or.inl (Gluing.Profile.lift_injective _ h)
    · right; left
      rw [Gluing.Profile.lift_rotate] at h
      exact Gluing.Profile.lift_injective _ h
    · obtain ⟨Y,hY⟩ := X.ungamma_of_member (D.toProfile hC) hDX
      subst X
      exact Or.inr (Or.inr
        ⟨Y,StaircaseFivePlacements.Scheme.member_ungamma hDX,
          StaircaseFivePlacements.Scheme.member_ungamma hEX⟩)
  · rintro (h | h | ⟨X,hD',hE'⟩)
    · rw [← D.toProfile_schur hC,← E.toProfile_schur hE,h]
    · rw [← D.toProfile_schur hC,← E.toProfile_schur hE,h,
        Gluing.Profile.schur_rotate]
    · have he := StaircaseFivePlacements.Scheme.member_schur hD' hE'
      simpa only [Gluing.Profile.toBetaDiagram_schur,D.toProfile_schur hC,
        E.toProfile_schur hE] using he

/-- The arbitrary mate has five rows before its normalized profile is used.
The order proof is retained explicitly, not hidden in a five-row premise. -/
theorem staircase_base_arbitrary_mate {m : ℕ} (D : BetaDiagram 5) (E : BetaDiagram m)
    (hD : HasStaircase D) (hC : D.Connected) (hE : E.Connected)
    (he : D.schur = E.schur) :
    ∃ hm : m = 5,
      let E' := E.castOrder hm
      let hE' := (E.castOrder_connected hm).mpr hE
      D.toProfile hC = E'.toProfile hE' ∨
      D.toProfile hC = (E'.toProfile hE').rotate ∨
      ∃ X : StaircaseFivePlacements.Scheme,
        X.Member (D.toProfile hC) ∧ X.Member (E'.toProfile hE') := by
  have hm : 5 = m := D.row_count_of_schur_eq E he
  subst m
  refine ⟨rfl,?_⟩
  simpa only [BetaDiagram.castOrder] using (staircase_base_profiles D E hD hC hE).mp he

/-- Every thick actual profile has exactly the complete five-row staircase
mask, including all zero first-subdiagonal entries. -/
theorem thick_profile_staircase (P : Gluing.Profile 4) (hP : Staircase.Thick P) :
    HasStaircase P.toBetaDiagram := by
  refine ⟨by decide,?_⟩
  intro i j
  change P.xi i < P.zeta j ↔ j.val+2 ≤ i.val
  constructor
  · intro hn
    by_contra hfar
    by_cases hij : i ≤ j
    · have hz := P.zeta_strictAnti.antitone hij
      have hr := P.xi_sub_zeta i
      have hp := P.r_pos i
      omega
    · let k : Fin 4 := ⟨j.val,by have := i.isLt; omega⟩
      have hi : i = k.succ := by apply Fin.ext; dsimp [k]; omega
      have hj : j = k.castSucc := by apply Fin.ext; rfl
      rw [hi,hj] at hn
      have hg := P.xi_succ_sub_zeta_castSucc k
      omega
  · intro hfar
    have h := hP.hessenberg i j (by omega)
    omega

theorem scheme_at_thick (X : StaircaseFivePlacements.Scheme) (i : Fin 4) :
    Staircase.Thick (X.at i) := by
  cases X <;> fin_cases i
  all_goals dsimp [StaircaseFivePlacements.Scheme.at,
    StaircaseFivePlacements.Scheme.first,StaircaseFivePlacements.Scheme.second]
  all_goals
    first
      | exact StaircaseFiveFamilies.profile_thick _ _ _ _ _ _ _ _ _ _
      | exact StaircaseFivePlacements.thick_rotate
          (StaircaseFiveFamilies.profile_thick _ _ _ _ _ _ _ _ _ _)

theorem scheme_at_staircase (X : StaircaseFivePlacements.Scheme) (i : Fin 4) :
    HasStaircase (X.at i).toBetaDiagram :=
  thick_profile_staircase _ (scheme_at_thick X i)

/-- A displayed scheme is its complete Schur fibre, with common beta entries
allowed.  Any intersecting M1/M2 descriptions denote the same four profiles. -/
theorem staircase_scheme_complete (X : StaircaseFivePlacements.Scheme) (i : Fin 4)
    (Q : Gluing.Profile 4) :
    (X.at i).toBetaDiagram.schur = Q.toBetaDiagram.schur ↔ X.Member Q := by
  constructor
  · intro he
    let D := (X.at i).toBetaDiagram
    let E := Q.toBetaDiagram
    have hD := Gluing.Profile.toBetaDiagram_connected (X.at i)
    have hE := Gluing.Profile.toBetaDiagram_connected Q
    have h := (staircase_base_profiles D E (scheme_at_staircase X i) hD hE).mp he
    have hDP : D.toProfile hD = X.at i :=
      StaircaseFivePlacements.profile_eq_of_translation _ _
        (translation_symm (translation_to_profile D hD))
    have hEP : E.toProfile hE = Q :=
      StaircaseFivePlacements.profile_eq_of_translation _ _
        (translation_symm (translation_to_profile E hE))
    rw [hDP,hEP] at h
    rcases h with h | h | ⟨Y,hXY,hYQ⟩
    · exact ⟨i,h.symm⟩
    · have hQ : Q = (X.at i).rotate := by
        simpa using congrArg Gluing.Profile.rotate h.symm
      rw [hQ]
      exact StaircaseFivePlacements.Scheme.member_rotation ⟨i,rfl⟩
    · exact StaircaseFivePlacements.Scheme.same_members hXY ⟨i,rfl⟩ hYQ
  · intro hQ
    exact StaircaseFivePlacements.Scheme.member_schur ⟨i,rfl⟩ hQ

/-- The exact upper bound is four translation classes, attained by every
scheme on its full standing parameter domain. -/
theorem staircase_scheme_fiber_four (X : StaircaseFivePlacements.Scheme) (i : Fin 4) :
    ∃ f : Fin 4 → Gluing.Profile 4,
      Function.Injective f ∧
      ∀ Q, (X.at i).toBetaDiagram.schur = Q.toBetaDiagram.schur ↔ ∃ j, Q = f j :=
  ⟨X.at,X.at_injective,fun Q => staircase_scheme_complete X i Q⟩

/-- The complete padded row count is read directly from the six-site mask. -/
theorem staircase_negativeRowCount {n : ℕ} (D : BetaDiagram n)
    (hD : HasStaircase D) (i : Fin n) :
    negativeRowCount D i = i.val+4-n := by
  have hn := hD.1
  let t : Fin n := ⟨i.val+4-n,by have := i.isLt; omega⟩
  have hset : Finset.univ.filter (fun j => D.row i < D.col j) = Finset.Iio t := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
    rw [hD.2]
    change j.val+(n-3) ≤ i.val ↔ j.val < i.val+4-n
    omega
  change (Finset.univ.filter (fun j => D.row i < D.col j)).card = i.val+4-n
  rw [hset,Fin.card_Iio]

/-- Zero padding is discarded only after the actual row counts have been
recovered.  Every staircase has precisely the partition (3,2,1). -/
theorem staircase_negativePartition {n : ℕ} (D : BetaDiagram n)
    (hD : HasStaircase D) : negativePartition D = [3,2,1] := by
  apply NegativePartitionTools.ext_getD
    D.negativePartition_isPartition.2 (by simp)
  intro k
  rw [D.negativePartition_getD]
  split_ifs with hk
  · rw [staircase_negativeRowCount D hD]
    simp only [Fin.val_rev]
    by_cases h0 : k = 0
    · subst k; simp; have := hD.1; omega
    · by_cases h1 : k = 1
      · subst k; simp; have := hD.1; omega
      · by_cases h2 : k = 2
        · subst k; simp; have := hD.1; omega
        · rw [List.getD_eq_default _ _ (by simp; omega)]
          omega
  · rw [List.getD_eq_default _ _ (by have := hD.1; simp; omega)]

/-- The minimum is the least actual connected realization, not merely the
row count of a displayed family. -/
theorem staircase_minimum_realizing_rows {n : ℕ} (D : BetaDiagram n)
    (hD : HasStaircase D) :
    minimumRealizingRows (negativePartition D) = 5 ∧
      IsLeast {m : ℕ | NegativeRealizable (negativePartition D) m} 5 := by
  have hp : IsNegativePartition [3,2,1] := by unfold IsNegativePartition; decide
  have hmin : minimumRealizingRows [3,2,1] = 5 := by decide
  rw [staircase_negativePartition D hD]
  exact ⟨hmin,by simpa only [hmin] using minimumRealizingRows_isLeast [3,2,1] hp⟩

theorem scheme_count_and_minimum (X : StaircaseFivePlacements.Scheme) (i : Fin 4) :
    negativeCount (X.at i).toBetaDiagram = 6 ∧
      minimumRealizingRows (negativePartition (X.at i).toBetaDiagram) = 5 :=
  ⟨staircase_negativeCount (scheme_at_staircase X i),
    (staircase_minimum_realizing_rows _ (scheme_at_staircase X i)).1⟩

/-- Translating a core translates its positive border by the same amount. -/
theorem positiveBorder_translation {n : ℕ} (D E : BetaDiagram (n+1))
    (h : D.TranslationEquivalent E) (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).TranslationEquivalent (E.positiveBorder u v hu hv) := by
  obtain ⟨c,hr,hc⟩ := h
  refine ⟨c,?_,?_⟩
  · intro i
    cases i using Fin.cases with
    | zero => simp only [BetaDiagram.positiveBorder_row_zero]; rw [hr]; ring
    | succ i => simpa only [BetaDiagram.positiveBorder_row_succ] using hr i
  · intro i
    cases i using Fin.lastCases with
    | last => simp only [BetaDiagram.positiveBorder_col_last]; rw [hc]; ring
    | cast i => simpa only [BetaDiagram.positiveBorder_col_castSucc] using hc i

/-- The actual maximal cofactor and the two actual margins recover the whole
parent, without a normalized-border hypothesis. -/
theorem parent_translation_border {n : ℕ} (D : BetaDiagram (n+2))
    (hP : D.PositiveCorner) :
    D.TranslationEquivalent
      ((D.cornerDiagram hP).positiveBorder D.topMargin D.bottomMargin
        D.topMargin_pos D.bottomMargin_pos) := by
  refine ⟨0,?_,?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
      simp only [BetaDiagram.positiveBorder_row_zero,BetaDiagram.cornerDiagram,
        BetaDiagram.topMargin]
      ring
    | succ i => simp [BetaDiagram.positiveBorder_row_succ,BetaDiagram.cornerDiagram]
  · intro i
    cases i using Fin.lastCases with
    | last =>
      simp only [BetaDiagram.positiveBorder_col_last,BetaDiagram.cornerDiagram,
        BetaDiagram.bottomMargin]
      ring
    | cast i => simp [BetaDiagram.positiveBorder_col_castSucc,BetaDiagram.cornerDiagram]

theorem profile_rotate_translation {n : ℕ} (P : Gluing.Profile n) :
    P.rotate.toBetaDiagram.TranslationEquivalent P.toBetaDiagram.rotate := by
  refine ⟨P.xi 0,?_,?_⟩
  · intro i
    change P.rotate.xi i = -P.zeta i.rev+P.xi 0
    rw [Gluing.Profile.xi_rotate]
    ring
  · intro i
    change P.rotate.zeta i = -P.xi i.rev+P.xi 0
    rw [Gluing.Profile.zeta_rotate]
    ring

/-- Actual equal normalized profiles are precisely a common translation of
the original complete beta arrays. -/
theorem translation_of_toProfile_eq {n : ℕ} (D E : BetaDiagram (n+1))
    (hD : D.Connected) (hE : E.Connected) (he : D.toProfile hD = E.toProfile hE) :
    D.TranslationEquivalent E := by
  have h := translation_to_profile D hD
  rw [he] at h
  exact translation_trans h (translation_symm (translation_to_profile E hE))

theorem rotation_of_toProfile_eq_rotate {n : ℕ} (D E : BetaDiagram (n+1))
    (hD : D.Connected) (hE : E.Connected)
    (he : D.toProfile hD = (E.toProfile hE).rotate) : D.RotationEquivalent E := by
  refine ⟨E.row 0+D.col (Fin.last n),?_,?_⟩
  · intro i
    have h := congrArg (fun P : Gluing.Profile n => P.xi i) he
    rw [D.toProfile_xi hD,Gluing.Profile.xi_rotate,
      E.toProfile_xi hE,E.toProfile_zeta hE] at h
    dsimp only at h
    change D.row i = E.row 0+D.col (Fin.last n)-E.col i.rev
    omega
  · intro i
    have h := congrArg (fun P : Gluing.Profile n => P.zeta i) he
    rw [D.toProfile_zeta hD,Gluing.Profile.zeta_rotate,E.toProfile_xi hE] at h
    dsimp only at h
    change D.col i = E.row 0+D.col (Fin.last n)-E.row i.rev
    omega

-- TODO-COPIED:
--   skew-jacobi-negative/lean/SkewJacobiNegative/ConnectedBorderRigidity.lean
--   skew-cofactor-independence/lean/SkewCofactorIndependence/NonnegativeRigidity.lean
private theorem parent_motion_of_child_motion {n : ℕ}
    (D E : BetaDiagram (n+3)) (hD : D.Connected) (hE : E.Connected)
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (hCD : (D.cornerDiagram hPD).Connected) (hCE : (E.cornerDiagram hPE).Connected)
    (hCM : HasStaircase (D.cornerDiagram hPD))
    (hcore : (D.cornerDiagram hPD).TranslationEquivalent (E.cornerDiagram hPE) ∨
      (D.cornerDiagram hPD).RotationEquivalent (E.cornerDiagram hPE))
    (he : D.schur = E.schur) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  have hEnds : ∀ t ht,
      ((D.cornerDiagram hPD).extendTop t ht).schur =
        ((D.cornerDiagram hPD).extendBottom t ht).schur →
        (D.cornerDiagram hPD).Symmetric := by
    intro t ht hh
    exact (staircase_endpoint_isolation _ hCM hCD t ht).mp hh
  rcases hcore with htr | hrot
  · exact D.connected_border_aligned_rigidity E hD hE hPD hPE hCD hCE htr hEnds he
  · have hEr := E.rotate_connected hE
    have hEqr : D.schur = E.rotate.schur := he.trans E.rotate_schur.symm
    have hCr : (E.rotate.cornerDiagram (E.rotate_positiveCorner hPE)).Connected := by
      apply BetaDiagram.connected_of_schur_irreducible _ (by omega)
      rw [← (D.corner_translation_of_rotation E hPD hPE hrot).schur_eq]
      exact (D.cornerDiagram hPD).schur_irreducible hCD
    rcases D.connected_border_aligned_rigidity E.rotate hD hEr hPD
        (E.rotate_positiveCorner hPE) hCD hCr
        (D.corner_translation_of_rotation E hPD hPE hrot) hEnds hEqr with hh | hh
    · exact Or.inr ((D.translation_rotate_iff_rotation E).mp hh)
    · exact Or.inl ((D.rotation_rotate_iff_translation E).mp hh)

/-- The partition itself reconstructs the exact staircase mask at the
actual row count.  Connectedness supplies the sharp lower row bound. -/
theorem staircase_of_partition {n : ℕ} (D : BetaDiagram n) (hD : D.Connected)
    (hρ : negativePartition D = [3,2,1]) : HasStaircase D := by
  have hp : IsNegativePartition [3,2,1] := by unfold IsNegativePartition; decide
  have hmin : minimumRealizingRows [3,2,1] = 5 := by decide
  have hn : 5 ≤ n := by
    have h := (minimumRealizingRows_isLeast [3,2,1] hp).2
      (show NegativeRealizable [3,2,1] n from ⟨D,hD,hρ⟩)
    simpa only [hmin] using h
  refine ⟨hn,?_⟩
  intro i j
  have h := D.negativePartition_getD i.rev.val
  rw [hρ,dif_pos i.rev.isLt] at h
  have hidx : (Fin.rev ⟨i.rev.val,i.rev.isLt⟩ : Fin n) = i := by
    change i.rev.rev = i
    exact Fin.rev_rev i
  rw [hidx] at h
  have htable : ∀ k : ℕ, ([3,2,1] : List ℕ).getD k 0 = 3-k := by
    intro k
    by_cases h0 : k = 0
    · subst k; rfl
    · by_cases h1 : k = 1
      · subst k; rfl
      · by_cases h2 : k = 2
        · subst k; rfl
        · rw [List.getD_eq_default _ _ (by simp; omega)]
          omega
  rw [htable] at h
  have hc : negativeRowCount D i = i.val+4-n := by
    simp only [Fin.val_rev] at h
    have := i.isLt
    omega
  rw [D.negative_iff_lt_rowCount,hc]
  have := i.isLt
  omega

theorem staircase_iff_partition {n : ℕ} (D : BetaDiagram n) (hD : D.Connected) :
    HasStaircase D ↔ negativePartition D = [3,2,1] :=
  ⟨staircase_negativePartition D,staircase_of_partition D hD⟩

/-- Every connected five-row staircase fibre has at most four normalized
representatives.  In the absence of an M1--M4 member it is rotation-rigid. -/
theorem staircase_base_classification (D : BetaDiagram 5)
    (hD : HasStaircase D) (hC : D.Connected) :
    D.RotationRigid ∨
      ∃ X : StaircaseFivePlacements.Scheme, X.Member (D.toProfile hC) ∧
        ∀ Q : Gluing.Profile 4,
          D.schur = Q.toBetaDiagram.schur ↔ X.Member Q := by
  classical
  by_cases hx : ∃ X : StaircaseFivePlacements.Scheme, X.Member (D.toProfile hC)
  · obtain ⟨X,i,hi⟩ := hx
    right
    refine ⟨X,⟨i,hi⟩,?_⟩
    intro Q
    have hpoly : D.schur = (X.at i).toBetaDiagram.schur := by
      rw [← D.toProfile_schur hC,hi]
      exact (Gluing.Profile.toBetaDiagram_schur (X.at i)).symm
    rw [hpoly]
    exact staircase_scheme_complete X i Q
  · left
    rw [D.rotationRigid_iff_same_order]
    intro E hE he
    have h := (staircase_base_profiles D E hD hC hE).mp he.symm
    rcases h with h | h | ⟨X,hDX,_⟩
    · exact Or.inl (translation_of_toProfile_eq D E hC hE h)
    · exact Or.inr (rotation_of_toProfile_eq_rotate D E hC hE h)
    · exact False.elim (hx ⟨X,hDX⟩)

private theorem profile_orientation_translation {n : ℕ} (P : Gluing.Profile n) (rev : Bool) :
    (StaircaseFivePlacements.profileOrientation P rev).toBetaDiagram.TranslationEquivalent
      (if rev then P.toBetaDiagram.rotate else P.toBetaDiagram) := by
  cases rev
  · exact ⟨0,fun _ => by simp [StaircaseFivePlacements.profileOrientation],
      fun _ => by simp [StaircaseFivePlacements.profileOrientation]⟩
  · exact profile_rotate_translation P

/-- A parent's actual normalized corner may be replaced by a chosen
orientation only after transporting the complete beta arrays. -/
theorem parent_schur_eq_oriented_border {n : ℕ} (D : BetaDiagram (n+2))
    (hP : D.PositiveCorner) (hC : (D.cornerDiagram hP).Connected)
    (P : Gluing.Profile n) (rev : Bool)
    (hprofile : (D.cornerDiagram hP).toProfile hC =
      StaircaseFivePlacements.profileOrientation P rev) :
    D.schur =
      ((if rev then P.toBetaDiagram.rotate else P.toBetaDiagram).positiveBorder
        D.topMargin D.bottomMargin D.topMargin_pos D.bottomMargin_pos).schur := by
  have hnorm := translation_to_profile (D.cornerDiagram hP) hC
  rw [hprofile] at hnorm
  have hcore := translation_trans hnorm (profile_orientation_translation P rev)
  exact (translation_trans (parent_translation_border D hP)
    (positiveBorder_translation _ _ hcore D.topMargin D.bottomMargin
      D.topMargin_pos D.bottomMargin_pos)).schur_eq

private theorem scheme_same_side (X : StaircaseFivePlacements.Scheme) (i j : Fin 4)
    (hside : i.val/2 = j.val/2) :
    X.at i = X.at j ∨ X.at i = (X.at j).rotate := by
  fin_cases i <;> fin_cases j
  all_goals norm_num at hside
  all_goals simp [StaircaseFivePlacements.Scheme.at]

open StaircaseFivePlacements

/-- All M1--M4 border separations are the exact actual B/A1/A2 separations
under their row/gap dictionaries, with no restriction on tied margins. -/
theorem scheme_border_separation (X : Scheme)
    (revF revH : Bool) (u v a b : ℤ)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b) :
    ((oriented X.first.toBetaDiagram revF).positiveBorder u v hu hv).schur ≠
      ((oriented X.second.toBetaDiagram revH).positiveBorder a b ha hb).schur := by
  cases X with
  | m1 X =>
    have := X.t_nonneg; have := X.d_nonneg
    have := X.a_gt; have := X.b_gt
    have hne : X.a+X.d ≠ X.b+X.d := by intro h; exact X.a_ne_b (by omega)
    have hF : StaircaseFiveFamilies.m1F X =
        bProfileF (X.a+X.d) (X.b+X.d) (X.t+X.d) X.d
          (by omega) (by omega) (by omega) (by omega) := by
      apply Gluing.Profile.ext
      all_goals funext i; fin_cases i <;>
        simp [StaircaseFiveFamilies.m1F,bProfileF,StaircaseFiveFamilies.profile] <;> omega
    have hH : StaircaseFiveFamilies.m1H X =
        bProfileH (X.a+X.d) (X.b+X.d) (X.t+X.d) X.d
          (by omega) (by omega) (by omega) (by omega) := by
      apply Gluing.Profile.ext
      all_goals funext i; fin_cases i <;>
        simp [StaircaseFiveFamilies.m1H,bProfileH,StaircaseFiveFamilies.profile] <;> omega
    simpa only [Scheme.first,Scheme.second,hF,hH] using
      b_border_separation (X.a+X.d) (X.b+X.d) (X.t+X.d) X.d
        (by omega) (by omega) (by omega) (by omega) hne revF revH u v a b hu hv ha hb
  | m2 X =>
    have := X.t_nonneg; have := X.d_nonneg
    have := X.a_gt; have := X.b_gt
    have hne : X.a+X.d ≠ X.b+X.d := by intro h; exact X.a_ne_b (by omega)
    have hF : StaircaseFiveFamilies.m2F X =
        bProfileF (X.a+X.d) (X.b+X.d) X.d (X.t+X.d)
          (by omega) (by omega) (by omega) (by omega) := by
      apply Gluing.Profile.ext
      all_goals funext i; fin_cases i <;>
        simp [StaircaseFiveFamilies.m2F,bProfileF,StaircaseFiveFamilies.profile] <;> omega
    have hH : StaircaseFiveFamilies.m2H X =
        bProfileH (X.a+X.d) (X.b+X.d) X.d (X.t+X.d)
          (by omega) (by omega) (by omega) (by omega) := by
      apply Gluing.Profile.ext
      all_goals funext i; fin_cases i <;>
        simp [StaircaseFiveFamilies.m2H,bProfileH,StaircaseFiveFamilies.profile] <;> omega
    simpa only [Scheme.first,Scheme.second,hF,hH] using
      b_border_separation (X.a+X.d) (X.b+X.d) X.d (X.t+X.d)
        (by omega) (by omega) (by omega) (by omega) hne revF revH u v a b hu hv ha hb
  | m3 X =>
    have hz := X.d_nonneg; have hp := X.a_pos; have hm := X.b_gt
    have hX : StaircaseFiveFamilies.aParameters (X.a+X.d) (X.b+X.d) X.d
        hz (by omega) (by omega) = X := by
      apply StaircaseFiveFamilies.ContactParameters.ext <;>
        simp [StaircaseFiveFamilies.aParameters]
    simpa [Scheme.first,Scheme.second,contactProfileF,contactProfileH,hX] using
      contact_border_separation false (X.a+X.d) (X.b+X.d) X.d hz (by omega) (by omega)
        revF revH u v a b hu hv ha hb
  | m4 X =>
    have hz := X.d_nonneg; have hp := X.a_pos; have hm := X.b_gt
    have hX : StaircaseFiveFamilies.aParameters (X.a+X.d) (X.b+X.d) X.d
        hz (by omega) (by omega) = X := by
      apply StaircaseFiveFamilies.ContactParameters.ext <;>
        simp [StaircaseFiveFamilies.aParameters]
    simpa [Scheme.first,Scheme.second,contactProfileF,contactProfileH,hX] using
      contact_border_separation true (X.a+X.d) (X.b+X.d) X.d hz (by omega) (by omega)
        revF revH u v a b hu hv ha hb

private theorem scheme_parent_separation (D E : BetaDiagram 6)
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (hCD : (D.cornerDiagram hPD).Connected) (hCE : (E.cornerDiagram hPE).Connected)
    (X : Scheme) (revF revH : Bool)
    (hD : (D.cornerDiagram hPD).toProfile hCD = profileOrientation X.first revF)
    (hE : (E.cornerDiagram hPE).toProfile hCE = profileOrientation X.second revH) :
    D.schur ≠ E.schur := by
  rw [parent_schur_eq_oriented_border D hPD hCD X.first revF hD,
    parent_schur_eq_oriented_border E hPE hCE X.second revH hE]
  exact scheme_border_separation X revF revH
    D.topMargin D.bottomMargin E.topMargin E.bottomMargin
    D.topMargin_pos D.bottomMargin_pos E.topMargin_pos E.bottomMargin_pos

/-- Six-row parents cannot lie above opposite rotation orbits of any
five-row scheme.  Both independent child orientations are retained. -/
theorem six_row_cross_orbits_impossible (D E : BetaDiagram 6)
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (hCD : (D.cornerDiagram hPD).Connected) (hCE : (E.cornerDiagram hPE).Connected)
    (X : Scheme) (i j : Fin 4)
    (hD : (D.cornerDiagram hPD).toProfile hCD = X.at i)
    (hE : (E.cornerDiagram hPE).toProfile hCE = X.at j)
    (hcross : i.val/2 ≠ j.val/2) : D.schur ≠ E.schur := by
  fin_cases i <;> fin_cases j
  all_goals norm_num at hcross
  all_goals simp only [Scheme.at,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three] at hD hE
  all_goals first
    | exact scheme_parent_separation D E hPD hPE hCD hCE X false false hD hE
    | exact scheme_parent_separation D E hPD hPE hCD hCE X false true hD hE
    | exact scheme_parent_separation D E hPD hPE hCD hCE X true false hD hE
    | exact scheme_parent_separation D E hPD hPE hCD hCE X true true hD hE
    | exact Ne.symm (scheme_parent_separation E D hPE hPD hCE hCD X false false hE hD)
    | exact Ne.symm (scheme_parent_separation E D hPE hPD hCE hCD X false true hE hD)
    | exact Ne.symm (scheme_parent_separation E D hPE hPD hCE hCD X true false hE hD)
    | exact Ne.symm (scheme_parent_separation E D hPE hPD hCE hCD X true true hE hD)

/-- The six-row boundary uses the complete five-row class theorem and the
actual all-margin border separation, not a rigid-child assumption. -/
theorem zeroFree_six_row_rigidity (D : BetaDiagram 6)
    (hD : HasStaircase D) (hC : D.Connected) (hZ : D.ZeroFree) : D.RotationRigid := by
  rw [D.rotationRigid_iff_same_order]
  intro E hE he
  let hPD := D.positiveCorner_of_connected_zeroFree hC hZ
  let hPE := D.positiveCorner_of_cornerPolynomial_eq E hC hE hPD
    (D.cornerPolynomial_eq_of_schur_eq E hC hE he.symm)
  have hCD : (D.cornerDiagram hPD).Connected := staircase_corner_connected D hD (by omega) hPD
  have hCE : (E.cornerDiagram hPE).Connected :=
    D.connected_corner_of_corner_eq E hC hE hPD hCD he.symm
  have hCM := staircase_corner D hD (by omega) hPD
  have hcore : (D.cornerDiagram hPD).schur = (E.cornerDiagram hPE).schur :=
    D.cornerPolynomial_eq_of_schur_eq E hC hE he.symm
  have h := (staircase_base_profiles _ _ hCM hCD hCE).mp hcore
  rcases h with h | h | ⟨X,⟨i,hi⟩,⟨j,hj⟩⟩
  · exact parent_motion_of_child_motion D E hC hE hPD hPE hCD hCE hCM
      (Or.inl (translation_of_toProfile_eq _ _ hCD hCE h)) he.symm
  · exact parent_motion_of_child_motion D E hC hE hPD hPE hCD hCE hCM
      (Or.inr (rotation_of_toProfile_eq_rotate _ _ hCD hCE h)) he.symm
  · by_cases hside : i.val/2 = j.val/2
    · have hprofiles := scheme_same_side X i j hside
      rcases hprofiles with h | h
      · have hcEq : (D.cornerDiagram hPD).toProfile hCD =
            (E.cornerDiagram hPE).toProfile hCE := hi.trans (h.trans hj.symm)
        exact parent_motion_of_child_motion D E hC hE hPD hPE hCD hCE hCM
          (Or.inl (translation_of_toProfile_eq _ _ hCD hCE hcEq)) he.symm
      · have hcRot : (D.cornerDiagram hPD).toProfile hCD =
            ((E.cornerDiagram hPE).toProfile hCE).rotate :=
          hi.trans (h.trans (congrArg Gluing.Profile.rotate hj.symm))
        exact parent_motion_of_child_motion D E hC hE hPD hPE hCD hCE hCM
          (Or.inr (rotation_of_toProfile_eq_rotate _ _ hCD hCE hcRot)) he.symm
    · exact False.elim (six_row_cross_orbits_impossible D E hPD hPE hCD hCE
        X i j hi hj hside he.symm)

/-- Above the six-row boundary, the connected staircase cofactor is rigid
by induction, while endpoint isolation holds independently at every order. -/
theorem zeroFree_higher_row_rigidity :
    ∀ (n : ℕ) (D : BetaDiagram (n+6)), HasStaircase D → D.Connected →
      D.ZeroFree → D.RotationRigid := by
  intro n
  induction n with
  | zero => exact zeroFree_six_row_rigidity
  | succ n ih =>
    intro D hD hC hZ
    let hP := D.positiveCorner_of_connected_zeroFree hC hZ
    have hCM := staircase_corner D hD (by omega) hP
    have hCC := staircase_corner_connected D hD (by omega) hP
    have hCZ : (D.cornerDiagram hP).ZeroFree := by
      intro i j
      exact hZ i.succ j.castSucc
    have hCore := ih (D.cornerDiagram hP) hCM hCC hCZ
    apply D.connected_border_endpoint_isolation hC hP hCC hCore
    intro t ht he
    exact (staircase_endpoint_isolation _ hCM hCC t ht).mp he

/-- `thm:staircase-higher`: every staircase of at least six rows is rigid
against connected mates of arbitrary order, including every common-beta
boundary.  Gamma removes units and then descends the full conclusion. -/
theorem staircase_higher_rows (n : ℕ) (D : BetaDiagram (n+6))
    (hD : HasStaircase D) (hC : D.Connected) : D.RotationRigid := by
  apply D.gamma_rigidity_descends hC
  exact zeroFree_higher_row_rigidity n D.gamma ((staircase_gamma_iff D).mpr hD)
    (D.gamma_connected_iff.mpr hC) D.gamma_zeroFree

/-- The partition formulation supplies the mask and covers every actual
six-negative staircase board, not only displayed positive-gap families. -/
theorem partition_higher_rows {n : ℕ} (D : BetaDiagram n)
    (hn : 6 ≤ n) (hD : D.Connected) (hρ : negativePartition D = [3,2,1]) :
    D.RotationRigid := by
  obtain ⟨k,hk⟩ : ∃ k : ℕ, n = k+6 := ⟨n-6,by omega⟩
  subst n
  exact staircase_higher_rows k D (staircase_of_partition D hD hρ) hD

theorem staircase_higher_full_mate {n m : ℕ} (D : BetaDiagram n) (E : BetaDiagram m)
    (hn : 6 ≤ n) (hD : D.Connected) (hρ : negativePartition D = [3,2,1])
    (he : E.schur = D.schur) : D.MotionEquivalent E :=
  (partition_higher_rows D hn hD hρ).full_mate hD E he

/-- Partition-level closure against a full-board mate of arbitrary order
uses the actual all-order overlap reconstruction of the staircase mask. -/
theorem staircase_partition_mate_closure {n m : ℕ}
    (D : BetaDiagram n) (E : BetaDiagram m)
    (hD : D.Connected) (hρ : negativePartition D = [3,2,1])
    (he : D.schur = E.schur) :
    n = m ∧ HasStaircase E ∧ negativePartition E = [3,2,1] := by
  have hM := staircase_of_partition D hD hρ
  obtain ⟨hn,hE⟩ := staircase_mate_closure hM he
  exact ⟨hn,hE,staircase_negativePartition E hE⟩

/-- Complete base classification stated directly for the negative
partition.  No preassigned staircase mask is an additional hypothesis. -/
theorem staircase_partition_base (D : BetaDiagram 5) (hD : D.Connected)
    (hρ : negativePartition D = [3,2,1]) :
    D.RotationRigid ∨
      ∃ X : Scheme, X.Member (D.toProfile hD) ∧
        ∀ Q : Gluing.Profile 4,
          D.schur = Q.toBetaDiagram.schur ↔ X.Member Q :=
  staircase_base_classification D (staircase_of_partition D hD hρ) hD

/-- Every base fibre has a four-element covering of its actual normalized
representatives, with no assumption that the source is exceptional. -/
theorem staircase_base_four_upper_bound (D : BetaDiagram 5)
    (hD : HasStaircase D) (hC : D.Connected) :
    ∃ f : Fin 4 → Gluing.Profile 4, ∀ Q : Gluing.Profile 4,
      D.schur = Q.toBetaDiagram.schur → ∃ i, Q = f i := by
  classical
  rcases staircase_base_classification D hD hC with hRigid | ⟨X,hDX,hX⟩
  · let P := D.toProfile hC
    refine ⟨![P,P.rotate,P,P.rotate],?_⟩
    intro Q he
    have hQ := Gluing.Profile.toBetaDiagram_connected Q
    have hmotion := (D.rotationRigid_iff_same_order).mp hRigid Q.toBetaDiagram hQ he.symm
    rcases hmotion with htr | hrot
    · have hp : P = Q := profile_eq_of_translation _ _
        (translation_trans (translation_symm (translation_to_profile D hC)) htr)
      exact ⟨0,hp.symm⟩
    · have hpRot : P.toBetaDiagram.RotationEquivalent Q.toBetaDiagram := by
        obtain ⟨c,hr,hc⟩ := translation_symm (translation_to_profile D hC)
        obtain ⟨d,hr',hc'⟩ := hrot
        refine ⟨c+d,?_,?_⟩ <;> intro i
        · have h1 := hr i
          have h2 := hr' i
          dsimp only [P] at h1 h2 ⊢
          omega
        · have h1 := hc i
          have h2 := hc' i
          dsimp only [P] at h1 h2 ⊢
          omega
      have hp : P = Q.rotate := profile_eq_rotate_of_rotation _ _ hpRot
      refine ⟨1,?_⟩
      simpa using congrArg Gluing.Profile.rotate hp.symm
  · refine ⟨X.at,?_⟩
    intro Q he
    exact (hX Q).mp he

end SkewJacobiNegative.StaircaseHigherRows
