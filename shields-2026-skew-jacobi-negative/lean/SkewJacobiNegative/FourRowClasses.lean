/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FourRowHessenberg
import SkewJacobiNegative.NegativeBudgetInventory
import SkewJacobiNegative.LowNegativeRigidity

/-!
# Four-row cofactor inventories

The three-singleton case of `prop:four-rows` and `app:four` in
`shields-2026-skew-jacobi-negative.tex`.  An arbitrary mate's Hessenberg
property is produced from its actual maximal-cofactor factor inventory.
The affine passage retains common betas and all four rows.
-/

namespace SkewJacobiNegative
namespace BetaDiagram

/-- A connected four-row board can have negatives only at the three sites
strictly below its first subdiagonal. -/
theorem four_negative_sites_subset (D : BetaDiagram 4) (hD : D.Connected) :
    negativeSites D ⊆ ({(2, 0), (3, 0), (3, 1)} : Finset (Fin 4 × Fin 4)) := by
  intro p hp
  have h := D.negative_lt_predecessor hD ((D.mem_negativeSites p.1 p.2).mp hp)
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp_all

/-- Saturating the connected four-row bound forces the actual Hessenberg board. -/
theorem four_hessenberg_of_negative_count (D : BetaDiagram 4) (hD : D.Connected)
    (hcount : 3 ≤ negativeCount D) :
    HessenbergExpansion.IntrinsicHessenberg D.row D.col := by
  classical
  have hs := D.four_negative_sites_subset hD
  have hcard : ({(2, 0), (3, 0), (3, 1)} : Finset (Fin 4 × Fin 4)).card ≤
      (negativeSites D).card := by
    simpa [negativeCount] using hcount
  have he := Finset.eq_of_subset_of_card_le hs hcard
  intro i j hij
  have hm : (i, j) ∈ negativeSites D := by
    rw [he]
    fin_cases i <;> fin_cases j <;> simp_all
  exact sub_neg.mpr ((D.mem_negativeSites i j).mp hm)

/-- In the Hessenberg case the three genuine diagonal singleton functions
multiply to the full maximal cofactor, without prescribed mate components. -/
theorem four_hessenberg_corner_product (D : BetaDiagram 4) (hP : D.PositiveCorner)
    (hH : HessenbergExpansion.IntrinsicHessenberg D.row D.col) :
    (D.cornerDiagram hP).schur =
      complete ((D.cornerDiagram hP).rowLength 0) *
      complete ((D.cornerDiagram hP).rowLength 1) *
      complete ((D.cornerDiagram hP).rowLength 2) := by
  let C := D.cornerDiagram hP
  have h10 : C.matrix 1 0 = 0 := by
    change complete (D.row 2 - D.col 0) = 0
    exact complete_of_neg (hH 2 0 (by decide))
  have h20 : C.matrix 2 0 = 0 := by
    change complete (D.row 3 - D.col 0) = 0
    exact complete_of_neg (hH 3 0 (by decide))
  have h21 : C.matrix 2 1 = 0 := by
    change complete (D.row 3 - D.col 1) = 0
    exact complete_of_neg (hH 3 1 (by decide))
  change C.matrix.det = _
  rw [Matrix.det_fin_three]
  simp only [h10, h20, h21, mul_zero, zero_mul, sub_zero, add_zero]
  rfl

/-- Unique factorization recovers three actual singleton leaves on any equal
mate.  Its Hessenberg pattern is a conclusion, never an input. -/
theorem four_hessenberg_mate_zeroFree (D E : BetaDiagram 4)
    (hD : D.Connected) (hE : E.Connected) (hZ : D.ZeroFree)
    (hH : HessenbergExpansion.IntrinsicHessenberg D.row D.col)
    (he : D.schur = E.schur) :
    HessenbergExpansion.IntrinsicHessenberg E.row E.col := by
  classical
  let hPD := D.positiveCorner_of_connected_zeroFree hD hZ
  let hPE := D.positiveCorner_of_cornerPolynomial_eq E hD hE hPD
    (D.cornerPolynomial_eq_of_schur_eq E hD hE he)
  let C := D.cornerDiagram hPD
  let T := E.cornerDiagram hPE
  let L : List (Σ k : ℕ, BetaDiagram k) :=
    [⟨1, singletonDiagram (C.rowLength 0) (C.rowLength_pos 0)⟩,
     ⟨1, singletonDiagram (C.rowLength 1) (C.rowLength_pos 1)⟩,
     ⟨1, singletonDiagram (C.rowLength 2) (C.rowLength_pos 2)⟩]
  let K := T.componentDecomposition
  have hL : ∀ X ∈ L, X.2.Connected := by
    intro X hX
    simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl <;> exact singletonDiagram_connected _ _
  have hp : (L.map (fun X => X.2.schur)).prod = T.schur := by
    calc
      _ = complete (C.rowLength 0) * (complete (C.rowLength 1) *
          complete (C.rowLength 2)) := by
        simp only [L, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          singletonDiagram_schur, mul_one]
      _ = C.schur := by
        simpa only [mul_assoc] using (D.four_hessenberg_corner_product hPD hH).symm
      _ = T.schur := D.cornerPolynomial_eq_of_schur_eq E hD hE he
  have hrel := T.component_matching_of_product K L hL hp
  have hlen : K.components.length = 3 := by
    have hh := Multiset.card_eq_card_of_rel hrel
    simpa only [L, Multiset.coe_card, List.length_cons, List.length_nil] using hh.symm
  have hcross := ComponentOrderInventory.three_component_bound
    (K.components.map Sigma.fst) K.orders_positive
    (by simp only [List.length_map, hlen]; omega)
  rw [K.component_rows_sum] at hcross
  have hb := K.negative_budget
  have hc : 3 ≤ negativeCount E := by
    rw [← E.corner_negativeCount hPE]
    change 3 ≤ negativeCount T
    omega
  exact E.four_hessenberg_of_negative_count hE hc

/-- The same inventory argument handles arbitrary common betas by faithful
Gamma transport, not by treating a zero entry as a negative one. -/
theorem four_hessenberg_mate (D E : BetaDiagram 4)
    (hD : D.Connected) (hE : E.Connected)
    (hH : HessenbergExpansion.IntrinsicHessenberg D.row D.col)
    (he : D.schur = E.schur) :
    HessenbergExpansion.IntrinsicHessenberg E.row E.col := by
  have hGH : HessenbergExpansion.IntrinsicHessenberg D.gamma.row D.gamma.col := by
    intro i j hij
    exact sub_neg.mpr ((D.gamma_negative_iff i j).mpr (sub_neg.mp (hH i j hij)))
  have hh := D.gamma.four_hessenberg_mate_zeroFree E.gamma
    ((D.gamma_connected_iff).mpr hD) ((E.gamma_connected_iff).mpr hE)
    D.gamma_zeroFree hGH ((D.gamma_schur_eq_iff_same_order E hD hE).mpr he)
  intro i j hij
  exact sub_neg.mpr ((E.gamma_negative_iff i j).mp (sub_neg.mp (hh i j hij)))

/-- The normalized natural profile retains the intrinsic board condition. -/
theorem toProfile_hessenberg_iff (D : BetaDiagram 4) (hD : D.Connected) :
    (D.toProfile hD).Hessenberg ↔
      HessenbergExpansion.IntrinsicHessenberg D.row D.col := by
  unfold Gluing.Profile.Hessenberg HessenbergExpansion.IntrinsicHessenberg
  simp only [D.toProfile_xi hD, D.toProfile_zeta hD]
  constructor <;> intro h i j hij <;> have hh := h i j hij <;> omega

/-- Complete F/H classification in the Hessenberg source case against an
arbitrary connected four-row mate, including common units. -/
theorem four_hessenberg_full_class_same_order (D E : BetaDiagram 4)
    (hD : D.Connected) (hE : E.Connected)
    (hH : HessenbergExpansion.IntrinsicHessenberg D.row D.col)
    (he : D.schur = E.schur) :
    FourRowHessenberg.Classified (D.toProfile hD) (E.toProfile hE) := by
  apply FourRowHessenberg.hessenberg_classification
  · exact (D.toProfile_hessenberg_iff hD).mpr hH
  · exact (E.toProfile_hessenberg_iff hE).mpr (D.four_hessenberg_mate E hD hE hH he)
  · simpa only [toProfile_schur] using he

/-- Both connectedness and the four-row order of a completely unrestricted
full-board mate are produced before applying the F/H classification. -/
theorem four_hessenberg_full_class (D : BetaDiagram 4) (hD : D.Connected)
    (hH : HessenbergExpansion.IntrinsicHessenberg D.row D.col)
    {m : ℕ} (E : BetaDiagram m) (he : E.schur = D.schur) :
    ∃ hrow : m = 4, ∃ hE : (E.castOrder hrow).Connected,
      FourRowHessenberg.Classified (D.toProfile hD) ((E.castOrder hrow).toProfile hE) := by
  have hrow : m = 4 := E.row_count_of_schur_eq D he
  have hE := D.connected_full_mate_of_schur_eq E hD he.symm
  refine ⟨hrow, (E.castOrder_connected hrow).mpr hE, ?_⟩
  apply D.four_hessenberg_full_class_same_order _ hD _ hH
  simpa only [castOrder_schur] using he.symm

/-- The connected-cofactor case of four-row rigidity is independently complete. -/
theorem four_connected_corner_rigidity (D : BetaDiagram 4) (hD : D.Connected)
    (hP : D.PositiveCorner) (hC : (D.cornerDiagram hP).Connected) :
    D.RotationRigid := by
  apply D.connected_border_rigidity hD hP hC
  · apply (rotationRigid_iff_same_order _).mpr
    intro E hE he
    exact (D.cornerDiagram hP).small_rows_rigidity_same_order E hC hE (by omega) he.symm
  · intro t ht
    apply (rotationRigid_iff_same_order _).mpr
    intro E hE he
    exact ((D.cornerDiagram hP).extendTop t ht).small_rows_rigidity_same_order E
      ((D.cornerDiagram hP).extendTop_connected hC t ht) hE (by omega) he.symm

end BetaDiagram
end SkewJacobiNegative

namespace SkewJacobiNegative.BetaDiagram
variable {n : ℕ}

/-- Actual translation transports rotation rigidity against every connected mate. -/
theorem rotationRigid_of_translation (D E : BetaDiagram n)
    (hT : D.TranslationEquivalent E) (hR : E.RotationRigid) : D.RotationRigid := by
  apply (rotationRigid_iff_same_order D).mpr
  intro F hF he
  have he' : F.schur = E.schur := he.trans hT.schur_eq
  rcases (rotationRigid_iff_same_order E).mp hR F hF he' with
    ⟨d, hr', hc'⟩ | ⟨d, hr', hc'⟩
  all_goals obtain ⟨c, hr, hc⟩ := hT
  · exact Or.inl ⟨c + d, fun i => by have := hr i; have := hr' i; omega,
      fun i => by have := hc i; have := hc' i; omega⟩
  · exact Or.inr ⟨c + d, fun i => by have := hr i; have := hr' i; omega,
      fun i => by have := hc i; have := hc' i; omega⟩

/-- Rigidity of the literal half-turn gives rigidity of the source. -/
theorem rotationRigid_of_rotate (D : BetaDiagram n) (hR : D.rotate.RotationRigid) :
    D.RotationRigid := by
  apply (rotationRigid_iff_same_order D).mpr
  intro E hE he
  rcases (rotationRigid_iff_same_order D.rotate).mp hR E hE
      (he.trans D.rotate_schur.symm) with ⟨c, hr, hc⟩ | ⟨c, hr, hc⟩
  · right
    refine ⟨-c, ?_, ?_⟩
    · intro i
      have hh := hc i.rev
      change -D.row i.rev.rev = E.col i.rev + c at hh
      simp only [Fin.rev_rev] at hh
      omega
    · intro i
      have hh := hr i.rev
      change -D.col i.rev.rev = E.row i.rev + c at hh
      simp only [Fin.rev_rev] at hh
      omega
  · left
    refine ⟨-c, ?_, ?_⟩
    · intro i
      have hh := hc i.rev
      change -D.row i.rev.rev = c - E.row i.rev.rev at hh
      simp only [Fin.rev_rev] at hh
      omega
    · intro i
      have hh := hr i.rev
      change -D.col i.rev.rev = c - E.col i.rev.rev at hh
      simp only [Fin.rev_rev] at hh
      omega

/-- The singleton-plus-dense-two-row branch of `app:four`, with its actual
singleton context produced from the source cut. -/
theorem four_first_cut_dense_rigidity (D : BetaDiagram 4)
    (hD : D.Connected) (hZ : D.ZeroFree)
    (hcut : D.row 2 < D.col 0) (hother : ¬ D.row 3 < D.col 1) :
    D.RotationRigid := by
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let Q := (D.cornerDiagram hP).tail
  have hbottom : D.col 1 < D.row 3 := by have := hZ 3 1; omega
  have hQ : Q.Dense := by
    intro i j
    change D.col j.succ.castSucc < D.row i.succ.succ
    have hr := D.row_strictAnti.antitone (Fin.le_last i.succ.succ)
    change D.row 3 ≤ D.row i.succ.succ at hr
    have hc := D.col_strictAnti.antitone
      (show (1 : Fin 4) ≤ j.succ.castSucc by change 1 ≤ j.val + 1; omega)
    omega
  obtain ⟨s, u, v, g, hs, hu, hv, hg, hT⟩ :=
    D.singleton_parent_of_first_cut hP hcut
  exact D.rotationRigid_of_translation _ hT
    (Q.singletonContext_rotationRigid_of_dense hQ s u v g hs hu hv hg)

/-- The actual four-row two-negative base, independent of any four-row
classification premise and of the later two-negative induction. -/
theorem four_two_negative_zeroFree_rigidity (D : BetaDiagram 4)
    (hD : D.Connected) (hZ : D.ZeroFree) (hcount : negativeCount D ≤ 2) :
    D.RotationRigid := by
  classical
  by_cases h0 : D.row 2 < D.col 0
  · have h1 : ¬ D.row 3 < D.col 1 := by
      intro h1
      have h30 := D.negative_southwest h0
        (show (2 : Fin 4) ≤ 3 by decide) (show (0 : Fin 4) ≤ 0 by rfl)
      have hs : ({(2, 0), (3, 0), (3, 1)} : Finset (Fin 4 × Fin 4)) ⊆ negativeSites D := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · exact (D.mem_negativeSites 2 0).mpr h0
        · exact (D.mem_negativeSites 3 0).mpr h30
        · exact (D.mem_negativeSites 3 1).mpr h1
      have hc := Finset.card_le_card hs
      have hn : 3 ≤ negativeCount D := by simpa [negativeCount] using hc
      omega
    exact D.four_first_cut_dense_rigidity hD hZ h0 h1
  · by_cases h1 : D.row 3 < D.col 1
    · apply D.rotationRigid_of_rotate
      have hZR : D.rotate.ZeroFree := by
        intro i j hh
        apply hZ j.rev i.rev
        change -D.col i.rev = -D.row j.rev at hh
        omega
      apply D.rotate.four_first_cut_dense_rigidity (D.rotate_connected hD) hZR
      · change -D.col 1 < -D.row 3
        omega
      · change ¬ -D.col 0 < -D.row 2
        omega
    · let hP := D.positiveCorner_of_connected_zeroFree hD hZ
      have hC : (D.cornerDiagram hP).Connected := by
        refine ⟨by omega, ?_⟩
        intro i hi
        fin_cases i
        · change D.col 0 ≤ D.row 2
          omega
        · change D.col 1 ≤ D.row 3
          omega
        · norm_num at hi
      exact D.four_connected_corner_rigidity hD hP hC

/-- The four-row two-negative base retains all common beta entries via Gamma. -/
theorem four_two_negative_rigidity (D : BetaDiagram 4) (hD : D.Connected)
    (hcount : negativeCount D ≤ 2) : D.RotationRigid := by
  apply D.gamma_rigidity_descends hD
  apply D.gamma.four_two_negative_zeroFree_rigidity
    ((D.gamma_connected_iff).mpr hD) D.gamma_zeroFree
  simpa only [gamma_negativeCount] using hcount

end SkewJacobiNegative.BetaDiagram

namespace SkewJacobiNegative.FourRowClasses
open Gluing FourRowHessenberg

/-- The complete four-member class, in the manuscript's displayed order. -/
def exceptionalQuartet (w b c : ℕ) (hcw : c < w) (hb : c + w < b) : List (Profile 3) :=
  [familyF w b c hcw hb, (familyF w b c hcw hb).rotate,
   familyH w b c hcw hb, (familyH w b c hcw hb).rotate]

/-- All four listed members are distinct for every allowed source parameter. -/
theorem exceptionalQuartet_nodup (w b c : ℕ) (hcw : c < w) (hb : c + w < b) :
    (exceptionalQuartet w b c hcw hb).Nodup :=
  family_four_distinct w b c hcw hb

/-- Each member, including both half-turns, has exactly three full-board negatives. -/
theorem exceptionalQuartet_negative_count (w b c : ℕ) (hcw : c < w)
    (hb : c + w < b) (P : Profile 3) (hP : P ∈ exceptionalQuartet w b c hcw hb) :
    negativeCount P.toBetaDiagram = 3 := by
  have hH : P.Hessenberg := by
    simp only [exceptionalQuartet, List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl
    · exact familyF_hessenberg w b c hcw hb
    · exact (familyF w b c hcw hb).hessenberg_rotate (familyF_hessenberg w b c hcw hb)
    · exact familyH_hessenberg w b c hcw hb
    · exact (familyH w b c hcw hb).hessenberg_rotate (familyH_hessenberg w b c hcw hb)
  exact negative_count_hessenberg P hH

/-- A classified mate of F belongs to its literal quartet with the same parameters;
the class calculation cannot silently change the exceptional parameter triple. -/
theorem classified_familyF_mem (w b c : ℕ) (hcw : c < w) (hb : c + w < b)
    (P : Profile 3) (hP : Classified (familyF w b c hcw hb) P) :
    P ∈ exceptionalQuartet w b c hcw hb := by
  rcases hP with hP | hP | ⟨W, B, C, hCW, hB, hcase⟩
  · simp only [exceptionalQuartet, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl hP.symm
  · have hh := congrArg Profile.rotate hP
    have hp : P = (familyF w b c hcw hb).rotate := by simpa using hh.symm
    simp only [exceptionalQuartet, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inl hp)
  · have he : (familyF w b c hcw hb).schur = (familyF W B C hCW hB).schur := by
      rcases hcase with ⟨hsource, _⟩ | ⟨hsource, _⟩
      · rcases hsource with h | h
        · exact congrArg Profile.schur h
        · exact (congrArg Profile.schur h).trans (Profile.schur_rotate _)
      · rcases hsource with h | h
        · exact (congrArg Profile.schur h).trans (family_schur_eq W B C hCW hB).symm
        · exact (congrArg Profile.schur h).trans
            ((Profile.schur_rotate _).trans (family_schur_eq W B C hCW hB).symm)
    obtain ⟨hw, hb', hc⟩ := family_parameters_recovered w b c W B C hcw hb hCW hB he
    subst W
    subst B
    subst C
    simp only [exceptionalQuartet, List.mem_cons, List.not_mem_nil, or_false]
    rcases hcase with ⟨_, htarget⟩ | ⟨_, htarget⟩
    · rcases htarget with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · rcases htarget with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

/-- Exact completeness of the exceptional class against every natural connected
profile; the mate is not assumed Hessenberg, zero-free or to have three negatives. -/
theorem familyF_schur_eq_iff_mem (w b c : ℕ) (hcw : c < w) (hb : c + w < b)
    (P : Profile 3) :
    (familyF w b c hcw hb).schur = P.schur ↔
      P ∈ exceptionalQuartet w b c hcw hb := by
  constructor
  · intro he
    have hH : P.Hessenberg := by
      have hh := (familyF w b c hcw hb).toBetaDiagram.four_hessenberg_mate
        P.toBetaDiagram (Profile.toBetaDiagram_connected _)
        (Profile.toBetaDiagram_connected P) (familyF_hessenberg w b c hcw hb)
        (by simpa only [Profile.toBetaDiagram_schur] using he)
      exact hh
    exact classified_familyF_mem w b c hcw hb P
      (hessenberg_classification _ P (familyF_hessenberg w b c hcw hb) hH he)
  · intro hP
    simp only [exceptionalQuartet, List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl
    · rfl
    · simp only [Profile.schur_rotate]
    · exact family_schur_eq w b c hcw hb
    · simpa only [Profile.schur_rotate] using family_schur_eq w b c hcw hb

/-- Exact quartet recovery from a full-board mate of any order and any component
inventory.  Both its row count and connectedness are conclusions. -/
theorem familyF_arbitrary_full_mate (w b c : ℕ) (hcw : c < w) (hb : c + w < b)
    {m : ℕ} (E : BetaDiagram m)
    (he : E.schur = (familyF w b c hcw hb).toBetaDiagram.schur) :
    ∃ hrow : m = 4, ∃ hE : (E.castOrder hrow).Connected,
      (E.castOrder hrow).toProfile hE ∈ exceptionalQuartet w b c hcw hb := by
  have hrow : m = 4 := E.row_count_of_schur_eq _ he
  have hE := (familyF w b c hcw hb).toBetaDiagram.connected_full_mate_of_schur_eq E
    (Profile.toBetaDiagram_connected _) he.symm
  refine ⟨hrow, (E.castOrder_connected hrow).mpr hE, ?_⟩
  apply (familyF_schur_eq_iff_mem w b c hcw hb _).mp
  simpa only [BetaDiagram.toProfile_schur, BetaDiagram.castOrder_schur,
    Profile.toBetaDiagram_schur] using he.symm

/-- Zero-freeness makes every natural adjacent-gap parameter strictly positive,
without imposing a stronger beta inequality before homogenization. -/
theorem profile_gap_pos_of_zeroFree {n : ℕ} (P : Profile n)
    (hZ : P.toBetaDiagram.ZeroFree) (j : Fin n) : 0 < P.g j := by
  have hz := hZ j.succ j.castSucc
  have hi := P.xi_succ_sub_zeta_castSucc j
  change P.xi j.succ ≠ P.zeta j.castSucc at hz
  omega

/-- A zero-free member of the actual exceptional quartet has c≥1.  This
produces the parameter domain required by `lem:four-border` from the source board. -/
theorem exceptional_c_pos_of_zeroFree (w b c : ℕ) (hcw : c < w)
    (hb : c + w < b) (P : Profile 3)
    (hP : P ∈ exceptionalQuartet w b c hcw hb) (hZ : P.toBetaDiagram.ZeroFree) :
    1 ≤ c := by
  have h0 := profile_gap_pos_of_zeroFree P hZ 0
  have h1 := profile_gap_pos_of_zeroFree P hZ 1
  simp only [exceptionalQuartet, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl <;>
    simp [familyF, familyH, Profile.rotate] at h0 h1 <;> omega

end SkewJacobiNegative.FourRowClasses

namespace SkewJacobiNegative.FourRowClasses
open Gluing FourRowHessenberg

/-- Motion of actual normalized beta boards is literal profile identity or reversal. -/
theorem profile_motion_of_beta_motion {n : ℕ} (P Q : Profile n)
    (h : P.toBetaDiagram.TranslationEquivalent Q.toBetaDiagram ∨
      P.toBetaDiagram.RotationEquivalent Q.toBetaDiagram) : P = Q ∨ P = Q.rotate := by
  rcases h with ⟨c, hr, hz⟩ | ⟨c, hr, hz⟩
  · have hc := hz (Fin.last n)
    change P.zeta (Fin.last n) = Q.zeta (Fin.last n) + c at hc
    rw [P.zeta_last, Q.zeta_last] at hc
    have hc0 : c = 0 := by omega
    left
    apply Profile.eq_of_beta_eq
    · funext i
      have hh := hr i
      change P.xi i = Q.xi i + c at hh
      omega
    · funext i
      have hh := hz i
      change P.zeta i = Q.zeta i + c at hh
      omega
  · have hc := hz (Fin.last n)
    change P.zeta (Fin.last n) = c - Q.xi (Fin.last n).rev at hc
    simp only [Profile.zeta_last, Fin.rev_last] at hc
    have hc0 : c = Q.xi 0 := by omega
    right
    apply Profile.eq_of_beta_eq
    · funext i
      rw [Profile.xi_rotate]
      have hh := hr i
      change P.xi i = c - Q.zeta i.rev at hh
      omega
    · funext i
      rw [Profile.zeta_rotate]
      have hh := hz i
      change P.zeta i = c - Q.xi i.rev at hh
      omega

/-- `prop:four-rows`: complete classification for all connected natural
four-row profiles, with no Hessenberg or zero-free premise on either side. -/
theorem four_rows_schur_eq_iff (P Q : Profile 3) :
    P.schur = Q.schur ↔ Classified P Q := by
  constructor
  · intro he
    by_cases hP : P.Hessenberg
    · have hQ : Q.Hessenberg := by
        exact P.toBetaDiagram.four_hessenberg_mate Q.toBetaDiagram
          (Profile.toBetaDiagram_connected _) (Profile.toBetaDiagram_connected _) hP
          (by simpa only [Profile.toBetaDiagram_schur] using he)
      exact hessenberg_classification P Q hP hQ he
    · have hcount : negativeCount P.toBetaDiagram ≤ 2 := by
        by_contra hh
        apply hP
        exact P.toBetaDiagram.four_hessenberg_of_negative_count
          (Profile.toBetaDiagram_connected _) (by omega)
      have hR := P.toBetaDiagram.four_two_negative_rigidity
        (Profile.toBetaDiagram_connected _) hcount
      have hm := (BetaDiagram.rotationRigid_iff_same_order _).mp hR Q.toBetaDiagram
        (Profile.toBetaDiagram_connected _) (by simpa only [Profile.toBetaDiagram_schur] using he.symm)
      rcases profile_motion_of_beta_motion P Q hm with hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
  · exact classified_schur_eq

/-- Full-board form of the four-row complete class, with actual source normalization. -/
theorem four_rows_complete_class_same_order (D E : BetaDiagram 4)
    (hD : D.Connected) (hE : E.Connected) (he : D.schur = E.schur) :
    Classified (D.toProfile hD) (E.toProfile hE) :=
  (four_rows_schur_eq_iff _ _).mp (by simpa only [BetaDiagram.toProfile_schur] using he)

/-- A completely unrestricted equal mate has the produced row count and connectedness,
and belongs to the exact four-row class. -/
theorem four_rows_complete_class (D : BetaDiagram 4) (hD : D.Connected)
    {m : ℕ} (E : BetaDiagram m) (he : E.schur = D.schur) :
    ∃ hrow : m = 4, ∃ hE : (E.castOrder hrow).Connected,
      Classified (D.toProfile hD) ((E.castOrder hrow).toProfile hE) := by
  have hrow : m = 4 := E.row_count_of_schur_eq D he
  have hE := D.connected_full_mate_of_schur_eq E hD he.symm
  refine ⟨hrow, (E.castOrder_connected hrow).mpr hE, ?_⟩
  exact four_rows_complete_class_same_order _ _ hD _
    (by simpa only [BetaDiagram.castOrder_schur] using he.symm)

end SkewJacobiNegative.FourRowClasses
