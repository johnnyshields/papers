/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.GeneralHessenberg
import Mathlib.Data.Finset.Sort

/-!
# All-order safe generator cuts

Actual connected thick components and determinant products for
`lem:staircase-minimum`, and the low-gap argument in
`lem:staircase-content` of `shields-2026-skew-jacobi-negative.tex`.
Components are the consecutive fibres of the number of erased seams above
a row.  All occurrences of a repeated gap are cut simultaneously.
-/

namespace SkewJacobiNegative.Staircase

private theorem erase_X (v w : ℕ+) :
    eraseGenerator v (MvPolynomial.X w) =
      if w = v then (0 : CompleteRing) else MvPolynomial.X w :=
  MvPolynomial.eval₂Hom_X' _ _ _

open Gluing GeneralHessenberg
open scoped BigOperators

/-- Number of seams of numerical value `v` strictly above a row. -/
def cutRank {n : ℕ} (P : Profile n) (v : ℕ+) (i : Fin (n + 1)) : ℕ :=
  ∑ j : Fin n, if j.val < i.val ∧ P.g j = v.val then 1 else 0

@[simp] theorem cutRank_zero {n : ℕ} (P : Profile n) (v : ℕ+) :
    cutRank P v 0 = 0 := by
  simp [cutRank]

/-- The rank increases precisely at an erased seam. -/
theorem cutRank_step {n : ℕ} (P : Profile n) (v : ℕ+) (j : Fin n) :
    cutRank P v j.succ = cutRank P v j.castSucc +
      if P.g j = v.val then 1 else 0 := by
  classical
  have ht (k : Fin n) :
      (if k.val < j.succ.val ∧ P.g k = v.val then 1 else 0) =
      (if k.val < j.castSucc.val ∧ P.g k = v.val then 1 else 0) +
      if k = j then (if P.g j = v.val then 1 else 0) else 0 := by
    by_cases hkj : k = j
    · subst k; simp
    · have hn : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      by_cases h : k.val < j.val
      · simp [hkj, h, show k.val < j.val + 1 by omega]
      · simp [hkj, h, show ¬ k.val < j.val + 1 by omega]
  unfold cutRank
  rw [Finset.sum_congr rfl (fun k _ => ht k), Finset.sum_add_distrib]
  simp

theorem cutRank_monotone {n : ℕ} (P : Profile n) (v : ℕ+) :
    Monotone (cutRank P v) := by
  intro i j hij
  unfold cutRank
  apply Finset.sum_le_sum
  intro k _
  split_ifs <;> omega

/-- The actual block labels, with nonempty fibres built into their type. -/
def CutBlock {n : ℕ} (P : Profile n) (v : ℕ+) :=
  {b : ℕ // b ∈ Finset.univ.image (cutRank P v)}
noncomputable instance {n : ℕ} (P : Profile n) (v : ℕ+) : Fintype (CutBlock P v) :=
  Fintype.ofFinset (Finset.univ.image (cutRank P v)) (fun _ => Iff.rfl)


/-- The rows in a simultaneous cut component. -/
def blockRows {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v) :
    Finset (Fin (n + 1)) := Finset.univ.filter (fun i => cutRank P v i = b.val)

theorem blockRows_nonempty {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v) :
    (blockRows P v b).Nonempty := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp b.property
  exact ⟨i, by simp [blockRows, hi]⟩

/-- Number of internal seams of the genuine component. -/
def blockSize {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v) : ℕ :=
  (blockRows P v b).card - 1

theorem blockRows_card {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v) :
    (blockRows P v b).card = blockSize P v b + 1 := by
  have hp := Finset.card_pos.mpr (blockRows_nonempty P v b)
  unfold blockSize
  omega

/-- Increasing enumeration of the actual rows, not an arbitrary reordering. -/
noncomputable def blockEmbedding {n : ℕ} (P : Profile n) (v : ℕ+)
    (b : CutBlock P v) : Fin (blockSize P v b + 1) ↪o Fin (n + 1) :=
  (blockRows P v b).orderEmbOfFin (blockRows_card P v b)

theorem blockEmbedding_rank {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v)
    (i : Fin (blockSize P v b + 1)) : cutRank P v (blockEmbedding P v b i) = b.val := by
  have hm := Finset.orderEmbOfFin_mem (blockRows P v b) (blockRows_card P v b) i
  change blockEmbedding P v b i ∈ blockRows P v b at hm
  exact (Finset.mem_filter.mp hm).2

/-- Every row in the rank fibre occurs in its ordered component. -/
theorem blockEmbedding_surjective {n : ℕ} (P : Profile n) (v : ℕ+)
    (b : CutBlock P v) (i : Fin (n + 1)) (hi : cutRank P v i = b.val) :
    ∃ j, blockEmbedding P v b j = i := by
  have hm : i ∈ blockRows P v b := by simp [blockRows, hi]
  let e := (blockRows P v b).orderIsoOfFin (blockRows_card P v b)
  exact ⟨e.symm ⟨i, hm⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i, hm⟩)⟩

theorem blockEmbedding_bounds {n : ℕ} (P : Profile n) (v : ℕ+)
    (b : CutBlock P v) (i : Fin (n + 1)) (hi : cutRank P v i = b.val) :
    blockEmbedding P v b 0 ≤ i ∧
      i ≤ blockEmbedding P v b (Fin.last (blockSize P v b)) := by
  obtain ⟨j, rfl⟩ := blockEmbedding_surjective P v b i hi
  exact ⟨(blockEmbedding P v b).monotone (Fin.zero_le _),
    (blockEmbedding P v b).monotone (Fin.le_last _)⟩

/-- Consecutive enumerated rows are consecutive original rows: rank fibres
are intervals, so no unrecorded row can be skipped. -/
theorem blockEmbedding_consecutive {n : ℕ} (P : Profile n) (v : ℕ+)
    (b : CutBlock P v) (j : Fin (blockSize P v b)) :
    (blockEmbedding P v b j.succ).val =
      (blockEmbedding P v b j.castSucc).val + 1 := by
  let e := blockEmbedding P v b
  have hlt : e j.castSucc < e j.succ := e.strictMono Fin.castSucc_lt_succ
  let t : Fin (n + 1) := ⟨(e j.castSucc).val + 1, by have := (e j.succ).isLt; omega⟩
  have htval : t.val = (e j.castSucc).val + 1 := rfl
  have ht : cutRank P v t = b.val := by
    have hlo := cutRank_monotone P v
      (show e j.castSucc ≤ t by change (e j.castSucc).val ≤ t.val; omega)
    have hhi := cutRank_monotone P v
      (show t ≤ e j.succ by change t.val ≤ (e j.succ).val; omega)
    have h1 := blockEmbedding_rank P v b j.castSucc
    have h2 := blockEmbedding_rank P v b j.succ
    change cutRank P v (e j.castSucc) = b.val at h1
    change cutRank P v (e j.succ) = b.val at h2
    omega
  obtain ⟨k, hk⟩ := blockEmbedding_surjective P v b t ht
  change e k = t at hk
  have h1 : j.castSucc < k := e.lt_iff_lt.mp (by
    rw [hk]
    change (e j.castSucc).val < t.val
    omega)
  have h2 : k ≤ j.succ := e.le_iff_le.mp (by
    rw [hk]
    change t.val ≤ (e j.succ).val
    omega)
  have he : k = j.succ := by
    have h1v : j.val < k.val := h1
    have h2v : k.val ≤ j.val + 1 := h2
    apply Fin.ext
    change k.val = j.val + 1
    omega
  subst k
  exact congrArg Fin.val hk

/-- The original seam between two component rows. -/
noncomputable def blockGap {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v)
    (j : Fin (blockSize P v b)) : Fin n :=
  ⟨(blockEmbedding P v b j.castSucc).val, by
    have h := blockEmbedding_consecutive P v b j
    have hb := (blockEmbedding P v b j.succ).isLt
    omega⟩

theorem blockGap_rows {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v)
    (j : Fin (blockSize P v b)) :
    (blockGap P v b j).castSucc = blockEmbedding P v b j.castSucc ∧
      (blockGap P v b j).succ = blockEmbedding P v b j.succ := by
  constructor
  · ext; rfl
  · ext; exact (blockEmbedding_consecutive P v b j).symm

/-- No component retains any seam of the cut value. -/
theorem blockGap_ne {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v)
    (j : Fin (blockSize P v b)) : P.g (blockGap P v b j) ≠ v.val := by
  intro h
  have hs := cutRank_step P v (blockGap P v b j)
  obtain ⟨h1, h2⟩ := blockGap_rows P v b j
  rw [h1, h2, blockEmbedding_rank, blockEmbedding_rank, if_pos h] at hs
  omega

/-- Actual normalized beta coordinates of a cut component. -/
noncomputable def blockPair {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v) :
    Profile.BetaPair (blockSize P v b) where
  xi i := P.xi (blockEmbedding P v b i) -
    P.zeta (blockEmbedding P v b (Fin.last (blockSize P v b)))
  zeta i := P.zeta (blockEmbedding P v b i) -
    P.zeta (blockEmbedding P v b (Fin.last (blockSize P v b)))
  xi_strictAnti i j hij := sub_lt_sub_right
    (P.xi_strictAnti ((blockEmbedding P v b).strictMono hij)) _
  zeta_strictAnti i j hij := sub_lt_sub_right
    (P.zeta_strictAnti ((blockEmbedding P v b).strictMono hij)) _
  zeta_last := sub_self _
  zeta_le_xi_succ j := by
    obtain ⟨h1, h2⟩ := blockGap_rows P v b j
    apply sub_le_sub_right
    rw [← h1, ← h2]
    exact P.zeta_le_xi_succ _
  xi_last_pos := by
    have hx := P.xi_sub_zeta (blockEmbedding P v b (Fin.last (blockSize P v b)))
    have hp := P.r_pos (blockEmbedding P v b (Fin.last (blockSize P v b)))
    omega

/-- The actual connected diagram profile in a canonical simultaneous cut. -/
noncomputable def cutComponent {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v) :
    Profile (blockSize P v b) := Profile.ofBetaPair (blockPair P v b)

@[simp] theorem cutComponent_row {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v)
    (i : Fin (blockSize P v b + 1)) :
    (cutComponent P v b).r i = P.r (blockEmbedding P v b i) := by
  simp only [cutComponent, Profile.ofBetaPair, blockPair]
  rw [show P.xi (blockEmbedding P v b i) -
      P.zeta (blockEmbedding P v b (Fin.last (blockSize P v b))) -
      (P.zeta (blockEmbedding P v b i) -
      P.zeta (blockEmbedding P v b (Fin.last (blockSize P v b)))) =
      P.xi (blockEmbedding P v b i) - P.zeta (blockEmbedding P v b i) by ring,
    P.xi_sub_zeta]
  simp

@[simp] theorem cutComponent_gap {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v)
    (j : Fin (blockSize P v b)) :
    (cutComponent P v b).g j = P.g (blockGap P v b j) := by
  obtain ⟨h1, h2⟩ := blockGap_rows P v b j
  simp only [cutComponent, Profile.ofBetaPair, blockPair]
  rw [show P.xi (blockEmbedding P v b j.succ) -
      P.zeta (blockEmbedding P v b (Fin.last (blockSize P v b))) -
      (P.zeta (blockEmbedding P v b j.castSucc) -
      P.zeta (blockEmbedding P v b (Fin.last (blockSize P v b)))) =
      P.xi (blockEmbedding P v b j.succ) - P.zeta (blockEmbedding P v b j.castSucc) by ring,
    ← h1, ← h2, P.xi_succ_sub_zeta_castSucc]
  simp

/-- Exact common-translation bridge for every cut component. -/
theorem cutComponent_beta {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v) :
    (cutComponent P v b).toBetaPair = blockPair P v b :=
  Profile.equivBetaPair.right_inv _

/-- Every component remains thick; all its cells are the inherited actual cells. -/
theorem cutComponent_thick {n : ℕ} {P : Profile n} (hP : Thick P)
    (v : ℕ+) (b : CutBlock P v) : Thick (cutComponent P v b) := by
  apply hessenberg_thick
  have hbeta := cutComponent_beta P v b
  have hx := congrArg Profile.BetaPair.xi hbeta
  have hz := congrArg Profile.BetaPair.zeta hbeta
  intro i j hij
  simp only [Profile.toBetaPair] at hx hz
  rw [hx, hz]
  simp only [blockPair]
  have hsmall : j.val + 1 < (Fin.last (blockSize P v b)).val := by
    have := i.isLt
    simp only [Fin.val_last]
    omega
  let js : Fin (blockSize P v b + 1) := ⟨j.val + 1, by omega⟩
  have h1 := (blockEmbedding P v b).strictMono
    (show j < js by change j.val < j.val + 1; omega)
  have h2 := (blockEmbedding P v b).strictMono
    (show js < i by change j.val + 1 < i.val; exact hij)
  have h := hP.hessenberg (blockEmbedding P v b i) (blockEmbedding P v b j)
    (by omega)
  linarith

/-- Exact determinant bridge to the actual principal submatrix. -/
theorem cutComponent_schur {n : ℕ} (P : Profile n) (v : ℕ+) (b : CutBlock P v) :
    (cutComponent P v b).toBetaDiagram.schur =
      (P.toBetaDiagram.matrix.submatrix (blockEmbedding P v b)
        (blockEmbedding P v b)).det := by
  rw [Profile.toBetaDiagram_schur]
  unfold Profile.schur
  have hbeta := cutComponent_beta P v b
  have hx := congrArg Profile.BetaPair.xi hbeta
  have hz := congrArg Profile.BetaPair.zeta hbeta
  simp only [Profile.toBetaPair] at hx hz
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp only [hx, hz, blockPair, Matrix.of_apply, Matrix.submatrix_apply,
    BetaDiagram.matrix, Profile.toBetaDiagram]
  rw [show (P.xi (blockEmbedding P v b i) -
      P.zeta (blockEmbedding P v b (Fin.last (blockSize P v b)))) -
      (P.zeta (blockEmbedding P v b j) -
      P.zeta (blockEmbedding P v b (Fin.last (blockSize P v b)))) =
      P.xi (blockEmbedding P v b i) - P.zeta (blockEmbedding P v b j) by ring]
  exact (complete_eq_hh _).symm

/-- Generator erasure makes the actual matrix block triangular at all seams
of the chosen numerical value, including repeated values. -/
theorem erasedMatrix_blockTriangular {n : ℕ} {P : Profile n}
    (hP : Thick P) (v : ℕ+) :
    Matrix.BlockTriangular (P.toBetaDiagram.matrix.map (eraseGenerator v))
      (cutRank P v) := by
  intro i j hij
  have hji : j < i := by
    by_contra h
    have hm := cutRank_monotone P v (le_of_not_gt h)
    omega
  by_cases hfar : j.val + 1 < i.val
  · change eraseGenerator v (complete (P.xi i - P.zeta j)) = 0
    rw [complete_of_neg (hP.hessenberg i j hfar), map_zero]
  · let s : Fin n := ⟨j.val, by have := i.isLt; omega⟩
    have hj : s.castSucc = j := by ext; rfl
    have hi : s.succ = i := by ext; dsimp [s]; omega
    have hs := cutRank_step P v s
    rw [hj, hi] at hs
    have hg : P.g s = v.val := by split_ifs at hs <;> omega
    change eraseGenerator v (complete (P.xi i - P.zeta j)) = 0
    rw [← hi, ← hj, P.xi_succ_sub_zeta_castSucc, hg]
    simp only [complete_nat, erase_X, ite_eq_left rfl, ite_true]

/-- Simultaneous safe cuts factor the actual erased determinant into the
actual erased principal component determinants at every finite order. -/
theorem erase_schur_cut_product {n : ℕ} {P : Profile n}
    (hP : Thick P) (v : ℕ+) :
    eraseGenerator v P.toBetaDiagram.schur =
      ∏ b : CutBlock P v,
        eraseGenerator v (cutComponent P v b).toBetaDiagram.schur := by
  classical
  rw [BetaDiagram.schur, eraseGenerator_det,
    (erasedMatrix_blockTriangular hP v).det]
  rw [← Finset.prod_attach]
  apply Finset.prod_congr rfl
  intro b _
  let b' : CutBlock P v := ⟨b.val, b.property⟩
  change ((P.toBetaDiagram.matrix.map (eraseGenerator v)).toSquareBlock
    (cutRank P v) b'.val).det =
    eraseGenerator v (cutComponent P v b').toBetaDiagram.schur
  rw [cutComponent_schur P v b', eraseGenerator_det]
  let e := (blockRows P v b').orderIsoOfFin (blockRows_card P v b')
  let f : (blockRows P v b') ≃ {i : Fin (n + 1) // cutRank P v i = b'.val} :=
    Equiv.subtypeEquivRight (fun i => by simp [blockRows])
  let ef := e.toEquiv.trans f
  rw [← Matrix.det_reindex_self ef.symm]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A private full-interval coefficient proves nonvanishing after two erasures.
The hypotheses are numerical gap/interval exclusions, not nonzero certificates. -/
theorem double_erase_schur_ne_zero {n : ℕ} {P : Profile n} (hP : Thick P)
    (q v : ℕ+) (hq : fullGenerator P ≠ q) (hv : fullGenerator P ≠ v)
    (hgq : ∀ j, P.g j ≠ q.val) (hgv : ∀ j, P.g j ≠ v.val) :
    eraseGenerator v (eraseGenerator q P.toBetaDiagram.schur) ≠ 0 := by
  classical
  let F := fullGenerator P
  have hgap : eraseGenerator v (eraseGenerator q (gapMonomial P)) = gapMonomial P := by
    simp only [gapMonomial, map_prod]
    apply Finset.prod_congr rfl
    intro j _
    rw [eraseGenerator_complete, if_neg (by exact_mod_cast hgq j),
      eraseGenerator_complete, if_neg (by exact_mod_cast hgv j)]
  have hres : F ∉ (eraseGenerator v (eraseGenerator q P.toBetaDiagram.cornerResidual)).vars :=
    not_mem_vars_erase v F _ (not_mem_vars_erase q F _
      P.toBetaDiagram.largest_not_mem_residual)
  have hgm : F ∉ (gapMonomial P).vars := full_not_mem_gapMonomial hP
  have ha : eraseGenerator v (eraseGenerator q P.toBetaDiagram.schur) =
      (-1 : CompleteRing) ^ n * gapMonomial P * MvPolynomial.X F +
        eraseGenerator v (eraseGenerator q P.toBetaDiagram.cornerResidual) := by
    have hsplit : P.toBetaDiagram.schur =
        (-1 : CompleteRing) ^ n * gapMonomial P * MvPolynomial.X F +
          P.toBetaDiagram.cornerResidual := by
      let T : ℕ+ := ⟨P.toBetaDiagram.largestLabel.toNat,
        by have := P.toBetaDiagram.largestLabel_pos; omega⟩
      have hTF : T = F := by
        apply Subtype.ext
        rfl
      have hs : P.toBetaDiagram.schur =
          P.toBetaDiagram.cornerCoefficient * (MvPolynomial.X T : CompleteRing) +
            P.toBetaDiagram.cornerResidual := P.toBetaDiagram.schur_corner_split
      rw [hTF] at hs
      simpa only [BetaDiagram.cornerCoefficient, cornerPolynomial_eq_gapMonomial hP] using hs
    rw [hsplit]
    simp only [map_add, map_mul, map_pow, map_neg, map_one]
    rw [hgap]
    have hqF : F ≠ q := hq
    have hvF : F ≠ v := hv
    simp only [erase_X, ite_eq_right hqF, ite_eq_right hvF]
  have hs : F ∉ (((-1 : CompleteRing) ^ n) * gapMonomial P).vars := by
    have hc : (-1 : CompleteRing) ^ n = MvPolynomial.C ((-1 : ℚ) ^ n) := by simp
    intro hm
    have hu := MvPolynomial.vars_mul _ _ hm
    rcases Finset.mem_union.mp hu with hm | hm
    · rw [hc, MvPolynomial.vars_C] at hm
      exact Finset.notMem_empty F hm
    · exact hgm hm
  intro hz
  have hd := congrArg (MvPolynomial.pderiv F) hz
  rw [ha] at hd
  simp only [map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hs,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hres,
    MvPolynomial.pderiv_X_self, map_zero, zero_mul, zero_add, mul_one, add_zero] at hd
  exact (mul_ne_zero (pow_ne_zero n (by norm_num)) (gapMonomial_ne_zero P)) hd

/-- A nonempty seam family puts every component next to a cut seam, at one
of its two endpoints. -/
theorem cutComponent_endpoint_above {n : ℕ} (P : Profile n) (v : ℕ+)
    (hocc : ∃ j, P.g j = v.val) (b : CutBlock P v) :
    v.val < (cutComponent P v b).r 0 ∨
      v.val < (cutComponent P v b).r (Fin.last (blockSize P v b)) := by
  let e := blockEmbedding P v b
  let t := e 0
  let u := e (Fin.last (blockSize P v b))
  by_cases hu : u.val < n
  · let s : Fin n := ⟨u.val, hu⟩
    have huc : s.castSucc = u := by ext; rfl
    have hg : P.g s = v.val := by
      by_contra hn
      have hr := cutRank_step P v s
      rw [huc, if_neg hn, add_zero] at hr
      have hb := blockEmbedding_rank P v b (Fin.last (blockSize P v b))
      have hmem : cutRank P v s.succ = b.val := hr.trans hb
      have hbound := (blockEmbedding_bounds P v b s.succ hmem).2
      change s.succ ≤ u at hbound
      have hv := congrArg Fin.val huc
      simp only [Fin.val_castSucc] at hv
      have : s.succ.val = s.val + 1 := rfl
      omega
    right
    rw [cutComponent_row]
    have hr := P.g_lt_castSucc s
    rw [huc, hg] at hr
    exact hr
  · have huLast : u = Fin.last n := by ext; simp only [Fin.val_last]; have := u.isLt; omega
    have ht : 0 < t.val := by
      by_contra hn
      have ht0 : t = 0 := by apply Fin.ext; change t.val = 0; omega
      have h0 := blockEmbedding_rank P v b 0
      have hlast := blockEmbedding_rank P v b (Fin.last (blockSize P v b))
      change cutRank P v t = b.val at h0
      change cutRank P v u = b.val at hlast
      rw [ht0, cutRank_zero] at h0
      rw [huLast] at hlast
      obtain ⟨j, hj⟩ := hocc
      have hs := cutRank_step P v j
      rw [if_pos hj] at hs
      have hm := cutRank_monotone P v (Fin.le_last j.succ)
      omega
    let s : Fin n := ⟨t.val - 1, by have := t.isLt; omega⟩
    have hts : s.succ = t := by ext; dsimp [s]; omega
    have hg : P.g s = v.val := by
      by_contra hn
      have hr := cutRank_step P v s
      rw [hts, if_neg hn, add_zero] at hr
      have hb := blockEmbedding_rank P v b 0
      have hmem : cutRank P v s.castSucc = b.val := hr.symm.trans hb
      have hbound := (blockEmbedding_bounds P v b s.castSucc hmem).1
      change t ≤ s.castSucc at hbound
      change t.val ≤ s.val at hbound
      have hv := congrArg Fin.val hts
      simp only [Fin.val_succ] at hv
      omega
    left
    rw [cutComponent_row]
    have hr := P.g_lt_succ s
    rw [hts, hg] at hr
    exact hr

/-- Each full interval exceeds every endpoint row, weakly; adjacency to a
cut of value `v` therefore makes the full interval strictly exceed `v`. -/
theorem cutComponent_full_gt {n : ℕ} (P : Profile n) (v : ℕ+)
    (hocc : ∃ j, P.g j = v.val) (b : CutBlock P v) :
    (v.val : ℤ) < fullIndex (cutComponent P v b) := by
  let C := cutComponent P v b
  have hx (i : Fin (blockSize P v b + 1)) : (C.r i : ℤ) ≤ fullIndex C := by
    have hr := C.xi_sub_zeta i
    have h1 := C.xi_strictAnti.antitone (Fin.zero_le i)
    have h2 := C.zeta_strictAnti.antitone (Fin.le_last i)
    change (C.r i : ℤ) ≤ C.xi 0 - C.zeta (Fin.last (blockSize P v b))
    omega
  rcases cutComponent_endpoint_above P v hocc b with h | h
  · have hc : (v.val : ℤ) < C.r 0 := by exact_mod_cast h
    exact hc.trans_le (hx 0)
  · have hc : (v.val : ℤ) < C.r (Fin.last (blockSize P v b)) := by exact_mod_cast h
    exact hc.trans_le (hx _)

/-- All double-erased actual component determinants are nonzero, without
assuming any factor's nonvanishing. -/
theorem double_erase_cutComponent_ne_zero {n : ℕ} {P : Profile n}
    {q : ℕ+} (hP : QComponent q P) (v : ℕ+) (hqv : q.val < v.val)
    (hocc : ∃ j, P.g j = v.val) (b : CutBlock P v) :
    eraseGenerator v (eraseGenerator q (cutComponent P v b).toBetaDiagram.schur) ≠ 0 := by
  have hf := cutComponent_full_gt P v hocc b
  have hne (w : ℕ+) (hw : w.val ≤ v.val) :
      fullGenerator (cutComponent P v b) ≠ w := by
    intro he
    have hv := congrArg Subtype.val he
    have hp := (cutComponent P v b).toBetaDiagram.largestLabel_pos
    change (fullIndex (cutComponent P v b)).toNat = w.val at hv
    change 0 < fullIndex (cutComponent P v b) at hp
    omega
  apply double_erase_schur_ne_zero (cutComponent_thick hP.thick v b) q v
    (hne q hqv.le) (hne v le_rfl)
  · intro j
    simpa only [cutComponent_gap] using hP.gap_ne (blockGap P v b j)
  · intro j
    simpa only [cutComponent_gap] using blockGap_ne P v b j

/-- Erasing a gap of index larger than the cut cannot annihilate the actual
restriction: simultaneous cuts give nonzero actual component determinants. -/
theorem erase_restriction_at_gap_ne_zero {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (v : ℕ+) (hqv : q.val < v.val)
    (hocc : ∃ j, P.g j = v.val) :
    eraseGenerator v (restriction q P) ≠ 0 := by
  classical
  have hcomm (p : CompleteRing) : eraseGenerator v (eraseGenerator q p) =
      eraseGenerator q (eraseGenerator v p) := by
    have he : (eraseGenerator v).comp (eraseGenerator q) =
        (eraseGenerator q).comp (eraseGenerator v) := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [eraseGenerator]
      · intro w
        have hqvn : q ≠ v := by
          intro h
          have he : q.val = v.val := congrArg (fun w : ℕ+ => w.val) h
          exact (ne_of_lt hqv) he
        simp only [RingHom.comp_apply]
        by_cases hwq : w = q <;> by_cases hwv : w = v <;>
          simp only [erase_X, hwq, hwv, ite_true, ite_false, map_zero]
        all_goals subst w; simp only [erase_X, hqvn, hqvn.symm, ite_true, ite_false,
          map_zero, ite_eq_left rfl]
    exact congrArg (fun f : CompleteRing →+* CompleteRing => f p) he
  unfold restriction
  rw [hcomm, erase_schur_cut_product hP.thick v, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  rw [← hcomm]
  exact double_erase_cutComponent_ne_zero hP v hqv hocc b

/-- No high-index internal gap variable divides the actual restriction. -/
theorem variable_not_dvd_restriction_of_high_gap {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (v : ℕ+) (hqv : q.val < v.val)
    (hocc : ∃ j, P.g j = v.val) : ¬ MvPolynomial.X v ∣ restriction q P := by
  rintro ⟨p, hp⟩
  apply erase_restriction_at_gap_ne_zero hP v hqv hocc
  rw [hp, map_mul]
  simp [eraseGenerator]

/-- A minimum generator is absent from every actual component after all
its seams have been cut. -/
theorem minimum_not_mem_cutComponent {n : ℕ} {P : Profile n}
    (hP : Thick P) (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j)
    (hocc : ∃ j, P.g j = z.val) (b : CutBlock P z) :
    z ∉ (cutComponent P z b).toBetaDiagram.schur.vars := by
  rw [cutComponent_schur]
  apply not_mem_vars_det
  intro i j
  change z ∉ (complete
    (P.xi (blockEmbedding P z b i) - P.zeta (blockEmbedding P z b j))).vars
  rw [mem_vars_complete_iff]
  intro he
  obtain ⟨s, hi, hj, hg⟩ :=
    (minimum_index_iff_seam hP z hmin hocc
      (blockEmbedding P z b i) (blockEmbedding P z b j)).mp he.symm
  have hs := cutRank_step P z s
  rw [← hi, ← hj, blockEmbedding_rank, blockEmbedding_rank, if_pos hg] at hs
  omega

/-- The constant minimum-gap layer is the product of the actual unspecialized
component polynomials, not a postulated factorization. -/
theorem minimum_cut_product {n : ℕ} {P : Profile n}
    (hP : Thick P) (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j)
    (hocc : ∃ j, P.g j = z.val) :
    eraseGenerator z P.toBetaDiagram.schur =
      ∏ b : CutBlock P z, (cutComponent P z b).toBetaDiagram.schur := by
  rw [erase_schur_cut_product hP z]
  apply Finset.prod_congr rfl
  intro b _
  exact eraseGenerator_eq_self z _
    (minimum_not_mem_cutComponent hP z hmin hocc b)

/-- Multiplicity counts seam positions, so coincident gaps contribute separately. -/
def minimumMultiplicity {n : ℕ} (P : Profile n) (z : ℕ+) : ℕ :=
  ∑ j : Fin n, if P.g j = z.val then 1 else 0

def minimumRow {n : ℕ} (P : Profile n) (z : ℕ+) (i : Fin (n + 1)) : Prop :=
  ∃ s : Fin n, i = s.succ ∧ P.g s = z.val
noncomputable instance {n : ℕ} (P : Profile n) (z : ℕ+) (i : Fin (n + 1)) :
    Decidable (minimumRow P z i) := Classical.propDecidable _


@[simp] theorem minimumRow_zero {n : ℕ} (P : Profile n) (z : ℕ+) :
    ¬ minimumRow P z 0 := by
  rintro ⟨s, hs, _⟩
  exact Fin.succ_ne_zero s hs.symm

@[simp] theorem minimumRow_succ {n : ℕ} (P : Profile n) (z : ℕ+) (s : Fin n) :
    minimumRow P z s.succ ↔ P.g s = z.val := by
  constructor
  · rintro ⟨t, ht, hg⟩
    have he := Fin.succ_injective _ ht
    simpa [he] using hg
  · intro h; exact ⟨s, rfl, h⟩

/-- The genuine top coefficient matrix: each minimum seam row is replaced
by its subdiagonal unit row, and every other row is the actual matrix row. -/
noncomputable def minimumTopMatrix {n : ℕ} (P : Profile n) (z : ℕ+) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) CompleteRing :=
  fun i j => if minimumRow P z i then
    (if i.val = j.val + 1 then 1 else 0) else
    complete (P.xi i - P.zeta j)

theorem minimumRow_contract {n : ℕ} (P : Profile (n + 1)) (z : ℕ+)
    (c : Fin (n + 1)) (i : Fin (n + 1)) :
    minimumRow (contract P c) z i ↔ minimumRow P z (c.succ.succAbove i) := by
  cases i using Fin.cases with
  | zero =>
      have he : c.succ.succAbove 0 = 0 := by
        apply Fin.ext
        simp only [Fin.succAbove]
        split_ifs <;> simp_all only [Fin.val_zero, Fin.val_castSucc,
          Fin.val_succ, Fin.lt_def] <;> omega
      simp [he]
  | succ i =>
      rw [(contraction_gap_indices c i).1]
      simp [minimumRow_succ, contract_gap]

/-- Deleting a selected seam from the top matrix is exactly the top matrix
of the actual contracted profile. -/
theorem minimumTopMatrix_contract {n : ℕ} (P : Profile (n + 1)) (z : ℕ+)
    (c : Fin (n + 1)) :
    (minimumTopMatrix P z).submatrix c.succ.succAbove c.castSucc.succAbove =
      minimumTopMatrix (contract P c) z := by
  classical
  obtain ⟨hx, hz⟩ := contract_beta P c
  apply Matrix.ext
  intro i j
  simp only [minimumTopMatrix, Matrix.submatrix_apply, hx, hz]
  simp only [← minimumRow_contract]
  by_cases hi : minimumRow (contract P c) z i
  · simp only [if_pos hi]
    obtain ⟨s, rfl, _⟩ := hi
    rw [(contraction_gap_indices c s).1]
    have he : (c.succAbove s).succ.val = (c.castSucc.succAbove j).val + 1 ↔
        s.succ.val = j.val + 1 := by
      have hcol := (contraction_gap_indices c s).2
      constructor
      · intro h
        have hc : c.castSucc.succAbove j = c.castSucc.succAbove s.castSucc := by
          rw [hcol]
          apply Fin.ext
          simp only [Fin.val_succ] at h
          simp only [Fin.val_castSucc]
          omega
        have hj := Fin.succAbove_right_injective hc
        rw [hj]
        simp
      · intro h
        have hj : j = s.castSucc := by
          apply Fin.ext
          simp only [Fin.val_succ] at h
          simp only [Fin.val_castSucc]
          omega
        rw [hj, hcol]
        simp
    simp only [he]
  · simp only [if_neg hi]

/-- Laplace extraction of a selected seam gives the actual contraction
with exactly one minus sign. -/
theorem minimumTopMatrix_det_contract {n : ℕ} (P : Profile (n + 1)) (z : ℕ+)
    (c : Fin (n + 1)) (hc : P.g c = z.val) :
    (minimumTopMatrix P z).det = -(minimumTopMatrix (contract P c) z).det := by
  classical
  rw [Matrix.det_succ_row _ c.succ]
  have hr (j : Fin (n + 2)) :
      minimumTopMatrix P z c.succ j = if j = c.castSucc then 1 else 0 := by
    have he : c.succ.val = j.val + 1 ↔ j = c.castSucc := by
      constructor
      · intro h
        apply Fin.ext
        simp only [Fin.val_succ] at h
        simp only [Fin.val_castSucc]
        omega
      · intro h
        subst j
        simp
    simp only [minimumTopMatrix, minimumRow_succ, hc, ite_true, he]
  simp only [hr]
  rw [Finset.sum_eq_single c.castSucc]
  · rw [minimumTopMatrix_contract]
    have hs : (-1 : CompleteRing) ^ (c.succ.val + c.castSucc.val) = -1 := by
      rw [show c.succ.val + c.castSucc.val = 2 * c.val + 1 by simp; omega,
        pow_add, pow_mul]
      simp
    simp [hs]
  · intro j _ hj; simp [hj]
  · simp

theorem minimumMultiplicity_contract {n : ℕ} (P : Profile (n + 1)) (z : ℕ+)
    (c : Fin (n + 1)) (hc : P.g c = z.val) :
    minimumMultiplicity P z = minimumMultiplicity (contract P c) z + 1 := by
  classical
  unfold minimumMultiplicity
  rw [Fin.sum_univ_succAbove _ c]
  simp only [hc, ite_true, contract_gap]
  omega

/-- Contract every occurrence of the numerical minimum, using only actual
profile contractions.  The result carries its genuine finite row count. -/
noncomputable def contractAllMinimum : {n : ℕ} → Profile n → ℕ+ → Σ k, Profile k
  | 0, P, _ => ⟨0, P⟩
  | n + 1, P, z =>
      if h : ∃ c : Fin (n + 1), P.g c = z.val then
        contractAllMinimum (contract P (Classical.choose h)) z
      else ⟨n + 1, P⟩

theorem contractAllMinimum_thick {n : ℕ} {P : Profile n} (hP : Thick P) (z : ℕ+) :
    Thick (contractAllMinimum P z).2 := by
  induction n with
  | zero => exact hP
  | succ n ih =>
      by_cases h : ∃ c : Fin (n + 1), P.g c = z.val
      · have he : contractAllMinimum P z =
            contractAllMinimum (contract P (Classical.choose h)) z := by
          simp only [contractAllMinimum, dif_pos h]
        rw [he]
        exact ih (contract_thick hP (Classical.choose h))
      · have he : contractAllMinimum P z = ⟨n + 1, P⟩ := by
          simp only [contractAllMinimum, dif_neg h]
        rw [he]
        exact hP

/-- The row loss is exactly the multiplicity of the contracted minimum. -/
theorem contractAllMinimum_size {n : ℕ} (P : Profile n) (z : ℕ+) :
    (contractAllMinimum P z).1 + minimumMultiplicity P z = n := by
  induction n with
  | zero => simp [contractAllMinimum, minimumMultiplicity]
  | succ n ih =>
      simp only [contractAllMinimum]
      split_ifs with h
      · rw [minimumMultiplicity_contract P z (Classical.choose h)
          (Classical.choose_spec h)]
        have hs := ih (contract P (Classical.choose h))
        omega
      · have hm : minimumMultiplicity P z = 0 := by
          unfold minimumMultiplicity
          apply Finset.sum_eq_zero
          intro c _
          rw [if_neg (fun hc => h ⟨c, hc⟩)]
        simp [hm]

/-- All selected-row Laplace contractions identify the genuine coefficient
matrix with the Schur polynomial of the actual thick contraction. -/
theorem minimumTopMatrix_det {n : ℕ} (P : Profile n) (z : ℕ+) :
    (minimumTopMatrix P z).det =
      (-1 : CompleteRing) ^ minimumMultiplicity P z *
        (contractAllMinimum P z).2.toBetaDiagram.schur := by
  induction n with
  | zero =>
      simp only [minimumMultiplicity, Fin.sum_univ_zero, contractAllMinimum,
        pow_zero, one_mul]
      change (minimumTopMatrix P z).det = P.toBetaDiagram.matrix.det
      rw [Matrix.det_fin_one, Matrix.det_fin_one]
      change minimumTopMatrix P z 0 0 = complete (P.xi 0 - P.zeta 0)
      simp only [minimumTopMatrix, minimumRow_zero, ite_false]
  | succ n ih =>
      by_cases h : ∃ c : Fin (n + 1), P.g c = z.val
      · have he : contractAllMinimum P z =
            contractAllMinimum (contract P (Classical.choose h)) z := by
          simp only [contractAllMinimum, dif_pos h]
        rw [he, minimumTopMatrix_det_contract P z (Classical.choose h)
          (Classical.choose_spec h), ih,
          minimumMultiplicity_contract P z (Classical.choose h) (Classical.choose_spec h)]
        rw [pow_succ]
        ring
      · have hcontract : contractAllMinimum P z = ⟨n + 1, P⟩ := by
          simp only [contractAllMinimum, dif_neg h]
        rw [hcontract]
        have hm : minimumMultiplicity P z = 0 := by
          unfold minimumMultiplicity
          apply Finset.sum_eq_zero
          intro c _
          rw [if_neg (fun hc => h ⟨c, hc⟩)]
        have he : minimumTopMatrix P z = P.toBetaDiagram.matrix := by
          apply Matrix.ext
          intro i j
          have hi : ¬ minimumRow P z i := by
            rintro ⟨c, _, hc⟩
            exact h ⟨c, hc⟩
          simp [minimumTopMatrix, hi, BetaDiagram.matrix, Profile.toBetaDiagram]
        simp [hm, he, BetaDiagram.schur]

/-- Regard the actual generator `h_z` as the univariate indeterminate, leaving
all other actual generators in the coefficient ring. -/
noncomputable def minimumPolynomial (z : ℕ+) : CompleteRing →+* Polynomial CompleteRing :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun w => if w = z then Polynomial.X else Polynomial.C (MvPolynomial.X w))

theorem minimumPolynomial_complete (z : ℕ+) (k : ℤ) :
    minimumPolynomial z (complete k) =
      if k = (z.val : ℤ) then Polynomial.X else Polynomial.C (complete k) := by
  classical
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [complete_of_neg hk, map_zero, if_neg (by have := z.pos; omega)]
    simp
  · rw [complete_zero, map_one, if_neg (by have := z.pos; omega)]
    simp
  · let w : ℕ+ := ⟨k.toNat, by omega⟩
    have hw : (w.val : ℤ) = k := by dsimp [w]; omega
    rw [← hw, complete_nat]
    have he : w = z ↔ (w.val : ℤ) = z.val := by
      constructor
      · intro h
        exact congrArg (fun a : ℕ+ => (a.val : ℤ)) h
      · intro h
        apply Subtype.ext
        have hn : w.val = z.val := by omega
        exact hn
    simp only [minimumPolynomial, MvPolynomial.eval₂Hom_X', he, complete_nat]

private theorem coeff_prod_row_bound {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (f : ι → Polynomial R) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
        Polynomial.coeff_mul_add_eq_of_natDegree_le
          (h i (Finset.mem_insert_self _ _))
          ((Polynomial.natDegree_prod_le s f).trans
            (Finset.sum_le_sum (fun j hj => h j (Finset.mem_insert_of_mem hj)))),
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

/-- The coefficient at the sum of row-degree bounds is the determinant of
the entrywise top row coefficients.  This is polynomial multilinearity,
not a leading-coefficient nonvanishing assumption. -/
theorem coeff_det_row_bound {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (Polynomial R)) (d : Fin n → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ d i) :
    M.det.coeff (∑ i, d i) =
      (Matrix.of (fun i j : Fin n => (M i j).coeff (d i))).det := by
  classical
  have hl : M.det =
      ∑ σ : Equiv.Perm (Fin n),
        (((Equiv.Perm.sign σ : ℤ) : Polynomial R)) * ∏ i, M i (σ i) := by
    rw [← Matrix.det_transpose M, Matrix.det_apply']
    simp only [Matrix.transpose_apply]
  have hr : (Matrix.of (fun i j : Fin n => (M i j).coeff (d i))).det =
      ∑ σ : Equiv.Perm (Fin n),
        (((Equiv.Perm.sign σ : ℤ) : R)) * ∏ i, (M i (σ i)).coeff (d i) := by
    rw [← Matrix.det_transpose (Matrix.of (fun i j : Fin n => (M i j).coeff (d i))),
      Matrix.det_apply']
    simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [hl, hr]
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ _
  have hs : (((Equiv.Perm.sign σ : ℤ) : Polynomial R)) =
      Polynomial.C (((Equiv.Perm.sign σ : ℤ) : R)) := by simp
  rw [hs, Polynomial.coeff_C_mul, coeff_prod_row_bound Finset.univ
    (fun i => M i (σ i)) d (fun i _ => h i (σ i))]

/-- The minimum multiplicity equals the sum of the selected-row degree bounds. -/
theorem minimumMultiplicity_rows {n : ℕ} (P : Profile n) (z : ℕ+) :
    minimumMultiplicity P z =
      ∑ i : Fin (n + 1), if minimumRow P z i then 1 else 0 := by
  classical
  rw [Fin.sum_univ_succ]
  simp only [minimumRow_zero, if_false, zero_add, minimumRow_succ]
  rfl

/-- Entrywise degree bounds and their exact top coefficients are produced
from the numerical minimum and the actual matrix geometry. -/
theorem minimum_entry_top {n : ℕ} {P : Profile n} (hP : Thick P)
    (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j) (hocc : ∃ j, P.g j = z.val)
    (i j : Fin (n + 1)) :
    (minimumPolynomial z (P.toBetaDiagram.matrix i j)).natDegree ≤
      (if minimumRow P z i then 1 else 0) ∧
    (minimumPolynomial z (P.toBetaDiagram.matrix i j)).coeff
      (if minimumRow P z i then 1 else 0) = minimumTopMatrix P z i j := by
  classical
  change (minimumPolynomial z (complete (P.xi i - P.zeta j))).natDegree ≤
      (if minimumRow P z i then 1 else 0) ∧
    (minimumPolynomial z (complete (P.xi i - P.zeta j))).coeff
      (if minimumRow P z i then 1 else 0) = minimumTopMatrix P z i j
  rw [minimumPolynomial_complete]
  by_cases he : P.xi i - P.zeta j = (z.val : ℤ)
  · obtain ⟨s, hi, hj, hg⟩ := (minimum_index_iff_seam hP z hmin hocc i j).mp he
    have hr : minimumRow P z i := ⟨s, hi, hg⟩
    have hval : i.val = j.val + 1 := by rw [hi, hj]; rfl
    simp only [he, ite_true, minimumTopMatrix, ite_eq_left hr, hval,
      Polynomial.natDegree_X, Polynomial.coeff_X_one, le_refl, and_self]
  · by_cases hr : minimumRow P z i
    · have hn : i.val ≠ j.val + 1 := by
        intro h
        obtain ⟨s, hi, hg⟩ := hr
        have hj : j = s.castSucc := by
          rw [hi] at h
          apply Fin.ext
          change j.val = s.val
          change s.val + 1 = j.val + 1 at h
          omega
        exact he ((minimum_index_iff_seam hP z hmin hocc i j).mpr ⟨s, hi, hj, hg⟩)
      simp [he, hr, hn, minimumTopMatrix]
    · simp [he, hr, minimumTopMatrix]

/-- The highest minimum-gap layer is exactly the signed actual Schur
polynomial after every minimum seam is contracted. -/
theorem minimum_highest_layer {n : ℕ} {P : Profile n} (hP : Thick P)
    (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j) (hocc : ∃ j, P.g j = z.val) :
    (minimumPolynomial z P.toBetaDiagram.schur).coeff (minimumMultiplicity P z) =
      (-1 : CompleteRing) ^ minimumMultiplicity P z *
        (contractAllMinimum P z).2.toBetaDiagram.schur := by
  classical
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial CompleteRing) :=
    (minimumPolynomial z).mapMatrix P.toBetaDiagram.matrix
  let d : Fin (n + 1) → ℕ := fun i => if minimumRow P z i then 1 else 0
  have hm : minimumPolynomial z P.toBetaDiagram.schur = M.det :=
    (minimumPolynomial z).map_det P.toBetaDiagram.matrix
  have hc : M.det.coeff (∑ i, d i) =
      (Matrix.of (fun i j : Fin (n + 1) => (M i j).coeff (d i))).det :=
    coeff_det_row_bound M d (fun i j => (minimum_entry_top hP z hmin hocc i j).1)
  rw [hm, minimumMultiplicity_rows]
  change M.det.coeff (∑ i, d i) =
    (-1 : CompleteRing) ^ (∑ i, d i) *
      (contractAllMinimum P z).2.toBetaDiagram.schur
  rw [hc]
  have he : (Matrix.of (fun i j : Fin (n + 1) => (M i j).coeff (d i))) =
      minimumTopMatrix P z := by
    apply Matrix.ext
    intro i j
    exact (minimum_entry_top hP z hmin hocc i j).2
  rw [he]
  simpa only [minimumMultiplicity_rows, BetaDiagram.schur, d] using minimumTopMatrix_det P z

theorem contractAllMinimum_gap_ne {n : ℕ} (P : Profile n) (z : ℕ+)
    (j : Fin (contractAllMinimum P z).1) :
    (contractAllMinimum P z).2.g j ≠ z.val := by
  revert j
  induction n with
  | zero => intro j; exact Fin.elim0 j
  | succ n ih =>
      by_cases h : ∃ c : Fin (n + 1), P.g c = z.val
      · have he : contractAllMinimum P z =
            contractAllMinimum (contract P (Classical.choose h)) z := by
          simp only [contractAllMinimum, dif_pos h]
        rw [he]
        exact ih (contract P (Classical.choose h))
      · have he : contractAllMinimum P z = ⟨n + 1, P⟩ := by
          simp only [contractAllMinimum, dif_neg h]
        rw [he]
        intro j hj
        exact h ⟨j, hj⟩

theorem contractAllMinimum_gap_pos {n : ℕ} (P : Profile n)
    (hp : ∀ j, 0 < P.g j) (z : ℕ+)
    (j : Fin (contractAllMinimum P z).1) :
    0 < (contractAllMinimum P z).2.g j := by
  revert j
  induction n with
  | zero => intro j; exact Fin.elim0 j
  | succ n ih =>
      by_cases h : ∃ c : Fin (n + 1), P.g c = z.val
      · have he : contractAllMinimum P z =
            contractAllMinimum (contract P (Classical.choose h)) z := by
          simp only [contractAllMinimum, dif_pos h]
        rw [he]
        apply ih (contract P (Classical.choose h))
        intro s
        rw [contract_gap]
        exact hp _
      · have he : contractAllMinimum P z = ⟨n + 1, P⟩ := by
          simp only [contractAllMinimum, dif_neg h]
        rw [he]
        exact hp

/-- Polynomial determinant degree is bounded by the sum of actual row bounds. -/
theorem natDegree_det_row_bound {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (Polynomial R)) (d : Fin n → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ d i) :
    M.det.natDegree ≤ ∑ i, d i := by
  classical
  rw [← Matrix.det_transpose M, Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hs : (((Equiv.Perm.sign σ : ℤ) : Polynomial R)) =
      Polynomial.C (((Equiv.Perm.sign σ : ℤ) : R)) := by simp
  rw [hs]
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_prod_le Finset.univ (fun i => M i (σ i))).trans
      (Finset.sum_le_sum (fun i _ => h i (σ i))))

/-- The minimum-gap degree is exactly its seam multiplicity.  Nonvanishing
of the top coefficient is produced by the actual contracted determinant. -/
theorem minimum_degree_exact {n : ℕ} {P : Profile n} (hP : Thick P)
    (z : ℕ+) (hmin : ∀ j, z.val ≤ P.g j) (hocc : ∃ j, P.g j = z.val) :
    (minimumPolynomial z P.toBetaDiagram.schur).natDegree = minimumMultiplicity P z := by
  classical
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [BetaDiagram.schur, (minimumPolynomial z).map_det, minimumMultiplicity_rows]
    exact natDegree_det_row_bound _ _
      (fun i j => (minimum_entry_top hP z hmin hocc i j).1)
  · rw [minimum_highest_layer hP z hmin hocc]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (contractAllMinimum P z).2.toBetaDiagram.schur_ne_zero

/-- Positive internal seams remain positive in every genuine cut component. -/
theorem cutComponent_gap_pos {n : ℕ} (P : Profile n) (hp : ∀ j, 0 < P.g j)
    (v : ℕ+) (b : CutBlock P v) (j : Fin (blockSize P v b)) :
    0 < (cutComponent P v b).g j := by
  rw [cutComponent_gap]
  exact hp _

theorem cutComponent_connected {n : ℕ} (P : Profile n) (v : ℕ+)
    (b : CutBlock P v) : (cutComponent P v b).toBetaDiagram.Connected :=
  (cutComponent P v b).toBetaDiagram_connected

end SkewJacobiNegative.Staircase
