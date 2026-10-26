/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroPrefixContraction
import SkewClassInflation.InflationClasses

/-!
# Exact reassembly of an ordered zero cut

Formalizes the literal positional reassembly in `thm:two-row-thin-class`
of `shields-2026-skew-class-inflation.tex`.  Both normalized principal
profiles are joined back with their actual span translation.  The result
is equality of connected translation classes, not merely Schur equality.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

/-- Complete normalized profile supports recover the literal connected translation class. -/
theorem profileSigma_eq_of_full_sets {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hr : P.toBetaDiagram.rowSet = Q.toBetaDiagram.rowSet)
    (hc : P.toBetaDiagram.colSet = Q.toBetaDiagram.colSet) :
    (⟨n, P⟩ : ConnectedProfile) = ⟨m, Q⟩ := by
  have hn := congrArg Finset.card hr
  rw [BetaDiagram.rowSet_card, BetaDiagram.rowSet_card] at hn
  have hnm := Nat.succ.inj hn
  subst m
  have he := BetaDiagram.ext_sets P.toBetaDiagram Q.toBetaDiagram hr hc
  have hx : P.xi = Q.xi := congrArg BetaDiagram.row he
  have hz : P.zeta = Q.zeta := congrArg BetaDiagram.col he
  have hPQ := SkewJacobiNegative.Gluing.Profile.eq_of_beta_eq hx hz
  cases hPQ
  rfl

/-- The two consecutive principal intervals cover the whole full coordinate list. -/
theorem image_at_cut {n : ℕ} (f : Fin (n + 2) → ℤ) (c : Fin (n + 1)) :
    Finset.univ.image f =
      Finset.univ.image (fun i => f (sliceEmbedding 0 c.val (by omega) i)) ∪
        Finset.univ.image (fun i => f
          (sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) i)) := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hic : i.val ≤ c.val
    · left
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      change f ⟨0 + i.val, by have := i.isLt; omega⟩ = x
      simpa only [Nat.zero_add] using hi
    · right
      refine ⟨⟨i.val - (c.val + 1), by have := i.isLt; have := c.isLt; omega⟩, ?_⟩
      have he : sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega)
          ⟨i.val - (c.val + 1), by have := i.isLt; have := c.isLt; omega⟩ = i := by
        apply Fin.ext
        change c.val + 1 + (i.val - (c.val + 1)) = i.val
        omega
      rw [he]
      exact hi
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨sliceEmbedding 0 c.val (by omega) i, hi⟩
    · exact ⟨sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) i, hi⟩

/-- A genuine zero cut reassembles literally into the two actual normalized principal profiles. -/
theorem zero_cut_reassembly {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1))
    (hc : P.g c = 0) :
    (⟨n + 1, P⟩ : ConnectedProfile) =
      ⟨c.val + (n - c.val) + 1, Profile.zeroJoin (leftOfSeam P c) (rightOfSeam P c)⟩ := by
  let L := slice P 0 c.val (by omega)
  let R := slice P (c.val + 1) (n - c.val) (by have := c.isLt; omega)
  obtain ⟨hxL, hzL⟩ := slice_beta P 0 c.val (by omega)
  obtain ⟨hxR, hzR⟩ := slice_beta P (c.val + 1) (n - c.val) (by have := c.isLt; omega)
  have hl : sliceEmbedding 0 c.val (by omega) (Fin.last c.val) = c.castSucc := by
    apply Fin.ext
    change 0 + c.val = c.val
    omega
  have hr : sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega)
      (Fin.last (n - c.val)) = Fin.last (n + 1) := by
    apply Fin.ext
    change c.val + 1 + (n - c.val) = n + 1
    have := c.isLt
    omega
  have h0 : sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) 0 = c.succ := by
    apply Fin.ext
    change c.val + 1 + 0 = c.val + 1
    omega
  have hspan : R.xi 0 = P.zeta c.castSucc := by
    have h := congrFun hxR 0
    rw [h0, hr, P.zeta_last, sub_zero] at h
    have hg := P.xi_succ_sub_zeta_castSucc c
    rw [hc] at hg
    exact h.trans (sub_eq_zero.mp (by simpa only [Nat.cast_zero] using hg))
  apply profileSigma_eq_of_full_sets P (Profile.zeroJoin L R)
  · rw [Profile.zeroJoin, Profile.join_rowSet]
    simp only [Nat.cast_zero, sub_zero]
    change Finset.univ.image P.xi = (Finset.univ.image L.xi).image (fun x => x + R.xi 0) ∪
      Finset.univ.image R.xi
    rw [Finset.image_image, image_at_cut P.xi c]
    congr 1
    · apply Finset.image_congr
      intro i _
      change P.xi (sliceEmbedding 0 c.val (by omega) i) = L.xi i + R.xi 0
      rw [congrFun hxL i, hl, hspan]
      ring
    · apply Finset.image_congr
      intro i _
      change P.xi (sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) i) = R.xi i
      rw [congrFun hxR i, hr, P.zeta_last, sub_zero]
  · rw [Profile.zeroJoin, Profile.join_colSet]
    simp only [Nat.cast_zero, sub_zero]
    change Finset.univ.image P.zeta = (Finset.univ.image L.zeta).image (fun x => x + R.xi 0) ∪
      Finset.univ.image R.zeta
    rw [Finset.image_image, image_at_cut P.zeta c]
    congr 1
    · apply Finset.image_congr
      intro i _
      change P.zeta (sliceEmbedding 0 c.val (by omega) i) = L.zeta i + R.xi 0
      rw [congrFun hzL i, hl, hspan]
      ring
    · apply Finset.image_congr
      intro i _
      change P.zeta (sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) i) = R.zeta i
      rw [congrFun hzR i, hr, P.zeta_last, sub_zero]

end SkewClassInflation
