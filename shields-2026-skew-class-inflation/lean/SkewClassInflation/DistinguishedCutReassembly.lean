/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroCutReassembly

/-!
# Literal reassembly at a specified numerical seam

The consecutive-profile split used in `lem:total-contraction-inverse`
of `shields-2026-skew-class-inflation.tex`.  The joining bounds and
literal full profile are produced from the actual chosen seam.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

/-- Cutting a genuine seam and rejoining its two actual principal profiles is literal equality. -/
theorem distinguished_cut_reassembly {n : ℕ} (P : Profile (n + 1))
    (c : Fin (n + 1)) (d : ℕ) (hc : P.g c = d) :
    ∃ hL : d < (leftOfSeam P c).r (Fin.last c.val),
    ∃ hR : d < (rightOfSeam P c).r 0,
      (⟨n + 1, P⟩ : ConnectedProfile) =
        ⟨c.val + (n - c.val) + 1,
          Profile.join (leftOfSeam P c) (rightOfSeam P c) d hL hR⟩ := by
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
  have hL : d < L.r (Fin.last c.val) := by
    change d < P.r (sliceEmbedding 0 c.val (by omega) (Fin.last c.val))
    rw [hl]
    simpa only [hc] using P.g_lt_castSucc c
  have hR : d < R.r 0 := by
    change d < P.r (sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) 0)
    rw [h0]
    simpa only [hc] using P.g_lt_succ c
  refine ⟨hL, hR, ?_⟩
  have hspan : R.xi 0 - (d : ℤ) = P.zeta c.castSucc := by
    have h := congrFun hxR 0
    rw [h0, hr, P.zeta_last, sub_zero] at h
    have hg := P.xi_succ_sub_zeta_castSucc c
    rw [hc] at hg
    change R.xi 0 = P.xi c.succ at h
    omega
  apply profileSigma_eq_of_full_sets P (Profile.join L R d hL hR)
  · rw [Profile.join_rowSet]
    change Finset.univ.image P.xi =
      (Finset.univ.image L.xi).image (fun x => x + R.xi 0 - (d : ℤ)) ∪ Finset.univ.image R.xi
    rw [Finset.image_image, image_at_cut P.xi c]
    congr 1
    · apply Finset.image_congr
      intro i _
      change P.xi (sliceEmbedding 0 c.val (by omega) i) = L.xi i + R.xi 0 - (d : ℤ)
      rw [congrFun hxL i, hl]
      omega
    · apply Finset.image_congr
      intro i _
      change P.xi (sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) i) = R.xi i
      rw [congrFun hxR i, hr, P.zeta_last, sub_zero]
  · rw [Profile.join_colSet]
    change Finset.univ.image P.zeta =
      (Finset.univ.image L.zeta).image (fun x => x + R.xi 0 - (d : ℤ)) ∪ Finset.univ.image R.zeta
    rw [Finset.image_image, image_at_cut P.zeta c]
    congr 1
    · apply Finset.image_congr
      intro i _
      change P.zeta (sliceEmbedding 0 c.val (by omega) i) = L.zeta i + R.xi 0 - (d : ℤ)
      rw [congrFun hzL i, hl]
      omega
    · apply Finset.image_congr
      intro i _
      change P.zeta (sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) i) = R.zeta i
      rw [congrFun hzR i, hr, P.zeta_last, sub_zero]

end SkewClassInflation
