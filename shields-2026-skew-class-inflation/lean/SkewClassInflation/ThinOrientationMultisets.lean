/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinMateContraction
import Mathlib.Data.List.OfFn
import Mathlib.Data.Multiset.AddSub

/-!
# Exact residual endpoint and junction multisets

Formalizes `eq:orientation-multiset` of
`shields-2026-skew-class-inflation.tex`.  Actual total-contracted mate
functions produce the full row multiset.  Removing the common internal
merger rows leaves exactly both exterior endpoints and the stated
remaining junction multiplicity.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative

variable (B : ThinParameters)

/-- Every positive thin power has its complete literal endpoint/interior row word. -/
theorem innerPower_word (m : ℕ) (hm : 0 < m) :
    List.ofFn (B.innerPower m hm).r = B.a :: (List.replicate (m - 1) (B.a + B.b) ++ [B.b]) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [List.ofFn_succ, List.ofFn_succ']
  have hmid : (fun i : Fin s => (B.innerPower (s + 1) hm).r i.castSucc.succ) =
      (fun _ => B.a + B.b) := by
    funext i
    change B.powerRows (s + 1) i.castSucc.succ = B.a + B.b
    have hi := i.isLt
    simp only [powerRows, Fin.val_succ, Fin.val_castSucc]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hlast : (B.innerPower (s + 1) hm).r (Fin.last s).succ = B.b := by
    simp only [innerPower, powerRows, Fin.val_succ, Fin.val_last,
      ite_eq_right (by omega : s + 1 ≠ 0), ite_true]
  rw [hmid, hlast, List.ofFn_const]
  change B.a :: (List.replicate s (B.a + B.b)).concat B.b = _
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, List.concat_eq_append]

/-- The actual thin power row multiset retains both endpoints and every repeated merger. -/
theorem innerPower_rowMultiset (m : ℕ) (hm : 0 < m) :
    (B.innerPower m hm).rowMultiset =
      B.a ::ₘ B.b ::ₘ Multiset.replicate (m - 1) (B.a + B.b) := by
  rw [Gluing.Profile.rowMultiset, Fin.univ_val_map, B.innerPower_word m hm]
  change B.a ::ₘ (((List.replicate (m - 1) (B.a + B.b) ++ [B.b]) : List ℕ) : Multiset ℕ) = _
  rw [← Multiset.coe_add]
  change B.a ::ₘ (Multiset.replicate (m - 1) (B.a + B.b) + (B.b ::ₘ 0)) = _
  rw [Multiset.add_comm]
  simp only [Multiset.cons_add, zero_add]

/-- Removing the common interior multiplicity leaves precisely the displayed junction rows. -/
theorem innerPower_orientation_residual (M ℓ : ℕ) (hℓ : 0 < ℓ) (hℓM : ℓ ≤ M) :
    (B.innerPower M (by omega)).rowMultiset - Multiset.replicate (M - ℓ) (B.a + B.b) =
      B.a ::ₘ B.b ::ₘ Multiset.replicate (ℓ - 1) (B.a + B.b) := by
  have hs : M - 1 = (ℓ - 1) + (M - ℓ) := by omega
  rw [B.innerPower_rowMultiset, hs, Multiset.replicate_add,
    ← Multiset.cons_add, ← Multiset.cons_add, Multiset.add_sub_cancel_right]

/-- Every actual connected source mate supplies the exact residual multiset in the paper. -/
theorem arbitrary_mate_orientation_residual {M n : ℕ} (α : Composition M) (hM : 0 < M)
    (Q : Profile n)
    (he : Q.toBetaDiagram.schur = (B.diagram α hM).2.toBetaDiagram.schur) :
    (contractAllZeros Q).2.rowMultiset - Multiset.replicate (M - α.length) (B.a + B.b) =
      B.a ::ₘ B.b ::ₘ Multiset.replicate (α.length - 1) (B.a + B.b) := by
  have hcore := B.arbitrary_mate_total_contraction α hM Q he
  have hrows := (Gluing.Profile.rows_eq_of_schur_eq (by
    simpa only [Gluing.Profile.toBetaDiagram_schur] using hcore)).2
  rw [hrows]
  exact B.innerPower_orientation_residual M α.length (α.length_pos_of_pos hM) α.length_le

end SkewClassInflation.ThinParameters
