/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileMergeInverse
import SkewClassInflation.SaturationPowerMerge
import SkewClassInflation.SaturationRibbonReduction

/-!
# Recovering both sides of a fixed full-power split

The local positional step of `lem:total-contraction-inverse` in
`shields-2026-skew-class-inflation.tex`.  A component's actual row count
locates the split; its unordered endpoint pair fixes the one merged row.
No one-copy component rigidity is assumed.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- A fixed literal total power and the first component's endpoints recover both actual blocks. -/
theorem merged_power_inverse {j n M : ℕ} (hj : 0 < j) (hM : 0 < M)
    (L : Profile (j * A.k)) (C : Profile n)
    (hL : ∀ i, A.d < L.r i) (hC : ∀ i, A.d < C.r i)
    (hends : (L.r 0 ::ₘ L.r (Fin.last (j * A.k)) ::ₘ 0 : Multiset ℕ) =
      A.r 0 ::ₘ A.r (Fin.last A.k) ::ₘ 0)
    (he : (⟨j * A.k + n, Profile.merge L C A.d (hL _) (hC _)⟩ : ConnectedProfile) =
      ⟨M * A.k, A.power M hM⟩) :
    ∃ t : ℕ, ∃ ht : 0 < t, M = j + t ∧ L = A.power j hj ∧
      (⟨n, C⟩ : ConnectedProfile) = ⟨t * A.k, A.power t ht⟩ := by
  have hjk : 0 < j * A.k := Nat.mul_pos hj A.k_pos
  have hfirstCore := congrArg (fun D : ConnectedProfile => D.2.r 0) he
  change (Profile.merge L C A.d (hL _) (hC _)).r 0 = (A.power M hM).r 0 at hfirstCore
  rw [A.power_first] at hfirstCore
  have hleft := Profile.merge_r_left L C A.d (hL _) (hC _) (⟨0, hjk⟩ : Fin (j * A.k))
  change (Profile.merge L C A.d (hL _) (hC _)).r 0 = L.r 0 at hleft
  have hLf : L.r 0 = A.r 0 := hleft.symm.trans hfirstCore
  have hLl : L.r (Fin.last (j * A.k)) = A.r (Fin.last A.k) := by
    rw [hLf] at hends
    simpa only [Multiset.cons_inj_right, Multiset.cons_inj_left] using hends
  have hn : 0 < n := by
    by_contra hnot
    have hn0 : n = 0 := by omega
    subst n
    have hlastCore := congrArg (fun D : ConnectedProfile => D.2.r (Fin.last D.1)) he
    change (Profile.merge L C A.d (hL _) (hC _)).r (Fin.last (j * A.k + 0)) =
      (A.power M hM).r (Fin.last (M * A.k)) at hlastCore
    rw [A.power_last] at hlastCore
    have hmid := Profile.merge_joined_row L C A.d (hL _) (hC _)
    have hidx : (⟨j * A.k, by omega⟩ : Fin (j * A.k + 0 + 1)) =
        Fin.last (j * A.k + 0) := Fin.ext rfl
    rw [hidx, hlastCore, hLl] at hmid
    have hbound := hC 0
    omega
  have hsize := congrArg Sigma.fst he
  change j * A.k + n = M * A.k at hsize
  have hjM : j < M := by
    by_contra he
    have hle := Nat.mul_le_mul_right A.k (show M ≤ j by omega)
    omega
  obtain ⟨t, ht, hMt⟩ : ∃ t, 0 < t ∧ M = j + t :=
    ⟨M - j, by omega, by omega⟩
  subst M
  have hnt : n = t * A.k := by rw [Nat.add_mul] at hsize; omega
  subst n
  have href := A.merge_powers j t hj ht
  have hmerge : Profile.merge L C A.d (hL _) (hC _) =
      Profile.merge (A.power j hj) (A.power t ht) A.d
        (A.power_rows_above_seam j hj _) (A.power_rows_above_seam t ht _) :=
    eq_of_heq (Sigma.mk.inj (he.trans href.symm)).2
  obtain ⟨hleft, hright⟩ := Profile.merge_pair_injective L (A.power j hj) C (A.power t ht) A.d
    (hL _) (hC _) (A.power_rows_above_seam j hj _) (A.power_rows_above_seam t ht _)
    (hLl.trans (A.power_last j hj).symm) hmerge
  exact ⟨t, ht, rfl, hleft, congrArg (fun P : Profile (t * A.k) =>
    (⟨t * A.k, P⟩ : ConnectedProfile)) hright⟩

/-- Actual component equality supplies both the split position and its unordered endpoints. -/
theorem merged_power_inverse_of_function {j l n M : ℕ} (hj : 0 < j) (hM : 0 < M)
    (L : Profile l) (C : Profile n)
    (hL : ∀ i, A.d < L.r i) (hC : ∀ i, A.d < C.r i)
    (hf : L.toBetaDiagram.schur = (A.power j hj).toBetaDiagram.schur)
    (he : (⟨l + n, Profile.merge L C A.d (hL _) (hC _)⟩ : ConnectedProfile) =
      ⟨M * A.k, A.power M hM⟩) :
    ∃ t : ℕ, ∃ ht : 0 < t, M = j + t ∧
      (⟨l, L⟩ : ConnectedProfile) = ⟨j * A.k, A.power j hj⟩ ∧
      (⟨n, C⟩ : ConnectedProfile) = ⟨t * A.k, A.power t ht⟩ := by
  have hl := Nat.succ.inj
    (L.toBetaDiagram.row_count_of_schur_eq (A.power j hj).toBetaDiagram hf)
  change l = j * A.k at hl
  subst l
  obtain ⟨t, ht, hM, hleft, hright⟩ := A.merged_power_inverse hj hM L C hL hC
    (A.power_mate_endpoints j hj L hf) he
  exact ⟨t, ht, hM, congrArg (fun P : Profile (j * A.k) =>
    (⟨j * A.k, P⟩ : ConnectedProfile)) hleft, hright⟩

end SkewClassInflation.SaturationInner
