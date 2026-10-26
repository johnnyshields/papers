/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileMergeReadings

/-!
# Positional inverse of a full-profile endpoint merger

The local splitting step in `lem:total-contraction-inverse` of
`shields-2026-skew-class-inflation.tex`.  At a fixed row position,
the merged profile and one original endpoint determine both complete
profiles.  No numerical row labels are assumed distinct.  Sorry-free.
-/

namespace SkewClassInflation.Profile

open SkewJacobiNegative

/-- Literal right-profile equality transports a join across its dependent finite order. -/
theorem join_right_congr {n : ℕ} (P : Profile n) (D E : ConnectedProfile) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hD : d < D.2.r 0) (hE : d < E.2.r 0) (he : D = E) :
    (⟨n + D.1 + 1, join P D.2 d hP hD⟩ : ConnectedProfile) =
      ⟨n + E.1 + 1, join P E.2 d hP hE⟩ := by
  cases he
  rfl

/-- Literal left-profile equality transports a join across its dependent finite order. -/
theorem join_left_congr {m : ℕ} (D E : ConnectedProfile) (Q : Profile m) (d : ℕ)
    (hD : d < D.2.r (Fin.last D.1)) (hE : d < E.2.r (Fin.last E.1))
    (hQ : d < Q.r 0) (he : D = E) :
    (⟨D.1 + m + 1, join D.2 Q d hD hQ⟩ : ConnectedProfile) =
      ⟨E.1 + m + 1, join E.2 Q d hE hQ⟩ := by
  cases he
  rfl

/-- Literal right-profile equality transports a merger across its dependent finite order. -/
theorem merge_right_congr {n : ℕ} (P : Profile n) (D E : ConnectedProfile) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hD : d < D.2.r 0) (hE : d < E.2.r 0) (he : D = E) :
    (⟨n + D.1, merge P D.2 d hP hD⟩ : ConnectedProfile) =
      ⟨n + E.1, merge P E.2 d hP hE⟩ := by
  cases he
  rfl

/-- A fixed split position and one endpoint recover both actual profiles from a merger. -/
theorem merge_pair_injective {n m : ℕ} (P U : Profile n) (Q V : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0)
    (hU : d < U.r (Fin.last n)) (hV : d < V.r 0)
    (hlast : P.r (Fin.last n) = U.r (Fin.last n))
    (he : merge P Q d hP hQ = merge U V d hU hV) : P = U ∧ Q = V := by
  have hmidP := merge_joined_row P Q d hP hQ
  have hmidU := merge_joined_row U V d hU hV
  rw [he, hlast] at hmidP
  have hfirst : Q.r 0 = V.r 0 := by omega
  constructor
  · apply Gluing.Profile.ext
    · funext i
      by_cases hi : i.val = n
      · have hilast : i = Fin.last n := Fin.ext hi
        rw [hilast]
        exact hlast
      · let j : Fin n := ⟨i.val, by have := i.isLt; omega⟩
        have hj : j.castSucc = i := Fin.ext rfl
        have hp := merge_r_left P Q d hP hQ j
        have hu := merge_r_left U V d hU hV j
        rw [he] at hp
        rw [hj] at hp hu
        exact hp.symm.trans hu
    · funext j
      have hp := merge_g_left P Q d hP hQ j
      have hu := merge_g_left U V d hU hV j
      rw [he] at hp
      exact hp.symm.trans hu
  · apply Gluing.Profile.ext
    · funext i
      refine Fin.cases hfirst (fun j => ?_) i
      have hq := merge_r_right P Q d hP hQ j
      have hv := merge_r_right U V d hU hV j
      rw [he] at hq
      exact hq.symm.trans hv
    · funext j
      have hq := merge_g_right P Q d hP hQ j
      have hv := merge_g_right U V d hU hV j
      rw [he] at hq
      exact hq.symm.trans hv

end SkewClassInflation.Profile
