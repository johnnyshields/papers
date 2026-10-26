/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.NestedStep
import SkewRibbonCoarsenings.TriangleIdentity

/-!
# The top step of the nested marked identity

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:detector` (`thm:nested`): the
labeled count `K` of the list `𝐚 = (a, y_{L-1}, …, y_0, r, s, z)` is the chain sum of the cut
weights (`K_detList`); the only proper subset sums on the `d`-grid are those of `{a}` and its
complement; and, by the antichain contraction, `ΔK = v(a) 𝓙_a(y_{L-1}, …, r, s, z)`
(`delta_K_eq`).  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset Nested

section Top

variable {n : ℕ} {S S' : Finset ℕ} {d e L : ℕ} {p : ℕ → ℕ} {a r s z : ℕ} {y : ℕ → ℕ}

namespace NestedData

variable (D : NestedData n S S' d e L p a r s z y)
include D

lemma detList_pos (i : Fin (L + 4)) : 0 < detList L a r s z y i := by
  unfold detList
  split_ifs with h0 h1 h2 h3
  · exact D.a_pos
  · apply Nat.pos_of_ne_zero
    intro h
    have hk : L - i.val < L := by omega
    exact D.ndvd_y _ hk (by rw [h]; exact dvd_zero _)
  · apply Nat.pos_of_ne_zero
    intro h
    exact D.ndvd_r (by rw [h]; exact dvd_zero _)
  · apply Nat.pos_of_ne_zero
    intro h
    exact D.ndvd_s (by rw [h]; exact dvd_zero _)
  · apply Nat.pos_of_ne_zero
    intro h
    exact D.ndvd_z (by rw [h]; exact dvd_zero _)

variable (h : NormalizedSetting n S S' d e)
include h

lemma sum_total [NeZero n] : ∑ i, detList L a r s z y i = n := by
  rw [sum_univ]; exact (D.layers h).sum_lab

/-- Every proper nonempty subset of the labels has a sum strictly between `0` and `n`. -/
lemma sum_proper [NeZero n] {X : Finset (Fin (L + 4))} (hne : X.Nonempty) (hX : X ≠ Finset.univ) :
    0 < ∑ i ∈ X, detList L a r s z y i ∧ ∑ i ∈ X, detList L a r s z y i < n := by
  constructor
  · exact Finset.sum_pos (fun i _ => D.detList_pos i) hne
  · rw [← D.sum_total h, ← Finset.sum_sdiff (Finset.subset_univ X) (f := detList L a r s z y)]
    have : (Finset.univ \ X).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hs
      exact hX (Finset.eq_univ_of_forall fun i => hs (Finset.mem_univ i))
    have := Finset.sum_pos (fun i _ => D.detList_pos i) this (f := detList L a r s z y)
    omega

/-- `eq:K` for the labeled list of `thm:nested`: the labeled count is the chain sum of the cut
weights `b(∑_{i ∈ I} 𝐚_i)`. -/
lemma K_detList [NeZero n] {S₀ : Finset ℕ} :
    (K S₀ (detList L a r s z y) : ℤ) =
      chainSum (fun X : Finset (Fin (L + 4)) =>
        cutInd n S₀ ((∑ i ∈ X, detList L a r s z y i : ℕ) : ZMod n)) ∅ Finset.univ := by
  rw [K_eq_chainSum]
  apply chainSum_congr (Finset.empty_subset _)
  intro X h1 h2
  have hne : X.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (Finset.ssubset_iff_subset_ne.mp h1).2.symm
  have hX : X ≠ Finset.univ := (Finset.ssubset_iff_subset_ne.mp h2).2
  have hlt := (D.sum_proper h hne hX).2
  simp only [cutWeight, cutInd, ZMod.val_natCast_of_lt hlt]

omit D in
/-- The two cut weights agree at every vertex whose sum is off the `d`-grid. -/
lemma cutInd_eq_of_ndvd [NeZero n] {t : ℕ} (hd : ¬ d ∣ t) :
    cutInd n S (t : ZMod n) = cutInd n S' (t : ZMod n) := by
  have := vFun_eq_zero_of_ndvd h hd
  unfold vFun at this
  omega

/-- The proper nonempty vertices carrying a different weight for `b` and `c` are `{a}` and its
complement. -/
lemma agree [NeZero n] {X : Finset (Fin (L + 4))} (hne : X.Nonempty) (hX : X ≠ Finset.univ)
    (h1 : X ≠ {idxA L}) (h2 : X ≠ Finset.univ.erase (idxA L)) :
    cutInd n S ((∑ i ∈ X, detList L a r s z y i : ℕ) : ZMod n) =
      cutInd n S' ((∑ i ∈ X, detList L a r s z y i : ℕ) : ZMod n) := by
  apply cutInd_eq_of_ndvd h
  intro hd
  have := (D.layers h).grid_univ hne hX ((D.p_dvd_d h le_rfl).trans hd)
  rcases this with h' | h'
  · exact h1 h'
  · exact h2 h'

/-- The sum over the complement of `a` is `n - a`. -/
lemma sum_erase_idxA [NeZero n] :
    ∑ i ∈ (Finset.univ : Finset (Fin (L + 4))).erase (idxA L), detList L a r s z y i = n - a := by
  have h1 := Finset.add_sum_erase (Finset.univ : Finset (Fin (L + 4)))
    (detList L a r s z y) (Finset.mem_univ (idxA L))
  rw [detList_idxA, D.sum_total h] at h1
  omega

omit h in
lemma a_le_n [NeZero n] : a ≤ n := by
  have := D.sum_eq; omega

/-- The top step of `thm:nested`: the antichain identity with the two exceptional vertices `{a}`
and its complement gives `ΔK = v(a) 𝓙_a(y_{L-1}, …, y_0, r, s, z)` (the second display of the
proof), in the chain-sum form `JJ` over the positions `Jset L L` of all labels but `a`. -/
theorem delta_K_eq [NeZero n] :
    (K S (detList L a r s z y) : ℤ) - (K S' (detList L a r s z y) : ℤ) =
      vFun n S S' (a : ZMod n) *
        JJ n S (detList L a r s z y) a (Jset L L) := by
  rw [D.K_detList h (S₀ := S), D.K_detList h (S₀ := S')]
  have hv_odd : vFun n S S' (-(a : ZMod n)) = - vFun n S S' (a : ZMod n) :=
    vFun_odd h.tau_eq _
  have hne : ((Finset.univ : Finset (Fin (L + 4))).erase (idxA L)).Nonempty :=
    ⟨rIdx L, by simp [rIdx, idxA, Fin.ext_iff]⟩
  have key := chainSum_contraction (Finset.mem_univ (idxA L)) hne
    (F' := fun X : Finset (Fin (L + 4)) =>
      cutInd n S ((∑ i ∈ X, detList L a r s z y i : ℕ) : ZMod n))
    (F := fun X : Finset (Fin (L + 4)) =>
      cutInd n S' ((∑ i ∈ X, detList L a r s z y i : ℕ) : ZMod n))
    (vFun n S S' (a : ZMod n))
    (fun X h1 h2 h3 h4 => by
      have hne' : X.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (Finset.ssubset_iff_subset_ne.mp h1).2.symm
      exact D.agree h hne' h2.ne h3 h4)
    (by simp [vFun, detList_idxA])
    (by
      rw [D.sum_erase_idxA h, Nat.cast_sub D.a_le_n, ZMod.natCast_self, zero_sub]
      have := hv_odd
      unfold vFun at this ⊢
      linarith)
  rw [key]
  congr 1
  unfold JJ
  rw [Jset_top]
  have hsub : ∀ X : Finset (Fin (L + 4)), ∅ ⊂ X → X ⊂ (Finset.univ : Finset (Fin (L + 4))).erase (idxA L) →
      X.Nonempty ∧ idxA L ∉ X ∧ X ⊂ Finset.univ := by
    intro X h1 h2
    exact ⟨Finset.nonempty_iff_ne_empty.mpr (Finset.ssubset_iff_subset_ne.mp h1).2.symm,
      fun hh => (Finset.notMem_erase (idxA L) Finset.univ) (h2.subset hh),
      h2.trans_subset (Finset.erase_subset _ _)⟩
  have hs : ∀ X : Finset (Fin (L + 4)), idxA L ∉ X →
      ∑ i ∈ insert (idxA L) X, detList L a r s z y i = a + ∑ i ∈ X, detList L a r s z y i := by
    intro X hX
    rw [Finset.sum_insert hX, detList_idxA]
  congr 1
  · apply chainSum_congr (Finset.empty_subset _)
    intro X h1 h2
    obtain ⟨hne', hnotin, hXu⟩ := hsub X h1 h2
    have hXe : X ≠ (Finset.univ : Finset (Fin (L + 4))).erase (idxA L) := h2.ne
    have hag := (D.agree h (X := insert (idxA L) X) (Finset.insert_nonempty _ _) ?_ ?_ ?_).symm
    · rw [hs X hnotin] at hag ⊢
      exact hag
    · intro hh
      apply hXe
      ext i
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hi hia; exact hnotin (hia ▸ hi)
      · intro hi
        have : i ∈ insert (idxA L) X := hh ▸ Finset.mem_univ i
        rcases Finset.mem_insert.mp this with h' | h'
        · exact absurd h' hi
        · exact h'
    · intro hh
      obtain ⟨i, hi⟩ := hne'
      have : i ∈ ({idxA L} : Finset (Fin (L + 4))) := hh ▸ Finset.mem_insert_of_mem hi
      exact hnotin (Finset.mem_singleton.mp this ▸ hi)
    · intro hh
      have : idxA L ∈ (Finset.univ : Finset (Fin (L + 4))).erase (idxA L) :=
        hh ▸ Finset.mem_insert_self _ _
      simp at this
  · apply chainSum_congr (Finset.empty_subset _)
    intro X h1 h2
    obtain ⟨hne', hnotin, hXu⟩ := hsub X h1 h2
    exact (D.agree h hne' hXu.ne (fun hh => hnotin (hh ▸ Finset.mem_singleton_self _))
      h2.ne).symm

end NestedData

end Top

end SkewRibbonCoarsenings
