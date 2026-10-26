/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ConsecutiveMatrixWindows

/-!
# Exact interior and exterior overlap starts

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A length-two interval meeting a longer interval is either inside it or
crosses exactly one endpoint. The actual finite exterior starts are retained.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Valid starts of a long interval and an overlapping adjacent pair. -/
abbrev IntervalOverlapStarts (N d : ℕ) :=
  {p : Fin (N - d) × Fin (N - 1) // p.1.val ≤ p.2.val + 1 ∧ p.2.val ≤ p.1.val + d}

/-- Interior pair starts, then left-exterior and right-exterior starts, enumerate
all overlaps exactly once. In particular the two exterior charges are distinct. -/
noncomputable def intervalOverlapStartsEquiv (N d : ℕ) (hd : 0 < d) :
    (Fin (N - d) × Fin d) ⊕ (Fin (N - d - 1) ⊕ Fin (N - d - 1)) ≃
      IntervalOverlapStarts N d := by
  let f : (Fin (N - d) × Fin d) ⊕ (Fin (N - d - 1) ⊕ Fin (N - d - 1)) →
      IntervalOverlapStarts N d := fun p => match p with
    | .inl (s, t) => ⟨(s, ⟨s.val + t.val, by have := s.isLt; have := t.isLt; omega⟩),
        by dsimp only; have := t.isLt; omega⟩
    | .inr (.inl s) => ⟨(⟨s.val + 1, by have := s.isLt; omega⟩,
        ⟨s.val, by have := s.isLt; omega⟩), by dsimp only; omega⟩
    | .inr (.inr s) => ⟨(⟨s.val, by have := s.isLt; omega⟩,
        ⟨s.val + d, by have := s.isLt; omega⟩), by dsimp only; omega⟩
  apply Equiv.ofBijective f
  constructor
  · rintro (⟨x, t⟩ | (x | x)) (⟨y, u⟩ | (y | y)) h
    all_goals
      have hx := congrArg (fun p : IntervalOverlapStarts N d => p.val.1.val) h
      have hy := congrArg (fun p : IntervalOverlapStarts N d => p.val.2.val) h
      dsimp only [f] at hx hy
    · have hxy : x = y := Fin.ext hx
      have htu : t = u := Fin.ext (by omega)
      cases hxy
      cases htu
      rfl
    · exfalso
      omega
    · exfalso
      have := t.isLt
      omega
    · exfalso
      omega
    · exact congrArg (fun k => Sum.inr (Sum.inl k)) (Fin.ext hy)
    · exfalso
      omega
    · exfalso
      have := u.isLt
      omega
    · exfalso
      omega
    · exact congrArg (fun k => Sum.inr (Sum.inr k)) (Fin.ext hx)
  · intro p
    have hbound := p.property
    have hs := p.val.1.isLt
    have ht := p.val.2.isLt
    by_cases hleft : p.val.2.val + 1 = p.val.1.val
    · refine ⟨.inr (.inl ⟨p.val.2.val, by omega⟩), ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact Fin.ext hleft
      · exact Fin.ext rfl
    · by_cases hright : p.val.2.val = p.val.1.val + d
      · refine ⟨.inr (.inr ⟨p.val.1.val, by omega⟩), ?_⟩
        apply Subtype.ext
        apply Prod.ext
        · exact Fin.ext rfl
        · exact Fin.ext hright.symm
      · refine ⟨.inl (p.val.1, ⟨p.val.2.val - p.val.1.val, by omega⟩), ?_⟩
        apply Subtype.ext
        apply Prod.ext
        · exact Fin.ext rfl
        · apply Fin.ext
          change p.val.1.val + (p.val.2.val - p.val.1.val) = p.val.2.val
          omega

/-- Exact finite overlap sums split into internal pairs and the two genuine
exterior contributions. All three start sets include their empty boundaries. -/
theorem interval_overlap_start_sum {N d : ℕ} (hd : 0 < d)
    {R : Type*} [AddCommMonoid R] (F : Fin (N - d) → Fin (N - 1) → R) :
    (∑ s : Fin (N - d), ∑ k : Fin (N - 1),
      if s.val ≤ k.val + 1 ∧ k.val ≤ s.val + d then F s k else 0) =
      (∑ s : Fin (N - d), ∑ t : Fin d,
        F s ⟨s.val + t.val, by have := s.isLt; have := t.isLt; omega⟩) +
      (∑ s : Fin (N - d - 1),
        F ⟨s.val + 1, by have := s.isLt; omega⟩ ⟨s.val, by have := s.isLt; omega⟩) +
      (∑ s : Fin (N - d - 1),
        F ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val + d, by have := s.isLt; omega⟩) := by
  classical
  let pred := fun p : Fin (N - d) × Fin (N - 1) =>
    p.1.val ≤ p.2.val + 1 ∧ p.2.val ≤ p.1.val + d
  have hsub : (∑ p : IntervalOverlapStarts N d, F p.val.1 p.val.2) =
      ∑ p ∈ Finset.univ.filter pred, F p.1 p.2 := by
    exact (Finset.sum_subtype (p := pred) (Finset.univ.filter pred)
      (fun p => by simp) (fun p => F p.1 p.2)).symm
  let G : (Fin (N - d) × Fin d) ⊕ (Fin (N - d - 1) ⊕ Fin (N - d - 1)) → R :=
    fun p => match p with
      | .inl (s, t) => F s ⟨s.val + t.val, by have := s.isLt; have := t.isLt; omega⟩
      | .inr (.inl s) =>
        F ⟨s.val + 1, by have := s.isLt; omega⟩ ⟨s.val, by have := s.isLt; omega⟩
      | .inr (.inr s) =>
        F ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val + d, by have := s.isLt; omega⟩
  have he := Fintype.sum_equiv (intervalOverlapStartsEquiv N d hd) G
    (fun p => F p.val.1 p.val.2) (by rintro (⟨s, t⟩ | (s | s)) <;> rfl)
  calc
    _ = ∑ p ∈ Finset.univ.filter pred, F p.1 p.2 := by
      simp only [Finset.sum_filter, Fintype.sum_prod_type, pred]
    _ = ∑ p : IntervalOverlapStarts N d, F p.val.1 p.val.2 := hsub.symm
    _ = _ := by
      rw [← he]
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, G, add_assoc]

end SkewCornerDescent.Matrix
