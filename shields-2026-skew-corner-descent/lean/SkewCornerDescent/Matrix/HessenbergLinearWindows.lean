/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic
import SkewCornerDescent.LinearWindows

/-!
# Literal internal interval starts

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Every eligible ordered endpoint pair has exactly one literal linear start. Equal
response values do not merge starts; at full window length the start set is empty.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Complete internal intervals of cost `m` are indexed by exactly `B - (m + 1)`
linear starts. This includes the full-length boundary with no internal start. -/
theorem hessenberg_internal_interval_sum {B m : ℕ} (hmB : m < B)
    {R : Type*} [AddCommMonoid R] (F : Fin (B + 1) → Fin (B + 1) → R) :
    (∑ i : Fin (B + 1), ∑ j : Fin (B + 1),
      if i.val ≤ j.val ∧ j.val - i.val = m ∧ 0 < i.val ∧ j.val < B then F i j else 0) =
    ∑ s : Fin (B - (m + 1)),
      F ⟨s.val + 1, by have := s.isLt; omega⟩
        ⟨s.val + m + 1, by have := s.isLt; omega⟩ := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_filter]
  apply Finset.sum_bij (fun p hp =>
    (⟨p.1.val - 1, by
      obtain ⟨_, h⟩ := Finset.mem_filter.mp hp
      omega⟩ : Fin (B - (m + 1))))
  · intro p hp
    exact Finset.mem_univ _
  · intro p hp q hq he
    have h := (Finset.mem_filter.mp hp).2
    have h' := (Finset.mem_filter.mp hq).2
    have hv := congrArg Fin.val he
    change p.1.val - 1 = q.1.val - 1 at hv
    apply Prod.ext <;> apply Fin.ext <;> omega
  · intro s _
    let i : Fin (B + 1) := ⟨s.val + 1, by have := s.isLt; omega⟩
    let j : Fin (B + 1) := ⟨s.val + m + 1, by have := s.isLt; omega⟩
    refine ⟨(i, j), Finset.mem_filter.mpr ⟨by simp, ?_⟩, ?_⟩
    · dsimp [i, j]
      have := s.isLt
      omega
    · apply Fin.ext
      dsimp [i]
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2
    congr 1 <;> apply Fin.ext
    · change p.1.val = p.1.val - 1 + 1
      omega
    · change p.2.val = p.1.val - 1 + m + 1
      omega

/-- A literal interval product is its full offset product, including both endpoints
and all repeated values. -/
theorem hessenberg_internal_interval_product {B m : ℕ} (hmB : m < B)
    {R : Type*} [CommMonoid R] (d : Fin (B + 1) → R)
    (s : Fin (B - (m + 1))) :
    (∏ k ∈ Finset.Icc (⟨s.val + 1, by have := s.isLt; omega⟩ : Fin (B + 1))
      ⟨s.val + m + 1, by have := s.isLt; omega⟩, d k) =
      ∏ a : Fin (m + 1), d ⟨s.val + a.val + 1, by have := s.isLt; have := a.isLt; omega⟩ := by
  classical
  apply Finset.prod_bij (fun k hk =>
    (⟨k.val - (s.val + 1), by
      obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hk
      change s.val + 1 ≤ k.val at hl
      change k.val ≤ s.val + m + 1 at hu
      omega⟩ : Fin (m + 1)))
  · intro k _
    exact Finset.mem_univ _
  · intro k hk l hl he
    obtain ⟨hklo, _⟩ := Finset.mem_Icc.mp hk
    obtain ⟨hllo, _⟩ := Finset.mem_Icc.mp hl
    change s.val + 1 ≤ k.val at hklo
    change s.val + 1 ≤ l.val at hllo
    have hv := congrArg Fin.val he
    change k.val - (s.val + 1) = l.val - (s.val + 1) at hv
    apply Fin.ext
    omega
  · intro a _
    let k : Fin (B + 1) := ⟨s.val + a.val + 1, by
      have := s.isLt
      have := a.isLt
      omega⟩
    refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · change s.val + 1 ≤ s.val + a.val + 1
      omega
    · change s.val + a.val + 1 ≤ s.val + m + 1
      have := a.isLt
      omega
    · apply Fin.ext
      dsimp [k]
      omega
  · intro k hk
    obtain ⟨hl, _⟩ := Finset.mem_Icc.mp hk
    change s.val + 1 ≤ k.val at hl
    congr 1
    apply Fin.ext
    change k.val = s.val + (k.val - (s.val + 1)) + 1
    omega

/-- The complete literal interval inverse products are the linear windows in the
internal diagonal word. The proof treats the zero-start full-length boundary exactly. -/
theorem hessenberg_internal_interval_inverse_windows {B m : ℕ} (hmB : m < B)
    {F : Type*} [Field F] (d : Fin (B + 1) → F) :
    (∑ s : Fin (B - (m + 1)),
      ∏ l ∈ Finset.Icc (⟨s.val + 1, by have := s.isLt; omega⟩ : Fin (B + 1))
        ⟨s.val + m + 1, by have := s.isLt; omega⟩, (d l)⁻¹) =
      linearInverseWindowSum
        (fun i : Fin (B - 1) => d ⟨i.val + 1, by have := i.isLt; omega⟩) (m + 1) := by
  classical
  cases B with
  | zero => omega
  | succ B =>
    simp only [Nat.succ_sub_one]
    unfold linearInverseWindowSum
    apply Finset.sum_congr rfl
    intro s _
    rw [hessenberg_internal_interval_product hmB]

end SkewCornerDescent.Matrix
