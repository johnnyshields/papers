/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.InactiveClassReplacement

/-!
# Finite inactive replacement preserves both original inventories

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
Any finite set of produced inactive constant masks can be replaced simultaneously by
nonzero units. The literal word, cyclic index set and complete window lengths are unchanged.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- Replace response coordinates, not occurrences in the word. -/
def replaceResponses {α R : Type*} [DecidableEq α]
    (S : Finset α) (response replacement : α → R) (a : α) : R :=
  if a ∈ S then replacement a else response a

/-- Inserting one class is the corresponding coordinate update. -/
theorem replaceResponses_insert {α R : Type*} [DecidableEq α]
    (S : Finset α) (response replacement : α → R) (a : α) :
    replaceResponses (insert a S) response replacement =
      Function.update (replaceResponses S response replacement) a (replacement a) := by
  funext Y
  by_cases hY : Y = a
  · subst Y
    simp only [replaceResponses, Finset.mem_insert_self, ite_true, Function.update_self]
  · simp only [replaceResponses, Finset.mem_insert, hY, false_or,
      Function.update_of_ne hY]

/-- Every nonzero inactive replacement preserves the complete short zero identity. -/
theorem shortDetector_replace_zero_iff {G α R : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [Field R]
    (word : G → α) (response replacement e : α → R) (step : G)
    (j prefixLength : ℕ) (start : G) (s m : R) (S : Finset α)
    (hresponse : ∀ a, response a ≠ 0)
    (hreplacement : ∀ a ∈ S, replacement a ≠ 0)
    (he : ∀ a ∈ S, e a = 0)
    (hcount : ∀ a ∈ S, ∀ i, windowSum (classMask word a) step j i =
      windowSum (classMask word a) step prefixLength start) :
    (s * (∑ i, (windowProduct (response ∘ word) step j i)⁻¹) -
      m * (windowProduct (response ∘ word) step prefixLength start)⁻¹ *
        (∑ Y, e Y * (response Y)⁻¹) = 0) ↔
    (s * (∑ i, (windowProduct (replaceResponses S response replacement ∘ word) step j i)⁻¹) -
      m * (windowProduct (replaceResponses S response replacement ∘ word)
        step prefixLength start)⁻¹ *
        (∑ Y, e Y * (replaceResponses S response replacement Y)⁻¹) = 0) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Function.comp_def, replaceResponses, Finset.notMem_empty, ite_false]
  | @insert a S ha ih =>
    have hS (Y : α) (hY : Y ∈ S) : Y ∈ insert a S := Finset.mem_insert_of_mem hY
    rw [ih (fun Y hY => hreplacement Y (hS Y hY))
      (fun Y hY => he Y (hS Y hY)) (fun Y hY => hcount Y (hS Y hY)),
      replaceResponses_insert]
    exact shortDetector_update_zero_iff word (replaceResponses S response replacement) e
      step j prefixLength (windowSum (classMask word a) step prefixLength start) start a
      (replacement a) s m
      (by simpa only [replaceResponses, ha, ite_false] using hresponse a)
      (hreplacement a (Finset.mem_insert_self a S))
      (he a (Finset.mem_insert_self a S))
      (hcount a (Finset.mem_insert_self a S)) rfl

/-- Every nonzero inactive replacement also preserves the complete forward zero identity. -/
theorem fullDetector_replace_zero_iff {α R : Type*}
    [Fintype α] [DecidableEq α] [Field R] {n : ℕ} [NeZero n]
    (word : ZMod n → α) (response replacement e : α → R)
    (m prefixLength k : ℕ) (scalar : R) (S : Finset α)
    (hresponse : ∀ a, response a ≠ 0)
    (hreplacement : ∀ a ∈ S, replacement a ≠ 0)
    (he : ∀ a ∈ S, e a = 0)
    (hcount : ∀ a ∈ S, ∀ i, windowSum (classMask word a) 1 m i =
      windowSum (classMask word a) 1 prefixLength 0) :
    (scalar * (windowProduct (response ∘ word) 1 n 0) ^ (k - 1) *
        windowProduct (response ∘ word) 1 prefixLength 0 -
      (∑ Y, e Y * (response Y)⁻¹) *
        (∑ i, windowProduct (response ∘ word) 1 ((k - 1) * n + m) i) = 0) ↔
    (scalar * (windowProduct (replaceResponses S response replacement ∘ word) 1 n 0) ^
        (k - 1) * windowProduct (replaceResponses S response replacement ∘ word)
          1 prefixLength 0 -
      (∑ Y, e Y * (replaceResponses S response replacement Y)⁻¹) *
        (∑ i, windowProduct (replaceResponses S response replacement ∘ word) 1
          ((k - 1) * n + m) i) = 0) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Function.comp_def, replaceResponses, Finset.notMem_empty, ite_false]
  | @insert a S ha ih =>
    have hS (Y : α) (hY : Y ∈ S) : Y ∈ insert a S := Finset.mem_insert_of_mem hY
    rw [ih (fun Y hY => hreplacement Y (hS Y hY))
      (fun Y hY => he Y (hS Y hY)) (fun Y hY => hcount Y (hS Y hY)),
      replaceResponses_insert]
    exact fullDetector_update_zero_iff word (replaceResponses S response replacement) e
      m prefixLength k (windowSum (classMask word a) 1 prefixLength 0) a
      (replacement a) scalar
      (by simpa only [replaceResponses, ha, ite_false] using hresponse a)
      (hreplacement a (Finset.mem_insert_self a S))
      (he a (Finset.mem_insert_self a S))
      (hcount a (Finset.mem_insert_self a S)) rfl

end SkewCornerDescent.CyclicWindows
