/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.Gluing.Profile
import SkewJacobiNegative.BetaDiagrams

/-!
# Additive inflation and connected deflation

Formalizes `eq:inflation`, `eq:profile-validity`, and the geometric part of
`cor:inflation-no-escape` in `shields-2026-skew-class-inflation.tex`.
Inflation adds to both profile words, leaves the column betas fixed, and
translates every row beta by the same amount.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- A connected row-and-overlap profile with `n + 1` nonempty rows. -/
abbrev Profile := SkewJacobiNegative.Gluing.Profile

namespace Profile

variable {n : ℕ}

/-- Add the same amount to every row length and every adjacent overlap. -/
def inflate (t : ℕ) (P : Profile n) : Profile n where
  r i := P.r i + t
  g j := P.g j + t
  r_pos i := by have := P.r_pos i; omega
  g_lt_castSucc j := Nat.add_lt_add_right (P.g_lt_castSucc j) t
  g_lt_succ j := Nat.add_lt_add_right (P.g_lt_succ j) t

@[simp] theorem inflate_r (t : ℕ) (P : Profile n) (i : Fin (n + 1)) :
    (inflate t P).r i = P.r i + t := rfl

@[simp] theorem inflate_g (t : ℕ) (P : Profile n) (j : Fin n) :
    (inflate t P).g j = P.g j + t := rfl

@[simp] theorem inflate_zero (P : Profile n) : inflate 0 P = P := by
  apply SkewJacobiNegative.Gluing.Profile.ext <;> funext i <;> simp

/-- Successive inflation is addition of the parameters. -/
theorem inflate_add (s t : ℕ) (P : Profile n) :
    inflate s (inflate t P) = inflate (s + t) P := by
  apply SkewJacobiNegative.Gluing.Profile.ext <;> funext i <;>
    simp [Nat.add_assoc, Nat.add_comm]

/-- No two literal profiles are identified by inflation. -/
theorem inflate_injective (t : ℕ) : Function.Injective (inflate t : Profile n → Profile n) := by
  intro P Q h
  apply SkewJacobiNegative.Gluing.Profile.ext
  · funext i
    have hi := congrArg (fun R : Profile n => R.r i) h
    exact Nat.add_right_cancel hi
  · funext j
    have hj := congrArg (fun R : Profile n => R.g j) h
    exact Nat.add_right_cancel hj

/-- Inflation commutes with reversal of the entire ordered profile. -/
theorem inflate_rotate (t : ℕ) (P : Profile n) :
    (inflate t P).rotate = inflate t P.rotate := rfl

/-- The unchanged differences between successive beta entries retain the column list. -/
@[simp] theorem zeta_inflate (t : ℕ) (P : Profile n) (i : Fin (n + 1)) :
    (inflate t P).zeta i = P.zeta i := by
  simp [SkewJacobiNegative.Gluing.Profile.zeta, Nat.cast_add]

/-- Every row beta increases by exactly the inflation parameter. -/
@[simp] theorem xi_inflate (t : ℕ) (P : Profile n) (i : Fin (n + 1)) :
    (inflate t P).xi i = P.xi i + t := by
  simp [SkewJacobiNegative.Gluing.Profile.xi, Nat.cast_add, add_assoc]

/-- All full Jacobi--Trudi indices shift, including negative indices and units. -/
theorem index_inflate (t : ℕ) (P : Profile n) (i j : Fin (n + 1)) :
    (inflate t P).xi i - (inflate t P).zeta j = P.xi i - P.zeta j + t := by
  simp only [xi_inflate, zeta_inflate]
  ring

/-- The exact image condition for connected deflation. -/
def CanDeflate (t : ℕ) (P : Profile n) : Prop :=
  (∀ i, t < P.r i) ∧ ∀ j, t ≤ P.g j

/-- Subtract a parameter only when every resulting row is positive and every gap nonnegative. -/
def deflate (t : ℕ) (P : Profile n) (h : CanDeflate t P) : Profile n where
  r i := P.r i - t
  g j := P.g j - t
  r_pos i := Nat.sub_pos_of_lt (h.1 i)
  g_lt_castSucc j := by
    have := P.g_lt_castSucc j
    have := h.2 j
    omega
  g_lt_succ j := by
    have := P.g_lt_succ j
    have := h.2 j
    omega

/-- Every inflated connected profile has a connected deflation. -/
theorem canDeflate_inflate (t : ℕ) (P : Profile n) : CanDeflate t (inflate t P) := by
  constructor
  · intro i; have := P.r_pos i; simp only [inflate_r]; omega
  · intro j; simp

@[simp] theorem deflate_inflate (t : ℕ) (P : Profile n) :
    deflate t (inflate t P) (canDeflate_inflate t P) = P := by
  apply SkewJacobiNegative.Gluing.Profile.ext <;> funext i <;>
    simp [deflate]

@[simp] theorem inflate_deflate (t : ℕ) (P : Profile n) (h : CanDeflate t P) :
    inflate t (deflate t P h) = P := by
  apply SkewJacobiNegative.Gluing.Profile.ext
  · funext i; have := h.1 i; simp only [inflate_r, deflate]; omega
  · funext j; have := h.2 j; simp only [inflate_g, deflate]; omega

/-- Membership in the inflation image is exactly the explicit connected-deflation condition. -/
theorem exists_inflate_iff (t : ℕ) (P : Profile n) :
    (∃ Q, inflate t Q = P) ↔ CanDeflate t P := by
  constructor
  · rintro ⟨Q, rfl⟩; exact canDeflate_inflate t Q
  · intro h; exact ⟨deflate t P h, inflate_deflate t P h⟩

end Profile
end SkewClassInflation
