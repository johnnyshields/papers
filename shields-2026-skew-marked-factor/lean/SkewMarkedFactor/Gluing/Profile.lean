/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/Profile.lean
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Zify
import SkewMarkedFactor.Gluing.Tactics

/-!
# Profiles of connected diagrams and their beta lists

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`,
the paragraph on profiles before `lem:gluing-row-action`, and the arithmetic half of
`lem:gluing-row-action`).

A connected diagram with `n + 1` rows has a profile `(r; g)`: its row lengths and adjacent
overlaps minus one, top to bottom, with `0 ≤ g_i < min (r_i, r_{i+1})`.  This file defines the
type of valid profiles, their beta lists `ξ`, `ζ`, and proves that valid profiles correspond
bijectively to the pairs of beta lists (`Profile.equivBetaPair`).  It defines rotation and the
affine map `𝓛_{q,w}` (`Profile.lift`), and proves that `𝓛_{q,w}` is injective, commutes with
rotation, sends the beta lists to `qξ_i + w` and `qζ_i`, and has as image exactly the profiles
whose row lengths and overlaps minus one all lie in the residue `w` modulo `q`.

Profiles are indexed by `Fin (n + 1)` so that "at least one row" is built into the type; the
number of rows of `Profile n` is `n + 1`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

/-- The profile `(r; g)` of a connected diagram with `n + 1` rows: `r i` is the length of row `i`
and `g j` is the overlap minus one of rows `j` and `j + 1`, both read top to bottom, with
`0 ≤ g j < min (r j, r (j + 1))`.  The positivity of the row lengths is implied by the overlap
conditions when `n > 0` and is needed only for a single row. -/
structure Profile (n : ℕ) where
  /-- The row lengths, top to bottom. -/
  r : Fin (n + 1) → ℕ
  /-- The adjacent overlaps minus one, top to bottom. -/
  g : Fin n → ℕ
  /-- Every row is nonempty. -/
  r_pos : ∀ i, 0 < r i
  /-- The overlap with the row below is smaller than the row. -/
  g_lt_castSucc : ∀ j, g j < r j.castSucc
  /-- The overlap with the row above is smaller than the row. -/
  g_lt_succ : ∀ j, g j < r j.succ

namespace Profile

variable {n : ℕ}

@[ext]
theorem ext {P Q : Profile n} (hr : P.r = Q.r) (hg : P.g = Q.g) : P = Q := by
  cases P
  cases Q
  congr

/-! ### Beta lists -/

/-- The beta list `ζ`, determined by `ζ_{last} = 0` and `g_i = ξ_{i+1} - ζ_i`, `r_i = ξ_i - ζ_i`:
that is `ζ_i = ∑_{k ≥ i} (r_{k+1} - g_k)`. -/
def zeta (P : Profile n) (i : Fin (n + 1)) : ℤ :=
  ∑ k : Fin n, if i.val ≤ k.val then ((P.r k.succ : ℤ) - P.g k) else 0

/-- The beta list `ξ`, with `ξ_i = ζ_i + r_i`. -/
def xi (P : Profile n) (i : Fin (n + 1)) : ℤ := P.zeta i + P.r i

theorem zeta_last (P : Profile n) : P.zeta (Fin.last n) = 0 := by
  unfold zeta
  refine Finset.sum_eq_zero fun k _ => ?_
  have := k.isLt
  simp only [Fin.val_last]
  simp [show ¬ n ≤ k.val by omega]

theorem zeta_castSucc (P : Profile n) (j : Fin n) :
    P.zeta j.castSucc = P.zeta j.succ + P.r j.succ - P.g j := by
  unfold zeta
  have key : ∀ k : Fin n,
      (if (j.castSucc).val ≤ k.val then ((P.r k.succ : ℤ) - P.g k) else 0)
        = (if (j.succ).val ≤ k.val then ((P.r k.succ : ℤ) - P.g k) else 0)
          + (if k = j then ((P.r k.succ : ℤ) - P.g k) else 0) := by
    intro k
    by_cases h1 : j.val < k.val
    · have h3 : k ≠ j := fun h => by subst h; omega
      simp [show j.val ≤ k.val by omega, show j.val + 1 ≤ k.val by omega, h3]
    · by_cases h2 : k = j
      · subst h2
        simp
      · have : k.val < j.val := by
          have : k.val ≠ j.val := fun h => h2 (Fin.ext h)
          omega
        simp [show ¬ j.val ≤ k.val by omega, show ¬ j.val + 1 ≤ k.val by omega, h2]
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  ring

theorem xi_sub_zeta (P : Profile n) (i : Fin (n + 1)) : P.xi i - P.zeta i = P.r i := by
  simp [xi]

theorem xi_succ_sub_zeta_castSucc (P : Profile n) (j : Fin n) :
    P.xi j.succ - P.zeta j.castSucc = P.g j := by
  have := P.zeta_castSucc j
  simp only [xi]
  omega

/-- The beta list `ζ` is strictly decreasing. -/
theorem zeta_strictAnti (P : Profile n) : StrictAnti P.zeta := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro j
  have := P.zeta_castSucc j
  have := P.g_lt_succ j
  omega

/-- The beta list `ξ` is strictly decreasing. -/
theorem xi_strictAnti (P : Profile n) : StrictAnti P.xi := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro j
  have h1 := P.zeta_castSucc j
  have h2 := P.g_lt_castSucc j
  simp only [xi]
  omega

theorem zeta_nonneg (P : Profile n) (i : Fin (n + 1)) : 0 ≤ P.zeta i := by
  rw [← P.zeta_last]
  exact P.zeta_strictAnti.antitone (Fin.le_last i)

theorem xi_pos (P : Profile n) (i : Fin (n + 1)) : 0 < P.xi i := by
  have := P.zeta_nonneg i
  have := P.r_pos i
  simp only [xi]
  omega

theorem zeta_le_xi_succ (P : Profile n) (j : Fin n) : P.zeta j.castSucc ≤ P.xi j.succ := by
  have := P.xi_succ_sub_zeta_castSucc j
  omega

/-- The beta lists are determined by their defining equations: if `x`, `z` satisfy
`z_last = 0`, `r_i = x_i - z_i` and `g_i = x_{i+1} - z_i`, then they are the beta lists. -/
theorem eq_beta_of_equations (P : Profile n) {x z : Fin (n + 1) → ℤ}
    (hz : z (Fin.last n) = 0) (hr : ∀ i, x i - z i = P.r i)
    (hg : ∀ j : Fin n, x j.succ - z j.castSucc = P.g j) : x = P.xi ∧ z = P.zeta := by
  have hzeq : z = P.zeta := by
    funext i
    induction i using Fin.reverseInduction with
    | last => rw [hz, P.zeta_last]
    | cast j ih =>
      have h1 := hr j.succ
      have h2 := hg j
      have h3 := P.zeta_castSucc j
      omega
  refine ⟨?_, hzeq⟩
  funext i
  have := hr i
  have := P.xi_sub_zeta i
  rw [hzeq] at *
  omega

/-! ### The bijection between profiles and pairs of beta lists -/

/-- A pair of beta lists: `ξ` and `ζ` strictly decreasing, `ζ_last = 0`, `ζ_i ≤ ξ_{i+1}` (so
that `g_i ≥ 0`), and `ξ_last > 0` (so that the last row is nonempty). -/
structure BetaPair (n : ℕ) where
  /-- The list `ξ`. -/
  xi : Fin (n + 1) → ℤ
  /-- The list `ζ`. -/
  zeta : Fin (n + 1) → ℤ
  /-- `ξ` is strictly decreasing. -/
  xi_strictAnti : StrictAnti xi
  /-- `ζ` is strictly decreasing. -/
  zeta_strictAnti : StrictAnti zeta
  /-- `ζ` ends in zero. -/
  zeta_last : zeta (Fin.last n) = 0
  /-- Each overlap minus one is nonnegative. -/
  zeta_le_xi_succ : ∀ j : Fin n, zeta j.castSucc ≤ xi j.succ
  /-- The last row is nonempty. -/
  xi_last_pos : 0 < xi (Fin.last n)

/-- The beta lists of a profile. -/
def toBetaPair (P : Profile n) : BetaPair n where
  xi := P.xi
  zeta := P.zeta
  xi_strictAnti := P.xi_strictAnti
  zeta_strictAnti := P.zeta_strictAnti
  zeta_last := P.zeta_last
  zeta_le_xi_succ := P.zeta_le_xi_succ
  xi_last_pos := P.xi_pos _

theorem BetaPair.zeta_lt_xi (B : BetaPair n) (i : Fin (n + 1)) : B.zeta i < B.xi i := by
  induction i using Fin.lastCases with
  | last => rw [B.zeta_last]; exact B.xi_last_pos
  | cast j =>
    have h1 := B.zeta_le_xi_succ j
    have h2 : B.xi j.succ < B.xi j.castSucc := B.xi_strictAnti (Fin.castSucc_lt_succ)
    omega

/-- The profile with the given beta lists: `r_i = ξ_i - ζ_i` and `g_i = ξ_{i+1} - ζ_i`. -/
def ofBetaPair (B : BetaPair n) : Profile n where
  r i := (B.xi i - B.zeta i).toNat
  g j := (B.xi j.succ - B.zeta j.castSucc).toNat
  r_pos i := by have := B.zeta_lt_xi i; omega
  g_lt_castSucc j := by
    have h1 : B.xi j.succ < B.xi j.castSucc := B.xi_strictAnti (Fin.castSucc_lt_succ)
    have := B.zeta_le_xi_succ j
    omega
  g_lt_succ j := by
    have h1 : B.zeta j.succ < B.zeta j.castSucc := B.zeta_strictAnti (Fin.castSucc_lt_succ)
    have := B.zeta_le_xi_succ j
    omega

/-- **Valid profiles are in bijection with pairs of beta lists.** -/
def equivBetaPair : Profile n ≃ BetaPair n where
  toFun := toBetaPair
  invFun := ofBetaPair
  left_inv P := by
    refine Profile.ext (funext fun i => ?_) (funext fun j => ?_)
    · have := P.xi_sub_zeta i
      simp only [ofBetaPair, toBetaPair]
      omega
    · have := P.xi_succ_sub_zeta_castSucc j
      simp only [ofBetaPair, toBetaPair]
      omega
  right_inv B := by
    have hr : ∀ i, B.xi i - B.zeta i = ((ofBetaPair B).r i : ℤ) := fun i => by
      have := B.zeta_lt_xi i
      simp only [ofBetaPair]
      omega
    have hg : ∀ j : Fin n, B.xi j.succ - B.zeta j.castSucc = ((ofBetaPair B).g j : ℤ) :=
      fun j => by
        have := B.zeta_le_xi_succ j
        simp only [ofBetaPair]
        omega
    obtain ⟨h1, h2⟩ := (ofBetaPair B).eq_beta_of_equations B.zeta_last hr hg
    cases B
    simp only [toBetaPair, BetaPair.mk.injEq]
    exact ⟨h1.symm, h2.symm⟩

/-- The profile is determined by its beta lists. -/
theorem eq_of_beta_eq {P Q : Profile n} (hxi : P.xi = Q.xi) (hzeta : P.zeta = Q.zeta) :
    P = Q := by
  apply equivBetaPair.injective
  simp only [equivBetaPair, Equiv.coe_fn_mk, toBetaPair, BetaPair.mk.injEq]
  exact ⟨hxi, hzeta⟩

/-! ### Rotation -/

/-- Rotation of a profile: reverse both lists. -/
def rotate (P : Profile n) : Profile n where
  r i := P.r i.rev
  g j := P.g j.rev
  r_pos i := P.r_pos _
  g_lt_castSucc j := by
    rw [Fin.rev_castSucc]
    exact P.g_lt_succ _
  g_lt_succ j := by
    rw [Fin.rev_succ]
    exact P.g_lt_castSucc _

@[simp]
theorem rotate_rotate (P : Profile n) : P.rotate.rotate = P := by
  refine Profile.ext (funext fun i => ?_) (funext fun j => ?_) <;> simp [rotate]

/-- The beta lists of the rotation: `ξ*_i = ξ_0 - ζ_{n-i}` and `ζ*_i = ξ_0 - ξ_{n-i}`. -/
theorem xi_rotate_zeta_rotate (P : Profile n) :
    P.rotate.xi = (fun i => P.xi 0 - P.zeta i.rev) ∧
      P.rotate.zeta = (fun i => P.xi 0 - P.xi i.rev) := by
  have key := (P.rotate.eq_beta_of_equations
    (x := fun i => P.xi 0 - P.zeta i.rev) (z := fun i => P.xi 0 - P.xi i.rev) ?_ ?_ ?_)
  · exact ⟨key.1.symm, key.2.symm⟩
  · simp
  · intro i
    have := P.xi_sub_zeta i.rev
    simp only [rotate]
    omega
  · intro j
    have := P.xi_succ_sub_zeta_castSucc j.rev
    simp only [rotate, Fin.rev_castSucc, Fin.rev_succ]
    omega

theorem xi_rotate (P : Profile n) (i : Fin (n + 1)) : P.rotate.xi i = P.xi 0 - P.zeta i.rev :=
  congrFun P.xi_rotate_zeta_rotate.1 i

theorem zeta_rotate (P : Profile n) (i : Fin (n + 1)) :
    P.rotate.zeta i = P.xi 0 - P.xi i.rev :=
  congrFun P.xi_rotate_zeta_rotate.2 i

/-! ### The affine map `𝓛_{q,w}` -/

end Profile

/-- The parameters `q ≥ 2`, `0 ≤ w < q` of the affine profile map `𝓛_{q,w}` (the period and the
width of a row mark). -/
structure RowShift where
  /-- The period `q`. -/
  q : ℕ
  /-- The width `w`. -/
  w : ℕ
  /-- `q ≥ 2`. -/
  two_le_q : 2 ≤ q
  /-- `w < q`. -/
  w_lt_q : w < q

namespace Profile

variable {n : ℕ}

/-- The affine map `𝓛_{q,w}(r; g) = (q r + w; q g + w)`. -/
def lift (s : RowShift) (P : Profile n) : Profile n where
  r i := s.q * P.r i + s.w
  g j := s.q * P.g j + s.w
  r_pos i := by have := P.r_pos i; have := s.two_le_q; nlinarith
  g_lt_castSucc j := by
    have := P.g_lt_castSucc j
    have := s.two_le_q
    nlinarith
  g_lt_succ j := by
    have := P.g_lt_succ j
    have := s.two_le_q
    nlinarith

@[simp]
theorem lift_r (s : RowShift) (P : Profile n) (i : Fin (n + 1)) :
    (P.lift s).r i = s.q * P.r i + s.w := rfl

@[simp]
theorem lift_g (s : RowShift) (P : Profile n) (j : Fin n) :
    (P.lift s).g j = s.q * P.g j + s.w := rfl

theorem lift_injective (s : RowShift) : Function.Injective (lift s : Profile n → Profile n) := by
  intro P Q h
  have hq : 0 < s.q := by have := s.two_le_q; omega
  refine Profile.ext (funext fun i => ?_) (funext fun j => ?_)
  · have := congrFun (congrArg Profile.r h) i
    simp only [lift_r] at this
    exact Nat.eq_of_mul_eq_mul_left hq (by omega)
  · have := congrFun (congrArg Profile.g h) j
    simp only [lift_g] at this
    exact Nat.eq_of_mul_eq_mul_left hq (by omega)

/-- `𝓛_{q,w}` commutes with rotation. -/
theorem lift_rotate (s : RowShift) (P : Profile n) : (P.lift s).rotate = P.rotate.lift s := rfl

/-- `𝓛_{q,w}` sends the beta lists to `q ξ_i + w` and `q ζ_i`. -/
theorem xi_lift_zeta_lift (s : RowShift) (P : Profile n) :
    (P.lift s).xi = (fun i => (s.q : ℤ) * P.xi i + s.w) ∧
      (P.lift s).zeta = (fun i => (s.q : ℤ) * P.zeta i) := by
  have key := (P.lift s).eq_beta_of_equations
    (x := fun i => (s.q : ℤ) * P.xi i + s.w) (z := fun i => (s.q : ℤ) * P.zeta i) ?_ ?_ ?_
  · exact ⟨key.1.symm, key.2.symm⟩
  · simp [P.zeta_last]
  · intro i
    have := P.xi_sub_zeta i
    simp only [lift_r]
    push_cast
    linear_combination (s.q : ℤ) * this
  · intro j
    have := P.xi_succ_sub_zeta_castSucc j
    simp only [lift_g]
    push_cast
    linear_combination (s.q : ℤ) * this

theorem xi_lift (s : RowShift) (P : Profile n) (i : Fin (n + 1)) :
    (P.lift s).xi i = (s.q : ℤ) * P.xi i + s.w :=
  congrFun (xi_lift_zeta_lift s P).1 i

theorem zeta_lift (s : RowShift) (P : Profile n) (i : Fin (n + 1)) :
    (P.lift s).zeta i = (s.q : ℤ) * P.zeta i :=
  congrFun (xi_lift_zeta_lift s P).2 i

/-! ### The image of `𝓛_{q,w}` -/

/-- Every row length and every overlap minus one of `P` lies in the residue `w` modulo `q`. -/
def HasResidue (s : RowShift) (P : Profile n) : Prop :=
  (∀ i, P.r i % s.q = s.w) ∧ ∀ j, P.g j % s.q = s.w

theorem hasResidue_lift (s : RowShift) (P : Profile n) : (P.lift s).HasResidue s := by
  have hq : 0 < s.q := by have := s.two_le_q; omega
  refine ⟨fun i => ?_, fun j => ?_⟩ <;>
    simp only [lift_r, lift_g] <;>
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt s.w_lt_q]

theorem le_r_lift (s : RowShift) (P : Profile n) (i : Fin (n + 1)) : s.q ≤ (P.lift s).r i := by
  have := P.r_pos i
  simp only [lift_r]
  nlinarith

/-- With at least two rows, the residue condition already forces every row to have length at
least `q`: the overlap below a row is a residue-`w` number smaller than the row. -/
theorem le_r_of_hasResidue {s : RowShift} {P : Profile n} (h : P.HasResidue s) (hn : 0 < n)
    (i : Fin (n + 1)) : s.q ≤ P.r i := by
  have key : ∀ (m : ℕ) (a : ℕ), a % s.q = s.w → m % s.q = s.w → a < m → s.q ≤ m := by
    intro m a ha hm hlt
    have h1 := Nat.div_add_mod m s.q
    have h2 := Nat.div_add_mod a s.q
    rw [hm] at h1
    rw [ha] at h2
    by_contra hcon
    have : m / s.q = 0 := Nat.div_eq_of_lt (by omega)
    rw [this] at h1
    have : a / s.q = 0 := Nat.div_eq_of_lt (by omega)
    rw [this] at h2
    omega
  by_cases hi : i.val < n
  · exact key _ _ (h.2 ⟨i.val, hi⟩) (h.1 i) (P.g_lt_castSucc ⟨i.val, hi⟩)
  · have hi' : i = (⟨n - 1, by omega⟩ : Fin n).succ := Fin.ext (by simp; omega)
    rw [hi']
    exact key _ _ (h.2 ⟨n - 1, by omega⟩) (h.1 _) (P.g_lt_succ ⟨n - 1, by omega⟩)

/-- The divided profile `((r - w) / q; (g - w) / q)` of a profile with residue `w` modulo `q`
and all row lengths at least `q`. -/
def divide (s : RowShift) (P : Profile n) (h : P.HasResidue s) (hlen : ∀ i, s.q ≤ P.r i) :
    Profile n where
  r i := P.r i / s.q
  g j := P.g j / s.q
  r_pos i := Nat.div_pos (hlen i) (by have := s.two_le_q; omega)
  g_lt_castSucc j := by
    have hq := s.two_le_q
    have h1 := Nat.div_add_mod (P.r j.castSucc) s.q
    have h2 := Nat.div_add_mod (P.g j) s.q
    rw [h.1] at h1
    rw [h.2] at h2
    have := P.g_lt_castSucc j
    by_contra hcon
    push Not at hcon
    have : s.q * (P.r j.castSucc / s.q) ≤ s.q * (P.g j / s.q) := Nat.mul_le_mul_left _ hcon
    omega
  g_lt_succ j := by
    have hq := s.two_le_q
    have h1 := Nat.div_add_mod (P.r j.succ) s.q
    have h2 := Nat.div_add_mod (P.g j) s.q
    rw [h.1] at h1
    rw [h.2] at h2
    have := P.g_lt_succ j
    by_contra hcon
    push Not at hcon
    have : s.q * (P.r j.succ / s.q) ≤ s.q * (P.g j / s.q) := Nat.mul_le_mul_left _ hcon
    omega

theorem lift_divide (s : RowShift) (P : Profile n) (h : P.HasResidue s)
    (hlen : ∀ i, s.q ≤ P.r i) : (P.divide s h hlen).lift s = P := by
  refine Profile.ext (funext fun i => ?_) (funext fun j => ?_)
  · have := Nat.div_add_mod (P.r i) s.q
    rw [h.1] at this
    simp only [lift_r, divide]
    omega
  · have := Nat.div_add_mod (P.g j) s.q
    rw [h.2] at this
    simp only [lift_g, divide]
    omega

/-- **The image of `𝓛_{q,w}`** (arithmetic half of `lem:gluing-row-action`): a profile is
`𝓛_{q,w} D` exactly when all its row lengths and overlaps minus one lie in the residue `w`
modulo `q` and every row has length at least `q`.  The last condition is automatic from the
residue condition when there are at least two rows (`le_r_of_hasResidue`); for a single row it
excludes the length `w`. -/
theorem mem_range_lift_iff (s : RowShift) (P : Profile n) :
    P ∈ Set.range (lift s : Profile n → Profile n) ↔ P.HasResidue s ∧ ∀ i, s.q ≤ P.r i := by
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨hasResidue_lift s D, le_r_lift s D⟩
  · rintro ⟨h, hlen⟩
    exact ⟨P.divide s h hlen, lift_divide s P h hlen⟩

/-- For a profile with at least two rows, the image of `𝓛_{q,w}` is exactly the profiles whose
row lengths and overlaps minus one all lie in the residue `w` modulo `q`. -/
theorem mem_range_lift_iff_hasResidue (s : RowShift) (hn : 0 < n) (P : Profile n) :
    P ∈ Set.range (lift s : Profile n → Profile n) ↔ P.HasResidue s := by
  rw [mem_range_lift_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, le_r_of_hasResidue h hn⟩⟩

/-- The divided profile is unique: if `P = 𝓛_{q,w} D = 𝓛_{q,w} D'` then `D = D'`. -/
theorem divide_unique (s : RowShift) {D D' : Profile n} (h : D.lift s = D'.lift s) : D = D' :=
  lift_injective s h

/-- The divided beta lists: if `P = 𝓛_{q,w} D`, then the beta lists of `D` are
`(ξ_i - w) / q` and `ζ_i / q`, where `ξ`, `ζ` are the beta lists of `P`. -/
theorem xi_zeta_of_lift_eq (s : RowShift) {D P : Profile n} (h : D.lift s = P)
    (i : Fin (n + 1)) :
    D.xi i = (P.xi i - s.w) / s.q ∧ D.zeta i = P.zeta i / s.q := by
  have hq : (s.q : ℤ) ≠ 0 := by have := s.two_le_q; omega
  subst h
  rw [xi_lift, zeta_lift]
  refine ⟨?_, ?_⟩
  · rw [add_sub_cancel_right, Int.mul_ediv_cancel_left _ hq]
  · rw [Int.mul_ediv_cancel_left _ hq]

/-! ### Multisets of row lengths and overlaps -/

/-- The multiset of row lengths of a profile. -/
def rowMultiset (P : Profile n) : Multiset ℕ := Finset.univ.val.map P.r

/-- The multiset of adjacent overlaps minus one of a profile. -/
def gapMultiset (P : Profile n) : Multiset ℕ := Finset.univ.val.map P.g

theorem mem_rowMultiset {P : Profile n} {x : ℕ} : x ∈ P.rowMultiset ↔ ∃ i, P.r i = x := by
  simp only [rowMultiset, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]

theorem mem_gapMultiset {P : Profile n} {x : ℕ} : x ∈ P.gapMultiset ↔ ∃ j, P.g j = x := by
  simp only [gapMultiset, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]

theorem rowMultiset_lift (s : RowShift) (P : Profile n) :
    (P.lift s).rowMultiset = P.rowMultiset.map fun x => s.q * x + s.w := by
  rw [rowMultiset, rowMultiset, Multiset.map_map]
  rfl

theorem gapMultiset_lift (s : RowShift) (P : Profile n) :
    (P.lift s).gapMultiset = P.gapMultiset.map fun x => s.q * x + s.w := by
  rw [gapMultiset, gapMultiset, Multiset.map_map]
  rfl

end Profile

end SkewMarkedFactor.Gluing
