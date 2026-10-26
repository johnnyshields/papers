/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Faithful finite packets with one active response class

Supports `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
Indicator functions isolate actual response values and collapse the rational
support packet to one label.  Signed exponents and all original multiplicities
are retained; no response-product independence is assumed.
Sorry-free.
-/

namespace SkewCornerDescent
open scoped BigOperators

/-- A finite packet faithfully representing a single active class has exactly
one support label.  Indicator functions isolate each actual response value;
no product independence or unsigned-multiplicity assumption is used. -/
theorem single_active_packet_support {C I F : Type*} [Fintype C] [Field F] [CharZero F]
    (support : Finset I) (value : C → F) (classExponent : C → ℤ) (active : C)
    (response : I → F) (hinj : Function.Injective response) (e : I → ℤ)
    (hother : ∀ X, X ≠ active → classExponent X = 0)
    (hmem : ∀ i ∈ support, e i ≠ 0) (d : ℤ) (hd : d ≠ 0)
    (hdegree : ∑ i ∈ support, e i = d)
    (hsums : ∀ H : F → F, (∑ X : C, (classExponent X : F) * H (value X)) =
      ∑ i ∈ support, (e i : F) * H (response i)) :
    ∃ i, support = {i} ∧ e i = d ∧ response i = value active := by
  classical
  have hvalue (i : I) (hi : i ∈ support) : response i = value active := by
    by_contra hn
    let H : F → F := fun x => if x = response i then 1 else 0
    have hleft : (∑ X : C, (classExponent X : F) * H (value X)) = 0 := by
      have hsingle : (∑ X : C, (classExponent X : F) * H (value X)) =
          (classExponent active : F) * H (value active) := by
        apply Finset.sum_eq_single active
        · intro X _ hX
          rw [hother X hX, Int.cast_zero, zero_mul]
        · intro hnot
          exact (hnot (Finset.mem_univ active)).elim
      rw [hsingle]
      simp only [H, ite_eq_right (Ne.symm hn), mul_zero]
    have hright : (∑ j ∈ support, (e j : F) * H (response j)) = (e i : F) := by
      rw [Finset.sum_eq_single i]
      · simp only [H, ite_eq_left rfl, mul_one]
      · intro j _ hji
        have hne : response j ≠ response i := fun he => hji (hinj he)
        simp only [H, ite_eq_right hne, mul_zero]
      · intro hnot
        exact (hnot hi).elim
    have he := hsums H
    rw [hleft, hright] at he
    have hz : e i = 0 := by exact_mod_cast he.symm
    exact hmem i hi hz
  have hnonempty : support.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hz
    apply hd
    have he := hdegree
    rw [hz, Finset.sum_empty] at he
    exact he.symm
  obtain ⟨i, hi⟩ := hnonempty
  have hsupport : support = {i} := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      have he : j = i := hinj ((hvalue j hj).trans (hvalue i hi).symm)
      simpa only [Finset.mem_singleton] using he
    · intro hj
      exact (Finset.mem_singleton.mp hj).symm ▸ hi
  exact ⟨i, hsupport, by simpa only [hsupport, Finset.sum_singleton] using hdegree, hvalue i hi⟩

end SkewCornerDescent
