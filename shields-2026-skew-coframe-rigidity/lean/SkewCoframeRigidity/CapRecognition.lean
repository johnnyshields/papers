/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.CapRecognition.Formula

/-!
# Weak-cap recognition and absolute flags

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Weak caps and absolute flags»
(`lem:cap-recognition`).  Work in the joint polynomial ring `J = ℚ[z, h_1, h_2, …]`, realized as
`MvPolynomial (Option ℕ+) ℚ` with `z = X none` and `h_k = X (some k)`.  A `WeakCap r` is a pair of
lists `X_1 > ⋯ > X_r > 0` and `Y_1 > ⋯ > Y_r > 0` with `X_i ≥ Y_i`.  With `A = (h_{X_i - Y_j})`,
`C = det A` and `b = (h_{X_i})`, the numerator is `N_A = C - (z^{Y_j}) adj(A) b` and the whole
rational coframe is `g_A = N_A / C`.

* `WeakCap.numerator_irreducible`: for a nonempty cap, `N_A` is irreducible in `J`.
* `WeakCap.ratio_injective`: `g_A` determines `X` and `Y`, including units and equal labels.
* `WeakCap.ratio_empty`: the empty cap has `g_A = 1`.

Sorry-free.
-/

namespace SkewCoframeRigidity.CapRecognition

open SkewCofactorIndependence

namespace WeakCap

variable {r : ℕ}

/-- The whole rational coframe `g_A = N_A / C` of a weak cap, in the fraction field of the joint
polynomial ring. -/
noncomputable def ratio (c : WeakCap r) : FractionRing J :=
  algebraMap J (FractionRing J) c.numerator / algebraMap J (FractionRing J) (ι c.detA)

/-- For a nonempty cap, `N_A` is irreducible in the joint polynomial ring. -/
theorem numerator_irreducible (c : WeakCap (r + 1)) : Irreducible c.numerator := by
  rw [c.numerator_eq_num]
  exact c.num_irreducible

/-- The empty cap has `g_A = 1`. -/
theorem ratio_empty (c : WeakCap 0) : c.ratio = 1 := by
  unfold ratio
  rw [numerator_eq_num, num_zero, detA_zero]
  simp

/-- The coframe determines the number of rows and the flags `X`, `Y`, including units and equal
labels. -/
theorem ratio_injective {r r' : ℕ} (c : WeakCap r) (c' : WeakCap r') (h : c.ratio = c'.ratio) :
    ∃ e : r = r', ∀ i : Fin r, c'.X (Fin.cast e i) = c.X i ∧ c'.Y (Fin.cast e i) = c.Y i := by
  unfold ratio at h
  rw [numerator_eq_num, numerator_eq_num] at h
  have hc := cross_mul_of_ratio_eq ((map_ne_zero_iff _ ι_injective).mpr c.detA_ne_zero)
    ((map_ne_zero_iff _ ι_injective).mpr c'.detA_ne_zero) h
  obtain ⟨e, he⟩ := eq_of_cross c c' hc
  subst e
  exact ⟨rfl, fun i => ⟨by rw [← he]; rfl, by rw [← he]; rfl⟩⟩

/-- Two weak caps with the same number of rows and the same coframe coincide. -/
theorem ratio_injective_same {c c' : WeakCap r} (h : c.ratio = c'.ratio) : c = c' := by
  obtain ⟨e, he⟩ := ratio_injective c c' h
  exact ext' (funext fun i => (he i).1.symm) (funext fun i => (he i).2.symm)

/-- The coframe determines the number of rows. -/
theorem ratio_length_eq {r r' : ℕ} (c : WeakCap r) (c' : WeakCap r') (h : c.ratio = c'.ratio) :
    r = r' := (ratio_injective c c' h).1

end WeakCap

end SkewCoframeRigidity.CapRecognition
