/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalAffineJets
import SkewCornerDescent.Matrix.SignedNormalProducts

/-!
# Affine first-fresh jets of full signed rational defects

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`). Full
products, powers, and signed denominator inverses preserve affine first-fresh
jets. This is formal-series algebra; the actual original fraction producers
retain their separate regular-unit certificates. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F : Type*} [Field F]

/-- A whole lower series has a constant affine fresh coefficient. -/
theorem jetsAffineOver_of_coeff_mem (S : Subfield F) (x : F) (p : PowerSeries F) (h : ℕ)
    (hp : ∀ n, PowerSeries.coeff n p ∈ S) : jetsAffineOver S x p h :=
  ⟨fun n _ => hp n, affineOver_of_mem S x (hp h)⟩

/-- A genuine lower constant contributes no protected generator at any order. -/
theorem jetsAffineOver_C (S : Subfield F) (x : F) {a : F} (ha : a ∈ S) (h : ℕ) :
    jetsAffineOver S x (PowerSeries.C a) h := by
  apply jetsAffineOver_of_coeff_mem
  intro n
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact S.zero_mem

/-- Addition preserves the entire earlier lower jet and affine fresh coefficient. -/
theorem jetsAffineOver_add (S : Subfield F) (x : F) {p q : PowerSeries F} {h : ℕ}
    (hp : jetsAffineOver S x p h) (hq : jetsAffineOver S x q h) :
    jetsAffineOver S x (p + q) h := by
  constructor
  · intro n hn
    rw [map_add]
    exact S.add_mem (hp.1 n hn) (hq.1 n hn)
  · rw [map_add]
    exact affineOver_add S x hp.2 hq.2

/-- Negation retains both lower coefficients of the affine fresh jet. -/
theorem jetsAffineOver_neg (S : Subfield F) (x : F) {p : PowerSeries F} {h : ℕ}
    (hp : jetsAffineOver S x p h) : jetsAffineOver S x (-p) h := by
  simpa only [neg_one_zsmul] using jetsAffineOver_zsmul S x hp (-1)

/-- Subtraction of full original series preserves first-fresh affineness. -/
theorem jetsAffineOver_sub (S : Subfield F) (x : F) {p q : PowerSeries F} {h : ℕ}
    (hp : jetsAffineOver S x p h) (hq : jetsAffineOver S x q h) :
    jetsAffineOver S x (p - q) h := by
  rw [sub_eq_add_neg]
  exact jetsAffineOver_add S x hp (jetsAffineOver_neg S x hq)

/-- Positive powers at positive normal order contain at most one fresh factor. -/
theorem jetsAffineOver_pow (S : Subfield F) (x : F) {p : PowerSeries F} {h : ℕ}
    (hh : 0 < h) (hp : jetsAffineOver S x p h) (d : ℕ) :
    jetsAffineOver S x (p ^ d) h := by
  induction d with
  | zero => simpa only [pow_zero, map_one] using jetsAffineOver_C S x S.one_mem h
  | succ d ih =>
    rw [pow_succ]
    exact jetsAffineOver_mul S x hh ih hp

/-- Every full finite product retains its earlier lower and first-fresh affine jet. -/
theorem jetsAffineOver_prod {ι : Type*} (S : Subfield F) (x : F) (s : Finset ι)
    (p : ι → PowerSeries F) {h : ℕ} (hh : 0 < h)
    (hp : ∀ i ∈ s, jetsAffineOver S x (p i) h) :
    jetsAffineOver S x (∏ i ∈ s, p i) h := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, map_one] using jetsAffineOver_C S x S.one_mem h
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact jetsAffineOver_mul S x hh (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

/-- Signed integer multiplicities retain full inverse denominator jets. -/
theorem jetsAffineOver_signedNormalProduct {ι : Type*} (S : Subfield F) (x : F)
    (s : Finset ι) (p : ι → PowerSeries F) (e : ι → ℤ) {h : ℕ} (hh : 0 < h)
    (hp : ∀ i ∈ s, jetsAffineOver S x (p i) h) :
    jetsAffineOver S x (signedNormalProduct s p e) h := by
  unfold signedNormalProduct
  apply jetsAffineOver_mul S x hh
  · exact jetsAffineOver_prod S x s _ hh
      (fun i hi => jetsAffineOver_pow S x hh (hp i hi) _)
  · exact jetsAffineOver_inv S x hh (jetsAffineOver_prod S x s _ hh
      (fun i hi => jetsAffineOver_pow S x hh (hp i hi) _))

/-- The whole original rational defect has an affine first-fresh coefficient when
its complete three source series do. No denominator is replaced by its residue. -/
theorem fullRationalDefect_jets_affine {ι : Type*} (S : Subfield F) (x : F)
    (s : Finset ι) (α : ι → F) (e : ι → ℤ) (ε : F)
    (f E β : PowerSeries F) (a b h : ℕ) (hh : 0 < h)
    (hε : ε ∈ S) (hα : ∀ i ∈ s, α i ∈ S)
    (hf : jetsAffineOver S x f h) (hE : jetsAffineOver S x E h)
    (hβ : jetsAffineOver S x β h) :
    jetsAffineOver S x
      (f ^ a * (E * f⁻¹ ^ 2) ^ b - PowerSeries.C ε *
        signedNormalProduct s (fun i => β * f⁻¹ ^ 2 - PowerSeries.C (α i)) e) h := by
  have hinv := jetsAffineOver_pow S x hh (jetsAffineOver_inv S x hh hf) 2
  apply jetsAffineOver_sub S x
  · exact jetsAffineOver_mul S x hh (jetsAffineOver_pow S x hh hf a)
      (jetsAffineOver_pow S x hh (jetsAffineOver_mul S x hh hE hinv) b)
  · apply jetsAffineOver_mul S x hh (jetsAffineOver_C S x hε h)
    exact jetsAffineOver_signedNormalProduct S x s _ e hh (fun i hi =>
      jetsAffineOver_sub S x (jetsAffineOver_mul S x hh hβ hinv)
        (jetsAffineOver_C S x (hα i hi) h))

end SkewCornerDescent.Matrix
