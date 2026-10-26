/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.DilationGeometry
import SkewCofactorIndependence.DisjointAlphabet

/-!
# Quadratic return polynomials

The actual `Q_lambda(b,a)` preceding `sec:dilation`, its reflection criterion
used in `lem:endpoint-normalization`, and the nondivisible return alphabet in
`eq:offgrid-relation`.
-/

noncomputable section
namespace SkewCofactorIndependence
open scoped BigOperators
open StrictTriangularPaths

/-- The actual finite positive-edge return quadratic. -/
def returnQuadratic (c : ℤ → ℚ) (b a : ℤ) : CompleteRing :=
  ∑ z ∈ Finset.Ioo b a, c z • (complete (a - z) * complete (z - b))

/-- Equality of two degree-two exponent vectors is equality of unordered pairs. -/
theorem pairExponent_eq_iff {α : Type*} (a b c d : α) :
    Finsupp.single a 1 + Finsupp.single b 1 =
      (Finsupp.single c 1 + Finsupp.single d 1 : α →₀ ℕ) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  constructor
  · intro h
    by_cases hac : a = c
    · subst c
      have he := add_left_cancel h
      have hb := congrArg (fun f : α →₀ ℕ => f b) he
      by_cases hbd : b = d
      · exact Or.inl ⟨rfl, hbd⟩
      · simp [hbd] at hb
    · by_cases had : a = d
      · subst d
        rw [add_comm (Finsupp.single c 1)] at h
        have he := add_left_cancel h
        have hb := congrArg (fun f : α →₀ ℕ => f b) he
        by_cases hbc : b = c
        · exact Or.inr ⟨rfl, hbc⟩
        · simp [hbc] at hb
      · have ha := congrArg (fun f : α →₀ ℕ => f a) h
        have hca : c ≠ a := Ne.symm hac
        have hda : d ≠ a := Ne.symm had
        by_cases hab : a = b
        · subst b
          simp [hca, hda] at ha
        · simp [hca, hda, Ne.symm hab] at ha
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact add_comm _ _

/-- The monomial exponent of a positive return pair. -/
def returnExponent (b a z : ℤ) (hz : b < z ∧ z < a) : ℕ+ →₀ ℕ :=
  Finsupp.single ⟨(a - z).toNat, by omega⟩ 1 +
    Finsupp.single ⟨(z - b).toNat, by omega⟩ 1

/-- No extra collisions occur among the return monomials. -/
theorem returnExponent_eq_iff (b a z w : ℤ)
    (hz : b < z ∧ z < a) (hw : b < w ∧ w < a) :
    returnExponent b a z hz = returnExponent b a w hw ↔
      w = z ∨ w = a + b - z := by
  let az : ℕ+ := ⟨(a - z).toNat, by omega⟩
  let bz : ℕ+ := ⟨(z - b).toNat, by omega⟩
  let aw : ℕ+ := ⟨(a - w).toNat, by omega⟩
  let bw : ℕ+ := ⟨(w - b).toNat, by omega⟩
  change (Finsupp.single az 1 + Finsupp.single bz 1 =
      (Finsupp.single aw 1 + Finsupp.single bw 1 : ℕ+ →₀ ℕ)) ↔ _
  rw [pairExponent_eq_iff az bz aw bw]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · have hh := congrArg (fun j : ℕ+ => (j : ℕ)) h₁
      change (a - z).toNat = (a - w).toNat at hh
      left
      omega
    · have hh := congrArg (fun j : ℕ+ => (j : ℕ)) h₁
      change (a - z).toNat = (w - b).toNat at hh
      right
      omega
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, rfl⟩
    · right
      constructor
      · apply Subtype.ext
        change (a - z).toNat = (a + b - z - b).toNat
        congr 1
        ring
      · apply Subtype.ext
        change (z - b).toNat = (a - (a + b - z)).toNat
        congr 1
        ring

/-- Coefficient extraction includes the midpoint without a spurious factor of two. -/
theorem returnQuadratic_coeff (c : ℤ → ℚ) (b a z : ℤ)
    (hz : b < z ∧ z < a) :
    (returnQuadratic c b a).coeff (returnExponent b a z hz) =
      if 2 * z = a + b then c z else c z + c (a + b - z) := by
  classical
  have hr : a + b - z ∈ Finset.Ioo b a := by simp; omega
  have hz' : z ∈ Finset.Ioo b a := by simpa using hz
  have term (w : ℤ) (hw : w ∈ Finset.Ioo b a) :
      (c w • (complete (a - w) * complete (w - b))).coeff
          (returnExponent b a z hz) =
        if w = z ∨ w = a + b - z then c w else 0 := by
    have hw' := Finset.mem_Ioo.mp hw
    have hm : c w • (complete (a - w) * complete (w - b)) =
        MvPolynomial.monomial (returnExponent b a w hw') (c w) := by
      rw [complete_of_pos (by omega), complete_of_pos (by omega)]
      let aw : ℕ+ := ⟨(a - w).toNat, by omega⟩
      let bw : ℕ+ := ⟨(w - b).toNat, by omega⟩
      change c w •
        ((MvPolynomial.monomial (Finsupp.single aw 1) 1 : CompleteRing) *
          MvPolynomial.monomial (Finsupp.single bw 1) 1) = _
      rw [MvPolynomial.monomial_mul_monomial, MvPolynomial.smul_monomial]
      simp only [smul_eq_mul, mul_one]
      rfl
    rw [hm, MvPolynomial.coeff_monomial]
    have he : returnExponent b a w hw' = returnExponent b a z hz ↔
        w = z ∨ w = a + b - z :=
      eq_comm.trans (returnExponent_eq_iff b a z w hz hw')
    simp only [he]
  rw [returnQuadratic, MvPolynomial.coeff_sum]
  simp_rw [Finset.sum_congr rfl (fun w hw => term w hw)]
  by_cases hmid : 2 * z = a + b
  · have he : a + b - z = z := by omega
    simp [hmid, he, hz']
  · have he : z ≠ a + b - z := by omega
    have hs : (∑ w ∈ Finset.Ioo b a,
        if w = z ∨ w = a + b - z then c w else 0) =
        c z + c (a + b - z) := by
      simp_rw [show ∀ w : ℤ, (if w = z ∨ w = a + b - z then c w else 0) =
        (if w = z then c z else 0) +
          (if w = a + b - z then c (a + b - z) else 0) by
            intro w; by_cases h₁ : w = z <;> by_cases h₂ : w = a + b - z <;>
              simp_all]
      simp [Finset.sum_add_distrib, hz', hr]
    simpa [hmid] using hs

/-- Vanishing of the actual quadratic is exactly odd reflection on its interval. -/
theorem returnQuadratic_eq_zero_iff (c : ℤ → ℚ) (b a : ℤ) :
    returnQuadratic c b a = 0 ↔
      ∀ z, b < z → z < a → c z + c (a + b - z) = 0 := by
  classical
  constructor
  · intro h z hb ha
    have he := returnQuadratic_coeff c b a z ⟨hb, ha⟩
    rw [h] at he
    by_cases hm : 2 * z = a + b
    · have hr : a + b - z = z := by omega
      simp only [hm, ite_true, AddMonoidAlgebra.coeff_zero] at he
      simp [hr, ← he]
    · simpa [hm] using he.symm
  · intro hc
    have hs : returnQuadratic c b a = -returnQuadratic c b a := by
      unfold returnQuadratic
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_bij (fun z _ => a + b - z)
      · intro z hz
        simp only [Finset.mem_Ioo] at hz ⊢
        omega
      · intro z hz w hw he
        omega
      · intro w hw
        refine ⟨a + b - w, ?_, ?_⟩
        · simp only [Finset.mem_Ioo] at hw ⊢; omega
        · omega
      · intro z hz
        have hz' := Finset.mem_Ioo.mp hz
        have h := hc z hz'.1 hz'.2
        have hneg : c z = -c (a + b - z) := by linarith
        rw [hneg, neg_smul, neg_inj]
        congr 1
        have h₁ : a - (a + b - z) = z - b := by ring
        have h₂ : a + b - z - b = a - z := by ring
        rw [h₁, h₂, mul_comm]
    have ht : (2 : CompleteRing) * returnQuadratic c b a = 0 := by
      linear_combination hs
    exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

/-- A nonpositive edge has no quadratic terms. -/
theorem returnQuadratic_of_le (c : ℤ → ℚ) {a b : ℤ} (h : a ≤ b) :
    returnQuadratic c b a = 0 := by
  simp [returnQuadratic, Finset.Ioo_eq_empty_of_le h]

/-- The return pair belongs to the off-grid alphabet when both endpoints are on-grid. -/
def offGridReturnIndex (t : ℕ+) (a z : ℤ) (ha : z < (t : ℕ) * a)
    (hz : ¬ (t : ℤ) ∣ z) : OffGridIndex t :=
  ⟨⟨((t : ℕ) * a - z).toNat, by omega⟩, by
    intro hd
    have hi' : (t : ℤ) ∣ (((t : ℕ) * a - z).toNat : ℤ) := by exact_mod_cast hd
    have he : (((t : ℕ) * a - z).toNat : ℤ) = (t : ℕ) * a - z :=
      Int.toNat_of_nonneg (by omega)
    have hi : (t : ℤ) ∣ (t : ℕ) * a - z := he ▸ hi'
    apply hz
    have hm : (t : ℤ) ∣ (t : ℕ) * a := dvd_mul_right _ _
    have hh := dvd_sub hm hi
    simpa using hh⟩

/-- The off-grid coefficient polynomial is built from the two actual return indices. -/
def offGridQuadratic (t : ℕ+) (c : ℤ → ℚ) (b a : ℤ) :
    MvPolynomial (OffGridIndex t) ℚ :=
  ∑ z ∈ (Finset.Ioo ((t : ℕ) * b) ((t : ℕ) * a)).attach,
    if hz : ¬ (t : ℤ) ∣ z.val then
      c z.val • (MvPolynomial.X (offGridReturnIndex t a z.val
        (Finset.mem_Ioo.mp z.property).2 hz) *
      MvPolynomial.X (offGridReturnIndex t (-b) (-z.val)
        (by have h := (Finset.mem_Ioo.mp z.property).1; linarith)
        (by simpa using hz)))
    else 0

set_option backward.isDefEq.respectTransparency false in
/-- An extension zero on the grid identifies the alphabet polynomial with its real quadratic. -/
theorem offGridEmbed_quadratic (t : ℕ+) (c : ℤ → ℚ) (b a : ℤ)
    (hc : ∀ z, (t : ℤ) ∣ z → c z = 0) :
    offGridEmbed t (offGridQuadratic t c b a) =
      returnQuadratic c ((t : ℕ) * b) ((t : ℕ) * a) := by
  classical
  let I := Finset.Ioo ((t : ℕ) * b) ((t : ℕ) * a)
  unfold returnQuadratic
  rw [← Finset.sum_coe_sort]
  change offGridEmbed t (∑ z : ↥I,
    if hz : ¬ (t : ℤ) ∣ z.val then
      c z.val • (MvPolynomial.X (offGridReturnIndex t a z.val
        (Finset.mem_Ioo.mp z.property).2 hz) *
        MvPolynomial.X (offGridReturnIndex t (-b) (-z.val)
          (by have h := (Finset.mem_Ioo.mp z.property).1; linarith)
          (by simpa using hz)))
    else 0) =
    ∑ z : ↥I, c z.val • (complete ((t : ℕ) * a - z.val) *
      complete (z.val - (t : ℕ) * b))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hd : (t : ℤ) ∣ z.val
  · simp [hd, hc z.val hd]
  · have hb := (Finset.mem_Ioo.mp z.property).1
    have ha := (Finset.mem_Ioo.mp z.property).2
    rw [dite_eq_left hd, map_smul, map_mul]
    have hxA : offGridEmbed t (MvPolynomial.X (offGridReturnIndex t a z.val ha hd)) =
        complete ((t : ℕ) * a - z.val) := by
      change MvPolynomial.rename Subtype.val (MvPolynomial.X _) = _
      rw [MvPolynomial.rename_X, complete_of_pos (by omega)]
      rfl
    have hxB : offGridEmbed t (MvPolynomial.X
        (offGridReturnIndex t (-b) (-z.val)
          (by simpa only [mul_neg, neg_lt_neg_iff] using hb) (by simpa using hd))) =
        complete (z.val - (t : ℕ) * b) := by
      change MvPolynomial.rename Subtype.val (MvPolynomial.X _) = _
      rw [MvPolynomial.rename_X, complete_of_pos (by omega)]
      congr 1
      apply Subtype.ext
      change ((t : ℕ) * (-b) - (-z.val)).toNat = (z.val - (t : ℕ) * b).toNat
      congr 1
      ring
    rw [hxA, hxB]

end SkewCofactorIndependence
