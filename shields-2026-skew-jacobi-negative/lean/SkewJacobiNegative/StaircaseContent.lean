/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircasePrimitives
import SkewJacobiNegative.StaircaseSafeCuts
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Monomial content of actual staircase restrictions

The monomial gcd and the collision-compatible interval identities used in
`lem:staircase-content` and `eq:staircase-four-expansion` of
`shields-2026-skew-jacobi-negative.tex`.
-/

namespace SkewJacobiNegative.Staircase

open Gluing HessenbergExpansion
open scoped BigOperators
/- Concrete positive indices and finite-coordinate casts are definitionally
equal across the inherited complete-generator representations. -/
set_option backward.isDefEq.respectTransparency false

@[simp] theorem eraseGenerator_X (v w : ℕ+) :
    eraseGenerator v (MvPolynomial.X w) =
      if w = v then (0 : CompleteRing) else MvPolynomial.X w :=
  MvPolynomial.eval₂Hom_X' _ _ _

theorem fullGenerator_int_coe {n : ℕ} (P : Profile n) :
    ((fullGenerator P).val : ℤ) = fullIndex P := by
  change ((P.toBetaDiagram.largestLabel.toNat : ℕ) : ℤ) = P.toBetaDiagram.largestLabel
  exact Int.toNat_of_nonneg P.toBetaDiagram.largestLabel_pos.le
theorem pnat_eq_of_int_coe_eq {v w : ℕ+}
    (h : (v.val : ℤ) = (w.val : ℤ)) : v = w := by
  apply Subtype.ext
  change v.val = w.val
  omega
@[simp] theorem pderiv_two (v : ℕ+) :
    MvPolynomial.pderiv v (2 : CompleteRing) = 0 :=
  (MvPolynomial.pderiv v).map_natCast 2

/-- A nonzero iterated coefficient proves nonvanishing without expanding the
polynomial when the zero hypothesis is substituted. -/
theorem ne_zero_of_iterated_pderiv_eq (u v : ℕ+) (p c : CompleteRing)
    (h : MvPolynomial.pderiv u (MvPolynomial.pderiv v p) = c)
    (hc : c ≠ 0) : p ≠ 0 := by
  intro hp
  have hz : MvPolynomial.pderiv u (MvPolynomial.pderiv v p) = 0 := by
    rw [hp, map_zero, map_zero]
  exact hc (h.symm.trans hz)




/-- Exponents of all positive internal gap variables, counting coincident gaps. -/
noncomputable def gapExponent {n : ℕ} (P : Profile n)
    (hp : ∀ j, 0 < P.g j) : ℕ+ →₀ ℕ :=
  ∑ j : Fin n, Finsupp.single (⟨P.g j, hp j⟩ : ℕ+) 1

/-- The gap product is a coefficient-one monomial even when gap values repeat. -/
theorem gapMonomial_eq_monomial {n : ℕ} (P : Profile n)
    (hp : ∀ j, 0 < P.g j) :
    gapMonomial P = MvPolynomial.monomial (gapExponent P hp) 1 := by
  classical
  rw [gapExponent, MvPolynomial.monomial_sum_one]
  apply Finset.prod_congr rfl
  intro j _
  simpa only [MvPolynomial.X, PNat.mk_coe] using complete_nat (⟨P.g j, hp j⟩ : ℕ+)

/-- Gcd content is a monomial up to a nonzero rational unit; no nonmonomial
factor can be hidden in a supplied content field. -/
theorem content_is_monomial {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    ∃ e : ℕ+ →₀ ℕ, ∃ u : ℚ,
      e ≤ gapExponent P hP.gap_pos ∧ IsUnit u ∧
        content q P = MvPolynomial.monomial e u := by
  apply (MvPolynomial.dvd_monomial_one_iff_exists).mp
  rw [← gapMonomial_eq_monomial P hP.gap_pos]
  exact gcd_dvd_left _ _

/-- The exponent of the actual gcd; its coefficient is discarded only as a unit. -/
noncomputable def contentExponent {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : ℕ+ →₀ ℕ :=
  Classical.choose (content_is_monomial hP)

noncomputable def contentUnit {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : ℚ :=
  Classical.choose (Classical.choose_spec (content_is_monomial hP))

theorem content_monomial_spec {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    contentExponent hP ≤ gapExponent P hP.gap_pos ∧ IsUnit (contentUnit hP) ∧
      content q P = MvPolynomial.monomial (contentExponent hP) (contentUnit hP) :=
  Classical.choose_spec (Classical.choose_spec (content_is_monomial hP))

/-- Monic gap content of the actual restricted determinant. -/
noncomputable def monicContent {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : CompleteRing :=
  MvPolynomial.monomial (contentExponent hP) 1

/-- Primitive paired with the monic content, before determinant sign normalization. -/
noncomputable def monicPrimitive {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : CompleteRing :=
  MvPolynomial.C (contentUnit hP) * primitive q P

/-- Actual factorization with monic monomial content. -/
theorem restriction_eq_monicContent_mul {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    restriction q P = monicContent hP * monicPrimitive hP := by
  rw [restriction_eq_content_mul_primitive hP, (content_monomial_spec hP).2.2]
  unfold monicContent monicPrimitive
  rw [← mul_assoc, mul_comm (MvPolynomial.monomial _ 1) (MvPolynomial.C _),
    MvPolynomial.C_mul_monomial, mul_one]

/-- Removing only the rational unit does not change irreducibility. -/
theorem monicPrimitive_irreducible {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : Irreducible (monicPrimitive hP) := by
  have hu : IsUnit (MvPolynomial.C (contentUnit hP) : CompleteRing) :=
    (content_monomial_spec hP).2.1.map MvPolynomial.C
  exact (associated_unit_mul_left (primitive q P) _ hu).irreducible_iff.mpr
    (primitive_irreducible hP)

/-- A variable in the content is an actual internal gap value, including ties. -/
theorem variable_dvd_content_is_gap {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (v : ℕ+)
    (hv : MvPolynomial.X v ∣ monicContent hP) : ∃ j, P.g j = v.val := by
  classical
  have hv' : contentExponent hP v ≠ 0 := by
    simpa only [monicContent, MvPolynomial.X_dvd_monomial, one_ne_zero, false_or] using hv
  have he := (content_monomial_spec hP).1 v
  have hg : gapExponent P hP.gap_pos v ≠ 0 := by omega
  by_contra hn
  push_neg at hn
  apply hg
  simp only [gapExponent, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hne : (⟨P.g j, hP.gap_pos j⟩ : ℕ+) ≠ v := by
    intro h
    exact hn j (congrArg Subtype.val h)
  simp [Finsupp.single_apply, hne]

/-- A cut generator can never occur in the extracted gap content. -/
theorem cut_variable_not_dvd_content {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : ¬ MvPolynomial.X q ∣ monicContent hP := by
  intro hd
  obtain ⟨j, hj⟩ := variable_dvd_content_is_gap hP q hd
  exact hP.gap_ne j hj

/-- The specialized complete-generator convention retains `h_0 = 1`. -/
noncomputable def bar (q : ℕ+) (k : ℤ) : CompleteRing := eraseGenerator q (complete k)

@[simp] theorem bar_cut (q : ℕ+) : bar q q.val = 0 := by
  simp [bar, eraseGenerator_complete]

@[simp] theorem bar_zero (q : ℕ+) : bar q 0 = 1 := by simp [bar]

/-- The actual four-row restriction is exactly the manuscript's eight terms. -/
theorem restriction_four_expansion (q : ℕ+) (P : Profile 3) (hP : Thick P) :
    restriction q P = fourInterval (bar q) (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (P.g 0) (P.g 1) (P.g 2) := by
  unfold restriction
  rw [Profile.toBetaDiagram_schur, Profile.schur_four_interval P hP.hessenberg]
  simp only [fourInterval, ← complete_eq_hh, map_sub, map_add, map_mul, bar]

/-- If the first row is erased, the actual four-row determinant reduces to a
three-row interval polynomial times the first gap, without gap-distinctness. -/
theorem restriction_four_first_row_cut {q : ℕ+} (P : Profile 3)
    (hP : Thick P) (ha : P.r 0 = q.val) :
    restriction q P = -bar q (P.g 0) *
      threeInterval (bar q) ((P.r 0 : ℤ) + P.r 1 - P.g 0) (P.r 2) (P.r 3)
        (P.g 1) (P.g 2) := by
  rw [restriction_four_expansion q P hP]
  have hz : bar q (P.r 0) = 0 := by simp [ha]
  have h1 : (P.r 0 : ℤ) + P.r 1 - P.g 0 + P.r 2 - P.g 1 =
      (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 := by ring
  have h2 : (P.r 0 : ℤ) + P.r 1 - P.g 0 + P.r 2 + P.r 3 - P.g 1 - P.g 2 =
      (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 := by ring
  simp only [fourInterval, threeInterval, hz, h1, h2]
  ring

/-- Cutting the middle gap gives an exact product, also when either end gap
has the same value as the middle gap. -/
theorem restriction_four_middle_cut (q v : ℕ+) (P : Profile 3) (hP : Thick P)
    (hv : P.g 1 = v.val) :
    eraseGenerator v (restriction q P) =
      (eraseGenerator v (bar q (P.r 0)) * eraseGenerator v (bar q (P.r 1)) -
        eraseGenerator v (bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0)) *
          eraseGenerator v (bar q (P.g 0))) *
      (eraseGenerator v (bar q (P.r 2)) * eraseGenerator v (bar q (P.r 3)) -
        eraseGenerator v (bar q ((P.r 2 : ℤ) + P.r 3 - P.g 2)) *
          eraseGenerator v (bar q (P.g 2))) := by
  have hz : eraseGenerator v (bar q (P.g 1)) = 0 := by
    simp only [bar, eraseGenerator_complete, hv]
    split_ifs <;> simp [eraseGenerator_complete]
  rw [restriction_four_expansion q P hP]
  simp only [fourInterval, map_sub, map_add, map_mul]
  rw [hz]
  ring

/-- The two repeated-endpoint conditions extract two gap occurrences, even if
all three internal gap labels agree. -/
theorem restriction_four_double_content {q : ℕ+} (P : Profile 3) (hP : Thick P)
    (ha : P.r 0 = q.val) (hc : P.r 2 = q.val) (hst : P.g 1 = P.g 2) :
    restriction q P = bar q (P.g 0) * bar q (P.g 1) *
      (bar q (((P.r 0 : ℤ) + P.r 1 - P.g 0) + P.r 2 - P.g 1) * bar q (P.r 3) -
        bar q (((P.r 0 : ℤ) + P.r 1 - P.g 0) + P.r 2 + P.r 3 - P.g 1 - P.g 2) *
          bar q (P.g 2) +
        bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0) *
          bar q ((P.r 2 : ℤ) + P.r 3 - P.g 2)) := by
  rw [restriction_four_first_row_cut P hP ha]
  have hz : bar q (P.r 2) = 0 := by simp [hc]
  simp only [threeInterval, hz, hst]
  ring

/-- The first of the middle-content alternatives.  All label collisions remain legal. -/
theorem four_middle_content_left {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d r s t : ℤ) (hb : h b = 0) (hrs : r = s) :
    h s ∣ fourInterval h a b c d r s t := by
  subst r
  refine ⟨-h (a + b - s) * h c * h d - h a * h (b + c - s) * h d +
    h s * h (a + b + c - s - s) * h d +
    h t * h (a + b - s) * h (c + d - t) +
    h t * h a * h (b + c + d - s - t) -
    h s * h t * h (a + b + c + d - s - s - t), ?_⟩
  simp only [fourInterval, hb]
  ring

/-- The second alternative, with a vanishing third row. -/
theorem four_middle_content_right {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d r s t : ℤ) (hc : h c = 0) (hst : s = t) :
    h s ∣ fourInterval h a b c d r s t := by
  subst t
  refine ⟨-h a * h (b + c - s) * h d - h a * h b * h (c + d - s) +
    h r * h (a + b + c - r - s) * h d +
    h r * h (a + b - r) * h (c + d - s) +
    h s * h a * h (b + c + d - s - s) -
    h r * h s * h (a + b + c + d - r - s - s), ?_⟩
  simp only [fourInterval, hc]
  ring

/-- The third alternative involves a vanished merged interval, not a vanished row. -/
theorem four_middle_content_merge {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d r s t : ℤ) (hu : h (a + b - r) = 0) (has : a = s) :
    h s ∣ fourInterval h a b c d r s t := by
  subst a
  refine ⟨h b * h c * h d - h s * h (b + c - s) * h d -
    h t * h b * h (c + d - t) +
    h r * h (s + b + c - r - s) * h d +
    h t * h s * h (b + c + d - s - t) -
    h r * h t * h (s + b + c + d - r - s - t), ?_⟩
  simp only [fourInterval, hu]
  ring

/-- The three conditions are logical alternatives yielding the same divisor.
This does not multiply their contributions when two conditions coincide. -/
theorem restriction_four_middle_content_dvd {q : ℕ+} (P : Profile 3)
    (hP : Thick P)
    (hc : (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
      (P.r 2 = q.val ∧ P.g 1 = P.g 2) ∨
      (((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ∧ P.r 0 = P.g 1)) :
    bar q (P.g 1) ∣ restriction q P := by
  rw [restriction_four_expansion q P hP]
  rcases hc with ⟨hb, hrs⟩ | ⟨hc, hst⟩ | ⟨hu, has⟩
  · exact four_middle_content_left (bar q) _ _ _ _ _ _ _
      (by simp [hb]) (by exact_mod_cast hrs)
  · exact four_middle_content_right (bar q) _ _ _ _ _ _ _
      (by simp [hc]) (by exact_mod_cast hst)
  · exact four_middle_content_merge (bar q) _ _ _ _ _ _ _
      (by simp [hu]) (by exact_mod_cast has)

/-- The coefficient monomial after monic gcd extraction. -/
noncomputable def monicPrimitiveCoefficient {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : CompleteRing :=
  MvPolynomial.monomial (gapExponent P hP.gap_pos - contentExponent hP) 1

/-- Exact division of coefficient-one monomials leaves coefficient one. -/
theorem monic_coefficient_factorization {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    gapMonomial P = monicContent hP * monicPrimitiveCoefficient hP := by
  rw [gapMonomial_eq_monomial P hP.gap_pos]
  unfold monicContent monicPrimitiveCoefficient
  rw [MvPolynomial.monomial_mul_monomial, mul_one,
    add_tsub_cancel_of_le (content_monomial_spec hP).1]

/-- The numerical unit of the gcd cancels exactly in the leading coefficient. -/
theorem scalar_primitiveCoefficient_eq {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    MvPolynomial.C (contentUnit hP) * primitiveCoefficient q P =
      monicPrimitiveCoefficient hP := by
  have hm : monicContent hP ≠ 0 := by
    simp [monicContent, MvPolynomial.monomial_eq_zero]
  apply mul_left_cancel₀ hm
  rw [← monic_coefficient_factorization hP]
  have hg := gap_content_mul_coefficient q P
  rw [(content_monomial_spec hP).2.2] at hg
  rw [hg]
  unfold monicContent
  rw [← mul_assoc, mul_comm (MvPolynomial.monomial _ 1) (MvPolynomial.C _),
    MvPolynomial.C_mul_monomial, mul_one]

/-- Sign-normalized primitive with monic gap content. -/
noncomputable def canonicalPrimitive {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : CompleteRing :=
  (-1 : CompleteRing) ^ n * monicPrimitive hP

/-- Exact product equation for the sign-normalized primitive, suitable for
rewriting the small-row content tables without division notation. -/
theorem monicContent_mul_canonicalPrimitive {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    monicContent hP * canonicalPrimitive hP = (-1 : CompleteRing) ^ n * restriction q P := by
  rw [restriction_eq_monicContent_mul hP]
  unfold canonicalPrimitive
  ring

theorem restriction_eq_signed_content_mul_canonical {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    restriction q P = (-1 : CompleteRing) ^ n * monicContent hP * canonicalPrimitive hP := by
  rw [mul_assoc, monicContent_mul_canonicalPrimitive hP]
  have hs : (-1 : CompleteRing) ^ n * (-1 : CompleteRing) ^ n = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hs, one_mul]

/-- Its full-interval coefficient is the positive coefficient-one monomial. -/
theorem canonicalPrimitive_affine {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    canonicalPrimitive hP = monicPrimitiveCoefficient hP *
      MvPolynomial.X (fullGenerator P) +
        (-1 : CompleteRing) ^ n * MvPolynomial.C (contentUnit hP) *
          primitiveConstant q P := by
  have hs : (-1 : CompleteRing) ^ n * (-1 : CompleteRing) ^ n = 1 := by
    rw [← mul_pow]
    simp
  unfold canonicalPrimitive monicPrimitive primitive
  calc
    _ = ((-1 : CompleteRing) ^ n * (-1 : CompleteRing) ^ n) *
        (MvPolynomial.C (contentUnit hP) * primitiveCoefficient q P) *
          MvPolynomial.X (fullGenerator P) +
        (-1 : CompleteRing) ^ n * MvPolynomial.C (contentUnit hP) *
          primitiveConstant q P := by ring
    _ = _ := by rw [hs, one_mul, scalar_primitiveCoefficient_eq hP]

theorem canonicalPrimitive_irreducible {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : Irreducible (canonicalPrimitive hP) := by
  have hu : IsUnit ((-1 : CompleteRing) ^ n) :=
    isUnit_neg_one.pow n
  exact (associated_unit_mul_left (monicPrimitive hP) _ hu).irreducible_iff.mpr
    (monicPrimitive_irreducible hP)

/-- The monic representative differs from the gcd only by its rational unit. -/
theorem content_eq_monicContent_mul_unit {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    content q P = monicContent hP * MvPolynomial.C (contentUnit hP) := by
  rw [(content_monomial_spec hP).2.2]
  unfold monicContent
  rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]

theorem monicContent_dvd_residual {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : monicContent hP ∣ residual q P := by
  apply dvd_trans (show monicContent hP ∣ content q P from
    ⟨MvPolynomial.C (contentUnit hP), content_eq_monicContent_mul_unit hP⟩)
  exact gcd_dvd_right _ _

/-- The singleton row of the complete table. -/
theorem singleton_content {q : ℕ+} {P : Profile 0} (hP : QComponent q P) :
    monicContent hP = 1 := by
  have he := (content_monomial_spec hP).1
  have hz : gapExponent P hP.gap_pos = 0 := by simp [gapExponent]
  rw [hz] at he
  have he0 : contentExponent hP = 0 := le_antisymm he zero_le
  simp [monicContent, he0]

/-- The two-row corner residual consists of the unmerged row product. -/
theorem residual_two (q : ℕ+) (P : Profile 1) :
    residual q P = bar q (P.r 0) * bar q (P.r 1) := by
  have hr : P.toBetaDiagram.cornerResidual =
      complete (P.r 0) * complete (P.r 1) := by
    simp [BetaDiagram.cornerResidual, Finset.univ_fin2, Matrix.det_fin_one,
      Matrix.submatrix_apply, BetaDiagram.matrix, Profile.toBetaDiagram,
      Profile.xi_sub_zeta]
  simp only [residual, hr, map_mul, bar]

/-- The two-row content is exactly its only gap when the first row is erased. -/
theorem two_content_first_row {q : ℕ+} {P : Profile 1} (hP : QComponent q P)
    (ha : P.r 0 = q.val) : monicContent hP = complete (P.g 0) := by
  classical
  have hb : residual q P = 0 := by rw [residual_two]; simp [ha]
  have hd : gapMonomial P ∣ content q P := by
    apply dvd_gcd dvd_rfl
    rw [hb]
    exact dvd_zero _
  have hcu := (content_monomial_spec hP).2.1.ne_zero
  rw [gapMonomial_eq_monomial P hP.gap_pos,
    (content_monomial_spec hP).2.2, MvPolynomial.monomial_dvd_monomial] at hd
  have he : contentExponent hP = gapExponent P hP.gap_pos :=
    le_antisymm (content_monomial_spec hP).1 (hd.1.resolve_left hcu)
  rw [monicContent, he, ← gapMonomial_eq_monomial P hP.gap_pos]
  simp [gapMonomial]

/-- The other two-row case has no gap content.  No numerical parameter bound
or distinctness condition beyond the profile inequalities is used. -/
theorem two_content_first_row_ne {q : ℕ+} {P : Profile 1} (hP : QComponent q P)
    (ha : P.r 0 ≠ q.val) : monicContent hP = 1 := by
  classical
  let A : ℕ+ := ⟨P.r 0, P.r_pos 0⟩
  let B : ℕ+ := ⟨P.r 1, P.r_pos 1⟩
  let R : ℕ+ := ⟨P.g 0, hP.gap_pos 0⟩
  have hb : P.r 1 ≠ q.val := by
    have ht := hP.bottom
    change q.val + lastGap P < P.r 1 at ht
    omega
  have har : A ≠ R := by
    intro he
    have hv := congrArg Subtype.val he
    have hg := P.g_lt_castSucc 0
    change P.g 0 < P.r 0 at hg
    dsimp [A, R] at hv
    omega
  have hbr : B ≠ R := by
    intro he
    have hv := congrArg Subtype.val he
    have hg := P.g_lt_succ 0
    change P.g 0 < P.r 1 at hg
    dsimp [B, R] at hv
    omega
  have hr : residual q P =
      MvPolynomial.monomial (Finsupp.single A 1 + Finsupp.single B 1) 1 := by
    rw [residual_two]
    have hqa : (P.r 0 : ℤ) ≠ q.val := by exact_mod_cast ha
    have hqb : (P.r 1 : ℤ) ≠ q.val := by exact_mod_cast hb
    simp only [bar, eraseGenerator_complete, if_neg hqa, if_neg hqb]
    rw [show complete (P.r 0) = MvPolynomial.X A from complete_nat A,
      show complete (P.r 1) = MvPolynomial.X B from complete_nat B]
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one]
  have heRows := monicContent_dvd_residual hP
  rw [hr] at heRows
  have heRows' : contentExponent hP ≤ Finsupp.single A 1 + Finsupp.single B 1 :=
    MvPolynomial.monomial_one_dvd_monomial_one.mp heRows
  have hg : gapExponent P hP.gap_pos = Finsupp.single R 1 := by
    simp [gapExponent, R, Fin.sum_univ_succ]
  have heGaps := (content_monomial_spec hP).1
  rw [hg] at heGaps
  have he0 : contentExponent hP = 0 := by
    ext v
    by_cases hv : v = R
    · subst v
      have hh := heRows' R
      have hh0 : contentExponent hP R ≤ 0 := by
        simpa [Finsupp.single_apply, har, hbr] using hh
      exact Nat.eq_zero_of_le_zero hh0
    · have hh := heGaps v
      simpa [Finsupp.single_apply, hv, Ne.symm hv] using Nat.eq_zero_of_le_zero
        (show contentExponent hP v ≤ 0 by simpa [Finsupp.single_apply, hv, Ne.symm hv] using hh)
  simp [monicContent, he0]

/-- The complete unbounded two-row table. -/
theorem two_content {q : ℕ+} {P : Profile 1} (hP : QComponent q P) :
    monicContent hP = if P.r 0 = q.val then complete (P.g 0) else 1 := by
  split_ifs with ha
  · exact two_content_first_row hP ha
  · exact two_content_first_row_ne hP ha

/-- The signed beta indices of the actual three-row component. -/
theorem indices_three (P : Profile 2) :
    (Matrix.of fun i j : Fin 3 => P.xi i - P.zeta j) =
      !![(P.r 0 : ℤ), (P.r 0 : ℤ) + P.r 1 - P.g 0,
          (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1;
         (P.g 0 : ℤ), (P.r 1 : ℤ), (P.r 1 : ℤ) + P.r 2 - P.g 1;
         (P.g 0 : ℤ) + P.g 1 - P.r 1, (P.g 1 : ℤ), (P.r 2 : ℤ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Profile.xi, Profile.zeta, Fin.sum_univ_succ] <;> ring

/-- The four interval terms are the actual three-row determinant, with its
genuine negative lower entry removed by thickness. -/
theorem restriction_three_expansion (q : ℕ+) (P : Profile 2) (hP : Thick P) :
    restriction q P = threeInterval (bar q) (P.r 0) (P.r 1) (P.r 2)
      (P.g 0) (P.g 1) := by
  have hn : (P.g 0 : ℤ) + P.g 1 - P.r 1 < 0 := by
    have ht := hP 0 1 (by decide)
    norm_num at ht
    omega
  have hm : P.toBetaDiagram.matrix =
      !![complete (P.r 0), complete ((P.r 0 : ℤ) + P.r 1 - P.g 0),
          complete ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1);
         complete (P.g 0), complete (P.r 1), complete ((P.r 1 : ℤ) + P.r 2 - P.g 1);
         complete ((P.g 0 : ℤ) + P.g 1 - P.r 1), complete (P.g 1), complete (P.r 2)] := by
    apply Matrix.ext
    intro i j
    have hi := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M i j) (indices_three P)
    change complete (P.xi i - P.zeta j) = _
    fin_cases i <;> fin_cases j <;> simpa using congrArg complete hi
  unfold restriction BetaDiagram.schur
  rw [hm, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons, complete_of_neg hn, mul_zero, zero_mul,
    add_zero, sub_zero, map_add, map_sub, map_mul]
  simp only [threeInterval, bar]
  ring

/-- The first-row cut reduces the three-row restriction to a two-row interval. -/
theorem restriction_three_first_row_cut {q : ℕ+} (P : Profile 2) (hP : Thick P)
    (ha : P.r 0 = q.val) :
    restriction q P = -bar q (P.g 0) *
      (bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0) * bar q (P.r 2) -
        bar q ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) *
          bar q (P.g 1)) := by
  rw [restriction_three_expansion q P hP]
  have hz : bar q (P.r 0) = 0 := by simp [ha]
  simp only [threeInterval, hz]
  ring

/-- Both nonendpoint three-row alternatives extract the same last-gap factor. -/
theorem restriction_three_last_content_dvd {q : ℕ+} (P : Profile 2)
    (hP : Thick P)
    (hc : (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
      (((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ∧ P.r 0 = P.g 1)) :
    bar q (P.g 1) ∣ restriction q P := by
  rw [restriction_three_expansion q P hP]
  rcases hc with ⟨hb, hrs⟩ | ⟨hu, has⟩
  · have hz : bar q (P.r 1) = 0 := by simp [hb]
    refine ⟨-bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0) * bar q (P.r 2) -
      bar q (P.r 0) * bar q ((P.r 1 : ℤ) + P.r 2 - P.g 1) +
      bar q ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) *
        bar q (P.g 0), ?_⟩
    simp only [threeInterval, hz, hrs]
    ring
  · have hz : bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0) = 0 := by simp [hu]
    refine ⟨bar q (P.r 1) * bar q (P.r 2) -
      bar q (P.r 0) * bar q ((P.r 1 : ℤ) + P.r 2 - P.g 1) +
      bar q ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) *
        bar q (P.g 0), ?_⟩
    simp only [threeInterval, has] at hz ⊢
    rw [hz]
    ring

/-- The sign-normalized primitive retains the exact positive top coefficient. -/
theorem canonicalPrimitive_pderiv {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    MvPolynomial.pderiv (fullGenerator P) (canonicalPrimitive hP) =
      monicPrimitiveCoefficient hP := by
  have hcoef : fullGenerator P ∉ (monicPrimitiveCoefficient hP).vars :=
    not_mem_vars_of_dvd (gapMonomial_ne_zero P)
      ⟨monicContent hP, by rw [monic_coefficient_factorization hP]; ring⟩ _
      (full_not_mem_gapMonomial hP.thick)
  have hc := MvPolynomial.pderiv_eq_zero_of_notMem_vars hcoef
  have hb := MvPolynomial.pderiv_eq_zero_of_notMem_vars
    (full_not_mem_primitiveConstant q P)
  have hs : (-1 : CompleteRing) ^ n = MvPolynomial.C ((-1 : ℚ) ^ n) := by simp
  have hsDeriv : MvPolynomial.pderiv (fullGenerator P) ((-1 : CompleteRing) ^ n) = 0 := by
    rw [hs]
    exact MvPolynomial.pderiv_C
  rw [canonicalPrimitive_affine hP]
  simp only [map_add, MvPolynomial.pderiv_mul, hsDeriv, hc, hb,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_self, zero_mul, mul_zero,
    zero_add, add_zero, mul_one]

theorem canonicalPrimitive_dvd_restriction {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : canonicalPrimitive hP ∣ restriction q P := by
  have hu : IsUnit ((-1 : CompleteRing) ^ n) := isUnit_neg_one.pow n
  apply (associated_unit_mul_left (monicPrimitive hP) _ hu).dvd.trans
  exact ⟨monicContent hP, by rw [restriction_eq_monicContent_mul hP]; ring⟩

theorem full_mem_canonicalPrimitive {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : fullGenerator P ∈ (canonicalPrimitive hP).vars := by
  by_contra hn
  have hz := MvPolynomial.pderiv_eq_zero_of_notMem_vars hn
  rw [canonicalPrimitive_pderiv hP] at hz
  simpa [monicPrimitiveCoefficient, MvPolynomial.monomial_eq_zero] using hz

theorem not_mem_canonicalPrimitive_above_full {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (v : ℕ+) (hv : fullIndex P < (v.val : ℤ)) :
    v ∉ (canonicalPrimitive hP).vars :=
  not_mem_vars_of_dvd (restriction_ne_zero hP) (canonicalPrimitive_dvd_restriction hP)
    v (not_mem_restriction_above_full q P v hv)

/-- Associates have the same unique largest variable, before any numerical
unit is compared. -/
theorem canonical_associated_fullGenerator_eq {n m : ℕ} {q : ℕ+}
    {P : Profile n} {Q : Profile m} (hP : QComponent q P) (hQ : QComponent q Q)
    (h : Associated (canonicalPrimitive hP) (canonicalPrimitive hQ)) :
    fullGenerator P = fullGenerator Q := by
  have hp := full_mem_canonicalPrimitive hP
  have hq := full_mem_canonicalPrimitive hQ
  have hp' : fullGenerator P ∈ (canonicalPrimitive hQ).vars := by
    by_contra hn
    exact not_mem_vars_of_dvd (canonicalPrimitive_irreducible hQ).ne_zero h.dvd
      _ hn hp
  have hq' : fullGenerator Q ∈ (canonicalPrimitive hP).vars := by
    by_contra hn
    exact not_mem_vars_of_dvd (canonicalPrimitive_irreducible hP).ne_zero h.symm.dvd
      _ hn hq
  have hpPos := P.toBetaDiagram.largestLabel_pos
  have hqPos := Q.toBetaDiagram.largestLabel_pos
  have hleP : fullIndex P ≤ fullIndex Q := by
    by_contra hn
    have hv : fullIndex Q < ((fullGenerator P).val : ℤ) := by
      rw [fullGenerator_int_coe]
      omega
    exact not_mem_canonicalPrimitive_above_full hQ _ hv hp'
  have hleQ : fullIndex Q ≤ fullIndex P := by
    by_contra hn
    have hv : fullIndex P < ((fullGenerator Q).val : ℤ) := by
      rw [fullGenerator_int_coe]
      omega
    exact not_mem_canonicalPrimitive_above_full hP _ hv hq'
  apply Subtype.ext
  dsimp [fullGenerator]
  rw [le_antisymm hleP hleQ]

/-- A scalar relating coefficient-one monomials is necessarily one. -/
theorem scalar_eq_one_of_monomial_eq (a : ℚ) (ha : a ≠ 0)
    (e f : ℕ+ →₀ ℕ)
    (h : (MvPolynomial.C a : CompleteRing) * MvPolynomial.monomial e 1 =
      MvPolynomial.monomial f 1) : a = 1 := by
  classical
  have hc := congrArg (fun p : CompleteRing => p.coeff e) h
  by_cases hef : e = f
  · simpa [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, hef] using hc
  · have hz : a = 0 := by
      simpa [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, hef, Ne.symm hef] using hc
    exact (ha hz).elim

/-- Sign-normalized primitive associates are equal, including components of
different row counts and coincident internal gap values. -/
theorem canonical_associated_eq {n m : ℕ} {q : ℕ+}
    {P : Profile n} {Q : Profile m} (hP : QComponent q P) (hQ : QComponent q Q)
    (h : Associated (canonicalPrimitive hP) (canonicalPrimitive hQ)) :
    canonicalPrimitive hP = canonicalPrimitive hQ := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨a, ha, hua⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have hfull := canonical_associated_fullGenerator_eq hP hQ ⟨u, hu⟩
  have he : (MvPolynomial.C a : CompleteRing) * monicPrimitiveCoefficient hP =
      monicPrimitiveCoefficient hQ := by
    have hd := congrArg (MvPolynomial.pderiv (fullGenerator P)) hu
    rw [hua] at hd
    rw [MvPolynomial.pderiv_mul] at hd
    rw [canonicalPrimitive_pderiv hP, hfull, canonicalPrimitive_pderiv hQ] at hd
    simpa only [MvPolynomial.pderiv_C, mul_zero, zero_mul, add_zero, mul_comm] using hd
  have ha1 : a = 1 := scalar_eq_one_of_monomial_eq a ha.ne_zero _ _ he
  simpa [hua, ha1] using hu

/-- Any nonzero coefficient bounds every extracted content exponent. -/
theorem contentExponent_le_of_coeff_ne_zero {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (d : ℕ+ →₀ ℕ)
    (hd : (restriction q P).coeff d ≠ 0) : contentExponent hP ≤ d := by
  classical
  rw [restriction_eq_monicContent_mul hP] at hd
  change (MvPolynomial.monomial (contentExponent hP) 1 * monicPrimitive hP).coeff d ≠ 0 at hd
  rw [MvPolynomial.coeff_monomial_mul'] at hd
  split_ifs at hd with he
  · exact he
  · exact (hd rfl).elim

/-- Exact monomial residuals calculate content by an exponent infimum, not by
a bounded census or a factorization oracle. -/
theorem contentExponent_eq_inf_of_residual_monomial {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (d : ℕ+ →₀ ℕ) (a : ℚ) (ha : a ≠ 0)
    (hr : residual q P = MvPolynomial.monomial d a) :
    contentExponent hP = gapExponent P hP.gap_pos ⊓ d := by
  classical
  have hd := monicContent_dvd_residual hP
  rw [hr, monicContent, MvPolynomial.monomial_dvd_monomial] at hd
  have he : contentExponent hP ≤ d := hd.1.resolve_left ha
  apply le_antisymm (le_inf (content_monomial_spec hP).1 he)
  have hgap : (MvPolynomial.monomial (gapExponent P hP.gap_pos ⊓ d) 1 : CompleteRing) ∣
      gapMonomial P := by
    rw [gapMonomial_eq_monomial P hP.gap_pos,
      MvPolynomial.monomial_one_dvd_monomial_one]
    exact inf_le_left
  have hres : (MvPolynomial.monomial (gapExponent P hP.gap_pos ⊓ d) 1 : CompleteRing) ∣
      residual q P := by
    rw [hr, MvPolynomial.monomial_dvd_monomial]
    exact ⟨Or.inr inf_le_right, one_dvd _⟩
  have hlow := dvd_gcd hgap hres
  rw [← show content q P = gcd (gapMonomial P) (residual q P) from rfl,
    (content_monomial_spec hP).2.2, MvPolynomial.monomial_dvd_monomial] at hlow
  exact hlow.1.resolve_left (content_monomial_spec hP).2.1.ne_zero

/-- Two generator erasures act directly on the integer-index convention. -/
theorem erase_bar (q v : ℕ+) (k : ℤ) :
    eraseGenerator v (bar q k) =
      if k = (q.val : ℤ) ∨ k = (v.val : ℤ) then 0 else complete k := by
  classical
  simp only [bar, eraseGenerator_complete]
  split_ifs <;> simp_all [eraseGenerator_complete]

/-- An unerased positive generator cannot vanish. -/
theorem erase_bar_ne_zero {q v : ℕ+} {k : ℤ} (hk : 0 < k)
    (hkq : k ≠ (q.val : ℤ)) (hkv : k ≠ (v.val : ℤ)) :
    eraseGenerator v (bar q k) ≠ 0 := by
  rw [erase_bar, if_neg (by tauto)]
  exact (complete_ne_zero_iff k).mpr hk.le

/-- A deleted two-row factor has precisely the two vanishing alternatives
used at the middle cut.  The deleted labels may coincide with either row. -/
theorem erased_two_factor_eq_zero_iff (q v : ℕ+) (a b r : ℤ)
    (hr : 0 < r) (hra : r < a) (hrb : r < b)
    (hvb : (v.val : ℤ) < b)
    (haq : a ≠ (q.val : ℤ)) (hrq : r ≠ (q.val : ℤ)) :
    eraseGenerator v (bar q a * bar q b - bar q r * bar q (a + b - r)) = 0 ↔
      (b = (q.val : ℤ) ∧ r = (v.val : ℤ)) ∨
        (a = (v.val : ℤ) ∧ a + b - r = (q.val : ℤ)) := by
  classical
  let u : ℤ := a + b - r
  have hua : a < u := by dsimp [u]; omega
  have hub : b < u := by dsimp [u]; omega
  have hur : r < u := by omega
  have huv : (v.val : ℤ) < u := hvb.trans hub
  have hau : a ≠ u := ne_of_lt hua
  have hbu : b ≠ u := ne_of_lt hub
  have hru : r ≠ u := ne_of_lt hur
  change eraseGenerator v (bar q a * bar q b - bar q r * bar q u) = 0 ↔ _
  by_cases hrv : r = (v.val : ℤ)
  · have hav : a ≠ (v.val : ℤ) := by omega
    have hA := erase_bar_ne_zero (q := q) (v := v) (by omega : 0 < a) haq hav
    have hB : eraseGenerator v (bar q b) = 0 ↔ b = (q.val : ℤ) := by
      by_cases hbq : b = (q.val : ℤ)
      · simp [erase_bar, hbq]
      · have hn := erase_bar_ne_zero (q := q) (v := v) (by omega : 0 < b)
          hbq (ne_of_gt hvb)
        simp [hn, hbq]
    simp only [map_sub, map_mul, erase_bar q v r, if_pos (Or.inr hrv), zero_mul,
      sub_zero, mul_eq_zero, hA, false_or, hB]
    simp [hrv, hav]
  · by_cases huq : u = (q.val : ℤ)
    · have hbq : b ≠ (q.val : ℤ) := by omega
      have hB := erase_bar_ne_zero (q := q) (v := v) (by omega : 0 < b)
        hbq (ne_of_gt hvb)
      have hA : eraseGenerator v (bar q a) = 0 ↔ a = (v.val : ℤ) := by
        by_cases hav : a = (v.val : ℤ)
        · simp [erase_bar, hav]
        · have hn := erase_bar_ne_zero (q := q) (v := v) (by omega : 0 < a) haq hav
          simp [hn, hav]
      simp only [map_sub, map_mul, erase_bar q v u, if_pos (Or.inl huq),
        mul_zero, sub_zero, mul_eq_zero, hA, hB, or_false]
      simp [hrv, show a + b - r = (q.val : ℤ) from huq]
    · have hR := erase_bar_ne_zero (q := q) (v := v) hr hrq hrv
      let U : ℕ+ := ⟨u.toNat, by omega⟩
      have hU : (U.val : ℤ) = u := by dsimp [U]; omega
      have hno (k : ℤ) (hku : k ≠ u) :
          MvPolynomial.pderiv U (eraseGenerator v (bar q k)) = 0 := by
        apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
        apply not_mem_vars_erase v U
        apply not_mem_vars_erase q U
        rw [mem_vars_complete_iff]
        simpa [hU, eq_comm] using hku
      have huEntry : eraseGenerator v (bar q u) = MvPolynomial.X U := by
        rw [erase_bar, if_neg (by omega), complete_of_pos (by omega)]
      have hnonzero :
          eraseGenerator v (bar q a * bar q b - bar q r * bar q u) ≠ 0 := by
        intro hz
        have hd := congrArg (MvPolynomial.pderiv U) hz
        simp only [map_sub, map_mul, MvPolynomial.pderiv_mul,
          hno a hau, hno b hbu, hno r hru, huEntry, MvPolynomial.pderiv_X_self,
          zero_mul, mul_zero, zero_add, add_zero, mul_one, sub_self, zero_sub,
          map_zero, neg_eq_zero] at hd
        exact hR hd
      have hrhs : ¬ ((b = (q.val : ℤ) ∧ r = (v.val : ℤ)) ∨
          (a = (v.val : ℤ) ∧ a + b - r = (q.val : ℤ))) := by
        dsimp [u] at huq
        tauto
      exact ⟨fun hz => (hnonzero hz).elim, fun hc => (hrhs hc).elim⟩

/-- A surviving negative full-interval term prevents a two-row factor from
vanishing after two erasures, even if one row itself is erased. -/
theorem erased_two_factor_ne_zero_of_full_survives (q v : ℕ+) (a b r : ℤ)
    (hr : 0 < r) (hra : r < a) (hrb : r < b)
    (hrq : r ≠ (q.val : ℤ)) (hrv : r ≠ (v.val : ℤ))
    (huq : a + b - r ≠ (q.val : ℤ)) (huv : a + b - r ≠ (v.val : ℤ)) :
    eraseGenerator v (bar q a * bar q b - bar q r * bar q (a + b - r)) ≠ 0 := by
  classical
  let u : ℤ := a + b - r
  let U : ℕ+ := ⟨u.toNat, by dsimp [u]; omega⟩
  have hU : (U.val : ℤ) = u := by dsimp [U, u]; omega
  have hno (k : ℤ) (hku : k ≠ u) :
      MvPolynomial.pderiv U (eraseGenerator v (bar q k)) = 0 := by
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    apply not_mem_vars_erase v U
    apply not_mem_vars_erase q U
    rw [mem_vars_complete_iff]
    simpa [hU, eq_comm] using hku
  have huEntry : eraseGenerator v (bar q u) = MvPolynomial.X U := by
    rw [erase_bar, if_neg (by dsimp [u]; tauto), complete_of_pos (by dsimp [u]; omega)]
  have hR := erase_bar_ne_zero (q := q) (v := v) hr hrq hrv
  intro hz
  have hd := congrArg (MvPolynomial.pderiv U) hz
  have hau : a ≠ u := by dsimp [u]; omega
  have hbu : b ≠ u := by dsimp [u]; omega
  have hru : r ≠ u := by dsimp [u]; omega
  change MvPolynomial.pderiv U
    (eraseGenerator v (bar q a * bar q b - bar q r * bar q u)) =
      MvPolynomial.pderiv U 0 at hd
  simp only [map_sub, map_mul, MvPolynomial.pderiv_mul, hno a hau, hno b hbu,
    hno r hru, huEntry, MvPolynomial.pderiv_X_self, zero_mul, mul_zero,
    zero_add, add_zero, mul_one, sub_self, zero_sub, map_zero, neg_eq_zero] at hd
  exact hR hd

theorem erase_eq_zero_of_X_dvd (v : ℕ+) (p : CompleteRing)
    (h : MvPolynomial.X v ∣ p) : eraseGenerator v p = 0 := by
  obtain ⟨f, hf⟩ := h
  rw [hf, map_mul]
  simp [eraseGenerator]

/-- The middle-cut vanishing test gives the exact last-gap divisibility
criterion for three rows, including equal gap values. -/
theorem three_last_gap_dvd_iff {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) :
    let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
    MvPolynomial.X S ∣ restriction q P ↔
      (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
        (((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ∧ P.r 0 = P.g 1) := by
  classical
  dsimp only
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  have hs0 : eraseGenerator S (bar q (P.g 1)) = 0 := by
    rw [erase_bar, if_pos]
    exact Or.inr rfl
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hC : eraseGenerator S (bar q (P.r 2)) ≠ 0 :=
    erase_bar_ne_zero (by have := P.r_pos 2; positivity)
      (by exact_mod_cast (show P.r 2 ≠ q.val by omega))
      (by dsimp [S]; omega)
  have hcut : eraseGenerator S (restriction q P) =
      eraseGenerator S (bar q (P.r 0) * bar q (P.r 1) -
        bar q (P.g 0) * bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0)) *
          eraseGenerator S (bar q (P.r 2)) := by
    rw [restriction_three_expansion q P hP.thick]
    simp only [threeInterval, map_add, map_sub, map_mul, hs0]
    ring
  have hfactor := erased_two_factor_eq_zero_iff q S (P.r 0) (P.r 1) (P.g 0)
    (by exact_mod_cast hP.gap_pos 0)
    (by exact_mod_cast P.g_lt_castSucc 0)
    (by exact_mod_cast P.g_lt_succ 0)
    (by dsimp [S]; exact_mod_cast P.g_lt_castSucc 1)
    (by exact_mod_cast ha)
    (by exact_mod_cast hP.gap_ne 0)
  constructor
  · intro hd
    have hz := erase_eq_zero_of_X_dvd S _ hd
    rw [hcut, mul_eq_zero] at hz
    have hF := hz.resolve_right hC
    have hc := hfactor.mp hF
    rcases hc with ⟨hb, hrs⟩ | ⟨has, hu⟩
    · exact Or.inl ⟨by exact_mod_cast hb, by exact_mod_cast hrs⟩
    · exact Or.inr ⟨hu, by exact_mod_cast has⟩
  · intro hc
    have hd := restriction_three_last_content_dvd P hP.thick hc
    have he : bar q (P.g 1) = MvPolynomial.X S := by
      rw [bar, eraseGenerator_complete, if_neg (by exact_mod_cast hP.gap_ne 1)]
      exact complete_nat S
    rwa [he] at hd

/-- Apart from a repeated last gap, the first gap cannot divide a three-row
restriction whose first row is not erased. -/
theorem three_first_gap_not_dvd {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) (hrs : P.g 0 ≠ P.g 1) :
    let R : ℕ+ := ⟨P.g 0, hP.gap_pos 0⟩
    ¬ MvPolynomial.X R ∣ restriction q P := by
  classical
  dsimp only
  let R : ℕ+ := ⟨P.g 0, hP.gap_pos 0⟩
  have hr0 : eraseGenerator R (bar q (P.g 0)) = 0 := by
    rw [erase_bar, if_pos]
    exact Or.inr rfl
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hthick := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hthick
  have hA : eraseGenerator R (bar q (P.r 0)) ≠ 0 :=
    erase_bar_ne_zero (by have := P.r_pos 0; positivity)
      (by exact_mod_cast ha) (by dsimp [R]; exact_mod_cast ne_of_gt (P.g_lt_castSucc 0))
  have hF := erased_two_factor_ne_zero_of_full_survives q R
    (P.r 1) (P.r 2) (P.g 1)
    (by exact_mod_cast hP.gap_pos 1)
    (by exact_mod_cast P.g_lt_castSucc 1)
    (by exact_mod_cast P.g_lt_succ 1)
    (by exact_mod_cast hP.gap_ne 1)
    (by dsimp [R]; exact_mod_cast Ne.symm hrs)
    (by omega) (by dsimp [R]; omega)
  have hcut : eraseGenerator R (restriction q P) =
      eraseGenerator R (bar q (P.r 0)) *
        eraseGenerator R (bar q (P.r 1) * bar q (P.r 2) -
          bar q (P.g 1) * bar q ((P.r 1 : ℤ) + P.r 2 - P.g 1)) := by
    rw [restriction_three_expansion q P hP.thick]
    simp only [threeInterval, map_add, map_sub, map_mul, hr0]
    ring
  intro hd
  have hz := erase_eq_zero_of_X_dvd R _ hd
  rw [hcut] at hz
  exact mul_ne_zero hA hF hz

/-- Internal gap variable divisors belong to the monomial content, never to
the unique full-interval primitive. -/
theorem gap_variable_dvd_content_iff {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (j : Fin n) :
    let V : ℕ+ := ⟨P.g j, hP.gap_pos j⟩
    MvPolynomial.X V ∣ monicContent hP ↔ MvPolynomial.X V ∣ restriction q P := by
  classical
  dsimp only
  let V : ℕ+ := ⟨P.g j, hP.gap_pos j⟩
  constructor
  · intro hd
    exact hd.trans ⟨monicPrimitive hP, restriction_eq_monicContent_mul hP⟩
  · intro hd
    rw [restriction_eq_monicContent_mul hP, MvPolynomial.X_dvd_mul_iff] at hd
    rcases hd with hd | hd
    · exact hd
    · have hdK : MvPolynomial.X V ∣ canonicalPrimitive hP :=
        dvd_mul_of_dvd_right hd _
      have hback : canonicalPrimitive hP ∣ MvPolynomial.X V :=
        (MvPolynomial.X_prime (i := V)).irreducible.dvd_symm
          (canonicalPrimitive_irreducible hP) hdK
      have hidx := index_lt_full P j.succ j.castSucc (Or.inl (Fin.succ_ne_zero j))
      rw [P.xi_succ_sub_zeta_castSucc] at hidx
      have hneq : fullGenerator P ≠ V := by
        intro he
        have hv := congrArg Subtype.val he
        have hp := P.toBetaDiagram.largestLabel_pos
        dsimp [fullGenerator, V, fullIndex] at *
        omega
      have hn : fullGenerator P ∉ (MvPolynomial.X V : CompleteRing).vars := by
        simp [hneq]
      exact (not_mem_vars_of_dvd (MvPolynomial.X_ne_zero V) hback _ hn
        (full_mem_canonicalPrimitive hP)).elim

/-- A monomial supported on two distinct gap variables is recovered from the
two variable-divisibility bits. -/
theorem content_three_distinct_gaps {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) (hrs : P.g 0 ≠ P.g 1) :
    monicContent hP =
      if (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
          (((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ∧ P.r 0 = P.g 1)
      then complete (P.g 1) else 1 := by
  classical
  let R : ℕ+ := ⟨P.g 0, hP.gap_pos 0⟩
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  have hRS : R ≠ S := by
    intro h
    exact hrs (congrArg Subtype.val h)
  have hbound : contentExponent hP ≤ Finsupp.single R 1 + Finsupp.single S 1 := by
    simpa [gapExponent, R, S, Fin.sum_univ_succ] using (content_monomial_spec hP).1
  have hR : contentExponent hP R = 0 := by
    have hn := three_first_gap_not_dvd hP ha hrs
    have hnG : ¬ MvPolynomial.X R ∣ monicContent hP :=
      fun h => hn ((gap_variable_dvd_content_iff hP 0).mp h)
    simpa only [monicContent, MvPolynomial.X_dvd_monomial, one_ne_zero, false_or,
      not_not] using hnG
  have hS : contentExponent hP S ≠ 0 ↔
      (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
        (((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ∧ P.r 0 = P.g 1) := by
    have he := (gap_variable_dvd_content_iff hP 1).trans (three_last_gap_dvd_iff hP ha)
    simpa only [monicContent, MvPolynomial.X_dvd_monomial, one_ne_zero, false_or] using he
  have hrest (v : ℕ+) (hvR : v ≠ R) (hvS : v ≠ S) : contentExponent hP v = 0 := by
    have hb := hbound v
    have hz : contentExponent hP v ≤ 0 := by
      simpa [Finsupp.single_apply, hvR, hvS, Ne.symm hvR, Ne.symm hvS] using hb
    omega
  split_ifs with hc
  · have hval : contentExponent hP S = 1 := by
      have hp := hS.mpr hc
      have hb := hbound S
      have hb' : contentExponent hP S ≤ 1 := by
        simpa [Finsupp.single_apply, hRS, Ne.symm hRS] using hb
      omega
    have he : contentExponent hP = Finsupp.single S 1 := by
      ext v
      by_cases hvS : v = S
      · subst v; simp [hval]
      · by_cases hvR : v = R
        · subst v; simp [hR, Finsupp.single_apply, hRS, Ne.symm hRS]
        · simp [hrest v hvR hvS, Finsupp.single_apply, hvS, Ne.symm hvS]
    rw [monicContent, he]
    exact (complete_nat S).symm
  · have hval : contentExponent hP S = 0 := not_ne_iff.mp (mt hS.mp hc)
    have he : contentExponent hP = 0 := by
      ext v
      by_cases hvS : v = S
      · subst v; exact hval
      · by_cases hvR : v = R
        · subst v; exact hR
        · exact hrest v hvR hvS
    simp [monicContent, he]

theorem fullIndex_three (P : Profile 2) :
    fullIndex P = (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 := by
  simp [fullIndex, BetaDiagram.largestLabel, Profile.toBetaDiagram, Profile.xi,
    Profile.zeta, Fin.sum_univ_succ]
  ring

theorem bar_fullIndex {n : ℕ} {q : ℕ+} {P : Profile n} (hP : QComponent q P) :
    bar q (fullIndex P) = MvPolynomial.X (fullGenerator P) := by
  rw [bar, eraseGenerator_complete, if_neg (ne_of_gt (fullIndex_gt_q hP))]
  exact complete_of_pos P.toBetaDiagram.largestLabel_pos

/-- The first-row-erased three-row residual has a single negative monomial. -/
theorem residual_three_first_row_cut {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 = q.val) :
    residual q P = -bar q (P.g 0) *
      bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0) * bar q (P.r 2) := by
  have hgap : gapMonomial P = bar q (P.g 0) * bar q (P.g 1) := by
    have hq0 : (P.g 0 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 0
    have hq1 : (P.g 1 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 1
    simp [gapMonomial, Fin.prod_univ_succ, bar, eraseGenerator_complete, hq0, hq1]
  have htop : MvPolynomial.X (fullGenerator P) =
      bar q ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) := by
    rw [← fullIndex_three P, bar_fullIndex hP]
  have haff := restriction_affine hP
  have hcut := restriction_three_first_row_cut P hP.thick ha
  rw [hgap, htop] at haff
  norm_num at haff
  linear_combination -haff + hcut

/-- Exact first-row branch of the three-row table, also when its two gaps
coincide. -/
theorem three_content_first_row {q : ℕ+} {P : Profile 2} (hP : QComponent q P)
    (ha : P.r 0 = q.val) : monicContent hP = complete (P.g 0) := by
  classical
  let R : ℕ+ := ⟨P.g 0, hP.gap_pos 0⟩
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  have ht := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at ht
  have hc : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hra := P.g_lt_castSucc 0
  change P.g 0 < P.r 0 at hra
  have huq : (q.val : ℤ) < (P.r 0 : ℤ) + P.r 1 - P.g 0 := by omega
  have hur : (P.g 0 : ℤ) < (P.r 0 : ℤ) + P.r 1 - P.g 0 := by omega
  have hus : (P.g 1 : ℤ) < (P.r 0 : ℤ) + P.r 1 - P.g 0 := by omega
  let U : ℕ+ := ⟨((P.r 0 : ℤ) + P.r 1 - P.g 0).toNat, by omega⟩
  let C : ℕ+ := ⟨P.r 2, P.r_pos 2⟩
  have hUval : (U.val : ℤ) = (P.r 0 : ℤ) + P.r 1 - P.g 0 := by dsimp [U]; omega
  have hUR : U ≠ R := by
    intro he
    have hv := congrArg (fun p : ℕ+ => (p.val : ℤ)) he
    rw [hUval] at hv
    change (P.r 0 : ℤ) + P.r 1 - P.g 0 = (P.g 0 : ℤ) at hv
    exact (ne_of_gt hur) hv
  have hUS : U ≠ S := by
    intro he
    have hv := congrArg (fun p : ℕ+ => (p.val : ℤ)) he
    rw [hUval] at hv
    change (P.r 0 : ℤ) + P.r 1 - P.g 0 = (P.g 1 : ℤ) at hv
    exact (ne_of_gt hus) hv
  have hCR : C ≠ R := by
    intro he
    have hv := congrArg Subtype.val he
    dsimp [C, R] at hv
    omega
  have hCS : C ≠ S := by
    intro he
    have hv := congrArg Subtype.val he
    dsimp [C, S] at hv
    omega
  have hr : residual q P =
      MvPolynomial.monomial (Finsupp.single R 1 + Finsupp.single U 1 +
        Finsupp.single C 1) (-1) := by
    rw [residual_three_first_row_cut hP ha]
    have hbr : bar q (P.g 0) = MvPolynomial.X R := by
      rw [bar, eraseGenerator_complete, if_neg (by exact_mod_cast hP.gap_ne 0)]
      exact complete_nat R
    have hbu : bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0) = MvPolynomial.X U := by
      rw [bar, eraseGenerator_complete, if_neg (ne_of_gt huq),
        complete_of_pos (by have := q.pos; omega)]
    have hbc : bar q (P.r 2) = MvPolynomial.X C := by
      rw [bar, eraseGenerator_complete, if_neg (by omega)]
      exact complete_nat C
    rw [hbr, hbu, hbc]
    change -MvPolynomial.monomial (Finsupp.single R 1) 1 *
      MvPolynomial.monomial (Finsupp.single U 1) 1 *
        MvPolynomial.monomial (Finsupp.single C 1) 1 = _
    simp [← neg_mul, MvPolynomial.monomial_mul_monomial, ← map_neg]
  have he := contentExponent_eq_inf_of_residual_monomial hP _ (-1) (by norm_num) hr
  have hg : gapExponent P hP.gap_pos = Finsupp.single R 1 + Finsupp.single S 1 := by
    simp [gapExponent, R, S, Fin.sum_univ_succ]
  rw [hg] at he
  have hinf :
      (Finsupp.single R 1 + Finsupp.single S 1) ⊓
        (Finsupp.single R 1 + Finsupp.single U 1 + Finsupp.single C 1) =
          Finsupp.single R 1 := by
    ext v
    change min ((Finsupp.single R 1 + Finsupp.single S 1 : ℕ+ →₀ ℕ) v)
      ((Finsupp.single R 1 + Finsupp.single U 1 + Finsupp.single C 1 : ℕ+ →₀ ℕ) v) =
        (Finsupp.single R 1 : ℕ+ →₀ ℕ) v
    by_cases hvR : v = R
    · subst v
      by_cases hRS : R = S
      · simp [Finsupp.single_apply, hRS, hUS, hCS, Ne.symm hUS, Ne.symm hCS]
      · simp [Finsupp.single_apply, hRS, hUR, hCR, Ne.symm hUR, Ne.symm hCR]
    · by_cases hvS : v = S
      · subst v
        simp [Finsupp.single_apply, hvR, Ne.symm hvR, hUS, hCS, Ne.symm hUS, Ne.symm hCS]
      · simp [Finsupp.single_apply, hvR, Ne.symm hvR, hvS, Ne.symm hvS]
  rw [hinf] at he
  rw [monicContent, he]
  exact (complete_nat R).symm

/-- Coincident gaps contribute only one factor in the nonendpoint branch.
The multiplicity is measured by an exact specialization whose value is -2. -/
theorem three_repeated_gap_square_not_dvd {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hrs : P.g 0 = P.g 1) (hb : P.r 1 = q.val) :
    let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
    ¬ (MvPolynomial.X S : CompleteRing) ^ 2 ∣ restriction q P := by
  classical
  dsimp only
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  let u : ℤ := (P.r 0 : ℤ) + P.r 1 - P.g 0
  let v : ℤ := (P.r 1 : ℤ) + P.r 2 - P.g 1
  let T : ℤ := (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1
  let L : CompleteRing := -bar q u * bar q (P.r 2) - bar q (P.r 0) * bar q v +
    MvPolynomial.X S * bar q T
  have hS : bar q (P.g 1) = MvPolynomial.X S := by
    rw [bar, eraseGenerator_complete, if_neg (by exact_mod_cast hP.gap_ne 1)]
    exact complete_nat S
  have hfactor : restriction q P = MvPolynomial.X S * L := by
    rw [restriction_three_expansion q P hP.thick]
    have hb0 : bar q (P.r 1) = 0 := by simp [hb]
    dsimp [L, u, v, T]
    simp only [threeInterval, hb0, hrs, hS]
    ring
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hrow := P.g_lt_castSucc 0
  change P.g 0 < P.r 0 at hrow
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  let E : CompleteRing →+* ℚ := MvPolynomial.eval (fun _ : ℕ+ => (1 : ℚ))
  have hev (k : ℤ) (hk : 0 < k) (hkq : k ≠ (q.val : ℤ))
      (hks : k ≠ (S.val : ℤ)) : E (eraseGenerator S (bar q k)) = 1 := by
    rw [erase_bar, if_neg (by tauto), complete_of_pos hk]
    simp only [E, MvPolynomial.eval_X]
  have hA : E (eraseGenerator S (bar q (P.r 0))) = 1 :=
    hev _ (by have := P.r_pos 0; positivity)
      (by exact_mod_cast ha) (by dsimp [S]; omega)
  have hC : E (eraseGenerator S (bar q (P.r 2))) = 1 :=
    hev _ (by have := P.r_pos 2; positivity) (by omega) (by dsimp [S]; omega)
  have hU : E (eraseGenerator S (bar q u)) = 1 :=
    hev _ (by dsimp [u]; omega) (by dsimp [u]; omega) (by dsimp [u, S]; omega)
  have hV : E (eraseGenerator S (bar q v)) = 1 :=
    hev _ (by dsimp [v]; omega) (by dsimp [v]; omega) (by dsimp [v, S]; omega)
  have hL : eraseGenerator S L ≠ 0 := by
    intro hz
    have he := congrArg E hz
    dsimp [L] at he
    simp only [map_add, map_sub, map_neg, map_mul, map_zero, hA, hC, hU, hV] at he
    have hx : eraseGenerator S (MvPolynomial.X S) = 0 := by simp [eraseGenerator]
    rw [hx, map_zero] at he
    norm_num at he
  intro hd
  rw [hfactor, pow_two] at hd
  have hdL : MvPolynomial.X S ∣ L :=
    (mul_dvd_mul_iff_left (MvPolynomial.X_ne_zero S)).mp hd
  exact hL (erase_eq_zero_of_X_dvd S L hdL)

/-- Complete repeated-gap branch through three rows. -/
theorem content_three_repeated_gaps {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) (hrs : P.g 0 = P.g 1) :
    monicContent hP = if P.r 1 = q.val then complete (P.g 1) else 1 := by
  classical
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  have hbound : contentExponent hP ≤ Finsupp.single S 2 := by
    have heq : gapExponent P hP.gap_pos = Finsupp.single S 2 := by
      ext v
      by_cases hv : v = S
      · subst v
        simp [gapExponent, hrs, S, Fin.sum_univ_succ]
      · simp [gapExponent, hrs, S, Fin.sum_univ_succ,
          Finsupp.single_apply, hv, Ne.symm hv]
    rw [← heq]
    exact (content_monomial_spec hP).1
  have haneq : P.r 0 ≠ P.g 1 := by
    have hrow := P.g_lt_castSucc 0
    change P.g 0 < P.r 0 at hrow
    omega
  have hS : contentExponent hP S ≠ 0 ↔ P.r 1 = q.val := by
    have he := (gap_variable_dvd_content_iff hP 1).trans (three_last_gap_dvd_iff hP ha)
    simpa [monicContent, MvPolynomial.X_dvd_monomial, hrs, haneq] using he
  have hrest (v : ℕ+) (hvs : v ≠ S) : contentExponent hP v = 0 := by
    have hh := hbound v
    have hh0 : contentExponent hP v ≤ 0 := by
      simpa [Finsupp.single_apply, hvs, Ne.symm hvs] using hh
    omega
  split_ifs with hb
  · have hpos := hS.mpr hb
    have hlt : contentExponent hP S < 2 := by
      by_contra hn
      have hd : (MvPolynomial.X S : CompleteRing) ^ 2 ∣ monicContent hP := by
        rw [MvPolynomial.X_pow_eq_monomial, monicContent,
          MvPolynomial.monomial_one_dvd_monomial_one]
        exact Finsupp.single_le_iff.mpr (by omega)
      have hd' : (MvPolynomial.X S : CompleteRing) ^ 2 ∣ restriction q P :=
        hd.trans ⟨monicPrimitive hP, restriction_eq_monicContent_mul hP⟩
      exact three_repeated_gap_square_not_dvd hP ha hrs hb hd'
    have hval : contentExponent hP S = 1 := by omega
    have he : contentExponent hP = Finsupp.single S 1 := by
      ext v
      by_cases hv : v = S
      · subst v; simp [hval]
      · simp [hrest v hv, Finsupp.single_apply, hv, Ne.symm hv]
    rw [monicContent, he]
    exact (complete_nat S).symm
  · have hval : contentExponent hP S = 0 := not_ne_iff.mp (mt hS.mp hb)
    have he : contentExponent hP = 0 := by
      ext v
      by_cases hv : v = S
      · subst v; exact hval
      · exact hrest v hv
    simp [monicContent, he]

/-- The complete three-row content table, with the alternatives taken once. -/
theorem three_content {q : ℕ+} {P : Profile 2} (hP : QComponent q P) :
    monicContent hP =
      if P.r 0 = q.val then complete (P.g 0)
      else if (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
          (((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ∧ P.r 0 = P.g 1)
      then complete (P.g 1) else 1 := by
  classical
  by_cases ha : P.r 0 = q.val
  · simpa [ha] using three_content_first_row hP ha
  · simp only [if_neg ha]
    by_cases hrs : P.g 0 = P.g 1
    · have haneq : P.r 0 ≠ P.g 1 := by
        have hrow := P.g_lt_castSucc 0
        change P.g 0 < P.r 0 at hrow
        omega
      simpa [hrs, haneq] using content_three_repeated_gaps hP ha hrs
    · exact content_three_distinct_gaps hP ha hrs

/-- At the bottom cut factor the only vanishing case erases both its first
row and its gap.  This uses the inherited q-boundary, not connectedness. -/
theorem four_bottom_factor_zero_iff {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) :
    let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
    eraseGenerator S
      (bar q (P.r 2) * bar q (P.r 3) -
        bar q (P.g 2) * bar q ((P.r 2 : ℤ) + P.r 3 - P.g 2)) = 0 ↔
      P.r 2 = q.val ∧ P.g 1 = P.g 2 := by
  classical
  dsimp only
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  change eraseGenerator S
    (bar q (P.r 2) * bar q (P.r 3) -
      bar q (P.g 2) * bar q ((P.r 2 : ℤ) + P.r 3 - P.g 2)) = 0 ↔
    P.r 2 = q.val ∧ P.g 1 = P.g 2
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hthick := hP.thick 1 2 (by decide)
  change P.g 1 + P.g 2 < P.r 2 at hthick
  by_cases hst : P.g 1 = P.g 2
  · have ht0 : eraseGenerator S (bar q (P.g 2)) = 0 := by
      rw [erase_bar, if_pos]
      exact Or.inr (by dsimp [S]; exact_mod_cast hst.symm)
    have hD : eraseGenerator S (bar q (P.r 3)) ≠ 0 :=
      erase_bar_ne_zero (by have := P.r_pos 3; positivity)
        (by omega) (by dsimp [S]; omega)
    have hC : eraseGenerator S (bar q (P.r 2)) = 0 ↔ P.r 2 = q.val := by
      by_cases hcq : P.r 2 = q.val
      · simp [erase_bar, hcq]
      · have hn := erase_bar_ne_zero (q := q) (v := S)
          (by have := P.r_pos 2; positivity : (0 : ℤ) < P.r 2)
          (by exact_mod_cast hcq) (by dsimp [S]; omega)
        simp [hn, hcq]
    simp only [map_sub, map_mul, ht0, zero_mul, sub_zero, mul_eq_zero,
      hC, hD, or_false]
    simp [hst]
  · have hn := erased_two_factor_ne_zero_of_full_survives q S
      (P.r 2) (P.r 3) (P.g 2)
      (by exact_mod_cast hP.gap_pos 2)
      (by exact_mod_cast P.g_lt_castSucc 2)
      (by exact_mod_cast P.g_lt_succ 2)
      (by exact_mod_cast hP.gap_ne 2)
      (by dsimp [S]; exact_mod_cast Ne.symm hst)
      (by omega) (by dsimp [S]; omega)
    exact ⟨fun hz => (hn hz).elim, fun hc => (hst hc.2).elim⟩

/-- Exact middle-gap criterion for four rows.  The three listed contacts are
alternatives; their intersection is not an extra multiplicative contribution. -/
theorem four_middle_gap_dvd_iff {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) :
    let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
    MvPolynomial.X S ∣ restriction q P ↔
      (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
      (P.r 2 = q.val ∧ P.g 1 = P.g 2) ∨
      (((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ∧ P.r 0 = P.g 1) := by
  classical
  dsimp only
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  have hleft := erased_two_factor_eq_zero_iff q S (P.r 0) (P.r 1) (P.g 0)
    (by exact_mod_cast hP.gap_pos 0)
    (by exact_mod_cast P.g_lt_castSucc 0)
    (by exact_mod_cast P.g_lt_succ 0)
    (by dsimp [S]; exact_mod_cast P.g_lt_castSucc 1)
    (by exact_mod_cast ha) (by exact_mod_cast hP.gap_ne 0)
  have hright := four_bottom_factor_zero_iff hP
  constructor
  · intro hd
    have hz := erase_eq_zero_of_X_dvd S _ hd
    rw [restriction_four_middle_cut q S P hP.thick rfl, mul_eq_zero] at hz
    rcases hz with hz | hz
    · have he := hleft.mp (by simpa only [map_mul, map_sub, mul_comm] using hz)
      rcases he with ⟨hb, hrs⟩ | ⟨has, hu⟩
      · exact Or.inl ⟨by exact_mod_cast hb, by exact_mod_cast hrs⟩
      · exact Or.inr (Or.inr ⟨hu, by exact_mod_cast has⟩)
    · have he := hright.mp (by simpa only [map_mul, map_sub, mul_comm] using hz)
      exact Or.inr (Or.inl he)
  · intro hc
    have hd := restriction_four_middle_content_dvd P hP.thick hc
    have he : bar q (P.g 1) = MvPolynomial.X S := by
      rw [bar, eraseGenerator_complete, if_neg (by exact_mod_cast hP.gap_ne 1)]
      exact complete_nat S
    rwa [he] at hd

/-- Every extracted variable lies strictly below the cut index.  Its proof
uses actual simultaneous high-gap cuts and nonzero double-erased components. -/
theorem content_variable_lt_cut {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (v : ℕ+) (hv : MvPolynomial.X v ∣ monicContent hP) :
    v.val < q.val := by
  obtain ⟨j, hj⟩ := variable_dvd_content_is_gap hP v hv
  have hneq : v.val ≠ q.val := by
    intro he
    exact hP.gap_ne j (hj.trans he)
  by_contra hn
  have hqv : q.val < v.val := by omega
  have hd : MvPolynomial.X v ∣ restriction q P :=
    hv.trans ⟨monicPrimitive hP, restriction_eq_monicContent_mul hP⟩
  exact variable_not_dvd_restriction_of_high_gap hP v hqv ⟨j, hj⟩ hd

/-- The support form of the low-gap assertion. -/
theorem contentExponent_support_lt_cut {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (v : ℕ+) (hv : v ∈ (contentExponent hP).support) :
    v.val < q.val := by
  apply content_variable_lt_cut hP v
  simpa only [monicContent, MvPolynomial.X_dvd_monomial, one_ne_zero, false_or,
    Finsupp.mem_support_iff] using hv

/-- If both rows exceed the additional cut, even erasing their merged full
interval leaves a nonzero positive row product. -/
theorem erased_two_factor_ne_zero_of_rows_above (q v : ℕ+) (a b r : ℤ)
    (hr : 0 < r) (hra : r < a) (hrb : r < b)
    (hva : (v.val : ℤ) < a) (hvb : (v.val : ℤ) < b)
    (hrq : r ≠ (q.val : ℤ)) (hrv : r ≠ (v.val : ℤ)) :
    eraseGenerator v (bar q a * bar q b - bar q r * bar q (a + b - r)) ≠ 0 := by
  by_cases huq : a + b - r = (q.val : ℤ)
  · have hU0 : eraseGenerator v (bar q (a + b - r)) = 0 := by simp [erase_bar, huq]
    have hA := erase_bar_ne_zero (q := q) (v := v) (by omega : 0 < a)
      (by omega) (ne_of_gt hva)
    have hB := erase_bar_ne_zero (q := q) (v := v) (by omega : 0 < b)
      (by omega) (ne_of_gt hvb)
    simpa only [map_sub, map_mul, hU0, mul_zero, sub_zero] using mul_ne_zero hA hB
  · exact erased_two_factor_ne_zero_of_full_survives q v a b r hr hra hrb hrq hrv
      huq (by omega)

/-- A four-row first-gap value distinct from the middle gap cannot be a
variable divisor when the first row is not erased. -/
theorem four_first_gap_not_dvd {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) (hrs : P.g 0 ≠ P.g 1) :
    let R : ℕ+ := ⟨P.g 0, hP.gap_pos 0⟩
    ¬ MvPolynomial.X R ∣ restriction q P := by
  classical
  dsimp only
  let R : ℕ+ := ⟨P.g 0, hP.gap_pos 0⟩
  have hr0 : eraseGenerator R (bar q (P.g 0)) = 0 := by
    rw [erase_bar, if_pos]
    exact Or.inr rfl
  have hA : eraseGenerator R (bar q (P.r 0)) ≠ 0 :=
    erase_bar_ne_zero (by have := P.r_pos 0; positivity)
      (by exact_mod_cast ha) (by dsimp [R]; exact_mod_cast ne_of_gt (P.g_lt_castSucc 0))
  have ht1 := hP.thick 0 1 (by decide)
  have ht2 := hP.thick 1 2 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at ht1
  change P.g 1 + P.g 2 < P.r 2 at ht2
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hcut : eraseGenerator R (restriction q P) =
      eraseGenerator R (bar q (P.r 0)) *
        threeInterval (fun k => eraseGenerator R (bar q k))
          (P.r 1) (P.r 2) (P.r 3) (P.g 1) (P.g 2) := by
    rw [restriction_four_expansion q P hP.thick]
    simp only [fourInterval, threeInterval, map_add, map_sub, map_mul, hr0]
    ring
  have hF : threeInterval (fun k => eraseGenerator R (bar q k))
      (P.r 1) (P.r 2) (P.r 3) (P.g 1) (P.g 2) ≠ 0 := by
    by_cases htr : P.g 2 = P.g 0
    · have ht0 : eraseGenerator R (bar q (P.g 2)) = 0 := by
        rw [erase_bar, if_pos]
        exact Or.inr (by dsimp [R]; exact_mod_cast htr)
      have hD : eraseGenerator R (bar q (P.r 3)) ≠ 0 :=
        erase_bar_ne_zero (by have := P.r_pos 3; positivity)
          (by omega) (by dsimp [R]; omega)
      have hBC := erased_two_factor_ne_zero_of_rows_above q R (P.r 1) (P.r 2) (P.g 1)
        (by exact_mod_cast hP.gap_pos 1)
        (by exact_mod_cast P.g_lt_castSucc 1)
        (by exact_mod_cast P.g_lt_succ 1)
        (by dsimp [R]; omega) (by dsimp [R]; omega)
        (by exact_mod_cast hP.gap_ne 1) (by dsimp [R]; exact_mod_cast Ne.symm hrs)
      have he :
          threeInterval (fun k => eraseGenerator R (bar q k))
            (P.r 1) (P.r 2) (P.r 3) (P.g 1) (P.g 2) =
          eraseGenerator R (bar q (P.r 1) * bar q (P.r 2) -
            bar q (P.g 1) * bar q ((P.r 1 : ℤ) + P.r 2 - P.g 1)) *
              eraseGenerator R (bar q (P.r 3)) := by
        simp only [threeInterval, map_mul, map_sub, ht0]
        ring
      rw [he]
      exact mul_ne_zero hBC hD
    · let Q := GeneralHessenberg.slice P 1 2 (by decide)
      have hr0 : Q.r 0 = P.r 1 := rfl
      have hr1 : Q.r 1 = P.r 2 := rfl
      have hr2 : Q.r 2 = P.r 3 := rfl
      have hg0 : Q.g 0 = P.g 1 := rfl
      have hg1 : Q.g 1 = P.g 2 := rfl
      have hQ : QComponent q Q := by
        refine ⟨GeneralHessenberg.slice_thick hP.thick 1 2 (by decide), ?_, ?_, ?_⟩
        · intro j
          fin_cases j
          · change 0 < Q.g 0
            rw [hg0]
            exact hP.gap_pos 1
          · change 0 < Q.g 1
            rw [hg1]
            exact hP.gap_pos 2
        · intro j
          fin_cases j
          · change Q.g 0 ≠ q.val
            rw [hg0]
            exact hP.gap_ne 1
          · change Q.g 1 ≠ q.val
            rw [hg1]
            exact hP.gap_ne 2
        · simpa [lastGap, Fin.sum_univ_succ, hr2, hg0, hg1] using hbottom
      have hf : (R.val : ℤ) < fullIndex Q := by
        rw [fullIndex_three, hr0, hr1, hr2, hg0, hg1]
        change (P.g 0 : ℤ) < (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2
        have hlast := P.g_lt_succ 2
        change P.g 2 < P.r 3 at hlast
        omega
      have hfull : fullGenerator Q ≠ R := by
        intro he
        have hv := congrArg (fun p : ℕ+ => (p.val : ℤ)) he
        rw [fullGenerator_int_coe] at hv
        exact (ne_of_gt hf) hv
      have hne := erase_restriction_ne_zero hQ R
        (by
          intro j
          fin_cases j
          · change P.g 1 ≠ P.g 0; exact Ne.symm hrs
          · change P.g 2 ≠ P.g 0; exact htr)
        hfull
      rw [restriction_three_expansion q Q hQ.thick] at hne
      simpa only [hr0, hr1, hr2, hg0, hg1, threeInterval,
        map_add, map_sub, map_mul] using hne
  intro hd
  have hz := erase_eq_zero_of_X_dvd R _ hd
  rw [hcut] at hz
  exact mul_ne_zero hA hF hz

/-- Erasing the full interval of a three-row prefix does not kill the
remaining polynomial when its bottom row exceeds the extra cut. -/
theorem three_prefix_full_cut_ne_zero (q t : ℕ+) (a b c r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (hra : r < a) (hrsb : r + s < b)
    (hsc : s < c) (htc : (t.val : ℤ) < c)
    (hrt : r ≠ (t.val : ℤ)) (hst : s ≠ (t.val : ℤ))
    (hq : a + b + c - r - s = (q.val : ℤ)) :
    threeInterval (fun k => eraseGenerator t (bar q k)) a b c r s ≠ 0 := by
  classical
  let u : ℤ := a + b - r
  let v : ℤ := b + c - s
  let E (z : ℤ) : CompleteRing →+* ℚ :=
    MvPolynomial.eval (fun j : ℕ+ => if (j.val : ℤ) = z then 2 else 1)
  have hev (z k : ℤ) (hk : 0 < k) (hkq : k < (q.val : ℤ)) :
      E z (eraseGenerator t (bar q k)) =
        if k = (t.val : ℤ) then 0 else if k = z then 2 else 1 := by
    rw [erase_bar]
    by_cases hkt : k = (t.val : ℤ)
    · rw [if_pos (Or.inr hkt), map_zero, if_pos hkt]
    · rw [if_neg (by omega), if_neg hkt, complete_of_pos hk]
      have hnat : ((k.toNat : ℕ) : ℤ) = k := by omega
      simp only [E, MvPolynomial.eval_X, PNat.mk_coe, hnat]
  have hfull0 : eraseGenerator t (bar q (a + b + c - r - s)) = 0 := by
    simp [erase_bar, hq]
  have hineq :
      0 < a ∧ 0 < b ∧ 0 < c ∧
      a < (q.val : ℤ) ∧ b < (q.val : ℤ) ∧ c < (q.val : ℤ) ∧
      r < (q.val : ℤ) ∧ s < (q.val : ℤ) ∧
      0 < u ∧ u < (q.val : ℤ) ∧ 0 < v ∧ v < (q.val : ℤ) ∧
      a < u ∧ b < u ∧ b < v ∧ c < v := by dsimp [u, v]; omega
  have hT (z : ℤ) :
      E z (threeInterval (fun k => eraseGenerator t (bar q k)) a b c r s) =
        (if a = (t.val : ℤ) then 0 else if a = z then 2 else 1) *
        (if b = (t.val : ℤ) then 0 else if b = z then 2 else 1) *
        (if c = (t.val : ℤ) then 0 else if c = z then 2 else 1) -
        (if u = (t.val : ℤ) then 0 else if u = z then 2 else 1) *
        (if r = (t.val : ℤ) then 0 else if r = z then 2 else 1) *
        (if c = (t.val : ℤ) then 0 else if c = z then 2 else 1) -
        (if a = (t.val : ℤ) then 0 else if a = z then 2 else 1) *
        (if v = (t.val : ℤ) then 0 else if v = z then 2 else 1) *
        (if s = (t.val : ℤ) then 0 else if s = z then 2 else 1) := by
    simp only [threeInterval, map_add, map_sub, map_mul, hfull0, map_zero, zero_mul, mul_zero,
      add_zero]
    rw [hev z a (by omega) (by omega), hev z b (by omega) (by omega),
      hev z c (by omega) (by omega), hev z r hr (by omega), hev z s hs (by omega),
      hev z u (by dsimp [u]; omega) (by dsimp [u]; omega),
      hev z v (by dsimp [v]; omega) (by dsimp [v]; omega)]
  intro hz
  by_cases hat : a = (t.val : ℤ)
  · have he := hT 0
    rw [hz, map_zero] at he
    have hut : u ≠ (t.val : ℤ) := by dsimp [u]; omega
    norm_num [hat, hut, hrt, hst, ne_of_gt hr, ne_of_gt hs,
      show c ≠ (t.val : ℤ) by omega,
      show c ≠ 0 by omega, show u ≠ 0 by dsimp [u]; omega] at he
  · by_cases hbt : b = (t.val : ℤ)
    · have he := hT 0
      rw [hz, map_zero] at he
      have hut : u ≠ (t.val : ℤ) := by dsimp [u]; omega
      have hvt : v ≠ (t.val : ℤ) := by dsimp [v]; omega
      norm_num [hat, hbt, hut, hvt, hrt, hst, ne_of_gt hr, ne_of_gt hs,
        show a ≠ 0 by omega, show c ≠ 0 by omega,
        show c ≠ (t.val : ℤ) by omega,
        show u ≠ 0 by dsimp [u]; omega, show v ≠ 0 by dsimp [v]; omega] at he
    · by_cases hut : u = (t.val : ℤ)
      · have he := hT v
        rw [hz, map_zero] at he
        have hva : a ≠ v := by dsimp [u, v] at *; omega
        have hvb : b ≠ v := by dsimp [v]; omega
        have hvc : c ≠ v := by dsimp [v]; omega
        have hvr : r ≠ v := by dsimp [v]; omega
        have hvs : s ≠ v := by dsimp [v]; omega
        have hvt : v ≠ (t.val : ℤ) := by dsimp [v]; omega
        norm_num [hat, hbt, hut, hrt, hst, hva, hvb, hvc, hvr, hvs, hvt,
          show c ≠ (t.val : ℤ) by omega] at he
      · have he := hT 0
        rw [hz, map_zero] at he
        have hvt : v ≠ (t.val : ℤ) := by dsimp [v]; omega
        norm_num [hat, hbt, hut, hrt, hst, hvt, ne_of_gt hr, ne_of_gt hs,
          show a ≠ 0 by omega, show b ≠ 0 by omega, show c ≠ 0 by omega,
          show c ≠ (t.val : ℤ) by omega,
          show u ≠ 0 by dsimp [u]; omega, show v ≠ 0 by dsimp [v]; omega] at he

/-- The last gap, unless equal to the middle one, is not a divisor.  The
prefix full-index collision with q is retained and proved separately. -/
theorem four_last_gap_not_dvd {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) (hst : P.g 1 ≠ P.g 2) :
    let T : ℕ+ := ⟨P.g 2, hP.gap_pos 2⟩
    ¬ MvPolynomial.X T ∣ restriction q P := by
  classical
  dsimp only
  let T : ℕ+ := ⟨P.g 2, hP.gap_pos 2⟩
  by_cases hrt : P.g 0 = P.g 2
  · have hrs : P.g 0 ≠ P.g 1 := by omega
    have hn := four_first_gap_not_dvd hP ha hrs
    simpa [hrt] using hn
  have ht0 : eraseGenerator T (bar q (P.g 2)) = 0 := by
    rw [erase_bar, if_pos]
    exact Or.inr rfl
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have ht1 := hP.thick 0 1 (by decide)
  have ht2 := hP.thick 1 2 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at ht1
  change P.g 1 + P.g 2 < P.r 2 at ht2
  have hD : eraseGenerator T (bar q (P.r 3)) ≠ 0 :=
    erase_bar_ne_zero (by have := P.r_pos 3; positivity) (by omega) (by dsimp [T]; omega)
  have hcut : eraseGenerator T (restriction q P) =
      threeInterval (fun k => eraseGenerator T (bar q k))
        (P.r 0) (P.r 1) (P.r 2) (P.g 0) (P.g 1) *
          eraseGenerator T (bar q (P.r 3)) := by
    rw [restriction_four_expansion q P hP.thick]
    simp only [fourInterval, threeInterval, map_add, map_sub, map_mul, ht0]
    ring
  have hF : threeInterval (fun k => eraseGenerator T (bar q k))
      (P.r 0) (P.r 1) (P.r 2) (P.g 0) (P.g 1) ≠ 0 := by
    by_cases hxq : (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 = q.val
    · exact three_prefix_full_cut_ne_zero q T _ _ _ _ _
        (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
        (by exact_mod_cast P.g_lt_castSucc 0) (by exact_mod_cast ht1)
        (by exact_mod_cast P.g_lt_succ 1) (by dsimp [T]; omega)
        (by dsimp [T]; exact_mod_cast hrt) (by dsimp [T]; exact_mod_cast hst) hxq
    · let Q := GeneralHessenberg.slice P 0 2 (by decide)
      have hQ := GeneralHessenberg.slice_thick hP.thick 0 2 (by decide)
      have hr0 : Q.r 0 = P.r 0 := rfl
      have hr1 : Q.r 1 = P.r 1 := rfl
      have hr2 : Q.r 2 = P.r 2 := rfl
      have hg0 : Q.g 0 = P.g 0 := rfl
      have hg1 : Q.g 1 = P.g 1 := rfl
      have hx : fullIndex Q =
          (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 := by
        rw [fullIndex_three, hr0, hr1, hr2, hg0, hg1]
      have hfull (v : ℕ+) (hv : fullIndex Q ≠ (v.val : ℤ)) : fullGenerator Q ≠ v := by
        intro he
        apply hv
        rw [← fullGenerator_int_coe Q, he]
      have hq : fullGenerator Q ≠ q := hfull q (by rw [hx]; exact hxq)
      have ht : fullGenerator Q ≠ T := hfull T (by
        rw [hx]
        have hr := P.g_lt_castSucc 0
        change P.g 0 < P.r 0 at hr
        change (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 ≠ (P.g 2 : ℤ)
        omega)
      have hn := double_erase_schur_ne_zero hQ q T hq ht
        (by
          intro j
          fin_cases j
          · change P.g 0 ≠ q.val; exact hP.gap_ne 0
          · change P.g 1 ≠ q.val; exact hP.gap_ne 1)
        (by
          intro j
          fin_cases j
          · change P.g 0 ≠ P.g 2; exact hrt
          · change P.g 1 ≠ P.g 2; exact hst)
      change eraseGenerator T (restriction q Q) ≠ 0 at hn
      rw [restriction_three_expansion q Q hQ] at hn
      simpa only [hr0, hr1, hr2, hg0, hg1, threeInterval,
        map_add, map_sub, map_mul] using hn
  intro hd
  have hz := erase_eq_zero_of_X_dvd T _ hd
  rw [hcut] at hz
  exact mul_ne_zero hF hD hz

/-- The four-row support calculation: only the middle gap can remain in
content once the first row survives the q-erasure. -/
theorem four_contentExponent_supported_middle {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) (v : ℕ+)
    (hv : v.val ≠ P.g 1) : contentExponent hP v = 0 := by
  classical
  by_contra hn
  have hdG : MvPolynomial.X v ∣ monicContent hP := by
    simpa only [monicContent, MvPolynomial.X_dvd_monomial, one_ne_zero, false_or] using hn
  have hd : MvPolynomial.X v ∣ restriction q P :=
    hdG.trans ⟨monicPrimitive hP, restriction_eq_monicContent_mul hP⟩
  obtain ⟨j, hj⟩ := variable_dvd_content_is_gap hP v hdG
  fin_cases j
  · have hrs : P.g 0 ≠ P.g 1 := fun he => hv (hj.symm.trans he)
    have hnR := four_first_gap_not_dvd hP ha hrs
    have hV : (⟨P.g 0, hP.gap_pos 0⟩ : ℕ+) = v := Subtype.ext hj
    exact hnR (by rwa [hV])
  · exact hv hj.symm
  · have hst : P.g 1 ≠ P.g 2 := fun he => hv (hj.symm.trans he.symm)
    have hnT := four_last_gap_not_dvd hP ha hst
    have hV : (⟨P.g 2, hP.gap_pos 2⟩ : ℕ+) = v := Subtype.ext hj
    exact hnT (by rwa [hV])

/-- The support and divisibility calculations reduce the nonendpoint
four-row table to the first-order multiplicity statement. -/
theorem four_content_of_middle_square_not_dvd {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hSquare : let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
      ¬ (MvPolynomial.X S : CompleteRing) ^ 2 ∣ restriction q P) :
    monicContent hP =
      if (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
          (P.r 2 = q.val ∧ P.g 1 = P.g 2) ∨
          (((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ∧ P.r 0 = P.g 1)
      then complete (P.g 1) else 1 := by
  classical
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  have hS : contentExponent hP S ≠ 0 ↔
      (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
      (P.r 2 = q.val ∧ P.g 1 = P.g 2) ∨
      (((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ∧ P.r 0 = P.g 1) := by
    have he := (gap_variable_dvd_content_iff hP 1).trans (four_middle_gap_dvd_iff hP ha)
    simpa only [monicContent, MvPolynomial.X_dvd_monomial, one_ne_zero, false_or] using he
  have hlt : contentExponent hP S < 2 := by
    by_contra hn
    have hdG : (MvPolynomial.X S : CompleteRing) ^ 2 ∣ monicContent hP := by
      rw [MvPolynomial.X_pow_eq_monomial, monicContent,
        MvPolynomial.monomial_one_dvd_monomial_one]
      exact Finsupp.single_le_iff.mpr (by omega)
    exact hSquare (hdG.trans ⟨monicPrimitive hP, restriction_eq_monicContent_mul hP⟩)
  have hrest (v : ℕ+) (hv : v ≠ S) : contentExponent hP v = 0 :=
    four_contentExponent_supported_middle hP ha v (by
      intro he
      exact hv (Subtype.ext he))
  split_ifs with hc
  · have hp := hS.mpr hc
    have hval : contentExponent hP S = 1 := by omega
    have he : contentExponent hP = Finsupp.single S 1 := by
      ext v
      by_cases hv : v = S
      · subst v; simp [hval]
      · simp [hrest v hv, Finsupp.single_apply, hv, Ne.symm hv]
    rw [monicContent, he]
    exact (complete_nat S).symm
  · have hval : contentExponent hP S = 0 := not_ne_iff.mp (mt hS.mp hc)
    have he : contentExponent hP = 0 := by
      ext v
      by_cases hv : v = S
      · subst v; exact hval
      · exact hrest v hv
    simp [monicContent, he]

/-- Exact affine coefficient and residual scaling transports the actual gcd,
including the multiplicity of a repeated extracted gap. -/
theorem monicContent_of_gap_scaling {n m : ℕ} {q : ℕ+}
    {P : Profile n} {Q : Profile m} (hP : QComponent q P) (hQ : QComponent q Q)
    (r : ℕ+) (hgap : gapMonomial P = MvPolynomial.X r * gapMonomial Q)
    (hres : residual q P = -MvPolynomial.X r * residual q Q) :
    monicContent hP = MvPolynomial.X r * monicContent hQ := by
  classical
  have hass : Associated (content q P) (MvPolynomial.X r * content q Q) := by
    unfold content
    rw [hgap, hres]
    have he : -(MvPolynomial.X r : CompleteRing) * residual q Q =
        MvPolynomial.X r * (-residual q Q) := by ring
    rw [he]
    have hm := gcd_mul_left' (MvPolynomial.X r) (gapMonomial Q) (-residual q Q)
    simpa only [gcd_neg] using hm
  have hnormP : Associated (content q P) (monicContent hP) := by
    rw [content_eq_monicContent_mul_unit hP]
    exact associated_mul_unit_left _ _ ((content_monomial_spec hP).2.1.map MvPolynomial.C)
  have hnormQ : Associated (content q Q) (monicContent hQ) := by
    rw [content_eq_monicContent_mul_unit hQ]
    exact associated_mul_unit_left _ _ ((content_monomial_spec hQ).2.1.map MvPolynomial.C)
  have hG := hnormP.symm.trans (hass.trans (hnormQ.mul_left (MvPolynomial.X r)))
  have hright : MvPolynomial.X r * monicContent hQ =
      MvPolynomial.monomial (Finsupp.single r 1 + contentExponent hQ) 1 := by
    simp [monicContent, MvPolynomial.X, MvPolynomial.monomial_mul_monomial]
  rw [hright] at hG ⊢
  have hle : contentExponent hP ≤ Finsupp.single r 1 + contentExponent hQ :=
    MvPolynomial.monomial_one_dvd_monomial_one.mp hG.dvd
  have hge : Finsupp.single r 1 + contentExponent hQ ≤ contentExponent hP :=
    MvPolynomial.monomial_one_dvd_monomial_one.mp hG.symm.dvd
  simp [monicContent, le_antisymm hle hge]

/-- Above-q first rows cannot create the merged-interval contact in the
three-row content table. -/
theorem three_content_first_above_cut {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (hnew : (q.val : ℤ) < P.r 0) :
    monicContent hP =
      if P.r 1 = q.val ∧ P.g 0 = P.g 1 then complete (P.g 1) else 1 := by
  have hfirst : P.r 0 ≠ q.val := by omega
  have hmerge : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by
    have hg := P.g_lt_succ 0
    change P.g 0 < P.r 1 at hg
    omega
  simpa only [if_neg hfirst, hmerge, false_and, or_false] using three_content hP

/-- The first-row-erased four-row branch contracts to the actual three-row
profile.  Its repeated first/second gap contributions retain multiplicity. -/
theorem four_content_first_row {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 = q.val) :
    monicContent hP =
      if P.r 2 = q.val ∧ P.g 1 = P.g 2
      then complete (P.g 0) * complete (P.g 1) else complete (P.g 0) := by
  classical
  let C := GeneralHessenberg.contract P 0
  let R : ℕ+ := ⟨P.g 0, hP.gap_pos 0⟩
  have hb := GeneralHessenberg.contract_beta P 0
  have hrow0 : (C.r 0 : ℤ) = (P.r 0 : ℤ) + P.r 1 - P.g 0 :=
    GeneralHessenberg.contract_joined_row P 0
  have hrow1 : C.r 1 = P.r 2 := by
    apply Int.ofNat_injective
    change (C.r 1 : ℤ) = (P.r 2 : ℤ)
    rw [← C.xi_sub_zeta 1]
    change (GeneralHessenberg.contract P 0).xi 1 -
      (GeneralHessenberg.contract P 0).zeta 1 = (P.r 2 : ℤ)
    rw [hb.1, hb.2]
    simpa [Fin.succAbove] using P.xi_sub_zeta (2 : Fin 4)
  have hrow2 : C.r 2 = P.r 3 := by
    apply Int.ofNat_injective
    change (C.r 2 : ℤ) = (P.r 3 : ℤ)
    rw [← C.xi_sub_zeta 2]
    change (GeneralHessenberg.contract P 0).xi 2 -
      (GeneralHessenberg.contract P 0).zeta 2 = (P.r 3 : ℤ)
    rw [hb.1, hb.2]
    simpa [Fin.succAbove] using P.xi_sub_zeta (3 : Fin 4)
  have hg0 : C.g 0 = P.g 1 := by
    simpa [C, Fin.succAbove] using GeneralHessenberg.contract_gap P 0 (0 : Fin 2)
  have hg1 : C.g 1 = P.g 2 := by
    simpa [C, Fin.succAbove] using GeneralHessenberg.contract_gap P 0 (1 : Fin 2)
  have hC : QComponent q C := by
    refine ⟨GeneralHessenberg.contract_thick hP.thick 0, ?_, ?_, ?_⟩
    · intro j
      fin_cases j
      · simpa [hg0] using hP.gap_pos (1 : Fin 3)
      · simpa [hg1] using hP.gap_pos (2 : Fin 3)
    · intro j
      fin_cases j
      · simpa [hg0] using hP.gap_ne (1 : Fin 3)
      · simpa [hg1] using hP.gap_ne (2 : Fin 3)
    · have hbottom := hP.bottom
      simpa [lastGap, Fin.sum_univ_succ, hg0, hg1, hrow2] using hbottom
  have hnew : (q.val : ℤ) < C.r 0 := by
    have hmid := hP.thick 0 1 (by decide)
    change P.g 0 + P.g 1 < P.r 1 at hmid
    omega
  have hIndex : fullIndex P = fullIndex C := by
    change P.xi 0 - P.zeta 3 = C.xi 0 - C.zeta 2
    change P.xi 0 - P.zeta 3 =
      (GeneralHessenberg.contract P 0).xi 0 - (GeneralHessenberg.contract P 0).zeta 2
    rw [hb.1, hb.2]
    simp [Fin.succAbove]
  have hgen : fullGenerator P = fullGenerator C := by
    apply Subtype.ext
    change (fullIndex P).toNat = (fullIndex C).toNat
    rw [hIndex]
  have hgap : gapMonomial P = MvPolynomial.X R * gapMonomial C := by
    have hR : complete (P.g 0) = MvPolynomial.X R := complete_nat R
    simp [gapMonomial, Fin.prod_univ_succ, hg0, hg1, hR, mul_assoc]
  have hbarR : bar q (P.g 0) = MvPolynomial.X R := by
    rw [bar, eraseGenerator_complete, if_neg (by exact_mod_cast hP.gap_ne 0)]
    exact complete_nat R
  have hcut : restriction q P = -MvPolynomial.X R * restriction q C := by
    rw [restriction_four_first_row_cut P hP.thick ha,
      restriction_three_expansion q C hC.thick, hbarR]
    simp only [hrow0, hrow1, hrow2, hg0, hg1]
  have haffP := restriction_affine hP
  have haffC := restriction_affine hC
  rw [hgap, hgen] at haffP
  norm_num at haffP haffC
  have hres : residual q P = -MvPolynomial.X R * residual q C := by
    linear_combination -haffP - MvPolynomial.X R * haffC + hcut
  rw [monicContent_of_gap_scaling hP hC R hgap hres,
    three_content_first_above_cut hC hnew]
  have hR : MvPolynomial.X R = complete (P.g 0) := (complete_nat R).symm
  simp only [hrow1, hg0, hg1, hR, mul_ite, mul_one]
  split_ifs with hc
  · rw [hc.2]
  · rfl

/-- A first-order coefficient nonzero after erasure excludes a square divisor. -/
theorem not_X_square_dvd_of_first_coefficient (v : ℕ+) (p : CompleteRing)
    (hp : eraseGenerator v (MvPolynomial.pderiv v p) ≠ 0) :
    ¬ (MvPolynomial.X v : CompleteRing) ^ 2 ∣ p := by
  rintro ⟨f, hf⟩
  apply hp
  rw [hf, pow_two]
  simp [MvPolynomial.pderiv_mul, eraseGenerator, map_add, map_mul]

/-- The full-interval primitive cannot have an internal gap variable divisor. -/
theorem gap_variable_not_dvd_monicPrimitive {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (j : Fin n) :
    let V : ℕ+ := ⟨P.g j, hP.gap_pos j⟩
    ¬ MvPolynomial.X V ∣ monicPrimitive hP := by
  classical
  dsimp only
  let V : ℕ+ := ⟨P.g j, hP.gap_pos j⟩
  intro hd
  have hdK : MvPolynomial.X V ∣ canonicalPrimitive hP := dvd_mul_of_dvd_right hd _
  have hback : canonicalPrimitive hP ∣ MvPolynomial.X V :=
    (MvPolynomial.X_prime (i := V)).irreducible.dvd_symm
      (canonicalPrimitive_irreducible hP) hdK
  have hidx := index_lt_full P j.succ j.castSucc (Or.inl (Fin.succ_ne_zero j))
  rw [P.xi_succ_sub_zeta_castSucc] at hidx
  have hneq : fullGenerator P ≠ V := by
    intro he
    have hv := congrArg Subtype.val he
    have hp := P.toBetaDiagram.largestLabel_pos
    dsimp [fullGenerator, V, fullIndex] at *
    omega
  have hn : fullGenerator P ∉ (MvPolynomial.X V : CompleteRing).vars := by simp [hneq]
  exact not_mem_vars_of_dvd (MvPolynomial.X_ne_zero V) hback _ hn
    (full_mem_canonicalPrimitive hP)

/-- All powers of an internal gap are extracted in the actual content, not
merely their first divisibility bit. -/
theorem gap_power_dvd_content_iff {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (j : Fin n) (k : ℕ) :
    let V : ℕ+ := ⟨P.g j, hP.gap_pos j⟩
    (MvPolynomial.X V : CompleteRing) ^ k ∣ monicContent hP ↔
      (MvPolynomial.X V : CompleteRing) ^ k ∣ restriction q P := by
  classical
  dsimp only
  constructor
  · intro hd
    exact hd.trans ⟨monicPrimitive hP, restriction_eq_monicContent_mul hP⟩
  · intro hd
    rw [restriction_eq_monicContent_mul hP] at hd
    exact (MvPolynomial.X_prime).pow_dvd_of_dvd_mul_right k
      (gap_variable_not_dvd_monicPrimitive hP j) hd

/-- If the middle label occurs only once among the gaps, its exponent is
automatically at most one; no separate multiplicity calculation is needed. -/
theorem four_middle_square_not_dvd_of_unique_gap {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hrs : P.g 0 ≠ P.g 1) (hst : P.g 1 ≠ P.g 2) :
    let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
    ¬ (MvPolynomial.X S : CompleteRing) ^ 2 ∣ restriction q P := by
  classical
  dsimp only
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  intro hd
  have hdG := (gap_power_dvd_content_iff hP 1 2).mpr hd
  rw [MvPolynomial.X_pow_eq_monomial, monicContent,
    MvPolynomial.monomial_one_dvd_monomial_one] at hdG
  have hlow : 2 ≤ contentExponent hP S := Finsupp.single_le_iff.mp hdG
  have hhigh := (content_monomial_spec hP).1 S
  have h0 : (⟨P.g 0, hP.gap_pos 0⟩ : ℕ+) ≠ S := by
    intro h
    exact hrs (congrArg Subtype.val h)
  have h2 : (⟨P.g 2, hP.gap_pos 2⟩ : ℕ+) ≠ S := by
    intro h
    exact hst (congrArg Subtype.val h).symm
  have hhigh' : contentExponent hP S ≤ 1 := by
    simpa [gapExponent, Fin.sum_univ_succ, Finsupp.single_apply, h0, h2, S] using hhigh
  omega

theorem pderiv_bar_eq_zero_of_ne (q v : ℕ+) (k : ℤ)
    (hk : k ≠ (v.val : ℤ)) : MvPolynomial.pderiv v (bar q k) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  apply not_mem_vars_erase q v
  rw [mem_vars_complete_iff]
  simpa [eq_comm] using hk

/-- Exact first coefficient when all three seams share a gap variable. -/
theorem four_equal_gaps_first_coefficient (q s : ℕ+) (a b c d : ℤ)
    (hsq : s ≠ q) (ha : (s.val : ℤ) < a) (hb : (s.val : ℤ) < b)
    (hc : (s.val : ℤ) < c) (hd : (s.val : ℤ) < d) :
    eraseGenerator s (MvPolynomial.pderiv s
      (fourInterval (bar q) a b c d s.val s.val s.val)) =
      -(eraseGenerator s (bar q (a + b - s.val)) *
          eraseGenerator s (bar q c) * eraseGenerator s (bar q d) +
        eraseGenerator s (bar q a) * eraseGenerator s (bar q (b + c - s.val)) *
          eraseGenerator s (bar q d) +
        eraseGenerator s (bar q a) * eraseGenerator s (bar q b) *
          eraseGenerator s (bar q (c + d - s.val))) := by
  have hgen : bar q s.val = MvPolynomial.X s := by
    rw [bar, eraseGenerator_complete, if_neg]
    · exact complete_nat s
    · intro he
      exact hsq (pnat_eq_of_int_coe_eq he)
  have hzero (k : ℤ) (hk : (s.val : ℤ) < k) :
      MvPolynomial.pderiv s (bar q k) = 0 :=
    pderiv_bar_eq_zero_of_ne q s k (ne_of_gt hk)
  have hU := hzero (a + b - s.val) (by omega)
  have hV := hzero (b + c - s.val) (by omega)
  have hW := hzero (c + d - s.val) (by omega)
  have hX := hzero (a + b + c - s.val - s.val) (by omega)
  have hY := hzero (b + c + d - s.val - s.val) (by omega)
  have hT := hzero (a + b + c + d - s.val - s.val - s.val) (by omega)
  have hxs : eraseGenerator s (MvPolynomial.X s) = 0 := by simp [eraseGenerator]
  simp only [fourInterval, hgen, map_add, map_sub, MvPolynomial.pderiv_mul,
    hzero a ha, hzero b hb, hzero c hc, hzero d hd, hU, hV, hW, hX, hY, hT,
    MvPolynomial.pderiv_X_self, zero_mul, mul_zero, zero_add, add_zero, mul_one,
    one_mul, sub_zero, zero_sub, map_neg, map_mul, map_zero, map_one, hxs]
  ring

/-- Simultaneous equality of all three gaps does not increase the middle
content exponent.  The surviving one-seam terms have a common negative sign. -/
theorem four_middle_square_not_dvd_equal_gaps {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hrs : P.g 0 = P.g 1) (hst : P.g 1 = P.g 2)
    (hcontact : P.r 1 = q.val ∨ P.r 2 = q.val) :
    let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
    ¬ (MvPolynomial.X S : CompleteRing) ^ 2 ∣ restriction q P := by
  classical
  dsimp only
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  have hsq : S ≠ q := by
    intro he
    exact hP.gap_ne 1 (congrArg Subtype.val he)
  have hrow0 := P.g_lt_castSucc 0
  have hrow1 := P.g_lt_castSucc 1
  have hrow2 := P.g_lt_succ 1
  change P.g 0 < P.r 0 at hrow0
  change P.g 1 < P.r 1 at hrow1
  change P.g 1 < P.r 2 at hrow2
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hcoeff := four_equal_gaps_first_coefficient q S
    (P.r 0) (P.r 1) (P.r 2) (P.r 3) hsq
    (by dsimp [S]; omega) (by dsimp [S]; omega)
    (by dsimp [S]; omega) (by dsimp [S]; omega)
  apply not_X_square_dvd_of_first_coefficient S
  rw [restriction_four_expansion q P hP.thick]
  simp only [hrs, ← hst]
  change eraseGenerator S (MvPolynomial.pderiv S
    (fourInterval (bar q) (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      S.val S.val S.val)) ≠ 0
  rw [hcoeff]
  let E : CompleteRing →+* ℚ := MvPolynomial.eval (fun _ : ℕ+ => (1 : ℚ))
  have hev (k : ℤ) (hk : (S.val : ℤ) < k) :
      E (eraseGenerator S (bar q k)) = if k = (q.val : ℤ) then 0 else 1 := by
    by_cases hkq : k = (q.val : ℤ)
    · simp [erase_bar, hkq]
    · rw [erase_bar, if_neg (by omega), complete_of_pos (by have := S.pos; omega)]
      simp only [E, MvPolynomial.eval_X, if_neg hkq]
  intro hz
  have he := congrArg E hz
  simp only [map_neg, map_add, map_mul, map_zero] at he
  rw [hev (P.r 0) (by dsimp [S]; omega),
    hev (P.r 1) (by dsimp [S]; omega),
    hev (P.r 2) (by dsimp [S]; omega),
    hev (P.r 3) (by dsimp [S]; omega),
    hev ((P.r 0 : ℤ) + P.r 1 - S.val) (by dsimp [S]; omega),
    hev ((P.r 1 : ℤ) + P.r 2 - S.val) (by dsimp [S]; omega),
    hev ((P.r 2 : ℤ) + P.r 3 - S.val) (by dsimp [S]; omega)] at he
  have ha' : (P.r 0 : ℤ) ≠ q.val := by exact_mod_cast ha
  have hd' : (P.r 3 : ℤ) ≠ q.val := by omega
  have hv' : (P.r 1 : ℤ) + P.r 2 - S.val ≠ q.val := by
    dsimp [S]
    rcases hcontact with hb | hc <;> omega
  have hw' : (P.r 2 : ℤ) + P.r 3 - S.val ≠ q.val := by dsimp [S]; omega
  simp only [if_neg ha', if_neg hd', if_neg hv', if_neg hw', mul_one, one_mul] at he
  split_ifs at he <;> norm_num at he

theorem pderiv_erase_bar_eq_zero_of_ne (q s v : ℕ+) (k : ℤ)
    (hk : k ≠ (v.val : ℤ)) :
    MvPolynomial.pderiv v (eraseGenerator s (bar q k)) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  apply not_mem_vars_erase s v
  apply not_mem_vars_erase q v
  rw [mem_vars_complete_iff]
  simpa [eq_comm] using hk

theorem pderiv_erase_bar_self (q s v : ℕ+) (hvq : v ≠ q) (hvs : v ≠ s) :
    MvPolynomial.pderiv v (eraseGenerator s (bar q v.val)) = 1 := by
  rw [erase_bar, if_neg]
  · rw [complete_nat, MvPolynomial.pderiv_X_self]
  · rintro (hq | hs)
    · exact hvq (pnat_eq_of_int_coe_eq hq)
    · exact hvs (pnat_eq_of_int_coe_eq hs)

theorem pderiv_erase_bar_positive_index (q s : ℕ+) (k : ℤ) (hk : 0 < k)
    (hkq : k ≠ (q.val : ℤ)) (hks : k ≠ (s.val : ℤ)) :
    MvPolynomial.pderiv (⟨k.toNat, by omega⟩ : ℕ+)
      (eraseGenerator s (bar q k)) = 1 := by
  rw [erase_bar, if_neg (by tauto), complete_of_pos hk]
  exact MvPolynomial.pderiv_X_self _

/-- Exact coefficient for a repeated left gap and an erased second row. -/
theorem four_left_repeat_first_coefficient (q s : ℕ+) (a c d t : ℤ)
    (hsq : s ≠ q) (ha : (s.val : ℤ) < a) (hc : (s.val : ℤ) + t < c)
    (hd : (q.val : ℤ) + t < d) (hq : (s.val : ℤ) < q.val)
    (ht : 0 < t) (hts : t ≠ (s.val : ℤ)) :
    eraseGenerator s (MvPolynomial.pderiv s
      (fourInterval (bar q) a q.val c d s.val s.val t)) =
      eraseGenerator s (bar q (a + q.val - s.val)) *
        (-eraseGenerator s (bar q c) * eraseGenerator s (bar q d) +
          eraseGenerator s (bar q t) * eraseGenerator s (bar q (c + d - t))) +
      eraseGenerator s (bar q a) *
        (-eraseGenerator s (bar q (q.val + c - s.val)) * eraseGenerator s (bar q d) +
          eraseGenerator s (bar q t) *
            eraseGenerator s (bar q (q.val + c + d - s.val - t))) := by
  have hgen : bar q s.val = MvPolynomial.X s := by
    rw [bar, eraseGenerator_complete, if_neg]
    · exact complete_nat s
    · intro he; exact hsq (pnat_eq_of_int_coe_eq he)
  have hzero (k : ℤ) (hk : (s.val : ℤ) < k) :
      MvPolynomial.pderiv s (bar q k) = 0 :=
    pderiv_bar_eq_zero_of_ne q s k (ne_of_gt hk)
  have hA := hzero a ha
  have hC := hzero c (by omega)
  have hD := hzero d (by omega)
  have ht0 := pderiv_bar_eq_zero_of_ne q s t hts
  have hU := hzero (a + q.val - s.val) (by omega)
  have hV := hzero (q.val + c - s.val) (by omega)
  have hW := hzero (c + d - t) (by omega)
  have hX := hzero (a + q.val + c - s.val - s.val) (by omega)
  have hY := hzero (q.val + c + d - s.val - t) (by omega)
  have hT := hzero (a + q.val + c + d - s.val - s.val - t) (by omega)
  have hx : eraseGenerator s (MvPolynomial.X s) = 0 := by simp [eraseGenerator]
  simp only [fourInterval, bar_cut, hgen, zero_mul, mul_zero, sub_zero, add_zero,
    map_add, map_sub, MvPolynomial.pderiv_mul, hA, hC, hD, ht0, hU, hV, hW, hX, hY, hT,
    MvPolynomial.pderiv_X_self, zero_add, mul_one, one_mul, zero_sub,
    map_neg, map_mul, map_zero, map_one, hx]
  ring

/-- The largest of the two endpoint labels prevents cancellation in the
repeated-left-gap coefficient; their tie yields the numerical coefficient two. -/
theorem four_left_repeat_coefficient_ne_zero (q s : ℕ+) (a c d t : ℤ)
    (ha : (s.val : ℤ) < a) (haq : a ≠ (q.val : ℤ))
    (hc : (s.val : ℤ) + t < c) (hd : (q.val : ℤ) + t < d)
    (hq : (s.val : ℤ) < q.val) (ht : 0 < t)
    (hts : t ≠ (s.val : ℤ)) (htq : t ≠ (q.val : ℤ)) :
    eraseGenerator s (bar q (a + q.val - s.val)) *
        (-eraseGenerator s (bar q c) * eraseGenerator s (bar q d) +
          eraseGenerator s (bar q t) * eraseGenerator s (bar q (c + d - t))) +
      eraseGenerator s (bar q a) *
        (-eraseGenerator s (bar q (q.val + c - s.val)) * eraseGenerator s (bar q d) +
          eraseGenerator s (bar q t) *
            eraseGenerator s (bar q (q.val + c + d - s.val - t))) ≠ 0 := by
  classical
  let u : ℤ := a + q.val - s.val
  let v : ℤ := q.val + c - s.val
  let w : ℤ := c + d - t
  let y : ℤ := q.val + c + d - s.val - t
  let H : ℤ → CompleteRing := fun k => eraseGenerator s (bar q k)
  let F : CompleteRing := H u * (-H c * H d + H t * H w) +
    H a * (-H v * H d + H t * H y)
  change F ≠ 0
  have hineq :
      (q.val : ℤ) < u ∧ a < u ∧
      (q.val : ℤ) < y ∧ w < y ∧ v < y ∧ c < y ∧ d < y ∧ t < y ∧
      c < w ∧ d < w ∧ t < w := by dsimp [u, v, w, y]; omega
  have hneq (k : ℤ) (hkq : k ≠ (q.val : ℤ)) (hks : k ≠ (s.val : ℤ))
      (hk : 0 < k) : H k ≠ 0 := erase_bar_ne_zero hk hkq hks
  have hTnz : H t ≠ 0 := hneq t htq hts ht
  have hAnz : H a ≠ 0 := hneq a haq (ne_of_gt ha) (by have := s.pos; omega)
  have hderiv (V : ℕ+) (k : ℤ) (hk : k ≠ (V.val : ℤ)) :
      MvPolynomial.pderiv V (H k) = 0 := pderiv_erase_bar_eq_zero_of_ne q s V k hk
  have hself (k : ℤ) (hkq : (q.val : ℤ) < k) :
      let V : ℕ+ := ⟨k.toNat, by have := q.pos; omega⟩
      MvPolynomial.pderiv V (H k) = 1 := by
    exact pderiv_erase_bar_positive_index q s k (by have := q.pos; omega)
      (ne_of_gt hkq) (ne_of_gt (hq.trans hkq))
  rcases lt_trichotomy u y with huy | huy | huy
  · let Y : ℕ+ := ⟨y.toNat, by omega⟩
    have hY : (Y.val : ℤ) = y := by dsimp [Y]; omega
    have hsY : MvPolynomial.pderiv Y (H y) = 1 := hself y (by omega)
    have hdF : MvPolynomial.pderiv Y F = H a * H t := by
      dsimp [F]
      simp only [map_add, MvPolynomial.pderiv_mul,
        hderiv Y u (by omega), hderiv Y c (by omega), hderiv Y d (by omega),
        hderiv Y t (by omega), hderiv Y w (by omega), hderiv Y a (by omega),
        hderiv Y v (by omega), map_neg, hsY, zero_mul, mul_zero, zero_add, add_zero,
        zero_sub, sub_zero, mul_one, neg_zero]
    intro hz
    rw [hz, map_zero] at hdF
    exact mul_ne_zero hAnz hTnz hdF.symm
  · have haw : a = w := by dsimp [u, y, w] at *; omega
    let U : ℕ+ := ⟨u.toNat, by omega⟩
    have hU : (U.val : ℤ) = u := by dsimp [U]; omega
    have hsU : MvPolynomial.pderiv U (H u) = 1 := hself u (by omega)
    have hdF : MvPolynomial.pderiv U F = -H c * H d + 2 * H t * H w := by
      dsimp [F]
      rw [huy, haw]
      simp only [map_add, MvPolynomial.pderiv_mul,
        hderiv U c (by omega), hderiv U d (by omega), hderiv U t (by omega),
        hderiv U w (by omega), hderiv U v (by omega), map_neg,
        show MvPolynomial.pderiv U (H y) = 1 by simpa [huy] using hsU,
        zero_mul, mul_zero, zero_add, add_zero, zero_sub, sub_zero, mul_one,
        one_mul, neg_zero]
      ring
    let W : ℕ+ := ⟨w.toNat, by omega⟩
    have hW : (W.val : ℤ) = w := by dsimp [W]; omega
    have hsW : MvPolynomial.pderiv W (H w) = 1 := hself w (by dsimp [w]; omega)
    have hd2 : MvPolynomial.pderiv W (MvPolynomial.pderiv U F) = 2 * H t := by
      rw [hdF]
      simp [MvPolynomial.pderiv_mul, hderiv W c (by omega), hderiv W d (by omega),
        hderiv W t (by omega), hsW]
    intro hz
    rw [hz, map_zero, map_zero] at hd2
    exact mul_ne_zero (by norm_num : (2 : CompleteRing) ≠ 0) hTnz hd2.symm
  · let U : ℕ+ := ⟨u.toNat, by omega⟩
    have hU : (U.val : ℤ) = u := by dsimp [U]; omega
    have hsU : MvPolynomial.pderiv U (H u) = 1 := hself u (by omega)
    have hdF : MvPolynomial.pderiv U F = -H c * H d + H t * H w := by
      dsimp [F]
      simp only [map_add, MvPolynomial.pderiv_mul,
        hderiv U c (by omega), hderiv U d (by omega), hderiv U t (by omega),
        hderiv U w (by omega), hderiv U a (by omega), hderiv U v (by omega),
        hderiv U y (by omega), map_neg, hsU, zero_mul, mul_zero, zero_add,
        add_zero, zero_sub, sub_zero, mul_one, one_mul, neg_zero]
    have hn := erased_two_factor_ne_zero_of_full_survives q s c d t
      ht (by omega) (by omega) htq hts (by dsimp [w]; omega) (by dsimp [w]; omega)
    have hn' : -H c * H d + H t * H w ≠ 0 := by
      have he : -H c * H d + H t * H w =
          -eraseGenerator s (bar q c * bar q d - bar q t * bar q (c + d - t)) := by
        dsimp [H, w]
        simp only [map_sub, map_mul]
        ring
      rw [he]
      exact neg_ne_zero.mpr hn
    intro hz
    rw [hz, map_zero] at hdF
    exact hn' hdF.symm

theorem four_middle_square_not_dvd_left_repeat {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hrs : P.g 0 = P.g 1) (hst : P.g 1 ≠ P.g 2) (hb : P.r 1 = q.val) :
    let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
    ¬ (MvPolynomial.X S : CompleteRing) ^ 2 ∣ restriction q P := by
  classical
  dsimp only
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  have hsq : S ≠ q := by
    intro he
    exact hP.gap_ne 1 (congrArg Subtype.val he)
  have hrow := P.g_lt_castSucc 0
  change P.g 0 < P.r 0 at hrow
  have ht1 := hP.thick 0 1 (by decide)
  have ht2 := hP.thick 1 2 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at ht1
  change P.g 1 + P.g 2 < P.r 2 at ht2
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hcoeff := four_left_repeat_first_coefficient q S
    (P.r 0) (P.r 2) (P.r 3) (P.g 2) hsq
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by omega)
    (by dsimp [S]; omega) (by exact_mod_cast hP.gap_pos 2)
    (by dsimp [S]; exact_mod_cast Ne.symm hst)
  apply not_X_square_dvd_of_first_coefficient S
  rw [restriction_four_expansion q P hP.thick]
  simp only [hrs, hb]
  change eraseGenerator S (MvPolynomial.pderiv S
    (fourInterval (bar q) (P.r 0) q.val (P.r 2) (P.r 3) S.val S.val (P.g 2))) ≠ 0
  rw [hcoeff]
  exact four_left_repeat_coefficient_ne_zero q S _ _ _ _
    (by dsimp [S]; omega) (by exact_mod_cast ha) (by dsimp [S]; omega) (by omega)
    (by dsimp [S]; omega) (by exact_mod_cast hP.gap_pos 2)
    (by dsimp [S]; exact_mod_cast Ne.symm hst) (by exact_mod_cast hP.gap_ne 2)

/-- Exact right-repeat coefficient; the first row is allowed to equal the
middle gap, so its derivative is not assumed zero. -/
theorem four_right_repeat_first_coefficient (q s : ℕ+) (a b d r : ℤ)
    (hsq : s ≠ q) (hr : 0 < r) (hra : r < a)
    (hb : r + s.val < b) (hd : (q.val : ℤ) + s.val < d)
    (hq : (s.val : ℤ) < q.val) (hrs : r ≠ (s.val : ℤ)) :
    eraseGenerator s (MvPolynomial.pderiv s
      (fourInterval (bar q) a b q.val d r s.val s.val)) =
      eraseGenerator s (bar q d) *
        (-eraseGenerator s (bar q a) * eraseGenerator s (bar q (b + q.val - s.val)) +
          eraseGenerator s (bar q r) *
            eraseGenerator s (bar q (a + b + q.val - r - s.val))) +
      eraseGenerator s (bar q (q.val + d - s.val)) *
        (-eraseGenerator s (bar q a) * eraseGenerator s (bar q b) +
          eraseGenerator s (bar q r) * eraseGenerator s (bar q (a + b - r))) := by
  have hgen : bar q s.val = MvPolynomial.X s := by
    rw [bar, eraseGenerator_complete, if_neg]
    · exact complete_nat s
    · intro he; exact hsq (pnat_eq_of_int_coe_eq he)
  have hzero (k : ℤ) (hk : (s.val : ℤ) < k) :
      MvPolynomial.pderiv s (bar q k) = 0 :=
    pderiv_bar_eq_zero_of_ne q s k (ne_of_gt hk)
  have hB := hzero b (by omega)
  have hD := hzero d (by omega)
  have hr0 := pderiv_bar_eq_zero_of_ne q s r hrs
  have hU := hzero (a + b - r) (by omega)
  have hV := hzero (b + q.val - s.val) (by omega)
  have hW := hzero (q.val + d - s.val) (by omega)
  have hX := hzero (a + b + q.val - r - s.val) (by omega)
  have hY := hzero (b + q.val + d - s.val - s.val) (by omega)
  have hT := hzero (a + b + q.val + d - r - s.val - s.val) (by omega)
  have hx : eraseGenerator s (MvPolynomial.X s) = 0 := by simp [eraseGenerator]
  simp only [fourInterval, bar_cut, hgen, zero_mul, mul_zero, sub_zero, add_zero,
    map_add, map_sub, MvPolynomial.pderiv_mul, hB, hD, hr0, hU, hV, hW, hX, hY, hT,
    MvPolynomial.pderiv_X_self, zero_add, mul_one, one_mul, zero_sub,
    map_neg, map_mul, map_zero, map_one, hx]
  ring

/-- The actual first coefficient used by the repeated right-gap calculation. -/
noncomputable def rightRepeatFirstCoefficient (q s : ℕ+) (a b d r : ℤ) : CompleteRing :=
  eraseGenerator s (bar q d) *
      (-eraseGenerator s (bar q a) * eraseGenerator s (bar q (b + q.val - s.val)) +
        eraseGenerator s (bar q r) *
          eraseGenerator s (bar q (a + b + q.val - r - s.val))) +
    eraseGenerator s (bar q (q.val + d - s.val)) *
      (-eraseGenerator s (bar q a) * eraseGenerator s (bar q b) +
        eraseGenerator s (bar q r) * eraseGenerator s (bar q (a + b - r)))

/-- A strict prefix maximum has the nonzero actual gap-times-last-row coefficient. -/
theorem right_repeat_prefix_larger_ne_zero (q s : ℕ+) (a b d r : ℤ)
    (hr : 0 < r) (hra : r < a) (hb : r + s.val < b)
    (hd : (q.val : ℤ) + s.val < d) (hq : (s.val : ℤ) < q.val)
    (hrs : r ≠ (s.val : ℤ)) (hrq : r ≠ (q.val : ℤ))
    (hxw : (q.val : ℤ) + d - s.val < a + b + q.val - r - s.val) :
    rightRepeatFirstCoefficient q s a b d r ≠ 0 := by
  classical
  let u : ℤ := a + b - r
  let v : ℤ := b + q.val - s.val
  let w : ℤ := q.val + d - s.val
  let x : ℤ := a + b + q.val - r - s.val
  let H : ℤ → CompleteRing := fun k => eraseGenerator s (bar q k)
  let F : CompleteRing := H d * (-H a * H v + H r * H x) +
    H w * (-H a * H b + H r * H u)
  change F ≠ 0
  have hineq : a < x ∧ b < x ∧ r < x ∧ u < x ∧ v < x ∧ d < x ∧ w < x ∧
      (q.val : ℤ) < x := by dsimp [u, v, w, x]; omega
  let X : ℕ+ := ⟨x.toNat, by have := q.pos; omega⟩
  have hX : (X.val : ℤ) = x := by
    change ((x.toNat : ℕ) : ℤ) = x
    exact Int.toNat_of_nonneg (by omega)
  have hsX : MvPolynomial.pderiv X (H x) = 1 :=
    pderiv_erase_bar_positive_index q s x (by have := q.pos; omega)
      (by omega) (by omega)
  have hderiv (k : ℤ) (hk : k < x) : MvPolynomial.pderiv X (H k) = 0 :=
    pderiv_erase_bar_eq_zero_of_ne q s X k (by rw [hX]; exact ne_of_lt hk)
  have hdF : MvPolynomial.pderiv X F = H d * H r := by
    dsimp [F]
    simp only [map_add, MvPolynomial.pderiv_mul, hderiv d (by omega),
      hderiv a (by omega), hderiv v (by omega), hderiv r (by omega),
      hderiv w (by omega), hderiv b (by omega), hderiv u (by omega),
      hsX, map_neg, zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one, neg_zero]
  have hRnz : H r ≠ 0 := erase_bar_ne_zero hr hrq hrs
  have hDnz : H d ≠ 0 :=
    erase_bar_ne_zero (by have := q.pos; omega) (by omega) (by omega)
  intro hz
  have hzero : MvPolynomial.pderiv X F = 0 := by rw [hz, map_zero]
  exact mul_ne_zero hDnz hRnz (hdF.symm.trans hzero)

/-- At a prefix/suffix tie the second derivative is twice the nonzero gap generator. -/
theorem right_repeat_prefix_tie_ne_zero (q s : ℕ+) (a b d r : ℤ)
    (hr : 0 < r) (hra : r < a) (hb : r + s.val < b)
    (hd : (q.val : ℤ) + s.val < d) (hq : (s.val : ℤ) < q.val)
    (hrs : r ≠ (s.val : ℤ)) (hrq : r ≠ (q.val : ℤ))
    (hxw : a + b + q.val - r - s.val = (q.val : ℤ) + d - s.val) :
    rightRepeatFirstCoefficient q s a b d r ≠ 0 := by
  classical
  let u : ℤ := a + b - r
  let v : ℤ := b + q.val - s.val
  let w : ℤ := q.val + d - s.val
  let x : ℤ := a + b + q.val - r - s.val
  let H : ℤ → CompleteRing := fun k => eraseGenerator s (bar q k)
  let F : CompleteRing := H d * (-H a * H v + H r * H x) +
    H w * (-H a * H b + H r * H u)
  change F ≠ 0
  have hud : u = d := by dsimp [u]; omega
  have hineq : a < u ∧ b < u ∧ r < u ∧ u < x ∧ v < x ∧
      (q.val : ℤ) < u ∧ (q.val : ℤ) < x := by dsimp [u, v, x]; omega
  let X : ℕ+ := ⟨x.toNat, by have := q.pos; omega⟩
  let U : ℕ+ := ⟨u.toNat, by have := q.pos; omega⟩
  have hX : (X.val : ℤ) = x := Int.toNat_of_nonneg (by omega)
  have hU : (U.val : ℤ) = u := Int.toNat_of_nonneg (by omega)
  have hsX : MvPolynomial.pderiv X (H x) = 1 :=
    pderiv_erase_bar_positive_index q s x (by have := q.pos; omega) (by omega) (by omega)
  have hsU : MvPolynomial.pderiv U (H u) = 1 :=
    pderiv_erase_bar_positive_index q s u (by have := q.pos; omega) (by omega) (by omega)
  have hderivX (k : ℤ) (hk : k < x) : MvPolynomial.pderiv X (H k) = 0 :=
    pderiv_erase_bar_eq_zero_of_ne q s X k (by rw [hX]; exact ne_of_lt hk)
  have hderivU (k : ℤ) (hk : k < u) : MvPolynomial.pderiv U (H k) = 0 :=
    pderiv_erase_bar_eq_zero_of_ne q s U k (by rw [hU]; exact ne_of_lt hk)
  have hdF : MvPolynomial.pderiv X F = 2 * H r * H u - H a * H b := by
    dsimp [F]
    have hwx : w = x := hxw.symm
    rw [hwx, ← hud]
    simp only [map_add, MvPolynomial.pderiv_mul, hderivX u (by omega),
      hderivX a (by omega), hderivX v (by omega), hderivX r (by omega),
      hderivX b (by omega), hsX, map_neg, zero_mul, mul_zero, zero_add,
      add_zero, one_mul, mul_one, neg_zero]
    ring
  have hd2 : MvPolynomial.pderiv U (MvPolynomial.pderiv X F) = 2 * H r := by
    rw [hdF]
    simp only [map_sub, MvPolynomial.pderiv_mul, pderiv_two, hderivU r (by omega),
      hderivU a (by omega), hderivU b (by omega), hsU, zero_mul, mul_zero,
      zero_add, add_zero, mul_one, sub_zero]
  exact ne_zero_of_iterated_pderiv_eq U X F (2 * H r) hd2
    (mul_ne_zero (by norm_num : (2 : CompleteRing) ≠ 0) (erase_bar_ne_zero hr hrq hrs))

theorem four_right_repeat_coefficient_ne_zero (q s : ℕ+) (a b d r : ℤ)
    (hr : 0 < r) (hra : r < a) (haq : a ≠ (q.val : ℤ))
    (hb : r + s.val < b) (hd : (q.val : ℤ) + s.val < d)
    (hq : (s.val : ℤ) < q.val) (hrs : r ≠ (s.val : ℤ)) (hrq : r ≠ (q.val : ℤ)) :
    eraseGenerator s (bar q d) *
        (-eraseGenerator s (bar q a) * eraseGenerator s (bar q (b + q.val - s.val)) +
          eraseGenerator s (bar q r) *
            eraseGenerator s (bar q (a + b + q.val - r - s.val))) +
      eraseGenerator s (bar q (q.val + d - s.val)) *
        (-eraseGenerator s (bar q a) * eraseGenerator s (bar q b) +
          eraseGenerator s (bar q r) * eraseGenerator s (bar q (a + b - r))) ≠ 0 := by
  classical
  let u : ℤ := a + b - r
  let v : ℤ := b + q.val - s.val
  let w : ℤ := q.val + d - s.val
  let x : ℤ := a + b + q.val - r - s.val
  let H : ℤ → CompleteRing := fun k => eraseGenerator s (bar q k)
  let F : CompleteRing := H d * (-H a * H v + H r * H x) +
    H w * (-H a * H b + H r * H u)
  change F ≠ 0
  have hineq :
      (s.val : ℤ) < u ∧ a < u ∧ b < u ∧ r < u ∧
      (q.val : ℤ) < x ∧ a < x ∧ b < x ∧ r < x ∧ u < x ∧ v < x ∧
      (q.val : ℤ) < w ∧ d < w := by dsimp [u, v, w, x]; omega
  have hRnz : H r ≠ 0 := erase_bar_ne_zero hr hrq hrs
  have hDnz : H d ≠ 0 := erase_bar_ne_zero (by have := q.pos; omega) (by omega) (by omega)
  have hderiv (V : ℕ+) (k : ℤ) (hk : k ≠ (V.val : ℤ)) :
      MvPolynomial.pderiv V (H k) = 0 := pderiv_erase_bar_eq_zero_of_ne q s V k hk
  have hself (k : ℤ) (hkq : (q.val : ℤ) < k) :
      let V : ℕ+ := ⟨k.toNat, by have := q.pos; omega⟩
      MvPolynomial.pderiv V (H k) = 1 := by
    exact pderiv_erase_bar_positive_index q s k (by have := q.pos; omega)
      (ne_of_gt hkq) (ne_of_gt (hq.trans hkq))
  by_cases has : a = (s.val : ℤ)
  · have hAz : H a = 0 := by dsimp [H]; simp [erase_bar, has]
    let E : CompleteRing →+* ℚ := MvPolynomial.eval (fun _ : ℕ+ => (1 : ℚ))
    have hev (k : ℤ) (hk : 0 < k) (hks : k ≠ (s.val : ℤ)) :
        E (H k) = if k = (q.val : ℤ) then 0 else 1 := by
      by_cases hkq : k = (q.val : ℤ)
      · simp [H, erase_bar, hkq]
      · dsimp [H]
        rw [erase_bar, if_neg (by tauto), complete_of_pos hk]
        simp only [E, MvPolynomial.eval_X, if_neg hkq]
    intro hz
    have he := congrArg E hz
    dsimp [F] at he
    simp only [hAz, zero_mul, neg_zero, zero_add, map_add, map_mul, map_zero] at he
    rw [hev d (by omega) (by omega), hev r hr hrs,
      hev x (by omega) (by omega), hev w (by omega) (by omega),
      hev u (by omega) (by omega)] at he
    simp only [if_neg (ne_of_gt (show (q.val : ℤ) < d by omega)), if_neg hrq,
      if_neg (ne_of_gt (show (q.val : ℤ) < x by omega)),
      if_neg (ne_of_gt (show (q.val : ℤ) < w by omega)), one_mul, mul_one] at he
    split_ifs at he <;> norm_num at he
  · rcases lt_trichotomy x w with hxw | hxw | hxw
    · let W : ℕ+ := ⟨w.toNat, by omega⟩
      have hW : (W.val : ℤ) = w := by dsimp [W]; omega
      have hsW : MvPolynomial.pderiv W (H w) = 1 := hself w (by omega)
      have hdF : MvPolynomial.pderiv W F = -H a * H b + H r * H u := by
        dsimp [F]
        simp only [map_add, MvPolynomial.pderiv_mul, hderiv W d (by omega),
          hderiv W a (by omega), hderiv W v (by omega), hderiv W r (by omega),
          hderiv W x (by omega), hderiv W b (by omega), hderiv W u (by omega),
          hsW, map_neg, zero_mul, mul_zero, zero_add, add_zero, zero_sub,
          sub_zero, one_mul, mul_one, neg_zero]
      have hn := erased_two_factor_eq_zero_iff q s a b r hr hra (by omega) (by omega) haq hrq
      have hn' : -H a * H b + H r * H u ≠ 0 := by
        have hbin : eraseGenerator s (bar q a * bar q b - bar q r * bar q u) ≠ 0 := by
          intro hz
          rcases hn.mp hz with hc | hc
          · exact hrs hc.2
          · exact has hc.1
        have he : -H a * H b + H r * H u =
            -eraseGenerator s (bar q a * bar q b - bar q r * bar q u) := by
          dsimp [H]
          simp only [map_sub, map_mul]
          ring
        rw [he]
        exact neg_ne_zero.mpr hbin
      intro hz
      rw [hz, map_zero] at hdF
      exact hn' hdF.symm
    · exact right_repeat_prefix_tie_ne_zero q s a b d r hr hra hb hd hq hrs hrq hxw
    · exact right_repeat_prefix_larger_ne_zero q s a b d r hr hra hb hd hq hrs hrq hxw

theorem four_middle_square_not_dvd_right_repeat {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hrs : P.g 0 ≠ P.g 1) (hst : P.g 1 = P.g 2) (hc : P.r 2 = q.val) :
    let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
    ¬ (MvPolynomial.X S : CompleteRing) ^ 2 ∣ restriction q P := by
  classical
  dsimp only
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  have hsq : S ≠ q := by
    intro he
    exact hP.gap_ne 1 (congrArg Subtype.val he)
  have hrow := P.g_lt_castSucc 0
  change P.g 0 < P.r 0 at hrow
  have ht1 := hP.thick 0 1 (by decide)
  have ht2 := hP.thick 1 2 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at ht1
  change P.g 1 + P.g 2 < P.r 2 at ht2
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hcoeff := four_right_repeat_first_coefficient q S
    (P.r 0) (P.r 1) (P.r 3) (P.g 0) hsq
    (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hrow)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
    (by dsimp [S]; exact_mod_cast hrs)
  apply not_X_square_dvd_of_first_coefficient S
  rw [restriction_four_expansion q P hP.thick]
  simp only [hc, ← hst]
  change eraseGenerator S (MvPolynomial.pderiv S
    (fourInterval (bar q) (P.r 0) (P.r 1) q.val (P.r 3) (P.g 0) S.val S.val)) ≠ 0
  rw [hcoeff]
  exact four_right_repeat_coefficient_ne_zero q S _ _ _ _
    (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hrow) (by exact_mod_cast ha)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
    (by dsimp [S]; exact_mod_cast hrs) (by exact_mod_cast hP.gap_ne 0)

/-- The merged-interval contact has a positive first coefficient, even when
the first row and the last gap share the middle gap's label. -/
theorem four_merge_repeat_first_coefficient (q s : ℕ+) (b c d r : ℤ)
    (hsq : s ≠ q) (hu : (s.val : ℤ) + b - r = q.val) :
    eraseGenerator s (MvPolynomial.pderiv s
      (fourInterval (bar q) s.val b c d r s.val s.val)) =
      eraseGenerator s (bar q d) *
        (eraseGenerator s (bar q b) * eraseGenerator s (bar q c) +
          eraseGenerator s (bar q r) *
            eraseGenerator s (bar q (s.val + b + c - r - s.val))) := by
  have hgen : bar q s.val = MvPolynomial.X s := by
    rw [bar, eraseGenerator_complete, if_neg]
    · exact complete_nat s
    · intro he; exact hsq (pnat_eq_of_int_coe_eq he)
  have hU : bar q (s.val + b - r) = 0 := by simp [hu]
  have hx : eraseGenerator s (MvPolynomial.X s) = 0 := by simp [eraseGenerator]
  simp only [fourInterval, hU, hgen, zero_mul, mul_zero, sub_zero, add_zero,
    map_add, map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
    zero_add, mul_one, one_mul, zero_sub, map_neg, map_mul, map_zero, map_one, hx]
  ring

theorem four_middle_square_not_dvd_merge_repeat {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hst : P.g 1 = P.g 2)
    (has : P.r 0 = P.g 1)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) :
    let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
    ¬ (MvPolynomial.X S : CompleteRing) ^ 2 ∣ restriction q P := by
  classical
  dsimp only
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  have hsq : S ≠ q := by
    intro he
    exact hP.gap_ne 1 (congrArg Subtype.val he)
  have hrow := P.g_lt_castSucc 0
  change P.g 0 < P.r 0 at hrow
  have ht1 := hP.thick 0 1 (by decide)
  have ht2 := hP.thick 1 2 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at ht1
  change P.g 1 + P.g 2 < P.r 2 at ht2
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hcoeff := four_merge_repeat_first_coefficient q S
    (P.r 1) (P.r 2) (P.r 3) (P.g 0) hsq (by dsimp [S]; omega)
  apply not_X_square_dvd_of_first_coefficient S
  rw [restriction_four_expansion q P hP.thick]
  simp only [has, ← hst]
  change eraseGenerator S (MvPolynomial.pderiv S
    (fourInterval (bar q) S.val (P.r 1) (P.r 2) (P.r 3) (P.g 0) S.val S.val)) ≠ 0
  rw [hcoeff]
  let E : CompleteRing →+* ℚ := MvPolynomial.eval (fun _ : ℕ+ => (1 : ℚ))
  have hev (k : ℤ) (hk : 0 < k) (hks : k ≠ (S.val : ℤ)) :
      E (eraseGenerator S (bar q k)) = if k = (q.val : ℤ) then 0 else 1 := by
    by_cases hkq : k = (q.val : ℤ)
    · simp [erase_bar, hkq]
    · rw [erase_bar, if_neg (by tauto), complete_of_pos hk]
      simp only [E, MvPolynomial.eval_X, if_neg hkq]
  intro hz
  have he := congrArg E hz
  simp only [map_mul, map_add, map_zero] at he
  rw [hev (P.r 3) (by have := P.r_pos 3; positivity) (by dsimp [S]; omega),
    hev (P.r 1) (by have := P.r_pos 1; positivity) (by dsimp [S]; omega),
    hev (P.r 2) (by have := P.r_pos 2; positivity) (by dsimp [S]; omega),
    hev (P.g 0) (by exact_mod_cast hP.gap_pos 0) (by dsimp [S]; omega),
    hev ((S.val : ℤ) + P.r 1 + P.r 2 - P.g 0 - S.val)
      (by dsimp [S]; omega) (by dsimp [S]; omega)] at he
  have hdq : (P.r 3 : ℤ) ≠ q.val := by omega
  have hbq : (P.r 1 : ℤ) ≠ q.val := by omega
  have hrq : (P.g 0 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 0
  have hxq : (S.val : ℤ) + P.r 1 + P.r 2 - P.g 0 - S.val ≠ q.val := by
    dsimp [S]
    omega
  simp only [if_neg hdq, if_neg hbq, if_neg hrq, if_neg hxq, one_mul, mul_one] at he
  split_ifs at he <;> norm_num at he

/-- Repeated contact alternatives never increase the middle-gap exponent.
This covers all three repeated-label patterns, including their intersections. -/
theorem four_middle_square_not_dvd {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) :
    let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
    ¬ (MvPolynomial.X S : CompleteRing) ^ 2 ∣ restriction q P := by
  classical
  dsimp only
  let S : ℕ+ := ⟨P.g 1, hP.gap_pos 1⟩
  by_cases hcontact :
      (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
      (P.r 2 = q.val ∧ P.g 1 = P.g 2) ∨
      (((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ∧ P.r 0 = P.g 1)
  · rcases hcontact with ⟨hb, hrs⟩ | ⟨hc, hst⟩ | ⟨hu, has⟩
    · by_cases hst : P.g 1 = P.g 2
      · exact four_middle_square_not_dvd_equal_gaps hP ha hrs hst (Or.inl hb)
      · exact four_middle_square_not_dvd_left_repeat hP ha hrs hst hb
    · by_cases hrs : P.g 0 = P.g 1
      · exact four_middle_square_not_dvd_equal_gaps hP ha hrs hst (Or.inr hc)
      · exact four_middle_square_not_dvd_right_repeat hP ha hrs hst hc
    · have hrs : P.g 0 ≠ P.g 1 := by
        have hrow := P.g_lt_castSucc 0
        change P.g 0 < P.r 0 at hrow
        omega
      by_cases hst : P.g 1 = P.g 2
      · exact four_middle_square_not_dvd_merge_repeat hP hst has hu
      · exact four_middle_square_not_dvd_of_unique_gap hP hrs hst
  · have hn : ¬ MvPolynomial.X S ∣ restriction q P :=
      fun hd => hcontact ((four_middle_gap_dvd_iff hP ha).mp hd)
    intro hd
    exact hn (dvd_trans (show (MvPolynomial.X S : CompleteRing) ∣
      (MvPolynomial.X S : CompleteRing) ^ 2 from
        ⟨MvPolynomial.X S, by ring⟩) hd)

/-- The complete unbounded four-row content table.  Coincident gap values
and simultaneous contact conditions are not excluded. -/
theorem four_content {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    monicContent hP =
      if P.r 0 = q.val then
        if P.r 2 = q.val ∧ P.g 1 = P.g 2
        then complete (P.g 0) * complete (P.g 1) else complete (P.g 0)
      else
        if (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
            (P.r 2 = q.val ∧ P.g 1 = P.g 2) ∨
            (((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ∧ P.r 0 = P.g 1)
        then complete (P.g 1) else 1 := by
  classical
  by_cases ha : P.r 0 = q.val
  · simpa only [if_pos ha] using four_content_first_row hP ha
  · simpa only [if_neg ha] using
      four_content_of_middle_square_not_dvd hP ha (four_middle_square_not_dvd hP ha)

/-- Actual polydeterminant factorization, irreducibility, coefficient-one
content, and the strict low-gap bound, assembled without certificate fields. -/
theorem staircase_content {n : ℕ} {q : ℕ+} {P : Profile n} (hP : QComponent q P) :
    restriction q P = monicContent hP * monicPrimitive hP ∧
      Irreducible (monicPrimitive hP) ∧
      monicContent hP = MvPolynomial.monomial (contentExponent hP) 1 ∧
      (∀ v ∈ (contentExponent hP).support, v.val < q.val) :=
  ⟨restriction_eq_monicContent_mul hP, monicPrimitive_irreducible hP, rfl,
    fun v hv => contentExponent_support_lt_cut hP v hv⟩

/-- Actual coordinates after contracting the first seam of a four-row profile. -/
theorem four_endpoint_contract_coordinates (P : Profile 3) :
    let C := GeneralHessenberg.contract P 0
    ((C.r 0 : ℤ) = (P.r 0 : ℤ) + P.r 1 - P.g 0) ∧
      C.r 1 = P.r 2 ∧ C.r 2 = P.r 3 ∧ C.g 0 = P.g 1 ∧ C.g 1 = P.g 2 := by
  dsimp only
  have hb := GeneralHessenberg.contract_beta P 0
  refine ⟨GeneralHessenberg.contract_joined_row P 0, ?_, ?_, ?_, ?_⟩
  · apply Int.ofNat_injective
    change ((GeneralHessenberg.contract P 0).r 1 : ℤ) = (P.r 2 : ℤ)
    rw [← (GeneralHessenberg.contract P 0).xi_sub_zeta 1, hb.1, hb.2]
    simpa [Fin.succAbove] using P.xi_sub_zeta (2 : Fin 4)
  · apply Int.ofNat_injective
    change ((GeneralHessenberg.contract P 0).r 2 : ℤ) = (P.r 3 : ℤ)
    rw [← (GeneralHessenberg.contract P 0).xi_sub_zeta 2, hb.1, hb.2]
    simpa [Fin.succAbove] using P.xi_sub_zeta (3 : Fin 4)
  · simpa [Fin.succAbove] using GeneralHessenberg.contract_gap P 0 (0 : Fin 2)
  · simpa [Fin.succAbove] using GeneralHessenberg.contract_gap P 0 (1 : Fin 2)

/-- Endpoint contraction preserves the actual q-component arithmetic domain. -/
theorem four_endpoint_contract_component {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (_ha : P.r 0 = q.val) :
    QComponent q (GeneralHessenberg.contract P 0) := by
  obtain ⟨hr0, hr1, hr2, hg0, hg1⟩ := four_endpoint_contract_coordinates P
  refine ⟨GeneralHessenberg.contract_thick hP.thick 0, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · change 0 < (GeneralHessenberg.contract P 0).g 0
      rw [hg0]
      exact hP.gap_pos 1
    · change 0 < (GeneralHessenberg.contract P 0).g 1
      rw [hg1]
      exact hP.gap_pos 2
  · intro j
    fin_cases j
    · change (GeneralHessenberg.contract P 0).g 0 ≠ q.val
      rw [hg0]
      exact hP.gap_ne 1
    · change (GeneralHessenberg.contract P 0).g 1 ≠ q.val
      rw [hg1]
      exact hP.gap_ne 2
  · simpa [lastGap, Fin.sum_univ_succ, hg0, hg1, hr2] using hP.bottom

/-- Contraction extracts exactly the endpoint gap's content contribution. -/
theorem four_endpoint_contract_content {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 = q.val) :
    monicContent hP = complete (P.g 0) *
      monicContent (four_endpoint_contract_component hP ha) := by
  let C := GeneralHessenberg.contract P 0
  have hC := four_endpoint_contract_component hP ha
  obtain ⟨hr0, hr1, hr2, hg0, hg1⟩ := four_endpoint_contract_coordinates P
  have hrow0 : (C.r 0 : ℤ) = (P.r 0 : ℤ) + P.r 1 - P.g 0 := hr0
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hnew : (q.val : ℤ) < C.r 0 := by change (q.val : ℤ) < _; omega
  have hCt := three_content_first_above_cut (hC : QComponent q C) hnew
  rw [four_content_first_row hP ha, hCt]
  simp only [hr1, hg0, hg1, mul_ite, mul_one]
  split_ifs with hc
  · rw [hc.2]
  · rfl

end SkewJacobiNegative.Staircase
