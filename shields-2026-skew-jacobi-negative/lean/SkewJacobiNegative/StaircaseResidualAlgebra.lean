/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseContent
import SkewJacobiNegative.FourRowHessenberg

/-!
# Endpoint readings and normalized staircase residuals

Exact collected endpoint coefficients and the actual monic normalization used in
`lem:staircase-endpoint-coefficients`, `lem:staircase-small-residuals`, and
`eq:staircase-residual-family` of `shields-2026-skew-jacobi-negative.tex`.
Generator collisions are retained in every polynomial identity.
-/

namespace SkewJacobiNegative.Staircase

open Gluing HessenbergExpansion

/-- The binomial quadratic, with a positive largest-generator coefficient. -/
noncomputable def quadraticB (r a c : ℤ) : CompleteRing :=
  complete r * complete (a + c - r) - complete a * complete c

/-- The middle-contact quadratic.  Repeated negative monomials are not discarded. -/
noncomputable def quadraticM (q r a c : ℤ) : CompleteRing :=
  complete r * complete (a + c + q - 2 * r) -
    complete (a + q - r) * complete c - complete a * complete (c + q - r)

/-- The interval-contact quadratic. -/
noncomputable def quadraticI (q r s c : ℤ) : CompleteRing :=
  complete (q - s + r) * complete c -
    complete s * complete (q + c - 2 * s + r) +
    complete r * complete (q + c - s)

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/DenseFourRemainder.lean
/-- Differentiation reads the actual signed-index generator convention. -/
theorem residual_pderiv_complete (v : ℕ+) (k : ℤ) :
    MvPolynomial.pderiv v (complete k) = if k = (v.val : ℤ) then 1 else 0 := by
  by_cases hk : k = (v.val : ℤ)
  · rw [hk, if_pos rfl, complete_nat, MvPolynomial.pderiv_X_self]
  · rw [if_neg hk]
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    rw [mem_vars_complete_iff]
    exact Ne.symm hk

/-- Erasure does not change differentiation at a different generator. -/
theorem residual_pderiv_bar (q v : ℕ+) (hvq : v ≠ q) (k : ℤ) :
    MvPolynomial.pderiv v (bar q k) = if k = (v.val : ℤ) then 1 else 0 := by
  rw [bar, eraseGenerator_complete]
  by_cases hk : k = (q.val : ℤ)
  · rw [if_pos hk, map_zero, if_neg]
    intro he
    apply hvq
    apply PNat.coe_injective
    exact_mod_cast he.symm.trans hk
  · rw [if_neg hk]
    exact residual_pderiv_complete v k

/-- Four-row prefix, suffix, and full-interval indices. -/
def prefixIndex (P : Profile 3) : ℤ :=
  (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1

def suffixIndex (P : Profile 3) : ℤ :=
  (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2

def secondIndex (P : Profile 3) : ℤ := max (prefixIndex P) (suffixIndex P)

/-- The private full interval expressed in row/gap coordinates. -/
theorem fullIndex_four (P : Profile 3) :
    fullIndex P = (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 -
      P.g 0 - P.g 1 - P.g 2 := by
  simp [fullIndex, BetaDiagram.largestLabel, Profile.toBetaDiagram,
    Profile.xi, Profile.zeta, Fin.sum_univ_succ]
  <;> ring

/-- Thickness puts every shorter interval below both three-row maxima. -/
theorem four_endpoint_index_bounds {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) :
    (q.val : ℤ) < secondIndex P ∧ secondIndex P < fullIndex P ∧
    (∀ i : Fin 4, (P.r i : ℤ) < secondIndex P) ∧
    (∀ j : Fin 3, (P.g j : ℤ) < secondIndex P) ∧
    (P.r 0 : ℤ) + P.r 1 - P.g 0 < secondIndex P ∧
    (P.r 1 : ℤ) + P.r 2 - P.g 1 < secondIndex P ∧
    (P.r 2 : ℤ) + P.r 3 - P.g 2 < secondIndex P := by
  have hd := P.four_domain hP.thick.hessenberg
  have hb : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  rcases hd with ⟨hr, hs, ht, ha, hb', hc, hd⟩
  have hbZ : (q.val : ℤ) + P.g 2 < P.r 3 := by exact_mod_cast hb
  have hmaxX : prefixIndex P ≤ secondIndex P := le_max_left _ _
  have hmaxY : suffixIndex P ≤ secondIndex P := le_max_right _ _
  rw [fullIndex_four]
  dsimp [prefixIndex, suffixIndex] at hmaxX hmaxY
  refine ⟨by omega, ?_, ?_, ?_, by omega, by omega, by omega⟩
  · dsimp [secondIndex, prefixIndex, suffixIndex]
    exact max_lt (by omega) (by omega)
  · intro i; fin_cases i <;> norm_num <;> omega
  · intro j; fin_cases j <;> norm_num <;> omega

/-- Positive label of the larger prefix/suffix interval. -/
def secondGenerator {q : ℕ+} {P : Profile 3} (hP : QComponent q P) : ℕ+ :=
  ⟨(secondIndex P).toNat, by
    have := (four_endpoint_index_bounds hP).1
    have := q.pos
    omega⟩

theorem secondGenerator_val {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    ((secondGenerator hP).val : ℤ) = secondIndex P := by
  have := (four_endpoint_index_bounds hP).1
  have := q.pos
  dsimp [secondGenerator]
  omega

/-- Both tied endpoint contributions survive, including coincident monomials. -/
theorem four_second_coefficient {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) :
    MvPolynomial.pderiv (secondGenerator hP) (restriction q P) =
      (if prefixIndex P = secondIndex P then
        bar q (P.g 0) * bar q (P.g 1) * bar q (P.r 3) else 0) +
      (if suffixIndex P = secondIndex P then
        bar q (P.g 1) * bar q (P.g 2) * bar q (P.r 0) else 0) := by
  classical
  obtain ⟨hMq, hMT, hrows, hgaps, hu, hv, hw⟩ := four_endpoint_index_bounds hP
  have hne : secondGenerator hP ≠ q := by
    intro he
    have := congrArg (fun v : ℕ+ => (v.val : ℤ)) he
    rw [secondGenerator_val] at this
    omega
  have hderiv (k : ℤ) (hk : k ≠ secondIndex P) :
      MvPolynomial.pderiv (secondGenerator hP) (bar q k) = 0 := by
    rw [residual_pderiv_bar q _ hne, secondGenerator_val, if_neg hk]
  have hrow (i : Fin 4) := hderiv (P.r i) (ne_of_lt (hrows i))
  have hgap (j : Fin 3) := hderiv (P.g j) (ne_of_lt (hgaps j))
  have hU := hderiv ((P.r 0 : ℤ) + P.r 1 - P.g 0) (ne_of_lt hu)
  have hV := hderiv ((P.r 1 : ℤ) + P.r 2 - P.g 1) (ne_of_lt hv)
  have hW := hderiv ((P.r 2 : ℤ) + P.r 3 - P.g 2) (ne_of_lt hw)
  have hT := hderiv (fullIndex P) (ne_of_gt hMT)
  rw [fullIndex_four] at hT
  rw [restriction_four_expansion q P hP.thick]
  simp only [fourInterval, map_add, map_sub, MvPolynomial.pderiv_mul,
    hrow, hgap, hU, hV, hW, hT, zero_mul, mul_zero, zero_add, add_zero,
    zero_sub, sub_zero, residual_pderiv_bar q _ hne, secondGenerator_val]
  change (if prefixIndex P = secondIndex P then (1 : CompleteRing) else 0) *
      bar q (P.g 0) * bar q (P.g 1) * bar q (P.r 3) +
    bar q (P.r 0) *
      (if suffixIndex P = secondIndex P then (1 : CompleteRing) else 0) *
      bar q (P.g 1) * bar q (P.g 2) = _
  split_ifs <;> ring

/-- The full-interval derivative is the exact signed gap monomial. -/
theorem four_full_coefficient {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) :
    MvPolynomial.pderiv (fullGenerator P) (restriction q P) = -gapMonomial P := by
  rw [restriction_affine hP]
  have hg := MvPolynomial.pderiv_eq_zero_of_notMem_vars
    (full_not_mem_gapMonomial hP.thick)
  have hr := MvPolynomial.pderiv_eq_zero_of_notMem_vars
    (full_not_mem_residual q P)
  norm_num [MvPolynomial.pderiv_mul, hg, hr]

/-- Equal actual content and equal restrictions give equal canonical primitives. -/
theorem canonical_eq_of_content_and_restriction_eq {n : ℕ} {q : ℕ+}
    {P Q : Profile n} (hP : QComponent q P) (hQ : QComponent q Q)
    (hc : monicContent hP = monicContent hQ)
    (he : restriction q P = restriction q Q) :
    canonicalPrimitive hP = canonicalPrimitive hQ := by
  have hn : monicContent hP ≠ 0 := by
    simp [monicContent, MvPolynomial.monomial_eq_zero]
  apply mul_left_cancel₀ hn
  rw [monicContent_mul_canonicalPrimitive hP, hc,
    monicContent_mul_canonicalPrimitive hQ, he]

/-- The two-row restriction retains its full independent complete convention. -/
theorem restriction_two_expansion (q : ℕ+) (P : Profile 1) :
    restriction q P = bar q (P.r 0) * bar q (P.r 1) -
      bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0) * bar q (P.g 0) := by
  have h0 := P.xi_sub_zeta (0 : Fin 2)
  have h1 := P.xi_sub_zeta (1 : Fin 2)
  have hg := P.xi_succ_sub_zeta_castSucc (0 : Fin 1)
  change P.xi 1 - P.zeta 0 = (P.g 0 : ℤ) at hg
  have hu : P.xi 0 - P.zeta 1 = (P.r 0 : ℤ) + P.r 1 - P.g 0 := by omega
  unfold restriction
  rw [BetaDiagram.schur, Matrix.det_fin_two]
  change eraseGenerator q
      (complete (P.xi 0 - P.zeta 0) * complete (P.xi 1 - P.zeta 1) -
        complete (P.xi 0 - P.zeta 1) * complete (P.xi 1 - P.zeta 0)) = _
  rw [h0, h1, hg, hu, map_sub, map_mul, map_mul]
  rfl

/-- A surviving two-row first row has exactly the normalized B origin. -/
theorem canonical_two_B {q : ℕ+} {P : Profile 1} (hP : QComponent q P)
    (ha : P.r 0 ≠ q.val) :
    canonicalPrimitive hP = quadraticB (P.g 0) (P.r 0) (P.r 1) := by
  have hc := two_content_first_row_ne hP ha
  have hb : q.val + P.g 0 < P.r 1 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hu : (q.val : ℤ) < (P.r 0 : ℤ) + P.r 1 - P.g 0 := by
    have := P.r_pos 0
    omega
  have hm := monicContent_mul_canonicalPrimitive hP
  rw [hc, one_mul, restriction_two_expansion] at hm
  have hbar (k : ℤ) (hk : k ≠ (q.val : ℤ)) : bar q k = complete k := by
    rw [bar, eraseGenerator_complete, if_neg hk]
  rw [hbar (P.r 0) (by exact_mod_cast ha),
    hbar (P.r 1) (by omega), hbar _ (ne_of_gt hu),
    hbar (P.g 0) (by exact_mod_cast hP.gap_ne 0)] at hm
  simp only [pow_one, neg_mul, one_mul] at hm
  calc
    canonicalPrimitive hP =
        -(complete (P.r 0) * complete (P.r 1) -
          complete ((P.r 0 : ℤ) + P.r 1 - P.g 0) * complete (P.g 0)) := hm
    _ = quadraticB (P.g 0) (P.r 0) (P.r 1) := by
      unfold quadraticB
      ring

/-- Endpoint erasure is a linear primitive, with the sharper two-row bound. -/
theorem canonical_two_linear {q : ℕ+} {P : Profile 1} (hP : QComponent q P)
    (ha : P.r 0 = q.val) :
    canonicalPrimitive hP = complete ((P.r 0 : ℤ) + P.r 1 - P.g 0) ∧
      2 * (q.val : ℤ) < (P.r 0 : ℤ) + P.r 1 - P.g 0 := by
  have hb : q.val + P.g 0 < P.r 1 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hu : 2 * (q.val : ℤ) < (P.r 0 : ℤ) + P.r 1 - P.g 0 := by omega
  refine ⟨?_, hu⟩
  have hm := monicContent_mul_canonicalPrimitive hP
  rw [two_content_first_row hP ha, restriction_two_expansion] at hm
  have hr : bar q (P.g 0) = complete (P.g 0) := by
    rw [bar, eraseGenerator_complete, if_neg (by exact_mod_cast hP.gap_ne 0)]
  have hU : bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0) =
      complete ((P.r 0 : ℤ) + P.r 1 - P.g 0) := by
    rw [bar, eraseGenerator_complete, if_neg (by have := q.pos; omega)]
  apply mul_left_cancel₀
    ((complete_ne_zero_iff (P.g 0)).mpr (show (0 : ℤ) ≤ P.g 0 by positivity))
  rw [hm, hr, hU]
  simp [ha]
  <;> ring

/-- Exact full-function defect of the residual quartet, before restricting q. -/
theorem residual_family_defect {R : Type*} [CommRing R] (h : ℤ → R)
    (a q r s : ℤ) :
    fourInterval h a q a (a + 2 * q - r - s) r s r -
      fourInterval h a (a + q - s) q (a + q - r) r r s =
    h q * (h a * (h a * h (a + 2 * q - r - s) -
      h r * h (2 * a + 2 * q - 2 * r - s)) -
      h (a + q - r) * (h a * h (a + q - s) -
        h r * h (2 * a + q - r - s))) := by
  simp only [fourInterval]
  ring_nf

/-- The new quartic equality is a generator erasure, including its cubic limit. -/
theorem residual_family_restriction (q : ℕ+) (a r s : ℤ) :
    fourInterval (bar q) a q.val a (a + 2 * q.val - r - s) r s r =
      fourInterval (bar q) a (a + q.val - s) q.val (a + q.val - r) r r s := by
  have he := residual_family_defect (bar q) a q.val r s
  rw [bar_cut, zero_mul] at he
  exact sub_eq_zero.mp he

/-- The positive-generator augmentation does not count distinct monomials. -/
noncomputable def residualAugmentation : CompleteRing →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun _ => 1)

theorem residualAugmentation_complete {k : ℤ} (hk : 0 < k) :
    residualAugmentation (complete k) = 1 := by
  let v : ℕ+ := ⟨k.toNat, by omega⟩
  have hv : (v.val : ℤ) = k := by
    dsimp [v]
    omega
  have he : complete k = (MvPolynomial.X v : CompleteRing) := by
    rw [← hv]
    exact complete_nat v
  rw [he]
  exact MvPolynomial.eval₂Hom_X' _ _ v

/-- Augmentation after erasure counts surviving positive factors, with multiplicity. -/
theorem residualAugmentation_bar (q : ℕ+) {k : ℤ} (hk : 0 < k) :
    residualAugmentation (bar q k) = if k = (q.val : ℤ) then 0 else 1 := by
  by_cases hq : k = (q.val : ℤ)
  · simp only [bar, eraseGenerator_complete, if_pos hq, map_zero]
  · simp only [bar, eraseGenerator_complete, if_neg hq]
    exact residualAugmentation_complete hk



/-- The largest generator in B is private. -/
theorem quadraticB_top (r a c : ℤ) (hr : 0 < r) (ha : r < a) (hc : r < c)
    (v : ℕ+) (hv : (v.val : ℤ) = a + c - r) :
    MvPolynomial.pderiv v (quadraticB r a c) = complete r := by
  simp only [quadraticB, map_sub, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, hv, if_pos rfl, ite_true, ite_false,
    if_neg (show r ≠ a + c - r by omega),
    if_neg (show a ≠ a + c - r by omega),
    if_neg (show c ≠ a + c - r by omega)]
  ring

theorem quadraticB_above (r a c : ℤ) (hr : 0 < r) (ha : r < a) (hc : r < c)
    (v : ℕ+) (hv : a + c - r < (v.val : ℤ)) :
    MvPolynomial.pderiv v (quadraticB r a c) = 0 := by
  simp only [quadraticB, map_sub, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, if_neg (show r ≠ (v.val : ℤ) by omega),
    if_neg (show a + c - r ≠ (v.val : ℤ) by omega),
    if_neg (show a ≠ (v.val : ℤ) by omega),
    if_neg (show c ≠ (v.val : ℤ) by omega)]
  ring

/-- Exact B matching key, with multiplicity and no generic-position restriction. -/
theorem quadraticB_eq_iff (r a c R A C : ℤ)
    (hr : 0 < r) (ha : r < a) (hc : r < c)
    (hR : 0 < R) (hA : R < A) (hC : R < C) :
    quadraticB r a c = quadraticB R A C ↔
      r = R ∧ ((a = A ∧ c = C) ∨ (a = C ∧ c = A)) := by
  constructor
  · intro he
    have hT : a + c - r = A + C - R := by
      rcases lt_trichotomy (a + c - r) (A + C - R) with h | h | h
      · let v : ℕ+ := ⟨(A + C - R).toNat, by omega⟩
        have hv : (v.val : ℤ) = A + C - R := by dsimp [v]; omega
        have hd := congrArg (MvPolynomial.pderiv v) he
        rw [quadraticB_above r a c hr ha hc v (by omega),
          quadraticB_top R A C hR hA hC v hv] at hd
        exact ((complete_ne_zero_iff R).mpr hR.le hd.symm).elim
      · exact h
      · let v : ℕ+ := ⟨(a + c - r).toNat, by omega⟩
        have hv : (v.val : ℤ) = a + c - r := by dsimp [v]; omega
        have hd := congrArg (MvPolynomial.pderiv v) he
        rw [quadraticB_top r a c hr ha hc v hv,
          quadraticB_above R A C hR hA hC v (by omega)] at hd
        exact ((complete_ne_zero_iff r).mpr hr.le hd).elim
    let v : ℕ+ := ⟨(a + c - r).toNat, by omega⟩
    have hv : (v.val : ℤ) = a + c - r := by dsimp [v]; omega
    have hd := congrArg (MvPolynomial.pderiv v) he
    rw [quadraticB_top r a c hr ha hc v hv,
      quadraticB_top R A C hR hA hC v (hv.trans hT)] at hd
    have hgap := complete_injective_nonnegative hr.le hR.le hd
    refine ⟨hgap, ?_⟩
    have hp : complete a * complete c = complete A * complete C := by
      unfold quadraticB at he
      rw [hT, hgap] at he
      exact sub_right_injective he
    exact complete_two_product_reading (by omega) (by omega) (by omega) (by omega) hp
  · rintro ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · rfl
    · simp only [quadraticB, add_comm, add_left_comm, add_assoc]
      ring

theorem bar_eq_complete_of_ne (q : ℕ+) (k : ℤ) (hk : k ≠ (q.val : ℤ)) :
    bar q k = complete k := by
  rw [bar, eraseGenerator_complete, if_neg hk]

/-- Endpoint contraction gives the B quadratic with its exact inherited domain. -/
theorem canonical_three_endpoint_B {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 = q.val) :
    canonicalPrimitive hP = quadraticB (P.g 1)
      ((P.r 0 : ℤ) + P.r 1 - P.g 0) (P.r 2) := by
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hm := monicContent_mul_canonicalPrimitive hP
  rw [three_content_first_row hP ha, restriction_three_first_row_cut P hP.thick ha] at hm
  have hU : (q.val : ℤ) < (P.r 0 : ℤ) + P.r 1 - P.g 0 := by omega
  have hT : (q.val : ℤ) < (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 := by omega
  rw [bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q _ (ne_of_gt hU),
    bar_eq_complete_of_ne q (P.r 2) (by omega),
    bar_eq_complete_of_ne q _ (ne_of_gt hT),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1)] at hm
  apply mul_left_cancel₀ ((complete_ne_zero_iff (P.g 0)).mpr (by positivity))
  rw [hm]
  norm_num [quadraticB]
  have hidx : (P.r 0 : ℤ) + P.r 1 - P.g 0 + P.r 2 - P.g 1 =
      (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 := by ring
  rw [hidx]
  ring

/-- Repeated gaps in a middle contact produce the canonical M polynomial. -/
theorem canonical_three_middle_M {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hb : P.r 1 = q.val) (hrs : P.g 0 = P.g 1) :
    canonicalPrimitive hP = quadraticM q.val (P.g 0) (P.r 0) (P.r 2) := by
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hend : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hm := monicContent_mul_canonicalPrimitive hP
  have hcontent : monicContent hP = complete (P.g 0) := by
    rw [three_content hP, if_neg ha, if_pos (Or.inl ⟨hb, hrs⟩), ← hrs]
  rw [hcontent, restriction_three_expansion q P hP.thick] at hm
  have hU : (q.val : ℤ) < (P.r 0 : ℤ) + P.r 1 - P.g 0 := by omega
  have hV : (q.val : ℤ) < (P.r 1 : ℤ) + P.r 2 - P.g 1 := by omega
  have hT : (q.val : ℤ) < (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 := by omega
  simp only [threeInterval, hb, bar_cut, mul_zero, zero_mul, zero_sub] at hm
  rw [bar_eq_complete_of_ne q (P.r 0) (by exact_mod_cast ha),
    bar_eq_complete_of_ne q (P.r 2) (by omega),
    bar_eq_complete_of_ne q ((P.r 0 : ℤ) + q.val - P.g 0) (by omega),
    bar_eq_complete_of_ne q ((q.val : ℤ) + P.r 2 - P.g 1) (by omega),
    bar_eq_complete_of_ne q
      ((P.r 0 : ℤ) + q.val + P.r 2 - P.g 0 - P.g 1) (by omega),
    bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1)] at hm
  apply mul_left_cancel₀ ((complete_ne_zero_iff (P.g 0)).mpr (by positivity))
  rw [hm]
  simp only [hrs, hb, quadraticM]
  have ht : (P.r 0 : ℤ) + q.val + P.r 2 - P.g 1 - P.g 1 =
      (P.r 0 : ℤ) + P.r 2 + q.val - 2 * P.g 1 := by ring
  have hv : (q.val : ℤ) + P.r 2 - P.g 1 =
      (P.r 2 : ℤ) + q.val - P.g 1 := by ring
  rw [ht, hv]
  norm_num
  ring

/-- Interval extraction gives I, including every possible same-sign collision. -/
theorem canonical_three_interval_I {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val)
    (has : P.r 0 = P.g 1) :
    canonicalPrimitive hP = quadraticI q.val (P.g 0) (P.g 1) (P.r 2) := by
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hend : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have ha : P.r 0 ≠ q.val := by omega
  have hb : (P.r 1 : ℤ) = q.val - P.g 1 + P.g 0 := by omega
  have hm := monicContent_mul_canonicalPrimitive hP
  have hcontent : monicContent hP = complete (P.g 1) := by
    rw [three_content hP, if_neg ha, if_pos (Or.inr ⟨hu, has⟩)]
  rw [hcontent, restriction_three_expansion q P hP.thick] at hm
  simp only [threeInterval, hu, bar_cut, mul_zero, zero_mul, sub_zero] at hm
  rw [bar_eq_complete_of_ne q (P.r 0) (by omega),
    bar_eq_complete_of_ne q (P.r 1) (by omega),
    bar_eq_complete_of_ne q (P.r 2) (by omega),
    bar_eq_complete_of_ne q ((P.r 1 : ℤ) + P.r 2 - P.g 1) (by omega),
    bar_eq_complete_of_ne q
      ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) (by omega),
    bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1)] at hm
  apply mul_left_cancel₀ ((complete_ne_zero_iff (P.g 1)).mpr (by positivity))
  rw [hm]
  rw [has]
  change _ = complete (P.g 1) * quadraticI q.val (P.g 0) (P.g 1) (P.r 2)
  have hV : (P.r 1 : ℤ) + P.r 2 - P.g 1 =
      q.val + P.r 2 - 2 * P.g 1 + P.g 0 := by omega
  have hT : (P.g 1 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 =
      q.val + P.r 2 - P.g 1 := by omega
  rw [hV, hT, hb]
  norm_num [quadraticI]
  ring

/-- First actual representative of the residual quartet. -/
def residualFamilyA (a q r s : ℕ) (ha : r + s < a) (hq : r + s < q) :
    Profile 3 where
  r := ![a, q, a, a + 2 * q - r - s]
  g := ![r, s, r]
  r_pos := by intro i; fin_cases i <;> simp <;> omega
  g_lt_castSucc := by intro i; fin_cases i <;> simp <;> omega
  g_lt_succ := by intro i; fin_cases i <;> simp <;> omega

/-- Second actual representative, with the two high rows in their exact order. -/
def residualFamilyB (a q r s : ℕ) (ha : r + s < a) (hq : r + s < q) :
    Profile 3 where
  r := ![a, a + q - s, q, a + q - r]
  g := ![r, r, s]
  r_pos := by intro i; fin_cases i <;> simp <;> omega
  g_lt_castSucc := by intro i; fin_cases i <;> simp <;> omega
  g_lt_succ := by intro i; fin_cases i <;> simp <;> omega

theorem residualFamilyA_component (a : ℕ) (q : ℕ+) (r s : ℕ)
    (ha : r + s < a) (hq : r + s < q.val) (hr : 0 < r) (hs : 0 < s) :
    QComponent q (residualFamilyA a q.val r s ha hq) := by
  constructor
  · intro j k hjk
    fin_cases j <;> fin_cases k <;>
      simp [residualFamilyA] at hjk ⊢ <;> omega
  · intro j; fin_cases j <;> simp [residualFamilyA]
      <;> omega
  · intro j; fin_cases j <;> simp [residualFamilyA] <;> omega
  · simp [lastGap, residualFamilyA, Fin.sum_univ_succ]
    omega

theorem residualFamilyB_component (a : ℕ) (q : ℕ+) (r s : ℕ)
    (ha : r + s < a) (hq : r + s < q.val) (hr : 0 < r) (hs : 0 < s) :
    QComponent q (residualFamilyB a q.val r s ha hq) := by
  constructor
  · intro j k hjk
    fin_cases j <;> fin_cases k <;>
      simp [residualFamilyB] at hjk ⊢ <;> omega
  · intro j; fin_cases j <;> simp [residualFamilyB] <;> omega
  · intro j; fin_cases j <;> simp [residualFamilyB] <;> omega
  · simp [lastGap, residualFamilyB, Fin.sum_univ_succ]
    omega

/-- Both actual restrictions agree, not just the interval-polynomial presentations. -/
theorem residualFamily_restriction_eq (a : ℕ) (q : ℕ+) (r s : ℕ)
    (ha : r + s < a) (hq : r + s < q.val) (hr : 0 < r) (hs : 0 < s) :
    restriction q (residualFamilyA a q.val r s ha hq) =
      restriction q (residualFamilyB a q.val r s ha hq) := by
  have hA := residualFamilyA_component a q r s ha hq hr hs
  have hB := residualFamilyB_component a q r s ha hq hr hs
  rw [restriction_four_expansion q _ hA.thick,
    restriction_four_expansion q _ hB.thick]
  have hD : ((a + 2 * q.val - r - s : ℕ) : ℤ) = (a : ℤ) + 2 * q.val - r - s := by omega
  have hU : ((a + q.val - r : ℕ) : ℤ) = (a : ℤ) + q.val - r := by omega
  have hV : ((a + q.val - s : ℕ) : ℤ) = (a : ℤ) + q.val - s := by omega
  simpa only [residualFamilyA, residualFamilyB, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, hD, hU, hV] using
      residual_family_restriction q (a : ℤ) (r : ℤ) (s : ℤ)

/-- The actual gcd table specializes to the same monic content on both sides.
At equal gaps the common content is one gap generator, not its square. -/
theorem residualFamily_content_eq (a : ℕ) (q : ℕ+) (r s : ℕ)
    (ha : r + s < a) (hq : r + s < q.val) (hr : 0 < r) (hs : 0 < s)
    (haq : a ≠ q.val) :
    monicContent (residualFamilyA_component a q r s ha hq hr hs) =
      monicContent (residualFamilyB_component a q r s ha hq hr hs) := by
  rw [four_content, four_content]
  have hU : (a : ℤ) + q.val - r ≠ q.val := by omega
  have hBq : a + q.val - s ≠ q.val := by omega
  have hV : (a : ℤ) + (a + q.val - s : ℕ) - r ≠ q.val := by omega
  by_cases hrs : r = s
  · subst s
    simp [residualFamilyA, residualFamilyB, haq]
  · have hsr : s ≠ r := Ne.symm hrs
    simp [residualFamilyA, residualFamilyB, haq, hU, hBq, hV, hrs, hsr]

/-- Exact canonical equality of both actual components, for arbitrary positive
parameters in the stated thickness/boundary domain, including equal gaps. -/
theorem residualFamily_canonical_eq (a : ℕ) (q : ℕ+) (r s : ℕ)
    (ha : r + s < a) (hq : r + s < q.val) (hr : 0 < r) (hs : 0 < s)
    (haq : a ≠ q.val) :
    canonicalPrimitive (residualFamilyA_component a q r s ha hq hr hs) =
      canonicalPrimitive (residualFamilyB_component a q r s ha hq hr hs) :=
  canonical_eq_of_content_and_restriction_eq _ _
    (residualFamily_content_eq a q r s ha hq hr hs haq)
    (residualFamily_restriction_eq a q r s ha hq hr hs)

/-- Unequal gaps make the quartet representatives genuinely different. -/
theorem residualFamily_ne (a q r s : ℕ) (ha : r + s < a) (hq : r + s < q)
    (hrs : r ≠ s) :
    residualFamilyA a q r s ha hq ≠ residualFamilyB a q r s ha hq := by
  intro he
  have h := congrArg (fun P : Profile 3 => P.g 1) he
  simp [residualFamilyA, residualFamilyB] at h
  exact hrs h.symm

/-- These two representatives are not related by profile rotation. -/
theorem residualFamily_ne_rotate (a q r s : ℕ) (ha : r + s < a) (hq : r + s < q) :
    residualFamilyA a q r s ha hq ≠ (residualFamilyB a q r s ha hq).rotate := by
  intro he
  have h := congrArg (fun P : Profile 3 => P.r 0) he
  simp [residualFamilyA, residualFamilyB, Profile.rotate] at h
  omega

/-- The endpoint identity contracts the actual four-row determinant. -/
theorem four_endpoint_contract_restriction {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 = q.val) :
    restriction q P = -complete (P.g 0) *
      restriction q (GeneralHessenberg.contract P 0) := by
  have hC := four_endpoint_contract_component hP ha
  obtain ⟨hr0, hr1, hr2, hg0, hg1⟩ := four_endpoint_contract_coordinates P
  rw [restriction_four_first_row_cut P hP.thick ha,
    restriction_three_expansion q _ hC.thick]
  rw [bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0)]
  simp only [hr0, hr1, hr2, hg0, hg1]

/-- Endpoint contraction preserves the actual canonical primitive, regardless
of the contracted contact type or repeated gap labels. -/
theorem four_endpoint_contract_canonical {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 = q.val) :
    canonicalPrimitive hP =
      canonicalPrimitive (four_endpoint_contract_component hP ha) := by
  have hC := four_endpoint_contract_component hP ha
  have hG : monicContent hP ≠ 0 := by
    simp [monicContent, MvPolynomial.monomial_eq_zero]
  apply mul_left_cancel₀ hG
  rw [monicContent_mul_canonicalPrimitive hP,
    four_endpoint_contract_content hP ha, mul_assoc,
    monicContent_mul_canonicalPrimitive hC,
    four_endpoint_contract_restriction hP ha]
  norm_num

/-- Necessity and sufficiency within the entire endpoint-lift class.
The endpoint gaps are allowed to be different. -/
theorem endpoint_lifts_match_iff {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 = q.val) (hA : Q.r 0 = q.val) :
    canonicalPrimitive hP = canonicalPrimitive hQ ↔
      canonicalPrimitive (four_endpoint_contract_component hP ha) =
        canonicalPrimitive (four_endpoint_contract_component hQ hA) := by
  rw [four_endpoint_contract_canonical hP ha, four_endpoint_contract_canonical hQ hA]

/-- No actual matrix entry has the erased positive label.  Negative and unit
entries are included rather than being silently discarded. -/
def NoEntryContact {n : ℕ} (q : ℕ+) (P : Profile n) : Prop :=
  ∀ i j : Fin (n + 1), P.xi i - P.zeta j ≠ (q.val : ℤ)

/-- On an untouched actual array the restriction is the full function. -/
theorem restriction_eq_full_of_no_entry_contact {n : ℕ} {q : ℕ+} {P : Profile n}
    (hc : NoEntryContact q P) :
    restriction q P = P.toBetaDiagram.schur := by
  unfold restriction BetaDiagram.schur
  rw [(eraseGenerator q).map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change eraseGenerator q (complete (P.xi i - P.zeta j)) =
    complete (P.xi i - P.zeta j)
  rw [eraseGenerator_complete, if_neg (hc i j)]

/-- Untouched four-row arrays have no extracted content. -/
theorem four_content_untouched {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hc : NoEntryContact q P) : monicContent hP = 1 := by
  have ha : P.r 0 ≠ q.val := by
    have h := hc 0 0
    rw [P.xi_sub_zeta] at h
    exact_mod_cast h
  have hb : P.r 1 ≠ q.val := by
    have h := hc 1 1
    rw [P.xi_sub_zeta] at h
    exact_mod_cast h
  have hcc : P.r 2 ≠ q.val := by
    have h := hc 2 2
    rw [P.xi_sub_zeta] at h
    exact_mod_cast h
  have hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by
    have hi := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M 0 1) P.indices_four
    change P.xi 0 - P.zeta 1 = (P.r 0 : ℤ) + P.r 1 - P.g 0 at hi
    intro he
    exact hc 0 1 (hi.trans he)
  rw [four_content hP, if_neg ha]
  simp [hb, hcc, hu]

/-- Necessity and sufficiency of the full four-row alternatives on the untouched
stratum, using the actual canonical primitive, not a supplied classification. -/
theorem untouched_four_match_iff {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hcP : NoEntryContact q P) (hcQ : NoEntryContact q Q) :
    canonicalPrimitive hP = canonicalPrimitive hQ ↔ FourRowHessenberg.Classified P Q := by
  have hPcan : canonicalPrimitive hP = -P.toBetaDiagram.schur := by
    have h := monicContent_mul_canonicalPrimitive hP
    rw [four_content_untouched hP hcP, one_mul,
      restriction_eq_full_of_no_entry_contact hcP] at h
    have hs : (-1 : CompleteRing) ^ 3 = -1 := by norm_num
    simpa only [hs, neg_one_mul] using h
  have hQcan : canonicalPrimitive hQ = -Q.toBetaDiagram.schur := by
    have h := monicContent_mul_canonicalPrimitive hQ
    rw [four_content_untouched hQ hcQ, one_mul,
      restriction_eq_full_of_no_entry_contact hcQ] at h
    have hs : (-1 : CompleteRing) ^ 3 = -1 := by norm_num
    simpa only [hs, neg_one_mul] using h
  rw [hPcan, hQcan, neg_inj, Profile.toBetaDiagram_schur, Profile.toBetaDiagram_schur]
  exact FourRowHessenberg.hessenberg_schur_eq_iff P Q hP.thick.hessenberg hQ.thick.hessenberg

theorem quadraticB_augmentation (r a c : ℤ) (hr : 0 < r) (ha : r < a) (hc : r < c) :
    residualAugmentation (quadraticB r a c) = 0 := by
  simp only [quadraticB, map_sub, map_mul,
    residualAugmentation_complete hr,
    residualAugmentation_complete (show 0 < a + c - r by omega),
    residualAugmentation_complete (show 0 < a by omega),
    residualAugmentation_complete (show 0 < c by omega)]
  norm_num

theorem quadraticM_augmentation (q r a c : ℤ)
    (hr : 0 < r) (hq : 2 * r < q) (ha : r < a) (hc : r < c) :
    residualAugmentation (quadraticM q r a c) = -1 := by
  simp only [quadraticM, map_sub, map_mul,
    residualAugmentation_complete hr,
    residualAugmentation_complete (show 0 < a + c + q - 2 * r by omega),
    residualAugmentation_complete (show 0 < a + q - r by omega),
    residualAugmentation_complete (show 0 < c + q - r by omega),
    residualAugmentation_complete (show 0 < a by omega),
    residualAugmentation_complete (show 0 < c by omega)]
  norm_num

theorem quadraticI_augmentation (q r s c : ℤ)
    (hr : 0 < r) (hrs : r < s) (hq : 2 * s < q) (hc : q + s < c) :
    residualAugmentation (quadraticI q r s c) = 1 := by
  simp only [quadraticI, map_sub, map_add, map_mul,
    residualAugmentation_complete hr,
    residualAugmentation_complete (show 0 < s by omega),
    residualAugmentation_complete (show 0 < q - s + r by omega),
    residualAugmentation_complete (show 0 < q + c - 2 * s + r by omega),
    residualAugmentation_complete (show 0 < q + c - s by omega),
    residualAugmentation_complete (show 0 < c by omega)]
  norm_num

/-- Different quadratic types cannot match; their parameters need not agree. -/
theorem quadratic_types_disjoint (q r a c R A C u v w d : ℤ)
    (hr : 0 < r) (ha : r < a) (hc : r < c)
    (hR : 0 < R) (hQ : 2 * R < q) (hA : R < A) (hC : R < C)
    (hv : 0 < v) (hvw : v < w) (hu : 2 * w < u) (hd : u + w < d) :
    quadraticB r a c ≠ quadraticM q R A C ∧
      quadraticB r a c ≠ quadraticI u v w d ∧
      quadraticM q R A C ≠ quadraticI u v w d := by
  have hB := quadraticB_augmentation r a c hr ha hc
  have hM := quadraticM_augmentation q R A C hR hQ hA hC
  have hI := quadraticI_augmentation u v w d hv hvw hu hd
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hh := congrArg residualAugmentation he
    rw [hB, hM] at hh
    norm_num at hh
  · intro he
    have hh := congrArg residualAugmentation he
    rw [hB, hI] at hh
    norm_num at hh
  · intro he
    have hh := congrArg residualAugmentation he
    rw [hM, hI] at hh
    norm_num at hh

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/ThreeRowRigidity.lean
theorem residual_monomial_pair_reading (a b c d : ℕ+ →₀ ℕ)
    (h : (MvPolynomial.monomial a 1 : CompleteRing) + MvPolynomial.monomial b 1 =
      MvPolynomial.monomial c 1 + MvPolynomial.monomial d 1) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  have hinj := MvPolynomial.monomial_left_injective (σ := ℕ+)
    (show (1 : ℚ) ≠ 0 by norm_num)
  by_cases hac : a = c
  · subst c
    exact Or.inl ⟨rfl, hinj (add_left_cancel h)⟩
  · have had : a = d := by
      by_contra had
      have hh := congrArg (fun p : CompleteRing => p.coeff a) h
      simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial] at hh
      by_cases hab : a = b
      · subst b
        simp only [ite_eq_right (Ne.symm hac), ite_eq_right (Ne.symm had)] at hh
        norm_num at hh
      · simp only [ite_eq_right (Ne.symm hac), ite_eq_right (Ne.symm had),
          ite_eq_right (Ne.symm hab)] at hh
        norm_num at hh
    subst d
    have hh : MvPolynomial.monomial b (1 : ℚ) = MvPolynomial.monomial c 1 := by
      linear_combination h
    exact Or.inr ⟨rfl, hinj hh⟩

/-- Two positive pairs are read as a multiset of monomials, retaining a repeated pair. -/
private theorem positive_pair_sum_reading (a b c d A B C D : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (he : complete a * complete b + complete c * complete d =
      complete A * complete B + complete C * complete D) :
    (((a = A ∧ b = B) ∨ (a = B ∧ b = A)) ∧
      ((c = C ∧ d = D) ∨ (c = D ∧ d = C))) ∨
    (((a = C ∧ b = D) ∨ (a = D ∧ b = C)) ∧
      ((c = A ∧ d = B) ∨ (c = B ∧ d = A))) := by
  let e (i j : ℤ) := hExp i.toNat + hExp j.toNat
  have hm (i j : ℤ) (hi : 0 < i) (hj : 0 < j) :
      complete i * complete j = MvPolynomial.monomial (e i j) 1 := by
    rw [complete_eq_hh, complete_eq_hh, hh_eq_monomial hi.le, hh_eq_monomial hj.le,
      MvPolynomial.monomial_mul_monomial]
    simp only [mul_one, e]
  have hh := he
  rw [hm a b ha hb, hm c d hc hd, hm A B hA hB, hm C D hC hD] at hh
  rcases residual_monomial_pair_reading _ _ _ _ hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    constructor
    · apply complete_two_product_reading ha hb hA hB
      rw [hm a b ha hb, hm A B hA hB, h1]
    · apply complete_two_product_reading hc hd hC hD
      rw [hm c d hc hd, hm C D hC hD, h2]
  · right
    constructor
    · apply complete_two_product_reading ha hb hC hD
      rw [hm a b ha hb, hm C D hC hD, h1]
    · apply complete_two_product_reading hc hd hA hB
      rw [hm c d hc hd, hm A B hA hB, h2]

theorem private_top_reading (p f : CompleteRing) (T U : ℤ) (c d : CompleteRing)
    (hT : 0 < T) (hU : 0 < U) (hc : c ≠ 0) (hd : d ≠ 0)
    (hpt : ∀ v : ℕ+, (v.val : ℤ) = T → MvPolynomial.pderiv v p = c)
    (hft : ∀ v : ℕ+, (v.val : ℤ) = U → MvPolynomial.pderiv v f = d)
    (hpa : ∀ v : ℕ+, T < (v.val : ℤ) → MvPolynomial.pderiv v p = 0)
    (hfa : ∀ v : ℕ+, U < (v.val : ℤ) → MvPolynomial.pderiv v f = 0)
    (he : p = f) : T = U ∧ c = d := by
  have hTU : T = U := by
    rcases lt_trichotomy T U with h | h | h
    · let v : ℕ+ := ⟨U.toNat, by omega⟩
      have hv : (v.val : ℤ) = U := by dsimp [v]; omega
      have hh := congrArg (MvPolynomial.pderiv v) he
      rw [hpa v (by omega), hft v hv] at hh
      exact (hd hh.symm).elim
    · exact h
    · let v : ℕ+ := ⟨T.toNat, by omega⟩
      have hv : (v.val : ℤ) = T := by dsimp [v]; omega
      have hh := congrArg (MvPolynomial.pderiv v) he
      rw [hpt v hv, hfa v (by omega)] at hh
      exact (hc hh).elim
  refine ⟨hTU, ?_⟩
  let v : ℕ+ := ⟨T.toNat, by omega⟩
  have hv : (v.val : ℤ) = T := by dsimp [v]; omega
  have hh := congrArg (MvPolynomial.pderiv v) he
  rwa [hpt v hv, hft v (hv.trans hTU)] at hh

theorem quadraticM_top (q r a c : ℤ) (hr : 0 < r) (hq : 2 * r < q)
    (ha : r < a) (hc : r < c) (v : ℕ+)
    (hv : (v.val : ℤ) = a + c + q - 2 * r) :
    MvPolynomial.pderiv v (quadraticM q r a c) = complete r := by
  simp only [quadraticM, map_sub, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, hv, if_pos rfl, ite_true, ite_false,
    if_neg (show r ≠ a + c + q - 2 * r by omega),
    if_neg (show a + q - r ≠ a + c + q - 2 * r by omega),
    if_neg (show c ≠ a + c + q - 2 * r by omega),
    if_neg (show a ≠ a + c + q - 2 * r by omega),
    if_neg (show c + q - r ≠ a + c + q - 2 * r by omega)]
  ring

theorem quadraticM_above (q r a c : ℤ) (hr : 0 < r) (hq : 2 * r < q)
    (ha : r < a) (hc : r < c) (v : ℕ+)
    (hv : a + c + q - 2 * r < (v.val : ℤ)) :
    MvPolynomial.pderiv v (quadraticM q r a c) = 0 := by
  simp only [quadraticM, map_sub, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, if_neg (show r ≠ (v.val : ℤ) by omega),
    if_neg (show a + c + q - 2 * r ≠ (v.val : ℤ) by omega),
    if_neg (show a + q - r ≠ (v.val : ℤ) by omega),
    if_neg (show c ≠ (v.val : ℤ) by omega),
    if_neg (show a ≠ (v.val : ℤ) by omega),
    if_neg (show c + q - r ≠ (v.val : ℤ) by omega)]
  ring

/-- Exact M matching key, including the coefficient-two repeated negative monomial. -/
theorem quadraticM_eq_iff (q r a c R A C : ℤ)
    (hr : 0 < r) (hq : 2 * r < q) (ha : r < a) (hc : r < c)
    (hR : 0 < R) (hQ : 2 * R < q) (hA : R < A) (hC : R < C) :
    quadraticM q r a c = quadraticM q R A C ↔
      r = R ∧ ((a = A ∧ c = C) ∨ (a = C ∧ c = A)) := by
  constructor
  · intro he
    have htop := private_top_reading _ _
      (a + c + q - 2 * r) (A + C + q - 2 * R) (complete r) (complete R)
      (by omega) (by omega) ((complete_ne_zero_iff _).mpr hr.le)
      ((complete_ne_zero_iff _).mpr hR.le)
      (quadraticM_top q r a c hr hq ha hc)
      (quadraticM_top q R A C hR hQ hA hC)
      (quadraticM_above q r a c hr hq ha hc)
      (quadraticM_above q R A C hR hQ hA hC) he
    have hgap := complete_injective_nonnegative hr.le hR.le htop.2
    refine ⟨hgap, ?_⟩
    have hs : complete (a + q - r) * complete c + complete a * complete (c + q - r) =
        complete (A + q - r) * complete C + complete A * complete (C + q - r) := by
      unfold quadraticM at he
      rw [htop.1, hgap] at he
      rw [hgap]
      linear_combination -he
    have hp := positive_pair_sum_reading (a + q - r) c a (c + q - r)
      (A + q - r) C A (C + q - r)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) hs
    rcases hp with ⟨hpair1, hpair2⟩ | ⟨hpair1, hpair2⟩ <;>
      rcases hpair1 with ⟨h11, h12⟩ | ⟨h11, h12⟩ <;>
      rcases hpair2 with ⟨h21, h22⟩ | ⟨h21, h22⟩ <;> omega
  · rintro ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · rfl
    · simp only [quadraticM, add_comm, add_left_comm, add_assoc]
      ring

/-- Removing I's private largest term leaves the negative of a B binomial. -/
theorem quadraticI_split (q r s c : ℤ) :
    quadraticI q r s c = complete r * complete (q + c - s) -
      quadraticB s (q - s + r) c := by
  unfold quadraticI quadraticB
  have hi : q - s + r + c - s = q + c - 2 * s + r := by ring
  rw [hi]
  ring

theorem quadraticI_top (q r s c : ℤ)
    (hr : 0 < r) (hrs : r < s) (hq : 2 * s < q) (hc : q + s < c)
    (v : ℕ+) (hv : (v.val : ℤ) = q + c - s) :
    MvPolynomial.pderiv v (quadraticI q r s c) = complete r := by
  simp only [quadraticI, map_sub, map_add, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, hv, if_pos rfl, ite_true, ite_false,
    if_neg (show q - s + r ≠ q + c - s by omega),
    if_neg (show c ≠ q + c - s by omega),
    if_neg (show s ≠ q + c - s by omega),
    if_neg (show q + c - 2 * s + r ≠ q + c - s by omega),
    if_neg (show r ≠ q + c - s by omega)]
  ring

theorem quadraticI_above (q r s c : ℤ)
    (hr : 0 < r) (hrs : r < s) (hq : 2 * s < q) (hc : q + s < c)
    (v : ℕ+) (hv : q + c - s < (v.val : ℤ)) :
    MvPolynomial.pderiv v (quadraticI q r s c) = 0 := by
  simp only [quadraticI, map_sub, map_add, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, if_neg (show q - s + r ≠ (v.val : ℤ) by omega),
    if_neg (show c ≠ (v.val : ℤ) by omega),
    if_neg (show s ≠ (v.val : ℤ) by omega),
    if_neg (show q + c - 2 * s + r ≠ (v.val : ℤ) by omega),
    if_neg (show r ≠ (v.val : ℤ) by omega),
    if_neg (show q + c - s ≠ (v.val : ℤ) by omega)]
  ring

/-- Exact I matching key; the smaller negative factor and the private top
coefficient fix both gaps even when the two positive monomials coincide. -/
theorem quadraticI_eq_iff (q r s c R S C : ℤ)
    (hr : 0 < r) (hrs : r < s) (hq : 2 * s < q) (hc : q + s < c)
    (hR : 0 < R) (hRS : R < S) (hQ : 2 * S < q) (hC : q + S < C) :
    quadraticI q r s c = quadraticI q R S C ↔ r = R ∧ s = S ∧ c = C := by
  constructor
  · intro he
    have htop := private_top_reading _ _
      (q + c - s) (q + C - S) (complete r) (complete R)
      (by omega) (by omega) ((complete_ne_zero_iff _).mpr hr.le)
      ((complete_ne_zero_iff _).mpr hR.le)
      (quadraticI_top q r s c hr hrs hq hc)
      (quadraticI_top q R S C hR hRS hQ hC)
      (quadraticI_above q r s c hr hrs hq hc)
      (quadraticI_above q R S C hR hRS hQ hC) he
    have hgap := complete_injective_nonnegative hr.le hR.le htop.2
    have hbin : quadraticB s (q - s + r) c = quadraticB S (q - S + R) C := by
      rw [quadraticI_split, quadraticI_split, htop.1, hgap] at he
      rw [hgap]
      exact sub_right_injective he
    have hb := (quadraticB_eq_iff s (q - s + r) c S (q - S + R) C
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp hbin
    exact ⟨hgap, hb.1, by have := htop.1; omega⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The double endpoint-contact quadratic is the same actual M primitive as
its contracted three-row origin. -/
theorem canonical_four_double_M {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 = q.val)
    (hc : P.r 2 = q.val) (hst : P.g 1 = P.g 2) :
    canonicalPrimitive hP = quadraticM q.val (P.g 1)
      ((P.r 0 : ℤ) + P.r 1 - P.g 0) (P.r 3) := by
  have hC := four_endpoint_contract_component hP ha
  obtain ⟨hr0, hr1, hr2, hg0, hg1⟩ := four_endpoint_contract_coordinates P
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hfirst : (GeneralHessenberg.contract P 0).r 0 ≠ q.val := by omega
  rw [four_endpoint_contract_canonical hP ha]
  rw [canonical_three_middle_M hC hfirst (hr1.trans hc) (by rw [hg0, hg1, hst])]
  rw [hr0, hg0, hr2]

/-- Every content variable is below q, so every endpoint generator is private
from the content even when extracted gap occurrences coincide. -/
theorem not_mem_monicContent_above_cut {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (v : ℕ+) (hv : q.val < v.val) :
    v ∉ (monicContent hP).vars := by
  intro hm
  rw [monicContent, MvPolynomial.vars_monomial (by norm_num : (1 : ℚ) ≠ 0)] at hm
  have hl := contentExponent_support_lt_cut hP v hm
  omega

/-- Cross multiplication expresses the exact endpoint-coefficient ratio without
choosing a fraction-field representative or a numerical gcd unit. -/
theorem canonical_coefficient_ratio {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (v : ℕ+) (hv : q.val < v.val) :
    MvPolynomial.pderiv v (restriction q P) *
        MvPolynomial.pderiv (fullGenerator P) (canonicalPrimitive hP) =
      MvPolynomial.pderiv v (canonicalPrimitive hP) *
        MvPolynomial.pderiv (fullGenerator P) (restriction q P) := by
  have hfull : q.val < (fullGenerator P).val := by
    have h := fullIndex_gt_q hP
    have hval := fullGenerator_int_coe P
    omega
  have hdv := MvPolynomial.pderiv_eq_zero_of_notMem_vars
    (not_mem_monicContent_above_cut hP v hv)
  have hdf := MvPolynomial.pderiv_eq_zero_of_notMem_vars
    (not_mem_monicContent_above_cut hP (fullGenerator P) hfull)
  have hs : (-1 : CompleteRing) ^ n = MvPolynomial.C ((-1 : ℚ) ^ n) := by simp
  have hdsv : MvPolynomial.pderiv v ((-1 : CompleteRing) ^ n) = 0 := by
    rw [hs]
    exact MvPolynomial.pderiv_C
  have hdsf : MvPolynomial.pderiv (fullGenerator P) ((-1 : CompleteRing) ^ n) = 0 := by
    rw [hs]
    exact MvPolynomial.pderiv_C
  rw [restriction_eq_signed_content_mul_canonical hP]
  simp only [MvPolynomial.pderiv_mul, hdv, hdf, hdsv, hdsf,
    zero_mul, mul_zero, zero_add]
  ring

/-- In a strict suffix maximum the ordered left row/gap quotient is recovered. -/
theorem four_strict_suffix_endpoint {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hxy : prefixIndex P < suffixIndex P) :
    MvPolynomial.pderiv (secondGenerator hP) (restriction q P) *
        bar q (P.g 0) =
      -MvPolynomial.pderiv (fullGenerator P) (restriction q P) * bar q (P.r 0) := by
  rw [four_second_coefficient hP, four_full_coefficient hP]
  have hy : secondIndex P = suffixIndex P := max_eq_right hxy.le
  simp only [hy, if_pos rfl, ite_true, ite_false, if_neg (ne_of_lt hxy),
    zero_add, neg_neg, gapMonomial, Fin.prod_univ_three]
  rw [bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1),
    bar_eq_complete_of_ne q (P.g 2) (by exact_mod_cast hP.gap_ne 2)]
  ring

/-- In a strict prefix maximum the ordered right row/gap quotient is recovered. -/
theorem four_strict_prefix_endpoint {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hxy : suffixIndex P < prefixIndex P) :
    MvPolynomial.pderiv (secondGenerator hP) (restriction q P) *
        bar q (P.g 2) =
      -MvPolynomial.pderiv (fullGenerator P) (restriction q P) * bar q (P.r 3) := by
  rw [four_second_coefficient hP, four_full_coefficient hP]
  have hx : secondIndex P = prefixIndex P := max_eq_left hxy.le
  simp only [hx, if_pos rfl, ite_true, ite_false, if_neg (ne_of_lt hxy),
    add_zero, neg_neg, gapMonomial, Fin.prod_univ_three]
  rw [bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1),
    bar_eq_complete_of_ne q (P.g 2) (by exact_mod_cast hP.gap_ne 2)]
  ring

theorem complete_pos_homogeneous (k : ℤ) (hk : 0 < k) :
    (complete k).IsHomogeneous 1 := by
  let v : ℕ+ := ⟨k.toNat, by omega⟩
  have hv : (v.val : ℤ) = k := by dsimp [v]; omega
  have he : complete k = (MvPolynomial.X v : CompleteRing) := by
    rw [← hv]
    exact complete_nat v
  rw [he]
  exact MvPolynomial.isHomogeneous_X ℚ v

/-- Thickness and positive gaps exclude index-zero entries in an actual component. -/
theorem component_entry_homogeneous {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (i j : Fin (n + 1)) :
    (complete (P.xi i - P.zeta j)).IsHomogeneous 1 := by
  by_cases hij : i ≤ j
  · have hz := P.zeta_strictAnti.antitone hij
    have hr : (0 : ℤ) < P.r i := by exact_mod_cast P.r_pos i
    have hd := P.xi_sub_zeta i
    have hp : 0 < P.xi i - P.zeta j := by omega
    exact complete_pos_homogeneous _ hp
  · by_cases hadj : j.val + 1 = i.val
    · let s : Fin n := ⟨j.val, by have := i.isLt; omega⟩
      have hi : i = s.succ := by ext; dsimp [s]; omega
      have hj : j = s.castSucc := by ext; rfl
      rw [hi, hj, P.xi_succ_sub_zeta_castSucc]
      have hp : (0 : ℤ) < P.g s := by exact_mod_cast hP.gap_pos s
      exact complete_pos_homogeneous _ hp
    · have hn := hP.thick.hessenberg i j (by have := i.isLt; have := j.isLt; omega)
      rw [complete_of_neg hn]
      exact MvPolynomial.isHomogeneous_zero ℕ+ ℚ 1

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/HomogeneousIrreducibility.lean
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/Gluing/Homogenization.lean
/-- The actual, nonhomogenized full component has pure ordinary row degree. -/
theorem component_schur_homogeneous {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : P.toBetaDiagram.schur.IsHomogeneous (n + 1) := by
  classical
  rw [BetaDiagram.schur, Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have hsign : ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : CompleteRing)).IsHomogeneous 0 := by
    rw [show ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : CompleteRing)) =
      MvPolynomial.C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) by simp]
    exact MvPolynomial.isHomogeneous_C _ _
  have hprod := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i : Fin (n + 1) => complete (P.xi (σ i) - P.zeta i))
    (fun _ => 1) (fun i _ => component_entry_homogeneous hP (σ i) i)
  simpa [BetaDiagram.matrix, Profile.toBetaDiagram] using hsign.mul hprod

/-- Erasing a generator preserves ordinary homogeneity, including every contact. -/
theorem restriction_homogeneous {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : (restriction q P).IsHomogeneous (n + 1) := by
  classical
  have h := (component_schur_homogeneous hP).eval₂
    (MvPolynomial.C : ℚ →+* CompleteRing)
    (fun v : ℕ+ => if v = q then (0 : CompleteRing) else MvPolynomial.X v)
    (fun a => MvPolynomial.isHomogeneous_C ℕ+ a)
    (fun v => by
      split_ifs
      · exact MvPolynomial.isHomogeneous_zero ℕ+ ℚ 1
      · exact MvPolynomial.isHomogeneous_X ℚ v)
  simpa only [one_mul, restriction, eraseGenerator,
    MvPolynomial.coe_eval₂Hom] using h

/-- The private full-interval term prevents a contacted restriction losing row degree. -/
theorem restriction_totalDegree {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) : (restriction q P).totalDegree = n + 1 :=
  (restriction_homogeneous hP).totalDegree (restriction_ne_zero hP)

/-- Equal restrictions recover row count before any first-coefficient comparison. -/
theorem row_count_eq_of_restriction_eq {n m : ℕ} {q : ℕ+}
    {P : Profile n} {Q : Profile m} (hP : QComponent q P) (hQ : QComponent q Q)
    (he : restriction q P = restriction q Q) : n = m := by
  have h := congrArg MvPolynomial.totalDegree he
  rw [restriction_totalDegree hP, restriction_totalDegree hQ] at h
  omega

theorem totalDegree_complete_pos (k : ℤ) (hk : 0 < k) :
    (complete k).totalDegree = 1 := by
  let v : ℕ+ := ⟨k.toNat, by omega⟩
  have hv : (v.val : ℤ) = k := by dsimp [v]; omega
  have he : complete k = (MvPolynomial.X v : CompleteRing) := by
    rw [← hv]
    exact complete_nat v
  rw [he]
  exact MvPolynomial.totalDegree_X v

/-- The extracted monomial degree and primitive degree add to the actual row count. -/
theorem content_degree_add_canonical_degree {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    (monicContent hP).totalDegree + (canonicalPrimitive hP).totalDegree = n + 1 := by
  have hc : monicContent hP ≠ 0 := by simp [monicContent, MvPolynomial.monomial_eq_zero]
  have hk : canonicalPrimitive hP ≠ 0 := (canonicalPrimitive_irreducible hP).ne_zero
  have hs : (-1 : CompleteRing) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h := congrArg MvPolynomial.totalDegree (monicContent_mul_canonicalPrimitive hP)
  rw [MvPolynomial.totalDegree_mul_of_isDomain hc hk,
    MvPolynomial.totalDegree_mul_of_isDomain hs (restriction_ne_zero hP)] at h
  have hconst : (((-1 : CompleteRing) ^ n)).totalDegree = 0 := by
    rw [show (-1 : CompleteRing) ^ n = MvPolynomial.C ((-1 : ℚ) ^ n) by simp]
    exact MvPolynomial.totalDegree_C _
  simpa only [hconst, zero_add, restriction_totalDegree hP] using h

/-- Exact exhaustive linear-origin classification through four rows.
No boundary for a two-row lift is imposed on the singleton origin. -/
theorem linear_origins_iff {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (hn : n ≤ 3) :
    (canonicalPrimitive hP).totalDegree = 1 ↔ n = 0 ∨ (n = 1 ∧ P.r 0 = q.val) := by
  have hdeg := content_degree_add_canonical_degree hP
  have hgap (j : Fin n) : (complete (P.g j)).totalDegree = 1 :=
    totalDegree_complete_pos _ (by exact_mod_cast hP.gap_pos j)
  interval_cases n
  · rw [singleton_content hP, MvPolynomial.totalDegree_one] at hdeg
    have hc : (canonicalPrimitive hP).totalDegree = 1 := by omega
    simp [hc]
  · rw [two_content hP] at hdeg
    by_cases ha : P.r 0 = q.val
    · rw [if_pos ha, hgap 0] at hdeg
      have hc : (canonicalPrimitive hP).totalDegree = 1 := by omega
      simp [hc, ha]
    · rw [if_neg ha, MvPolynomial.totalDegree_one] at hdeg
      have hc : (canonicalPrimitive hP).totalDegree ≠ 1 := by omega
      simp [hc, ha]
  · have hc : (canonicalPrimitive hP).totalDegree ≠ 1 := by
      rw [three_content hP] at hdeg
      split_ifs at hdeg <;>
        simp only [hgap, MvPolynomial.totalDegree_one] at hdeg <;> omega
    simp [hc]
  · have hc : (canonicalPrimitive hP).totalDegree ≠ 1 := by
      rw [four_content hP] at hdeg
      have hprod : (complete (P.g 0) * complete (P.g 1)).totalDegree = 2 := by
        rw [MvPolynomial.totalDegree_mul_of_isDomain
          ((complete_ne_zero_iff _).mpr (by positivity))
          ((complete_ne_zero_iff _).mpr (by positivity)), hgap 0, hgap 1]
      split_ifs at hdeg <;>
        simp only [hgap, hprod, MvPolynomial.totalDegree_one] at hdeg <;> omega
    simp [hc]

/-- The complete list of quadratic origins, stated only in actual row/gap data. -/
inductive QuadraticOrigin {q : ℕ+} : {n : ℕ} → Profile n → Prop
  | two (P : Profile 1) (ha : P.r 0 ≠ q.val) : QuadraticOrigin P
  | threeEndpoint (P : Profile 2) (ha : P.r 0 = q.val) : QuadraticOrigin P
  | threeMiddle (P : Profile 2) (ha : P.r 0 ≠ q.val)
      (hb : P.r 1 = q.val) (hrs : P.g 0 = P.g 1) : QuadraticOrigin P
  | threeInterval (P : Profile 2)
      (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val)
      (has : P.r 0 = P.g 1) : QuadraticOrigin P
  | fourDouble (P : Profile 3) (ha : P.r 0 = q.val)
      (hc : P.r 2 = q.val) (hst : P.g 1 = P.g 2) : QuadraticOrigin P

/-- Necessity of the origin list follows from the actual gcd and ordinary degree,
not from a numerical parameter search or an assumed matching theorem. -/
theorem quadratic_origin_of_degree_two {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (hn : n ≤ 3)
    (hd : (canonicalPrimitive hP).totalDegree = 2) : @QuadraticOrigin q n P := by
  have hdeg := content_degree_add_canonical_degree hP
  rw [hd] at hdeg
  have hgap (j : Fin n) : (complete (P.g j)).totalDegree = 1 :=
    totalDegree_complete_pos _ (by exact_mod_cast hP.gap_pos j)
  interval_cases n
  · rw [singleton_content hP, MvPolynomial.totalDegree_one] at hdeg
    omega
  · by_cases ha : P.r 0 = q.val
    · rw [two_content hP, if_pos ha, hgap 0] at hdeg
      omega
    · exact QuadraticOrigin.two P ha
  · by_cases ha : P.r 0 = q.val
    · exact QuadraticOrigin.threeEndpoint P ha
    · by_cases hcontact : (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
          ((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 0 = P.g 1)
      · rcases hcontact with ⟨hb, hrs⟩ | ⟨hu, has⟩
        · exact QuadraticOrigin.threeMiddle P ha hb hrs
        · exact QuadraticOrigin.threeInterval P hu has
      · rw [three_content hP, if_neg ha, if_neg hcontact,
          MvPolynomial.totalDegree_one] at hdeg
        omega
  · by_cases ha : P.r 0 = q.val
    · by_cases hdouble : P.r 2 = q.val ∧ P.g 1 = P.g 2
      · exact QuadraticOrigin.fourDouble P ha hdouble.1 hdouble.2
      · rw [four_content hP, if_pos ha, if_neg hdouble, hgap 0] at hdeg
        omega
    · rw [four_content hP, if_neg ha] at hdeg
      split_ifs at hdeg <;>
        simp only [hgap, MvPolynomial.totalDegree_one] at hdeg <;> omega

/-- Every listed origin is genuinely quadratic in its canonical actual normalization. -/
theorem QuadraticOrigin.degree_two {n : ℕ} {q : ℕ+} {P : Profile n}
    (ho : @QuadraticOrigin q n P) (hP : QComponent q P) :
    (canonicalPrimitive hP).totalDegree = 2 := by
  have hdeg := content_degree_add_canonical_degree hP
  have hgap (j : Fin n) : (complete (P.g j)).totalDegree = 1 :=
    totalDegree_complete_pos _ (by exact_mod_cast hP.gap_pos j)
  cases ho with
  | two P ha =>
    rw [two_content hP, if_neg ha, MvPolynomial.totalDegree_one] at hdeg
    omega
  | threeEndpoint P ha =>
    rw [three_content hP, if_pos ha, hgap 0] at hdeg
    omega
  | threeMiddle P ha hb hrs =>
    rw [three_content hP, if_neg ha, if_pos (Or.inl ⟨hb, hrs⟩), hgap 1] at hdeg
    omega
  | threeInterval P hu has =>
    have hr : P.g 0 < P.r 0 := P.g_lt_castSucc 0
    have hm := hP.thick 0 1 (by decide)
    change P.g 0 + P.g 1 < P.r 1 at hm
    have ha : P.r 0 ≠ q.val := by omega
    rw [three_content hP, if_neg ha, if_pos (Or.inr ⟨hu, has⟩), hgap 1] at hdeg
    omega
  | fourDouble P ha hc hst =>
    rw [four_content hP, if_pos ha, if_pos ⟨hc, hst⟩] at hdeg
    have hprod : (complete (P.g 0) * complete (P.g 1)).totalDegree = 2 := by
      rw [MvPolynomial.totalDegree_mul_of_isDomain
        ((complete_ne_zero_iff _).mpr (by positivity))
        ((complete_ne_zero_iff _).mpr (by positivity)), hgap 0, hgap 1]
    rw [hprod] at hdeg
    omega

/-- Uniform necessary-and-sufficient quadratic-origin table through four rows. -/
theorem quadratic_origins_iff {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (hn : n ≤ 3) :
    (canonicalPrimitive hP).totalDegree = 2 ↔ @QuadraticOrigin q n P :=
  ⟨quadratic_origin_of_degree_two hP hn, fun ho => ho.degree_two hP⟩

/-- The singleton linear origin retains only the singleton boundary T > q. -/
theorem canonical_singleton_linear {q : ℕ+} {P : Profile 0} (hP : QComponent q P) :
    canonicalPrimitive hP = complete (P.r 0) ∧ q.val < P.r 0 := by
  have hb : q.val < P.r 0 := by simpa [lastGap] using hP.bottom
  refine ⟨?_, hb⟩
  have hm := monicContent_mul_canonicalPrimitive hP
  rw [singleton_content hP, one_mul] at hm
  have hs : restriction q P = complete (P.r 0) := by
    unfold restriction
    rw [BetaDiagram.schur, Matrix.det_fin_one]
    change eraseGenerator q (complete (P.xi 0 - P.zeta 0)) = complete (P.r 0)
    rw [P.xi_sub_zeta, eraseGenerator_complete,
      if_neg (show (P.r 0 : ℤ) ≠ q.val by omega)]
  simpa only [pow_zero, one_mul, hs] using hm

/-- The M quadratic is irreducible on its full intrinsic domain.  In particular,
the additional bottom-boundary condition c > q + r is not needed. -/
theorem quadraticM_irreducible (q r a c : ℤ)
    (hr : 0 < r) (hq : 2 * r < q) (ha : r < a) (hc : r < c) :
    Irreducible (quadraticM q r a c) := by
  classical
  let R : ℕ+ := ⟨r.toNat, by omega⟩
  let V : ℕ+ := ⟨(a + c + q - 2 * r).toNat, by omega⟩
  let f : CompleteRing := -complete (a + q - r) * complete c -
    complete a * complete (c + q - r)
  have hR : (R.val : ℤ) = r := by dsimp [R]; omega
  have hV : (V.val : ℤ) = a + c + q - 2 * r := by dsimp [V]; omega
  have hgen (v : ℕ+) (k : ℤ) (hk : k ≠ (v.val : ℤ)) :
      v ∉ (complete k).vars := by
    rw [mem_vars_complete_iff]
    exact Ne.symm hk
  have hfvars (v : ℕ+)
      (hu : a + q - r ≠ (v.val : ℤ)) (hcv : c ≠ (v.val : ℤ))
      (hav : a ≠ (v.val : ℤ)) (hw : c + q - r ≠ (v.val : ℤ)) : v ∉ f.vars := by
    intro hm
    have hm' := MvPolynomial.vars_sub_subset (p := -complete (a + q - r) * complete c)
      (q := complete a * complete (c + q - r)) hm
    rcases Finset.mem_union.mp hm' with hm' | hm'
    · have hm'' := MvPolynomial.vars_mul _ _ hm'
      rcases Finset.mem_union.mp hm'' with hm'' | hm''
      · rw [MvPolynomial.vars_neg] at hm''
        exact hgen v _ hu hm''
      · exact hgen v _ hcv hm''
    · have hm'' := MvPolynomial.vars_mul _ _ hm'
      rcases Finset.mem_union.mp hm'' with hm'' | hm''
      · exact hgen v _ hav hm''
      · exact hgen v _ hw hm''
  have hRn : R ∉ f.vars := hfvars R (by omega) (by omega) (by omega) (by omega)
  have hVn : V ∉ f.vars := hfvars V (by omega) (by omega) (by omega) (by omega)
  have hn : f ≠ 0 := by
    intro hz
    have he := congrArg residualAugmentation hz
    dsimp [f] at he
    simp only [map_sub, map_mul, map_neg, map_zero,
      residualAugmentation_complete (show 0 < a + q - r by omega),
      residualAugmentation_complete (show 0 < c by omega),
      residualAugmentation_complete (show 0 < a by omega),
      residualAugmentation_complete (show 0 < c + q - r by omega)] at he
    norm_num at he
  have hnot : ¬ (MvPolynomial.X R : CompleteRing) ∣ f := by
    intro hd
    have hz := erase_eq_zero_of_X_dvd R f hd
    rw [eraseGenerator_eq_self R f hRn] at hz
    exact hn hz
  have hrel : IsRelPrime (complete r) f := by
    have he : complete r = (MvPolynomial.X R : CompleteRing) := by
      rw [← hR]
      exact complete_nat R
    rw [he]
    exact (MvPolynomial.X_prime (i := R)).irreducible.isRelPrime_iff_not_dvd.mpr hnot
  have hcoeff : V ∉ (complete r).vars := hgen V r (by omega)
  have he : quadraticM q r a c = complete r * MvPolynomial.X V + f := by
    have htop : complete (a + c + q - 2 * r) = (MvPolynomial.X V : CompleteRing) := by
      rw [← hV]
      exact complete_nat V
    unfold quadraticM
    rw [htop]
    dsimp [f]
    ring
  rw [he]
  exact MvPolynomial.irreducible_mul_X_add (complete r) f V
    ((complete_ne_zero_iff r).mpr hr.le) hcoeff hVn hrel

/-- The manuscript's untouched interval-index condition is equivalent to
no contact in the actual full array; the q-component domain supplies all lower entries. -/
theorem no_entry_contact_iff_upper {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) :
    NoEntryContact q P ↔
      ∀ i j : Fin (n + 1), i ≤ j → P.xi i - P.zeta j ≠ (q.val : ℤ) := by
  constructor
  · intro hc i j _
    exact hc i j
  · intro hc i j
    by_cases hij : i ≤ j
    · exact hc i j hij
    · by_cases hadj : j.val + 1 = i.val
      · let s : Fin n := ⟨j.val, by have := i.isLt; omega⟩
        have hi : i = s.succ := by ext; dsimp [s]; omega
        have hj : j = s.castSucc := by ext; rfl
        rw [hi, hj, P.xi_succ_sub_zeta_castSucc]
        exact_mod_cast hP.gap_ne s
      · have hn := hP.thick.hessenberg i j (by omega)
        have hqp : (0 : ℤ) < q.val := by exact_mod_cast q.pos
        omega

/-- If the first row survives, the second endpoint coefficient is nonzero.
At a tie the two contributions add, including a coefficient-two collision. -/
theorem four_second_coefficient_ne_zero {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) :
    MvPolynomial.pderiv (secondGenerator hP) (restriction q P) ≠ 0 := by
  classical
  have hb : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hbar (k : ℤ) (hk : 0 < k) (hne : k ≠ (q.val : ℤ)) :
      residualAugmentation (bar q k) = 1 := by
    rw [bar_eq_complete_of_ne q k hne]
    exact residualAugmentation_complete hk
  have hg0 := hbar (P.g 0) (by exact_mod_cast hP.gap_pos 0)
    (by exact_mod_cast hP.gap_ne 0)
  have hg1 := hbar (P.g 1) (by exact_mod_cast hP.gap_pos 1)
    (by exact_mod_cast hP.gap_ne 1)
  have hg2 := hbar (P.g 2) (by exact_mod_cast hP.gap_pos 2)
    (by exact_mod_cast hP.gap_ne 2)
  have hA := hbar (P.r 0) (by exact_mod_cast P.r_pos 0) (by exact_mod_cast ha)
  have hD := hbar (P.r 3) (by exact_mod_cast P.r_pos 3) (by omega)
  have hmax : prefixIndex P = secondIndex P ∨ suffixIndex P = secondIndex P := by
    rcases le_total (prefixIndex P) (suffixIndex P) with h | h
    · exact Or.inr (max_eq_right h).symm
    · exact Or.inl (max_eq_left h).symm
  intro hz
  have he := congrArg residualAugmentation hz
  rw [four_second_coefficient hP] at he
  simp only [map_add, map_zero] at he
  split_ifs at he <;>
    simp only [map_mul, map_zero, hg0, hg1, hg2, hA, hD, one_mul] at he
  all_goals try norm_num at he
  all_goals rcases hmax with h | h <;> contradiction

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/ThreeRowRigidity.lean
-- TODO-COPIED: skew-cofactor-independence/lean/SkewCofactorIndependence/NonnegativeRigidity.lean
theorem residual_triple_product_reading {a b c d e f : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (h : complete a * complete b * complete c = complete d * complete e * complete f) :
    FourRowHessenberg.tripleMatch a b c d e f := by
  have hi : Base.complete a * Base.complete b * Base.complete c =
      Base.complete d * Base.complete e * Base.complete f := by
    apply integerLift_injective
    simpa only [map_mul, complete] using h
  have hcast : ∀ x : ℤ, 0 < x → (x.toNat : ℤ) = x := fun x hx => by omega
  have hm : (([a.toNat, b.toNat, c.toNat] : List ℕ) : Multiset ℕ) =
      (([d.toNat, e.toNat, f.toNat] : List ℕ) : Multiset ℕ) := by
    apply (Base.prod_complete_eq_iff_of_pos _ _ (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> omega) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> omega)).mp
    simpa [hcast a ha, hcast b hb, hcast c hc, hcast d hd, hcast e he, hcast f hf,
      mul_assoc] using hi
  have hmem : a.toNat = d.toNat ∨ a.toNat = e.toNat ∨ a.toNat = f.toNat := by
    have hh : a.toNat ∈ (([a.toNat, b.toNat, c.toNat] : List ℕ) : Multiset ℕ) := by simp
    rw [hm] at hh
    simpa using hh
  have hpair {x y : ℤ} (hx : 0 < x) (hy : 0 < y)
      (hh : complete a * complete b * complete c = complete a * complete x * complete y) :
      (b = x ∧ c = y) ∨ (b = y ∧ c = x) := by
    apply complete_two_product_reading hb hc hx hy
    apply mul_left_cancel₀ ((complete_ne_zero_iff a).mpr ha.le)
    simpa only [mul_assoc] using hh
  rcases hmem with h₁ | h₁ | h₁
  · have h₁ : a = d := by omega
    subst d
    rcases hpair he hf h with ⟨hb', hc'⟩ | ⟨hb', hc'⟩
    · exact Or.inl ⟨rfl, hb', hc'⟩
    · exact Or.inr (Or.inl ⟨rfl, hb', hc'⟩)
  · have h₁ : a = e := by omega
    subst e
    rcases hpair hd hf (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)
      with ⟨hb', hc'⟩ | ⟨hb', hc'⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hb', hc'⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hb', hc'⟩)))
  · have h₁ : a = f := by omega
    subst f
    rcases hpair hd he (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)
      with ⟨hb', hc'⟩ | ⟨hb', hc'⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hb', hc'⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hb', hc'⟩))))

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/ThreeRowRigidity.lean
private theorem positive_triple_sum_reading {a b c d e f u v w x y z : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : complete a * complete b * complete c + complete d * complete e * complete f =
      complete u * complete v * complete w + complete x * complete y * complete z) :
    (FourRowHessenberg.tripleMatch a b c u v w ∧
      FourRowHessenberg.tripleMatch d e f x y z) ∨
      (FourRowHessenberg.tripleMatch a b c x y z ∧
        FourRowHessenberg.tripleMatch d e f u v w) := by
  let mon (i j k : ℤ) := hExp i.toNat + hExp j.toNat + hExp k.toNat
  have hm {i j k : ℤ} (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
      complete i * complete j * complete k = MvPolynomial.monomial (mon i j k) 1 := by
    rw [complete_eq_hh, complete_eq_hh, complete_eq_hh,
      hh_eq_monomial hi.le, hh_eq_monomial hj.le, hh_eq_monomial hk.le,
      MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial]
    simp only [mul_one, mon]
  have hh := h
  rw [hm ha hb hc, hm hd he hf, hm hu hv hw, hm hx hy hz] at hh
  rcases residual_monomial_pair_reading _ _ _ _ hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    constructor
    · apply residual_triple_product_reading ha hb hc hu hv hw
      rw [hm ha hb hc, hm hu hv hw, h1]
    · apply residual_triple_product_reading hd he hf hx hy hz
      rw [hm hd he hf, hm hx hy hz, h2]
  · right
    constructor
    · apply residual_triple_product_reading ha hb hc hx hy hz
      rw [hm ha hb hc, hm hx hy hz, h1]
    · apply residual_triple_product_reading hd he hf hu hv hw
      rw [hm hd he hf, hm hu hv hw, h2]

/-- The actual three-row restriction with its sole middle row contacted. -/
noncomputable def middleContactCubic (q a c r s : ℤ) : CompleteRing :=
  -complete r * complete (a + q - r) * complete c -
    complete s * complete a * complete (q + c - s) +
    complete r * complete s * complete (a + q + c - r - s)

theorem middleContactCubic_top (q a c r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (hq : r + s < q)
    (ha : r < a) (hc : q + s < c) (v : ℕ+)
    (hv : (v.val : ℤ) = a + q + c - r - s) :
    MvPolynomial.pderiv v (middleContactCubic q a c r s) = complete r * complete s := by
  simp only [middleContactCubic, map_add, map_sub, map_neg, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, hv, if_pos rfl, ite_true, ite_false,
    if_neg (show r ≠ a + q + c - r - s by omega),
    if_neg (show s ≠ a + q + c - r - s by omega),
    if_neg (show a + q - r ≠ a + q + c - r - s by omega),
    if_neg (show c ≠ a + q + c - r - s by omega),
    if_neg (show a ≠ a + q + c - r - s by omega),
    if_neg (show q + c - s ≠ a + q + c - r - s by omega)]
  ring

theorem middleContactCubic_above (q a c r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (hq : r + s < q)
    (ha : r < a) (hc : q + s < c) (v : ℕ+)
    (hv : a + q + c - r - s < (v.val : ℤ)) :
    MvPolynomial.pderiv v (middleContactCubic q a c r s) = 0 := by
  simp only [middleContactCubic, map_add, map_sub, map_neg, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, if_neg (show r ≠ (v.val : ℤ) by omega),
    if_neg (show s ≠ (v.val : ℤ) by omega),
    if_neg (show a + q - r ≠ (v.val : ℤ) by omega),
    if_neg (show c ≠ (v.val : ℤ) by omega),
    if_neg (show a ≠ (v.val : ℤ) by omega),
    if_neg (show q + c - s ≠ (v.val : ℤ) by omega),
    if_neg (show a + q + c - r - s ≠ (v.val : ℤ) by omega)]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- Independent middle-contact cubic comparison, including every triple-factor
coincidence and the equal-gap quadratic-content limit. -/
theorem middleContactCubic_rigidity (q a c r s A C R S : ℤ)
    (hr : 0 < r) (hs : 0 < s) (hq : r + s < q) (ha : r < a) (hc : q + s < c)
    (hR : 0 < R) (hS : 0 < S) (hQ : R + S < q) (hA : R < A) (hC : q + S < C)
    (he : middleContactCubic q a c r s = middleContactCubic q A C R S) :
    (a = A ∧ c = C ∧ r = R ∧ s = S) ∨
      (a = C ∧ c = A ∧ r = S ∧ s = R) := by
  have ht := private_top_reading _ _ (a + q + c - r - s) (A + q + C - R - S)
    (complete r * complete s) (complete R * complete S)
    (by omega) (by omega)
    (mul_ne_zero ((complete_ne_zero_iff r).mpr hr.le) ((complete_ne_zero_iff s).mpr hs.le))
    (mul_ne_zero ((complete_ne_zero_iff R).mpr hR.le) ((complete_ne_zero_iff S).mpr hS.le))
    (middleContactCubic_top q a c r s hr hs hq ha hc)
    (middleContactCubic_top q A C R S hR hS hQ hA hC)
    (middleContactCubic_above q a c r s hr hs hq ha hc)
    (middleContactCubic_above q A C R S hR hS hQ hA hC) he
  have hg := complete_two_product_reading hr hs hR hS ht.2
  have hneg : complete r * complete (a + q - r) * complete c +
      complete s * complete a * complete (q + c - s) =
    complete R * complete (A + q - R) * complete C +
      complete S * complete A * complete (q + C - S) := by
    unfold middleContactCubic at he
    rw [ht.1] at he
    have hlead := congrArg (fun p : CompleteRing => p * complete (A + q + C - R - S)) ht.2
    linear_combination -he + hlead
  have hmon := positive_triple_sum_reading hr (by omega) (by omega)
    hs (by omega) (by omega) hR (by omega) (by omega)
    hS (by omega) (by omega) hneg
  rcases hg with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩ <;>
    rcases hmon with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩ <;>
    unfold FourRowHessenberg.tripleMatch at hm1 hm2 <;>
    rcases hm1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases hm2 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- The actual three-row restriction when the first merged interval is contacted. -/
noncomputable def intervalContactCubic (q a b c r s : ℤ) : CompleteRing :=
  complete a * complete b * complete c -
    complete s * complete a * complete (b + c - s) +
    complete r * complete s * complete (q + c - s)

theorem intervalContactCubic_top (q a b c r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ha : r < a) (hb : r + s < b)
    (hc : q + s < c) (hu : a + b - r = q)
    (v : ℕ+) (hv : (v.val : ℤ) = q + c - s) :
    MvPolynomial.pderiv v (intervalContactCubic q a b c r s) = complete r * complete s := by
  simp only [intervalContactCubic, map_add, map_sub, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, hv, if_pos rfl, ite_true, ite_false,
    if_neg (show a ≠ q + c - s by omega),
    if_neg (show b ≠ q + c - s by omega),
    if_neg (show c ≠ q + c - s by omega),
    if_neg (show s ≠ q + c - s by omega),
    if_neg (show r ≠ q + c - s by omega),
    if_neg (show b + c - s ≠ q + c - s by omega)]
  ring

theorem intervalContactCubic_above (q a b c r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ha : r < a) (hb : r + s < b)
    (hc : q + s < c) (hu : a + b - r = q)
    (v : ℕ+) (hv : q + c - s < (v.val : ℤ)) :
    MvPolynomial.pderiv v (intervalContactCubic q a b c r s) = 0 := by
  simp only [intervalContactCubic, map_add, map_sub, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, if_neg (show a ≠ (v.val : ℤ) by omega),
    if_neg (show b ≠ (v.val : ℤ) by omega),
    if_neg (show c ≠ (v.val : ℤ) by omega),
    if_neg (show s ≠ (v.val : ℤ) by omega),
    if_neg (show r ≠ (v.val : ℤ) by omega),
    if_neg (show b + c - s ≠ (v.val : ℤ) by omega),
    if_neg (show q + c - s ≠ (v.val : ℤ) by omega)]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- Independent interval-contact cubic comparison.  Its surviving diagonal and
negative monomial recover the ordered first row, including repeated factors. -/
theorem intervalContactCubic_rigidity (q a b c r s A B C R S : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ha : r < a) (hb : r + s < b)
    (hc : q + s < c) (hu : a + b - r = q) (has : a ≠ s)
    (hR : 0 < R) (hS : 0 < S) (hA : R < A) (hB : R + S < B)
    (hC : q + S < C) (hU : A + B - R = q) (hAS : A ≠ S)
    (he : intervalContactCubic q a b c r s = intervalContactCubic q A B C R S) :
    a = A ∧ b = B ∧ c = C ∧ r = R ∧ s = S := by
  have ht := private_top_reading _ _ (q + c - s) (q + C - S)
    (complete r * complete s) (complete R * complete S)
    (by omega) (by omega)
    (mul_ne_zero ((complete_ne_zero_iff r).mpr hr.le) ((complete_ne_zero_iff s).mpr hs.le))
    (mul_ne_zero ((complete_ne_zero_iff R).mpr hR.le) ((complete_ne_zero_iff S).mpr hS.le))
    (intervalContactCubic_top q a b c r s hr hs ha hb hc hu)
    (intervalContactCubic_top q A B C R S hR hS hA hB hC hU)
    (intervalContactCubic_above q a b c r s hr hs ha hb hc hu)
    (intervalContactCubic_above q A B C R S hR hS hA hB hC hU) he
  have hg := complete_two_product_reading hr hs hR hS ht.2
  have hsum : complete a * complete b * complete c +
      complete S * complete A * complete (B + C - S) =
    complete A * complete B * complete C +
      complete s * complete a * complete (b + c - s) := by
    unfold intervalContactCubic at he
    rw [ht.1] at he
    have hlead := congrArg (fun p : CompleteRing => p * complete (q + C - S)) ht.2
    linear_combination he - hlead
  have hmon := positive_triple_sum_reading (by omega) (by omega) (by omega)
    hS (by omega) (by omega) (by omega) (by omega) (by omega)
    hs (by omega) (by omega) hsum
  rcases hg with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩ <;>
    rcases hmon with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩ <;>
    unfold FourRowHessenberg.tripleMatch at hm1 hm2 <;>
    rcases hm1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases hm2 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

theorem middleContactCubic_augmentation (q a c r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (hq : r + s < q) (ha : r < a) (hc : q + s < c) :
    residualAugmentation (middleContactCubic q a c r s) = -1 := by
  simp only [middleContactCubic, map_add, map_sub, map_mul, map_neg,
    residualAugmentation_complete hr, residualAugmentation_complete hs,
    residualAugmentation_complete (show 0 < a + q - r by omega),
    residualAugmentation_complete (show 0 < c by omega),
    residualAugmentation_complete (show 0 < a by omega),
    residualAugmentation_complete (show 0 < q + c - s by omega),
    residualAugmentation_complete (show 0 < a + q + c - r - s by omega)]
  norm_num

theorem intervalContactCubic_augmentation (q a b c r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ha : r < a) (hb : r + s < b)
    (hc : q + s < c) (hu : a + b - r = q) :
    residualAugmentation (intervalContactCubic q a b c r s) = 1 := by
  simp only [intervalContactCubic, map_add, map_sub, map_mul,
    residualAugmentation_complete hr, residualAugmentation_complete hs,
    residualAugmentation_complete (show 0 < a by omega),
    residualAugmentation_complete (show 0 < b by omega),
    residualAugmentation_complete (show 0 < c by omega),
    residualAugmentation_complete (show 0 < b + c - s by omega),
    residualAugmentation_complete (show 0 < q + c - s by omega)]
  norm_num

theorem canonical_three_middle_cubic {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) (hb : P.r 1 = q.val)
    (hrs : P.g 0 ≠ P.g 1) :
    canonicalPrimitive hP =
      middleContactCubic q.val (P.r 0) (P.r 2) (P.g 0) (P.g 1) := by
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hend : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := by omega
  have hcon : monicContent hP = 1 := by
    rw [three_content hP, if_neg ha]
    have hnot : ¬ ((P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
        ((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 0 = P.g 1)) := by
      rintro (h | h)
      · exact hrs h.2
      · exact hu h.1
    rw [if_neg hnot]
  have hm := monicContent_mul_canonicalPrimitive hP
  rw [hcon, one_mul] at hm
  norm_num at hm
  rw [hm, restriction_three_expansion q P hP.thick]
  simp only [threeInterval, hb, bar_cut, mul_zero, zero_mul, zero_sub]
  rw [bar_eq_complete_of_ne q (P.r 0) (by exact_mod_cast ha),
    bar_eq_complete_of_ne q (P.r 2) (by omega),
    bar_eq_complete_of_ne q ((P.r 0 : ℤ) + q.val - P.g 0) (by omega),
    bar_eq_complete_of_ne q ((q.val : ℤ) + P.r 2 - P.g 1) (by omega),
    bar_eq_complete_of_ne q
      ((P.r 0 : ℤ) + q.val + P.r 2 - P.g 0 - P.g 1) (by omega),
    bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1)]
  unfold middleContactCubic
  ring

theorem canonical_three_interval_cubic {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) (has : P.r 0 ≠ P.g 1) :
    canonicalPrimitive hP =
      intervalContactCubic q.val (P.r 0) (P.r 1) (P.r 2) (P.g 0) (P.g 1) := by
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hend : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have ha : P.r 0 ≠ q.val := by omega
  have hb : P.r 1 ≠ q.val := by omega
  have hcon : monicContent hP = 1 := by
    rw [three_content hP, if_neg ha]
    simp [hb, has]
  have hm := monicContent_mul_canonicalPrimitive hP
  rw [hcon, one_mul] at hm
  norm_num at hm
  rw [hm, restriction_three_expansion q P hP.thick]
  simp only [threeInterval, hu, bar_cut, mul_zero, zero_mul, sub_zero]
  rw [bar_eq_complete_of_ne q (P.r 0) (by omega),
    bar_eq_complete_of_ne q (P.r 1) (by omega),
    bar_eq_complete_of_ne q (P.r 2) (by omega),
    bar_eq_complete_of_ne q ((P.r 1 : ℤ) + P.r 2 - P.g 1) (by omega),
    bar_eq_complete_of_ne q
      ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) (by omega),
    bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1)]
  have hT : (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 =
      (q.val : ℤ) + P.r 2 - P.g 1 := by omega
  rw [hT]
  unfold intervalContactCubic
  ring

/-- Cubic degree through three rows proves all the nonextraction conditions. -/
theorem three_cubic_nonextraction {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (hd : (canonicalPrimitive hP).totalDegree = 3) :
    monicContent hP = 1 ∧ P.r 0 ≠ q.val ∧
      (P.r 1 = q.val → P.g 0 ≠ P.g 1) ∧
      ((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val → P.r 0 ≠ P.g 1) := by
  have hdeg := content_degree_add_canonical_degree hP
  rw [hd] at hdeg
  have hgap (j : Fin 2) : (complete (P.g j)).totalDegree = 1 :=
    totalDegree_complete_pos _ (by exact_mod_cast hP.gap_pos j)
  have ha : P.r 0 ≠ q.val := by
    intro ha
    rw [three_content hP, if_pos ha, hgap 0] at hdeg
    omega
  have hcontact : ¬ ((P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
      ((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 0 = P.g 1)) := by
    intro h
    rw [three_content hP, if_neg ha, if_pos h, hgap 1] at hdeg
    omega
  refine ⟨?_, ha, ?_, ?_⟩
  · rw [three_content hP, if_neg ha, if_neg hcontact]
  · intro hb hrs
    exact hcontact (Or.inl ⟨hb, hrs⟩)
  · intro hu has
    exact hcontact (Or.inr ⟨hu, has⟩)

theorem three_no_contact_of_first_indices {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) (hb : P.r 1 ≠ q.val)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val) : NoEntryContact q P := by
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hra := P.g_lt_castSucc 0
  have hsb := P.g_lt_castSucc 1
  have hc : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hrq : (P.g 0 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 0
  have hsq : (P.g 1 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 1
  intro i j
  change (Matrix.of (fun i j : Fin 3 => P.xi i - P.zeta j)) i j ≠ (q.val : ℤ)
  rw [indices_three P]
  fin_cases i <;> fin_cases j <;> norm_num <;> omega

/-- The three possible cubic contact types are produced from actual degree. -/
theorem three_cubic_contact_cases {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (hd : (canonicalPrimitive hP).totalDegree = 3) :
    NoEntryContact q P ∨
      (P.r 0 ≠ q.val ∧ P.r 1 = q.val ∧ P.g 0 ≠ P.g 1) ∨
      ((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 0 ≠ P.g 1) := by
  obtain ⟨hcon, ha, hmiddle, hinterval⟩ := three_cubic_nonextraction hP hd
  by_cases hb : P.r 1 = q.val
  · exact Or.inr (Or.inl ⟨ha, hb, hmiddle hb⟩)
  · by_cases hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val
    · exact Or.inr (Or.inr ⟨hu, hinterval hu⟩)
    · exact Or.inl (three_no_contact_of_first_indices hP ha hb hu)

/-- Three-row actual full functions have augmentation zero. -/
theorem component_three_full_augmentation {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) : residualAugmentation P.toBetaDiagram.schur = 0 := by
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hra := P.g_lt_castSucc 0
  have hsb := P.g_lt_castSucc 1
  have hrow (i : Fin 3) : (0 : ℤ) < P.r i := by exact_mod_cast P.r_pos i
  have hgap (j : Fin 2) : (0 : ℤ) < P.g j := by exact_mod_cast hP.gap_pos j
  have hi := indices_three P
  have hu : P.xi 0 - P.zeta 1 = (P.r 0 : ℤ) + P.r 1 - P.g 0 :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 0 1) hi
  have hv : P.xi 1 - P.zeta 2 = (P.r 1 : ℤ) + P.r 2 - P.g 1 :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 1 2) hi
  have hl : P.xi 2 - P.zeta 0 = (P.g 0 : ℤ) + P.g 1 - P.r 1 :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 2 0) hi
  have hn : complete (P.xi 2 - P.zeta 0) = 0 := by
    rw [hl]
    apply complete_of_neg
    omega
  have ht : P.xi 0 - P.zeta 2 = (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 0 2) hi
  have hg0 : P.xi 1 - P.zeta 0 = (P.g 0 : ℤ) :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 1 0) hi
  have hg1 : P.xi 2 - P.zeta 1 = (P.g 1 : ℤ) :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 2 1) hi
  rw [BetaDiagram.schur_three_expansion]
  simp only [Profile.toBetaDiagram, BetaDiagram.rowLength, P.xi_sub_zeta,
    hg0, hg1, hu, hv, ht, hn, mul_zero, sub_zero, add_zero,
    map_add, map_sub, map_mul, residualAugmentation_complete (hrow 0),
    residualAugmentation_complete (hrow 1), residualAugmentation_complete (hrow 2),
    residualAugmentation_complete (hgap 0), residualAugmentation_complete (hgap 1),
    residualAugmentation_complete (show 0 < (P.r 0 : ℤ) + P.r 1 - P.g 0 by omega),
    residualAugmentation_complete (show 0 < (P.r 1 : ℤ) + P.r 2 - P.g 1 by omega),
    residualAugmentation_complete
      (show 0 < (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 by omega)]
  norm_num

theorem three_cubic_untouched_augmentation {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (hd : (canonicalPrimitive hP).totalDegree = 3)
    (hc : NoEntryContact q P) : residualAugmentation (canonicalPrimitive hP) = 0 := by
  obtain ⟨hcon, _, _, _⟩ := three_cubic_nonextraction hP hd
  have hm := monicContent_mul_canonicalPrimitive hP
  rw [hcon, one_mul, restriction_eq_full_of_no_entry_contact hc] at hm
  norm_num at hm
  rw [hm]
  exact component_three_full_augmentation hP

theorem three_cubic_middle_augmentation {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hb : P.r 1 = q.val) (hrs : P.g 0 ≠ P.g 1) :
    residualAugmentation (canonicalPrimitive hP) = -1 := by
  rw [canonical_three_middle_cubic hP ha hb hrs]
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  exact middleContactCubic_augmentation _ _ _ _ _
    (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
    (by omega) (by exact_mod_cast P.g_lt_castSucc 0) (by exact_mod_cast hbottom)

theorem three_cubic_interval_augmentation {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) (has : P.r 0 ≠ P.g 1) :
    residualAugmentation (canonicalPrimitive hP) = 1 := by
  rw [canonical_three_interval_cubic hP hu has]
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  exact intervalContactCubic_augmentation _ _ _ _ _ _
    (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
    (by exact_mod_cast P.g_lt_castSucc 0) (by exact_mod_cast hmid)
    (by exact_mod_cast hbottom) hu

theorem three_middle_cubic_profile_rigidity {q : ℕ+} {P Q : Profile 2}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 ≠ q.val) (hb : P.r 1 = q.val) (hrs : P.g 0 ≠ P.g 1)
    (hA : Q.r 0 ≠ q.val) (hB : Q.r 1 = q.val) (hRS : Q.g 0 ≠ Q.g 1)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ) : P = Q ∨ P = Q.rotate := by
  rw [canonical_three_middle_cubic hP ha hb hrs,
    canonical_three_middle_cubic hQ hA hB hRS] at he
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hMID := hQ.thick 0 1 (by decide)
  change Q.g 0 + Q.g 1 < Q.r 1 at hMID
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hBOTTOM : q.val + Q.g 1 < Q.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  have hraw := middleContactCubic_rigidity q.val (P.r 0) (P.r 2) (P.g 0) (P.g 1)
    (Q.r 0) (Q.r 2) (Q.g 0) (Q.g 1)
    (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
    (by omega) (by exact_mod_cast P.g_lt_castSucc 0) (by exact_mod_cast hbottom)
    (by exact_mod_cast hQ.gap_pos 0) (by exact_mod_cast hQ.gap_pos 1)
    (by omega) (by exact_mod_cast Q.g_lt_castSucc 0) (by exact_mod_cast hBOTTOM)
    he
  rcases hraw with ⟨hrow0, hrow2, hgap0, hgap1⟩ | ⟨hrow0, hrow2, hgap0, hgap1⟩
  · have hr0 : P.r 0 = Q.r 0 := by exact_mod_cast hrow0
    have hr2 : P.r 2 = Q.r 2 := by exact_mod_cast hrow2
    have hg0 : P.g 0 = Q.g 0 := by exact_mod_cast hgap0
    have hg1 : P.g 1 = Q.g 1 := by exact_mod_cast hgap1
    left
    apply Profile.ext
    · funext i; fin_cases i <;> simp_all
    · funext j; fin_cases j <;> simp_all
  · have hr0 : P.r 0 = Q.r 2 := by exact_mod_cast hrow0
    have hr2 : P.r 2 = Q.r 0 := by exact_mod_cast hrow2
    have hg0 : P.g 0 = Q.g 1 := by exact_mod_cast hgap0
    have hg1 : P.g 1 = Q.g 0 := by exact_mod_cast hgap1
    right
    apply Profile.ext
    · funext i; fin_cases i <;> simp_all [Profile.rotate]
    · funext j; fin_cases j <;> simp_all [Profile.rotate]

theorem three_interval_cubic_profile_rigidity {q : ℕ+} {P Q : Profile 2}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) (has : P.r 0 ≠ P.g 1)
    (hU : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 = q.val) (hAS : Q.r 0 ≠ Q.g 1)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ) : P = Q := by
  rw [canonical_three_interval_cubic hP hu has,
    canonical_three_interval_cubic hQ hU hAS] at he
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hMID := hQ.thick 0 1 (by decide)
  change Q.g 0 + Q.g 1 < Q.r 1 at hMID
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hBOTTOM : q.val + Q.g 1 < Q.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  obtain ⟨hrow0, hrow1, hrow2, hgap0, hgap1⟩ :=
    intervalContactCubic_rigidity q.val (P.r 0) (P.r 1) (P.r 2) (P.g 0) (P.g 1)
      (Q.r 0) (Q.r 1) (Q.r 2) (Q.g 0) (Q.g 1)
      (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
      (by exact_mod_cast P.g_lt_castSucc 0) (by exact_mod_cast hmid)
      (by exact_mod_cast hbottom) hu (by exact_mod_cast has)
      (by exact_mod_cast hQ.gap_pos 0) (by exact_mod_cast hQ.gap_pos 1)
      (by exact_mod_cast Q.g_lt_castSucc 0) (by exact_mod_cast hMID)
      (by exact_mod_cast hBOTTOM) hU (by exact_mod_cast hAS) he
  have hr0 : P.r 0 = Q.r 0 := by exact_mod_cast hrow0
  have hr1 : P.r 1 = Q.r 1 := by exact_mod_cast hrow1
  have hr2 : P.r 2 = Q.r 2 := by exact_mod_cast hrow2
  have hg0 : P.g 0 = Q.g 0 := by exact_mod_cast hgap0
  have hg1 : P.g 1 = Q.g 1 := by exact_mod_cast hgap1
  apply Profile.ext
  · funext i; fin_cases i <;> simp_all
  · funext j; fin_cases j <;> simp_all

/-- Full primitive-three-row cubic rigidity, with all contact types produced
from actual canonical degree and no matching premise supplied by a caller. -/
theorem three_primitive_cubic_rigidity {q : ℕ+} {P Q : Profile 2}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hdP : (canonicalPrimitive hP).totalDegree = 3)
    (hdQ : (canonicalPrimitive hQ).totalDegree = 3)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ) : P = Q ∨ P = Q.rotate := by
  have haug := congrArg residualAugmentation he
  rcases three_cubic_contact_cases hP hdP with hfreeP | ⟨ha, hb, hrs⟩ | ⟨hu, has⟩
  · rcases three_cubic_contact_cases hQ hdQ with hfreeQ | ⟨hA, hB, hRS⟩ | ⟨hU, hAS⟩
    · obtain ⟨hconP, _, _, _⟩ := three_cubic_nonextraction hP hdP
      obtain ⟨hconQ, _, _, _⟩ := three_cubic_nonextraction hQ hdQ
      have hp := monicContent_mul_canonicalPrimitive hP
      have hq := monicContent_mul_canonicalPrimitive hQ
      rw [hconP, one_mul, restriction_eq_full_of_no_entry_contact hfreeP] at hp
      rw [hconQ, one_mul, restriction_eq_full_of_no_entry_contact hfreeQ] at hq
      norm_num at hp hq
      have hfull : P.schur = Q.schur := by
        rw [← Profile.toBetaDiagram_schur, ← Profile.toBetaDiagram_schur, ← hp, ← hq]
        exact he
      exact FourRowHessenberg.small_profile_rigidity P Q (by decide) hfull
    · rw [three_cubic_untouched_augmentation hP hdP hfreeP,
        three_cubic_middle_augmentation hQ hA hB hRS] at haug
      norm_num at haug
    · rw [three_cubic_untouched_augmentation hP hdP hfreeP,
        three_cubic_interval_augmentation hQ hU hAS] at haug
      norm_num at haug
  · rcases three_cubic_contact_cases hQ hdQ with hfreeQ | ⟨hA, hB, hRS⟩ | ⟨hU, hAS⟩
    · rw [three_cubic_middle_augmentation hP ha hb hrs,
        three_cubic_untouched_augmentation hQ hdQ hfreeQ] at haug
      norm_num at haug
    · exact three_middle_cubic_profile_rigidity hP hQ ha hb hrs hA hB hRS he
    · rw [three_cubic_middle_augmentation hP ha hb hrs,
        three_cubic_interval_augmentation hQ hU hAS] at haug
      norm_num at haug
  · rcases three_cubic_contact_cases hQ hdQ with hfreeQ | ⟨hA, hB, hRS⟩ | ⟨hU, hAS⟩
    · rw [three_cubic_interval_augmentation hP hu has,
        three_cubic_untouched_augmentation hQ hdQ hfreeQ] at haug
      norm_num at haug
    · rw [three_cubic_interval_augmentation hP hu has,
        three_cubic_middle_augmentation hQ hA hB hRS] at haug
      norm_num at haug
    · exact Or.inl (three_interval_cubic_profile_rigidity hP hQ hu has hU hAS he)

/-- The binomial B is primitive and affine in its private largest generator. -/
theorem quadraticB_irreducible (r a c : ℤ)
    (hr : 0 < r) (ha : r < a) (hc : r < c) : Irreducible (quadraticB r a c) := by
  classical
  let R : ℕ+ := ⟨r.toNat, by omega⟩
  let V : ℕ+ := ⟨(a + c - r).toNat, by omega⟩
  let f : CompleteRing := -(complete a * complete c)
  have hR : (R.val : ℤ) = r := by dsimp [R]; omega
  have hV : (V.val : ℤ) = a + c - r := by dsimp [V]; omega
  have hgen (v : ℕ+) (k : ℤ) (hk : k ≠ (v.val : ℤ)) :
      v ∉ (complete k).vars := by rw [mem_vars_complete_iff]; exact Ne.symm hk
  have hfn : V ∉ f.vars := by
    intro h
    have hh : V ∈ (complete a * complete c).vars := by
      simpa only [f, MvPolynomial.vars_neg] using h
    rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hh) with h | h
    · exact hgen V a (by omega) h
    · exact hgen V c (by omega) h
  have hnot : ¬ (MvPolynomial.X R : CompleteRing) ∣ f := by
    intro hd
    have hz := erase_eq_zero_of_X_dvd R f hd
    dsimp [f] at hz
    rw [map_neg, map_mul, eraseGenerator_complete, eraseGenerator_complete,
      if_neg (show a ≠ (R.val : ℤ) by omega),
      if_neg (show c ≠ (R.val : ℤ) by omega)] at hz
    exact neg_ne_zero.mpr
      (mul_ne_zero ((complete_ne_zero_iff a).mpr (by omega))
        ((complete_ne_zero_iff c).mpr (by omega))) hz
  have hcoeff : complete r = (MvPolynomial.X R : CompleteRing) := by
    rw [← hR]; exact complete_nat R
  have hrel : IsRelPrime (complete r) f := by
    rw [hcoeff]
    exact (MvPolynomial.X_prime (i := R)).irreducible.isRelPrime_iff_not_dvd.mpr hnot
  have htop : complete (a + c - r) = (MvPolynomial.X V : CompleteRing) := by
    rw [← hV]; exact complete_nat V
  have he : quadraticB r a c = complete r * MvPolynomial.X V + f := by
    unfold quadraticB
    rw [htop]
    dsimp [f]
    ring
  rw [he]
  exact MvPolynomial.irreducible_mul_X_add (complete r) f V
    ((complete_ne_zero_iff r).mpr hr.le) (hgen V r (by omega)) hfn hrel

theorem quadraticB_degree_two (r a c : ℤ) (hr : 0 < r) (ha : r < a) (hc : r < c) :
    (quadraticB r a c).totalDegree = 2 := by
  have h (k : ℤ) (hk : 0 < k) : (complete k).IsHomogeneous 1 := by
    exact complete_pos_homogeneous k hk
  have hf : (quadraticB r a c).IsHomogeneous 2 := by
    exact (h r hr |>.mul (h (a + c - r) (by omega))).sub
      (h a (by omega) |>.mul (h c (by omega)))
  exact hf.totalDegree (quadraticB_irreducible r a c hr ha hc).ne_zero

private theorem variable_not_dvd_irreducible_degree_two (f : CompleteRing)
    (hf : Irreducible f) (hd : f.totalDegree = 2) (v : ℕ+) :
    ¬ (MvPolynomial.X v : CompleteRing) ∣ f := by
  intro hv
  have hass := (MvPolynomial.X_prime (i := v)).irreducible.associated_of_dvd hf hv
  obtain ⟨k, hk⟩ := hass.symm.dvd
  have hkn : k ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hk
    exact MvPolynomial.X_ne_zero v hk
  have hdegree := congrArg MvPolynomial.totalDegree hk
  rw [MvPolynomial.totalDegree_X,
    MvPolynomial.totalDegree_mul_of_isDomain hf.ne_zero hkn, hd] at hdegree
  omega

/-- A variable times B recovers its linear origin without a no-collision
assumption on that variable and the two rows or the gap. -/
theorem variable_times_B_reading (b r a c B R A C : ℤ)
    (hb : 0 < b) (hB : 0 < B) (hr : 0 < r) (ha : r < a) (hc : r < c)
    (hR : 0 < R) (hA : R < A) (hC : R < C)
    (he : complete b * quadraticB r a c = complete B * quadraticB R A C) :
    b = B ∧ r = R ∧ ((a = A ∧ c = C) ∨ (a = C ∧ c = A)) := by
  let v : ℕ+ := ⟨b.toNat, by omega⟩
  let w : ℕ+ := ⟨B.toNat, by omega⟩
  have hv : (v.val : ℤ) = b := by dsimp [v]; omega
  have hw : (w.val : ℤ) = B := by dsimp [w]; omega
  have hbv : complete b = (MvPolynomial.X v : CompleteRing) := by
    rw [← hv]; exact complete_nat v
  have hBw : complete B = (MvPolynomial.X w : CompleteRing) := by
    rw [← hw]; exact complete_nat w
  have hd : (MvPolynomial.X v : CompleteRing) ∣ complete B * quadraticB R A C := by
    rw [← he, hbv]
    exact dvd_mul_right _ _
  have hdiv := (MvPolynomial.X_prime (i := v)).dvd_mul.mp hd
  have hbb : b = B := by
    rcases hdiv with hdiv | hdiv
    · rw [hBw, MvPolynomial.X_dvd_X] at hdiv
      have hh := congrArg (fun z : ℕ+ => (z.val : ℤ)) hdiv
      rw [hv, hw] at hh
      exact hh
    · exact (variable_not_dvd_irreducible_degree_two _ (quadraticB_irreducible R A C hR hA hC)
        (quadraticB_degree_two R A C hR hA hC) v hdiv).elim
  refine ⟨hbb, ?_⟩
  have hpoly : quadraticB r a c = quadraticB R A C := by
    rw [hbb] at he
    exact mul_left_cancel₀ ((complete_ne_zero_iff B).mpr hB.le) he
  exact (quadraticB_eq_iff r a c R A C hr ha hc hR hA hC).mp hpoly

/-- The UC first-coefficient comparison recovers the large endpoint and both
gap factors, independently of the order of the two small rows. -/
theorem uc_first_coefficient_reading {q : ℕ+} {a b r t d A B R T D : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (ht : 0 < t)
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) (hT : 0 < T)
    (haq : a < (q.val : ℤ)) (hbq : b < (q.val : ℤ)) (hrq : r < (q.val : ℤ))
    (htq : t < (q.val : ℤ))
    (hAq : A < (q.val : ℤ)) (hBq : B < (q.val : ℤ)) (hRq : R < (q.val : ℤ))
    (hTq : T < (q.val : ℤ))
    (hd : (q.val : ℤ) + t < d) (hD : (q.val : ℤ) + T < D)
    (he : complete a * complete b * complete d +
        complete r * complete t * complete ((q.val : ℤ) + d - t) =
      complete A * complete B * complete D +
        complete R * complete T * complete ((q.val : ℤ) + D - T)) :
    d = D ∧ t = T ∧ r = R := by
  let F (a b d r t : ℤ) : CompleteRing :=
    complete a * complete b * complete d +
      complete r * complete t * complete ((q.val : ℤ) + d - t)
  have htop (a b d r t : ℤ) (ha : a < (q.val : ℤ)) (hb : b < (q.val : ℤ))
      (hr : r < (q.val : ℤ)) (ht : t < (q.val : ℤ))
      (hp : 0 < t) (hd : (q.val : ℤ) + t < d) (v : ℕ+)
      (hv : (v.val : ℤ) = (q.val : ℤ) + d - t) :
      MvPolynomial.pderiv v (F a b d r t) = complete r * complete t := by
    dsimp [F]
    simp [MvPolynomial.pderiv_mul, residual_pderiv_complete, hv,
      show a ≠ (q.val : ℤ) + d - t by omega,
      show b ≠ (q.val : ℤ) + d - t by omega,
      show d ≠ (q.val : ℤ) + d - t by omega,
      show r ≠ (q.val : ℤ) + d - t by omega,
      show t ≠ (q.val : ℤ) + d - t by omega]
  have habove (a b d r t : ℤ) (ha : a < (q.val : ℤ)) (hb : b < (q.val : ℤ))
      (hr : r < (q.val : ℤ)) (ht : t < (q.val : ℤ))
      (hp : 0 < t) (hd : (q.val : ℤ) + t < d) (v : ℕ+)
      (hv : (q.val : ℤ) + d - t < (v.val : ℤ)) :
      MvPolynomial.pderiv v (F a b d r t) = 0 := by
    dsimp [F]
    simp [MvPolynomial.pderiv_mul, residual_pderiv_complete,
      show a ≠ (v.val : ℤ) by omega, show b ≠ (v.val : ℤ) by omega,
      show d ≠ (v.val : ℤ) by omega, show r ≠ (v.val : ℤ) by omega,
      show t ≠ (v.val : ℤ) by omega,
      show (q.val : ℤ) + d - t ≠ (v.val : ℤ) by omega]
  have hp := private_top_reading (F a b d r t) (F A B D R T)
    ((q.val : ℤ) + d - t) ((q.val : ℤ) + D - T)
    (complete r * complete t) (complete R * complete T)
    (by omega) (by omega)
    (mul_ne_zero ((complete_ne_zero_iff r).mpr hr.le) ((complete_ne_zero_iff t).mpr ht.le))
    (mul_ne_zero ((complete_ne_zero_iff R).mpr hR.le) ((complete_ne_zero_iff T).mpr hT.le))
    (htop a b d r t haq hbq hrq htq ht hd)
    (htop A B D R T hAq hBq hRq hTq hT hD)
    (habove a b d r t haq hbq hrq htq ht hd)
    (habove A B D R T hAq hBq hRq hTq hT hD) he
  have hdiag : complete a * complete b * complete d = complete A * complete B * complete D := by
    rw [hp.1] at he
    have hl := congrArg (fun p : CompleteRing => p * complete ((q.val : ℤ) + D - T)) hp.2
    linear_combination he - hl
  have hrows := residual_triple_product_reading ha hb (by omega) hA hB (by omega) hdiag
  have hdD : d = D := by
    unfold FourRowHessenberg.tripleMatch at hrows
    rcases hrows with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
  have htT : t = T := by have := hp.1; omega
  have hcoef := hp.2
  rw [htT] at hcoef
  have hrR := mul_right_cancel₀ ((complete_ne_zero_iff T).mpr hT.le) hcoef
  exact ⟨hdD, htT, complete_injective_nonnegative hr.le hR.le hrR⟩

/-- The AV first-coefficient comparison recovers its quadratic factor and
monomial content, including all collisions between the content and row/gap labels. -/
theorem av_first_coefficient_reading {q : ℕ+} {b c s t d B C S T D : ℤ}
    (hb : 0 < b) (hc : t < c) (hs : 0 < s) (ht : 0 < t)
    (hB : 0 < B) (hC : T < C) (hS : 0 < S) (hT : 0 < T)
    (hbq : b < (q.val : ℤ)) (hcq : c < (q.val : ℤ))
    (hsq : s < (q.val : ℤ)) (htq : t < (q.val : ℤ))
    (hBq : B < (q.val : ℤ)) (hCq : C < (q.val : ℤ))
    (hSq : S < (q.val : ℤ)) (hTq : T < (q.val : ℤ))
    (hd : (q.val : ℤ) + t < d) (hD : (q.val : ℤ) + T < D)
    (he : complete b * complete c * complete d -
        complete t * complete b * complete (c + d - t) +
        complete s * complete t * complete ((q.val : ℤ) + d - t) =
      complete B * complete C * complete D -
        complete T * complete B * complete (C + D - T) +
        complete S * complete T * complete ((q.val : ℤ) + D - T)) :
    b = B ∧ c = C ∧ d = D ∧ s = S ∧ t = T := by
  let F (b c d s t : ℤ) : CompleteRing :=
    complete b * complete c * complete d - complete t * complete b * complete (c + d - t) +
      complete s * complete t * complete ((q.val : ℤ) + d - t)
  have htop (b c d s t : ℤ) (hb : b < (q.val : ℤ)) (hc : c < (q.val : ℤ))
      (hs : s < (q.val : ℤ)) (ht : t < (q.val : ℤ))
      (hp : 0 < t) (hd : (q.val : ℤ) + t < d) (v : ℕ+)
      (hv : (v.val : ℤ) = (q.val : ℤ) + d - t) :
      MvPolynomial.pderiv v (F b c d s t) = complete s * complete t := by
    dsimp [F]
    simp [MvPolynomial.pderiv_mul, residual_pderiv_complete, hv,
      show b ≠ (q.val : ℤ) + d - t by omega,
      show c ≠ (q.val : ℤ) + d - t by omega,
      show d ≠ (q.val : ℤ) + d - t by omega,
      show s ≠ (q.val : ℤ) + d - t by omega,
      show t ≠ (q.val : ℤ) + d - t by omega,
      show c + d - t ≠ (q.val : ℤ) + d - t by omega]
  have habove (b c d s t : ℤ) (hb : b < (q.val : ℤ)) (hc : c < (q.val : ℤ))
      (hs : s < (q.val : ℤ)) (ht : t < (q.val : ℤ))
      (hp : 0 < t) (hd : (q.val : ℤ) + t < d) (v : ℕ+)
      (hv : (q.val : ℤ) + d - t < (v.val : ℤ)) :
      MvPolynomial.pderiv v (F b c d s t) = 0 := by
    dsimp [F]
    simp [MvPolynomial.pderiv_mul, residual_pderiv_complete,
      show b ≠ (v.val : ℤ) by omega, show c ≠ (v.val : ℤ) by omega,
      show d ≠ (v.val : ℤ) by omega, show s ≠ (v.val : ℤ) by omega,
      show t ≠ (v.val : ℤ) by omega, show c + d - t ≠ (v.val : ℤ) by omega,
      show (q.val : ℤ) + d - t ≠ (v.val : ℤ) by omega]
  have hp := private_top_reading (F b c d s t) (F B C D S T)
    ((q.val : ℤ) + d - t) ((q.val : ℤ) + D - T)
    (complete s * complete t) (complete S * complete T)
    (by omega) (by omega)
    (mul_ne_zero ((complete_ne_zero_iff s).mpr hs.le) ((complete_ne_zero_iff t).mpr ht.le))
    (mul_ne_zero ((complete_ne_zero_iff S).mpr hS.le) ((complete_ne_zero_iff T).mpr hT.le))
    (htop b c d s t hbq hcq hsq htq ht hd)
    (htop B C D S T hBq hCq hSq hTq hT hD)
    (habove b c d s t hbq hcq hsq htq ht hd)
    (habove B C D S T hBq hCq hSq hTq hT hD) he
  have hbin : complete b * quadraticB t c d = complete B * quadraticB T C D := by
    rw [hp.1] at he
    have hl := congrArg (fun p : CompleteRing => p * complete ((q.val : ℤ) + D - T)) hp.2
    unfold quadraticB
    linear_combination -he + hl
  obtain ⟨hbb, htt, hrows⟩ := variable_times_B_reading b t c d B T C D
    hb hB ht hc (by omega) hT hC (by omega) hbin
  have hcc : c = C := by rcases hrows with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hdd : d = D := by rcases hrows with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hcoef := hp.2
  rw [htt] at hcoef
  have hss := mul_right_cancel₀ ((complete_ne_zero_iff T).mpr hT.le) hcoef
  exact ⟨hbb, hcc, hdd, complete_injective_nonnegative hs.le hS.le hss, htt⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- The BC first coefficient already fixes the endpoint row product, including
ties and repeated monomials; the middle gap is not needed for this reading. -/
theorem bc_endpoint_product_reading (q a d r t A D R T : ℤ)
    (hr : 0 < r) (ht : 0 < t) (hrq : r < q) (htq : t < q)
    (ha : r < a) (hd : q + t < d) (haq : a ≠ q)
    (hR : 0 < R) (hT : 0 < T) (hRq : R < q) (hTq : T < q)
    (hA : R < A) (hD : q + T < D) (hAq : A ≠ q)
    (he : complete r * complete (a + q - r) * complete d +
        complete t * complete a * complete (q + d - t) =
      complete R * complete (A + q - R) * complete D +
        complete T * complete A * complete (q + D - T)) :
    (a = A ∧ d = D) ∨ (a = D ∧ d = A) := by
  have hmon := positive_triple_sum_reading hr (by omega) (by omega)
    ht (by omega) (by omega) hR (by omega) (by omega)
    hT (by omega) (by omega) he
  rcases hmon with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩ <;>
    unfold FourRowHessenberg.tripleMatch at hm1 hm2 <;>
    rcases hm1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases hm2 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- Every coefficient in the derivative of a negative monomial pair has
nonpositive augmentation, regardless of repeated factors or term collisions. -/
theorem negative_triple_pair_derivative_nonpos (a b c d e f : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (v : ℕ+) :
    residualAugmentation (MvPolynomial.pderiv v
      (-(complete a * complete b * complete c) -
        complete d * complete e * complete f)) ≤ 0 := by
  simp only [map_sub, map_add, map_neg, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, map_mul, apply_ite, map_one, map_zero,
    residualAugmentation_complete ha, residualAugmentation_complete hb,
    residualAugmentation_complete hc, residualAugmentation_complete hd,
    residualAugmentation_complete he, residualAugmentation_complete hf]
  split_ifs <;> norm_num

/-- AC has a private positive largest first-coefficient contribution. -/
theorem ac_first_coefficient_top (q b d r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hrq : r < q)
    (hq : s + t < q) (hb : r + s < b) (hd : q + t < d)
    (v : ℕ+) (hv : (v.val : ℤ) = b + q + d - s - t) :
    MvPolynomial.pderiv v
      (-complete r * complete (q + b - r) * complete d -
        complete s * complete (q + b - s) * complete d -
        complete t * complete b * complete (q + d - t) +
        complete s * complete t * complete (b + q + d - s - t)) =
      complete s * complete t := by
  simp only [map_add, map_sub, map_neg, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, hv, if_pos rfl, ite_true, ite_false,
    if_neg (show r ≠ b + q + d - s - t by omega),
    if_neg (show s ≠ b + q + d - s - t by omega),
    if_neg (show t ≠ b + q + d - s - t by omega),
    if_neg (show b ≠ b + q + d - s - t by omega),
    if_neg (show d ≠ b + q + d - s - t by omega),
    if_neg (show q + b - r ≠ b + q + d - s - t by omega),
    if_neg (show q + b - s ≠ b + q + d - s - t by omega),
    if_neg (show q + d - t ≠ b + q + d - s - t by omega)]
  ring


/-- Actual restrictions retain their private full-interval coefficient at every row count. -/
theorem restriction_top_derivative {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (v : ℕ+) (hv : (v.val : ℤ) = fullIndex P) :
    MvPolynomial.pderiv v (restriction q P) = (-1 : CompleteRing) ^ n * gapMonomial P := by
  have heq : v = fullGenerator P := by
    apply PNat.coe_injective
    exact_mod_cast hv.trans (fullGenerator_int_coe P).symm
  subst v
  have hg := MvPolynomial.pderiv_eq_zero_of_notMem_vars (full_not_mem_gapMonomial hP.thick)
  have hr := MvPolynomial.pderiv_eq_zero_of_notMem_vars (full_not_mem_residual q P)
  have hs : (-1 : CompleteRing) ^ n = MvPolynomial.C ((-1 : ℚ) ^ n) := by simp
  have hd : MvPolynomial.pderiv (fullGenerator P) ((-1 : CompleteRing) ^ n) = 0 := by
    rw [hs]
    exact MvPolynomial.pderiv_C
  rw [restriction_affine hP]
  simp only [map_add, MvPolynomial.pderiv_mul, hg, hr, hd,
    MvPolynomial.pderiv_X_self, zero_mul, mul_zero, zero_add, add_zero, mul_one]

theorem restriction_derivative_above {n : ℕ} {q : ℕ+} {P : Profile n}
    (v : ℕ+) (hv : fullIndex P < (v.val : ℤ)) :
    MvPolynomial.pderiv v (restriction q P) = 0 :=
  MvPolynomial.pderiv_eq_zero_of_notMem_vars (not_mem_restriction_above_full q P v hv)

/-- Full interval and the repeated gap multiset are recovered from collected
restricted polynomials, before any component matching classification. -/
theorem restriction_full_and_gap_eq {n : ℕ} {q : ℕ+} {P Q : Profile n}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (he : restriction q P = restriction q Q) :
    fullIndex P = fullIndex Q ∧ gapMonomial P = gapMonomial Q := by
  have hs : (-1 : CompleteRing) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h := private_top_reading _ _ (fullIndex P) (fullIndex Q)
    ((-1 : CompleteRing) ^ n * gapMonomial P) ((-1 : CompleteRing) ^ n * gapMonomial Q)
    P.toBetaDiagram.largestLabel_pos Q.toBetaDiagram.largestLabel_pos
    (mul_ne_zero hs (gapMonomial_ne_zero P)) (mul_ne_zero hs (gapMonomial_ne_zero Q))
    (restriction_top_derivative hP) (restriction_top_derivative hQ)
    (fun v hv => restriction_derivative_above v hv)
    (fun v hv => restriction_derivative_above v hv) he
  exact ⟨h.1, mul_left_cancel₀ hs h.2⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- The two distinct contracted rotations of an AC lift cannot have the same
tail first coefficient.  The statement permits repeated gap and row labels. -/
theorem ac_rotated_tail_reading (q r s t b d B D : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hrq : r < q) (hq : s + t < q)
    (hb : r + s < b) (hB : r + t < B)
    (hd : q + t < d) (hD : q + s < D)
    (hbq : b ≠ q) (hBq : B ≠ q)
    (hDlift : D = q + b - r) (hdlift : d = q + B - r)
    (he : complete s * complete (q + b - s) * complete d +
        complete t * complete b * complete (q + d - t) =
      complete t * complete (q + B - t) * complete D +
        complete s * complete B * complete (q + D - s)) :
    b = B ∧ d = D ∧ s = t := by
  have hmon := positive_triple_sum_reading hs (by omega) (by omega)
    ht (by omega) (by omega) ht (by omega) (by omega)
    hs (by omega) (by omega) he
  rcases hmon with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩ <;>
    unfold FourRowHessenberg.tripleMatch at hm1 hm2 <;>
    rcases hm1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases hm2 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

theorem ac_first_coefficient_above (q b d r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hrq : r < q)
    (hq : s + t < q) (hb : r + s < b) (hd : q + t < d)
    (v : ℕ+) (hv : b + q + d - s - t < (v.val : ℤ)) :
    MvPolynomial.pderiv v
      (-complete r * complete (q + b - r) * complete d -
        complete s * complete (q + b - s) * complete d -
        complete t * complete b * complete (q + d - t) +
        complete s * complete t * complete (b + q + d - s - t)) = 0 := by
  simp only [map_add, map_sub, map_neg, MvPolynomial.pderiv_mul,
    residual_pderiv_complete,
    if_neg (show r ≠ (v.val : ℤ) by omega),
    if_neg (show s ≠ (v.val : ℤ) by omega),
    if_neg (show t ≠ (v.val : ℤ) by omega),
    if_neg (show b ≠ (v.val : ℤ) by omega),
    if_neg (show d ≠ (v.val : ℤ) by omega),
    if_neg (show q + b - r ≠ (v.val : ℤ) by omega),
    if_neg (show q + b - s ≠ (v.val : ℤ) by omega),
    if_neg (show q + d - t ≠ (v.val : ℤ) by omega),
    if_neg (show b + q + d - s - t ≠ (v.val : ℤ) by omega)]
  ring

/-- The private positive coefficient identifies the AC suffix interval and its
gap pair, independently of the first endpoint lift. -/
theorem ac_first_coefficient_largest (q b d r s t B D R S T : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hrq : r < q)
    (hq : s + t < q) (hb : r + s < b) (hd : q + t < d)
    (hR : 0 < R) (hS : 0 < S) (hT : 0 < T) (hRq : R < q)
    (hQ : S + T < q) (hB : R + S < B) (hD : q + T < D)
    (he : -complete r * complete (q + b - r) * complete d -
        complete s * complete (q + b - s) * complete d -
        complete t * complete b * complete (q + d - t) +
        complete s * complete t * complete (b + q + d - s - t) =
      -complete R * complete (q + B - R) * complete D -
        complete S * complete (q + B - S) * complete D -
        complete T * complete B * complete (q + D - T) +
        complete S * complete T * complete (B + q + D - S - T)) :
    b + q + d - s - t = B + q + D - S - T ∧
      complete s * complete t = complete S * complete T := by
  exact private_top_reading _ _ (b + q + d - s - t) (B + q + D - S - T)
    (complete s * complete t) (complete S * complete T)
    (by omega) (by omega)
    (mul_ne_zero ((complete_ne_zero_iff s).mpr hs.le) ((complete_ne_zero_iff t).mpr ht.le))
    (mul_ne_zero ((complete_ne_zero_iff S).mpr hS.le) ((complete_ne_zero_iff T).mpr hT.le))
    (ac_first_coefficient_top q b d r s t hr hs ht hrq hq hb hd)
    (ac_first_coefficient_top q B D R S T hR hS hT hRq hQ hB hD)
    (ac_first_coefficient_above q b d r s t hr hs ht hrq hq hb hd)
    (ac_first_coefficient_above q B D R S T hR hS hT hRq hQ hB hD) he

noncomputable def abcFirstPolynomial (q d r s t : ℤ) : CompleteRing :=
  -complete r * complete (2 * q - r) * complete d -
    complete s * complete (2 * q - s) * complete d +
    complete s * complete t * complete (2 * q + d - s - t)

noncomputable def uvFirstPolynomial (a c d r s t : ℤ) : CompleteRing :=
  -complete r * complete c * complete d -
    complete s * complete a * complete d +
    complete r * complete t * complete (c + d - t)

theorem abc_first_top (q d r s t : ℤ) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hrq : r < q) (hq : s + t < q) (hd : q + t < d)
    (v : ℕ+) (hv : (v.val : ℤ) = 2 * q + d - s - t) :
    MvPolynomial.pderiv v (abcFirstPolynomial q d r s t) = complete s * complete t := by
  simp only [abcFirstPolynomial, map_add, map_sub, map_neg, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, hv, if_pos rfl, ite_true, ite_false,
    if_neg (show r ≠ 2 * q + d - s - t by omega),
    if_neg (show s ≠ 2 * q + d - s - t by omega),
    if_neg (show t ≠ 2 * q + d - s - t by omega),
    if_neg (show d ≠ 2 * q + d - s - t by omega),
    if_neg (show 2 * q - r ≠ 2 * q + d - s - t by omega),
    if_neg (show 2 * q - s ≠ 2 * q + d - s - t by omega)]
  ring

theorem abc_first_above (q d r s t : ℤ) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hrq : r < q) (hq : s + t < q) (hd : q + t < d)
    (v : ℕ+) (hv : 2 * q + d - s - t < (v.val : ℤ)) :
    MvPolynomial.pderiv v (abcFirstPolynomial q d r s t) = 0 := by
  simp only [abcFirstPolynomial, map_add, map_sub, map_neg, MvPolynomial.pderiv_mul,
    residual_pderiv_complete,
    if_neg (show r ≠ (v.val : ℤ) by omega),
    if_neg (show s ≠ (v.val : ℤ) by omega),
    if_neg (show t ≠ (v.val : ℤ) by omega),
    if_neg (show d ≠ (v.val : ℤ) by omega),
    if_neg (show 2 * q - r ≠ (v.val : ℤ) by omega),
    if_neg (show 2 * q - s ≠ (v.val : ℤ) by omega),
    if_neg (show 2 * q + d - s - t ≠ (v.val : ℤ) by omega)]
  ring

theorem uv_first_top (q a c d r s t : ℤ)
    (ha : a < q) (hc : c < q) (hr : r < q) (hs : s < q) (ht : t < q)
    (hct : t < c) (htPos : 0 < t) (hd : q + t < d)
    (v : ℕ+) (hv : (v.val : ℤ) = c + d - t) :
    MvPolynomial.pderiv v (uvFirstPolynomial a c d r s t) = complete r * complete t := by
  simp only [uvFirstPolynomial, map_add, map_sub, map_neg, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, hv, if_pos rfl, ite_true, ite_false,
    if_neg (show a ≠ c + d - t by omega), if_neg (show c ≠ c + d - t by omega),
    if_neg (show r ≠ c + d - t by omega), if_neg (show s ≠ c + d - t by omega),
    if_neg (show t ≠ c + d - t by omega), if_neg (show d ≠ c + d - t by omega)]
  ring

theorem uv_first_above (q a c d r s t : ℤ)
    (ha : a < q) (hc : c < q) (hr : r < q) (hs : s < q) (ht : t < q)
    (hct : t < c) (htPos : 0 < t) (hd : q + t < d)
    (v : ℕ+) (hv : c + d - t < (v.val : ℤ)) :
    MvPolynomial.pderiv v (uvFirstPolynomial a c d r s t) = 0 := by
  simp only [uvFirstPolynomial, map_add, map_sub, map_neg, MvPolynomial.pderiv_mul,
    residual_pderiv_complete,
    if_neg (show a ≠ (v.val : ℤ) by omega), if_neg (show c ≠ (v.val : ℤ) by omega),
    if_neg (show r ≠ (v.val : ℤ) by omega), if_neg (show s ≠ (v.val : ℤ) by omega),
    if_neg (show t ≠ (v.val : ℤ) by omega), if_neg (show d ≠ (v.val : ℤ) by omega),
    if_neg (show c + d - t ≠ (v.val : ℤ) by omega)]
  ring

theorem abc_first_largest (q d r s t D R S T : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hrq : r < q) (hq : s + t < q) (hd : q + t < d)
    (hR : 0 < R) (hS : 0 < S) (hT : 0 < T)
    (hRq : R < q) (hQ : S + T < q) (hD : q + T < D)
    (he : abcFirstPolynomial q d r s t = abcFirstPolynomial q D R S T) :
    2 * q + d - s - t = 2 * q + D - S - T ∧
      complete s * complete t = complete S * complete T :=
  private_top_reading _ _ (2 * q + d - s - t) (2 * q + D - S - T)
    (complete s * complete t) (complete S * complete T)
    (by omega) (by omega)
    (mul_ne_zero ((complete_ne_zero_iff s).mpr hs.le) ((complete_ne_zero_iff t).mpr ht.le))
    (mul_ne_zero ((complete_ne_zero_iff S).mpr hS.le) ((complete_ne_zero_iff T).mpr hT.le))
    (abc_first_top q d r s t hr hs ht hrq hq hd)
    (abc_first_top q D R S T hR hS hT hRq hQ hD)
    (abc_first_above q d r s t hr hs ht hrq hq hd)
    (abc_first_above q D R S T hR hS hT hRq hQ hD) he

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- ABC cannot cross-match UV: the remaining negative triples have respectively
one and two indices below q, counted with multiplicity. -/
theorem abc_uv_first_ne (q d r s t A C D R S T : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hrq : r < q) (hsq : s < q) (hq : s + t < q) (hd : q + t < d)
    (hA : 0 < A) (hC : 0 < C) (hR : 0 < R) (hS : 0 < S) (hT : 0 < T)
    (hAq : A < q) (hCq : C < q) (hRq : R < q) (hSq : S < q) (hTq : T < q)
    (hCT : T < C) (hD : q + T < D) :
    abcFirstPolynomial q d r s t ≠ uvFirstPolynomial A C D R S T := by
  intro he
  have hp := private_top_reading _ _ (2 * q + d - s - t) (C + D - T)
    (complete s * complete t) (complete R * complete T)
    (by omega) (by omega)
    (mul_ne_zero ((complete_ne_zero_iff s).mpr hs.le) ((complete_ne_zero_iff t).mpr ht.le))
    (mul_ne_zero ((complete_ne_zero_iff R).mpr hR.le) ((complete_ne_zero_iff T).mpr hT.le))
    (abc_first_top q d r s t hr hs ht hrq hq hd)
    (uv_first_top q A C D R S T hAq hCq hRq hSq hTq hCT hT hD)
    (abc_first_above q d r s t hr hs ht hrq hq hd)
    (uv_first_above q A C D R S T hAq hCq hRq hSq hTq hCT hT hD) he
  have hneg : complete r * complete (2 * q - r) * complete d +
      complete s * complete (2 * q - s) * complete d =
    complete R * complete C * complete D + complete S * complete A * complete D := by
    unfold abcFirstPolynomial uvFirstPolynomial at he
    rw [hp.1] at he
    have hl := congrArg (fun p : CompleteRing => p * complete (C + D - T)) hp.2
    linear_combination -he + hl
  have hmon := positive_triple_sum_reading hr (by omega) (by omega)
    hs (by omega) (by omega) hR hC (by omega) hS hA (by omega) hneg
  rcases hmon with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩ <;>
    unfold FourRowHessenberg.tripleMatch at hm1 hm2 <;>
    rcases hm1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

theorem negative_triple_derivative_nonpos (a b c : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (v : ℕ+) :
    residualAugmentation (MvPolynomial.pderiv v (-(complete a * complete b * complete c))) ≤ 0 := by
  simp only [map_add, map_neg, MvPolynomial.pderiv_mul, residual_pderiv_complete,
    map_mul, apply_ite, map_one, map_zero,
    residualAugmentation_complete ha, residualAugmentation_complete hb,
    residualAugmentation_complete hc]
  split_ifs <;> norm_num

/-- A repeated gap product recovers its arithmetic sum, with all multiplicities. -/
theorem gap_sum_three_eq {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (he : gapMonomial P = gapMonomial Q) :
    (P.g 0 : ℤ) + P.g 1 + P.g 2 = (Q.g 0 : ℤ) + Q.g 1 + Q.g 2 := by
  have hp : complete (P.g 0) * complete (P.g 1) * complete (P.g 2) =
      complete (Q.g 0) * complete (Q.g 1) * complete (Q.g 2) := by
    simpa only [gapMonomial, Fin.prod_univ_three, mul_assoc] using he
  have hm := residual_triple_product_reading
    (show (0 : ℤ) < P.g 0 by exact_mod_cast hP.gap_pos 0)
    (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1)
    (show (0 : ℤ) < P.g 2 by exact_mod_cast hP.gap_pos 2)
    (show (0 : ℤ) < Q.g 0 by exact_mod_cast hQ.gap_pos 0)
    (show (0 : ℤ) < Q.g 1 by exact_mod_cast hQ.gap_pos 1)
    (show (0 : ℤ) < Q.g 2 by exact_mod_cast hQ.gap_pos 2) hp
  unfold FourRowHessenberg.tripleMatch at hm
  rcases hm with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
    ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

theorem residual_initialForm_neg (w : ℕ+ → ℝ) (p : CompleteRing) :
    Base.initialForm w (-p) = -Base.initialForm w p := by
  have hweight : Base.leastWeight w (-p) = Base.leastWeight w p := by
    simp only [Base.leastWeight, MvPolynomial.support_neg]
  unfold Base.initialForm
  rw [hweight, map_neg]

theorem residual_initialForm_complete (k : ℤ) (hk : 0 ≤ k) :
    Base.initialForm Base.squareWeight.generatorWeight (complete k) = complete k := by
  rw [complete, integerLift_initialForm, Base.complete_initialForm Base.squareWeight k hk]

/-- B's square-initial monomial has negative sign.  The proof uses an actual
two-row profile, so index-zero conventions are not replaced by a new weight model. -/
theorem quadraticB_square_initial (r a c : ℤ) (hr : 0 < r) (ha : r < a) (hc : r < c) :
    Base.initialForm Base.squareWeight.generatorWeight (quadraticB r a c) =
      -(complete a * complete c) := by
  let P : Profile 1 :=
    { r := ![a.toNat, c.toNat]
      g := ![r.toNat]
      r_pos := by intro i; fin_cases i <;> simp <;> omega
      g_lt_castSucc := by intro j; fin_cases j <;> simp <;> omega
      g_lt_succ := by intro j; fin_cases j <;> simp <;> omega }
  have hRa : (P.r 0 : ℤ) = a := by dsimp [P]; omega
  have hRc : (P.r 1 : ℤ) = c := by dsimp [P]; omega
  have hRg : (P.g 0 : ℤ) = r := by dsimp [P]; omega
  have h0 := P.xi_sub_zeta (0 : Fin 2)
  have h1 := P.xi_sub_zeta (1 : Fin 2)
  have hg := P.xi_succ_sub_zeta_castSucc (0 : Fin 1)
  change P.xi 1 - P.zeta 0 = (P.g 0 : ℤ) at hg
  rw [hRa] at h0
  rw [hRc] at h1
  rw [hRg] at hg
  have hu : P.xi 0 - P.zeta 1 = a + c - r := by omega
  have hpoly : P.toBetaDiagram.schur = -quadraticB r a c := by
    rw [BetaDiagram.schur, Matrix.det_fin_two]
    change complete (P.xi 0 - P.zeta 0) * complete (P.xi 1 - P.zeta 1) -
      complete (P.xi 0 - P.zeta 1) * complete (P.xi 1 - P.zeta 0) = _
    rw [h0, h1, hu, hg]
    unfold quadraticB
    ring
  have h := P.toBetaDiagram.square_initialForm
  rw [hpoly, residual_initialForm_neg] at h
  change -Base.initialForm Base.squareWeight.generatorWeight (quadraticB r a c) =
    ∏ i : Fin 2, complete (P.xi i - P.zeta i) at h
  have hdiag : (∏ i : Fin 2, complete (P.xi i - P.zeta i)) =
      complete a * complete c := by
    simp only [Fin.prod_univ_two, P.xi_sub_zeta, hRa, hRc]
  rw [hdiag] at h
  simpa only [neg_neg] using congrArg (fun p : CompleteRing => -p) h

theorem variable_times_B_square_augmentation (b r a c : ℤ)
    (hb : 0 < b) (hr : 0 < r) (ha : r < a) (hc : r < c) :
    residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight
      (complete b * quadraticB r a c)) = -1 := by
  rw [Base.initialForm_mul ((complete_ne_zero_iff b).mpr hb.le)
    (quadraticB_irreducible r a c hr ha hc).ne_zero,
    residual_initialForm_complete b hb.le, quadraticB_square_initial r a c hr ha hc]
  simp only [map_mul, map_neg, residualAugmentation_complete hb,
    residualAugmentation_complete (show 0 < a by omega),
    residualAugmentation_complete (show 0 < c by omega)]
  norm_num

theorem negative_variable_times_B_square_augmentation (b r a c : ℤ)
    (hb : 0 < b) (hr : 0 < r) (ha : r < a) (hc : r < c) :
    residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight
      (-(complete b * quadraticB r a c))) = 1 := by
  rw [residual_initialForm_neg, map_neg,
    variable_times_B_square_augmentation b r a c hb hr ha hc]
  norm_num

/-- Every actual full Schur function has a positive square-initial monomial. -/
theorem profile_square_initial_augmentation {n : ℕ} (P : Profile n) :
    residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight
      P.toBetaDiagram.schur) = 1 := by
  rw [P.toBetaDiagram.square_initialForm, map_prod]
  change (∏ i : Fin (n + 1), residualAugmentation (complete (P.xi i - P.zeta i))) = 1
  apply Finset.prod_eq_one
  intro i _
  rw [P.xi_sub_zeta]
  exact residualAugmentation_complete (by exact_mod_cast P.r_pos i)

/-- The isolated U competitor of an AB jet has an extra private proper-interval
label.  This proves the exclusion directly, without a coefficient-norm census. -/
theorem ab_u_restriction_defect_ne (q r s t c d C D : ℤ)
    (hs : 0 < s) (hrr : s < r) (ht : 0 < t) (hq : 2 * r < q)
    (hc : s + t < c) (hd : q + t < d)
    (hC : q + t < C) (hD : q + t < D)
    (hrows : C + D = q + c + d - s) :
    -threeInterval complete (2 * q - r) c d s t ≠
      complete (q + s - r) * complete C * complete D -
        complete r * complete (q + s - r + C - r) * complete D -
        complete t * complete (q + s - r) * complete (C + D - t) +
        complete s * complete (q + C - r) * complete D +
        complete r * complete t * complete (q + s - r + C + D - r - t) -
        complete s * complete t * complete (q + s - r + C + D - s - t) := by
  classical
  let y : ℤ := q + s - r + C + D - r - t
  have hy : 0 < y := by dsimp [y]; omega
  let v : ℕ+ := ⟨y.toNat, by omega⟩
  have hv : (v.val : ℤ) = y := by dsimp [v]; omega
  have hsmall :
      2 * q - r < y ∧ c < y ∧ d < y ∧ s < y ∧ t < y ∧ r < y ∧
      2 * q - r + c - s < y ∧ c + d - t < y ∧
      q + s - r < y ∧ C < y ∧ D < y ∧
      q + s - r + C - r < y ∧ C + D - t < y ∧ q + C - r < y := by
    dsimp [y]
    omega
  have hfull : y < 2 * q - r + c + d - s - t ∧
      y < q + s - r + C + D - s - t := by dsimp [y]; omega
  have hzero (k : ℤ) (hk : k ≠ y) : MvPolynomial.pderiv v (complete k) = 0 := by
    rw [residual_pderiv_complete, hv, if_neg hk]
  have hself : MvPolynomial.pderiv v (complete y) = 1 := by
    rw [residual_pderiv_complete, hv, if_pos rfl]
  have hleft : MvPolynomial.pderiv v
      (-threeInterval complete (2 * q - r) c d s t) = 0 := by
    simp only [threeInterval, map_neg, map_add, map_sub, MvPolynomial.pderiv_mul,
      hzero (2 * q - r) (by omega), hzero c (by omega), hzero d (by omega),
      hzero s (by omega), hzero t (by omega),
      hzero (2 * q - r + c - s) (by omega), hzero (c + d - t) (by omega),
      hzero (2 * q - r + c + d - s - t) (by omega),
      zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub, neg_zero]
  have hright : MvPolynomial.pderiv v
      (complete (q + s - r) * complete C * complete D -
        complete r * complete (q + s - r + C - r) * complete D -
        complete t * complete (q + s - r) * complete (C + D - t) +
        complete s * complete (q + C - r) * complete D +
        complete r * complete t * complete (q + s - r + C + D - r - t) -
        complete s * complete t * complete (q + s - r + C + D - s - t)) =
      complete r * complete t := by
    change MvPolynomial.pderiv v
      (complete (q + s - r) * complete C * complete D -
        complete r * complete (q + s - r + C - r) * complete D -
        complete t * complete (q + s - r) * complete (C + D - t) +
        complete s * complete (q + C - r) * complete D +
        complete r * complete t * complete y -
        complete s * complete t * complete (q + s - r + C + D - s - t)) = _
    simp only [map_add, map_sub, MvPolynomial.pderiv_mul, hself,
      hzero (q + s - r) (by omega), hzero C (by omega), hzero D (by omega),
      hzero r (by omega), hzero t (by omega), hzero s (by omega),
      hzero (q + s - r + C - r) (by omega), hzero (C + D - t) (by omega),
      hzero (q + C - r) (by omega), hzero (q + s - r + C + D - s - t) (by omega),
      zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub, mul_one]
  intro he
  have h := congrArg (MvPolynomial.pderiv v) he
  rw [hleft, hright] at h
  exact mul_ne_zero ((complete_ne_zero_iff r).mpr (by omega))
    ((complete_ne_zero_iff t).mpr ht.le) h.symm

theorem four_no_contact_of_first_indices {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P)
    (ha : P.r 0 ≠ q.val) (hb : P.r 1 ≠ q.val) (hc : P.r 2 ≠ q.val)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val)
    (hv : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val)
    (hx : prefixIndex P ≠ q.val) : NoEntryContact q P := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hfull := fullIndex_gt_q hP
  rw [fullIndex_four] at hfull
  change (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 ≠ q.val at hx
  have hg0 : (P.g 0 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 0
  have hg1 : (P.g 1 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 1
  have hg2 : (P.g 2 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 2
  intro i j
  change (Matrix.of (fun i j : Fin 4 => P.xi i - P.zeta j)) i j ≠ (q.val : ℤ)
  rw [P.indices_four]
  fin_cases i <;> fin_cases j <;> norm_num [fourIndices] <;> omega

/-- Sum of absolute collected coefficients; repeated monomials retain their multiplicity. -/
noncomputable def collectedNorm (p : CompleteRing) : ℚ :=
  ∑ d ∈ p.support, |p.coeff d|

theorem residualAugmentation_eq_sum_coeff (p : CompleteRing) :
    residualAugmentation p = ∑ d ∈ p.support, p.coeff d := by
  change p.eval₂ (RingHom.id ℚ) (fun _ => 1) = _
  simp [MvPolynomial.eval₂_eq]

private theorem collectedNorm_sub_union (p n : CompleteRing) :
    collectedNorm (p - n) =
      ∑ d ∈ p.support ∪ n.support, |(p - n).coeff d| := by
  classical
  apply Finset.sum_subset (MvPolynomial.support_sub ℕ+ p n)
  intro d _ hd
  rw [MvPolynomial.notMem_support_iff.mp hd, abs_zero]

private theorem sum_coeff_union_left (p n : CompleteRing) :
    (∑ d ∈ p.support ∪ n.support, p.coeff d) = residualAugmentation p := by
  classical
  rw [residualAugmentation_eq_sum_coeff]
  symm
  apply Finset.sum_subset (Finset.subset_union_left)
  intro d _ hd
  exact MvPolynomial.notMem_support_iff.mp hd

private theorem sum_coeff_union_right (p n : CompleteRing) :
    (∑ d ∈ p.support ∪ n.support, n.coeff d) = residualAugmentation n := by
  classical
  rw [residualAugmentation_eq_sum_coeff]
  symm
  apply Finset.sum_subset (Finset.subset_union_right)
  intro d _ hd
  exact MvPolynomial.notMem_support_iff.mp hd

/-- The triangle bound is a statement about collected coefficients, not term count. -/
theorem collectedNorm_sub_le_of_nonnegative (p n : CompleteRing)
    (hp : ∀ d, 0 ≤ p.coeff d) (hn : ∀ d, 0 ≤ n.coeff d) :
    collectedNorm (p - n) ≤ residualAugmentation p + residualAugmentation n := by
  classical
  rw [collectedNorm_sub_union]
  calc
    (∑ d ∈ p.support ∪ n.support, |(p - n).coeff d|) ≤
        ∑ d ∈ p.support ∪ n.support, (p.coeff d + n.coeff d) := by
      apply Finset.sum_le_sum
      intro d _
      rw [MvPolynomial.coeff_sub]
      apply abs_le.mpr
      constructor <;> have h1 := hp d <;> have h2 := hn d <;> linarith
    _ = residualAugmentation p + residualAugmentation n := by
      rw [Finset.sum_add_distrib, sum_coeff_union_left, sum_coeff_union_right]

/-- Opposite-sign disjointness is sufficient for the exact norm; no distinctness
is imposed among the positive terms or among the negative terms. -/
theorem collectedNorm_sub_of_nonnegative_disjoint (p n : CompleteRing)
    (hp : ∀ d, 0 ≤ p.coeff d) (hn : ∀ d, 0 ≤ n.coeff d)
    (hdisj : Disjoint p.support n.support) :
    collectedNorm (p - n) = residualAugmentation p + residualAugmentation n := by
  classical
  rw [collectedNorm_sub_union]
  calc
    (∑ d ∈ p.support ∪ n.support, |(p - n).coeff d|) =
        ∑ d ∈ p.support ∪ n.support, (p.coeff d + n.coeff d) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [MvPolynomial.coeff_sub]
      by_cases hd : d ∈ p.support
      · have hdn : d ∉ n.support := fun h => Finset.disjoint_left.mp hdisj hd h
        rw [MvPolynomial.notMem_support_iff.mp hdn, sub_zero, add_zero, abs_of_nonneg (hp d)]
      · rw [MvPolynomial.notMem_support_iff.mp hd, zero_sub, zero_add, abs_neg,
          abs_of_nonneg (hn d)]
    _ = residualAugmentation p + residualAugmentation n := by
      rw [Finset.sum_add_distrib, sum_coeff_union_left, sum_coeff_union_right]

noncomputable def monomialSum {m : ℕ} (e : Fin m → ℕ+ →₀ ℕ) : CompleteRing :=
  ∑ i : Fin m, MvPolynomial.monomial (e i) 1

theorem residualAugmentation_monomial (d : ℕ+ →₀ ℕ) (a : ℚ) :
    residualAugmentation (MvPolynomial.monomial d a) = a := by
  simp [residualAugmentation, MvPolynomial.eval₂Hom_monomial]

theorem monomialSum_augmentation {m : ℕ} (e : Fin m → ℕ+ →₀ ℕ) :
    residualAugmentation (monomialSum e) = m := by
  simp [monomialSum, map_sum, residualAugmentation_monomial]

theorem monomialSum_coeff_nonnegative {m : ℕ} (e : Fin m → ℕ+ →₀ ℕ) (d : ℕ+ →₀ ℕ) :
    0 ≤ (monomialSum e).coeff d := by
  classical
  simp only [monomialSum, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

private theorem monomialSum_support_witness {m : ℕ}
    (e : Fin m → ℕ+ →₀ ℕ) (d : ℕ+ →₀ ℕ) (hd : d ∈ (monomialSum e).support) :
    ∃ i : Fin m, e i = d := by
  classical
  by_contra hn
  push_neg at hn
  apply (MvPolynomial.mem_support_iff.mp hd)
  simp only [monomialSum, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg (hn i)]

theorem monomialSum_disjoint {m k : ℕ}
    (e : Fin m → ℕ+ →₀ ℕ) (f : Fin k → ℕ+ →₀ ℕ)
    (h : ∀ i j, e i ≠ f j) :
    Disjoint (monomialSum e).support (monomialSum f).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro d he hf
  obtain ⟨i, hi⟩ := monomialSum_support_witness e d he
  obtain ⟨j, hj⟩ := monomialSum_support_witness f d hf
  exact h i j (hi.trans hj.symm)

theorem collectedNorm_signed_monomialSum_le {m k : ℕ}
    (e : Fin m → ℕ+ →₀ ℕ) (f : Fin k → ℕ+ →₀ ℕ) :
    collectedNorm (monomialSum e - monomialSum f) ≤ (m : ℚ) + k := by
  simpa only [monomialSum_augmentation] using
    collectedNorm_sub_le_of_nonnegative (monomialSum e) (monomialSum f)
      (monomialSum_coeff_nonnegative e) (monomialSum_coeff_nonnegative f)

theorem collectedNorm_signed_monomialSum {m k : ℕ}
    (e : Fin m → ℕ+ →₀ ℕ) (f : Fin k → ℕ+ →₀ ℕ)
    (h : ∀ i j, e i ≠ f j) :
    collectedNorm (monomialSum e - monomialSum f) = (m : ℚ) + k := by
  simpa only [monomialSum_augmentation] using
    collectedNorm_sub_of_nonnegative_disjoint (monomialSum e) (monomialSum f)
      (monomialSum_coeff_nonnegative e) (monomialSum_coeff_nonnegative f)
      (monomialSum_disjoint e f h)

noncomputable def tripleTerm (T : Fin 3 → ℤ) : CompleteRing :=
  complete (T 0) * complete (T 1) * complete (T 2)

noncomputable def tripleExponent (T : Fin 3 → ℤ) : ℕ+ →₀ ℕ :=
  hExp (T 0).toNat + hExp (T 1).toNat + hExp (T 2).toNat

theorem tripleTerm_monomial (T : Fin 3 → ℤ) (hT : ∀ j, 0 < T j) :
    tripleTerm T = MvPolynomial.monomial (tripleExponent T) 1 := by
  rw [tripleTerm, complete_eq_hh, complete_eq_hh, complete_eq_hh,
    hh_eq_monomial (hT 0).le, hh_eq_monomial (hT 1).le, hh_eq_monomial (hT 2).le,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial]
  simp only [tripleExponent, mul_one]

theorem triple_sum_eq_monomialSum {m : ℕ} (T : Fin m → Fin 3 → ℤ)
    (hT : ∀ i j, 0 < T i j) :
    (∑ i : Fin m, tripleTerm (T i)) = monomialSum (fun i => tripleExponent (T i)) := by
  apply Finset.sum_congr rfl
  intro i _
  exact tripleTerm_monomial (T i) (hT i)

theorem collectedNorm_signed_triples_le {m k : ℕ}
    (T : Fin m → Fin 3 → ℤ) (U : Fin k → Fin 3 → ℤ)
    (hT : ∀ i j, 0 < T i j) (hU : ∀ i j, 0 < U i j) :
    collectedNorm ((∑ i : Fin m, tripleTerm (T i)) -
      ∑ j : Fin k, tripleTerm (U j)) ≤ (m : ℚ) + k := by
  rw [triple_sum_eq_monomialSum T hT, triple_sum_eq_monomialSum U hU]
  exact collectedNorm_signed_monomialSum_le _ _

theorem collectedNorm_signed_triples {m k : ℕ}
    (T : Fin m → Fin 3 → ℤ) (U : Fin k → Fin 3 → ℤ)
    (hT : ∀ i j, 0 < T i j) (hU : ∀ i j, 0 < U i j)
    (hne : ∀ i j, tripleTerm (T i) ≠ tripleTerm (U j)) :
    collectedNorm ((∑ i : Fin m, tripleTerm (T i)) -
      ∑ j : Fin k, tripleTerm (U j)) = (m : ℚ) + k := by
  rw [triple_sum_eq_monomialSum T hT, triple_sum_eq_monomialSum U hU]
  apply collectedNorm_signed_monomialSum
  intro i j he
  apply hne i j
  rw [tripleTerm_monomial (T i) (hT i), tripleTerm_monomial (U j) (hU j), he]

def leftMiddlePositive (q a c d r t : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![c, a + q - r, d], ![a, q + c - r, d],
    ![r, t, a + q + c + d - 2 * r - t]]

def leftMiddleNegative (q a c d r t : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![r, a + q + c - 2 * r, d], ![t, a + q - r, c + d - t],
    ![t, a, q + c + d - r - t]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- Left-middle extraction has no opposite-sign coincidence, including all
same-sign mergers.  The inherited bottom bound rules out the sole crossed case. -/
theorem left_middle_opposite_ne (q a c d r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hq : 2 * r < q)
    (hc : r + t < c) (hd : q + t < d) (i j : Fin 3) :
    tripleTerm (leftMiddlePositive q a c d r t i) ≠
      tripleTerm (leftMiddleNegative q a c d r t j) := by
  have hpos : ∀ i k, 0 < leftMiddlePositive q a c d r t i k := by
    intro i k; fin_cases i <;> fin_cases k <;> simp [leftMiddlePositive] <;> omega
  have hneg : ∀ i k, 0 < leftMiddleNegative q a c d r t i k := by
    intro i k; fin_cases i <;> fin_cases k <;> simp [leftMiddleNegative] <;> omega
  intro he
  have h := residual_triple_product_reading (hpos i 0) (hpos i 1) (hpos i 2)
    (hneg j 0) (hneg j 1) (hneg j 2) he
  fin_cases i <;> fin_cases j <;>
    unfold FourRowHessenberg.tripleMatch at h <;>
    simp only [leftMiddlePositive, leftMiddleNegative, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] at h <;>
    rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> omega

def intervalPositive (q b c d r s t : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![s, b + c - s, d], ![t, b, c + d - t], ![r, t, q + c + d - s - t]]

def intervalNegative (q b c d r s t : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![b, c, d], ![r, q + c - s, d], ![s, t, b + c + d - s - t]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- Interval extraction has no opposite-sign coincidence under its actual
arithmetic domain; a deleted c or v term is treated separately in the norm. -/
theorem interval_opposite_ne (q b c d r s t : ℤ)
    (hr : 0 < r) (hrs : r < s) (ht : 0 < t)
    (hb : r + s < b) (hu : s + b - r = q)
    (hc : s + t < c) (hd : q + t < d) (i j : Fin 3) :
    tripleTerm (intervalPositive q b c d r s t i) ≠
      tripleTerm (intervalNegative q b c d r s t j) := by
  have hpos : ∀ i k, 0 < intervalPositive q b c d r s t i k := by
    intro i k; fin_cases i <;> fin_cases k <;> simp [intervalPositive] <;> omega
  have hneg : ∀ i k, 0 < intervalNegative q b c d r s t i k := by
    intro i k; fin_cases i <;> fin_cases k <;> simp [intervalNegative] <;> omega
  intro he
  have h := residual_triple_product_reading (hpos i 0) (hpos i 1) (hpos i 2)
    (hneg j 0) (hneg j 1) (hneg j 2) he
  fin_cases i <;> fin_cases j <;>
    unfold FourRowHessenberg.tripleMatch at h <;>
    simp only [intervalPositive, intervalNegative, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] at h <;>
    rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> omega

def rightMiddlePositive (q a b d r s : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![a, b + q - s, d], ![a, b, q + d - s],
    ![r, s, a + b + q + d - r - 2 * s]]

def rightMiddleNegative (q a b d r s : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![r, a + b + q - r - s, d], ![r, a + b - r, q + d - s],
    ![s, a, b + q + d - 2 * s]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- The right-middle table has precisely one possible opposite-sign match.
The exceptional locus is derived from matching the actual three factors. -/
theorem right_middle_opposite_locus (q a b d r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ha : r < a)
    (hb : r + s < b) (hq : 2 * s < q) (hd : q + s < d)
    (i j : Fin 3)
    (he : tripleTerm (rightMiddlePositive q a b d r s i) =
      tripleTerm (rightMiddleNegative q a b d r s j)) :
    i = 0 ∧ j = 1 ∧ d = r ∧ a = q + r - s := by
  have hpos : ∀ i k, 0 < rightMiddlePositive q a b d r s i k := by
    intro i k; fin_cases i <;> fin_cases k <;> simp [rightMiddlePositive] <;> omega
  have hneg : ∀ i k, 0 < rightMiddleNegative q a b d r s i k := by
    intro i k; fin_cases i <;> fin_cases k <;> simp [rightMiddleNegative] <;> omega
  have h := residual_triple_product_reading (hpos i 0) (hpos i 1) (hpos i 2)
    (hneg j 0) (hneg j 1) (hneg j 2) he
  fin_cases i <;> fin_cases j <;>
    unfold FourRowHessenberg.tripleMatch at h <;>
    simp only [rightMiddlePositive, rightMiddleNegative, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] at h <;>
    rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;>
    try omega
  all_goals refine ⟨by decide, by decide, ?_, ?_⟩ <;> omega

/-- The full three-row interval expansion is shared by matching and jet recovery. -/
theorem three_full_interval {q : ℕ+} {P : Profile 2} (hP : QComponent q P) :
    P.toBetaDiagram.schur = threeInterval complete (P.r 0) (P.r 1) (P.r 2)
      (P.g 0) (P.g 1) := by
  have hmid := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hmid
  have hi := indices_three P
  have hu : P.xi 0 - P.zeta 1 = (P.r 0 : ℤ) + P.r 1 - P.g 0 :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 0 1) hi
  have hv : P.xi 1 - P.zeta 2 = (P.r 1 : ℤ) + P.r 2 - P.g 1 :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 1 2) hi
  have ht : P.xi 0 - P.zeta 2 =
      (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 0 2) hi
  have hl : P.xi 2 - P.zeta 0 = (P.g 0 : ℤ) + P.g 1 - P.r 1 :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 2 0) hi
  have hn : complete (P.xi 2 - P.zeta 0) = 0 := by
    rw [hl]
    apply complete_of_neg
    omega
  have hg0 : P.xi 1 - P.zeta 0 = (P.g 0 : ℤ) :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 1 0) hi
  have hg1 : P.xi 2 - P.zeta 1 = (P.g 1 : ℤ) :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 2 1) hi
  rw [BetaDiagram.schur_three_expansion]
  simp only [Profile.toBetaDiagram, BetaDiagram.rowLength, P.xi_sub_zeta,
    hg0, hg1, hu, hv, ht, hn, mul_zero, zero_mul, sub_zero,
    add_zero, threeInterval]

/-- Every actual primitive three-row cubic has collected norm at most four.
The bound is proved after producing its contact type from its actual degree. -/
theorem three_primitive_cubic_norm_le {q : ℕ+} {P : Profile 2}
    (hP : QComponent q P) (hd : (canonicalPrimitive hP).totalDegree = 3) :
    collectedNorm (canonicalPrimitive hP) ≤ 4 := by
  have hrow (i : Fin 3) : (0 : ℤ) < P.r i := by exact_mod_cast P.r_pos i
  have hgap (j : Fin 2) : (0 : ℤ) < P.g j := by exact_mod_cast hP.gap_pos j
  have hrow0 := hrow 0
  have hrow1 := hrow 1
  have hrow2 := hrow 2
  have hgap0 := hgap 0
  have hgap1 := hgap 1
  have hra := P.g_lt_castSucc 0
  have hrb := P.g_lt_succ 0
  have hsb := P.g_lt_castSucc 1
  have hsc := P.g_lt_succ 1
  change P.g 0 < P.r 0 at hra
  change P.g 0 < P.r 1 at hrb
  change P.g 1 < P.r 1 at hsb
  change P.g 1 < P.r 2 at hsc
  have hbottom : q.val + P.g 1 < P.r 2 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  rcases three_cubic_contact_cases hP hd with hfree | ⟨ha, hb, hrs⟩ | ⟨hu, has⟩
  · have hm := monicContent_mul_canonicalPrimitive hP
    rw [(three_cubic_nonextraction hP hd).1, one_mul,
      restriction_eq_full_of_no_entry_contact hfree] at hm
    norm_num at hm
    let T : Fin 2 → Fin 3 → ℤ :=
      ![![(P.r 0 : ℤ), P.r 1, P.r 2], ![(P.g 0 : ℤ), P.g 1, fullIndex P]]
    let U : Fin 2 → Fin 3 → ℤ :=
      ![![(P.g 0 : ℤ), (P.r 0 : ℤ) + P.r 1 - P.g 0, P.r 2],
        ![(P.g 1 : ℤ), P.r 0, (P.r 1 : ℤ) + P.r 2 - P.g 1]]
    have hT : ∀ i j, 0 < T i j := by
      intro i j; fin_cases i <;> fin_cases j <;>
        simp [T, fullIndex_three] <;> omega
    have hU : ∀ i j, 0 < U i j := by
      intro i j; fin_cases i <;> fin_cases j <;> simp [U] <;> omega
    have he : canonicalPrimitive hP =
        (∑ i : Fin 2, tripleTerm (T i)) - ∑ j : Fin 2, tripleTerm (U j) := by
      rw [hm, three_full_interval hP]
      simp only [T, U, Fin.sum_univ_two, tripleTerm,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        fullIndex_three, threeInterval, Fin.reduceFinMk]
      ring
    rw [he]
    have hnorm := collectedNorm_signed_triples_le T U hT hU
    norm_num only [Nat.cast_ofNat] at hnorm
    exact hnorm
  · let T : Fin 1 → Fin 3 → ℤ :=
      ![![(P.g 0 : ℤ), P.g 1,
        (P.r 0 : ℤ) + q.val + P.r 2 - P.g 0 - P.g 1]]
    let U : Fin 2 → Fin 3 → ℤ :=
      ![![(P.g 0 : ℤ), (P.r 0 : ℤ) + q.val - P.g 0, P.r 2],
        ![(P.g 1 : ℤ), P.r 0, (q.val : ℤ) + P.r 2 - P.g 1]]
    have hT : ∀ i j, 0 < T i j := by
      intro i j; fin_cases i <;> fin_cases j <;> simp [T] <;> omega
    have hU : ∀ i j, 0 < U i j := by
      intro i j; fin_cases i <;> fin_cases j <;> simp [U] <;> omega
    have he : canonicalPrimitive hP =
        (∑ i : Fin 1, tripleTerm (T i)) - ∑ j : Fin 2, tripleTerm (U j) := by
      rw [canonical_three_middle_cubic hP ha hb hrs]
      simp only [T, U, Fin.sum_univ_one, Fin.sum_univ_two, tripleTerm,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        middleContactCubic, Fin.reduceFinMk]
      ring
    have hbound := collectedNorm_signed_triples_le T U hT hU
    rw [← he] at hbound
    norm_num at hbound
    linarith
  · let T : Fin 2 → Fin 3 → ℤ :=
      ![![(P.r 0 : ℤ), P.r 1, P.r 2],
        ![(P.g 0 : ℤ), P.g 1, (q.val : ℤ) + P.r 2 - P.g 1]]
    let U : Fin 1 → Fin 3 → ℤ :=
      ![![(P.g 1 : ℤ), P.r 0, (P.r 1 : ℤ) + P.r 2 - P.g 1]]
    have hT : ∀ i j, 0 < T i j := by
      intro i j; fin_cases i <;> fin_cases j <;> simp [T] <;> omega
    have hU : ∀ i j, 0 < U i j := by
      intro i j; fin_cases i <;> fin_cases j <;> simp [U] <;> omega
    have he : canonicalPrimitive hP =
        (∑ i : Fin 2, tripleTerm (T i)) - ∑ j : Fin 1, tripleTerm (U j) := by
      rw [canonical_three_interval_cubic hP hu has]
      simp only [T, U, Fin.sum_univ_one, Fin.sum_univ_two, tripleTerm,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        intervalContactCubic, Fin.reduceFinMk]
      ring
    have hbound := collectedNorm_signed_triples_le T U hT hU
    rw [← he] at hbound
    norm_num at hbound
    linarith

noncomputable def leftMiddleCubic (q : ℕ+) (a c d r t : ℤ) : CompleteRing :=
  bar q c * complete (a + q.val - r) * complete d +
    complete a * complete (q.val + c - r) * complete d -
    complete r * complete (a + q.val + c - 2 * r) * complete d -
    complete t * complete (a + q.val - r) * complete (c + d - t) -
    complete t * complete a * complete (q.val + c + d - r - t) +
    complete r * complete t * complete (a + q.val + c + d - 2 * r - t)

noncomputable def rightMiddleCubic (q : ℕ+) (a b d r s : ℤ) : CompleteRing :=
  complete a * complete (b + q.val - s) * complete d +
    complete a * bar q b * complete (q.val + d - s) -
    complete r * complete (a + b + q.val - r - s) * complete d -
    complete r * bar q (a + b - r) * complete (q.val + d - s) -
    complete s * complete a * complete (b + q.val + d - 2 * s) +
    complete r * complete s * complete (a + b + q.val + d - r - 2 * s)

noncomputable def intervalExtractionCubic (q : ℕ+) (b c d r s t : ℤ) : CompleteRing :=
  -complete b * bar q c * complete d +
    complete s * bar q (b + c - s) * complete d +
    complete t * complete b * complete (c + d - t) -
    complete r * complete (q.val + c - s) * complete d -
    complete s * complete t * complete (b + c + d - s - t) +
    complete r * complete t * complete (q.val + c + d - s - t)

theorem canonical_four_left_middle {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hb : P.r 1 = q.val) (hrs : P.g 0 = P.g 1) :
    canonicalPrimitive hP =
      leftMiddleCubic q (P.r 0) (P.r 2) (P.r 3) (P.g 0) (P.g 2) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hcon : monicContent hP = complete (P.g 0) := by
    rw [four_content hP, if_neg ha, if_pos (Or.inl ⟨hb, hrs⟩), ← hrs]
  have hm := monicContent_mul_canonicalPrimitive hP
  rw [hcon, restriction_four_expansion q P hP.thick] at hm
  simp only [fourInterval, hb, bar_cut, mul_zero, zero_mul, zero_sub, sub_zero, add_zero] at hm
  rw [bar_eq_complete_of_ne q (P.r 0) (by exact_mod_cast ha),
    bar_eq_complete_of_ne q (P.r 3) (by omega),
    bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1),
    bar_eq_complete_of_ne q (P.g 2) (by exact_mod_cast hP.gap_ne 2),
    bar_eq_complete_of_ne q ((P.r 0 : ℤ) + q.val - P.g 0) (by omega),
    bar_eq_complete_of_ne q ((q.val : ℤ) + P.r 2 - P.g 1) (by omega),
    bar_eq_complete_of_ne q ((P.r 0 : ℤ) + q.val + P.r 2 - P.g 0 - P.g 1) (by omega),
    bar_eq_complete_of_ne q ((P.r 2 : ℤ) + P.r 3 - P.g 2) (by omega),
    bar_eq_complete_of_ne q ((q.val : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2) (by omega),
    bar_eq_complete_of_ne q
      ((P.r 0 : ℤ) + q.val + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2) (by omega)] at hm
  apply mul_left_cancel₀ ((complete_ne_zero_iff (P.g 0)).mpr (by positivity))
  rw [hm]
  simp only [leftMiddleCubic, hrs]
  have hx : (P.r 0 : ℤ) + q.val + P.r 2 - P.g 1 - P.g 1 =
      (P.r 0 : ℤ) + q.val + P.r 2 - 2 * P.g 1 := by ring
  have hf : (P.r 0 : ℤ) + q.val + P.r 2 + P.r 3 - P.g 1 - P.g 1 - P.g 2 =
      (P.r 0 : ℤ) + q.val + P.r 2 + P.r 3 - 2 * P.g 1 - P.g 2 := by ring
  rw [hx, hf]
  norm_num
  ring

theorem canonical_four_right_middle {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hc : P.r 2 = q.val) (hst : P.g 1 = P.g 2) :
    canonicalPrimitive hP =
      rightMiddleCubic q (P.r 0) (P.r 1) (P.r 3) (P.g 0) (P.g 1) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hcon : monicContent hP = complete (P.g 1) := by
    rw [four_content hP, if_neg ha, if_pos (Or.inr (Or.inl ⟨hc, hst⟩))]
  have hm := monicContent_mul_canonicalPrimitive hP
  rw [hcon, restriction_four_expansion q P hP.thick] at hm
  simp only [fourInterval, hc, bar_cut, mul_zero, zero_mul, zero_sub, sub_zero, add_zero] at hm
  rw [bar_eq_complete_of_ne q (P.r 0) (by exact_mod_cast ha),
    bar_eq_complete_of_ne q (P.r 3) (by omega),
    bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1),
    bar_eq_complete_of_ne q (P.g 2) (by exact_mod_cast hP.gap_ne 2),
    bar_eq_complete_of_ne q ((P.r 1 : ℤ) + q.val - P.g 1) (by omega),
    bar_eq_complete_of_ne q ((q.val : ℤ) + P.r 3 - P.g 2) (by omega),
    bar_eq_complete_of_ne q ((P.r 0 : ℤ) + P.r 1 + q.val - P.g 0 - P.g 1) (by omega),
    bar_eq_complete_of_ne q ((P.r 1 : ℤ) + q.val + P.r 3 - P.g 1 - P.g 2) (by omega),
    bar_eq_complete_of_ne q
      ((P.r 0 : ℤ) + P.r 1 + q.val + P.r 3 - P.g 0 - P.g 1 - P.g 2) (by omega)] at hm
  apply mul_left_cancel₀ ((complete_ne_zero_iff (P.g 1)).mpr (by positivity))
  rw [hm]
  simp only [rightMiddleCubic, ← hst]
  have hy : (P.r 1 : ℤ) + q.val + P.r 3 - P.g 1 - P.g 1 =
      (P.r 1 : ℤ) + q.val + P.r 3 - 2 * P.g 1 := by ring
  have hf : (P.r 0 : ℤ) + P.r 1 + q.val + P.r 3 - P.g 0 - P.g 1 - P.g 1 =
      (P.r 0 : ℤ) + P.r 1 + q.val + P.r 3 - P.g 0 - 2 * P.g 1 := by ring
  rw [hy, hf]
  norm_num
  ring

theorem canonical_four_interval_extraction {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) (has : P.r 0 = P.g 1) :
    canonicalPrimitive hP =
      intervalExtractionCubic q (P.r 1) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hbne : P.r 1 ≠ q.val := by omega
  have hcon : monicContent hP = complete (P.g 1) := by
    rw [four_content hP, if_neg ha, if_pos (Or.inr (Or.inr ⟨hu, has⟩))]
  have hm := monicContent_mul_canonicalPrimitive hP
  rw [hcon, restriction_four_expansion q P hP.thick] at hm
  simp only [fourInterval, hu, bar_cut, mul_zero, zero_mul, sub_zero, add_zero] at hm
  rw [bar_eq_complete_of_ne q (P.r 0) (by exact_mod_cast ha),
    bar_eq_complete_of_ne q (P.r 1) (by exact_mod_cast hbne),
    bar_eq_complete_of_ne q (P.r 3) (by omega),
    bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1),
    bar_eq_complete_of_ne q (P.g 2) (by exact_mod_cast hP.gap_ne 2),
    bar_eq_complete_of_ne q ((P.r 2 : ℤ) + P.r 3 - P.g 2) (by omega),
    bar_eq_complete_of_ne q
      ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) (by omega),
    bar_eq_complete_of_ne q ((P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2) (by omega),
    bar_eq_complete_of_ne q
      ((P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2) (by omega)] at hm
  apply mul_left_cancel₀ ((complete_ne_zero_iff (P.g 1)).mpr (by positivity))
  rw [hm]
  simp only [intervalExtractionCubic, has]
  have hx : (P.g 1 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 =
      (q.val : ℤ) + P.r 2 - P.g 1 := by omega
  have hf : (P.g 1 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 =
      (q.val : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 := by omega
  rw [hx, hf]
  norm_num
  ring

theorem left_middle_collectedNorm (q : ℕ+) (a c d r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hq : 2 * r < q.val)
    (hc : r + t < c) (hd : (q.val : ℤ) + t < d) :
    collectedNorm (leftMiddleCubic q a c d r t) =
      if c = (q.val : ℤ) then 5 else 6 := by
  classical
  let P := leftMiddlePositive q.val a c d r t
  let N := leftMiddleNegative q.val a c d r t
  have hP : ∀ i j, 0 < P i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [P, leftMiddlePositive] <;> omega
  have hN : ∀ i j, 0 < N i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [N, leftMiddleNegative] <;> omega
  have hne : ∀ i j, tripleTerm (P i) ≠ tripleTerm (N j) :=
    left_middle_opposite_ne q.val a c d r t hr ht ha hq hc hd
  by_cases hcq : c = (q.val : ℤ)
  · rw [if_pos hcq]
    let P' : Fin 2 → Fin 3 → ℤ := fun i => P i.succ
    have hb : bar q c = 0 := by rw [hcq, bar_cut]
    have he : leftMiddleCubic q a c d r t =
        (∑ i : Fin 2, tripleTerm (P' i)) - ∑ j : Fin 3, tripleTerm (N j) := by
      simp only [leftMiddleCubic, hb, zero_mul, zero_add, P', P, N,
        leftMiddlePositive, leftMiddleNegative, Fin.sum_univ_two, Fin.sum_univ_three,
        tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Fin.reduceFinMk, Fin.succ_zero_eq_one', Fin.succ_one_eq_two', add_zero]
      ring
    rw [he]
    have hnorm := collectedNorm_signed_triples P' N
      (fun i j => hP i.succ j) hN (fun i j => hne i.succ j)
    norm_num only [Nat.cast_ofNat] at hnorm
    exact hnorm
  · rw [if_neg hcq]
    have he : leftMiddleCubic q a c d r t =
        (∑ i : Fin 3, tripleTerm (P i)) - ∑ j : Fin 3, tripleTerm (N j) := by
      rw [leftMiddleCubic, bar_eq_complete_of_ne q c hcq]
      simp only [P, N, leftMiddlePositive, leftMiddleNegative, Fin.sum_univ_three,
        tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Fin.reduceFinMk]
      ring
    rw [he]
    have hnorm := collectedNorm_signed_triples P N hP hN hne
    norm_num only [Nat.cast_ofNat] at hnorm
    exact hnorm

theorem interval_extraction_collectedNorm (q : ℕ+) (b c d r s t : ℤ)
    (hr : 0 < r) (hrs : r < s) (ht : 0 < t)
    (hb : r + s < b) (hu : s + b - r = q.val)
    (hc : s + t < c) (hd : (q.val : ℤ) + t < d) :
    collectedNorm (intervalExtractionCubic q b c d r s t) =
      if c = (q.val : ℤ) ∨ b + c - s = (q.val : ℤ) then 5 else 6 := by
  classical
  let P := intervalPositive q.val b c d r s t
  let N := intervalNegative q.val b c d r s t
  have hP : ∀ i j, 0 < P i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [P, intervalPositive] <;> omega
  have hN : ∀ i j, 0 < N i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [N, intervalNegative] <;> omega
  have hne : ∀ i j, tripleTerm (P i) ≠ tripleTerm (N j) :=
    interval_opposite_ne q.val b c d r s t hr hrs ht hb hu hc hd
  by_cases hcq : c = (q.val : ℤ)
  · rw [if_pos (Or.inl hcq)]
    let N' : Fin 2 → Fin 3 → ℤ := fun i => N i.succ
    have hC : bar q c = 0 := by rw [hcq, bar_cut]
    have hv : b + c - s ≠ (q.val : ℤ) := by omega
    have he : intervalExtractionCubic q b c d r s t =
        (∑ i : Fin 3, tripleTerm (P i)) - ∑ j : Fin 2, tripleTerm (N' j) := by
      rw [intervalExtractionCubic, hC, bar_eq_complete_of_ne q _ hv]
      simp only [zero_mul, mul_zero, zero_add, zero_sub, P, N, N',
        intervalPositive, intervalNegative, Fin.sum_univ_three, Fin.sum_univ_two,
        tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Fin.reduceFinMk, Fin.succ_zero_eq_one', Fin.succ_one_eq_two', add_zero]
      ring
    rw [he]
    have hnorm := collectedNorm_signed_triples P N' hP
      (fun i j => hN i.succ j) (fun i j => hne i j.succ)
    norm_num only [Nat.cast_ofNat] at hnorm
    exact hnorm
  · by_cases hvq : b + c - s = (q.val : ℤ)
    · rw [if_pos (Or.inr hvq)]
      let P' : Fin 2 → Fin 3 → ℤ := fun i => P i.succ
      have hv : bar q (b + c - s) = 0 := by rw [hvq, bar_cut]
      have he : intervalExtractionCubic q b c d r s t =
          (∑ i : Fin 2, tripleTerm (P' i)) - ∑ j : Fin 3, tripleTerm (N j) := by
        rw [intervalExtractionCubic, bar_eq_complete_of_ne q c hcq, hv]
        simp only [zero_mul, mul_zero, add_zero, P, P', N, intervalPositive,
          intervalNegative, Fin.sum_univ_two, Fin.sum_univ_three, tripleTerm,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk,
          Fin.succ_zero_eq_one', Fin.succ_one_eq_two']
        ring
      rw [he]
      have hnorm := collectedNorm_signed_triples P' N
        (fun i j => hP i.succ j) hN (fun i j => hne i.succ j)
      norm_num only [Nat.cast_ofNat] at hnorm
      exact hnorm
    · rw [if_neg (by tauto)]
      have he : intervalExtractionCubic q b c d r s t =
          (∑ i : Fin 3, tripleTerm (P i)) - ∑ j : Fin 3, tripleTerm (N j) := by
        rw [intervalExtractionCubic, bar_eq_complete_of_ne q c hcq,
          bar_eq_complete_of_ne q _ hvq]
        simp only [P, N, intervalPositive, intervalNegative, Fin.sum_univ_three,
          tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val, Fin.reduceFinMk]
        ring
      rw [he]
      have hnorm := collectedNorm_signed_triples P N hP hN hne
      norm_num only [Nat.cast_ofNat] at hnorm
      exact hnorm

theorem right_middle_collectedNorm_of_not_exception (q : ℕ+) (a b d r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ha : r < a)
    (hb : r + s < b) (hq : 2 * s < q.val) (hd : (q.val : ℤ) + s < d)
    (hex : ¬ (d = r ∧ a = (q.val : ℤ) + r - s)) :
    collectedNorm (rightMiddleCubic q a b d r s) =
      if b = (q.val : ℤ) ∨ a + b - r = (q.val : ℤ) then 5 else 6 := by
  classical
  let P := rightMiddlePositive q.val a b d r s
  let N := rightMiddleNegative q.val a b d r s
  have hP : ∀ i j, 0 < P i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [P, rightMiddlePositive] <;> omega
  have hN : ∀ i j, 0 < N i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [N, rightMiddleNegative] <;> omega
  have hne : ∀ i j, tripleTerm (P i) ≠ tripleTerm (N j) := by
    intro i j he
    obtain ⟨_, _, h1, h2⟩ := right_middle_opposite_locus q.val a b d r s hr hs ha hb hq hd i j he
    exact hex ⟨h1, h2⟩
  by_cases hbq : b = (q.val : ℤ)
  · rw [if_pos (Or.inl hbq)]
    let sel : Fin 2 → Fin 3 := ![0, 2]
    let P' : Fin 2 → Fin 3 → ℤ := fun i => P (sel i)
    have hB : bar q b = 0 := by rw [hbq, bar_cut]
    have hu : a + b - r ≠ (q.val : ℤ) := by omega
    have he : rightMiddleCubic q a b d r s =
        (∑ i : Fin 2, tripleTerm (P' i)) - ∑ j : Fin 3, tripleTerm (N j) := by
      rw [rightMiddleCubic, hB, bar_eq_complete_of_ne q _ hu]
      simp only [zero_mul, mul_zero, add_zero, P, P', N, sel, rightMiddlePositive,
        rightMiddleNegative, Fin.sum_univ_two, Fin.sum_univ_three, tripleTerm,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk]
      ring
    rw [he]
    have hnorm := collectedNorm_signed_triples P' N
      (fun i j => hP (sel i) j) hN (fun i j => hne (sel i) j)
    norm_num only [Nat.cast_ofNat] at hnorm
    exact hnorm
  · by_cases huq : a + b - r = (q.val : ℤ)
    · rw [if_pos (Or.inr huq)]
      let sel : Fin 2 → Fin 3 := ![0, 2]
      let N' : Fin 2 → Fin 3 → ℤ := fun i => N (sel i)
      have hU : bar q (a + b - r) = 0 := by rw [huq, bar_cut]
      have he : rightMiddleCubic q a b d r s =
          (∑ i : Fin 3, tripleTerm (P i)) - ∑ j : Fin 2, tripleTerm (N' j) := by
        rw [rightMiddleCubic, bar_eq_complete_of_ne q b hbq, hU]
        simp only [zero_mul, mul_zero, sub_zero, P, N, N', sel, rightMiddlePositive,
          rightMiddleNegative, Fin.sum_univ_three, Fin.sum_univ_two, tripleTerm,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk, add_zero]
        ring
      rw [he]
      have hnorm := collectedNorm_signed_triples P N' hP
        (fun i j => hN (sel i) j) (fun i j => hne i (sel j))
      norm_num only [Nat.cast_ofNat] at hnorm
      exact hnorm
    · rw [if_neg (by tauto)]
      have he : rightMiddleCubic q a b d r s =
          (∑ i : Fin 3, tripleTerm (P i)) - ∑ j : Fin 3, tripleTerm (N j) := by
        rw [rightMiddleCubic, bar_eq_complete_of_ne q b hbq,
          bar_eq_complete_of_ne q _ huq]
        simp only [P, N, rightMiddlePositive, rightMiddleNegative, Fin.sum_univ_three,
          tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val, Fin.reduceFinMk]
        ring
      rw [he]
      have hnorm := collectedNorm_signed_triples P N hP hN hne
      norm_num only [Nat.cast_ofNat] at hnorm
      exact hnorm

noncomputable def exceptionCubic (q b r s : ℤ) : CompleteRing :=
  complete (q + r - s) ^ 2 * complete b -
    complete r ^ 2 * complete (b + 2 * q - 2 * s) -
    complete s * complete (q + r - s) * complete (b + r + q - 2 * s) +
    complete r * complete s * complete (b + r + 2 * q - 3 * s)

theorem right_middle_exception_expansion (q : ℕ+) (b r s : ℤ)
    (hs : 0 < s) (hq : 2 * s < q.val) (hr : (q.val : ℤ) + s < r) (hb : r + s < b) :
    rightMiddleCubic q ((q.val : ℤ) + r - s) b r r s = exceptionCubic q.val b r s := by
  rw [rightMiddleCubic, bar_eq_complete_of_ne q b (by omega),
    bar_eq_complete_of_ne q (((q.val : ℤ) + r - s) + b - r) (by omega)]
  have hu : (q.val : ℤ) + r - s + b - r = b + q.val - s := by ring
  have hx : (q.val : ℤ) + r - s + b + q.val - r - s = b + 2 * q.val - 2 * s := by ring
  have hy : b + (q.val : ℤ) + r - 2 * s = b + r + q.val - 2 * s := by ring
  have hf : (q.val : ℤ) + r - s + b + q.val + r - r - 2 * s =
      b + r + 2 * q.val - 3 * s := by ring
  rw [hu, hx, hy, hf]
  unfold exceptionCubic
  ring

theorem exceptionCubic_augmentation (q b r s : ℤ)
    (hs : 0 < s) (hq : 2 * s < q) (hr : q + s < r) (hb : r + s < b) :
    residualAugmentation (exceptionCubic q b r s) = 0 := by
  simp only [exceptionCubic, map_add, map_sub, map_mul, map_pow,
    residualAugmentation_complete (show 0 < q + r - s by omega),
    residualAugmentation_complete (show 0 < b by omega),
    residualAugmentation_complete (show 0 < r by omega),
    residualAugmentation_complete hs,
    residualAugmentation_complete (show 0 < b + 2 * q - 2 * s by omega),
    residualAugmentation_complete (show 0 < b + r + q - 2 * s by omega),
    residualAugmentation_complete (show 0 < b + r + 2 * q - 3 * s by omega)]
  norm_num

theorem three_interval_top (a b c r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ha : r < a) (hb : r + s < b) (hc : s < c)
    (v : ℕ+) (hv : (v.val : ℤ) = a + b + c - r - s) :
    MvPolynomial.pderiv v (threeInterval complete a b c r s) = complete r * complete s := by
  simp only [threeInterval, map_add, map_sub, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, hv, if_pos rfl, ite_true, ite_false,
    if_neg (show a ≠ a + b + c - r - s by omega),
    if_neg (show b ≠ a + b + c - r - s by omega),
    if_neg (show c ≠ a + b + c - r - s by omega),
    if_neg (show r ≠ a + b + c - r - s by omega),
    if_neg (show s ≠ a + b + c - r - s by omega),
    if_neg (show a + b - r ≠ a + b + c - r - s by omega),
    if_neg (show b + c - s ≠ a + b + c - r - s by omega)]
  ring

theorem three_interval_above (a b c r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ha : r < a) (hb : r + s < b) (hc : s < c)
    (v : ℕ+) (hv : a + b + c - r - s < (v.val : ℤ)) :
    MvPolynomial.pderiv v (threeInterval complete a b c r s) = 0 := by
  simp only [threeInterval, map_add, map_sub, MvPolynomial.pderiv_mul,
    residual_pderiv_complete,
    if_neg (show a ≠ (v.val : ℤ) by omega), if_neg (show b ≠ (v.val : ℤ) by omega),
    if_neg (show c ≠ (v.val : ℤ) by omega), if_neg (show r ≠ (v.val : ℤ) by omega),
    if_neg (show s ≠ (v.val : ℤ) by omega),
    if_neg (show a + b - r ≠ (v.val : ℤ) by omega),
    if_neg (show b + c - s ≠ (v.val : ℤ) by omega),
    if_neg (show a + b + c - r - s ≠ (v.val : ℤ) by omega)]
  ring

theorem exceptionCubic_top (q b r s : ℤ)
    (hs : 0 < s) (hq : 2 * s < q) (hr : q + s < r) (hb : r + s < b)
    (v : ℕ+) (hv : (v.val : ℤ) = b + r + 2 * q - 3 * s) :
    MvPolynomial.pderiv v (exceptionCubic q b r s) = complete r * complete s := by
  simp only [exceptionCubic, pow_two, map_add, map_sub, MvPolynomial.pderiv_mul,
    residual_pderiv_complete, hv, if_pos rfl, ite_true, ite_false,
    if_neg (show q + r - s ≠ b + r + 2 * q - 3 * s by omega),
    if_neg (show b ≠ b + r + 2 * q - 3 * s by omega),
    if_neg (show r ≠ b + r + 2 * q - 3 * s by omega),
    if_neg (show s ≠ b + r + 2 * q - 3 * s by omega),
    if_neg (show b + 2 * q - 2 * s ≠ b + r + 2 * q - 3 * s by omega),
    if_neg (show b + r + q - 2 * s ≠ b + r + 2 * q - 3 * s by omega)]
  ring

theorem exceptionCubic_above (q b r s : ℤ)
    (hs : 0 < s) (hq : 2 * s < q) (hr : q + s < r) (hb : r + s < b)
    (v : ℕ+) (hv : b + r + 2 * q - 3 * s < (v.val : ℤ)) :
    MvPolynomial.pderiv v (exceptionCubic q b r s) = 0 := by
  simp only [exceptionCubic, pow_two, map_add, map_sub, MvPolynomial.pderiv_mul,
    residual_pderiv_complete,
    if_neg (show q + r - s ≠ (v.val : ℤ) by omega),
    if_neg (show b ≠ (v.val : ℤ) by omega), if_neg (show r ≠ (v.val : ℤ) by omega),
    if_neg (show s ≠ (v.val : ℤ) by omega),
    if_neg (show b + 2 * q - 2 * s ≠ (v.val : ℤ) by omega),
    if_neg (show b + r + q - 2 * s ≠ (v.val : ℤ) by omega),
    if_neg (show b + r + 2 * q - 3 * s ≠ (v.val : ℤ) by omega)]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- The norm-four right-middle exception is not an actual full three-row
function.  The signed monomial inventory proves the row-factor obstruction. -/
theorem exception_cubic_not_three_full (q b r s A B C R S : ℤ)
    (hs : 0 < s) (hq : 2 * s < q) (hr : q + s < r) (hb : r + s < b)
    (hR : 0 < R) (hS : 0 < S) (hA : R < A) (hB : R + S < B) (hC : q + S < C) :
    exceptionCubic q b r s ≠ threeInterval complete A B C R S := by
  intro he
  have hp := private_top_reading _ _ (b + r + 2 * q - 3 * s) (A + B + C - R - S)
    (complete r * complete s) (complete R * complete S)
    (by omega) (by omega)
    (mul_ne_zero ((complete_ne_zero_iff r).mpr (by omega)) ((complete_ne_zero_iff s).mpr hs.le))
    (mul_ne_zero ((complete_ne_zero_iff R).mpr hR.le) ((complete_ne_zero_iff S).mpr hS.le))
    (exceptionCubic_top q b r s hs hq hr hb)
    (three_interval_top A B C R S hR hS hA hB (by omega))
    (exceptionCubic_above q b r s hs hq hr hb)
    (three_interval_above A B C R S hR hS hA hB (by omega)) he
  have hgap := complete_two_product_reading (show 0 < r by omega) hs hR hS hp.2
  let T : Fin 3 → Fin 3 → ℤ :=
    ![![q + r - s, q + r - s, b], ![R, A + B - R, C], ![S, A, B + C - S]]
  let U : Fin 3 → Fin 3 → ℤ :=
    ![![A, B, C], ![r, r, b + 2 * q - 2 * s],
      ![s, q + r - s, b + r + q - 2 * s]]
  have hT : ∀ i j, 0 < T i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [T] <;> omega
  have hU : ∀ i j, 0 < U i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [U] <;> omega
  have hsum : tripleTerm (T 0) + tripleTerm (T 1) + tripleTerm (T 2) =
      tripleTerm (U 0) + tripleTerm (U 1) + tripleTerm (U 2) := by
    unfold exceptionCubic threeInterval at he
    rw [hp.1] at he
    have hlead := congrArg (fun p : CompleteRing => p * complete (A + B + C - R - S)) hp.2
    simp only [T, U, tripleTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    simp only [pow_two] at he
    linear_combination he - hlead
  have hmon := FourRowHessenberg.three_sum_reading T U hT hU (by
    change tripleTerm (T 0) + tripleTerm (T 1) + tripleTerm (T 2) =
      tripleTerm (U 0) + tripleTerm (U 1) + tripleTerm (U 2)
    exact hsum)
  rcases hgap with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩ <;>
    unfold FourRowHessenberg.threeMatches at hmon <;>
    rcases hmon with ⟨hm0, hrest⟩ | ⟨hm0, hrest⟩ | ⟨hm0, hrest⟩ <;>
    rcases hrest with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩ <;>
    simp only [T, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hm0 hm1 hm2 <;>
    unfold FourRowHessenberg.tripleMatch at hm0 hm1 hm2 <;>
    rcases hm0 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> try omega <;>
    rcases hm1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> try omega <;>
    rcases hm2 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- Cubic degree and a surviving first row produce exactly the three middle
extraction mechanisms in the actual four-row content table. -/
theorem four_nonendpoint_cubic_cases {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hd : (canonicalPrimitive hP).totalDegree = 3) :
    (P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
      (P.r 2 = q.val ∧ P.g 1 = P.g 2) ∨
      ((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 0 = P.g 1) := by
  have hdeg := content_degree_add_canonical_degree hP
  rw [hd] at hdeg
  by_contra hn
  rw [four_content hP, if_neg ha, if_neg hn, MvPolynomial.totalDegree_one] at hdeg
  omega

theorem four_right_exception_not_three_cubic {q : ℕ+} {P : Profile 3} {Q : Profile 2}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 ≠ q.val) (hc : P.r 2 = q.val) (hst : P.g 1 = P.g 2)
    (hde : P.r 3 = P.g 0)
    (hae : (P.r 0 : ℤ) = (q.val : ℤ) + P.g 0 - P.g 1)
    (hdQ : (canonicalPrimitive hQ).totalDegree = 3) :
    canonicalPrimitive hP ≠ canonicalPrimitive hQ := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hsPos : (0 : ℤ) < P.g 1 := by exact_mod_cast hP.gap_pos 1
  have hq2s : 2 * (P.g 1 : ℤ) < q.val := by omega
  have hrBig : (q.val : ℤ) + P.g 1 < P.g 0 := by omega
  have hp : canonicalPrimitive hP = exceptionCubic q.val (P.r 1) (P.g 0) (P.g 1) := by
    rw [canonical_four_right_middle hP ha hc hst, hde, hae]
    exact right_middle_exception_expansion q (P.r 1) (P.g 0) (P.g 1) hsPos hq2s hrBig hb'
  have haugP : residualAugmentation (canonicalPrimitive hP) = 0 := by
    rw [hp]
    exact exceptionCubic_augmentation q.val (P.r 1) (P.g 0) (P.g 1) hsPos hq2s hrBig hb'
  intro he
  have haug := congrArg residualAugmentation he
  rw [haugP] at haug
  rcases three_cubic_contact_cases hQ hdQ with hfree | ⟨hA, hB, hRS⟩ | ⟨hU, hAS⟩
  · have hcon := (three_cubic_nonextraction hQ hdQ).1
    have hQcan := monicContent_mul_canonicalPrimitive hQ
    rw [hcon, one_mul, restriction_eq_full_of_no_entry_contact hfree] at hQcan
    norm_num at hQcan
    rw [hp, hQcan, three_full_interval hQ] at he
    have hmid := hQ.thick 0 1 (by decide)
    change Q.g 0 + Q.g 1 < Q.r 1 at hmid
    have hQbottom : q.val + Q.g 1 < Q.r 2 := by
      simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
    exact exception_cubic_not_three_full q.val (P.r 1) (P.g 0) (P.g 1)
      (Q.r 0) (Q.r 1) (Q.r 2) (Q.g 0) (Q.g 1) hsPos hq2s hrBig hb'
      (by exact_mod_cast hQ.gap_pos 0) (by exact_mod_cast hQ.gap_pos 1)
      (by exact_mod_cast Q.g_lt_castSucc 0) (by exact_mod_cast hmid)
      (by exact_mod_cast hQbottom) he
  · rw [three_cubic_middle_augmentation hQ hA hB hRS] at haug
    norm_num at haug
  · rw [three_cubic_interval_augmentation hQ hU hAS] at haug
    norm_num at haug

/-- Uniform cross-size necessity for actual canonical cubics.  Nonendpoint
mechanisms are excluded by collected norms, including the norm-four exception. -/
theorem cross_size_cubic_match {q : ℕ+} {P : Profile 3} {Q : Profile 2}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hdP : (canonicalPrimitive hP).totalDegree = 3)
    (hdQ : (canonicalPrimitive hQ).totalDegree = 3)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ) :
    P.r 0 = q.val ∧
      (GeneralHessenberg.contract P 0 = Q ∨ GeneralHessenberg.contract P 0 = Q.rotate) := by
  have hthree := three_primitive_cubic_norm_le hQ hdQ
  have ha : P.r 0 = q.val := by
    by_contra ha
    have hdom := P.four_domain hP.thick.hessenberg
    rcases hdom with ⟨hr, hs, ht, ha', hb', hc', hd⟩
    have hbottom : q.val + P.g 2 < P.r 3 := by
      simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
    rcases four_nonendpoint_cubic_cases hP ha hdP with ⟨hb, hrs⟩ | ⟨hc, hst⟩ | ⟨hu, has⟩
    · have hnorm := left_middle_collectedNorm q (P.r 0) (P.r 2) (P.r 3) (P.g 0) (P.g 2)
        (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 2)
        ha' (by omega) (by omega) (by exact_mod_cast hbottom)
      rw [← canonical_four_left_middle hP ha hb hrs, he] at hnorm
      split_ifs at hnorm <;> linarith
    · by_cases hex : P.r 3 = P.g 0 ∧
          (P.r 0 : ℤ) = (q.val : ℤ) + P.g 0 - P.g 1
      · exact four_right_exception_not_three_cubic hP hQ ha hc hst hex.1 hex.2 hdQ he
      · have hnorm := right_middle_collectedNorm_of_not_exception q
          (P.r 0) (P.r 1) (P.r 3) (P.g 0) (P.g 1)
          (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
          ha' hb' (by omega) (by omega) (by
            intro hx
            apply hex
            exact ⟨by exact_mod_cast hx.1, hx.2⟩)
        rw [← canonical_four_right_middle hP ha hc hst, he] at hnorm
        split_ifs at hnorm <;> linarith
    · have hrs : P.g 0 < P.g 1 := by have := P.g_lt_castSucc 0; omega
      have hnorm := interval_extraction_collectedNorm q
        (P.r 1) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2)
        (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hrs)
        (by exact_mod_cast hP.gap_pos 2) hb' (by omega) hc'
        (by exact_mod_cast hbottom)
      rw [← canonical_four_interval_extraction hP ha hu has, he] at hnorm
      split_ifs at hnorm <;> linarith
  refine ⟨ha, ?_⟩
  have hC := four_endpoint_contract_component hP ha
  have hdC : (canonicalPrimitive hC).totalDegree = 3 := by
    rw [← four_endpoint_contract_canonical hP ha]
    exact hdP
  have heC : canonicalPrimitive hC = canonicalPrimitive hQ := by
    rw [← four_endpoint_contract_canonical hP ha]
    exact he
  exact three_primitive_cubic_rigidity hC hQ hdC hdQ heC

/-- Equality of actual restrictions identifies their normalized irreducible
factors; no alternative factorization is supplied as a hypothesis. -/
theorem canonical_eq_of_restriction_eq {n m : ℕ} {q : ℕ+}
    {P : Profile n} {Q : Profile m} (hP : QComponent q P) (hQ : QComponent q Q)
    (he : restriction q P = restriction q Q) :
    canonicalPrimitive hP = canonicalPrimitive hQ := by
  have hp : Prime (canonicalPrimitive hP) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (canonicalPrimitive_irreducible hP)
  have hdiv : canonicalPrimitive hP ∣ monicContent hQ * monicPrimitive hQ := by
    rw [← restriction_eq_monicContent_mul hQ, ← he]
    exact canonicalPrimitive_dvd_restriction hP
  have hnot : ¬ canonicalPrimitive hP ∣ monicContent hQ := by
    intro hd
    have hC : monicContent hQ ≠ 0 := by simp [monicContent, MvPolynomial.monomial_eq_zero]
    have hfull : q.val < (fullGenerator P).val := by
      have h := fullIndex_gt_q hP
      rw [← fullGenerator_int_coe P] at h
      exact_mod_cast h
    have hvar := not_mem_vars_of_dvd hC hd (fullGenerator P)
      (not_mem_monicContent_above_cut hQ (fullGenerator P) hfull)
    exact hvar (full_mem_canonicalPrimitive hP)
  have hL : canonicalPrimitive hP ∣ monicPrimitive hQ :=
    (hp.dvd_or_dvd hdiv).resolve_left hnot
  have hPL : Associated (canonicalPrimitive hP) (monicPrimitive hQ) :=
    ((canonicalPrimitive_irreducible hP).dvd_irreducible_iff_associated
      (monicPrimitive_irreducible hQ)).mp hL
  have hQL : Associated (canonicalPrimitive hQ) (monicPrimitive hQ) := by
    exact associated_unit_mul_left (monicPrimitive hQ) ((-1 : CompleteRing) ^ m)
      (isUnit_neg_one.pow m)
  exact canonical_associated_eq hP hQ (hPL.trans hQL.symm)

theorem canonical_eq_of_profile_eq {n : ℕ} {q : ℕ+} {P Q : Profile n}
    (hP : QComponent q P) (hQ : QComponent q Q) (he : P = Q) :
    canonicalPrimitive hP = canonicalPrimitive hQ := by
  subst Q
  rfl

theorem restriction_rotate {n : ℕ} (q : ℕ+) (P : Profile n) :
    restriction q P.rotate = restriction q P := by
  unfold restriction
  rw [Profile.toBetaDiagram_schur, Profile.schur_rotate, Profile.toBetaDiagram_schur]

/-- Rotation covariance is derived on every orientation that is an actual
q-component; temporary orientations are not assigned this domain predicate. -/
theorem canonical_rotate_eq {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (hR : QComponent q P.rotate) :
    canonicalPrimitive hR = canonicalPrimitive hP :=
  canonical_eq_of_restriction_eq hR hP (restriction_rotate q P)

/-- Exact endpoint-lift cubic classification, with different endpoint gap
values allowed and all contraction/rotation domain conditions produced. -/
theorem endpoint_cubic_lifts_match_iff {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 = q.val) (hA : Q.r 0 = q.val)
    (hdP : (canonicalPrimitive hP).totalDegree = 3)
    (hdQ : (canonicalPrimitive hQ).totalDegree = 3) :
    canonicalPrimitive hP = canonicalPrimitive hQ ↔
      GeneralHessenberg.contract P 0 = GeneralHessenberg.contract Q 0 ∨
        GeneralHessenberg.contract P 0 = (GeneralHessenberg.contract Q 0).rotate := by
  have hC := four_endpoint_contract_component hP ha
  have hD := four_endpoint_contract_component hQ hA
  constructor
  · intro he
    have hdC : (canonicalPrimitive hC).totalDegree = 3 := by
      rw [← four_endpoint_contract_canonical hP ha]
      exact hdP
    have hdD : (canonicalPrimitive hD).totalDegree = 3 := by
      rw [← four_endpoint_contract_canonical hQ hA]
      exact hdQ
    rw [endpoint_lifts_match_iff hP hQ ha hA] at he
    exact three_primitive_cubic_rigidity hC hD hdC hdD he
  · intro he
    rw [endpoint_lifts_match_iff hP hQ ha hA]
    rcases he with he | he
    · exact canonical_eq_of_profile_eq hC hD he
    · have hR : QComponent q (GeneralHessenberg.contract Q 0).rotate := by
        rw [← he]
        exact hC
      exact (canonical_eq_of_profile_eq hC hR he).trans (canonical_rotate_eq hD hR)

def inRotationOrbit (P A : Profile 3) : Prop := P = A ∨ P = A.rotate

/-- Cross-orbit members of the actual residual rotation quadruple. -/
def residualQuartetAt (q : ℕ+) (P Q : Profile 3) (a r s : ℕ)
    (ha : r + s < a) (hq : r + s < q.val) : Prop :=
  (inRotationOrbit P (residualFamilyA a q.val r s ha hq) ∧
    inRotationOrbit Q (residualFamilyB a q.val r s ha hq)) ∨
  (inRotationOrbit P (residualFamilyB a q.val r s ha hq) ∧
    inRotationOrbit Q (residualFamilyA a q.val r s ha hq))

def cubicResidualQuartet (q : ℕ+) (P Q : Profile 3) : Prop :=
  ∃ a z : ℕ, ∃ ha : z + z < a, ∃ hq : z + z < q.val,
    0 < z ∧ a ≠ q.val ∧ residualQuartetAt q P Q a z z ha hq

def quarticResidualQuartet (q : ℕ+) (P Q : Profile 3) : Prop :=
  ∃ a r s : ℕ, ∃ ha : r + s < a, ∃ hq : r + s < q.val,
    0 < r ∧ 0 < s ∧ r ≠ s ∧ a ≠ q.val ∧ residualQuartetAt q P Q a r s ha hq

def cubicResidualAlternatives (q : ℕ+) (P Q : Profile 3) : Prop :=
  (P.r 0 = q.val ∧ Q.r 0 = q.val ∧
    (GeneralHessenberg.contract P 0 = GeneralHessenberg.contract Q 0 ∨
      GeneralHessenberg.contract P 0 = (GeneralHessenberg.contract Q 0).rotate)) ∨
  P = Q ∨ P = Q.rotate ∨ cubicResidualQuartet q P Q

def quarticResidualAlternatives (q : ℕ+) (P Q : Profile 3) : Prop :=
  P = Q ∨ P = Q.rotate ∨
    (NoEntryContact q P ∧ NoEntryContact q Q ∧ FourRowHessenberg.Classified P Q) ∨
      quarticResidualQuartet q P Q

/-- Four-row quartic degree proves that the actual monic content is one. -/
theorem four_quartic_content_one {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hd : (canonicalPrimitive hP).totalDegree = 4) :
    monicContent hP = 1 ∧ P.r 0 ≠ q.val := by
  have hdeg := content_degree_add_canonical_degree hP
  rw [hd] at hdeg
  have hgap (j : Fin 3) : (complete (P.g j)).totalDegree = 1 :=
    totalDegree_complete_pos _ (by exact_mod_cast hP.gap_pos j)
  have ha : P.r 0 ≠ q.val := by
    intro ha
    rw [four_content hP, if_pos ha] at hdeg
    have hprod : (complete (P.g 0) * complete (P.g 1)).totalDegree = 2 := by
      rw [MvPolynomial.totalDegree_mul_of_isDomain
        ((complete_ne_zero_iff _).mpr (by positivity))
        ((complete_ne_zero_iff _).mpr (by positivity)), hgap 0, hgap 1]
    split_ifs at hdeg <;> simp only [hgap, hprod] at hdeg <;> omega
  have hnot : ¬ ((P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
      (P.r 2 = q.val ∧ P.g 1 = P.g 2) ∨
      ((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 0 = P.g 1)) := by
    intro hc
    rw [four_content hP, if_neg ha, if_pos hc, hgap 1] at hdeg
    omega
  exact ⟨by rw [four_content hP, if_neg ha, if_neg hnot], ha⟩

theorem residualQuartetAt_restriction_eq {q : ℕ+} {P Q : Profile 3}
    {a r s : ℕ} {ha : r + s < a} {hq : r + s < q.val}
    (hr : 0 < r) (hs : 0 < s) (h : residualQuartetAt q P Q a r s ha hq) :
    restriction q P = restriction q Q := by
  have he := residualFamily_restriction_eq a q r s ha hq hr hs
  have horbit {P A : Profile 3} (h : inRotationOrbit P A) :
      restriction q P = restriction q A := by
    rcases h with h | h
    · rw [h]
    · rw [h, restriction_rotate]
  rcases h with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · exact (horbit hP).trans (he.trans (horbit hQ).symm)
  · exact (horbit hP).trans (he.symm.trans (horbit hQ).symm)

theorem cubicResidualQuartet_canonical_eq {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q) (h : cubicResidualQuartet q P Q) :
    canonicalPrimitive hP = canonicalPrimitive hQ := by
  obtain ⟨a, z, ha, hq, hz, hneq, h⟩ := h
  exact canonical_eq_of_restriction_eq hP hQ
    (residualQuartetAt_restriction_eq hz hz h)

theorem quarticResidualQuartet_canonical_eq {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q) (h : quarticResidualQuartet q P Q) :
    canonicalPrimitive hP = canonicalPrimitive hQ := by
  obtain ⟨a, r, s, ha, hq, hr, hs, hneq, haneq, h⟩ := h
  exact canonical_eq_of_restriction_eq hP hQ
    (residualQuartetAt_restriction_eq hr hs h)

/-- Every cubic alternative supplies equality of the actual normalized primitive. -/
theorem cubicResidualAlternatives_canonical_eq {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hdP : (canonicalPrimitive hP).totalDegree = 3)
    (hdQ : (canonicalPrimitive hQ).totalDegree = 3)
    (h : cubicResidualAlternatives q P Q) :
    canonicalPrimitive hP = canonicalPrimitive hQ := by
  rcases h with ⟨ha, hA, hsame⟩ | h | h | h
  · exact (endpoint_cubic_lifts_match_iff hP hQ ha hA hdP hdQ).mpr hsame
  · exact canonical_eq_of_profile_eq hP hQ h
  · have hR : QComponent q Q.rotate := by rw [← h]; exact hP
    exact (canonical_eq_of_profile_eq hP hR h).trans (canonical_rotate_eq hQ hR)
  · exact cubicResidualQuartet_canonical_eq hP hQ h

/-- Every quartic alternative supplies equality of the actual normalized primitive. -/
theorem quarticResidualAlternatives_canonical_eq {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (h : quarticResidualAlternatives q P Q) :
    canonicalPrimitive hP = canonicalPrimitive hQ := by
  rcases h with h | h | ⟨hfreeP, hfreeQ, hfull⟩ | h
  · exact canonical_eq_of_profile_eq hP hQ h
  · have hR : QComponent q Q.rotate := by rw [← h]; exact hP
    exact (canonical_eq_of_profile_eq hP hR h).trans (canonical_rotate_eq hQ hR)
  · exact (untouched_four_match_iff hP hQ hfreeP hfreeQ).mpr hfull
  · exact quarticResidualQuartet_canonical_eq hP hQ h

theorem four_quartic_nonextraction {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hd : (canonicalPrimitive hP).totalDegree = 4) :
    monicContent hP = 1 ∧ P.r 0 ≠ q.val ∧
      (P.r 1 = q.val → P.g 0 ≠ P.g 1) ∧
      (P.r 2 = q.val → P.g 1 ≠ P.g 2) ∧
      ((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val → P.r 0 ≠ P.g 1) := by
  obtain ⟨hcon, ha⟩ := four_quartic_content_one hP hd
  have hnot : ¬ ((P.r 1 = q.val ∧ P.g 0 = P.g 1) ∨
      (P.r 2 = q.val ∧ P.g 1 = P.g 2) ∨
      ((P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val ∧ P.r 0 = P.g 1)) := by
    intro hc
    have hdegree := content_degree_add_canonical_degree hP
    rw [four_content hP, if_neg ha, if_pos hc, hd,
      totalDegree_complete_pos (P.g 1) (by exact_mod_cast hP.gap_pos 1)] at hdegree
    omega
  refine ⟨hcon, ha, ?_, ?_, ?_⟩
  · intro hb hrs
    exact hnot (Or.inl ⟨hb, hrs⟩)
  · intro hc hst
    exact hnot (Or.inr (Or.inl ⟨hc, hst⟩))
  · intro hu has
    exact hnot (Or.inr (Or.inr ⟨hu, has⟩))

theorem four_quartic_restriction_eq {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ) :
    restriction q P = restriction q Q := by
  have hdQ : (canonicalPrimitive hQ).totalDegree = 4 := by rw [← he]; exact hd
  rw [restriction_eq_signed_content_mul_canonical hP,
    restriction_eq_signed_content_mul_canonical hQ,
    (four_quartic_content_one hP hd).1, (four_quartic_content_one hQ hdQ).1, he]


end SkewJacobiNegative.Staircase
