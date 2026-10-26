/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.HessenbergExpansion
import SkewJacobiNegative.NegativeInvariants
import SkewJacobiNegative.NonnegativeRigidity
import SkewJacobiNegative.SingletonLift
import SkewJacobiNegative.SmallRowRigidity

/-!
# Four-row Hessenberg profiles

The exceptional profiles and minimum-gap calculation in `app:four`,
`prop:four-rows`, and `eq:four-family` of
`shields-2026-skew-jacobi-negative.tex`.  Polynomial sufficiency and geometric
distinctness are separate statements.  Unit-variable shortening is performed
by an injective variable renaming in `HomLambda`.
-/

namespace SkewJacobiNegative
namespace FourRowHessenberg

open Gluing HessenbergExpansion

@[simp] private theorem fin4_mk_zero (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] private theorem fin4_mk_one (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] private theorem fin4_mk_two (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] private theorem fin4_mk_three (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] private theorem fin3_mk_zero (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] private theorem fin3_mk_one (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] private theorem fin3_mk_two (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl

/-- The first exceptional profile, including the common-beta boundary `c = 0`. -/
def familyF (w b c : ℕ) (hcw : c < w) (hb : c + w < b) : Profile 3 where
  r := ![w, b, b, b + w - c]
  g := ![c, c, w]
  r_pos := by intro i; fin_cases i <;> simp <;> omega
  g_lt_castSucc := by intro i; fin_cases i <;> simp <;> omega
  g_lt_succ := by intro i; fin_cases i <;> simp <;> omega

/-- The second exceptional profile. -/
def familyH (w b c : ℕ) (hcw : c < w) (hb : c + w < b) : Profile 3 where
  r := ![w, b, b + w - c, b]
  g := ![c, w, c]
  r_pos := by intro i; fin_cases i <;> simp <;> omega
  g_lt_castSucc := by intro i; fin_cases i <;> simp <;> omega
  g_lt_succ := by intro i; fin_cases i <;> simp <;> omega

/-- Both exceptional representatives satisfy the intrinsic Hessenberg condition. -/
theorem familyF_hessenberg (w b c : ℕ) (hcw : c < w) (hb : c + w < b) :
    (familyF w b c hcw hb).Hessenberg := by
  rw [Profile.hessenberg_four_iff]
  simp [familyF]
  omega

theorem familyH_hessenberg (w b c : ℕ) (hcw : c < w) (hb : c + w < b) :
    (familyH w b c hcw hb).Hessenberg := by
  rw [Profile.hessenberg_four_iff]
  simp [familyH]
  omega

/-- Sufficiency is an eight-term identity, valid for any complete-generator convention. -/
theorem family_interval_identity {R : Type*} [CommRing R] (h : ℤ → R)
    (w b c : ℤ) :
    fourInterval h w b b (b + w - c) c c w =
      fourInterval h w b (b + w - c) b c w c := by
  have h1 : w + b - c = b + w - c := by omega
  have h2 : b + (b + w - c) - w = b + b - c := by omega
  have h3 : b + w - c + b - c = b + b + w - c - c := by omega
  have h4 : w + b + (b + w - c) - c - w = w + b + b - c - c := by omega
  have h5 : b + b + (b + w - c) - c - w = b + (b + w - c) + b - w - c := by omega
  have h6 : w + b + b + (b + w - c) - c - c - w =
      w + b + (b + w - c) + b - c - w - c := by omega
  have h7 : b + b + w - c - c = w + b + b - c - c := by omega
  simp only [fourInterval, h1, h2, h3, h4, h5, h6, h7]
  ring

/-- The actual full polynomials agree, not merely a specialized cofactor or mask. -/
theorem family_schur_eq (w b c : ℕ) (hcw : c < w) (hb : c + w < b) :
    (familyF w b c hcw hb).schur = (familyH w b c hcw hb).schur := by
  rw [Profile.schur_four_interval _ (familyF_hessenberg w b c hcw hb),
    Profile.schur_four_interval _ (familyH_hessenberg w b c hcw hb)]
  have hn : ((b + w - c : ℕ) : ℤ) = (b : ℤ) + w - c := by omega
  simpa only [familyF, familyH, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, hn] using family_interval_identity hh (w : ℤ) (b : ℤ) (c : ℤ)

/-- Homogenized sufficiency retains `H_0` as an independent variable. -/
theorem family_schurHom_eq (w b c : ℕ) (hcw : c < w) (hb : c + w < b) :
    (familyF w b c hcw hb).schurHom = (familyH w b c hcw hb).schurHom :=
  (Profile.schur_eq_iff_schurHom_eq _ _).mp (family_schur_eq w b c hcw hb)

/-- The overlap words distinguish F from H even when some rows coincide. -/
theorem family_ne (w b c : ℕ) (hcw : c < w) (hb : c + w < b) :
    familyF w b c hcw hb ≠ familyH w b c hcw hb := by
  intro he
  have hg := congrArg (fun P : Profile 3 => P.g 1) he
  simp [familyF, familyH] at hg
  omega

/-- The two representatives also lie in different rotation orbits. -/
theorem family_ne_rotate (w b c : ℕ) (hcw : c < w) (hb : c + w < b) :
    familyF w b c hcw hb ≠ (familyH w b c hcw hb).rotate := by
  intro he
  have hg := congrArg (fun P : Profile 3 => P.g 1) he
  simp [familyF, familyH, Profile.rotate] at hg
  omega

/-- Each orbit contains two distinct profiles. -/
theorem familyF_not_symmetric (w b c : ℕ) (hcw : c < w) (hb : c + w < b) :
    familyF w b c hcw hb ≠ (familyF w b c hcw hb).rotate := by
  intro he
  have hg := congrArg (fun P : Profile 3 => P.g 0) he
  simp [familyF, Profile.rotate] at hg
  omega

theorem familyH_not_symmetric (w b c : ℕ) (hcw : c < w) (hb : c + w < b) :
    familyH w b c hcw hb ≠ (familyH w b c hcw hb).rotate := by
  intro he
  have hr := congrArg (fun P : Profile 3 => P.r 0) he
  simp [familyH, Profile.rotate] at hr
  omega

/-- Every intrinsic four-row Hessenberg profile has exactly these three negatives. -/
theorem negative_sites_hessenberg (P : Profile 3) (hP : P.Hessenberg) :
    negativeSites P.toBetaDiagram = {(2, 0), (3, 0), (3, 1)} := by
  classical
  have hidx := P.indices_four
  have hdom := P.four_domain hP
  rcases hdom with ⟨ha, hb, hd, hp, hq, hr, hs⟩
  ext ij
  rcases ij with ⟨i, j⟩
  rw [P.toBetaDiagram.mem_negativeSites]
  change (P.xi i < P.zeta j) ↔ _
  have hi := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M i j) hidx
  simp only [Matrix.of_apply] at hi
  rw [← sub_neg, hi]
  fin_cases i <;> fin_cases j
  all_goals norm_num [fourIndices]
  all_goals omega

/-- The negative count is intrinsic to the full arrays, not a chosen mask. -/
theorem negative_count_hessenberg (P : Profile 3) (hP : P.Hessenberg) :
    negativeCount P.toBetaDiagram = 3 := by
  rw [negativeCount, negative_sites_hessenberg P hP]
  decide

/-- Both exceptional families realize the claimed three-negative boundary. -/
theorem family_negative_counts (w b c : ℕ) (hcw : c < w) (hb : c + w < b) :
    negativeCount (familyF w b c hcw hb).toBetaDiagram = 3 ∧
      negativeCount (familyH w b c hcw hb).toBetaDiagram = 3 :=
  ⟨negative_count_hessenberg _ (familyF_hessenberg w b c hcw hb),
    negative_count_hessenberg _ (familyH_hessenberg w b c hcw hb)⟩

/-- Restoring a common shortening shifts every generator index, including zero. -/
noncomputable def restoreIndices (c : ℕ) : HomLambda →ₐ[ℚ] HomLambda :=
  MvPolynomial.rename (fun k => k + c)

/-- Independent H0 makes index restoration faithful without a unit-variable exception. -/
theorem restoreIndices_injective (c : ℕ) : Function.Injective (restoreIndices c) := by
  apply MvPolynomial.rename_injective
  intro i j hij
  change i + c = j + c at hij
  omega

/-- The shortening identity applies only to nonnegative generator indices. -/
theorem restore_hTilde (c : ℕ) (k : ℤ) (hk : 0 ≤ k) :
    restoreIndices c (hTilde k) = hTilde (k + c) := by
  have hkc : ¬ k + (c : ℤ) < 0 := by omega
  simp only [restoreIndices, hTilde, if_neg (not_lt.mpr hk), if_neg hkc,
    MvPolynomial.rename_X]
  congr 1
  omega

/-- Subtracting a minimum from all row and gap coordinates stays in the strict domain. -/
theorem shorten_domain {p q r s a b d c : ℤ}
    (h : FourDomain p q r s a b d) (hc : 0 ≤ c)
    (hca : c ≤ a) (hcb : c ≤ b) (hcd : c ≤ d) :
    FourDomain (p - c) (q - c) (r - c) (s - c) (a - c) (b - c) (d - c) := by
  rcases h with ⟨ha, hb, hd, hp, hq, hr, hs⟩
  unfold FourDomain
  omega

/-- Uniform three-minimum shortening restores the full degree-four interval polynomial. -/
theorem restore_uniform_interval (c : ℕ) (p q r s : ℤ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s) :
    restoreIndices c (fourInterval hTilde p q r s 0 0 0) =
      fourInterval hTilde (p + c) (q + c) (r + c) (s + c) c c c := by
  have h1 : p + (c : ℤ) + (q + c) - c = p + q + c := by omega
  have h2 : q + (c : ℤ) + (r + c) - c = q + r + c := by omega
  have h3 : r + (c : ℤ) + (s + c) - c = r + s + c := by omega
  have h4 : p + (c : ℤ) + (q + c) + (r + c) - c - c = p + q + r + c := by omega
  have h5 : q + (c : ℤ) + (r + c) + (s + c) - c - c = q + r + s + c := by omega
  have h6 : p + (c : ℤ) + (q + c) + (r + c) + (s + c) - c - c - c =
      p + q + r + s + c := by omega
  simp only [fourInterval, map_sub, map_add, map_mul, sub_zero, add_zero, zero_add,
    restore_hTilde c p hp.le, restore_hTilde c q hq.le,
    restore_hTilde c r hr.le, restore_hTilde c s hs.le,
    restore_hTilde c 0 (by omega),
    restore_hTilde c (p + q) (by omega),
    restore_hTilde c (q + r) (by omega),
    restore_hTilde c (r + s) (by omega),
    restore_hTilde c (p + q + r) (by omega),
    restore_hTilde c (q + r + s) (by omega),
    restore_hTilde c (p + q + r + s) (by omega), h1, h2, h3, h4, h5, h6]

/-- Three-minimum equality is exactly ribbon equality with independent unit variables. -/
theorem uniform_interval_eq_iff (c : ℕ) (p q r s P Q R S : ℤ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (hP : 0 < P) (hQ : 0 < Q) (hR : 0 < R) (hS : 0 < S) :
    fourInterval hTilde (p + c) (q + c) (r + c) (s + c) c c c =
      fourInterval hTilde (P + c) (Q + c) (R + c) (S + c) c c c ↔
    fourInterval hTilde p q r s 0 0 0 = fourInterval hTilde P Q R S 0 0 0 := by
  rw [← restore_uniform_interval c p q r s hp hq hr hs,
    ← restore_uniform_interval c P Q R S hP hQ hR hS]
  exact (restoreIndices_injective c).eq_iff

/-- Three independent factors match with multiplicity, without a distinctness hypothesis. -/
def tripleMatch (a b c d e f : ℤ) : Prop :=
  (a = d ∧ b = e ∧ c = f) ∨ (a = d ∧ b = f ∧ c = e) ∨
  (a = e ∧ b = d ∧ c = f) ∨ (a = e ∧ b = f ∧ c = d) ∨
  (a = f ∧ b = d ∧ c = e) ∨ (a = f ∧ b = e ∧ c = d)

/-- All structural permutations of a four-factor product. -/
def fourMatch (a b c d A B C D : ℤ) : Prop :=
  (a = A ∧ tripleMatch b c d B C D) ∨
  (a = B ∧ tripleMatch b c d A C D) ∨
  (a = C ∧ tripleMatch b c d A B D) ∨
  (a = D ∧ tripleMatch b c d A B C)

private theorem triple_product_reading {a b c d e f : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (h : complete a * complete b * complete c = complete d * complete e * complete f) :
    tripleMatch a b c d e f := by
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
  have hmema : a.toNat = d.toNat ∨ a.toNat = e.toNat ∨ a.toNat = f.toNat := by
    have hh : a.toNat ∈ (([a.toNat, b.toNat, c.toNat] : List ℕ) : Multiset ℕ) := by simp
    rw [hm] at hh
    simpa using hh
  have hpair {x y : ℤ} (hx : 0 < x) (hy : 0 < y)
      (hh : complete a * complete b * complete c = complete a * complete x * complete y) :
      (b = x ∧ c = y) ∨ (b = y ∧ c = x) := by
    apply complete_two_product_reading hb hc hx hy
    apply mul_left_cancel₀ ((complete_ne_zero_iff a).mpr ha.le)
    simpa only [mul_assoc] using hh
  rcases hmema with h₁ | h₁ | h₁
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

/-- A four-row row monomial recovers the row multiset with all multiplicities. -/
theorem four_product_reading {a b c d A B C D : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (h : complete a * complete b * complete c * complete d =
      complete A * complete B * complete C * complete D) :
    fourMatch a b c d A B C D := by
  have hi : Base.complete a * Base.complete b * Base.complete c * Base.complete d =
      Base.complete A * Base.complete B * Base.complete C * Base.complete D := by
    apply integerLift_injective
    simpa only [map_mul, complete] using h
  have hcast : ∀ x : ℤ, 0 < x → (x.toNat : ℤ) = x := fun x hx => by omega
  have hm : (([a.toNat, b.toNat, c.toNat, d.toNat] : List ℕ) : Multiset ℕ) =
      (([A.toNat, B.toNat, C.toNat, D.toNat] : List ℕ) : Multiset ℕ) := by
    apply (Base.prod_complete_eq_iff_of_pos _ _ (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> omega) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> omega)).mp
    simpa [hcast a ha, hcast b hb, hcast c hc, hcast d hd,
      hcast A hA, hcast B hB, hcast C hC, hcast D hD, mul_assoc] using hi
  have hmem : a.toNat = A.toNat ∨ a.toNat = B.toNat ∨
      a.toNat = C.toNat ∨ a.toNat = D.toNat := by
    have hh : a.toNat ∈ (([a.toNat, b.toNat, c.toNat, d.toNat] : List ℕ) : Multiset ℕ) := by simp
    rw [hm] at hh
    simpa using hh
  have hcancel {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
      (hh : complete a * complete b * complete c * complete d =
        complete a * complete x * complete y * complete z) :
      tripleMatch b c d x y z := by
    apply triple_product_reading hb hc hd hx hy hz
    apply mul_left_cancel₀ ((complete_ne_zero_iff a).mpr ha.le)
    simpa only [mul_assoc] using hh
  rcases hmem with h₁ | h₁ | h₁ | h₁
  · have h₁ : a = A := by omega
    subst A
    exact Or.inl ⟨rfl, hcancel hB hC hD h⟩
  · have h₁ : a = B := by omega
    subst B
    exact Or.inr (Or.inl ⟨rfl, hcancel hA hC hD
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)⟩)
  · have h₁ : a = C := by omega
    subst C
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hcancel hA hB hD
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)⟩))
  · have h₁ : a = D := by omega
    subst D
    exact Or.inr (Or.inr (Or.inr ⟨rfl, hcancel hA hB hC
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)⟩))

private theorem monomial_pair_reading (a b c d : ℕ+ →₀ ℕ)
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

private theorem monomial_three_reading (a b c A B C : ℕ+ →₀ ℕ)
    (h : (MvPolynomial.monomial a 1 : CompleteRing) + MvPolynomial.monomial b 1 +
      MvPolynomial.monomial c 1 =
      MvPolynomial.monomial A 1 + MvPolynomial.monomial B 1 + MvPolynomial.monomial C 1) :
    (a = A ∧ ((b = B ∧ c = C) ∨ (b = C ∧ c = B))) ∨
    (a = B ∧ ((b = A ∧ c = C) ∨ (b = C ∧ c = A))) ∨
    (a = C ∧ ((b = A ∧ c = B) ∨ (b = B ∧ c = A))) := by
  classical
  have ha : a = A ∨ a = B ∨ a = C := by
    by_contra hn
    push_neg at hn
    have hh := congrArg (fun p : CompleteRing => p.coeff a) h
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial] at hh
    simp only [ite_true, ite_eq_right (Ne.symm hn.1),
      ite_eq_right (Ne.symm hn.2.1), ite_eq_right (Ne.symm hn.2.2)] at hh
    split_ifs at hh <;> norm_num at hh
  rcases ha with ha | ha | ha
  · subst A
    left
    refine ⟨rfl, monomial_pair_reading b c B C ?_⟩
    linear_combination h
  · subst B
    right; left
    refine ⟨rfl, monomial_pair_reading b c A C ?_⟩
    linear_combination h
  · subst C
    right; right
    refine ⟨rfl, monomial_pair_reading b c A B ?_⟩
    linear_combination h

/-- Matching of the three adjacent coarsenings, including coincident monomials. -/
def threeMatches (T U : Fin 3 → Fin 3 → ℤ) : Prop :=
  (tripleMatch (T 0 0) (T 0 1) (T 0 2) (U 0 0) (U 0 1) (U 0 2) ∧
    ((tripleMatch (T 1 0) (T 1 1) (T 1 2) (U 1 0) (U 1 1) (U 1 2) ∧
      tripleMatch (T 2 0) (T 2 1) (T 2 2) (U 2 0) (U 2 1) (U 2 2)) ∨
     (tripleMatch (T 1 0) (T 1 1) (T 1 2) (U 2 0) (U 2 1) (U 2 2) ∧
      tripleMatch (T 2 0) (T 2 1) (T 2 2) (U 1 0) (U 1 1) (U 1 2)))) ∨
  (tripleMatch (T 0 0) (T 0 1) (T 0 2) (U 1 0) (U 1 1) (U 1 2) ∧
    ((tripleMatch (T 1 0) (T 1 1) (T 1 2) (U 0 0) (U 0 1) (U 0 2) ∧
      tripleMatch (T 2 0) (T 2 1) (T 2 2) (U 2 0) (U 2 1) (U 2 2)) ∨
     (tripleMatch (T 1 0) (T 1 1) (T 1 2) (U 2 0) (U 2 1) (U 2 2) ∧
      tripleMatch (T 2 0) (T 2 1) (T 2 2) (U 0 0) (U 0 1) (U 0 2)))) ∨
  (tripleMatch (T 0 0) (T 0 1) (T 0 2) (U 2 0) (U 2 1) (U 2 2) ∧
    ((tripleMatch (T 1 0) (T 1 1) (T 1 2) (U 0 0) (U 0 1) (U 0 2) ∧
      tripleMatch (T 2 0) (T 2 1) (T 2 2) (U 1 0) (U 1 1) (U 1 2)) ∨
     (tripleMatch (T 1 0) (T 1 1) (T 1 2) (U 1 0) (U 1 1) (U 1 2) ∧
      tripleMatch (T 2 0) (T 2 1) (T 2 2) (U 0 0) (U 0 1) (U 0 2))))

private noncomputable def tripleProduct (T : Fin 3 → ℤ) : CompleteRing :=
  complete (T 0) * complete (T 1) * complete (T 2)

/-- Three coefficient-one monomials recover the entire unordered coarsening inventory. -/
theorem three_sum_reading (T U : Fin 3 → Fin 3 → ℤ)
    (hT : ∀ i j, 0 < T i j) (hU : ∀ i j, 0 < U i j)
    (he : tripleProduct (T 0) + tripleProduct (T 1) + tripleProduct (T 2) =
      tripleProduct (U 0) + tripleProduct (U 1) + tripleProduct (U 2)) :
    threeMatches T U := by
  let mon (V : Fin 3 → ℤ) :=
    Gluing.hExp (V 0).toNat + Gluing.hExp (V 1).toNat + Gluing.hExp (V 2).toNat
  have hm (V : Fin 3 → ℤ) (hV : ∀ j, 0 < V j) :
      tripleProduct V = MvPolynomial.monomial (mon V) 1 := by
    rw [tripleProduct, complete_eq_hh, complete_eq_hh, complete_eq_hh,
      Gluing.hh_eq_monomial (hV 0).le, Gluing.hh_eq_monomial (hV 1).le,
      Gluing.hh_eq_monomial (hV 2).le,
      MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial]
    simp [mon]
  have ht (i j : Fin 3) (hij : mon (T i) = mon (U j)) :
      tripleMatch (T i 0) (T i 1) (T i 2) (U j 0) (U j 1) (U j 2) := by
    apply triple_product_reading (hT i 0) (hT i 1) (hT i 2)
      (hU j 0) (hU j 1) (hU j 2)
    change tripleProduct (T i) = tripleProduct (U j)
    rw [hm (T i) (hT i), hm (U j) (hU j), hij]
  rw [hm (T 0) (hT 0), hm (T 1) (hT 1), hm (T 2) (hT 2),
    hm (U 0) (hU 0), hm (U 1) (hU 1), hm (U 2) (hU 2)] at he
  rcases monomial_three_reading _ _ _ _ _ _ he with ⟨h0, h12⟩ | ⟨h0, h12⟩ | ⟨h0, h12⟩
  · left; refine ⟨ht 0 0 h0, ?_⟩
    rcases h12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨ht 1 1 h1, ht 2 2 h2⟩
    · exact Or.inr ⟨ht 1 2 h1, ht 2 1 h2⟩
  · right; left; refine ⟨ht 0 1 h0, ?_⟩
    rcases h12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨ht 1 0 h1, ht 2 2 h2⟩
    · exact Or.inr ⟨ht 1 2 h1, ht 2 0 h2⟩
  · right; right; refine ⟨ht 0 2 h0, ?_⟩
    rcases h12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨ht 1 0 h1, ht 2 1 h2⟩
    · exact Or.inr ⟨ht 1 1 h1, ht 2 0 h2⟩

/-- The actual three degree-three adjacent coarsenings of a four-row ribbon. -/
def ribbonCoarsenings (a b c d : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![a + b, c, d], ![a, b + c, d], ![a, b, c + d]]

syntax "four_row_ribbon_prune " ident ident : tactic

macro_rules
  | `(tactic| four_row_ribbon_prune $hr:ident $hcoarsen:ident) => `(tactic| (
      unfold tripleMatch at $hr:ident
      rcases $hr:ident with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
        ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩
      all_goals subst_vars
      all_goals try (clear $hcoarsen:ident; omega)
      all_goals simp only [threeMatches, ribbonCoarsenings, Matrix.cons_val] at $hcoarsen:ident
      all_goals
        rcases $hcoarsen:ident with ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ |
          ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ |
          ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩
      all_goals unfold tripleMatch at h1
      all_goals
        rcases h1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
          ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩
      all_goals subst_vars
      all_goals try (clear h2 h3; omega)
      all_goals unfold tripleMatch at h2
      all_goals
        rcases h2 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
          ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩
      all_goals subst_vars
      all_goals try (clear h3; omega)
      all_goals unfold tripleMatch at h3
      all_goals
        rcases h3 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
          ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩
      all_goals subst_vars
      all_goals omega))

section RibbonPositions

-- Each first-row position has an independent finite matching proof.
set_option maxHeartbeats 300000
set_option maxRecDepth 10000

private theorem ribbon_first_position (a b c d A B C D : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (h0 : a = A) (hr : tripleMatch b c d B C D)
    (hcoarsen : threeMatches (ribbonCoarsenings a b c d)
      (ribbonCoarsenings A B C D)) :
    (a = A ∧ b = B ∧ c = C ∧ d = D) ∨
      (a = D ∧ b = C ∧ c = B ∧ d = A) := by
  four_row_ribbon_prune hr hcoarsen

private theorem ribbon_second_position (a b c d A B C D : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (h0 : a = B) (hr : tripleMatch b c d A C D)
    (hcoarsen : threeMatches (ribbonCoarsenings a b c d)
      (ribbonCoarsenings A B C D)) :
    (a = A ∧ b = B ∧ c = C ∧ d = D) ∨
      (a = D ∧ b = C ∧ c = B ∧ d = A) := by
  four_row_ribbon_prune hr hcoarsen

private theorem ribbon_third_position (a b c d A B C D : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (h0 : a = C) (hr : tripleMatch b c d A B D)
    (hcoarsen : threeMatches (ribbonCoarsenings a b c d)
      (ribbonCoarsenings A B C D)) :
    (a = A ∧ b = B ∧ c = C ∧ d = D) ∨
      (a = D ∧ b = C ∧ c = B ∧ d = A) := by
  four_row_ribbon_prune hr hcoarsen

private theorem ribbon_fourth_position (a b c d A B C D : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (h0 : a = D) (hr : tripleMatch b c d A B C)
    (hcoarsen : threeMatches (ribbonCoarsenings a b c d)
      (ribbonCoarsenings A B C D)) :
    (a = A ∧ b = B ∧ c = C ∧ d = D) ∨
      (a = D ∧ b = C ∧ c = B ∧ d = A) := by
  four_row_ribbon_prune hr hcoarsen

end RibbonPositions

/-- Height four has no nonrotation ambiguity: structural factor permutations, not a census. -/
theorem ribbon_factor_reading (a b c d A B C D : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hrow : fourMatch a b c d A B C D)
    (hcoarsen : threeMatches (ribbonCoarsenings a b c d)
      (ribbonCoarsenings A B C D)) :
    (a = A ∧ b = B ∧ c = C ∧ d = D) ∨
      (a = D ∧ b = C ∧ c = B ∧ d = A) := by
  rcases hrow with ⟨h0, hr⟩ | ⟨h0, hr⟩ | ⟨h0, hr⟩ | ⟨h0, hr⟩
  · exact ribbon_first_position a b c d A B C D ha hb hc hd hA hB hC hD h0 hr hcoarsen
  · exact ribbon_second_position a b c d A B C D ha hb hc hd hA hB hC hD h0 hr hcoarsen
  · exact ribbon_third_position a b c d A B C D ha hb hc hd hA hB hC hD h0 hr hcoarsen
  · exact ribbon_fourth_position a b c d A B C D ha hb hc hd hA hB hC hD h0 hr hcoarsen

private theorem complete_homogeneous {k : ℤ} (hk : 0 < k) :
    (complete k).IsHomogeneous 1 := by
  rw [complete_of_pos hk]
  exact MvPolynomial.isHomogeneous_X _ _

private theorem project_one (m : ℕ) {a : ℤ} (ha : 0 < a) :
    MvPolynomial.homogeneousComponent m (complete a) =
      if m = 1 then complete a else 0 :=
  MvPolynomial.homogeneousComponent_of_mem (complete_homogeneous ha)

private theorem project_two (m : ℕ) {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    MvPolynomial.homogeneousComponent m (complete a * complete b) =
      if m = 2 then complete a * complete b else 0 := by
  exact MvPolynomial.homogeneousComponent_of_mem
    ((complete_homogeneous ha).mul (complete_homogeneous hb))

private theorem project_three (m : ℕ) {a b c : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    MvPolynomial.homogeneousComponent m (complete a * complete b * complete c) =
      if m = 3 then complete a * complete b * complete c else 0 := by
  exact MvPolynomial.homogeneousComponent_of_mem
    (((complete_homogeneous ha).mul (complete_homogeneous hb)).mul (complete_homogeneous hc))

private theorem project_four (m : ℕ) {a b c d : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    MvPolynomial.homogeneousComponent m (complete a * complete b * complete c * complete d) =
      if m = 4 then complete a * complete b * complete c * complete d else 0 := by
  exact MvPolynomial.homogeneousComponent_of_mem
    ((((complete_homogeneous ha).mul (complete_homogeneous hb)).mul
      (complete_homogeneous hc)).mul (complete_homogeneous hd))

/-- Degree four and degree three are derived from the actual ribbon polynomial equality. -/
theorem ribbon_polynomial_readings (a b c d A B C D : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (he : fourInterval complete a b c d 0 0 0 = fourInterval complete A B C D 0 0 0) :
    fourMatch a b c d A B C D ∧
      threeMatches (ribbonCoarsenings a b c d) (ribbonCoarsenings A B C D) := by
  have hab : 0 < a + b := by omega
  have hbc : 0 < b + c := by omega
  have hcd : 0 < c + d := by omega
  have habc : 0 < a + b + c := by omega
  have hbcd : 0 < b + c + d := by omega
  have habcd : 0 < a + b + c + d := by omega
  have hAB : 0 < A + B := by omega
  have hBC : 0 < B + C := by omega
  have hCD : 0 < C + D := by omega
  have hABC : 0 < A + B + C := by omega
  have hBCD : 0 < B + C + D := by omega
  have hABCD : 0 < A + B + C + D := by omega
  simp only [fourInterval, complete_zero, sub_zero, mul_one] at he
  have h4 := congrArg (MvPolynomial.homogeneousComponent (σ := ℕ+) (R := ℚ) 4) he
  have h3 := congrArg (MvPolynomial.homogeneousComponent (σ := ℕ+) (R := ℚ) 3) he
  simp [map_sub, map_add, project_one, project_two, project_three, project_four,
    ha, hb, hc, hd, hA, hB, hC, hD, hab, hbc, hcd, habc, hbcd, habcd,
    hAB, hBC, hCD, hABC, hBCD, hABCD] at h4 h3
  constructor
  · exact four_product_reading ha hb hc hd hA hB hC hD h4
  · apply three_sum_reading
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [ribbonCoarsenings] <;> omega
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [ribbonCoarsenings] <;> omega
    · simp only [ribbonCoarsenings, tripleProduct, Matrix.cons_val]
      linear_combination -h3

/-- The height-four ribbon assertion is unconditional; no BTVW oracle is used. -/
theorem ribbon_four_rigidity (a b c d A B C D : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (he : fourInterval complete a b c d 0 0 0 = fourInterval complete A B C D 0 0 0) :
    (a = A ∧ b = B ∧ c = C ∧ d = D) ∨
      (a = D ∧ b = C ∧ c = B ∧ d = A) := by
  obtain ⟨hr, ht⟩ := ribbon_polynomial_readings a b c d A B C D
    ha hb hc hd hA hB hC hD he
  exact ribbon_factor_reading a b c d A B C D ha hb hc hd hA hB hC hD hr ht

/-- Homogeneous H0 ribbon equality specializes faithfully for the rigidity argument. -/
theorem ribbon_four_hom_rigidity (a b c d A B C D : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (he : fourInterval hTilde a b c d 0 0 0 = fourInterval hTilde A B C D 0 0 0) :
    (a = A ∧ b = B ∧ c = C ∧ d = D) ∨
      (a = D ∧ b = C ∧ c = B ∧ d = A) := by
  apply ribbon_four_rigidity a b c d A B C D ha hb hc hd hA hB hC hD
  have hh := congrArg dehom he
  simpa only [fourInterval, map_sub, map_add, map_mul, dehom_hTilde,
    ← complete_eq_hh] using hh

/-- Uniform minimum subtraction and restoration leave only identity and rotation. -/
theorem uniform_minimum_rigidity (c : ℕ) (a b r s A B R S : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hs : 0 < s)
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R) (hS : 0 < S)
    (he : fourInterval hTilde (a + c) (b + c) (r + c) (s + c) c c c =
      fourInterval hTilde (A + c) (B + c) (R + c) (S + c) c c c) :
    (a = A ∧ b = B ∧ r = R ∧ s = S) ∨
      (a = S ∧ b = R ∧ r = B ∧ s = A) := by
  apply ribbon_four_hom_rigidity a b r s A B R S ha hb hr hs hA hB hR hS
  exact (uniform_interval_eq_iff c a b r s A B R S
    ha hb hr hs hA hB hR hS).mp he

private def endComparisonLeft (p q r s c a b : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![p + q - c, r, s], ![p + s + r - c - b, b, q],
    ![p + s - c, r + q - a, a]]

private def endComparisonRight (p q r s c a b : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![p + s - c, r, q], ![p + q + r - c - a, a, s],
    ![p + q - c, r + s - b, b]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem end_factor_reading (p q r s c a b : ℤ)
    (hc : 0 ≤ c) (hca : c < a) (hcb : c < b)
    (hp : c < p) (hq : a < q) (hr : a + b < r) (hs : b < s)
    (he : threeMatches (endComparisonLeft p q r s c a b)
      (endComparisonRight p q r s c a b)) : q = s ∧ a = b := by
  simp only [threeMatches, endComparisonLeft, endComparisonRight, Matrix.cons_val] at he
  rcases he with ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ |
    ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ |
    ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ <;>
    unfold tripleMatch at h1 h2 h3 <;>
    rcases h1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases h2 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases h3 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- An end-minimum block reversal is Schur-equal only when it was already symmetric. -/
theorem one_end_minimum_rigidity (p q r s c a b : ℤ)
    (hc : 0 ≤ c) (hca : c < a) (hcb : c < b)
    (hp : c < p) (hq : a < q) (hr : a + b < r) (hs : b < s)
    (he : fourInterval complete p q r s c a b =
      fourInterval complete p s r q c b a) : q = s ∧ a = b := by
  rw [end_minimum_table, end_minimum_table, threeInterval_reverse] at he
  have hN : p + s + r + q - c - b - a = p + q + r + s - c - a - b := by omega
  have hRQ : r + q - a = q + r - a := by omega
  have hcoef :
      complete (p + q - c) * complete r * complete s -
        complete (p + q + r - c - a) * complete a * complete s -
        complete (p + q - c) * complete (r + s - b) * complete b =
      complete (p + s - c) * complete r * complete q -
        complete (p + s + r - c - b) * complete b * complete q -
        complete (p + s - c) * complete (r + q - a) * complete a := by
    apply mul_left_cancel₀ ((complete_ne_zero_iff c).mpr hc)
    rw [hN] at he
    linear_combination -he
  have hsum : tripleProduct (endComparisonLeft p q r s c a b 0) +
      tripleProduct (endComparisonLeft p q r s c a b 1) +
      tripleProduct (endComparisonLeft p q r s c a b 2) =
      tripleProduct (endComparisonRight p q r s c a b 0) +
      tripleProduct (endComparisonRight p q r s c a b 1) +
      tripleProduct (endComparisonRight p q r s c a b 2) := by
    simp only [tripleProduct, endComparisonLeft, endComparisonRight, Matrix.cons_val]
    linear_combination hcoef
  apply end_factor_reading p q r s c a b hc hca hcb hp hq hr hs
  apply three_sum_reading _ _ ?_ ?_ hsum
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [endComparisonLeft] <;> omega
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [endComparisonRight] <;> omega

private def twoMatches (T U : Fin 2 → Fin 3 → ℤ) : Prop :=
  (tripleMatch (T 0 0) (T 0 1) (T 0 2) (U 0 0) (U 0 1) (U 0 2) ∧
    tripleMatch (T 1 0) (T 1 1) (T 1 2) (U 1 0) (U 1 1) (U 1 2)) ∨
  (tripleMatch (T 0 0) (T 0 1) (T 0 2) (U 1 0) (U 1 1) (U 1 2) ∧
    tripleMatch (T 1 0) (T 1 1) (T 1 2) (U 0 0) (U 0 1) (U 0 2))

private theorem two_sum_reading (T U : Fin 2 → Fin 3 → ℤ)
    (hT : ∀ i j, 0 < T i j) (hU : ∀ i j, 0 < U i j)
    (he : tripleProduct (T 0) + tripleProduct (T 1) =
      tripleProduct (U 0) + tripleProduct (U 1)) : twoMatches T U := by
  let mon (V : Fin 3 → ℤ) :=
    Gluing.hExp (V 0).toNat + Gluing.hExp (V 1).toNat + Gluing.hExp (V 2).toNat
  have hm (V : Fin 3 → ℤ) (hV : ∀ j, 0 < V j) :
      tripleProduct V = MvPolynomial.monomial (mon V) 1 := by
    rw [tripleProduct, complete_eq_hh, complete_eq_hh, complete_eq_hh,
      Gluing.hh_eq_monomial (hV 0).le, Gluing.hh_eq_monomial (hV 1).le,
      Gluing.hh_eq_monomial (hV 2).le,
      MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial]
    simp [mon]
  have ht (i j : Fin 2) (hij : mon (T i) = mon (U j)) :
      tripleMatch (T i 0) (T i 1) (T i 2) (U j 0) (U j 1) (U j 2) := by
    apply triple_product_reading (hT i 0) (hT i 1) (hT i 2)
      (hU j 0) (hU j 1) (hU j 2)
    change tripleProduct (T i) = tripleProduct (U j)
    rw [hm (T i) (hT i), hm (U j) (hU j), hij]
  rw [hm (T 0) (hT 0), hm (T 1) (hT 1),
    hm (U 0) (hU 0), hm (U 1) (hU 1)] at he
  rcases monomial_pair_reading _ _ _ _ he with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨ht 0 0 h0, ht 1 1 h1⟩
  · exact Or.inr ⟨ht 0 1 h0, ht 1 0 h1⟩

set_option maxHeartbeats 0 in
/-- The largest-label obstruction common to middle flips and L-singleton exchanges. -/
theorem binomial_exchange_rigidity (p q u v s b : ℤ)
    (hp : 0 < p) (hq : 0 < q) (hu : 0 < u) (huv : u < v)
    (hb : 0 < b) (hbs : b < s)
    (he : complete s * (complete p * complete (q + u) - complete q * complete (p + u)) -
      complete b * (complete p * complete (q + v) - complete q * complete (p + v)) = 0) :
    p = q := by
  let T : Fin 2 → Fin 3 → ℤ := ![![s, p, q + u], ![b, q, p + v]]
  let U : Fin 2 → Fin 3 → ℤ := ![![s, q, p + u], ![b, p, q + v]]
  have hsum : tripleProduct (T 0) + tripleProduct (T 1) =
      tripleProduct (U 0) + tripleProduct (U 1) := by
    simp only [T, U, tripleProduct, Matrix.cons_val]
    linear_combination he
  have hm := two_sum_reading T U (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [T] <;> omega) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [U] <;> omega) hsum
  simp only [twoMatches, T, U, Matrix.cons_val] at hm
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    unfold tripleMatch at h1 h2 <;>
    rcases h1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases h2 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- The seven possible minimum-site patterns exhaust all three adjacent gaps. -/
theorem minimum_patterns (a b d c : ℕ) (hc : c = min a (min b d)) :
    (a = c ∧ b = c ∧ d = c) ∨
    (a = c ∧ b = c ∧ c < d) ∨
    (a = c ∧ d = c ∧ c < b) ∨
    (b = c ∧ d = c ∧ c < a) ∨
    (a = c ∧ c < b ∧ c < d) ∨
    (b = c ∧ c < a ∧ c < d) ∨
    (d = c ∧ c < a ∧ c < b) := by
  omega

/-- Every occurrence of the minimum generator in the actual matrix is a minimum seam. -/
theorem minimum_index_sites (P : Profile 3) (hP : P.Hessenberg) (c : ℕ)
    (hmin : ∀ j, c ≤ P.g j) (i j : Fin 4) :
    P.xi i - P.zeta j = c ↔
      ∃ k : Fin 3, i = k.succ ∧ j = k.castSucc ∧ P.g k = c := by
  have hidx := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M i j) P.indices_four
  have hdom := P.four_domain hP
  have hg0 := hmin 0
  have hg1 := hmin 1
  have hg2 := hmin 2
  rcases hdom with ⟨ha, hb, hd, hp, hq, hr, hs⟩
  fin_cases i <;> fin_cases j <;>
    simp [Fin.exists_fin_succ, fourIndices] at hidx ⊢ <;> omega

/-- The zero specialization of the actual minimum generator. -/
noncomputable def killMinimum (c : ℕ) : HomLambda →ₐ[ℚ] HomLambda :=
  MvPolynomial.aeval (fun k => if k = c then 0 else MvPolynomial.X k)

/-- No other generator or independent unit variable is changed by the cut. -/
theorem killMinimum_hTilde (c : ℕ) (k : ℤ) :
    killMinimum c (hTilde k) = if k = (c : ℤ) then 0 else hTilde k := by
  by_cases hk : k < 0
  · have hne : k ≠ (c : ℤ) := by omega
    simp [hTilde, hk, hne]
  · have hiff : k.toNat = c ↔ k = (c : ℤ) := by omega
    simp [killMinimum, hTilde, hk, hiff]

/-- The actual matrix specialization cuts precisely the minimum subdiagonal sites. -/
theorem minimum_matrix_specialization (P : Profile 3) (hP : P.Hessenberg)
    (c : ℕ) (hmin : ∀ j, c ≤ P.g j) :
    (Matrix.of fun i j : Fin 4 => hTilde (P.xi i - P.zeta j)).map (killMinimum c) =
      Matrix.of (fun i j : Fin 4 =>
        if ∃ k : Fin 3, i = k.succ ∧ j = k.castSucc ∧ P.g k = c
        then 0 else hTilde (P.xi i - P.zeta j)) := by
  classical
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, killMinimum_hTilde,
    minimum_index_sites P hP c hmin i j]

/-- The matrix cut computes the full specialized determinant. -/
theorem minimum_det_specialization (P : Profile 3) (hP : P.Hessenberg)
    (c : ℕ) (hmin : ∀ j, c ≤ P.g j) :
    killMinimum c P.schurHom =
      (Matrix.of (fun i j : Fin 4 =>
        if ∃ k : Fin 3, i = k.succ ∧ j = k.castSucc ∧ P.g k = c
        then 0 else hTilde (P.xi i - P.zeta j))).det := by
  rw [Profile.schurHom, AlgHom.map_det]
  apply congrArg Matrix.det
  change (Matrix.of fun i j : Fin 4 => hTilde (P.xi i - P.zeta j)).map
    (killMinimum c) = _
  exact minimum_matrix_specialization P hP c hmin

/-- Keep one minimum generator as an ordinary univariate variable for coefficient extraction. -/
noncomputable def minimumMap (c : ℕ) : HomLambda →+* Polynomial HomLambda :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) (fun k =>
    if k = c then Polynomial.X else Polynomial.C (MvPolynomial.X k))

theorem minimumMap_self (c : ℕ) :
    minimumMap c (hTilde (c : ℤ)) = Polynomial.X := by
  rw [hTilde, ite_eq_right (show ¬ (c : ℤ) < 0 by omega)]
  simp only [Int.toNat_natCast, minimumMap, MvPolynomial.eval₂Hom_X',
    ite_eq_left rfl, ite_true]

theorem minimumMap_constant (c : ℕ) (k : ℤ) (hk : (c : ℤ) < k) :
    minimumMap c (hTilde k) = Polynomial.C (hTilde k) := by
  have hk0 : ¬ k < 0 := by omega
  have hkc : k.toNat ≠ c := by omega
  simp [minimumMap, hTilde, hk0, hkc]

/-- The L linear coefficient from the appendix, as a polynomial in the other generators. -/
noncomputable def linearL (h : ℤ → HomLambda) (p q a b c d : ℤ) : HomLambda :=
  -h (p + q - c) * h a * h b
    + h (p + q - c) * h (a + b - d) * h d
    - h p * h (q + a - c) * h b
    + h p * h (q + a + b - c - d) * h d

noncomputable def quadraticL (h : ℤ → HomLambda) (p q a b c d : ℤ) : HomLambda :=
  h (p + q + a - 2 * c) * h b - h (p + q + a + b - 2 * c - d) * h d

noncomputable def linearM (h : ℤ → HomLambda) (p q a b c d : ℤ) : HomLambda :=
  -h (p + a - c) * h b * h q - h p * h a * h (q + b - c)
    + h (p + a + b - c - d) * h d * h q
    + h p * h (q + a + b - c - d) * h d

noncomputable def quadraticM (h : ℤ → HomLambda) (p q a b c d : ℤ) : HomLambda :=
  h (p + a - c) * h (q + b - c)
    - h (p + q + a + b - 2 * c - d) * h d

/-- L has no hidden occurrences of the minimum in its displayed coefficient table. -/
theorem minimumMap_L (p q a b d : ℤ) (c : ℕ)
    (hdom : FourDomain p q a b c c d) (hcd : (c : ℤ) < d) :
    minimumMap c (fourInterval hTilde p q a b c c d) =
      Polynomial.C (hTilde p * hTilde q * (hTilde a * hTilde b - hTilde (a + b - d) * hTilde d))
      + Polynomial.X * Polynomial.C (linearL hTilde p q a b c d)
      + Polynomial.X ^ 2 * Polynomial.C (quadraticL hTilde p q a b c d) := by
  rcases hdom with ⟨hc0, hc1, hd, hp, hq, ha, hb⟩
  rw [two_minimum_L_table]
  simp only [map_add, map_mul, map_sub, map_neg, map_pow, minimumMap_self,
    minimumMap_constant c p (by omega), minimumMap_constant c q (by omega),
    minimumMap_constant c a (by omega), minimumMap_constant c b (by omega),
    minimumMap_constant c d hcd,
    minimumMap_constant c (a + b - d) (by omega),
    minimumMap_constant c (p + q - c) (by omega),
    minimumMap_constant c (q + a - c) (by omega),
    minimumMap_constant c (q + a + b - c - d) (by omega),
    minimumMap_constant c (p + q + a - 2 * c) (by omega),
    minimumMap_constant c (p + q + a + b - 2 * c - d) (by omega)]
  simp only [linearL, quadraticL, map_add, map_sub, map_neg, map_mul]

/-- M has the same constant block product and the stated linear and quadratic coefficients. -/
theorem minimumMap_M (p q a b d : ℤ) (c : ℕ)
    (hdom : FourDomain p a b q c d c) (hcd : (c : ℤ) < d) :
    minimumMap c (fourInterval hTilde p a b q c d c) =
      Polynomial.C (hTilde p * hTilde q * (hTilde a * hTilde b - hTilde (a + b - d) * hTilde d))
      + Polynomial.X * Polynomial.C (linearM hTilde p q a b c d)
      + Polynomial.X ^ 2 * Polynomial.C (quadraticM hTilde p q a b c d) := by
  rcases hdom with ⟨hc0, hd, hc1, hp, ha, hb, hq⟩
  rw [two_minimum_M_table]
  simp only [map_add, map_mul, map_sub, map_neg, map_pow, minimumMap_self,
    minimumMap_constant c p (by omega), minimumMap_constant c q (by omega),
    minimumMap_constant c a (by omega), minimumMap_constant c b (by omega),
    minimumMap_constant c d hcd,
    minimumMap_constant c (a + b - d) (by omega),
    minimumMap_constant c (p + a - c) (by omega),
    minimumMap_constant c (q + b - c) (by omega),
    minimumMap_constant c (p + a + b - c - d) (by omega),
    minimumMap_constant c (q + a + b - c - d) (by omega),
    minimumMap_constant c (p + q + a + b - 2 * c - d) (by omega)]
  simp only [linearM, quadraticM, map_add, map_sub, map_neg, map_mul]

private theorem coeff_quadratic_one (A B C : HomLambda) :
    (Polynomial.C A + Polynomial.X * Polynomial.C B +
      Polynomial.X ^ 2 * Polynomial.C C).coeff 1 = B := by
  simp [Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_C,
    Polynomial.coeff_X_pow]

private theorem coeff_quadratic_two (A B C : HomLambda) :
    (Polynomial.C A + Polynomial.X * Polynomial.C B +
      Polynomial.X ^ 2 * Polynomial.C C).coeff 2 = C := by
  simp [Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_C,
    Polynomial.coeff_X_pow]

/-- L/M coefficient constraints are consequences of full polynomial equality. -/
theorem two_minimum_LM_readings (p q a b d : ℤ) (c : ℕ)
    (hL : FourDomain p q a b c c d) (hM : FourDomain p a b q c d c)
    (hcd : (c : ℤ) < d)
    (he : fourInterval hTilde p q a b c c d = fourInterval hTilde p a b q c d c) :
    linearL hTilde p q a b c d = linearM hTilde p q a b c d ∧
      quadraticL hTilde p q a b c d = quadraticM hTilde p q a b c d := by
  have hh := congrArg (minimumMap c) he
  rw [minimumMap_L p q a b d c hL hcd, minimumMap_M p q a b d c hM hcd] at hh
  constructor
  · have h1 := congrArg (fun f : Polynomial HomLambda => f.coeff 1) hh
    simpa only [coeff_quadratic_one] using h1
  · have h2 := congrArg (fun f : Polynomial HomLambda => f.coeff 2) hh
    simpa only [coeff_quadratic_two] using h2

private def LMLeft (p q a b c d : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![p + q - c, a + b - d, d], ![b, b, q], ![p, a, q + b - c]]

private def LMRight (p q a b c d : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![p + q - c, a, b], ![p, q + a - c, b], ![p + a + b - c - d, d, q]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem LM_factor_reading (p q a b c d : ℤ)
    (hc : 0 ≤ c) (hcd : c < d)
    (hp : c < p) (hq : 2 * c < q) (ha : c + d < a) (hb : d < b)
    (hm : b = p + a - c)
    (he : threeMatches (LMLeft p q a b c d) (LMRight p q a b c d)) :
    p = d ∧ q = a := by
  simp only [threeMatches, LMLeft, LMRight, Matrix.cons_val] at he
  rcases he with ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ |
    ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ |
    ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ <;>
    unfold tripleMatch at h1 h2 h3 <;>
    rcases h1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases h2 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases h3 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- The exceptional parameters are necessary for the first L/M alignment. -/
theorem two_minimum_LM_necessity (p q a b d : ℤ) (c : ℕ)
    (hL : FourDomain p q a b c c d) (hM : FourDomain p a b q c d c)
    (hcd : (c : ℤ) < d)
    (he : fourInterval hTilde p q a b c c d = fourInterval hTilde p a b q c d c) :
    p = d ∧ q = a ∧ b = a + d - c ∧ (c : ℤ) + d < a := by
  obtain ⟨hlin, hquad⟩ := two_minimum_LM_readings p q a b d c hL hM hcd he
  rcases hL with ⟨hc0, hc1, hd, hp, hq, ha, hb⟩
  have hqp : complete (p + q + a - 2 * c) * complete b =
      complete (p + a - c) * complete (q + b - c) := by
    have hh := congrArg dehom hquad
    simp only [quadraticL, quadraticM, map_sub, map_mul, dehom_hTilde,
      ← complete_eq_hh] at hh
    linear_combination hh
  have hm : b = p + a - c := by
    have hpairs := complete_two_product_reading (show 0 < p + q + a - 2 * c by omega)
      (show 0 < b by omega) (show 0 < p + a - c by omega)
      (show 0 < q + b - c by omega) hqp
    rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hlin' := congrArg dehom hlin
  simp only [linearL, linearM, map_add, map_sub, map_neg, map_mul,
    dehom_hTilde, ← complete_eq_hh] at hlin'
  have hsum : tripleProduct (LMLeft p q a b c d 0) +
      tripleProduct (LMLeft p q a b c d 1) +
      tripleProduct (LMLeft p q a b c d 2) =
      tripleProduct (LMRight p q a b c d 0) +
      tripleProduct (LMRight p q a b c d 1) +
      tripleProduct (LMRight p q a b c d 2) := by
    rw [← hm] at hlin'
    simp only [LMLeft, LMRight, tripleProduct, Matrix.cons_val]
    linear_combination hlin'
  have ht := three_sum_reading (LMLeft p q a b c d) (LMRight p q a b c d)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [LMLeft] <;> omega)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [LMRight] <;> omega) hsum
  have hpar := LM_factor_reading p q a b c d (by omega) hcd hp (by omega) ha hb hm ht
  exact ⟨hpar.1, hpar.2, by omega, ha⟩

/-- Necessity and sufficiency for this alignment are separate actual polynomial arguments. -/
theorem two_minimum_LM_eq_iff (p q a b d : ℤ) (c : ℕ)
    (hL : FourDomain p q a b c c d) (hM : FourDomain p a b q c d c)
    (hcd : (c : ℤ) < d) :
    fourInterval hTilde p q a b c c d = fourInterval hTilde p a b q c d c ↔
      p = d ∧ q = a ∧ b = a + d - c := by
  constructor
  · intro he
    have hh := two_minimum_LM_necessity p q a b d c hL hM hcd he
    exact ⟨hh.1, hh.2.1, hh.2.2.1⟩
  · rintro ⟨hp, hq, hb⟩
    rw [hp, hq, hb]
    exact family_interval_identity hTilde d a c

/-- A single orientation flip at an interior minimum changes the full polynomial. -/
theorem one_middle_minimum_left_flip (p q r s a c b : ℤ)
    (hdom : FourDomain p q r s a c b) (hc : 0 ≤ c) (hca : c < a) (hcb : c < b)
    (he : fourInterval complete p q r s a c b =
      fourInterval complete q p r s a c b) : p = q := by
  rcases hdom with ⟨ha0, hc0, hb0, hp, hq, hr, hs⟩
  rw [middle_minimum_table, middle_minimum_table] at he
  have hsum : q + p - a = p + q - a := by omega
  have htriple : q + p + r - a - c = p + q + r - a - c := by omega
  have hN : q + p + r + s - a - c - b = p + q + r + s - a - c - b := by omega
  have hqu : q + r - c = q + (r - c) := by omega
  have hpu : p + r - c = p + (r - c) := by omega
  have hqv : q + r + s - b - c = q + (r + s - b - c) := by omega
  have hpv : p + r + s - b - c = p + (r + s - b - c) := by omega
  rw [hsum, htriple, hN, hqu, hpu, hqv, hpv] at he
  apply binomial_exchange_rigidity p q (r - c) (r + s - b - c) s b
    (by omega) (by omega) (by omega) (by omega) (by omega) hs
  apply mul_left_cancel₀ ((complete_ne_zero_iff c).mpr hc)
  change complete c * _ = complete c * 0
  linear_combination -he

private def middleBothLeft (p q r s a c b : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![q + r - c, p, s], ![q + p + s - a - c, a, r],
    ![p + s + r - b - c, b, q]]

private def middleBothRight (p q r s a c b : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![p + s - c, q, r], ![p + q + r - a - c, a, s],
    ![q + r + s - b - c, b, p]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem middle_both_factor_reading (p q r s a c b : ℤ)
    (hc : 0 ≤ c) (hca : c < a) (hcb : c < b)
    (hp : a + c < p) (hq : a + c < q) (hr : b + c < r) (hs : b + c < s)
    (he : threeMatches (middleBothLeft p q r s a c b)
      (middleBothRight p q r s a c b)) :
    (p = q ∧ r = s) ∨ (a = b ∧ p = r ∧ q = s) := by
  simp only [threeMatches, middleBothLeft, middleBothRight, Matrix.cons_val] at he
  rcases he with ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ |
    ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ |
    ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩ <;>
    unfold tripleMatch at h1 h2 h3 <;>
    rcases h1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases h2 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases h3 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- Both middle-block flips give only identity or global rotation, including tied gaps. -/
theorem one_middle_minimum_both_flip (p q r s a c b : ℤ)
    (hdom : FourDomain p q r s a c b) (hflip : FourDomain q p s r a c b)
    (hc : 0 ≤ c) (hca : c < a) (hcb : c < b)
    (he : fourInterval complete p q r s a c b =
      fourInterval complete q p s r a c b) :
    (p = q ∧ r = s) ∨ (a = b ∧ p = r ∧ q = s) := by
  rcases hdom with ⟨ha0, hc0, hb0, hpa, hq, hr, hsb⟩
  rcases hflip with ⟨ha1, hc1, hb1, hqa, hp, hs, hrb⟩
  rw [middle_minimum_table, middle_minimum_table] at he
  have hpq : q + p - a = p + q - a := by omega
  have hrs : s + r - b = r + s - b := by omega
  have hN : q + p + s + r - a - c - b = p + q + r + s - a - c - b := by omega
  rw [hpq, hrs, hN] at he
  have hcoef :
      complete (q + r - c) * complete p * complete s -
        complete (p + q + r - a - c) * complete a * complete s -
        complete (q + r + s - b - c) * complete b * complete p =
      complete (p + s - c) * complete q * complete r -
        complete (q + p + s - a - c) * complete a * complete r -
        complete (p + s + r - b - c) * complete b * complete q := by
    apply mul_left_cancel₀ ((complete_ne_zero_iff c).mpr hc)
    linear_combination -he
  have hsum : tripleProduct (middleBothLeft p q r s a c b 0) +
      tripleProduct (middleBothLeft p q r s a c b 1) +
      tripleProduct (middleBothLeft p q r s a c b 2) =
      tripleProduct (middleBothRight p q r s a c b 0) +
      tripleProduct (middleBothRight p q r s a c b 1) +
      tripleProduct (middleBothRight p q r s a c b 2) := by
    simp only [middleBothLeft, middleBothRight, tripleProduct, Matrix.cons_val]
    linear_combination hcoef
  apply middle_both_factor_reading p q r s a c b hc hca hcb hp hq (by omega) (by omega)
  apply three_sum_reading _ _ ?_ ?_ hsum
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [middleBothLeft] <;> omega
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [middleBothRight] <;> omega

/-- L fixes the orientation of its two-row block, even if a singleton has the same length. -/
theorem two_minimum_LL_block_flip (p q a b d : ℤ) (c : ℕ)
    (hL : FourDomain p q a b c c d) (hflip : FourDomain p q b a c c d)
    (hcd : (c : ℤ) < d)
    (he : fourInterval hTilde p q a b c c d = fourInterval hTilde p q b a c c d) :
    a = b := by
  have hh := congrArg (minimumMap c) he
  rw [minimumMap_L p q a b d c hL hcd, minimumMap_L p q b a d c hflip hcd] at hh
  have hq := congrArg (fun f : Polynomial HomLambda => f.coeff 2) hh
  simp only [coeff_quadratic_two] at hq
  have hq' := congrArg dehom hq
  simp only [quadraticL, map_sub, map_mul, dehom_hTilde, ← complete_eq_hh] at hq'
  have hN : p + q + b + a - 2 * c - d = p + q + a + b - 2 * c - d := by omega
  rw [hN] at hq'
  have hprod : complete (p + q + a - 2 * c) * complete b =
      complete (p + q + b - 2 * c) * complete a := by
    linear_combination hq'
  rcases hL with ⟨hc0, hc1, hd, hp, hq, ha, hb⟩
  rcases hflip with ⟨hc2, hc3, hd1, hp1, hq1, hb1, ha1⟩
  rcases complete_two_product_reading (show 0 < p + q + a - 2 * c by omega)
    (show 0 < b by omega) (show 0 < p + q + b - 2 * c by omega)
    (show 0 < a by omega) hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- L also fixes unequal singleton order once the two-row orientation is fixed. -/
theorem two_minimum_LL_singleton_flip (p q a b d : ℤ) (c : ℕ)
    (hL : FourDomain p q a b c c d) (hflip : FourDomain q p a b c c d)
    (hcd : (c : ℤ) < d)
    (he : fourInterval hTilde p q a b c c d = fourInterval hTilde q p a b c c d) :
    p = q := by
  have hh := congrArg (minimumMap c) he
  rw [minimumMap_L p q a b d c hL hcd, minimumMap_L q p a b d c hflip hcd] at hh
  have hl := congrArg (fun f : Polynomial HomLambda => f.coeff 1) hh
  simp only [coeff_quadratic_one] at hl
  have hl' := congrArg dehom hl
  simp only [linearL, map_add, map_sub, map_neg, map_mul,
    dehom_hTilde, ← complete_eq_hh] at hl'
  have hpq : q + p - c = p + q - c := by omega
  have hqu : q + a - c = q + (a - c) := by omega
  have hpu : p + a - c = p + (a - c) := by omega
  have hqv : q + a + b - c - d = q + (a + b - d - c) := by omega
  have hpv : p + a + b - c - d = p + (a + b - d - c) := by omega
  rw [hpq, hqu, hpu, hqv, hpv] at hl'
  rcases hL with ⟨hc0, hc1, hd, hp, hq, ha, hb⟩
  apply binomial_exchange_rigidity p q (a - c) (a + b - d - c) b d
    (by omega) (by omega) (by omega) (by omega) (by omega) hb
  linear_combination -hl'

/-- M has only identity/global-rotation exchanges within a recovered cut inventory. -/
theorem two_minimum_MM_block_flip (p q a b d : ℤ) (c : ℕ)
    (hM : FourDomain p a b q c d c) (hflip : FourDomain p b a q c d c)
    (hcd : (c : ℤ) < d)
    (he : fourInterval hTilde p a b q c d c = fourInterval hTilde p b a q c d c) :
    p = q ∨ a = b := by
  have hh := congrArg (minimumMap c) he
  rw [minimumMap_M p q a b d c hM hcd, minimumMap_M p q b a d c hflip hcd] at hh
  have hq := congrArg (fun f : Polynomial HomLambda => f.coeff 2) hh
  simp only [coeff_quadratic_two] at hq
  have hq' := congrArg dehom hq
  simp only [quadraticM, map_sub, map_mul, dehom_hTilde, ← complete_eq_hh] at hq'
  have hN : p + q + b + a - 2 * c - d = p + q + a + b - 2 * c - d := by omega
  rw [hN] at hq'
  have hprod : complete (p + a - c) * complete (q + b - c) =
      complete (p + b - c) * complete (q + a - c) := by
    linear_combination hq'
  rcases hM with ⟨hc0, hd, hc1, hp, ha, hb, hq⟩
  rcases complete_two_product_reading (show 0 < p + a - c by omega)
    (show 0 < q + b - c by omega) (show 0 < p + b - c by omega)
    (show 0 < q + a - c by omega) hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

set_option maxHeartbeats 0 in
private theorem LM_other_factor_contradiction (p q a b c d : ℤ)
    (hc : 0 ≤ c) (hcd : c < d)
    (hp : c < p) (hq : 2 * c < q) (ha : c + d < a) (hb : d < b)
    (hm : b = q + a - c)
    (he : twoMatches
      ![![p + q - c, a + b - d, d], ![p + b - c, a, q]]
      ![![p + q - c, a, b], ![p + a + b - c - d, d, q]]) : False := by
  simp only [twoMatches, Matrix.cons_val] at he
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    unfold tripleMatch at h1 h2 <;>
    rcases h1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases h2 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- The other L/M alignment has no full-polynomial equality in the legitimate domain. -/
theorem two_minimum_LM_other_ne (p q a b d : ℤ) (c : ℕ)
    (hL : FourDomain p q a b c c d) (hM : FourDomain p b a q c d c)
    (hcd : (c : ℤ) < d) :
    fourInterval hTilde p q a b c c d ≠ fourInterval hTilde p b a q c d c := by
  intro he
  have hh := congrArg (minimumMap c) he
  rw [minimumMap_L p q a b d c hL hcd, minimumMap_M p q b a d c hM hcd] at hh
  have hlin := congrArg (fun f : Polynomial HomLambda => f.coeff 1) hh
  have hquad := congrArg (fun f : Polynomial HomLambda => f.coeff 2) hh
  simp only [coeff_quadratic_one] at hlin
  simp only [coeff_quadratic_two] at hquad
  have hl := congrArg dehom hlin
  have hq := congrArg dehom hquad
  simp only [quadraticL, quadraticM, map_sub, map_mul,
    dehom_hTilde, ← complete_eq_hh] at hq
  simp only [linearL, linearM, map_add, map_sub, map_neg, map_mul,
    dehom_hTilde, ← complete_eq_hh] at hl
  have hN : p + q + b + a - 2 * c - d = p + q + a + b - 2 * c - d := by omega
  have hab : b + a - d = a + b - d := by omega
  have hpt : p + b + a - c - d = p + a + b - c - d := by omega
  have hqt : q + b + a - c - d = q + a + b - c - d := by omega
  rw [hN] at hq
  rw [hpt, hqt] at hl
  have hprod : complete (p + q + a - 2 * c) * complete b =
      complete (p + b - c) * complete (q + a - c) := by
    linear_combination hq
  rcases hL with ⟨hc0, hc1, hd, hp, hq, ha, hb⟩
  have hm : b = q + a - c := by
    rcases complete_two_product_reading (show 0 < p + q + a - 2 * c by omega)
      (show 0 < b by omega) (show 0 < p + b - c by omega)
      (show 0 < q + a - c by omega) hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  let T : Fin 2 → Fin 3 → ℤ :=
    ![![p + q - c, a + b - d, d], ![p + b - c, a, q]]
  let U : Fin 2 → Fin 3 → ℤ :=
    ![![p + q - c, a, b], ![p + a + b - c - d, d, q]]
  have hs : tripleProduct (T 0) + tripleProduct (T 1) =
      tripleProduct (U 0) + tripleProduct (U 1) := by
    simp only [T, U, tripleProduct, Matrix.cons_val]
    linear_combination hl
  apply LM_other_factor_contradiction p q a b c d (by omega) hcd hp (by omega) ha hb hm
  exact two_sum_reading T U
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [T] <;> omega)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [U] <;> omega) hs

/-- Maximal surviving row intervals after every minimum seam is cut. -/
def minimumProfiles (P : Profile 3) (c : ℕ) : List (Σ m : ℕ, Profile m) :=
  if P.g 0 = c then
    if P.g 1 = c then
      if P.g 2 = c then
        [⟨0, P.slice 0 0 (by omega)⟩, ⟨0, P.slice 1 0 (by omega)⟩,
          ⟨0, P.slice 2 0 (by omega)⟩, ⟨0, P.slice 3 0 (by omega)⟩]
      else
        [⟨0, P.slice 0 0 (by omega)⟩, ⟨0, P.slice 1 0 (by omega)⟩,
          ⟨1, P.slice 2 1 (by omega)⟩]
    else if P.g 2 = c then
      [⟨0, P.slice 0 0 (by omega)⟩, ⟨1, P.slice 1 1 (by omega)⟩,
        ⟨0, P.slice 3 0 (by omega)⟩]
    else
      [⟨0, P.slice 0 0 (by omega)⟩, ⟨2, P.slice 1 2 (by omega)⟩]
  else if P.g 1 = c then
    if P.g 2 = c then
      [⟨1, P.slice 0 1 (by omega)⟩, ⟨0, P.slice 2 0 (by omega)⟩,
        ⟨0, P.slice 3 0 (by omega)⟩]
    else
      [⟨1, P.slice 0 1 (by omega)⟩, ⟨1, P.slice 2 1 (by omega)⟩]
  else if P.g 2 = c then
    [⟨2, P.slice 0 2 (by omega)⟩, ⟨0, P.slice 3 0 (by omega)⟩]
  else
    [⟨3, P⟩]

/-- The cut inventory contains actual connected full beta arrays, not formal factors. -/
def minimumBlocks (P : Profile 3) (c : ℕ) : List (Σ k : ℕ, BetaDiagram k) :=
  (minimumProfiles P c).map (fun X => ⟨X.1 + 1, X.2.toBetaDiagram⟩)

theorem minimum_blocks_connected (P : Profile 3) (c : ℕ) :
    ∀ X ∈ minimumBlocks P c, X.2.Connected := by
  intro X hX
  obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
  exact Y.2.toBetaDiagram_connected

/-- A genuine minimum leaves only blocks of at most three rows. -/
theorem minimum_profile_order (P : Profile 3) (c : ℕ)
    (hc : c = min (P.g 0) (min (P.g 1) (P.g 2))) :
    ∀ X ∈ minimumProfiles P c, X.1 ≤ 2 := by
  intro X hX
  have hsome : P.g 0 = c ∨ P.g 1 = c ∨ P.g 2 = c := by
    have hh := minimum_patterns (P.g 0) (P.g 1) (P.g 2) c hc
    rcases hh with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
  unfold minimumProfiles at hX
  split_ifs at hX
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
  all_goals rcases hX with rfl | rfl | rfl | rfl
  all_goals norm_num
  all_goals rcases hsome with hsome | hsome | hsome <;> contradiction

theorem killMinimum_constant (c : ℕ) (k : ℤ) (hk : (c : ℤ) < k) :
    killMinimum c (hTilde k) = hTilde k := by
  rw [killMinimum_hTilde]
  simp [show k ≠ (c : ℤ) by omega]

/-- The matrix cut factors as the homogenized determinants of its literal surviving intervals. -/
theorem minimum_profile_product (P : Profile 3) (hP : P.Hessenberg) (c : ℕ)
    (hc : c = min (P.g 0) (min (P.g 1) (P.g 2))) :
    killMinimum c P.schurHom =
      ((minimumProfiles P c).map (fun X => X.2.schurHom)).prod := by
  obtain ⟨hq, hr⟩ := P.hessenberg_four_iff.mp hP
  have hmin0 : c ≤ P.g 0 := by omega
  have hmin1 : c ≤ P.g 1 := by omega
  have hmin2 : c ≤ P.g 2 := by omega
  have hsome : P.g 0 = c ∨ P.g 1 = c ∨ P.g 2 = c := by
    have hh := minimum_patterns (P.g 0) (P.g 1) (P.g 2) c hc
    rcases hh with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
  have hdom := P.four_domain hP
  rcases hdom with ⟨ha, hb, hd, hp, hq', hr', hs⟩
  have hfirst := (P.slice 0 2 (by omega)).schurHom_three_interval (by
    simpa [Profile.slice] using hq)
  have hlast := (P.slice 1 2 (by omega)).schurHom_three_interval (by
    simpa [Profile.slice] using hr)
  rw [P.schurHom_four_interval hP]
  simp only [fourInterval, map_sub, map_add, map_mul,
    killMinimum_constant c (P.r 0) (by omega),
    killMinimum_constant c (P.r 1) (by omega),
    killMinimum_constant c (P.r 2) (by omega),
    killMinimum_constant c (P.r 3) (by omega),
    killMinimum_constant c ((P.r 0 : ℤ) + P.r 1 - P.g 0) (by omega),
    killMinimum_constant c ((P.r 1 : ℤ) + P.r 2 - P.g 1) (by omega),
    killMinimum_constant c ((P.r 2 : ℤ) + P.r 3 - P.g 2) (by omega),
    killMinimum_constant c ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) (by omega),
    killMinimum_constant c ((P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2) (by omega),
    killMinimum_constant c ((P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 -
      P.g 0 - P.g 1 - P.g 2) (by omega)]
  by_cases h0 : P.g 0 = c <;> by_cases h1 : P.g 1 = c <;>
    by_cases h2 : P.g 2 = c
  all_goals first
    | omega
    | simp only [minimumProfiles, h0, h1, h2, if_true, if_false,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Profile.schurHom_single_interval, Profile.schurHom_two_interval,
        hfirst, hlast, killMinimum_hTilde, Int.natCast_inj,
        h0, h1, h2, if_true, if_false, threeInterval]
      norm_num [Profile.slice] <;> ring

/-- The actual complete-ring block product is recovered after the H0-faithful cut. -/
theorem minimum_block_product (P : Profile 3) (hP : P.Hessenberg) (c : ℕ)
    (hc : c = min (P.g 0) (min (P.g 1) (P.g 2))) :
    dehom (killMinimum c P.schurHom) =
      ((minimumBlocks P c).map (fun X => X.2.schur)).prod := by
  rw [minimum_profile_product P hP c hc, map_list_prod]
  simp only [minimumBlocks, List.map_map, Function.comp_def,
    Profile.toBetaDiagram_schur, Profile.dehom_schurHom]

/-- Irreducibility recovers every cut block and its actual row count, with multiplicity. -/
theorem minimum_block_inventory (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (c : ℕ)
    (hcP : c = min (P.g 0) (min (P.g 1) (P.g 2)))
    (hcQ : c = min (Q.g 0) (min (Q.g 1) (Q.g 2)))
    (he : P.schur = Q.schur) :
    Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k =>
      X.2.schur = Y.2.schur ∧ X.1 = Y.1)
      (minimumBlocks P c : Multiset _) (minimumBlocks Q c : Multiset _) := by
  apply BetaDiagram.product_component_matching
    (minimumBlocks P c) (minimumBlocks Q c)
    (minimum_blocks_connected P c) (minimum_blocks_connected Q c)
  have hh := congrArg (fun p : HomLambda => dehom (killMinimum c p))
    ((Profile.schur_eq_iff_schurHom_eq P Q).mp he)
  rwa [minimum_block_product P hP c hcP, minimum_block_product Q hQ c hcQ] at hh

private theorem hTilde_pderiv (n : ℕ) (k : ℤ) (hk : 0 ≤ k) :
    MvPolynomial.pderiv n (hTilde k) =
      if k = (n : ℤ) then (1 : HomLambda) else 0 := by
  simp only [hTilde, ite_eq_right (show ¬ k < 0 by omega),
    MvPolynomial.pderiv_X, Pi.single_apply]
  by_cases he : k = (n : ℤ)
  · have hn : k.toNat = n := by omega
    simp [he, hn]
  · have hn : k.toNat ≠ n := by omega
    simp [he, hn]

/-- The largest interval label has exactly the signed adjacent-gap product as its coefficient. -/
theorem largest_interval_derivative (p q r s a b d : ℤ)
    (hdom : FourDomain p q r s a b d) :
    MvPolynomial.pderiv (p + q + r + s - a - b - d).toNat
      (fourInterval hTilde p q r s a b d) =
      -hTilde a * hTilde b * hTilde d := by
  rcases hdom with ⟨ha, hb, hd, hp, hq, hr, hs⟩
  let N := p + q + r + s - a - b - d
  have hN : 0 < N := by dsimp [N]; omega
  have hcast : (N.toNat : ℤ) = N := by omega
  have hz (k : ℤ) (hk : 0 ≤ k) (hkn : k < N) :
      MvPolynomial.pderiv N.toNat (hTilde k) = 0 := by
    rw [hTilde_pderiv _ _ hk]
    simp [hcast, show k ≠ N by omega]
  have hone : MvPolynomial.pderiv N.toNat (hTilde N) = 1 := by
    rw [hTilde_pderiv _ _ hN.le]
    simp [hcast]
  have hone' : MvPolynomial.pderiv N.toNat
      (hTilde (p + q + r + s - a - b - d)) = 1 := hone
  change MvPolynomial.pderiv N.toNat (fourInterval hTilde p q r s a b d) = _
  simp only [fourInterval, map_sub, map_add, MvPolynomial.pderiv_mul,
    hz p (by omega) (by dsimp [N]; omega),
    hz q (by omega) (by dsimp [N]; omega),
    hz r (by omega) (by dsimp [N]; omega),
    hz s (by omega) (by dsimp [N]; omega),
    hz a ha (by dsimp [N]; omega),
    hz b hb (by dsimp [N]; omega),
    hz d hd (by dsimp [N]; omega),
    hz (p + q - a) (by omega) (by dsimp [N]; omega),
    hz (q + r - b) (by omega) (by dsimp [N]; omega),
    hz (r + s - d) (by omega) (by dsimp [N]; omega),
    hz (p + q + r - a - b) (by omega) (by dsimp [N]; omega),
    hz (q + r + s - b - d) (by omega) (by dsimp [N]; omega), hone']
  ring

/-- Actual full equality recovers the homogenized gap product, including gap zero. -/
theorem hessenberg_gap_product (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) :
    hTilde (P.g 0) * hTilde (P.g 1) * hTilde (P.g 2) =
      hTilde (Q.g 0) * hTilde (Q.g 1) * hTilde (Q.g 2) := by
  have heB : P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
    rwa [Profile.toBetaDiagram_schur, Profile.toBetaDiagram_schur]
  have hlarge := P.toBetaDiagram.largestLabel_eq_of_schur_eq Q.toBetaDiagram
    P.toBetaDiagram_connected Q.toBetaDiagram_connected heB
  change P.xi 0 - P.zeta 3 = Q.xi 0 - Q.zeta 3 at hlarge
  have hPi := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M 0 3) P.indices_four
  have hQi := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M 0 3) Q.indices_four
  norm_num [fourIndices] at hPi hQi
  have hN : (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 =
      (Q.r 0 : ℤ) + Q.r 1 + Q.r 2 + Q.r 3 - Q.g 0 - Q.g 1 - Q.g 2 := by
    omega
  have hp := largest_interval_derivative (P.r 0) (P.r 1) (P.r 2) (P.r 3)
    (P.g 0) (P.g 1) (P.g 2) (P.four_domain hP)
  have hq := largest_interval_derivative (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3)
    (Q.g 0) (Q.g 1) (Q.g 2) (Q.four_domain hQ)
  have hh := congrArg (MvPolynomial.pderiv
    ((P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2).toNat)
    ((Profile.schur_eq_iff_schurHom_eq P Q).mp he)
  rw [P.schurHom_four_interval hP, Q.schurHom_four_interval hQ, hp, hN, hq] at hh
  linear_combination -hh

private theorem select_two {α : Type*} (A B x : α) (xs : Multiset α)
    (he : ([A, B] : Multiset α) = x ::ₘ xs) :
    (x = A ∧ xs = [B]) ∨ (x = B ∧ xs = [A]) := by
  have hx : x ∈ ([A, B] : Multiset α) := by rw [he]; simp
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · left; refine ⟨rfl, ?_⟩
    change x ::ₘ ([B] : Multiset α) = x ::ₘ xs at he
    exact (Multiset.cons_inj_right x).mp he.symm
  · right; refine ⟨rfl, ?_⟩
    have hswap : ([A, x] : Multiset α) = x ::ₘ ([A] : Multiset α) := by
      change A ::ₘ (x ::ₘ 0) = x ::ₘ (A ::ₘ 0)
      exact Multiset.cons_swap A x 0
    exact (Multiset.cons_inj_right x).mp (he.symm.trans hswap)

private theorem select_three {α : Type*} (A B C x : α) (xs : Multiset α)
    (he : ([A, B, C] : Multiset α) = x ::ₘ xs) :
    (x = A ∧ xs = [B, C]) ∨ (x = B ∧ xs = [A, C]) ∨
      (x = C ∧ xs = [A, B]) := by
  have hx : x ∈ ([A, B, C] : Multiset α) := by rw [he]; simp
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · left; refine ⟨rfl, ?_⟩
    change x ::ₘ ([B, C] : Multiset α) = x ::ₘ xs at he
    exact (Multiset.cons_inj_right x).mp he.symm
  · right; left; refine ⟨rfl, ?_⟩
    have hswap : ([A, x, C] : Multiset α) = x ::ₘ ([A, C] : Multiset α) := by
      change A ::ₘ (x ::ₘ (C ::ₘ 0)) = x ::ₘ (A ::ₘ (C ::ₘ 0))
      exact Multiset.cons_swap A x (C ::ₘ 0)
    exact (Multiset.cons_inj_right x).mp (he.symm.trans hswap)
  · right; right; refine ⟨rfl, ?_⟩
    have hswap : ([A, B, x] : Multiset α) = x ::ₘ ([A, B] : Multiset α) := by
      change A ::ₘ (B ::ₘ (x ::ₘ 0)) = x ::ₘ (A ::ₘ (B ::ₘ 0))
      calc
        A ::ₘ (B ::ₘ (x ::ₘ 0)) = A ::ₘ (x ::ₘ (B ::ₘ 0)) :=
          congrArg (fun t : Multiset α => A ::ₘ t) (Multiset.cons_swap B x 0)
        _ = x ::ₘ (A ::ₘ (B ::ₘ 0)) := Multiset.cons_swap A x (B ::ₘ 0)
    exact (Multiset.cons_inj_right x).mp (he.symm.trans hswap)

private theorem rel_singleton_reading {α β : Type*} {r : α → β → Prop}
    {a : α} {b : β} (h : Multiset.Rel r [a] [b]) : r a b := by
  change Multiset.Rel r (a ::ₘ 0) (b ::ₘ 0) at h
  obtain ⟨y, ys, hay, hrest, he⟩ := Multiset.rel_cons_left.mp h
  have hy0 : ys = 0 := Multiset.rel_zero_left.mp hrest
  subst ys
  have hy : b = y := (Multiset.cons_inj_left 0).mp he
  subst y
  exact hay

private theorem rel_two_reading {α β : Type*} {r : α → β → Prop}
    {a b : α} {A B : β} (h : Multiset.Rel r [a, b] [A, B]) :
    (r a A ∧ r b B) ∨ (r a B ∧ r b A) := by
  change Multiset.Rel r (a ::ₘ (b ::ₘ 0)) (A ::ₘ (B ::ₘ 0)) at h
  obtain ⟨y, ys, hay, hrest, he⟩ := Multiset.rel_cons_left.mp h
  rcases select_two A B y ys he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨hay, rel_singleton_reading hrest⟩
  · exact Or.inr ⟨hay, rel_singleton_reading hrest⟩

/-- Every three-block pairing is enumerated structurally, including repeated equal blocks. -/
theorem rel_three_reading {α β : Type*} {r : α → β → Prop}
    {a b c : α} {A B C : β} (h : Multiset.Rel r [a, b, c] [A, B, C]) :
    (r a A ∧ r b B ∧ r c C) ∨ (r a A ∧ r b C ∧ r c B) ∨
    (r a B ∧ r b A ∧ r c C) ∨ (r a B ∧ r b C ∧ r c A) ∨
    (r a C ∧ r b A ∧ r c B) ∨ (r a C ∧ r b B ∧ r c A) := by
  change Multiset.Rel r (a ::ₘ (b ::ₘ (c ::ₘ 0))) (A ::ₘ (B ::ₘ (C ::ₘ 0))) at h
  obtain ⟨y, ys, hay, hrest, he⟩ := Multiset.rel_cons_left.mp h
  rcases select_three A B C y ys he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases rel_two_reading hrest with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact Or.inl ⟨hay, hb, hc⟩
    · exact Or.inr (Or.inl ⟨hay, hb, hc⟩)
  · rcases rel_two_reading hrest with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hay, hb, hc⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hay, hb, hc⟩)))
  · rcases rel_two_reading hrest with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hay, hb, hc⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hay, hb, hc⟩))))

private theorem hom_three_product_reading (a b c d e f : ℕ)
    (h : hTilde (a : ℤ) * hTilde (b : ℤ) * hTilde (c : ℤ) =
      hTilde (d : ℤ) * hTilde (e : ℤ) * hTilde (f : ℤ)) :
    tripleMatch (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ) (e : ℤ) (f : ℤ) := by
  have hx (k : ℕ) : hTilde (k : ℤ) = (MvPolynomial.X k : HomLambda) := by
    rw [hTilde, ite_eq_right (show ¬ (k : ℤ) < 0 by omega)]
    congr 1
  rw [hx a, hx b, hx c, hx d, hx e, hx f] at h
  let ex (i : ℕ) : ℕ →₀ ℕ := Finsupp.single i 1
  have hm : (MvPolynomial.monomial (ex a + ex b + ex c) (1 : ℚ) : HomLambda) =
      MvPolynomial.monomial (ex d + ex e + ex f) 1 := by
    simpa only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one, ex] using h
  have he := MvPolynomial.monomial_left_injective (show (1 : ℚ) ≠ 0 by norm_num) hm
  have hs := congrArg Finsupp.toMultiset he
  have hlist : ([a, b, c] : Multiset ℕ) = ([d, e, f] : Multiset ℕ) := by
    simpa only [ex, Finsupp.toMultiset_add, Finsupp.toMultiset_single,
      one_nsmul, add_assoc, Multiset.singleton_add, ← Multiset.cons_coe,
      Multiset.coe_nil, Multiset.cons_zero] using hs
  have hmatches := rel_three_reading (r := fun x y : ℕ => x = y)
    (a := a) (b := b) (c := c) (A := d) (B := e) (C := f)
    (Multiset.rel_eq.mpr hlist)
  rcases hmatches with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp [tripleMatch]

/-- Independent generator exponents recover every gap, including the index zero. -/
theorem hessenberg_gap_reading (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) :
    tripleMatch (P.g 0) (P.g 1) (P.g 2) (Q.g 0) (Q.g 1) (Q.g 2) := by
  exact hom_three_product_reading (P.g 0) (P.g 1) (P.g 2) (Q.g 0) (Q.g 1) (Q.g 2)
    (hessenberg_gap_product P Q hP hQ he)

/-- The numerical minimum is derived from full equality, not supplied as a class certificate. -/
theorem hessenberg_minimum_eq (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) :
    min (P.g 0) (min (P.g 1) (P.g 2)) =
      min (Q.g 0) (min (Q.g 1) (Q.g 2)) := by
  have hh := hessenberg_gap_reading P Q hP hQ he
  unfold tripleMatch at hh
  omega

/-- Unrestricted Hessenberg mates have the same actual minimum-cut component inventory. -/
theorem hessenberg_minimum_inventory (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) :
    let c := min (P.g 0) (min (P.g 1) (P.g 2))
    Multiset.Rel (fun X Y : Σ k : ℕ, BetaDiagram k =>
      X.2.schur = Y.2.schur ∧ X.1 = Y.1)
      (minimumBlocks P c : Multiset _) (minimumBlocks Q c : Multiset _) := by
  dsimp
  apply minimum_block_inventory P Q hP hQ _ rfl
    (hessenberg_minimum_eq P Q hP hQ he) he

/-- Small component equality recovers a literal profile or its rotation. -/
theorem small_profile_rigidity {n : ℕ} (P Q : Profile n) (hn : n ≤ 2)
    (he : P.schur = Q.schur) : P = Q ∨ P = Q.rotate := by
  have heB : P.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
    rwa [Profile.toBetaDiagram_schur, Profile.toBetaDiagram_schur]
  rcases P.toBetaDiagram.small_rows_rigidity_same_order Q.toBetaDiagram
    P.toBetaDiagram_connected Q.toBetaDiagram_connected (by omega) heB
    with ⟨c, hr, hz⟩ | ⟨c, hr, hz⟩
  · have hc := hz (Fin.last n)
    change P.zeta (Fin.last n) = Q.zeta (Fin.last n) + c at hc
    rw [P.zeta_last, Q.zeta_last] at hc
    have hc0 : c = 0 := by omega
    left
    apply Profile.eq_of_beta_eq
    · funext i
      have hh := hr i
      change P.xi i = Q.xi i + c at hh
      omega
    · funext i
      have hh := hz i
      change P.zeta i = Q.zeta i + c at hh
      omega
  · have hc := hz (Fin.last n)
    change P.zeta (Fin.last n) = c - Q.xi (Fin.last n).rev at hc
    simp only [Profile.zeta_last, Fin.rev_last] at hc
    have hc0 : c = Q.xi 0 := by omega
    right
    apply Profile.eq_of_beta_eq
    · funext i
      rw [Profile.xi_rotate]
      have hh := hr i
      change P.xi i = c - Q.zeta i.rev at hh
      omega
    · funext i
      rw [Profile.zeta_rotate]
      have hh := hz i
      change P.zeta i = c - Q.xi i.rev at hh
      omega

/-- Motion of a genuine cut block, with the actual order equality carrying the transport. -/
def BlockMotion (X Y : Σ n : ℕ, Profile n) : Prop :=
  ∃ h : X.1 = Y.1, X.2 = (h.symm ▸ Y.2) ∨ X.2 = (h.symm ▸ Y.2).rotate

/-- All cut-block orientations and orders are derived from the unrestricted full equality. -/
theorem hessenberg_minimum_block_motions (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) :
    let c := min (P.g 0) (min (P.g 1) (P.g 2))
    Multiset.Rel BlockMotion (minimumProfiles P c : Multiset _)
      (minimumProfiles Q c : Multiset _) := by
  dsimp
  let c := min (P.g 0) (min (P.g 1) (P.g 2))
  have hh := hessenberg_minimum_inventory P Q hP hQ he
  change Multiset.Rel _
    (↑(minimumBlocks P c) : Multiset (Σ k : ℕ, BetaDiagram k))
    (↑(minimumBlocks Q c) : Multiset (Σ k : ℕ, BetaDiagram k)) at hh
  simp only [minimumBlocks, ← Multiset.map_coe, Multiset.rel_map,
    Profile.toBetaDiagram_schur] at hh
  apply hh.mono
  intro X hX Y hY hXY
  have hn := minimum_profile_order P c rfl X (by simpa using hX)
  rcases X with ⟨n, XP⟩
  rcases Y with ⟨m, YP⟩
  have hnm : n = m := by
    have hh := hXY.2
    dsimp at hh
    omega
  subst m
  refine ⟨rfl, ?_⟩
  exact small_profile_rigidity XP YP hn hXY.1

private theorem blockMotion_same {n : ℕ} (P Q : Profile n) :
    BlockMotion ⟨n, P⟩ ⟨n, Q⟩ ↔ P = Q ∨ P = Q.rotate := by
  constructor
  · rintro ⟨h, hh⟩
    cases h
    exact hh
  · intro hh
    exact ⟨rfl, hh⟩

private theorem singleton_motion (P Q : Profile 0)
    (h : BlockMotion ⟨0, P⟩ ⟨0, Q⟩) : P.r 0 = Q.r 0 := by
  rcases (blockMotion_same P Q).mp h with h | h
  · exact congrArg (fun T : Profile 0 => T.r 0) h
  · simpa [Profile.rotate] using congrArg (fun T : Profile 0 => T.r 0) h

private theorem pair_motion (P Q : Profile 1)
    (h : BlockMotion ⟨1, P⟩ ⟨1, Q⟩) :
    ((P.r 0 = Q.r 0 ∧ P.r 1 = Q.r 1) ∨
      (P.r 0 = Q.r 1 ∧ P.r 1 = Q.r 0)) ∧ P.g 0 = Q.g 0 := by
  rcases (blockMotion_same P Q).mp h with h | h
  · exact ⟨Or.inl ⟨congrArg (fun T : Profile 1 => T.r 0) h,
      congrArg (fun T : Profile 1 => T.r 1) h⟩,
      congrArg (fun T : Profile 1 => T.g 0) h⟩
  · have h0 := congrArg (fun T : Profile 1 => T.r 0) h
    have h1 := congrArg (fun T : Profile 1 => T.r 1) h
    have hg := congrArg (fun T : Profile 1 => T.g 0) h
    simp [Profile.rotate] at h0 h1 hg
    exact ⟨Or.inr ⟨h0, h1⟩, hg⟩

/-- The three-minimum case for actual profiles, against every actual Hessenberg mate. -/
theorem three_minimum_profile_rigidity (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) (c : ℕ)
    (hg0 : P.g 0 = c) (hg1 : P.g 1 = c) (hg2 : P.g 2 = c) :
    P = Q ∨ P = Q.rotate := by
  have hg := hessenberg_gap_reading P Q hP hQ he
  simp only [tripleMatch, hg0, hg1, hg2] at hg
  have hQ0 : Q.g 0 = c := by omega
  have hQ1 : Q.g 1 = c := by omega
  have hQ2 : Q.g 2 = c := by omega
  have hdP := P.four_domain hP
  have hdQ := Q.four_domain hQ
  simp only [FourDomain, hg0, hg1, hg2] at hdP
  simp only [FourDomain, hQ0, hQ1, hQ2] at hdQ
  have hh := (Profile.schur_eq_iff_schurHom_eq P Q).mp he
  rw [P.schurHom_four_interval hP, Q.schurHom_four_interval hQ] at hh
  simp only [hg0, hg1, hg2, hQ0, hQ1, hQ2] at hh
  have hs := uniform_minimum_rigidity c
    ((P.r 0 : ℤ) - c) ((P.r 1 : ℤ) - c) ((P.r 2 : ℤ) - c) ((P.r 3 : ℤ) - c)
    ((Q.r 0 : ℤ) - c) ((Q.r 1 : ℤ) - c) ((Q.r 2 : ℤ) - c) ((Q.r 3 : ℤ) - c)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (by simpa only [sub_add_cancel] using hh)
  rcases hs with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
  · left
    apply Profile.ext
    · funext i
      fin_cases i <;> simp <;> omega
    · funext j
      fin_cases j <;> simp <;> omega
  · right
    apply Profile.ext
    · funext i
      fin_cases i <;> simp [Profile.rotate] <;> omega
    · funext j
      fin_cases j <;> simp [Profile.rotate] <;> omega

/-- The displayed exceptional class really has four distinct actual profiles. -/
theorem family_four_distinct (w b c : ℕ) (hcw : c < w) (hb : c + w < b) :
    ([familyF w b c hcw hb, (familyF w b c hcw hb).rotate,
      familyH w b c hcw hb, (familyH w b c hcw hb).rotate] : List (Profile 3)).Nodup := by
  have hFH := family_ne w b c hcw hb
  have hFHrot := family_ne_rotate w b c hcw hb
  have hFFrot := familyF_not_symmetric w b c hcw hb
  have hHHrot := familyH_not_symmetric w b c hcw hb
  have hFrotH : (familyF w b c hcw hb).rotate ≠ familyH w b c hcw hb := by
    intro he
    apply hFHrot
    have hh := congrArg Profile.rotate he
    simpa using hh
  have hFrotHrot : (familyF w b c hcw hb).rotate ≠ (familyH w b c hcw hb).rotate := by
    intro he
    apply hFH
    have hh := congrArg Profile.rotate he
    simpa using hh
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, hFH, hFHrot, hFFrot, hHHrot, hFrotH, hFrotHrot,
    false_or, not_false_eq_true, and_self]

/-- Full polynomial equality recovers the exceptional parameters, including the zero-gap boundary. -/
theorem family_parameters_recovered (w b c W B C : ℕ)
    (hcw : c < w) (hb : c + w < b) (hCW : C < W) (hB : C + W < B)
    (he : (familyF w b c hcw hb).schur = (familyF W B C hCW hB).schur) :
    w = W ∧ b = B ∧ c = C := by
  have hg := hessenberg_gap_reading (familyF w b c hcw hb) (familyF W B C hCW hB)
    (familyF_hessenberg w b c hcw hb) (familyF_hessenberg W B C hCW hB) he
  simp only [familyF, Matrix.cons_val, tripleMatch] at hg
  have hcC : c = C := by omega
  have hwW : w = W := by omega
  have heB : (familyF w b c hcw hb).toBetaDiagram.schur =
      (familyF W B C hCW hB).toBetaDiagram.schur := by
    rwa [Profile.toBetaDiagram_schur, Profile.toBetaDiagram_schur]
  have hrow := congrArg (Base.initialForm Base.squareWeight.generatorWeight) heB
  rw [BetaDiagram.square_initialForm, BetaDiagram.square_initialForm] at hrow
  have hprod : complete (w : ℤ) * complete (b : ℤ) * complete (b : ℤ) *
      complete ((b + w - c : ℕ) : ℤ) =
      complete (W : ℤ) * complete (B : ℤ) * complete (B : ℤ) *
      complete ((B + W - C : ℕ) : ℤ) := by
    simpa [Profile.toBetaDiagram, Profile.xi_sub_zeta, Fin.prod_univ_succ,
      familyF, mul_assoc] using hrow
  have hm := four_product_reading (show 0 < (w : ℤ) by omega)
    (show 0 < (b : ℤ) by omega) (show 0 < (b : ℤ) by omega)
    (show 0 < ((b + w - c : ℕ) : ℤ) by omega)
    (show 0 < (W : ℤ) by omega) (show 0 < (B : ℤ) by omega)
    (show 0 < (B : ℤ) by omega) (show 0 < ((B + W - C : ℕ) : ℤ) by omega) hprod
  unfold fourMatch tripleMatch at hm
  have hbB : b = B := by omega
  exact ⟨hwW, hbB, hcC⟩

private theorem tuple_four_eq (v : Fin 4 → ℕ) (a b c d : ℕ)
    (h0 : v 0 = a) (h1 : v 1 = b) (h2 : v 2 = c) (h3 : v 3 = d) :
    v = ![a, b, c, d] := by
  funext i
  fin_cases i <;> simp_all

private theorem tuple_three_eq (v : Fin 3 → ℕ) (a b c : ℕ)
    (h0 : v 0 = a) (h1 : v 1 = b) (h2 : v 2 = c) :
    v = ![a, b, c] := by
  funext i
  fin_cases i <;> simp_all

/-- All row words with an end-position two-row block, without excluding repeated rows. -/
def rowsL (P Q : Profile 3) : Prop :=
  Q.r = ![P.r 0, P.r 1, P.r 2, P.r 3] ∨
  Q.r = ![P.r 1, P.r 0, P.r 2, P.r 3] ∨
  Q.r = ![P.r 0, P.r 1, P.r 3, P.r 2] ∨
  Q.r = ![P.r 1, P.r 0, P.r 3, P.r 2]

/-- All row words with an interior-position two-row block. -/
def rowsM (P Q : Profile 3) : Prop :=
  Q.r = ![P.r 0, P.r 2, P.r 3, P.r 1] ∨
  Q.r = ![P.r 1, P.r 2, P.r 3, P.r 0] ∨
  Q.r = ![P.r 0, P.r 3, P.r 2, P.r 1] ∨
  Q.r = ![P.r 1, P.r 3, P.r 2, P.r 0]

private theorem rowsL_of_fields (P Q : Profile 3)
    (hs : (P.r 0 = Q.r 0 ∧ P.r 1 = Q.r 1) ∨ (P.r 0 = Q.r 1 ∧ P.r 1 = Q.r 0))
    (hb : (P.r 2 = Q.r 2 ∧ P.r 3 = Q.r 3) ∨ (P.r 2 = Q.r 3 ∧ P.r 3 = Q.r 2)) :
    rowsL P Q := by
  rcases hs with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases hb with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · exact Or.inl (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega))
  · exact Or.inr (Or.inr (Or.inl
      (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega))))
  · exact Or.inr (Or.inl
      (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)))
  · exact Or.inr (Or.inr (Or.inr
      (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega))))

private theorem rowsM_of_fields (P Q : Profile 3)
    (hs : (P.r 0 = Q.r 0 ∧ P.r 1 = Q.r 3) ∨ (P.r 0 = Q.r 3 ∧ P.r 1 = Q.r 0))
    (hb : (P.r 2 = Q.r 1 ∧ P.r 3 = Q.r 2) ∨ (P.r 2 = Q.r 2 ∧ P.r 3 = Q.r 1)) :
    rowsM P Q := by
  rcases hs with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases hb with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · exact Or.inl (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega))
  · exact Or.inr (Or.inr (Or.inl
      (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega))))
  · exact Or.inr (Or.inl
      (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)))
  · exact Or.inr (Or.inr (Or.inr
      (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega))))

private theorem reassemble_L_to_L (P Q : Profile 3) (c d : ℕ) (hcd : c < d)
    (hP0 : P.g 0 = c) (hP1 : P.g 1 = c) (hP2 : P.g 2 = d)
    (hQ0 : Q.g 0 = c) (hQ1 : Q.g 1 = c) (hQ2 : Q.g 2 = d)
    (hm : Multiset.Rel BlockMotion (minimumProfiles P c : Multiset _)
      (minimumProfiles Q c : Multiset _)) : rowsL P Q := by
  simp only [minimumProfiles, hP0, hP1, hP2, hQ0, hQ1, hQ2,
    if_pos rfl, if_neg hcd.ne', ← Multiset.cons_coe, Multiset.coe_nil] at hm
  have hh := rel_three_reading hm
  rcases hh with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have hs0 := singleton_motion _ _ h0
    have hs1 := singleton_motion _ _ h1
    have hp := pair_motion _ _ h2
    simp [Profile.slice] at hs0 hs1 hp
    exact rowsL_of_fields P Q (Or.inl ⟨hs0, hs1⟩) hp.1
  · obtain ⟨ho, _⟩ := h1
    norm_num at ho
  · have hs0 := singleton_motion _ _ h0
    have hs1 := singleton_motion _ _ h1
    have hp := pair_motion _ _ h2
    simp [Profile.slice] at hs0 hs1 hp
    exact rowsL_of_fields P Q (Or.inr ⟨hs0, hs1⟩) hp.1
  · obtain ⟨ho, _⟩ := h1
    norm_num at ho
  · obtain ⟨ho, _⟩ := h0
    norm_num at ho
  · obtain ⟨ho, _⟩ := h0
    norm_num at ho

private theorem reassemble_L_to_M (P Q : Profile 3) (c d : ℕ) (hcd : c < d)
    (hP0 : P.g 0 = c) (hP1 : P.g 1 = c) (hP2 : P.g 2 = d)
    (hQ0 : Q.g 0 = c) (hQ1 : Q.g 1 = d) (hQ2 : Q.g 2 = c)
    (hm : Multiset.Rel BlockMotion (minimumProfiles P c : Multiset _)
      (minimumProfiles Q c : Multiset _)) : rowsM P Q := by
  simp only [minimumProfiles, hP0, hP1, hP2, hQ0, hQ1, hQ2,
    if_pos rfl, if_neg hcd.ne', ← Multiset.cons_coe, Multiset.coe_nil] at hm
  have hh := rel_three_reading hm
  rcases hh with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · obtain ⟨ho, _⟩ := h1
    norm_num at ho
  · have hs0 := singleton_motion _ _ h0
    have hs1 := singleton_motion _ _ h1
    have hp := pair_motion _ _ h2
    simp [Profile.slice] at hs0 hs1 hp
    exact rowsM_of_fields P Q (Or.inl ⟨hs0, hs1⟩) hp.1
  · obtain ⟨ho, _⟩ := h0
    norm_num at ho
  · obtain ⟨ho, _⟩ := h0
    norm_num at ho
  · have hs0 := singleton_motion _ _ h0
    have hs1 := singleton_motion _ _ h1
    have hp := pair_motion _ _ h2
    simp [Profile.slice] at hs0 hs1 hp
    exact rowsM_of_fields P Q (Or.inr ⟨hs0, hs1⟩) hp.1
  · obtain ⟨ho, _⟩ := h1
    norm_num at ho

/-- Full equality exhausts the actual two-minimum arrangements, modulo global rotation. -/
theorem two_minimum_L_reassembly (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur)
    (c d : ℕ) (hcd : c < d)
    (hP0 : P.g 0 = c) (hP1 : P.g 1 = c) (hP2 : P.g 2 = d) :
    (Q.g = ![c, c, d] ∧ rowsL P Q) ∨
    (Q.g = ![c, d, c] ∧ rowsM P Q) ∨
    (Q.rotate.g = ![c, c, d] ∧ rowsL P Q.rotate) := by
  have hg := hessenberg_gap_reading P Q hP hQ he
  simp only [tripleMatch, hP0, hP1, hP2] at hg
  have hcases :
      (Q.g 0 = c ∧ Q.g 1 = c ∧ Q.g 2 = d) ∨
      (Q.g 0 = c ∧ Q.g 1 = d ∧ Q.g 2 = c) ∨
      (Q.g 0 = d ∧ Q.g 1 = c ∧ Q.g 2 = c) := by omega
  have hmin : min (P.g 0) (min (P.g 1) (P.g 2)) = c := by omega
  have hm := hessenberg_minimum_block_motions P Q hP hQ he
  simp only [hmin] at hm
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact Or.inl ⟨tuple_three_eq _ _ _ _ h0 h1 h2,
      reassemble_L_to_L P Q c d hcd hP0 hP1 hP2 h0 h1 h2 hm⟩
  · exact Or.inr (Or.inl ⟨tuple_three_eq _ _ _ _ h0 h1 h2,
      reassemble_L_to_M P Q c d hcd hP0 hP1 hP2 h0 h1 h2 hm⟩)
  · have he' : P.schur = Q.rotate.schur := by rwa [Profile.schur_rotate]
    have hm' := hessenberg_minimum_block_motions P Q.rotate hP (Q.hessenberg_rotate hQ) he'
    simp only [hmin] at hm'
    have h0' : Q.rotate.g 0 = c := by simpa [Profile.rotate] using h2
    have h1' : Q.rotate.g 1 = c := by simpa [Profile.rotate] using h1
    have h2' : Q.rotate.g 2 = d := by simpa [Profile.rotate] using h0
    exact Or.inr (Or.inr ⟨tuple_three_eq _ _ _ _ h0' h1' h2',
      reassemble_L_to_L P Q.rotate c d hcd hP0 hP1 hP2 h0' h1' h2' hm'⟩)

/-- Simultaneous L flips still fix both singleton order and block orientation. -/
theorem two_minimum_LL_both_flip (p q a b d : ℤ) (c : ℕ)
    (hL : FourDomain p q a b c c d) (hflip : FourDomain q p b a c c d)
    (hcd : (c : ℤ) < d)
    (he : fourInterval hTilde p q a b c c d = fourInterval hTilde q p b a c c d) :
    p = q ∧ a = b := by
  have hh := congrArg (minimumMap c) he
  rw [minimumMap_L p q a b d c hL hcd, minimumMap_L q p b a d c hflip hcd] at hh
  have hq := congrArg (fun f : Polynomial HomLambda => f.coeff 2) hh
  simp only [coeff_quadratic_two] at hq
  have hq' := congrArg dehom hq
  simp only [quadraticL, map_sub, map_mul, dehom_hTilde, ← complete_eq_hh] at hq'
  have hN : q + p + b + a - 2 * c - d = p + q + a + b - 2 * c - d := by omega
  have hx : q + p + b - 2 * c = p + q + b - 2 * c := by omega
  rw [hN, hx] at hq'
  have hprod : complete (p + q + a - 2 * c) * complete b =
      complete (p + q + b - 2 * c) * complete a := by
    linear_combination hq'
  have haEq : a = b := by
    rcases hL with ⟨hc0, hc1, hd, hp, hq, ha, hb⟩
    rcases hflip with ⟨hc2, hc3, hd1, hp1, hq1, hb1, ha1⟩
    rcases complete_two_product_reading (show 0 < p + q + a - 2 * c by omega)
      (show 0 < b by omega) (show 0 < p + q + b - 2 * c by omega)
      (show 0 < a by omega) hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  subst b
  exact ⟨two_minimum_LL_singleton_flip p q a a d c hL hflip hcd he, rfl⟩

/-- The two genuinely different exceptional rotation orbits. -/
def FamilyRelation (P Q : Profile 3) : Prop :=
  ∃ w b c : ℕ, ∃ hcw : c < w, ∃ hb : c + w < b,
    (((P = familyF w b c hcw hb ∨ P = (familyF w b c hcw hb).rotate) ∧
      (Q = familyH w b c hcw hb ∨ Q = (familyH w b c hcw hb).rotate)) ∨
     ((P = familyH w b c hcw hb ∨ P = (familyH w b c hcw hb).rotate) ∧
      (Q = familyF w b c hcw hb ∨ Q = (familyF w b c hcw hb).rotate)))

/-- The complete proposed four-row alternatives are literal profiles, not masks. -/
def Classified (P Q : Profile 3) : Prop := P = Q ∨ P = Q.rotate ∨ FamilyRelation P Q

private theorem familyRelation_rotate_right {P Q : Profile 3}
    (h : FamilyRelation P Q.rotate) : FamilyRelation P Q := by
  obtain ⟨w, b, c, hcw, hb, hh⟩ := h
  refine ⟨w, b, c, hcw, hb, ?_⟩
  rcases hh with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · left; refine ⟨hP, ?_⟩
    rcases hQ with hQ | hQ
    · right
      have hh := congrArg Profile.rotate hQ
      simpa using hh
    · left
      have hh := congrArg Profile.rotate hQ
      simpa using hh
  · right; refine ⟨hP, ?_⟩
    rcases hQ with hQ | hQ
    · right
      have hh := congrArg Profile.rotate hQ
      simpa using hh
    · left
      have hh := congrArg Profile.rotate hQ
      simpa using hh

theorem classified_rotate_right {P Q : Profile 3}
    (h : Classified P Q.rotate) : Classified P Q := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl (by simpa using h)
  · exact Or.inr (Or.inr (familyRelation_rotate_right h))

theorem classified_symm {P Q : Profile 3} (h : Classified P Q) : Classified Q P := by
  rcases h with h | h | ⟨w, b, c, hcw, hb, hh⟩
  · exact Or.inl h.symm
  · right; left
    have hh := congrArg Profile.rotate h
    simpa using hh.symm
  · right; right
    refine ⟨w, b, c, hcw, hb, ?_⟩
    rcases hh with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · exact Or.inr ⟨hQ, hP⟩
    · exact Or.inl ⟨hQ, hP⟩

private theorem L_same_position (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur)
    (c d : ℕ) (hcd : c < d)
    (hP0 : P.g 0 = c) (hP1 : P.g 1 = c) (hP2 : P.g 2 = d)
    (hQg : Q.g = ![c, c, d]) (hrows : rowsL P Q) : P = Q := by
  have hL := P.four_domain hP
  simp only [hP0, hP1, hP2] at hL
  have hflip := Q.four_domain hQ
  have hh := (Profile.schur_eq_iff_schurHom_eq P Q).mp he
  rw [P.schurHom_four_interval hP, Q.schurHom_four_interval hQ] at hh
  unfold rowsL at hrows
  rcases hrows with hrows | hrows | hrows | hrows
  · apply Profile.ext
    · rw [hrows]
      exact tuple_four_eq P.r _ _ _ _ rfl rfl rfl rfl
    · funext i
      fin_cases i <;> simp [hQg] <;> omega
  · simp only [hP0, hP1, hP2, hrows, hQg, Matrix.cons_val] at hflip hh
    have hm := two_minimum_LL_singleton_flip (P.r 0) (P.r 1) (P.r 2) (P.r 3) d c
      hL hflip (by omega) hh
    apply Profile.ext
    · funext i
      fin_cases i <;> simp [hrows] <;> omega
    · funext i
      fin_cases i <;> simp [hQg] <;> omega
  · simp only [hP0, hP1, hP2, hrows, hQg, Matrix.cons_val] at hflip hh
    have hm := two_minimum_LL_block_flip (P.r 0) (P.r 1) (P.r 2) (P.r 3) d c
      hL hflip (by omega) hh
    apply Profile.ext
    · funext i
      fin_cases i <;> simp [hrows] <;> omega
    · funext i
      fin_cases i <;> simp [hQg] <;> omega
  · simp only [hP0, hP1, hP2, hrows, hQg, Matrix.cons_val] at hflip hh
    obtain ⟨h0, h1⟩ := two_minimum_LL_both_flip (P.r 0) (P.r 1) (P.r 2) (P.r 3) d c
      hL hflip (by omega) hh
    apply Profile.ext
    · funext i
      fin_cases i <;> simp [hrows] <;> omega
    · funext i
      fin_cases i <;> simp [hQg] <;> omega

private theorem L_to_M_family (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur)
    (c d : ℕ) (hcd : c < d)
    (hP0 : P.g 0 = c) (hP1 : P.g 1 = c) (hP2 : P.g 2 = d)
    (hQg : Q.g = ![c, d, c]) (hQr : Q.r = ![P.r 0, P.r 2, P.r 3, P.r 1]) :
    FamilyRelation P Q := by
  have hL := P.four_domain hP
  have hM := Q.four_domain hQ
  have hh := (Profile.schur_eq_iff_schurHom_eq P Q).mp he
  rw [P.schurHom_four_interval hP, Q.schurHom_four_interval hQ] at hh
  simp only [hP0, hP1, hP2, hQg, hQr, Matrix.cons_val] at hL hM hh
  obtain ⟨hp, hq, hb, hbound⟩ := two_minimum_LM_necessity
    (P.r 0) (P.r 1) (P.r 2) (P.r 3) d c hL hM (by omega) hh
  have hparam : c + d < P.r 2 := by omega
  have hPF : P = familyF d (P.r 2) c hcd hparam := by
    apply Profile.ext
    · funext i
      fin_cases i <;> simp [familyF] <;> omega
    · funext i
      fin_cases i <;> simp [familyF] <;> omega
  have hQH : Q = familyH d (P.r 2) c hcd hparam := by
    apply Profile.ext
    · funext i
      fin_cases i <;> simp [familyH, hQr] <;> omega
    · funext i
      fin_cases i <;> simp [familyH, hQg]
  exact ⟨d, P.r 2, c, hcd, hparam, Or.inl ⟨Or.inl hPF, Or.inl hQH⟩⟩

private theorem L_to_M_other_impossible (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur)
    (c d : ℕ) (hcd : c < d)
    (hP0 : P.g 0 = c) (hP1 : P.g 1 = c) (hP2 : P.g 2 = d)
    (hQg : Q.g = ![c, d, c]) (hQr : Q.r = ![P.r 0, P.r 3, P.r 2, P.r 1]) : False := by
  have hL := P.four_domain hP
  have hM := Q.four_domain hQ
  have hh := (Profile.schur_eq_iff_schurHom_eq P Q).mp he
  rw [P.schurHom_four_interval hP, Q.schurHom_four_interval hQ] at hh
  simp only [hP0, hP1, hP2, hQg, hQr, Matrix.cons_val] at hL hM hh
  exact two_minimum_LM_other_ne (P.r 0) (P.r 1) (P.r 2) (P.r 3) d c
    hL hM (by omega) hh

/-- The complete class of every actual L-type profile, against unrestricted Hessenberg mates. -/
theorem two_minimum_L_classification (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur)
    (c d : ℕ) (hcd : c < d)
    (hP0 : P.g 0 = c) (hP1 : P.g 1 = c) (hP2 : P.g 2 = d) :
    Classified P Q := by
  rcases two_minimum_L_reassembly P Q hP hQ he c d hcd hP0 hP1 hP2
    with ⟨hQg, hr⟩ | ⟨hQg, hr⟩ | ⟨hQg, hr⟩
  · exact Or.inl (L_same_position P Q hP hQ he c d hcd hP0 hP1 hP2 hQg hr)
  · unfold rowsM at hr
    rcases hr with hr | hr | hr | hr
    · exact Or.inr (Or.inr (L_to_M_family P Q hP hQ he c d hcd hP0 hP1 hP2 hQg hr))
    · have he' : P.schur = Q.rotate.schur := by rwa [Profile.schur_rotate]
      have hg' : Q.rotate.g = ![c, d, c] := by
        funext i; fin_cases i <;> simp [Profile.rotate, hQg]
      have hr' : Q.rotate.r = ![P.r 0, P.r 3, P.r 2, P.r 1] := by
        funext i; fin_cases i <;> simp [Profile.rotate, hr]
      exact False.elim (L_to_M_other_impossible P Q.rotate hP (Q.hessenberg_rotate hQ)
        he' c d hcd hP0 hP1 hP2 hg' hr')
    · exact False.elim (L_to_M_other_impossible P Q hP hQ he c d hcd hP0 hP1 hP2 hQg hr)
    · apply classified_rotate_right
      have he' : P.schur = Q.rotate.schur := by rwa [Profile.schur_rotate]
      have hg' : Q.rotate.g = ![c, d, c] := by
        funext i; fin_cases i <;> simp [Profile.rotate, hQg]
      have hr' : Q.rotate.r = ![P.r 0, P.r 2, P.r 3, P.r 1] := by
        funext i; fin_cases i <;> simp [Profile.rotate, hr]
      exact Or.inr (Or.inr (L_to_M_family P Q.rotate hP (Q.hessenberg_rotate hQ)
        he' c d hcd hP0 hP1 hP2 hg' hr'))
  · apply classified_rotate_right
    have he' : P.schur = Q.rotate.schur := by rwa [Profile.schur_rotate]
    exact Or.inl (L_same_position P Q.rotate hP (Q.hessenberg_rotate hQ) he'
      c d hcd hP0 hP1 hP2 hQg hr)

theorem classified_rotate_left {P Q : Profile 3}
    (h : Classified P.rotate Q) : Classified P Q :=
  classified_symm (classified_rotate_right (classified_symm h))

private def rowsMM (P Q : Profile 3) : Prop :=
  Q.r = ![P.r 0, P.r 1, P.r 2, P.r 3] ∨
  Q.r = ![P.r 3, P.r 1, P.r 2, P.r 0] ∨
  Q.r = ![P.r 0, P.r 2, P.r 1, P.r 3] ∨
  Q.r = ![P.r 3, P.r 2, P.r 1, P.r 0]

private theorem rowsMM_of_fields (P Q : Profile 3)
    (hs : (P.r 0 = Q.r 0 ∧ P.r 3 = Q.r 3) ∨ (P.r 0 = Q.r 3 ∧ P.r 3 = Q.r 0))
    (hb : (P.r 1 = Q.r 1 ∧ P.r 2 = Q.r 2) ∨ (P.r 1 = Q.r 2 ∧ P.r 2 = Q.r 1)) :
    rowsMM P Q := by
  rcases hs with ⟨h0, h3⟩ | ⟨h0, h3⟩ <;> rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega))
  · exact Or.inr (Or.inr (Or.inl
      (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega))))
  · exact Or.inr (Or.inl
      (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)))
  · exact Or.inr (Or.inr (Or.inr
      (tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega))))

private theorem reassemble_M_to_M (P Q : Profile 3) (c d : ℕ) (hcd : c < d)
    (hP0 : P.g 0 = c) (hP1 : P.g 1 = d) (hP2 : P.g 2 = c)
    (hQ0 : Q.g 0 = c) (hQ1 : Q.g 1 = d) (hQ2 : Q.g 2 = c)
    (hm : Multiset.Rel BlockMotion (minimumProfiles P c : Multiset _)
      (minimumProfiles Q c : Multiset _)) : rowsMM P Q := by
  simp only [minimumProfiles, hP0, hP1, hP2, hQ0, hQ1, hQ2,
    if_pos rfl, if_neg hcd.ne', ← Multiset.cons_coe, Multiset.coe_nil] at hm
  have hh := rel_three_reading hm
  rcases hh with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have hs0 := singleton_motion _ _ h0
    have hs1 := singleton_motion _ _ h2
    have hp := pair_motion _ _ h1
    simp [Profile.slice] at hs0 hs1 hp
    exact rowsMM_of_fields P Q (Or.inl ⟨hs0, hs1⟩) hp.1
  · obtain ⟨ho, _⟩ := h1
    norm_num at ho
  · obtain ⟨ho, _⟩ := h0
    norm_num at ho
  · obtain ⟨ho, _⟩ := h0
    norm_num at ho
  · obtain ⟨ho, _⟩ := h1
    norm_num at ho
  · have hs0 := singleton_motion _ _ h0
    have hs1 := singleton_motion _ _ h2
    have hp := pair_motion _ _ h1
    simp [Profile.slice] at hs0 hs1 hp
    exact rowsMM_of_fields P Q (Or.inr ⟨hs0, hs1⟩) hp.1

private theorem M_block_flip_classified (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur)
    (c d : ℕ) (hcd : c < d)
    (hP0 : P.g 0 = c) (hP1 : P.g 1 = d) (hP2 : P.g 2 = c)
    (hQg : Q.g = ![c, d, c]) (hQr : Q.r = ![P.r 0, P.r 2, P.r 1, P.r 3]) :
    Classified P Q := by
  have hM := P.four_domain hP
  have hflip := Q.four_domain hQ
  have hh := (Profile.schur_eq_iff_schurHom_eq P Q).mp he
  rw [P.schurHom_four_interval hP, Q.schurHom_four_interval hQ] at hh
  simp only [hP0, hP1, hP2, hQg, hQr, Matrix.cons_val] at hM hflip hh
  have hm := two_minimum_MM_block_flip (P.r 0) (P.r 3) (P.r 1) (P.r 2) d c
    hM hflip (by omega) hh
  rcases hm with hm | hm
  · right; left
    apply Profile.ext
    · funext i; fin_cases i <;> simp [Profile.rotate, hQr] <;> omega
    · funext i; fin_cases i <;> simp [Profile.rotate, hQg] <;> omega
  · left
    apply Profile.ext
    · funext i; fin_cases i <;> simp [hQr] <;> omega
    · funext i; fin_cases i <;> simp [hQg] <;> omega

-- The dependent component transports occur in every structural singleton/block placement.
set_option maxHeartbeats 1000000 in
/-- The complete class of every actual M-type profile, including exceptional mates of L type. -/
theorem two_minimum_M_classification (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur)
    (c d : ℕ) (hcd : c < d)
    (hP0 : P.g 0 = c) (hP1 : P.g 1 = d) (hP2 : P.g 2 = c) :
    Classified P Q := by
  have hg := hessenberg_gap_reading P Q hP hQ he
  simp only [tripleMatch, hP0, hP1, hP2] at hg
  have hcases :
      (Q.g 0 = c ∧ Q.g 1 = c ∧ Q.g 2 = d) ∨
      (Q.g 0 = c ∧ Q.g 1 = d ∧ Q.g 2 = c) ∨
      (Q.g 0 = d ∧ Q.g 1 = c ∧ Q.g 2 = c) := by omega
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact classified_symm (two_minimum_L_classification Q P hQ hP he.symm c d hcd h0 h1 h2)
  · have hmin : min (P.g 0) (min (P.g 1) (P.g 2)) = c := by omega
    have hm := hessenberg_minimum_block_motions P Q hP hQ he
    simp only [hmin] at hm
    have hr := reassemble_M_to_M P Q c d hcd hP0 hP1 hP2 h0 h1 h2 hm
    have hQg := tuple_three_eq Q.g c d c h0 h1 h2
    rcases hr with hr | hr | hr | hr
    · left
      apply Profile.ext
      · rw [hr]; exact tuple_four_eq P.r _ _ _ _ rfl rfl rfl rfl
      · funext i; fin_cases i <;> simp [hQg] <;> omega
    · apply classified_rotate_right
      have he' : P.schur = Q.rotate.schur := by rwa [Profile.schur_rotate]
      have hg' : Q.rotate.g = ![c, d, c] := by
        funext i; fin_cases i <;> simp [Profile.rotate, hQg]
      have hr' : Q.rotate.r = ![P.r 0, P.r 2, P.r 1, P.r 3] := by
        funext i; fin_cases i <;> simp [Profile.rotate, hr]
      exact M_block_flip_classified P Q.rotate hP (Q.hessenberg_rotate hQ) he'
        c d hcd hP0 hP1 hP2 hg' hr'
    · exact M_block_flip_classified P Q hP hQ he c d hcd hP0 hP1 hP2 hQg hr
    · right; left
      apply Profile.ext
      · funext i; fin_cases i <;> simp [Profile.rotate, hr]
      · funext i; fin_cases i <;> simp [Profile.rotate, hQg] <;> omega
  · apply classified_rotate_right
    have hg0 : Q.rotate.g 0 = c := by simpa [Profile.rotate] using h2
    have hg1 : Q.rotate.g 1 = c := by simpa [Profile.rotate] using h1
    have hg2 : Q.rotate.g 2 = d := by simpa [Profile.rotate] using h0
    have he' : Q.rotate.schur = P.schur := Q.schur_rotate.trans he.symm
    exact classified_symm (two_minimum_L_classification Q.rotate P (Q.hessenberg_rotate hQ)
      hP he' c d hcd hg0 hg1 hg2)

private theorem triple_motion (P Q : Profile 2)
    (h : BlockMotion ⟨2, P⟩ ⟨2, Q⟩) :
    (P.r 0 = Q.r 0 ∧ P.r 1 = Q.r 1 ∧ P.r 2 = Q.r 2 ∧
      P.g 0 = Q.g 0 ∧ P.g 1 = Q.g 1) ∨
    (P.r 0 = Q.r 2 ∧ P.r 1 = Q.r 1 ∧ P.r 2 = Q.r 0 ∧
      P.g 0 = Q.g 1 ∧ P.g 1 = Q.g 0) := by
  rcases (blockMotion_same P Q).mp h with h | h
  · left
    exact ⟨congrArg (fun T : Profile 2 => T.r 0) h,
      congrArg (fun T : Profile 2 => T.r 1) h,
      congrArg (fun T : Profile 2 => T.r 2) h,
      congrArg (fun T : Profile 2 => T.g 0) h,
      congrArg (fun T : Profile 2 => T.g 1) h⟩
  · right
    have h0 := congrArg (fun T : Profile 2 => T.r 0) h
    have h1 := congrArg (fun T : Profile 2 => T.r 1) h
    have h2 := congrArg (fun T : Profile 2 => T.r 2) h
    have hg0 := congrArg (fun T : Profile 2 => T.g 0) h
    have hg1 := congrArg (fun T : Profile 2 => T.g 1) h
    simp [Profile.rotate] at h0 h1 h2 hg0 hg1
    exact ⟨h0, h1, h2, hg0, hg1⟩

private theorem end_to_end_literal (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) (c : ℕ)
    (hP0 : P.g 0 = c) (hP1 : c < P.g 1) (hP2 : c < P.g 2)
    (hQ0 : Q.g 0 = c) (hQ1 : c < Q.g 1) (hQ2 : c < Q.g 2) : P = Q := by
  have hm := hessenberg_minimum_block_motions P Q hP hQ he
  have hmin : min (P.g 0) (min (P.g 1) (P.g 2)) = c := by omega
  dsimp only at hm
  rw [hmin] at hm
  simp only [minimumProfiles, hP0, hQ0, if_pos rfl,
    if_neg hP1.ne', if_neg hP2.ne', if_neg hQ1.ne', if_neg hQ2.ne',
    ← Multiset.cons_coe, Multiset.coe_nil] at hm
  rcases rel_two_reading hm with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hs := singleton_motion _ _ h0
    have ht := triple_motion _ _ h1
    simp [Profile.slice] at hs ht
    rcases ht with ⟨h1, h2, h3, hg1, hg2⟩ | ⟨h1, h2, h3, hg1, hg2⟩
    · apply Profile.ext
      · funext i; fin_cases i <;> simp <;> omega
      · funext i; fin_cases i <;> simp <;> omega
    · have hQr : Q.r = ![P.r 0, P.r 3, P.r 2, P.r 1] :=
        tuple_four_eq _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      have hQg : Q.g = ![c, P.g 2, P.g 1] :=
        tuple_three_eq _ _ _ _ hQ0 (by omega) (by omega)
      have hh := he
      rw [P.schur_four_complete hP, Q.schur_four_complete hQ] at hh
      simp only [hP0, hQr, hQg, Matrix.cons_val] at hh
      have hd := P.four_domain hP
      simp only [FourDomain, hP0] at hd
      have hp := one_end_minimum_rigidity (P.r 0) (P.r 1) (P.r 2) (P.r 3) c
        (P.g 1) (P.g 2) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hh
      apply Profile.ext
      · funext i; fin_cases i <;> simp [hQr] <;> omega
      · funext i; fin_cases i <;> simp [hQg] <;> omega
  · obtain ⟨ho, _⟩ := h0
    norm_num at ho

private theorem end_to_middle_impossible (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) (c : ℕ)
    (hP0 : P.g 0 = c) (hP1 : c < P.g 1) (hP2 : c < P.g 2)
    (hQ0 : c < Q.g 0) (hQ1 : Q.g 1 = c) (hQ2 : c < Q.g 2) : False := by
  have hm := hessenberg_minimum_block_motions P Q hP hQ he
  have hmin : min (P.g 0) (min (P.g 1) (P.g 2)) = c := by omega
  dsimp only at hm
  rw [hmin] at hm
  simp only [minimumProfiles, hP0, hQ1, if_pos rfl,
    if_neg hP1.ne', if_neg hP2.ne', if_neg hQ0.ne', if_neg hQ2.ne',
    ← Multiset.cons_coe, Multiset.coe_nil] at hm
  rcases rel_two_reading hm with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    obtain ⟨ho, _⟩ := h0 <;> norm_num at ho

/-- The end-minimum case is rotation-rigid against every actual Hessenberg mate. -/
theorem one_end_minimum_profile_rigidity (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) (c : ℕ)
    (hP0 : P.g 0 = c) (hP1 : c < P.g 1) (hP2 : c < P.g 2) :
    P = Q ∨ P = Q.rotate := by
  have hg := hessenberg_gap_reading P Q hP hQ he
  simp only [tripleMatch, hP0] at hg
  have hcases :
      (Q.g 0 = c ∧ c < Q.g 1 ∧ c < Q.g 2) ∨
      (Q.g 1 = c ∧ c < Q.g 0 ∧ c < Q.g 2) ∨
      (Q.g 2 = c ∧ c < Q.g 0 ∧ c < Q.g 1) := by omega
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h1, h0, h2⟩ | ⟨h2, h0, h1⟩
  · exact Or.inl (end_to_end_literal P Q hP hQ he c hP0 hP1 hP2 h0 h1 h2)
  · exact False.elim (end_to_middle_impossible P Q hP hQ he c hP0 hP1 hP2 h0 h1 h2)
  · right
    have he' : P.schur = Q.rotate.schur := by rwa [Profile.schur_rotate]
    apply end_to_end_literal P Q.rotate hP (Q.hessenberg_rotate hQ) he' c hP0 hP1 hP2
    · simpa [Profile.rotate] using h2
    · simpa [Profile.rotate] using h1
    · simpa [Profile.rotate] using h0

private theorem middle_ordered_rigidity (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) (c : ℕ)
    (hP0 : c < P.g 0) (hP1 : P.g 1 = c) (hP2 : c < P.g 2)
    (hQg : Q.g = ![P.g 0, c, P.g 2]) (hrows : rowsL P Q) :
    P = Q ∨ P = Q.rotate := by
  have hdom := P.four_domain hP
  have hflip := Q.four_domain hQ
  have hh := he
  rw [P.schur_four_complete hP, Q.schur_four_complete hQ] at hh
  simp only [hP1] at hdom
  unfold rowsL at hrows
  rcases hrows with hrows | hrows | hrows | hrows
  · left
    apply Profile.ext
    · rw [hrows]; exact tuple_four_eq P.r _ _ _ _ rfl rfl rfl rfl
    · funext i; fin_cases i <;> simp [hQg] <;> omega
  · simp only [hP1, hQg, hrows, Matrix.cons_val] at hflip hh
    have hm := one_middle_minimum_left_flip (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (P.g 0) c (P.g 2) hdom (by omega) (by omega) (by omega) hh
    left
    apply Profile.ext
    · funext i; fin_cases i <;> simp [hrows] <;> omega
    · funext i; fin_cases i <;> simp [hQg] <;> omega
  · have he' : P.rotate.schur = Q.rotate.schur := by
      simpa only [Profile.schur_rotate] using he
    have hdom' := P.rotate.four_domain (P.hessenberg_rotate hP)
    rw [P.rotate.schur_four_complete (P.hessenberg_rotate hP),
      Q.rotate.schur_four_complete (Q.hessenberg_rotate hQ)] at he'
    simp [Profile.rotate, hP1, hQg, hrows] at hdom' he'
    have hm := one_middle_minimum_left_flip (P.r 3) (P.r 2) (P.r 1) (P.r 0)
      (P.g 2) c (P.g 0) hdom' (by omega) (by omega) (by omega) he'
    left
    apply Profile.ext
    · funext i; fin_cases i <;> simp [hrows] <;> omega
    · funext i; fin_cases i <;> simp [hQg] <;> omega
  · simp only [hP1, hQg, hrows, Matrix.cons_val] at hflip hh
    have hm := one_middle_minimum_both_flip (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (P.g 0) c (P.g 2) hdom hflip (by omega) (by omega) (by omega) hh
    rcases hm with ⟨h0, h1⟩ | ⟨hg, h0, h1⟩
    · left
      apply Profile.ext
      · funext i; fin_cases i <;> simp [hrows] <;> omega
      · funext i; fin_cases i <;> simp [hQg] <;> omega
    · right
      apply Profile.ext
      · funext i; fin_cases i <;> simp [Profile.rotate, hrows] <;> omega
      · funext i; fin_cases i <;> simp [Profile.rotate, hQg] <;> omega

private theorem middle_to_middle_rigidity (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) (c : ℕ)
    (hP0 : c < P.g 0) (hP1 : P.g 1 = c) (hP2 : c < P.g 2)
    (hQ0 : c < Q.g 0) (hQ1 : Q.g 1 = c) (hQ2 : c < Q.g 2) :
    P = Q ∨ P = Q.rotate := by
  have hm := hessenberg_minimum_block_motions P Q hP hQ he
  have hmin : min (P.g 0) (min (P.g 1) (P.g 2)) = c := by omega
  dsimp only at hm
  rw [hmin] at hm
  simp only [minimumProfiles, hP1, hQ1, if_pos rfl,
    if_neg hP0.ne', if_neg hP2.ne', if_neg hQ0.ne', if_neg hQ2.ne',
    ← Multiset.cons_coe, Multiset.coe_nil] at hm
  rcases rel_two_reading hm with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hp0 := pair_motion _ _ h0
    have hp1 := pair_motion _ _ h1
    simp [Profile.slice] at hp0 hp1
    have hg : Q.g = ![P.g 0, c, P.g 2] :=
      tuple_three_eq _ _ _ _ hp0.2.symm hQ1 hp1.2.symm
    exact middle_ordered_rigidity P Q hP hQ he c hP0 hP1 hP2 hg
      (rowsL_of_fields P Q hp0.1 hp1.1)
  · have hp0 := pair_motion _ _ h0
    have hp1 := pair_motion _ _ h1
    simp [Profile.slice] at hp0 hp1
    have he' : P.schur = Q.rotate.schur := by rwa [Profile.schur_rotate]
    have hg : Q.rotate.g = ![P.g 0, c, P.g 2] := by
      funext i
      fin_cases i <;> simp [Profile.rotate] <;> omega
    have hr0 :
        (P.r 0 = Q.rotate.r 0 ∧ P.r 1 = Q.rotate.r 1) ∨
        (P.r 0 = Q.rotate.r 1 ∧ P.r 1 = Q.rotate.r 0) := by
      rcases hp0.1 with h | h
      · right; simpa [Profile.rotate] using h
      · left; simpa [Profile.rotate] using h
    have hr1 :
        (P.r 2 = Q.rotate.r 2 ∧ P.r 3 = Q.rotate.r 3) ∨
        (P.r 2 = Q.rotate.r 3 ∧ P.r 3 = Q.rotate.r 2) := by
      rcases hp1.1 with h | h
      · right; simpa [Profile.rotate] using h
      · left; simpa [Profile.rotate] using h
    have hh := middle_ordered_rigidity P Q.rotate hP (Q.hessenberg_rotate hQ) he'
      c hP0 hP1 hP2 hg (rowsL_of_fields P Q.rotate hr0 hr1)
    rcases hh with hh | hh
    · exact Or.inr hh
    · exact Or.inl (by simpa using hh)

-- Both orders of the recovered two-row blocks require dependent profile transports.
set_option maxHeartbeats 1000000 in
/-- An interior minimum gives no nonrotation mate, including coincident block lengths and gaps. -/
theorem one_middle_minimum_profile_rigidity (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) (c : ℕ)
    (hP0 : c < P.g 0) (hP1 : P.g 1 = c) (hP2 : c < P.g 2) :
    P = Q ∨ P = Q.rotate := by
  have hg := hessenberg_gap_reading P Q hP hQ he
  simp only [tripleMatch, hP1] at hg
  have hcases :
      (Q.g 0 = c ∧ c < Q.g 1 ∧ c < Q.g 2) ∨
      (Q.g 1 = c ∧ c < Q.g 0 ∧ c < Q.g 2) ∨
      (Q.g 2 = c ∧ c < Q.g 0 ∧ c < Q.g 1) := by omega
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h1, h0, h2⟩ | ⟨h2, h0, h1⟩
  · exact False.elim (end_to_middle_impossible Q P hQ hP he.symm c h0 h1 h2 hP0 hP1 hP2)
  · exact middle_to_middle_rigidity P Q hP hQ he c hP0 hP1 hP2 h0 h1 h2
  · have he' : Q.rotate.schur = P.schur := Q.schur_rotate.trans he.symm
    have hQ0' : Q.rotate.g 0 = c := by simpa [Profile.rotate] using h2
    have hQ1' : c < Q.rotate.g 1 := by simpa [Profile.rotate] using h1
    have hQ2' : c < Q.rotate.g 2 := by simpa [Profile.rotate] using h0
    exact False.elim (end_to_middle_impossible Q.rotate P (Q.hessenberg_rotate hQ) hP
      he' c hQ0' hQ1' hQ2' hP0 hP1 hP2)

/-- Necessity: every actual four-row Hessenberg mate is a rotation or belongs to F/H. -/
theorem hessenberg_classification (P Q : Profile 3)
    (hP : P.Hessenberg) (hQ : Q.Hessenberg) (he : P.schur = Q.schur) :
    Classified P Q := by
  let c := min (P.g 0) (min (P.g 1) (P.g 2))
  rcases minimum_patterns (P.g 0) (P.g 1) (P.g 2) c rfl with
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h2, h1⟩ |
    ⟨h1, h2, h0⟩ | ⟨h0, h1, h2⟩ | ⟨h1, h0, h2⟩ | ⟨h2, h0, h1⟩
  · rcases three_minimum_profile_rigidity P Q hP hQ he c h0 h1 h2 with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
  · exact two_minimum_L_classification P Q hP hQ he c (P.g 2) h2 h0 h1 rfl
  · exact two_minimum_M_classification P Q hP hQ he c (P.g 1) h1 h0 rfl h2
  · apply classified_rotate_left
    have he' : P.rotate.schur = Q.schur := by rwa [Profile.schur_rotate]
    apply two_minimum_L_classification P.rotate Q (P.hessenberg_rotate hP) hQ he'
      c (P.g 0) h0
    · simpa [Profile.rotate] using h2
    · simpa [Profile.rotate] using h1
    · simp [Profile.rotate]
  · rcases one_end_minimum_profile_rigidity P Q hP hQ he c h0 h1 h2 with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
  · rcases one_middle_minimum_profile_rigidity P Q hP hQ he c h0 h1 h2 with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
  · apply classified_rotate_left
    have he' : P.rotate.schur = Q.schur := by rwa [Profile.schur_rotate]
    have h0' : P.rotate.g 0 = c := by simpa [Profile.rotate] using h2
    have h1' : c < P.rotate.g 1 := by simpa [Profile.rotate] using h1
    have h2' : c < P.rotate.g 2 := by simpa [Profile.rotate] using h0
    rcases one_end_minimum_profile_rigidity P.rotate Q (P.hessenberg_rotate hP) hQ
      he' c h0' h1' h2' with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)

/-- Sufficiency: every listed alternative gives equality of the actual full polynomials. -/
theorem classified_schur_eq {P Q : Profile 3} (h : Classified P Q) : P.schur = Q.schur := by
  rcases h with h | h | ⟨w, b, c, hcw, hb, hh⟩
  · rw [h]
  · rw [h, Profile.schur_rotate]
  · rcases hh with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · have hbase := family_schur_eq w b c hcw hb
      rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
      all_goals simpa only [Profile.schur_rotate] using hbase
    · have hbase := (family_schur_eq w b c hcw hb).symm
      rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
      all_goals simpa only [Profile.schur_rotate] using hbase

/-- Complete symbolic classification in the legitimate Hessenberg domain, with no tie exclusions. -/
theorem hessenberg_schur_eq_iff (P Q : Profile 3) (hP : P.Hessenberg) (hQ : Q.Hessenberg) :
    P.schur = Q.schur ↔ Classified P Q :=
  ⟨hessenberg_classification P Q hP hQ, classified_schur_eq⟩

end FourRowHessenberg
end SkewJacobiNegative
