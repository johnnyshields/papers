/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Nonlinear

/-!
# Fixed-inner composition preserves the first ordinary degree

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:recovery`
(`prop:depth-cancel`, `eq:leading-substitution`).

`ordGE k f` says that every monomial of `f` has ordinary degree at least `k`.  Over any
commutative coefficient ring `R` the substitution `Ψ_ε` (`PsiR`) sends each generator `h_j` to
`h_{pj}` plus terms of ordinary degree at least two, so it agrees with the relabeling
`h_j ↦ h_{pj}` (`rescale`) to order one beyond the first ordinary degree of the argument
(`ordGE_alg_sub`).  Over `ℤ` the content (gcd of all coefficients) is preserved as well.
Sorry-free.
-/

namespace SkewRibbonCoarsenings

open MvPolynomial

section Order

variable {R : Type*} [CommRing R]

/-- Every monomial of `f` has ordinary degree at least `k` (each `h_j` has degree `1`). -/
def ordGE (k : ℕ) (f : MvPolynomial ℕ+ R) : Prop :=
  ∀ d : ℕ+ →₀ ℕ, d.degree < k → f.coeff d = 0

lemma ordGE_zero_index (f : MvPolynomial ℕ+ R) : ordGE 0 f :=
  fun _ hd => absurd hd (Nat.not_lt_zero _)

lemma ordGE_mono {k k' : ℕ} (h : k' ≤ k) {f : MvPolynomial ℕ+ R} (hf : ordGE k f) :
    ordGE k' f :=
  fun d hd => hf d (lt_of_lt_of_le hd h)

lemma ordGE_zero (k : ℕ) : ordGE k (0 : MvPolynomial ℕ+ R) := fun d _ => by simp

lemma ordGE_add {k : ℕ} {f g : MvPolynomial ℕ+ R} (hf : ordGE k f) (hg : ordGE k g) :
    ordGE k (f + g) := fun d hd => by simp [hf d hd, hg d hd]

lemma ordGE_sub {k : ℕ} {f g : MvPolynomial ℕ+ R} (hf : ordGE k f) (hg : ordGE k g) :
    ordGE k (f - g) := fun d hd => by rw [coeff_sub, hf d hd, hg d hd, sub_zero]

lemma ordGE_C_mul {k : ℕ} (c : R) {f : MvPolynomial ℕ+ R} (hf : ordGE k f) :
    ordGE k (C c * f) := fun d hd => by rw [coeff_C_mul, hf d hd, mul_zero]

lemma ordGE_sum {ι : Type*} {k : ℕ} (s : Finset ι) (f : ι → MvPolynomial ℕ+ R)
    (h : ∀ i ∈ s, ordGE k (f i)) : ordGE k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (ordGE k) (fun _ _ => ordGE_add) (ordGE_zero k) h

lemma ordGE_mul {k₁ k₂ : ℕ} {f g : MvPolynomial ℕ+ R} (hf : ordGE k₁ f) (hg : ordGE k₂ g) :
    ordGE (k₁ + k₂) (f * g) := by
  intro d hd
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : x.1.degree + x.2.degree = d.degree := by
    rw [← map_add, hx']
  by_cases h1 : x.1.degree < k₁
  · rw [hf _ h1, zero_mul]
  · have h2 : x.2.degree < k₂ := by omega
    rw [hg _ h2, mul_zero]

lemma ordGE_X (j : ℕ+) : ordGE 1 (X j : MvPolynomial ℕ+ R) := by
  intro d hd
  have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
  subst hd0
  exact coeff_zero_X j

lemma ordGE_prod {ι : Type*} (s : Finset ι) (n : ι → ℕ) (a : ι → MvPolynomial ℕ+ R)
    (h : ∀ i ∈ s, ordGE (n i) (a i)) : ordGE (∑ i ∈ s, n i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact ordGE_zero_index _
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact ordGE_mul (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma ordGE_multiset_prod (m : Multiset (MvPolynomial ℕ+ R)) (h : ∀ x ∈ m, ordGE 1 x) :
    ordGE (Multiset.card m) m.prod := by
  induction m using Multiset.induction with
  | empty => simpa using ordGE_zero_index (1 : MvPolynomial ℕ+ R)
  | cons a m ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, add_comm]
    exact ordGE_mul (h a (Multiset.mem_cons_self _ _))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

/-- Difference of products: if each factor pair agrees to one order beyond its own order, the
products agree to one order beyond the total. -/
lemma ordGE_prod_sub {ι : Type*} (s : Finset ι) (n : ι → ℕ) (a b : ι → MvPolynomial ℕ+ R)
    (ha : ∀ i ∈ s, ordGE (n i) (a i)) (hb : ∀ i ∈ s, ordGE (n i) (b i))
    (hab : ∀ i ∈ s, ordGE (n i + 1) (a i - b i)) :
    ordGE (∑ i ∈ s, n i + 1) (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty, Finset.prod_empty, sub_self]
    exact ordGE_zero _
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    have hmem : i ∈ insert i s := Finset.mem_insert_self _ _
    have hsub : ∀ j ∈ s, j ∈ insert i s := fun j hj => Finset.mem_insert_of_mem hj
    have e : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j
        = a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) + (a i - b i) * ∏ j ∈ s, b j := by ring
    rw [e]
    have h1 := ordGE_mul (ha i hmem)
      (ih (fun j hj => ha j (hsub j hj)) (fun j hj => hb j (hsub j hj))
        (fun j hj => hab j (hsub j hj)))
    have h2 := ordGE_mul (hab i hmem) (ordGE_prod s n b fun j hj => hb j (hsub j hj))
    exact ordGE_add (ordGE_mono (by omega) h1) (ordGE_mono (by omega) h2)

lemma ordGE_pow {k e : ℕ} {a : MvPolynomial ℕ+ R} (ha : ordGE k a) : ordGE (e * k) (a ^ e) := by
  induction e with
  | zero => simpa using ordGE_zero_index (1 : MvPolynomial ℕ+ R)
  | succ e ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ordGE_mul ih ha

lemma ordGE_pow_sub {a b : MvPolynomial ℕ+ R} (ha : ordGE 1 a) (hb : ordGE 1 b)
    (hab : ordGE 2 (a - b)) (e : ℕ) : ordGE (e + 1) (a ^ e - b ^ e) := by
  induction e with
  | zero => simpa using ordGE_zero (R := R) 1
  | succ e ih =>
    have eq : a ^ (e + 1) - b ^ (e + 1) = a ^ e * (a - b) + (a ^ e - b ^ e) * b := by ring
    rw [eq]
    have h1 := ordGE_mul (ordGE_pow (e := e) ha) hab
    have h2 := ordGE_mul ih hb
    exact ordGE_add (ordGE_mono (by omega) h1) (ordGE_mono (by omega) h2)

lemma alg_monomial (φ : MvPolynomial ℕ+ R →ₐ[R] MvPolynomial ℕ+ R) (d : ℕ+ →₀ ℕ) (c : R) :
    φ (monomial d c) = C c * ∏ j ∈ d.support, φ (X j) ^ d j := by
  rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod]
  simp [map_pow]

/-- Two algebra endomorphisms of `R[h₁, h₂, …]` whose generator images have order at least one
and agree to order two agree to order `r + 1` on every polynomial of order at least `r`. -/
theorem ordGE_alg_sub (φ ψ : MvPolynomial ℕ+ R →ₐ[R] MvPolynomial ℕ+ R)
    (h1 : ∀ j, ordGE 1 (φ (X j))) (h1' : ∀ j, ordGE 1 (ψ (X j)))
    (h2 : ∀ j, ordGE 2 (φ (X j) - ψ (X j))) (F : MvPolynomial ℕ+ R) (r : ℕ)
    (hF : ordGE r F) : ordGE (r + 1) (φ F - ψ F) := by
  classical
  have hF' : φ F - ψ F
      = ∑ d ∈ F.support, (φ (monomial d (F.coeff d)) - ψ (monomial d (F.coeff d))) := by
    conv_lhs => rw [F.as_sum]
    rw [map_sum, map_sum, Finset.sum_sub_distrib]
  rw [hF']
  refine ordGE_sum _ _ fun d hd => ?_
  have hrd : r ≤ d.degree := by
    by_contra hlt
    exact (mem_support_iff.mp hd) (hF d (not_le.mp hlt))
  rw [alg_monomial, alg_monomial, ← mul_sub]
  refine ordGE_C_mul _ (ordGE_mono (by omega : r + 1 ≤ d.degree + 1) ?_)
  have := ordGE_prod_sub d.support (fun j => d j)
    (fun j => φ (X j) ^ d j) (fun j => ψ (X j) ^ d j)
    (fun j _ => by simpa using ordGE_pow (e := d j) (h1 j))
    (fun j _ => by simpa using ordGE_pow (e := d j) (h1' j))
    (fun j _ => ordGE_pow_sub (h1 j) (h1' j) (h2 j) (d j))
  rwa [← Finsupp.degree_apply] at this

lemma ordGE_map {S : Type*} [CommRing S] (f : R →+* S) {k : ℕ} {F : MvPolynomial ℕ+ R}
    (hF : ordGE k F) : ordGE k (MvPolynomial.map f F) := fun d hd => by
  rw [coeff_map, hF d hd, map_zero]

lemma ordGE_iff_hc {k : ℕ} {F : MvPolynomial ℕ+ R} :
    ordGE k F ↔ ∀ s < k, homogeneousComponent s F = 0 := by
  constructor
  · intro h s hs
    ext d
    rw [coeff_homogeneousComponent]
    split_ifs with hd
    · exact h d (hd ▸ hs)
    · simp
  · intro h d hd
    have := congrArg (fun F : MvPolynomial ℕ+ R => F.coeff d) (h d.degree hd)
    rw [coeff_homogeneousComponent] at this
    simpa using this

theorem homogeneousComponent_eq_of_ordGE {f g : MvPolynomial ℕ+ R} {r : ℕ}
    (h : ordGE (r + 1) (f - g)) :
    homogeneousComponent r f = homogeneousComponent r g := by
  ext d
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
  split_ifs with hd
  · have := h d (by omega)
    rw [coeff_sub, sub_eq_zero] at this
    exact this
  · rfl

theorem eq_zero_of_ordGE_all {F : MvPolynomial ℕ+ R} (hF : ∀ k, ordGE k F) : F = 0 := by
  ext d
  change F.coeff d = 0
  exact hF (d.degree + 1) d (Nat.lt_succ_self _)

end Order

section Substitution

variable {R : Type*} [CommRing R]

/-- The relabeling of generators `j ↦ p j`. -/
def pnatMul (p : ℕ) (j : ℕ+) : ℕ+ := Nat.toPNat' (p * (j : ℕ))

lemma pnatMul_val {p : ℕ} (hp : 0 < p) (j : ℕ+) : ((pnatMul p j : ℕ+) : ℕ) = p * (j : ℕ) := by
  unfold pnatMul
  rw [PNat.toPNat'_coe (Nat.mul_pos hp j.pos)]

lemma pnatMul_injective {p : ℕ} (hp : 0 < p) : Function.Injective (pnatMul p) := by
  intro i j h
  have := congrArg (fun x : ℕ+ => (x : ℕ)) h
  simp only [pnatMul_val hp] at this
  exact PNat.eq (Nat.eq_of_mul_eq_mul_left hp this)

/-- The relabeling substitution `F ↦ F(h_j ↦ h_{pj})` of the right-hand side of
`eq:leading-substitution`, as an algebra endomorphism of `R[h₁, h₂, …]`. -/
noncomputable def rescale (R : Type*) [CommRing R] (p : ℕ) :
    MvPolynomial ℕ+ R →ₐ[R] MvPolynomial ℕ+ R :=
  MvPolynomial.rename (pnatMul p)

lemma rescale_X (p : ℕ) (j : ℕ+) : rescale R p (X j) = X (pnatMul p j) := by
  simp [rescale]

/-- Relabeling the independent variables is injective over any coefficient ring. -/
lemma rescale_injective {p : ℕ} (hp : 0 < p) : Function.Injective (rescale R p) :=
  MvPolynomial.rename_injective _ (pnatMul_injective hp)

lemma rescale_homogeneousComponent (p n : ℕ) (F : MvPolynomial ℕ+ R) :
    rescale R p (homogeneousComponent n F) = homogeneousComponent n (rescale R p F) :=
  rename_homogeneousComponent n F

lemma hgen_eq_X {n : ℕ} (hn : 0 < n) : hgen n = X (Nat.toPNat' n) := by
  rw [hgen, dite_eq_left_of_eq_true (eq_true hn)]
  congr 1
  apply PNat.eq
  rw [PNat.toPNat'_coe hn]
  rfl

private lemma card_gaps' {n : ℕ} {T : Finset ℕ} (hT : IsCutSet n T) :
    (gaps n T).card = T.card + 1 := by
  unfold gaps
  rw [Multiset.card_map]
  change (insert n T).card = _
  rw [Finset.card_insert_of_notMem]
  intro h
  have := Finset.mem_Ioo.mp (hT h)
  omega

lemma ordGE_hgen {x : ℕ} (hx : 0 < x) : ordGE 1 (hgen x) := by
  rw [hgen, dite_eq_left_of_eq_true (eq_true hx)]
  exact ordGE_X _

/-- A coarsening polynomial of positive weight is `h_n` plus terms of ordinary degree at least
two: the single retained-cut-free coarsening contributes `h_n`, every other one is a product of
at least two positive generators. -/
lemma ordGE_G_sub {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) :
    ordGE 2 (G n S - hgen n) := by
  unfold G
  have h0 : (∅ : Finset ℕ) ∈ S.powerset := Finset.empty_mem_powerset S
  rw [← Finset.add_sum_erase _ _ h0]
  simp only [gaps_empty, Multiset.map_singleton, Multiset.prod_singleton, add_sub_cancel_left]
  refine ordGE_sum _ _ fun T hT => ?_
  obtain ⟨hne, hTS⟩ := Finset.mem_erase.mp hT
  have hT' : IsCutSet n T := fun x hx => hS ((Finset.mem_powerset.mp hTS) hx)
  have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  have hpos := gaps_pos hn hT'
  have hcard : 2 ≤ Multiset.card ((gaps n T).map hgen) := by
    rw [Multiset.card_map, card_gaps' hT']
    have := Finset.card_pos.mpr hTne
    omega
  refine ordGE_mono hcard (ordGE_multiset_prod _ ?_)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  exact ordGE_hgen (hpos y hy)

lemma ordGE_G_one {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) :
    ordGE 1 (G n S) := by
  have h := ordGE_add (ordGE_mono (by omega) (ordGE_G_sub hn hS)) (ordGE_hgen hn)
  simpa using h

/-- The substitution `Ψ_ε` of `eq:introPsi` over an arbitrary commutative coefficient ring `R`:
the `R`-algebra endomorphism of `R[h₁, h₂, …]` with `h_j ↦ G_{ε^{⊙ j}}`, for the inner
composition of weight `p` with cut set `E`. -/
noncomputable def PsiR (R : Type*) [CommRing R] (p : ℕ) (E : Finset ℕ) :
    MvPolynomial ℕ+ R →ₐ[R] MvPolynomial ℕ+ R :=
  MvPolynomial.aeval fun j : ℕ+ =>
    MvPolynomial.map (Int.castRingHom R) (G ((j : ℕ) * p) (nearPowerCuts p E j))

lemma PsiR_X (p : ℕ) (E : Finset ℕ) (j : ℕ+) :
    PsiR R p E (X j)
      = MvPolynomial.map (Int.castRingHom R) (G ((j : ℕ) * p) (nearPowerCuts p E j)) := by
  simp [PsiR]

/-- Over `ℤ`, `PsiR` is the substitution `Ψ_ε` of `Defs`. -/
theorem PsiR_int (p : ℕ) (E : Finset ℕ) (F : Lam) : PsiR ℤ p E F = Psi p E F := by
  have h : ((PsiR ℤ p E : Lam →ₐ[ℤ] Lam) : Lam →+* Lam) = Psi p E := by
    apply ringHom_ext_Lam
    intro j
    rw [← hgen_pnat, Psi_hgen]
    simp only [hgen_pnat]
    rw [AlgHom.coe_toRingHom, PsiR_X, Int.castRingHom_int]
    exact MvPolynomial.map_id _
  exact RingHom.congr_fun h F

/-- Each generator image of `Ψ_ε` is `h_{pj}` plus terms of ordinary degree at least two. -/
lemma PsiR_X_sub {p : ℕ} {E : Finset ℕ} (hp : 0 < p) (hE : IsCutSet p E) (j : ℕ+) :
    ordGE 2 (PsiR R p E (X j) - rescale R p (X j)) := by
  have hn : 0 < (j : ℕ) * p := Nat.mul_pos j.pos hp
  have hS := nearPowerCuts_isCutSet hE (j : ℕ)
  have h := ordGE_map (Int.castRingHom R) (ordGE_G_sub hn hS)
  have e : PsiR R p E (X j) - rescale R p (X j)
      = MvPolynomial.map (Int.castRingHom R)
          (G ((j : ℕ) * p) (nearPowerCuts p E j) - hgen ((j : ℕ) * p)) := by
    rw [PsiR_X, rescale_X, map_sub, hgen_eq_X hn, map_X, pnatMul, mul_comm p]
  rwa [e]

lemma PsiR_X_one {p : ℕ} {E : Finset ℕ} (hp : 0 < p) (hE : IsCutSet p E) (j : ℕ+) :
    ordGE 1 (PsiR R p E (X j)) := by
  rw [PsiR_X]
  exact ordGE_map _ (ordGE_G_one (Nat.mul_pos j.pos hp) (nearPowerCuts_isCutSet hE (j : ℕ)))

/-- `Ψ_ε` and the relabeling agree to one order beyond the order of the argument. -/
lemma PsiR_sub_rescale {p : ℕ} {E : Finset ℕ} (hp : 0 < p) (hE : IsCutSet p E)
    {F : MvPolynomial ℕ+ R} {r : ℕ} (hF : ordGE r F) :
    ordGE (r + 1) (PsiR R p E F - rescale R p F) :=
  ordGE_alg_sub _ _ (PsiR_X_one hp hE)
    (fun j => by rw [rescale_X]; exact ordGE_X _) (PsiR_X_sub hp hE) F r hF

/-- `eq:leading-substitution`: if every homogeneous component of `F` below degree `r` vanishes,
so does every one of `Ψ_ε F`, and `(Ψ_ε F)^{[r]} = F^{[r]}(h_j ↦ h_{pj})`, over any commutative
coefficient ring `R`; `p` is the weight of the inner composition with cut set `E`. -/
theorem leading_substitution {p : ℕ} {E : Finset ℕ} (hp : 0 < p) (hE : IsCutSet p E)
    {F : MvPolynomial ℕ+ R} {r : ℕ} (hF : ∀ s < r, homogeneousComponent s F = 0) :
    (∀ s < r, homogeneousComponent s (PsiR R p E F) = 0) ∧
      homogeneousComponent r (PsiR R p E F) = rescale R p (homogeneousComponent r F) := by
  have hF' : ordGE r F := ordGE_iff_hc.mpr hF
  have hd := PsiR_sub_rescale hp hE hF'
  have hresc : ordGE r (rescale R p F) := by
    refine ordGE_iff_hc.mpr fun s hs => ?_
    rw [← rescale_homogeneousComponent, hF s hs, map_zero]
  refine ⟨ordGE_iff_hc.mp ?_, ?_⟩
  · have := ordGE_add (ordGE_mono (Nat.le_succ r) hd) hresc
    simpa using this
  · rw [homogeneousComponent_eq_of_ordGE hd, rescale_homogeneousComponent]

/-- `F` has first ordinary degree `r`: all components below degree `r` vanish and the component
of degree `r` does not. -/
def IsFirstDegree (F : MvPolynomial ℕ+ R) (r : ℕ) : Prop :=
  (∀ s < r, homogeneousComponent s F = 0) ∧ homogeneousComponent r F ≠ 0

/-- Every nonzero polynomial has a first ordinary degree. -/
theorem exists_isFirstDegree {F : MvPolynomial ℕ+ R} (hF : F ≠ 0) : ∃ r, IsFirstDegree F r := by
  classical
  have h : ∃ r, homogeneousComponent r F ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hF
    rw [← sum_homogeneousComponent F]
    exact Finset.sum_eq_zero fun i _ => hcon i
  refine ⟨Nat.find h, fun s hs => ?_, Nat.find_spec h⟩
  have := Nat.find_min h hs
  push Not at this
  exact this

end Substitution

section Content

/-- The content of a polynomial over `ℤ`: the gcd of all its coefficients. -/
noncomputable def content (F : Lam) : ℤ := Finset.gcd F.support F.coeff

lemma content_nonneg (F : Lam) : 0 ≤ content F :=
  Int.nonneg_of_normalize_eq_self Finset.normalize_gcd

lemma content_eq_zero_iff (F : Lam) : content F = 0 ↔ F = 0 := by
  rw [content, Finset.gcd_eq_zero_iff]
  constructor
  · intro h
    ext d
    change F.coeff d = 0
    by_cases hd : d ∈ F.support
    · exact h d hd
    · exact notMem_support_iff.mp hd
  · intro h x hx
    rw [h] at hx
    simp at hx

lemma dvd_content_iff (c : ℤ) (F : Lam) : c ∣ content F ↔ C c ∣ F := by
  rw [C_dvd_iff_dvd_coeff, content, Finset.dvd_gcd_iff]
  constructor
  · intro h i
    by_cases hi : i ∈ F.support
    · exact h i hi
    · rw [notMem_support_iff.mp hi]
      exact dvd_zero c
  · intro h i _
    exact h i

/-- A ring endomorphism of `Λ_ℤ` fixing the integer constants maps the content to a multiple of
it. -/
lemma content_dvd_content_map (φ : Lam →+* Lam) (hφ : ∀ c : ℤ, φ (C c) = C c) (F : Lam) :
    content F ∣ content (φ F) := by
  rw [dvd_content_iff]
  obtain ⟨H, hH⟩ := (dvd_content_iff _ F).mp dvd_rfl
  have := congrArg φ hH
  rw [map_mul, hφ] at this
  exact Dvd.intro _ this.symm

lemma Psi_C (p : ℕ) (E : Finset ℕ) (c : ℤ) : Psi p E (C c) = C c := by
  simp [Psi]

lemma proj_C (p : ℕ) (c : ℤ) : proj p (C c) = C c := by
  simp [proj]

/-- The substitution `Ψ_ε` preserves the gcd of all coefficients (`prop:depth-cancel`, last
assertion): integrality of `Ψ_ε` gives `content F ∣ content (Ψ_ε F)` and the integral left
inverse `π_p` gives the reverse divisibility. -/
theorem content_Psi {p : ℕ} {E : Finset ℕ} (hp : 0 < p) (hE : IsCutSet p E) (F : Lam) :
    content (Psi p E F) = content F := by
  have h1 : content F ∣ content (Psi p E F) :=
    content_dvd_content_map (Psi p E) (Psi_C p E) F
  have h2 : content (Psi p E F) ∣ content F := by
    have := content_dvd_content_map (proj p) (proj_C p) (Psi p E F)
    rwa [← RingHom.comp_apply, proj_Psi hp hE, RingHom.id_apply] at this
  exact Int.dvd_antisymm (content_nonneg _) (content_nonneg _) h2 h1

end Content

/-- `prop:depth-cancel`: for a nonzero polynomial `F` whose first ordinary degree is `r`, the
substitution `Ψ_ε` (inner composition of weight `p > 0` with cut set `E`) satisfies
`(Ψ_ε F)^{[r]} = F^{[r]}(h_j ↦ h_{pj})` (`eq:leading-substitution`), so that `Ψ_ε F` has the
same first ordinary degree `r`, over any commutative coefficient ring `R`. -/
theorem depth_cancel {R : Type*} [CommRing R] {p : ℕ} {E : Finset ℕ} (hp : 0 < p)
    (hE : IsCutSet p E) {F : MvPolynomial ℕ+ R} {r : ℕ} (hF : IsFirstDegree F r) :
    IsFirstDegree (PsiR R p E F) r ∧
      homogeneousComponent r (PsiR R p E F) = rescale R p (homogeneousComponent r F) := by
  obtain ⟨h1, h2⟩ := leading_substitution hp hE hF.1
  refine ⟨⟨h1, ?_⟩, h2⟩
  rw [h2]
  intro h
  exact hF.2 (rescale_injective hp (by rw [h, map_zero]))

/-- `prop:depth-cancel` over `ℤ`, in terms of the substitution `Ψ_ε` of `Defs`: the first
ordinary degree `r` of a nonzero `F` is preserved, `(Ψ_ε F)^{[r]} = F^{[r]}(h_j ↦ h_{pj})`
(`eq:leading-substitution`), and the gcd of all coefficients is preserved. -/
theorem depth_cancel_int {p : ℕ} {E : Finset ℕ} (hp : 0 < p) (hE : IsCutSet p E) {F : Lam}
    {r : ℕ} (hF : IsFirstDegree F r) :
    IsFirstDegree (Psi p E F) r ∧
      homogeneousComponent r (Psi p E F) = rescale ℤ p (homogeneousComponent r F) ∧
      content (Psi p E F) = content F := by
  have h := depth_cancel hp hE hF
  rw [PsiR_int] at h
  exact ⟨h.1, h.2, content_Psi hp hE F⟩

end SkewRibbonCoarsenings
