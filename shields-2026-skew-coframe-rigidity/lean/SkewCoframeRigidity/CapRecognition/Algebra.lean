/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.CapRecognition.Basic

/-!
# Variable-freeness in the joint ring

A polynomial is *free of a label* `k` when none of the variables `h_k` occurs in it.  Freeness is
closed under sums, products and determinants, passes to divisors of a nonzero polynomial, and a
polynomial linear in a variable `x` with coprime coefficients is irreducible.  Sorry-free.
-/

namespace SkewCoframeRigidity.CapRecognition

open SkewCofactorIndependence MvPolynomial

/-- No variable `h_j` with `j = k` occurs in `f`. -/
def NoLabel (f : J) (k : ℤ) : Prop := ∀ j : ℕ+, (j : ℤ) = k → some j ∉ f.vars

/-- The positive integer `k > 0` as an index. -/
def pn (k : ℤ) (hk : 0 < k) : ℕ+ := ⟨k.toNat, by omega⟩

theorem pn_coe (k : ℤ) (hk : 0 < k) : ((pn k hk : ℕ+) : ℤ) = k := by
  simp only [pn, PNat.mk_coe]; omega

/-- The variable carrying the label `k > 0`. -/
def lvar (k : ℤ) (hk : 0 < k) : Option ℕ+ := some (pn k hk)

theorem NoLabel.notMem {f : J} {k : ℤ} (h : NoLabel f k) (hk : 0 < k) : lvar k hk ∉ f.vars :=
  h _ (pn_coe k hk)

theorem noLabel_of_notMem {f : J} {k : ℤ} (hk : 0 < k) (h : lvar k hk ∉ f.vars) : NoLabel f k := by
  intro j hj
  have : j = pn k hk := PNat.coe_injective (by
    apply Int.ofNat.inj
    simpa [pn_coe] using hj)
  subst this
  exact h

theorem hJ_eq_X {k : ℤ} (hk : 0 < k) : hJ k = X (lvar k hk) := by
  unfold hJ ι
  rw [complete_of_pos hk]
  exact rename_X _ _

theorem NoLabel.zero {k : ℤ} : NoLabel (0 : J) k := by intro j _; simp
theorem NoLabel.one {k : ℤ} : NoLabel (1 : J) k := by intro j _; simp

theorem NoLabel.add {f g : J} {k : ℤ} (hf : NoLabel f k) (hg : NoLabel g k) :
    NoLabel (f + g) k := fun j hj hm => by
  rcases Finset.mem_union.mp (vars_add_subset _ _ hm) with h | h
  exacts [hf j hj h, hg j hj h]

theorem NoLabel.mul {f g : J} {k : ℤ} (hf : NoLabel f k) (hg : NoLabel g k) :
    NoLabel (f * g) k := fun j hj hm => by
  rcases Finset.mem_union.mp (vars_mul _ _ hm) with h | h
  exacts [hf j hj h, hg j hj h]

theorem NoLabel.neg {f : J} {k : ℤ} (hf : NoLabel f k) : NoLabel (-f) k := fun j hj hm => by
  rw [vars_neg] at hm
  exact hf j hj hm

theorem NoLabel.sub {f g : J} {k : ℤ} (hf : NoLabel f k) (hg : NoLabel g k) :
    NoLabel (f - g) k := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem NoLabel.pow {f : J} {k : ℤ} (hf : NoLabel f k) (n : ℕ) : NoLabel (f ^ n) k := by
  induction n with
  | zero => simpa using NoLabel.one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem NoLabel.sum {ι' : Type*} {s : Finset ι'} {f : ι' → J} {k : ℤ}
    (h : ∀ i ∈ s, NoLabel (f i) k) : NoLabel (∑ i ∈ s, f i) k :=
  Finset.sum_induction f (fun x => NoLabel x k) (fun _ _ => NoLabel.add) NoLabel.zero h

theorem NoLabel.prod {ι' : Type*} {s : Finset ι'} {f : ι' → J} {k : ℤ}
    (h : ∀ i ∈ s, NoLabel (f i) k) : NoLabel (∏ i ∈ s, f i) k :=
  Finset.prod_induction f (fun x => NoLabel x k) (fun _ _ => NoLabel.mul) NoLabel.one h

theorem NoLabel.det {n : ℕ} {M : Matrix (Fin n) (Fin n) J} {k : ℤ}
    (h : ∀ i j, NoLabel (M i j) k) : NoLabel M.det k := by
  rw [Matrix.det_apply]
  apply NoLabel.sum
  intro σ _
  have hp : NoLabel (∏ i, M (σ i) i) k := NoLabel.prod fun i _ => h _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using hp.neg

theorem noLabel_hJ {k' k : ℤ} (h : k' ≠ k) : NoLabel (hJ k') k := by
  intro j hj hm
  unfold hJ ι at hm
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hm
  obtain ⟨j', hj', hjj⟩ := mem_vars_rename _ _ hm
  cases hjj
  rw [mem_vars_complete_iff] at hj'
  have hm := hj'
  exact h (hm.symm.trans hj)

theorem noLabel_zpow (e : ℕ) {k : ℤ} : NoLabel (zJ ^ e) k := by
  intro j _ hm
  have := vars_pow (zJ) e hm
  simp [zJ] at this

theorem noLabel_ι_of_lt {k' k : ℤ} (h : k' < k) : NoLabel (hJ k') k :=
  noLabel_hJ h.ne

/-- A divisor of a polynomial free of a variable is free of it. -/
theorem notMem_vars_of_dvd {σ : Type*} {i : σ} {f g : MvPolynomial σ ℚ} (hf : f ≠ 0)
    (hg : g ∣ f) (h : i ∉ f.vars) : i ∉ g.vars := by
  obtain ⟨h', rfl⟩ := hg
  have hg0 : g ≠ 0 := left_ne_zero_of_mul hf
  have hh0 : h' ≠ 0 := right_ne_zero_of_mul hf
  rw [mem_vars_iff_degreeOf_ne_zero] at h ⊢
  have := degreeOf_mul_eq (n := i) hg0 hh0
  omega

theorem NoLabel.of_dvd {f g : J} {k : ℤ} (hf : f ≠ 0) (hg : g ∣ f) (h : NoLabel f k) :
    NoLabel g k := fun j hj => notMem_vars_of_dvd hf hg (h j hj)

theorem pderiv_mul_of_notMem {i : Option ℕ+} {a b : J} (hb : i ∉ b.vars) :
    pderiv i (a * b) = pderiv i a * b := by
  rw [pderiv_mul, pderiv_eq_zero_of_notMem_vars hb]
  simp [mul_comm]

theorem pderiv_mul_of_notMem_left {i : Option ℕ+} {a b : J} (ha : i ∉ a.vars) :
    pderiv i (a * b) = a * pderiv i b := by
  rw [pderiv_mul, pderiv_eq_zero_of_notMem_vars ha]
  simp

/-- A polynomial linear in `x_i` with coprime coefficients is irreducible. -/
theorem irreducible_linear {i : Option ℕ+} {p0 d : J} (h0 : i ∉ p0.vars) (hd : i ∉ d.vars)
    (hd0 : d ≠ 0) (hcop : IsRelPrime d p0) : Irreducible (p0 + X i * d) := by
  set p : J := p0 + X i * d with hp
  have hder : pderiv i p = d := by
    rw [hp, map_add, pderiv_eq_zero_of_notMem_vars h0, pderiv_mul, pderiv_eq_zero_of_notMem_vars hd]
    simp
  have hp0 : p ≠ 0 := fun h => hd0 (by rw [← hder, h, map_zero])
  have hip : i ∈ p.vars := by
    by_contra h
    exact hd0 (by rw [← hder, pderiv_eq_zero_of_notMem_vars h])
  have hdeg1 : degreeOf i p = 1 := by
    have hle : degreeOf i p ≤ 1 := by
      refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · have : degreeOf i p0 = 0 := by
          by_contra hne
          exact h0 (mem_vars_iff_degreeOf_ne_zero.mpr hne)
        omega
      · refine (degreeOf_mul_le _ _ _).trans ?_
        have : degreeOf i d = 0 := by
          by_contra hne
          exact hd (mem_vars_iff_degreeOf_ne_zero.mpr hne)
        rw [this, degreeOf_X]
        simp
    have : degreeOf i p ≠ 0 := mem_vars_iff_degreeOf_ne_zero.mp hip
    omega
  have key : ∀ a b : J, p = a * b → i ∉ b.vars → IsUnit b := by
    intro a b hab hb
    have h1 : b ∣ d := ⟨pderiv i a, by rw [← hder, hab, pderiv_mul_of_notMem hb]; ring⟩
    have h2 : b ∣ p0 := by
      have : p0 = p - X i * d := by rw [hp]; ring
      rw [this]
      exact dvd_sub ⟨a, by rw [hab]; ring⟩ (dvd_mul_of_dvd_right h1 _)
    exact hcop h1 h2
  refine ⟨?_, fun a b hab => ?_⟩
  · intro hu
    obtain ⟨c, -, hc⟩ := (isUnit_iff_eq_C_of_isReduced.mp hu)
    apply hd0
    rw [← hder, hc]
    exact pderiv_C
  · have ha0 : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hp0)
    have hb0 : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hp0)
    have := degreeOf_mul_eq (n := i) ha0 hb0
    rw [← hab, hdeg1] at this
    by_cases hb : degreeOf i b = 0
    · right
      exact key a b hab (fun h => (mem_vars_iff_degreeOf_ne_zero.mp h) hb)
    · left
      have ha : degreeOf i a = 0 := by omega
      exact key b a (hab.trans (mul_comm a b)) (fun h => (mem_vars_iff_degreeOf_ne_zero.mp h) ha)

end SkewCoframeRigidity.CapRecognition
