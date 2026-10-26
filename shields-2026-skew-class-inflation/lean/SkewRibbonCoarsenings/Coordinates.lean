/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/Coordinates.lean
import SkewRibbonCoarsenings.DepthCancel

/-!
# Composition coordinates

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:recovery`
(`prop:coordinates`, `eq:coordinates`).

`Theta p E` is the ring endomorphism `Θ_ε` of `Λ_ℤ`, `h_r ↦ G_{ε^{⊙(r/p)}}` if `p ∣ r` and
`h_r ↦ h_r` otherwise.  It is weight preserving, with an explicit recursive inverse
(unitriangularity of `G_{ε^{⊙ j}} = h_{pj} + R_j(h_1, …, h_{pj-1})`), so the generators
`G_{ε^{⊙ j}}`, `h_r` (`p ∤ r`) are algebraically independent and generate `Λ_ℤ`.  Also the
block lengths of a coarsening sum to the weight, so `G_β` is weighted homogeneous of weight `n`
for `wt h_j = j`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset MvPolynomial

/-- Removing the last cut `x` of a coarsening removes the last block `n - x`. -/
lemma gaps_insert_max {n x : ℕ} {T : Finset ℕ} (hx : x < n) (hT : ∀ z ∈ T, z < x) :
    gaps n (insert x T) = (n - x) ::ₘ gaps x T := by
  have hxT : x ∉ T := fun h => lt_irrefl _ (hT x h)
  have hsupT : T.sup id ≤ x := Finset.sup_le fun z hz => (hT z hz).le
  have hnT : n ∉ insert x T := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · omega
    · have := hT n h; omega
  unfold gaps
  have h1 : ((insert x T).filter (· < n)).sup id = x := by
    rw [Finset.filter_true_of_mem (fun z hz => by
      rcases Finset.mem_insert.1 hz with h | h
      · omega
      · have := hT z h; omega)]
    rw [Finset.sup_insert]
    simp only [id]
    exact max_eq_left hsupT
  have h2 : ((insert x T).filter (· < x)) = T.filter (· < x) := by
    rw [Finset.filter_insert, ite_eq_right_iff.mpr (fun h => absurd h (lt_irrefl x))]
  have h3 : ∀ y ∈ T, ((insert x T).filter (· < y)) = T.filter (· < y) := by
    intro y hy
    rw [Finset.filter_insert, ite_eq_right_iff.mpr (fun h => by have := hT y hy; omega)]
  rw [Finset.insert_val_of_notMem hnT, Finset.insert_val_of_notMem hxT]
  simp only [Multiset.map_cons, h1, h2]
  congr 2
  exact Multiset.map_congr rfl fun y hy => by simp only [h3 y hy]

/-- The block lengths of a coarsening sum to the weight. -/
theorem sum_gaps {n : ℕ} {T : Finset ℕ} (hT : IsCutSet n T) : (gaps n T).sum = n := by
  induction T using Finset.induction_on_max generalizing n with
  | empty => simp [gaps]
  | insert a s ha ih =>
    have hs : ∀ z ∈ s, z < a := ha
    have han : a < n := (Finset.mem_Ioo.mp (hT (Finset.mem_insert_self a s))).2
    rw [gaps_insert_max han hs, Multiset.sum_cons, ih]
    · omega
    · intro z hz
      exact Finset.mem_Ioo.mpr ⟨(Finset.mem_Ioo.mp (hT (Finset.mem_insert_of_mem hz))).1, hs z hz⟩

/-- The weight of `h_j`. -/
def hgenWeight : ℕ+ → ℕ := fun j => (j : ℕ)

lemma isWeightedHomogeneous_hgen (j : ℕ) : IsWeightedHomogeneous hgenWeight (hgen j) j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa [hgen] using isWeightedHomogeneous_one (R := ℤ) hgenWeight
  · have := isWeightedHomogeneous_X ℤ hgenWeight (Nat.toPNat j hj)
    have e : hgen j = X (Nat.toPNat j hj) := by simp [hgen, hj]; rfl
    rw [e]
    have e2 : ((Nat.toPNat j hj : ℕ+) : ℕ) = j := rfl
    convert this using 1
    exact e2.symm

lemma isWeightedHomogeneous_prod_hgen (M : Multiset ℕ) :
    IsWeightedHomogeneous hgenWeight (M.map hgen).prod M.sum := by
  induction M using Multiset.induction with
  | empty => simpa using isWeightedHomogeneous_one (R := ℤ) hgenWeight
  | cons a M ih =>
    simpa using (isWeightedHomogeneous_hgen a).mul ih

/-- `G_β` is weighted homogeneous of weight `n` (`wt h_j = j`). -/
theorem G_isWeightedHomogeneous {n : ℕ} {S : Finset ℕ} (hS : IsCutSet n S) :
    IsWeightedHomogeneous hgenWeight (G n S) n := by
  unfold G
  apply IsWeightedHomogeneous.sum
  intro T hT
  have hT' : IsCutSet n T := fun x hx => hS ((Finset.mem_powerset.mp hT) hx)
  have := isWeightedHomogeneous_prod_hgen (gaps n T)
  rwa [sum_gaps hT'] at this


open Finset MvPolynomial

/-- The coarsening polynomial of a weight-`n` composition is `h_n` plus a polynomial in
`h_1, …, h_{n-1}`: the retained-cut-free coarsening contributes `h_n` once, every other one is a
product of positive generators of index below `n`. -/
lemma G_sub_mem_supported {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) :
    G n S - hgen n ∈ MvPolynomial.supported ℤ {k : ℕ+ | (k : ℕ) < n} := by
  unfold G
  have h0 : (∅ : Finset ℕ) ∈ S.powerset := Finset.empty_mem_powerset S
  rw [← Finset.add_sum_erase _ _ h0]
  simp only [gaps_empty, Multiset.map_singleton, Multiset.prod_singleton, add_sub_cancel_left]
  refine Subalgebra.sum_mem _ fun T hT => ?_
  obtain ⟨hne, hTS⟩ := Finset.mem_erase.mp hT
  have hT' : IsCutSet n T := fun x hx => hS ((Finset.mem_powerset.mp hTS) hx)
  have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  have hpos := gaps_pos hn hT'
  have hcard : (gaps n T).card = T.card + 1 := by
    unfold gaps
    rw [Multiset.card_map]
    change (insert n T).card = _
    rw [Finset.card_insert_of_notMem]
    intro h
    have := Finset.mem_Ioo.mp (hT' h)
    omega
  refine Subalgebra.multiset_prod_mem _ fun f hf => ?_
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hf
  have hx0 := hpos x hx
  have hxn : x < n := by
    obtain ⟨M', hM'⟩ := Multiset.exists_cons_of_mem hx
    have hsum := sum_gaps hT'
    have hM'card : 0 < M'.card := by
      have := Finset.card_pos.mpr hTne
      have h2 : (gaps n T).card = M'.card + 1 := by rw [hM']; simp
      omega
    obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp hM'card
    have hy0 : 0 < y := hpos y (by rw [hM']; exact Multiset.mem_cons_of_mem hy)
    have hyle : y ≤ M'.sum := Multiset.le_sum_of_mem hy
    rw [hM', Multiset.sum_cons] at hsum
    omega
  have hxX : hgen x = X ⟨x, hx0⟩ := by simp [hgen, hx0]
  rw [hxX, MvPolynomial.supported_eq_adjoin_X]
  exact Algebra.subset_adjoin ⟨⟨x, hx0⟩, hxn, rfl⟩

lemma aeval_congr_supported {s : Set ℕ+} {q : Lam} (hq : q ∈ MvPolynomial.supported ℤ s)
    (f g : ℕ+ → Lam) (h : ∀ k ∈ s, f k = g k) :
    MvPolynomial.aeval f q = MvPolynomial.aeval g q := by
  rw [MvPolynomial.mem_supported] at hq
  have := MvPolynomial.eval₂Hom_congr' (f₁ := algebraMap ℤ Lam) (f₂ := algebraMap ℤ Lam)
    (g₁ := f) (g₂ := g) (p₁ := q) (p₂ := q) rfl (fun i hi _ => h i (hq hi)) rfl
  simpa [MvPolynomial.aeval_def] using this

lemma ringHom_aeval (ψ : Lam →+* Lam) (f : ℕ+ → Lam) (q : Lam) :
    ψ (MvPolynomial.aeval f q) = MvPolynomial.aeval (fun k => ψ (f k)) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.aeval_C, map_intCast, algebraMap_int_eq, eq_intCast]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, MvPolynomial.aeval_X, hp]

lemma isWeightedHomogeneous_aeval (g : ℕ+ → Lam)
    (hg : ∀ j : ℕ+, IsWeightedHomogeneous hgenWeight (g j) (j : ℕ)) {F : Lam} {s : ℕ}
    (hF : IsWeightedHomogeneous hgenWeight F s) :
    IsWeightedHomogeneous hgenWeight (MvPolynomial.aeval g F) s := by
  conv_lhs => rw [MvPolynomial.as_sum F]
  rw [map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have hds : Finsupp.weight hgenWeight d = s := hF (MvPolynomial.mem_support_iff.mp hd)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  have hprod : IsWeightedHomogeneous hgenWeight (d.prod fun j e => g j ^ e)
      (∑ j ∈ d.support, d j * (j : ℕ)) := by
    refine IsWeightedHomogeneous.prod _ _ _ fun j _ => ?_
    exact (hg j).pow (d j)
  have hw : (∑ j ∈ d.support, d j * (j : ℕ)) = s := by
    rw [← hds, Finsupp.weight_apply, Finsupp.sum]
    simp [hgenWeight]
  rw [hw] at hprod
  exact hprod.C_mul _

/-- The image `Θ_ε(h_r)` of the generator `h_r`: `G_{ε^{⊙(r/p)}}` if `p ∣ r`, else `h_r`. -/
noncomputable def thetaGen (p : ℕ) (E : Finset ℕ) (j : ℕ+) : Lam :=
  if p ∣ (j : ℕ) then G ((j : ℕ) / p * p) (nearPowerCuts p E ((j : ℕ) / p)) else X j

/-- `prop:coordinates`: the substitution `Θ_ε`, `h_r ↦ G_{ε^{⊙(r/p)}}` if `p ∣ r` and
`h_r ↦ h_r` otherwise, for the inner composition of weight `p` with cut set `E`. -/
noncomputable def Theta (p : ℕ) (E : Finset ℕ) : Lam →+* Lam :=
  (MvPolynomial.aeval (thetaGen p E) : Lam →ₐ[ℤ] Lam).toRingHom

lemma Theta_X (p : ℕ) (E : Finset ℕ) (j : ℕ+) : Theta p E (X j) = thetaGen p E j := by
  simp [Theta]

lemma Theta_apply (p : ℕ) (E : Finset ℕ) (q : Lam) :
    Theta p E q = MvPolynomial.aeval (thetaGen p E) q := rfl

lemma thetaGen_dvd {p : ℕ} {E : Finset ℕ} {j : ℕ+} (h : p ∣ (j : ℕ)) :
    thetaGen p E j = G ((j : ℕ) / p * p) (nearPowerCuts p E ((j : ℕ) / p)) := by
  simp [thetaGen, h]

lemma thetaGen_ndvd {p : ℕ} {E : Finset ℕ} {j : ℕ+} (h : ¬ p ∣ (j : ℕ)) :
    thetaGen p E j = X j := by
  simp [thetaGen, h]

/-- `Θ_ε(h_{pj}) = Ψ_ε(h_j)`. -/
lemma Theta_hgen_mul (p : ℕ) (hp : 0 < p) (E : Finset ℕ) (j : ℕ+) :
    Theta p E (hgen (p * j)) = Psi p E (hgen j) := by
  have hpj : 0 < p * (j : ℕ) := Nat.mul_pos hp j.pos
  have e : hgen (p * j) = (X (Nat.toPNat (p * j) hpj) : Lam) := hgen_pnat (Nat.toPNat (p * j) hpj)
  rw [e, Theta_X, Psi_hgen, thetaGen_dvd (j := Nat.toPNat (p * j) hpj) ⟨j, rfl⟩]
  have hc : ((Nat.toPNat (p * j) hpj : ℕ+) : ℕ) = p * j := rfl
  simp only [hc, Nat.mul_div_cancel_left _ hp, mul_comm]

/-- `Θ_ε` sends weighted-homogeneous polynomials of weight `s` to weighted-homogeneous
polynomials of weight `s`. -/
theorem Theta_weight {p : ℕ} (hp : 0 < p) {E : Finset ℕ} (hE : IsCutSet p E) {F : Lam} {s : ℕ}
    (hF : IsWeightedHomogeneous hgenWeight F s) :
    IsWeightedHomogeneous hgenWeight (Theta p E F) s := by
  rw [Theta_apply]
  refine isWeightedHomogeneous_aeval _ (fun j => ?_) hF
  by_cases h : p ∣ (j : ℕ)
  · rw [thetaGen_dvd h]
    have hw := G_isWeightedHomogeneous (nearPowerCuts_isCutSet hE ((j : ℕ) / p))
    rw [Nat.div_mul_cancel h] at hw
    rw [Nat.div_mul_cancel h]
    exact hw
  · rw [thetaGen_ndvd h]
    exact isWeightedHomogeneous_X ℤ hgenWeight j

/-- The tail `R_j = G_{ε^{⊙ j}} - h_{pj}` of the unitriangular substitution. -/
noncomputable def thetaTail (p : ℕ) (E : Finset ℕ) (j : ℕ) : Lam :=
  G (j * p) (nearPowerCuts p E j) - hgen (j * p)

/-- `prop:coordinates`, unitriangular form: `G_{ε^{⊙ j}} = h_{pj} + R_j(h_1, …, h_{pj-1})`. -/
theorem G_nearPower_eq {p : ℕ} (hp : 0 < p) {E : Finset ℕ} (hE : IsCutSet p E) {j : ℕ}
    (hj : 0 < j) :
    G (j * p) (nearPowerCuts p E j) = hgen (j * p) + thetaTail p E j ∧
      thetaTail p E j ∈ MvPolynomial.supported ℤ {k : ℕ+ | (k : ℕ) < j * p} := by
  refine ⟨by simp [thetaTail], ?_⟩
  exact G_sub_mem_supported (Nat.mul_pos hj hp) (nearPowerCuts_isCutSet hE j)

/-- The recursively defined integral inverse on generators. -/
noncomputable def phiFun (p : ℕ) (E : Finset ℕ) (r : ℕ) : Lam :=
  if p ∣ r ∧ 0 < r then
    hgen r - MvPolynomial.aeval
      (fun k : ℕ+ => if h : (k : ℕ) < r then phiFun p E k else 0) (thetaTail p E (r / p))
  else hgen r
termination_by r
decreasing_by exact h

/-- The integral inverse `Φ_ε` of `Θ_ε`. -/
noncomputable def Phi (p : ℕ) (E : Finset ℕ) : Lam →ₐ[ℤ] Lam :=
  MvPolynomial.aeval fun k : ℕ+ => phiFun p E k

lemma phiFun_dvd {p : ℕ} (E : Finset ℕ) {r : ℕ} (h : p ∣ r) (hr : 0 < r) :
    phiFun p E r = hgen r - MvPolynomial.aeval
      (fun k : ℕ+ => if (k : ℕ) < r then phiFun p E k else 0) (thetaTail p E (r / p)) := by
  rw [phiFun, if_pos ⟨h, hr⟩]
  simp only [dite_eq_ite]

lemma phiFun_ndvd {p : ℕ} (E : Finset ℕ) {r : ℕ} (h : ¬ (p ∣ r ∧ 0 < r)) :
    phiFun p E r = hgen r := by
  rw [phiFun, if_neg h]

lemma Theta_hgen_ndvd {p : ℕ} (E : Finset ℕ) {r : ℕ} (h : ¬ (p ∣ r ∧ 0 < r)) :
    Theta p E (hgen r) = hgen r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [hgen]
  · have hnd : ¬ p ∣ r := fun hd => h ⟨hd, hr⟩
    have e : hgen r = (X (Nat.toPNat r hr) : Lam) := hgen_pnat (Nat.toPNat r hr)
    rw [e, Theta_X, thetaGen_ndvd (j := Nat.toPNat r hr) hnd]

lemma Theta_phiFun {p : ℕ} (hp : 0 < p) {E : Finset ℕ} (hE : IsCutSet p E) :
    ∀ r : ℕ, Theta p E (phiFun p E r) = hgen r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    by_cases h : p ∣ r ∧ 0 < r
    · obtain ⟨hd, hr⟩ := h
      obtain ⟨j, rfl⟩ := hd
      have hj : 0 < j := Nat.pos_of_mul_pos_left hr
      rw [phiFun_dvd E ⟨j, rfl⟩ hr, map_sub]
      have hrj : p * j / p = j := Nat.mul_div_cancel_left _ hp
      rw [hrj]
      obtain ⟨hGeq, hsupp⟩ := G_nearPower_eq hp hE hj
      have hmul : j * p = p * j := mul_comm _ _
      have hGeq0 := hGeq
      rw [hmul] at hsupp hGeq
      have h1 : Theta p E (MvPolynomial.aeval
          (fun k : ℕ+ => if (k : ℕ) < p * j then phiFun p E k else 0) (thetaTail p E j))
          = thetaTail p E j := by
        rw [ringHom_aeval]
        have : MvPolynomial.aeval (fun k : ℕ+ =>
            Theta p E (if (k : ℕ) < p * j then phiFun p E k else 0)) (thetaTail p E j)
            = MvPolynomial.aeval (fun k : ℕ+ => (X k : Lam)) (thetaTail p E j) := by
          refine aeval_congr_supported hsupp _ _ fun k hk => ?_
          have hk' : (k : ℕ) < p * j := hk
          simp only [hk', if_true]
          rw [ih k hk', hgen_pnat]
        rw [this, MvPolynomial.aeval_X_left_apply]
      have h2 := Theta_hgen_mul p hp E (⟨j, hj⟩ : ℕ+)
      simp only [PNat.mk_coe] at h2
      rw [h1, h2, Psi_hgen, hGeq0, hmul]
      ring
    · rw [phiFun_ndvd E h, Theta_hgen_ndvd E h]


lemma Phi_X (p : ℕ) (E : Finset ℕ) (k : ℕ+) : Phi p E (X k) = phiFun p E k := by
  simp [Phi]

/-- `Φ_ε Θ_ε = id`. -/
lemma Phi_Theta {p : ℕ} (hp : 0 < p) {E : Finset ℕ} (hE : IsCutSet p E) (q : Lam) :
    Phi p E (Theta p E q) = q := by
  have key : ∀ j : ℕ+, Phi p E (Theta p E (X j)) = X j := by
    intro j
    rw [Theta_X]
    by_cases h : p ∣ (j : ℕ)
    · obtain ⟨i, hi⟩ := h
      have hi0 : 0 < i := Nat.pos_of_mul_pos_left (hi ▸ j.pos)
      obtain ⟨hGeq, hsupp⟩ := G_nearPower_eq hp hE hi0
      have hmul : i * p = p * i := mul_comm _ _
      have hjv : (j : ℕ) = p * i := hi
      rw [thetaGen_dvd ⟨i, hi⟩, hjv, Nat.mul_div_cancel_left _ hp, hmul]
      rw [hmul] at hGeq hsupp
      rw [hGeq, map_add]
      have hpi : 0 < p * i := Nat.mul_pos hp hi0
      have e2 : hgen (p * i) = (X (Nat.toPNat (p * i) hpi) : Lam) :=
        hgen_pnat (Nat.toPNat (p * i) hpi)
      have e3 : Phi p E (hgen (p * i)) = phiFun p E (p * i) := by
        rw [e2, Phi_X]; rfl
      rw [e3, phiFun_dvd E ⟨i, rfl⟩ hpi, Nat.mul_div_cancel_left _ hp]
      have : Phi p E (thetaTail p E i) = MvPolynomial.aeval
          (fun k : ℕ+ => if (k : ℕ) < p * i then phiFun p E k else 0) (thetaTail p E i) := by
        rw [Phi]
        refine aeval_congr_supported hsupp _ _ fun k hk => ?_
        have hk' : (k : ℕ) < p * i := hk
        simp [hk']
      rw [this]
      have hjX : (X j : Lam) = hgen (p * i) := by
        rw [← hgen_pnat j, hjv]
      rw [hjX]
      ring
    · rw [thetaGen_ndvd h, Phi_X, phiFun_ndvd E (fun hh => h hh.1), hgen_pnat]
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a j ha => simp only [map_mul, ha, key]

/-- `Θ_ε Φ_ε = id`. -/
lemma Theta_Phi {p : ℕ} (hp : 0 < p) {E : Finset ℕ} (hE : IsCutSet p E) (q : Lam) :
    Theta p E (Phi p E q) = q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a j ha =>
    simp only [map_mul, ha, Phi_X, Theta_phiFun hp hE, hgen_pnat]

/-- The image `Φ_ε(h_k)` is weighted homogeneous of weight `k`. -/
lemma phiFun_weight {p : ℕ} (hp : 0 < p) {E : Finset ℕ} (hE : IsCutSet p E) :
    ∀ r : ℕ, IsWeightedHomogeneous hgenWeight (phiFun p E r) r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    by_cases h : p ∣ r ∧ 0 < r
    · obtain ⟨hd, hr⟩ := h
      rw [phiFun_dvd E hd hr]
      refine (isWeightedHomogeneous_hgen r).sub ?_
      have htail : IsWeightedHomogeneous hgenWeight (thetaTail p E (r / p)) r := by
        have hj : 0 < r / p := Nat.div_pos (Nat.le_of_dvd hr hd) hp
        have hw := G_isWeightedHomogeneous (nearPowerCuts_isCutSet hE (r / p))
        rw [Nat.div_mul_cancel hd] at hw
        have := hw.sub (isWeightedHomogeneous_hgen r)
        unfold thetaTail
        rw [Nat.div_mul_cancel hd]
        exact this
      refine isWeightedHomogeneous_aeval _ (fun k => ?_) htail
      by_cases hk : (k : ℕ) < r
      · simp only [hk, if_true]; exact ih k hk
      · simp only [hk, if_false]; exact isWeightedHomogeneous_zero _ _ _
    · rw [phiFun_ndvd E h]; exact isWeightedHomogeneous_hgen r

/-- `prop:coordinates`: `Θ_ε` as an algebra automorphism of `Λ_ℤ` with the integral inverse
`Φ_ε`. -/
noncomputable def ThetaAlgEquiv {p : ℕ} (hp : 0 < p) {E : Finset ℕ} (hE : IsCutSet p E) :
    Lam ≃ₐ[ℤ] Lam :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval (thetaGen p E)) (Phi p E)
    (AlgHom.ext fun q => Theta_Phi hp hE q) (AlgHom.ext fun q => Phi_Theta hp hE q)

/-- `prop:coordinates`: `Θ_ε` is a ring automorphism of `Λ_ℤ`. -/
noncomputable def ThetaEquiv {p : ℕ} (hp : 0 < p) {E : Finset ℕ} (hE : IsCutSet p E) :
    Lam ≃+* Lam := (ThetaAlgEquiv hp hE).toRingEquiv

/-- `prop:coordinates`, automorphism and weight preservation: `ThetaEquiv` is `Θ_ε`, is a ring
automorphism of `Λ_ℤ`, and it and its inverse send weighted-homogeneous polynomials of weight
`s` (`wt h_j = j`) to weighted-homogeneous polynomials of weight `s`. -/
theorem prop_coordinates_automorphism {p : ℕ} (hp : 0 < p) {E : Finset ℕ} (hE : IsCutSet p E) :
    (∀ q, ThetaEquiv hp hE q = Theta p E q) ∧
    (∀ {F : Lam} {s : ℕ}, IsWeightedHomogeneous hgenWeight F s →
      IsWeightedHomogeneous hgenWeight (ThetaEquiv hp hE F) s) ∧
    (∀ {F : Lam} {s : ℕ}, IsWeightedHomogeneous hgenWeight F s →
      IsWeightedHomogeneous hgenWeight ((ThetaEquiv hp hE).symm F) s) := by
  have hsymm : ∀ q, (ThetaEquiv hp hE).symm q = Phi p E q := fun q => rfl
  refine ⟨fun q => rfl, fun {F s} hF => Theta_weight hp hE hF, fun {F s} hF => ?_⟩
  rw [hsymm]
  refine isWeightedHomogeneous_aeval _ (fun k => ?_) hF
  exact phiFun_weight hp hE k

/-- `eq:coordinates`: the generators `G_{ε^{⊙ j}}` and `h_r` (`p ∤ r`) of `Λ_ℤ`, indexed by
the positive integers `r` (`thetaGen p E r`), are algebraically independent over `ℤ` and
generate `Λ_ℤ`, so `Λ_ℤ = ℤ[G_ε, G_{ε^{⊙ 2}}, …, h_r (p ∤ r)]` is a polynomial ring in them. -/
theorem eq_coordinates {p : ℕ} (hp : 0 < p) {E : Finset ℕ} (hE : IsCutSet p E) :
    AlgebraicIndependent ℤ (thetaGen p E) ∧
      Algebra.adjoin ℤ (Set.range (thetaGen p E)) = ⊤ := by
  let e : Lam ≃ₐ[ℤ] Lam := ThetaAlgEquiv hp hE
  have hX : ∀ j, e (X j) = thetaGen p E j := fun j => Theta_X p E j
  have hcomp : (e.toAlgHom ∘ (X : ℕ+ → Lam)) = thetaGen p E := funext hX
  refine ⟨?_, ?_⟩
  · have := (algebraicIndependent_X (R := ℤ) (σ := ℕ+)).map' (f := e.toAlgHom) e.injective
    rwa [hcomp] at this
  · rw [← hcomp, Set.range_comp, Algebra.adjoin_image, MvPolynomial.adjoin_range_X,
      Algebra.map_top, AlgHom.range_eq_top]
    exact e.surjective

/-- `prop:coordinates`, retraction: `Ψ_ε π_p` is idempotent, fixes `im Ψ_ε` pointwise, and has
range exactly `im Ψ_ε`; that is, it is an idempotent retraction onto `im Ψ_ε`. -/
theorem prop_coordinates_retraction {p : ℕ} {E : Finset ℕ} (hp : 0 < p) (hE : IsCutSet p E) :
    ((Psi p E).comp (proj p)).comp ((Psi p E).comp (proj p)) = (Psi p E).comp (proj p) ∧
    (∀ x, ((Psi p E).comp (proj p)) (Psi p E x) = Psi p E x) ∧
    ((Psi p E).comp (proj p)).range = (Psi p E).range := by
  have hx : ∀ x, proj p (Psi p E x) = x := fun x => by
    have := congrArg (fun f : Lam →+* Lam => f x) (proj_Psi hp hE)
    simpa using this
  refine ⟨?_, fun x => by simp [hx], ?_⟩
  · apply ringHom_ext_Lam
    intro j
    simp [hx]
  · ext y
    constructor
    · rintro ⟨q, rfl⟩; exact ⟨proj p q, rfl⟩
    · rintro ⟨q, rfl⟩; exact ⟨Psi p E q, by simp [hx]⟩

end SkewRibbonCoarsenings
