/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.MixedTerminal

/-!
# The triangular readout of a power-sum expansion

«Recovering mixed ribbon factors» (`sec:mixed-extraction`, `rt:outer-triangle`) of
`shields-2026-skew-marked-factor.tex`.
For a word `w` of positive parts, `mixedWord` applies `B_{w₁}` first, then `B_{w₂}`, and so on.
On a power-sum monomial `p_L` of the same weight, the word gives zero when it is shorter than
`L`, gives zero when it is as long as `L` but not a rearrangement of it, and gives a positive
constant when it is a rearrangement of `L` (for `ρ > 0`).
Consequently a function of weight `m` is determined by the constants `B_ν f`, `ν ⊢ m`.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

variable (p ρ : ℚ)

/-- The word `B_{w₁}` first, then `B_{w₂}`, and so on. -/
def mixedWord : List ℕ → Lambda →ₗ[ℚ] Lambda
  | [] => LinearMap.id
  | a :: w => (mixedWord w).comp (mixedOp p ρ a).toLinearMap

theorem mixedWord_cons (a : ℕ) (w : List ℕ) (f : Lambda) :
    mixedWord p ρ (a :: w) f = mixedWord p ρ w (mixedOp p ρ a f) := rfl

/-- The terms of `B_a p_L` that keep the number of power-sum factors. -/
def growTerms (a : ℕ) : List ℕ → List (ℚ × List ℕ)
  | [] => []
  | j :: L => (if a < j then [(p * j, (j - a) :: L)] else []) ++
      (growTerms a L).map (fun cM => (cM.1, j :: cM.2))

/-- The factors `p_a` of `L` removed one at a time. -/
def remTerms (a : ℕ) : List ℕ → List (List ℕ)
  | [] => []
  | j :: L => (if a = j then [L] else []) ++ (remTerms a L).map (fun M => j :: M)

theorem pProd_cons (j : ℕ) (L : List ℕ) : pProd (j :: L) = pPoly j * pProd L := by
  simp [pProd]

theorem mixedOp_pProd {a : ℕ} (ha : 0 < a) (L : List ℕ) :
    mixedOp p ρ a (pProd L) =
      ((growTerms p a L).map (fun cM => C cM.1 * pProd cM.2)).sum +
        C (ρ * a) * ((remTerms a L).map pProd).sum := by
  induction L with
  | nil => simp [growTerms, remTerms, pProd, Derivation.map_one_eq_zero]
  | cons j L ih =>
    have keyG : ∀ l : List (ℚ × List ℕ),
        (l.map (fun x => C x.1 * (pPoly j * pProd x.2))).sum =
          pPoly j * (l.map (fun cM => C cM.1 * pProd cM.2)).sum := by
      intro l; induction l with
      | nil => simp
      | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    have keyR : ∀ l : List (List ℕ),
        (l.map (fun x => pPoly j * pProd x)).sum = pPoly j * (l.map pProd).sum := by
      intro l; induction l with
      | nil => simp
      | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    have hG : ((growTerms p a (j :: L)).map (fun cM => C cM.1 * pProd cM.2)).sum =
        (if a < j then C (p * j) * pPoly (j - a) * pProd L else 0) +
        pPoly j * ((growTerms p a L).map (fun cM => C cM.1 * pProd cM.2)).sum := by
      simp only [growTerms, List.map_append, List.sum_append, List.map_map, Function.comp_def,
        pProd_cons]
      rw [keyG]
      split_ifs <;> simp [pProd_cons, map_mul] <;> ring
    have hR : ((remTerms a (j :: L)).map pProd).sum =
        (if a = j then pProd L else 0) + pPoly j * ((remTerms a L).map pProd).sum := by
      simp only [remTerms, List.map_append, List.sum_append, List.map_map, Function.comp_def,
        pProd_cons]
      rw [keyR]
      split_ifs <;> simp
    rw [pProd_cons, Derivation.leibniz, ih, mixedOp_pPoly p ρ ha, hG, hR]
    simp only [smul_eq_mul]
    by_cases h1 : a < j
    · have h2 : ¬ a = j := by omega
      simp only [h1, h2, ite_true, ite_false, mul_zero, add_zero]
      ring
    · by_cases h2 : a = j
      · subst h2
        simp only [lt_irrefl, ite_true, ite_false, mul_zero, add_zero, zero_add]
        ring
      · simp only [h1, h2, ite_false, mul_zero, add_zero, zero_add]
        ring

theorem growTerms_spec {a : ℕ} :
    ∀ (L : List ℕ) (cM : ℚ × List ℕ), (∀ x ∈ L, 0 < x) → cM ∈ growTerms p a L →
      cM.2.length = L.length ∧ cM.2.sum + a = L.sum ∧ ∀ x ∈ cM.2, 0 < x
  | [], cM, _, h => by simp [growTerms] at h
  | j :: L, cM, hpos, h => by
    simp only [growTerms, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨cM', hcM', rfl⟩
    · split_ifs at h with hj
      · simp only [List.mem_singleton] at h
        subst h
        refine ⟨rfl, ?_, ?_⟩
        · simp only [List.sum_cons]; omega
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · omega
          · exact hpos x (List.mem_cons_of_mem _ hx)
      · simp at h
    · have ih := growTerms_spec L cM' (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) hcM'
      refine ⟨by simp [ih.1], by simp only [List.sum_cons]; omega, ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hpos _ (List.mem_cons_self ..)
      · exact ih.2.2 x hx

theorem remTerms_perm (a : ℕ) :
    ∀ (L M : List ℕ), M ∈ remTerms a L → (a :: M).Perm L
  | [], M, h => by simp [remTerms] at h
  | j :: L, M, h => by
    simp only [remTerms, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨M', hM', rfl⟩
    · split_ifs at h with hj
      · simp only [List.mem_singleton] at h
        subst h; subst hj; exact List.Perm.refl _
      · simp at h
    · exact (List.Perm.swap j a M').trans ((remTerms_perm a L M' hM').cons j)

theorem remTerms_ne_nil (a : ℕ) : ∀ (L : List ℕ), a ∈ L → remTerms a L ≠ []
  | [], h => by simp at h
  | j :: L, h => by
    simp only [remTerms]
    by_cases hj : a = j
    · simp [hj]
    · have : a ∈ L := by simpa [hj] using h
      have := remTerms_ne_nil a L this
      simp [hj, this]

theorem mixedWord_C_mul (w : List ℕ) (c : ℚ) (f : Lambda) :
    mixedWord p ρ w (C c * f) = C c * mixedWord p ρ w f := by
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, MvPolynomial.smul_eq_C_mul]

theorem list_sum_const {α : Type*} (Ms : List α) (f : α → Lambda) (hne : Ms ≠ [])
    (h : ∀ M ∈ Ms, ∃ c : ℚ, 0 < c ∧ f M = C c) :
    ∃ c : ℚ, 0 < c ∧ (Ms.map f).sum = C c := by
  induction Ms with
  | nil => exact absurd rfl hne
  | cons M Ms ih =>
    obtain ⟨c, hc, hfM⟩ := h M (List.mem_cons_self ..)
    by_cases hMs : Ms = []
    · subst hMs; exact ⟨c, hc, by simp [hfM]⟩
    · obtain ⟨c', hc', hs⟩ := ih hMs (fun N hN => h N (List.mem_cons_of_mem _ hN))
      exact ⟨c + c', by positivity, by simp only [List.map_cons, List.sum_cons, hfM, hs, map_add]⟩

theorem word_pProd (hρ : 0 < ρ) : ∀ (w L : List ℕ), (∀ x ∈ w, 0 < x) → (∀ x ∈ L, 0 < x) →
    w.sum = L.sum →
    (w.length < L.length → mixedWord p ρ w (pProd L) = 0) ∧
    (w.length = L.length →
      (w.Perm L → ∃ c : ℚ, 0 < c ∧ mixedWord p ρ w (pProd L) = C c) ∧
      (¬ w.Perm L → mixedWord p ρ w (pProd L) = 0))
  | [], L, _, hL, hs => by
    have hL0 : L = [] := by
      cases L with
      | nil => rfl
      | cons x L =>
        have := hL x (List.mem_cons_self ..)
        simp only [List.sum_nil, List.sum_cons] at hs
        omega
    subst hL0
    refine ⟨by simp, fun _ => ⟨fun _ => ⟨1, one_pos, by simp [mixedWord, pProd]⟩, fun h => absurd (List.Perm.refl _) h⟩⟩
  | a :: w', L, hw, hL, hs => by
    have ha : 0 < a := hw a (List.mem_cons_self ..)
    have hw' : ∀ x ∈ w', 0 < x := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    have hs' : a + w'.sum = L.sum := by simpa using hs
    -- the expansion of the first operator
    have hexp : mixedWord p ρ (a :: w') (pProd L) =
        ((growTerms p a L).map (fun cM => C cM.1 * mixedWord p ρ w' (pProd cM.2))).sum +
          C (ρ * a) * ((remTerms a L).map (fun M => mixedWord p ρ w' (pProd M))).sum := by
      rw [mixedWord_cons, mixedOp_pProd p ρ ha, map_add, map_list_sum, mixedWord_C_mul,
        List.map_map, map_list_sum, List.map_map]
      congr 2
      · apply List.map_congr_left
        intro cM _
        simp [mixedWord_C_mul]
    rw [hexp]
    have hgrow : w'.length + 1 ≤ L.length →
        ((growTerms p a L).map
          (fun cM => C cM.1 * mixedWord p ρ w' (pProd cM.2))).sum = 0 := by
      intro hlen
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨cM, hcM, rfl⟩ := List.mem_map.mp hx
      obtain ⟨h1, h2, h3⟩ := growTerms_spec p L cM hL hcM
      have := (word_pProd hρ w' cM.2 hw' h3 (by omega)).1 (by omega)
      rw [this, mul_zero]
    have hremprops : ∀ M ∈ remTerms a L, M.length + 1 = L.length ∧ M.sum + a = L.sum ∧
        (∀ x ∈ M, 0 < x) := by
      intro M hM
      have hp := remTerms_perm a L M hM
      refine ⟨by simpa using hp.length_eq, by have := hp.sum_eq; simp at this; omega, ?_⟩
      intro x hx
      exact hL x (hp.subset (List.mem_cons_of_mem _ hx))
    constructor
    · intro hlen
      rw [hgrow (by simp at hlen; omega)]
      have : ((remTerms a L).map (fun M => mixedWord p ρ w' (pProd M))).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hx
        obtain ⟨h1, h2, h3⟩ := hremprops M hM
        exact (word_pProd hρ w' M hw' h3 (by omega)).1 (by simp at hlen; omega)
      rw [this, mul_zero, zero_add]
    · intro hlen
      have hlen' : w'.length + 1 = L.length := by simpa using hlen
      rw [hgrow (by omega), zero_add]
      constructor
      · intro hperm
        have haL : a ∈ L := hperm.subset (List.mem_cons_self ..)
        obtain ⟨c, hc, hsum⟩ := list_sum_const (remTerms a L)
          (fun M => mixedWord p ρ w' (pProd M)) (remTerms_ne_nil a L haL) (by
            intro M hM
            obtain ⟨h1, h2, h3⟩ := hremprops M hM
            have hpM : w'.Perm M := by
              have := hperm.trans (remTerms_perm a L M hM).symm
              exact (List.perm_cons a).1 this
            exact ((word_pProd hρ w' M hw' h3 (by omega)).2 (by omega)).1 hpM)
        refine ⟨ρ * a * c, by positivity, ?_⟩
        rw [hsum, ← map_mul]
      · intro hnp
        have : ((remTerms a L).map (fun M => mixedWord p ρ w' (pProd M))).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hx
          obtain ⟨h1, h2, h3⟩ := hremprops M hM
          refine ((word_pProd hρ w' M hw' h3 (by omega)).2 (by omega)).2 ?_
          intro hpM
          exact hnp ((((List.perm_cons a).2 hpM).trans (remTerms_perm a L M hM)))
        rw [this, mul_zero]

/-- A product of powers of power sums is `p_L` for a list `L` of the right weight. -/
theorem exists_list_prod (e : ℕ+ → ℕ) (s : Finset ℕ+) :
    ∃ L : List ℕ, (∀ x ∈ L, 0 < x) ∧ L.sum = ∑ k ∈ s, e k * (k : ℕ) ∧
      ∏ k ∈ s, pPoly (k : ℕ) ^ e k = pProd L := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp, by simp [pProd]⟩
  | insert k s hk ih =>
    obtain ⟨L, hpos, hsum, hprod⟩ := ih
    refine ⟨List.replicate (e k) (k : ℕ) ++ L, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rw [(List.mem_replicate.mp hx).2]; exact k.pos
      · exact hpos x hx
    · rw [Finset.sum_insert hk, List.sum_append, List.sum_replicate, hsum]
      simp [mul_comm]
    · rw [Finset.prod_insert hk, hprod]
      simp [pProd, List.prod_append, List.map_replicate, List.prod_replicate]

/-- **A function of weight `m` is determined by its triangular readout**: if `B_ν f = 0` for every
partition `ν ⊢ m` (nonincreasing, `ν₁` acting first), then `f = 0`. -/
theorem readout_injective (hρ : 0 < ρ) {m : ℕ} {f : Lambda}
    (hf : IsWeightedHomogeneous degWeight f m)
    (h : ∀ ν : List ℕ, (∀ x ∈ ν, 0 < x) → ν.sum = m → ν.Pairwise (· ≥ ·) →
      mixedWord p ρ ν f = 0) : f = 0 := by
  classical
  have hg := homogeneous_powerSumEquiv_symm hf
  set g := powerSumEquiv.symm f with hgdef
  have hfg : f = powerSumEquiv g := by simp [hgdef]
  -- the list attached to each monomial
  have hex : ∀ d ∈ g.support, ∃ L : List ℕ, L.Pairwise (· ≥ ·) ∧ (∀ x ∈ L, 0 < x) ∧
      L.sum = m ∧ powerSumEquiv (monomial d (g.coeff d)) = C (g.coeff d) * pProd L := by
    intro d hd
    have hw := hg (MvPolynomial.mem_support_iff.mp hd)
    obtain ⟨L, hpos, hsum, hprod⟩ := exists_list_prod (fun k => d k) d.support
    have hwt : ∑ k ∈ d.support, d k * (k : ℕ) = m := by
      simpa [Finsupp.weight_apply, Finsupp.sum, degWeight, smul_eq_mul] using hw
    refine ⟨L.insertionSort (· ≥ ·), ?_, ?_, ?_, ?_⟩
    · exact List.pairwise_insertionSort _ _
    · intro x hx; exact hpos x ((List.perm_insertionSort _ L).subset hx)
    · rw [(List.perm_insertionSort _ L).sum_eq, hsum, hwt]
    · rw [MvPolynomial.monomial_eq, map_mul, map_finsuppProd]
      have hsplit : powerSumEquiv (C (g.coeff d)) = C (g.coeff d) := powerSumEquiv.commutes _
      rw [hsplit]
      congr 1
      have : pProd (L.insertionSort (· ≥ ·)) = pProd L := by
        unfold pProd
        exact ((List.perm_insertionSort _ L).map _).prod_eq
      rw [this, ← hprod]
      simp [Finsupp.prod, powerSumEquiv_X]
  choose! Ld hLd1 hLd2 hLd3 hLd4 using hex
  set F : Finset (List ℕ) := g.support.image Ld with hF
  set γ : List ℕ → ℚ := fun L => ∑ d ∈ g.support.filter (fun d => Ld d = L), g.coeff d with hγ
  have hfsum : f = ∑ L ∈ F, C (γ L) * pProd L := by
    rw [hfg, MvPolynomial.as_sum g, map_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := g.support) (t := F) (g := Ld)
      (fun d hd => Finset.mem_image_of_mem _ hd)]
    refine Finset.sum_congr rfl fun L hL => ?_
    simp only [hγ, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_filter] at hd
    rw [hLd4 d hd.1, hd.2]
  by_contra hf0
  have hex0 : ∃ L ∈ F, γ L ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hf0
    rw [hfsum]
    exact Finset.sum_eq_zero fun L hL => by rw [hno L hL]; simp
  obtain ⟨L₀, hL₀, hmin⟩ := Finset.exists_min_image (F.filter fun L => γ L ≠ 0) List.length
    (by obtain ⟨L, hL, hne⟩ := hex0; exact ⟨L, Finset.mem_filter.mpr ⟨hL, hne⟩⟩)
  obtain ⟨hL₀F, hγ₀⟩ := Finset.mem_filter.mp hL₀
  have hprops : ∀ L ∈ F, L.Pairwise (· ≥ ·) ∧ (∀ x ∈ L, 0 < x) ∧ L.sum = m := by
    intro L hL
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hL
    exact ⟨hLd1 d hd, hLd2 d hd, hLd3 d hd⟩
  obtain ⟨p0, q0, r0⟩ := hprops L₀ hL₀F
  have hzero := h L₀ q0 r0 p0
  rw [hfsum, map_sum] at hzero
  simp only [mixedWord_C_mul] at hzero
  rw [Finset.sum_eq_single L₀] at hzero
  · have hT := word_pProd p ρ hρ L₀ L₀ q0 q0 rfl
    obtain ⟨c, hc, hcv⟩ := (hT.2 rfl).1 (List.Perm.refl _)
    rw [hcv, ← map_mul] at hzero
    have := MvPolynomial.C_injective ℕ+ ℚ (hzero.trans (map_zero C).symm)
    exact hγ₀ ((mul_eq_zero.mp this).resolve_right hc.ne')
  · intro L hL hne
    by_cases hγL : γ L = 0
    · simp [hγL]
    · obtain ⟨pL, qL, rL⟩ := hprops L hL
      have hle : L₀.length ≤ L.length := hmin L (Finset.mem_filter.mpr ⟨hL, hγL⟩)
      have hT := word_pProd p ρ hρ L₀ L q0 qL (by rw [r0, rL])
      rcases lt_or_eq_of_le hle with hlt | heq
      · rw [hT.1 hlt, mul_zero]
      · have hnp : ¬ L₀.Perm L := fun hp =>
          hne.symm (hp.eq_of_pairwise' p0 pL)
        rw [(hT.2 heq).2 hnp, mul_zero]
  · intro hno; exact absurd hL₀F hno

end SkewMarkedFactor
