-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/Kernel/Independence.lean
import GluingCore.OlsonHarris.Plan.Kernel.RibbonAdd

/-!
# Linear independence of the Schur functions of Young diagrams

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.2 (`OlsonHarris2024HopfApplications`), the
linear independence of the Schur functions `s_σ` of the Young diagrams `σ` in `Λ`.

**Differs from the paper's route.**  The source takes this from the orthonormality of the Schur
functions; here the Schur functions of the Young diagrams of one size `n` span the degree-`n`
part of `Λ` (the power sums span `Λ`, and each product `p_ν` is a combination of `s_σ` by
iterating the multiplication form of the Murnaghan–Nakayama rule), the monomials `h_{σ₁} h_{σ₂} ⋯`
are `p(n)` independent elements of that part, so the `p(n)` Schur functions are independent.

Uses `pPoly_mul_cellSchur_ferrers` and `exists_pProd_expansion`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace KernelAux

open MvPolynomial Shields

/-- The span of the Schur functions of the Young diagrams with `n` cells. -/
noncomputable def ferrersSpan (n : ℕ) : Submodule ℚ Lambda :=
  Submodule.span ℚ (ferrersSchur '' {sigma : YoungDiagram | sigma.card = n})

theorem ferrersSchur_mem_ferrersSpan (sigma : YoungDiagram) :
    ferrersSchur sigma ∈ ferrersSpan sigma.card :=
  Submodule.subset_span ⟨sigma, rfl, rfl⟩

theorem intCast_mul_eq_smul (z : ℤ) (f : Lambda) : (z : Lambda) * f = (z : ℚ) • f := by
  rw [Algebra.smul_def]
  simp

theorem pProd_mul_ferrersSchur_mem {nu : List ℕ} (hnu : ∀ m ∈ nu, 0 < m) (rho : YoungDiagram) :
    pProd nu * ferrersSchur rho ∈ ferrersSpan (rho.card + nu.sum) := by
  induction nu generalizing rho with
  | nil =>
    simpa [pProd] using ferrersSchur_mem_ferrersSpan rho
  | cons m nu ih =>
    have hm : 0 < m := hnu m List.mem_cons_self
    have hnu' : ∀ k ∈ nu, 0 < k := fun k hk => hnu k (List.mem_cons_of_mem _ hk)
    have : pProd (m :: nu) * ferrersSchur rho = pProd nu * (pPoly m * ferrersSchur rho) := by
      simp only [pProd, List.map_cons, List.prod_cons]
      ring
    rw [this, pPoly_mul_ferrersSchur rho hm, Finset.mul_sum]
    refine Submodule.sum_mem _ fun sigma hs => ?_
    have hc := card_of_mem_ribbonAdds hs
    have h2 := ih hnu' sigma
    rw [hc] at h2
    have h3 : pProd nu * ((ribbonSign (skewDiagram sigma rho) : Lambda) * ferrersSchur sigma) =
        (ribbonSign (skewDiagram sigma rho) : ℚ) • (pProd nu * ferrersSchur sigma) := by
      rw [← intCast_mul_eq_smul]
      ring
    rw [h3]
    refine Submodule.smul_mem _ _ ?_
    have h4 : rho.card + m + nu.sum = rho.card + (m :: nu).sum := by
      simp only [List.sum_cons]; ring
    rwa [h4] at h2

theorem pProd_mem_ferrersSpan {nu : List ℕ} (hnu : ∀ m ∈ nu, 0 < m) :
    pProd nu ∈ ferrersSpan nu.sum := by
  simpa [ferrersSchur_bot, card_bot_young] using pProd_mul_ferrersSchur_mem hnu ⊥

/-- Every homogeneous element of degree `n` of `Λ` is a combination of the Schur functions of the
Young diagrams with `n` cells. -/
theorem mem_ferrersSpan_of_isWeightedHomogeneous {n : ℕ} {f : Lambda}
    (hf : IsWeightedHomogeneous degWeight f n) : f ∈ ferrersSpan n := by
  classical
  obtain ⟨l, hpos, hfl⟩ := exists_pProd_expansion f
  have key : ∀ l : List (ℚ × List ℕ), (∀ p ∈ l, ∀ m ∈ p.2, 0 < m) →
      weightedHomogeneousComponent degWeight n
        ((l.map fun p => p.1 • pProd p.2).sum) ∈ ferrersSpan n := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons p l ih =>
      intro hl
      rw [List.map_cons, List.sum_cons, map_add]
      refine add_mem ?_ (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
      rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have hp := isWeightedHomogeneous_pProd p.2
      rw [weightedHomogeneousComponent_of_mem
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hp)]
      by_cases hn : n = p.2.sum
      · simp only [hn, ite_true]
        exact pProd_mem_ferrersSpan (hl p List.mem_cons_self)
      · simp only [hn, ite_false]
        exact zero_mem _
  have := key l hpos
  rw [← hfl, weightedHomogeneousComponent_eq_self hf] at this
  exact this

/-! ### Degreewise independence -/

/-- The monomial `h_{σ₁} h_{σ₂} ⋯` of a Young diagram, as an exponent vector. -/
noncomputable def rowMonomial (sigma : YoungDiagram) : ℕ+ →₀ ℕ :=
  Multiset.toFinsupp ((sigma.rowLens.map Nat.toPNat' : List ℕ+) : Multiset ℕ+)

theorem coe_toPNat'_of_mem_rowLens (sigma : YoungDiagram) {l : ℕ} (hl : l ∈ sigma.rowLens) :
    ((Nat.toPNat' l : ℕ+) : ℕ) = l := by
  have := YoungDiagram.pos_of_mem_rowLens sigma l hl
  rw [Nat.toPNat'_coe]
  simp [this]

theorem weight_toFinsupp (s : Multiset ℕ+) :
    Finsupp.weight degWeight (Multiset.toFinsupp s) = (s.map degWeight).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, map_add Multiset.toFinsupp, map_add (Finsupp.weight degWeight),
      ih, Multiset.map_add, Multiset.sum_add, Multiset.toFinsupp_singleton,
      Finsupp.weight_single]
    simp

theorem weight_rowMonomial (sigma : YoungDiagram) :
    Finsupp.weight degWeight (rowMonomial sigma) = sigma.card := by
  unfold rowMonomial
  rw [weight_toFinsupp, Multiset.map_coe, Multiset.sum_coe, List.map_map]
  rw [← YoungDiagram.sum_rowLens_eq_card]
  congr 1
  refine (List.map_congr_left fun l hl => ?_).trans (List.map_id _)
  exact coe_toPNat'_of_mem_rowLens sigma hl

theorem rowMonomial_injective : Function.Injective rowMonomial := by
  intro sigma tau h
  unfold rowMonomial at h
  have h1 := Multiset.toFinsupp.injective h
  rw [Multiset.coe_eq_coe] at h1
  have h2 := h1.map (fun p : ℕ+ => (p : ℕ))
  rw [List.map_map, List.map_map] at h2
  have e1 : sigma.rowLens = (sigma.rowLens.map Nat.toPNat').map (fun p : ℕ+ => (p : ℕ)) := by
    rw [List.map_map]
    exact ((List.map_congr_left fun l hl => coe_toPNat'_of_mem_rowLens sigma hl).trans
      (List.map_id _)).symm
  have e2 : tau.rowLens = (tau.rowLens.map Nat.toPNat').map (fun p : ℕ+ => (p : ℕ)) := by
    rw [List.map_map]
    exact ((List.map_congr_left fun l hl => coe_toPNat'_of_mem_rowLens tau hl).trans
      (List.map_id _)).symm
  have h3 : sigma.rowLens.Perm tau.rowLens := by
    rw [e1, e2]
    rw [List.map_map, List.map_map]
    exact h2
  have h4 := h3.eq_of_sortedGE (YoungDiagram.rowLens_sorted sigma) (YoungDiagram.rowLens_sorted tau)
  rw [← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := sigma),
    ← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := tau)]
  congr 1

theorem ferrersSpan_eq_span_range (n : ℕ) :
    ferrersSpan n = Submodule.span ℚ
      (Set.range fun sigma : {sigma : YoungDiagram // sigma.card = n} => ferrersSchur sigma.1) := by
  unfold ferrersSpan
  congr 1
  ext f
  constructor
  · rintro ⟨sigma, hs, rfl⟩
    exact ⟨⟨sigma, hs⟩, rfl⟩
  · rintro ⟨⟨sigma, hs⟩, rfl⟩
    exact ⟨sigma, hs, rfl⟩

/-- The Schur functions of the Young diagrams with `n` cells are linearly independent. -/
theorem linearIndependent_ferrersSchur_deg (n : ℕ) :
    LinearIndependent ℚ
      (fun sigma : {sigma : YoungDiagram // sigma.card = n} => ferrersSchur sigma.1) := by
  classical
  have hfin : Finite {sigma : YoungDiagram // sigma.card = n} :=
    (finite_young_card n).to_subtype
  have : Fintype {sigma : YoungDiagram // sigma.card = n} := Fintype.ofFinite _
  rw [linearIndependent_iff_card_le_finrank_span]
  let u : {sigma : YoungDiagram // sigma.card = n} → Lambda :=
    fun sigma => monomial (rowMonomial sigma.1) (1 : ℚ)
  have hu : LinearIndependent ℚ u := by
    have := (MvPolynomial.basisMonomials ℕ+ ℚ).linearIndependent.comp
      (fun sigma : {sigma : YoungDiagram // sigma.card = n} => rowMonomial sigma.1)
      (fun a b h => Subtype.ext (rowMonomial_injective h))
    simpa [Function.comp_def, u, MvPolynomial.coe_basisMonomials] using this
  have hmem : ∀ sigma, u sigma ∈ Submodule.span ℚ
      (Set.range fun sigma : {sigma : YoungDiagram // sigma.card = n} => ferrersSchur sigma.1) := by
    intro sigma
    rw [← ferrersSpan_eq_span_range]
    refine mem_ferrersSpan_of_isWeightedHomogeneous ?_
    have := isWeightedHomogeneous_monomial degWeight (rowMonomial sigma.1) (1 : ℚ)
      (m := Finsupp.weight degWeight (rowMonomial sigma.1)) rfl
    rw [weight_rowMonomial, sigma.2] at this
    exact this
  set W := Submodule.span ℚ
      (Set.range fun sigma : {sigma : YoungDiagram // sigma.card = n} => ferrersSchur sigma.1)
    with hW
  have : Module.Finite ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hu' : LinearIndependent ℚ (fun sigma => (⟨u sigma, hmem sigma⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hu
  exact hu'.fintype_card_le_finrank

/-- **The Schur functions of the Young diagrams are linearly independent in `Λ`.** -/
theorem linearIndependent_ferrersSchur : LinearIndependent ℚ ferrersSchur := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  ext sigma
  by_contra hne
  set n := sigma.card with hn
  have hc := congrArg (weightedHomogeneousComponent degWeight n) hl
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_zero] at hc
  have hterm : ∀ j ∈ l.support, weightedHomogeneousComponent degWeight n (l j • ferrersSchur j) =
      if j.card = n then l j • ferrersSchur j else 0 := by
    intro j _
    rw [map_smul, weightedHomogeneousComponent_of_mem
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (ferrersSchur_homogeneous j))]
    by_cases h : n = j.card
    · simp [h]
    · have h' : ¬ j.card = n := fun e => h e.symm
      simp [h, h']
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter] at hc
  have hli := linearIndependent_iff'.mp (linearIndependent_ferrersSchur_deg n)
  have hsum : ∑ i ∈ l.support.subtype (fun j : YoungDiagram => j.card = n),
      (fun i : {sigma : YoungDiagram // sigma.card = n} => l i.1) i • ferrersSchur i.1 = 0 := by
    simp only []
    rw [Finset.sum_subtype_eq_sum_filter (f := fun j => l j • ferrersSchur j)]
    exact hc
  have := hli _ _ hsum ⟨sigma, hn.symm⟩ (by
    rw [Finset.mem_subtype]
    exact Finsupp.mem_support_iff.mpr hne)
  exact hne this

end KernelAux

end Plan

end GluingCore
