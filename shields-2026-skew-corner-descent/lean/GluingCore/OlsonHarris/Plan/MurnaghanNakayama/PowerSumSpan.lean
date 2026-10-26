-- TODO-COPIED from skew-factor-gluing/lean/
-- SkewGluing/OlsonHarris/Plan/MurnaghanNakayama/PowerSumSpan.lean
import GluingCore.OlsonHarris.Plan.Defs

/-!
# The power sums span `Λ`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the input of thesis §5.1 (`OlsonHarris2024HopfApplications`)
that every element of `Λ = ℚ[h₁, h₂, …]` is a rational combination of the products `p_ν`.

`pProdSpan` is the `ℚ`-span of the products `p_ν` with positive parts.  It is closed under
multiplication (`pProdSpan_mul`), contains every `h_n` (Newton's identity, by strong induction,
`hPos_mem_pProdSpan`), hence is everything (`mem_pProdSpan`); membership in the span is the
list form of `Plan.exists_pProd_expansion` (`exists_pProd_expansion_aux`).

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace MN

open MvPolynomial

/-- The products `p_ν` with positive parts. -/
def pProdSet : Set Lambda := {f | ∃ ν : List ℕ, (∀ m ∈ ν, 0 < m) ∧ f = pProd ν}

/-- The `ℚ`-span of the products `p_ν`. -/
noncomputable def pProdSpan : Submodule ℚ Lambda := Submodule.span ℚ pProdSet

theorem pProd_mem_pProdSpan {ν : List ℕ} (hν : ∀ m ∈ ν, 0 < m) : pProd ν ∈ pProdSpan :=
  Submodule.subset_span ⟨ν, hν, rfl⟩

theorem pProd_append (ν ρ : List ℕ) : pProd (ν ++ ρ) = pProd ν * pProd ρ := by
  simp [pProd]

theorem pProdSpan_mul_pProd {ν : List ℕ} (hν : ∀ m ∈ ν, 0 < m) {g : Lambda}
    (hg : g ∈ pProdSpan) : pProd ν * g ∈ pProdSpan := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ρ, hρ, rfl⟩ := hx
    rw [← pProd_append]
    exact pProd_mem_pProdSpan (by
      intro m hm
      rcases List.mem_append.mp hm with h | h
      · exact hν m h
      · exact hρ m h)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem pProdSpan_mul {f g : Lambda} (hf : f ∈ pProdSpan) (hg : g ∈ pProdSpan) :
    f * g ∈ pProdSpan := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν, hν, rfl⟩ := hx
    exact pProdSpan_mul_pProd hν hg
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem one_mem_pProdSpan : (1 : Lambda) ∈ pProdSpan := by
  simpa [pProd] using pProd_mem_pProdSpan (ν := []) (by simp)

theorem pPoly_mem_pProdSpan {k : ℕ} (hk : 0 < k) : pPoly k ∈ pProdSpan := by
  simpa [pProd] using pProd_mem_pProdSpan (ν := [k]) (by simpa using hk)

/-- Newton's identity expresses `h_{n+1}` through the `p_i`. -/
theorem hPos_succ_eq (n : ℕ) :
    hPos (n + 1) = ((1 : ℚ) / (n + 1 : ℕ)) •
      (pPoly (n + 1) + ∑ i : Fin n, pPoly (i + 1) * hPos (n - i)) := by
  have h : pPoly (n + 1) = ((n + 1 : ℕ) : Lambda) * hPos (n + 1) -
      ∑ i : Fin n, pPoly (i + 1) * hPos (n - i) := by
    rw [pPoly]
  have h2 : pPoly (n + 1) + ∑ i : Fin n, pPoly (i + 1) * hPos (n - i) =
      ((n + 1 : ℕ) : Lambda) * hPos (n + 1) := by
    rw [h]; ring
  rw [h2]
  have hq : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [Algebra.smul_def, ← mul_assoc]
  have : (algebraMap ℚ Lambda) ((1 : ℚ) / (n + 1 : ℕ)) * ((n + 1 : ℕ) : Lambda) = 1 := by
    rw [show ((n + 1 : ℕ) : Lambda) = algebraMap ℚ Lambda ((n + 1 : ℕ) : ℚ) by simp,
      ← map_mul, one_div, inv_mul_cancel₀ hq, map_one]
  rw [this, one_mul]

theorem hPos_mem_pProdSpan (n : ℕ) : hPos n ∈ pProdSpan := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simpa using one_mem_pProdSpan
    · rw [hPos_succ_eq]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ (pPoly_mem_pProdSpan (by omega))
        (Submodule.sum_mem _ fun i _ => pProdSpan_mul (pPoly_mem_pProdSpan (by omega))
          (ih _ (by omega))))

theorem X_mem_pProdSpan (k : ℕ+) : (X k : Lambda) ∈ pProdSpan := by
  rw [← hPos_pnat]
  exact hPos_mem_pProdSpan k

theorem mem_pProdSpan (f : Lambda) : f ∈ pProdSpan := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have : (C a : Lambda) = a • (1 : Lambda) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ one_mem_pProdSpan
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | mul_X p k hp => exact pProdSpan_mul hp (X_mem_pProdSpan k)

/-- Membership in the span of the `p_ν` is the list form of a rational combination. -/
theorem exists_pProd_expansion_aux {f : Lambda} (hf : f ∈ pProdSpan) :
    ∃ l : List (ℚ × List ℕ), (∀ p ∈ l, ∀ m ∈ p.2, 0 < m) ∧
      f = (l.map fun p => p.1 • pProd p.2).sum := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν, hν, rfl⟩ := hx
    exact ⟨[(1, ν)], by simpa using hν, by simp⟩
  | zero => exact ⟨[], by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨l₁, h₁, e₁⟩ := hx
    obtain ⟨l₂, h₂, e₂⟩ := hy
    refine ⟨l₁ ++ l₂, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · exact h₁ p h
      · exact h₂ p h
    · rw [List.map_append, List.sum_append, e₁, e₂]
  | smul c x _ hx =>
    obtain ⟨l, h, e⟩ := hx
    refine ⟨l.map fun p => (c * p.1, p.2), ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact h q hq
    · rw [e, List.smul_sum, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun p _ => ?_
      simp [mul_smul]

end MN

end Plan

end GluingCore
