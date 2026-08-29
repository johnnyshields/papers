/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ClauseThreeSupply
import ForgacsTran.CubicPhaseSign
import ForgacsTran.PencilArcSymmetry
import ForgacsTran.CompositionLinks
import ForgacsTran.CompositionLinksRhoOne
import ForgacsTran.PhaseSupplyUniform

/-!
# `thm:main` clause 3 at an admissible pencil, with nothing assumed

`MainAdmissible` closes clauses 1 and 2 at all four corners of the admissible class.
Clause 3 is the third, and it differs from clause 2 in one respect only: the defect
constants must be fixed before the numerator.  `PhaseSupplyUniform` produces the phase
supply in exactly that order, and `ClauseThreeSupply.exists_interiorZeros_of_ftPhaseSupply`
turns it into the count `eq:angular-distinct-lower` states, so the four theorems below
carry no analytic hypothesis: their binders are the pencil's zeros, its leading constant,
the exponent, the multiplicity of the smallest zero, and the numerator's own two
conditions.

**What the statement makes checkable.**  `hcol`, `κ_0`, `κ_1` are bound by one existential
standing ahead of `∀ N`, so `defectC₀ hcol κ_0` and `defectC₁ κ_1` cannot see the
numerator; `M₀` is bound after `N`, which is where `subsec:proof` puts the threshold.  A
constant that had moved with the numerator would have to appear as a binder, and there
would be nothing to bind it to.

**The reduced weight is where the numerator enters.**  `deg B_N` of
`eq:canonical-Laurent-factorization` is the only numerator-dependent quantity in the bound,
and `lem:laurent-reduction`'s two conditions on `B_N` — real coefficients and `B_N(0) ≠ 0` —
are what the supply is quantified over, so the instantiation is immediate.

Sorry-free.

## Main statements

* `clauseThree_admissible` — `ρ ≥ 2`, `2 ≤ r`.
* `clauseThree_admissible_one` — `ρ ≥ 2`, `r = 1`.
* `clauseThree_admissible_rho_one` — `ρ = 1`, `2 ≤ r`.
* `clauseThree_admissible_rho_one_one` — `ρ = 1`, `r = 1`.
* `clauseThree_numUniform_admissible` and its three siblings — the same four corners read at
  the real numerator, where the uniformity is the manuscript's own
  `PhaseVariation.NumeratorUniform` rather than an unfolded copy of it, and the clause is
  carried all the way to the `exceptionalRoots` bound `thm:main` states.

`DominanceCellPartition.ft_dominance_cell_of_admissible` exhausts the admissible class by
those four corners.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `thm:main` clause 3,
`prop:angular-discrepancy`, `eq:angular-distinct-lower`, `lem:laurent-reduction`,
`eq:canonical-Laurent-factorization`.

## Tags

main theorem, clause three, admissible pencil, numerator uniform
-/

namespace ForgacsTran

open Polynomial Set Real

variable {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

/-- **`thm:main` clause 3 at an admissible pencil with `2 ≤ r` and a repeated smallest
zero.**  One triple `(h, κ_0, κ_1)`, fixed by the pencil, bounds the defect of every
proper numerator: the coefficient polynomial has at least
`M/r - ⌈C_0 + C_1\deg B_N⌉` distinct zeros in the angular window, and the `ℕ`-valued
defect is `≤ C_0' + C_1'\deg B_N` at constants that do not see `N`. -/
theorem clauseThree_admissible (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      (∃ C₀ C₁ : ℕ, ∀ N : (ℂ[X])[X],
        ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
            * ((laurentWeight (ftRootPoly c a) r N).natDegree : ℝ)⌉₊
          ≤ C₀ + C₁ * (laurentWeight (ftRootPoly c a) r N).natDegree) ∧
      ∀ N : (ℂ[X])[X], N ≠ 0 → (∀ β, HasRealCoeffs (N.coeff β)) →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPoly c a).natDegree r : ℕ) : WithBot ℕ)) →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / r - ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
              * ((laurentWeight (ftRootPoly c a) r N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, (ftCoeffPoly (ftRootPoly c a)
              (laurentWeight (ftRootPoly c a) r N) r M).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLower a c r (n - 1)) 0 (π / r)) := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hQ0 : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  obtain ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, hs⟩ :=
    ft_ftPhaseSupply_uniform (ρ := ρ) (x₁ := x₁) hn2 ha hc hr hx₁ hmin hcard hρ
  refine ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁,
    ⟨⌈defectC₀ hcol κ₀⌉₊, ⌈defectC₁ κ₁⌉₊, fun N => ceil_affine_le _ _ _⟩,
    fun N hN hNr hproper => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hs (laurentWeight (ftRootPoly c a) r N)
    (hasRealCoeffs_laurentWeight hr1 hQ0 (hasRealCoeffs_ftRootPoly c a) hN hNr hproper)
    (eval_laurentWeight_zero_ne_zero (ftRootPoly c a) hr1 hQ0 hN hproper)
  refine ⟨M₀, fun M hM _ => ?_⟩
  exact exists_interiorZeros_of_ftPhaseSupply hr1 hhcol hκ₀ hκ₁
    (strictMonoOn_ftBranchZLower_Ioo hn ha hc hr1 hnr)
    (continuousOn_ftBranchZLower_Ioo hn ha hr1 hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ) (hM₀ M hM)

/-- **`thm:main` clause 3 at `r = 1`, repeated smallest zero.**  `3 ≤ n` is the
`(deg Q, r) ≠ (2,1)` exclusion the `r = 1` dominance corner carries. -/
theorem clauseThree_admissible_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      (∃ C₀ C₁ : ℕ, ∀ N : (ℂ[X])[X],
        ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
            * ((laurentWeight (ftRootPoly c a) 1 N).natDegree : ℝ)⌉₊
          ≤ C₀ + C₁ * (laurentWeight (ftRootPoly c a) 1 N).natDegree) ∧
      ∀ N : (ℂ[X])[X], N ≠ 0 → (∀ β, HasRealCoeffs (N.coeff β)) →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPoly c a).natDegree 1 : ℕ) : WithBot ℕ)) →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / 1 - ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
              * ((laurentWeight (ftRootPoly c a) 1 N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, (ftCoeffPoly (ftRootPoly c a)
              (laurentWeight (ftRootPoly c a) 1 N) 1 M).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLower a c 1 (n - 1)) 0
            (π / ((1 : ℕ) : ℝ))) := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  have hQ0 : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  obtain ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, hs⟩ :=
    ft_ftPhaseSupply_uniform_one (ρ := ρ) (x₁ := x₁) hn3 ha hc hx₁ hmin hcard hρ
  refine ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁,
    ⟨⌈defectC₀ hcol κ₀⌉₊, ⌈defectC₁ κ₁⌉₊, fun N => ceil_affine_le _ _ _⟩,
    fun N hN hNr hproper => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hs (laurentWeight (ftRootPoly c a) 1 N)
    (hasRealCoeffs_laurentWeight le_rfl hQ0 (hasRealCoeffs_ftRootPoly c a) hN hNr hproper)
    (eval_laurentWeight_zero_ne_zero (ftRootPoly c a) le_rfl hQ0 hN hproper)
  refine ⟨M₀, fun M hM _ => ?_⟩
  exact exists_interiorZeros_of_ftPhaseSupply le_rfl hhcol hκ₀ hκ₁
    (strictMonoOn_ftBranchZLower_Ioo hn ha hc le_rfl hnr)
    (continuousOn_ftBranchZLower_Ioo hn ha le_rfl hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ) (hM₀ M hM)

/-- **`thm:main` clause 3 at a SIMPLE smallest zero, `2 ≤ r`.**  The branch's lower
endpoint is a critical point inside the first gap rather than the smallest zero, so it is
produced by the pencil and stands existentially beside the constants — no hypothesis names
it either. -/
theorem clauseThree_admissible_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta hcol κ₀ κ₁ : ℝ, 0 < ta ∧ 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      (∃ C₀ C₁ : ℕ, ∀ N : (ℂ[X])[X],
        ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
            * ((laurentWeight (ftRootPoly c a) r N).natDegree : ℝ)⌉₊
          ≤ C₀ + C₁ * (laurentWeight (ftRootPoly c a) r N).natDegree) ∧
      ∀ N : (ℂ[X])[X], N ≠ 0 → (∀ β, HasRealCoeffs (N.coeff β)) →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPoly c a).natDegree r : ℕ) : WithBot ℕ)) →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / r - ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
              * ((laurentWeight (ftRootPoly c a) r N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, (ftCoeffPoly (ftRootPoly c a)
              (laurentWeight (ftRootPoly c a) r N) r M).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLowerAt a c r (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ r)) 0 (π / r)) := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hQ0 : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  obtain ⟨ta, hcol, κ₀, κ₁, hta, hhcol, hκ₀, hκ₁, hs⟩ :=
    ft_ftPhaseSupply_uniform_rho_one hn2 ha hc hr hmin hsim
  refine ⟨ta, hcol, κ₀, κ₁, hta, hhcol, hκ₀, hκ₁,
    ⟨⌈defectC₀ hcol κ₀⌉₊, ⌈defectC₁ κ₁⌉₊, fun N => ceil_affine_le _ _ _⟩,
    fun N hN hNr hproper => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hs (laurentWeight (ftRootPoly c a) r N)
    (hasRealCoeffs_laurentWeight hr1 hQ0 (hasRealCoeffs_ftRootPoly c a) hN hNr hproper)
    (eval_laurentWeight_zero_ne_zero (ftRootPoly c a) hr1 hQ0 hN hproper)
  refine ⟨M₀, fun M hM _ => ?_⟩
  exact exists_interiorZeros_of_ftPhaseSupply hr1 hhcol hκ₀ hκ₁
    (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc hr1 hnr)
    (continuousOn_ftBranchZLowerAt_Ioo hn ha hr1 hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ) (hM₀ M hM)

/-- **`thm:main` clause 3 at a SIMPLE smallest zero, `r = 1`** — the last of the four
corners. -/
theorem clauseThree_admissible_rho_one_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta hcol κ₀ κ₁ : ℝ, 0 < ta ∧ 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      (∃ C₀ C₁ : ℕ, ∀ N : (ℂ[X])[X],
        ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
            * ((laurentWeight (ftRootPoly c a) 1 N).natDegree : ℝ)⌉₊
          ≤ C₀ + C₁ * (laurentWeight (ftRootPoly c a) 1 N).natDegree) ∧
      ∀ N : (ℂ[X])[X], N ≠ 0 → (∀ β, HasRealCoeffs (N.coeff β)) →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPoly c a).natDegree 1 : ℕ) : WithBot ℕ)) →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / 1 - ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
              * ((laurentWeight (ftRootPoly c a) 1 N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, (ftCoeffPoly (ftRootPoly c a)
              (laurentWeight (ftRootPoly c a) 1 N) 1 M).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLowerAt a c 1 (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) 0 (π / ((1 : ℕ) : ℝ))) := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  have hQ0 : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  obtain ⟨ta, hcol, κ₀, κ₁, hta, hhcol, hκ₀, hκ₁, hs⟩ :=
    ft_ftPhaseSupply_uniform_rho_one_one hn3 ha hc hmin hsim
  refine ⟨ta, hcol, κ₀, κ₁, hta, hhcol, hκ₀, hκ₁,
    ⟨⌈defectC₀ hcol κ₀⌉₊, ⌈defectC₁ κ₁⌉₊, fun N => ceil_affine_le _ _ _⟩,
    fun N hN hNr hproper => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hs (laurentWeight (ftRootPoly c a) 1 N)
    (hasRealCoeffs_laurentWeight le_rfl hQ0 (hasRealCoeffs_ftRootPoly c a) hN hNr hproper)
    (eval_laurentWeight_zero_ne_zero (ftRootPoly c a) le_rfl hQ0 hN hproper)
  refine ⟨M₀, fun M hM _ => ?_⟩
  exact exists_interiorZeros_of_ftPhaseSupply le_rfl hhcol hκ₀ hκ₁
    (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc le_rfl hnr)
    (continuousOn_ftBranchZLowerAt_Ioo hn ha le_rfl hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ) (hM₀ M hM)

/-! ### The same clause at the REAL numerator, carrying `NumeratorUniform`

`PhaseVariation.NumeratorUniform` is typed at `Q : Polynomial ℝ` and `N : (ℝ[X])[X]`, which
is the manuscript's own setting — the numerators are real bivariate polynomials.  The four
theorems above state the uniformity by hand because they run at the complexified reduced
weight, where the predicate does not typecheck.

Reading the pencil as `ftRootPolyReal c a` removes that.  The reduced weight is then computed
over `ℝ` and complexified afterwards, and nothing has to be known about `laurentWeight`
commuting with the coefficient map: the supply producers accept **any** `B : ℂ[X]` that is
real and nonvanishing at the origin, and the complexification of `B_N` is one.  So
`ClauseThreeSupply.clauseThree_of_ftPhaseSupply_of_admissible` applies directly, and its
conclusion is the pair `ClauseThreeDefect.clauseThree_exceptionalRoots_of_ne_zero` consumes.
-/

/-- `Q(0) = c\prod_k \tau_k \ne 0` over `ℝ`, which is what the Laurent reduction asks of the
pencil.  The complex form is `ftRootPoly_coeff_zero_ne_zero`. -/
theorem ftRootPolyReal_coeff_zero_ne_zero {c : ℝ} (hc : c ≠ 0) (ha : ∀ k, 0 < a k) :
    (ftRootPolyReal c a).coeff 0 ≠ 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_ftRootPolyReal]
  refine mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun k _ => ?_)
  have := ha k
  linarith

/-- **The complexified reduced weight is an admissible weight.**  Real coefficients because
it is the image of a real polynomial, and nonvanishing at the origin because
`eq:canonical-Laurent-factorization` gives that over `ℝ` and the coefficient map is
injective. -/
theorem admissible_map_laurentWeight {Q : Polynomial ℝ} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) {N : Polynomial (Polynomial ℝ)} (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) :
    HasRealCoeffs ((laurentWeight Q r N).map (algebraMap ℝ ℂ)) ∧
      ((laurentWeight Q r N).map (algebraMap ℝ ℂ)).eval 0 ≠ 0 := by
  refine ⟨hasRealCoeffs_map_ofReal _, ?_⟩
  have hval := eval_map_ofReal (P := laurentWeight Q r N) (x := 0)
  rw [Complex.ofReal_zero] at hval
  rw [hval]
  exact Complex.ofReal_ne_zero.2 (eval_laurentWeight_zero_ne_zero Q hr hQ0 hN hproper)

/-- **`thm:main` clause 3 at the real numerator, `ρ ≥ 2`, `2 ≤ r`.**  Three statements in one:
the uniformity is `PhaseVariation.NumeratorUniform` itself, the interior count is
`eq:angular-distinct-lower`, and the last conjunct is the manuscript's `exceptionalRoots`
form of the clause.  The three constants, the real coefficient family `P_{N,M}`, and the
two defect constants all stand ahead of `∀ N`; only the onset is bound after it. -/
theorem clauseThree_numUniform_admissible (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ (hcol κ₀ κ₁ : ℝ) (Pof : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℝ),
      0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      (∀ N M, (Pof N M).map (algebraMap ℝ ℂ)
        = ftCoeffPoly (ftRootPoly c a)
            ((laurentWeight (ftRootPolyReal c a) r N).map (algebraMap ℝ ℂ)) r M) ∧
      NumeratorUniform (ftRootPolyReal c a) r
        (fun N => ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
          * ((laurentWeight (ftRootPolyReal c a) r N).natDegree : ℝ)⌉₊) ∧
      (∀ N : Polynomial (Polynomial ℝ), N ≠ 0 →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPolyReal c a).natDegree r : ℕ) : WithBot ℕ)) →
        ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / r - ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
            * ((laurentWeight (ftRootPolyReal c a) r N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, ((Pof N M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLower a c r (n - 1)) 0 (π / r))) ∧
      ∃ C₀ C₁ : ℕ, ∀ N : Polynomial (Polynomial ℝ), N ≠ 0 →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPolyReal c a).natDegree r : ℕ) : WithBot ℕ)) →
        ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
          (exceptionalRoots ((Pof N m).map (algebraMap ℝ ℂ))
              (ftWindow (ftBranchZLower a c r (n - 1)) 0 (π / r))).card
            ≤ C₀ + C₁ * (laurentWeight (ftRootPolyReal c a) r N).natDegree := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hQ0R : (ftRootPolyReal c a).coeff 0 ≠ 0 := ftRootPolyReal_coeff_zero_ne_zero hc.ne' ha
  have hQ0C : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  choose Pof hPof using fun N : Polynomial (Polynomial ℝ) =>
    exists_real_ftCoeffPoly_family_of_real (Q := ftRootPoly c a)
      (B := (laurentWeight (ftRootPolyReal c a) r N).map (algebraMap ℝ ℂ))
      (hasRealCoeffs_ftRootPoly c a) (hasRealCoeffs_map_ofReal _) r
  obtain ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, hs⟩ :=
    ft_ftPhaseSupply_uniform (ρ := ρ) (x₁ := x₁) hn2 ha hc hr hx₁ hmin hcard hρ
  have hsup : ∀ N : Polynomial (Polynomial ℝ),
      (N ≠ 0 ∧ ∀ β, (N.coeff β).degree
        < ((max (ftRootPolyReal c a).natDegree r : ℕ) : WithBot ℕ)) →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply (ftRootPoly c a)
          ((laurentWeight (ftRootPolyReal c a) r N).map (algebraMap ℝ ℂ)) r
          (ftBranchZLower a c r (n - 1)) (ftTauArc a r (n - 1) x₁) hcol κ₀ κ₁ M :=
    fun N hN => hs _ (admissible_map_laurentWeight hr1 hQ0R hN.1 hN.2).1
      (admissible_map_laurentWeight hr1 hQ0R hN.1 hN.2).2
  obtain ⟨huni, hmain⟩ :=
    clauseThree_of_ftPhaseSupply_of_admissible (ftRootPolyReal c a) r hr1 hhcol hκ₀ hκ₁
      (strictMonoOn_ftBranchZLower_Ioo hn ha hc hr1 hnr)
      (continuousOn_ftBranchZLower_Ioo hn ha hr1 hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
      (Bof := fun N => (laurentWeight (ftRootPolyReal c a) r N).map (algebraMap ℝ ℂ))
      (Pof := Pof) (fun _ _ => rfl) (fun N M _ => hPof N M) hsup
  obtain ⟨D₀, D₁, hD⟩ :=
    clauseThree_exceptionalRoots_of_ftPhaseSupply_of_admissible (ftRootPolyReal c a) r
      hr1 hQ0C hhcol hκ₀ hκ₁
      (strictMonoOn_ftBranchZLower_Ioo hn ha hc hr1 hnr)
      (continuousOn_ftBranchZLower_Ioo hn ha hr1 hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
      (Bof := fun N => (laurentWeight (ftRootPolyReal c a) r N).map (algebraMap ℝ ℂ))
      (Pof := Pof) (fun _ _ => rfl) (fun N M _ => hPof N M) hsup
  exact ⟨hcol, κ₀, κ₁, Pof, hhcol, hκ₀, hκ₁, hPof, huni,
    fun N hN hproper => hmain N ⟨hN, hproper⟩,
    D₀, D₁, fun N hN hproper => hD N ⟨hN, hproper⟩⟩

/-- **`thm:main` clause 3 at the real numerator, `ρ ≥ 2`, `r = 1`.**  Three statements in one:
the uniformity is `PhaseVariation.NumeratorUniform` itself, the interior count is
`eq:angular-distinct-lower`, and the last conjunct is the manuscript's `exceptionalRoots`
form of the clause.  The three constants, the real coefficient family `P_{N,M}`, and the
two defect constants all stand ahead of `∀ N`; only the onset is bound after it. -/
theorem clauseThree_numUniform_admissible_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ (hcol κ₀ κ₁ : ℝ) (Pof : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℝ),
      0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      (∀ N M, (Pof N M).map (algebraMap ℝ ℂ)
        = ftCoeffPoly (ftRootPoly c a)
            ((laurentWeight (ftRootPolyReal c a) 1 N).map (algebraMap ℝ ℂ)) 1 M) ∧
      NumeratorUniform (ftRootPolyReal c a) 1
        (fun N => ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
          * ((laurentWeight (ftRootPolyReal c a) 1 N).natDegree : ℝ)⌉₊) ∧
      (∀ N : Polynomial (Polynomial ℝ), N ≠ 0 →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPolyReal c a).natDegree 1 : ℕ) : WithBot ℕ)) →
        ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / 1 - ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
            * ((laurentWeight (ftRootPolyReal c a) 1 N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, ((Pof N M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLower a c 1 (n - 1)) 0 (π / ((1 : ℕ) : ℝ)))) ∧
      ∃ C₀ C₁ : ℕ, ∀ N : Polynomial (Polynomial ℝ), N ≠ 0 →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPolyReal c a).natDegree 1 : ℕ) : WithBot ℕ)) →
        ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
          (exceptionalRoots ((Pof N m).map (algebraMap ℝ ℂ))
              (ftWindow (ftBranchZLower a c 1 (n - 1)) 0 (π / ((1 : ℕ) : ℝ)))).card
            ≤ C₀ + C₁ * (laurentWeight (ftRootPolyReal c a) 1 N).natDegree := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  have hQ0R : (ftRootPolyReal c a).coeff 0 ≠ 0 := ftRootPolyReal_coeff_zero_ne_zero hc.ne' ha
  have hQ0C : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  choose Pof hPof using fun N : Polynomial (Polynomial ℝ) =>
    exists_real_ftCoeffPoly_family_of_real (Q := ftRootPoly c a)
      (B := (laurentWeight (ftRootPolyReal c a) 1 N).map (algebraMap ℝ ℂ))
      (hasRealCoeffs_ftRootPoly c a) (hasRealCoeffs_map_ofReal _) 1
  obtain ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, hs⟩ :=
    ft_ftPhaseSupply_uniform_one (ρ := ρ) (x₁ := x₁) hn3 ha hc hx₁ hmin hcard hρ
  have hsup : ∀ N : Polynomial (Polynomial ℝ),
      (N ≠ 0 ∧ ∀ β, (N.coeff β).degree
        < ((max (ftRootPolyReal c a).natDegree 1 : ℕ) : WithBot ℕ)) →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply (ftRootPoly c a)
          ((laurentWeight (ftRootPolyReal c a) 1 N).map (algebraMap ℝ ℂ)) 1
          (ftBranchZLower a c 1 (n - 1)) (ftTauArc a 1 (n - 1) x₁) hcol κ₀ κ₁ M :=
    fun N hN => hs _ (admissible_map_laurentWeight le_rfl hQ0R hN.1 hN.2).1
      (admissible_map_laurentWeight le_rfl hQ0R hN.1 hN.2).2
  obtain ⟨huni, hmain⟩ :=
    clauseThree_of_ftPhaseSupply_of_admissible (ftRootPolyReal c a) 1 le_rfl hhcol hκ₀ hκ₁
      (strictMonoOn_ftBranchZLower_Ioo hn ha hc le_rfl hnr)
      (continuousOn_ftBranchZLower_Ioo hn ha le_rfl hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
      (Bof := fun N => (laurentWeight (ftRootPolyReal c a) 1 N).map (algebraMap ℝ ℂ))
      (Pof := Pof) (fun _ _ => rfl) (fun N M _ => hPof N M) hsup
  obtain ⟨D₀, D₁, hD⟩ :=
    clauseThree_exceptionalRoots_of_ftPhaseSupply_of_admissible (ftRootPolyReal c a) 1
      le_rfl hQ0C hhcol hκ₀ hκ₁
      (strictMonoOn_ftBranchZLower_Ioo hn ha hc le_rfl hnr)
      (continuousOn_ftBranchZLower_Ioo hn ha le_rfl hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
      (Bof := fun N => (laurentWeight (ftRootPolyReal c a) 1 N).map (algebraMap ℝ ℂ))
      (Pof := Pof) (fun _ _ => rfl) (fun N M _ => hPof N M) hsup
  exact ⟨hcol, κ₀, κ₁, Pof, hhcol, hκ₀, hκ₁, hPof, huni,
    fun N hN hproper => hmain N ⟨hN, hproper⟩,
    D₀, D₁, fun N hN hproper => hD N ⟨hN, hproper⟩⟩

/-- **`thm:main` clause 3 at the real numerator, a SIMPLE smallest zero, `2 ≤ r`.**
Three statements in one: the uniformity is `PhaseVariation.NumeratorUniform` itself, the
interior count is `eq:angular-distinct-lower`, and the last conjunct is the manuscript's
`exceptionalRoots` form of the clause.  The three constants, the real coefficient family
`P_{N,M}`, and the two defect constants all stand ahead of `∀ N`; only the onset is bound
after it. -/
theorem clauseThree_numUniform_admissible_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 2 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ (ta hcol κ₀ κ₁ : ℝ) (Pof : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℝ),
      0 < ta ∧ 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      (∀ N M, (Pof N M).map (algebraMap ℝ ℂ)
        = ftCoeffPoly (ftRootPoly c a)
            ((laurentWeight (ftRootPolyReal c a) r N).map (algebraMap ℝ ℂ)) r M) ∧
      NumeratorUniform (ftRootPolyReal c a) r
        (fun N => ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
          * ((laurentWeight (ftRootPolyReal c a) r N).natDegree : ℝ)⌉₊) ∧
      (∀ N : Polynomial (Polynomial ℝ), N ≠ 0 →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPolyReal c a).natDegree r : ℕ) : WithBot ℕ)) →
        ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / r - ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
            * ((laurentWeight (ftRootPolyReal c a) r N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, ((Pof N M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLowerAt a c r (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ r)) 0 (π / r))) ∧
      ∃ C₀ C₁ : ℕ, ∀ N : Polynomial (Polynomial ℝ), N ≠ 0 →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPolyReal c a).natDegree r : ℕ) : WithBot ℕ)) →
        ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
          (exceptionalRoots ((Pof N m).map (algebraMap ℝ ℂ))
              (ftWindow (ftBranchZLowerAt a c r (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ r)) 0 (π / r))).card
            ≤ C₀ + C₁ * (laurentWeight (ftRootPolyReal c a) r N).natDegree := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hQ0R : (ftRootPolyReal c a).coeff 0 ≠ 0 := ftRootPolyReal_coeff_zero_ne_zero hc.ne' ha
  have hQ0C : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  choose Pof hPof using fun N : Polynomial (Polynomial ℝ) =>
    exists_real_ftCoeffPoly_family_of_real (Q := ftRootPoly c a)
      (B := (laurentWeight (ftRootPolyReal c a) r N).map (algebraMap ℝ ℂ))
      (hasRealCoeffs_ftRootPoly c a) (hasRealCoeffs_map_ofReal _) r
  obtain ⟨ta, hcol, κ₀, κ₁, hta, hhcol, hκ₀, hκ₁, hs⟩ :=
    ft_ftPhaseSupply_uniform_rho_one hn2 ha hc hr hmin hsim
  have hsup : ∀ N : Polynomial (Polynomial ℝ),
      (N ≠ 0 ∧ ∀ β, (N.coeff β).degree
        < ((max (ftRootPolyReal c a).natDegree r : ℕ) : WithBot ℕ)) →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply (ftRootPoly c a)
          ((laurentWeight (ftRootPolyReal c a) r N).map (algebraMap ℝ ℂ)) r
          (ftBranchZLowerAt a c r (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ r)) (ftTauArc a r (n - 1) ta) hcol κ₀ κ₁ M :=
    fun N hN => hs _ (admissible_map_laurentWeight hr1 hQ0R hN.1 hN.2).1
      (admissible_map_laurentWeight hr1 hQ0R hN.1 hN.2).2
  obtain ⟨huni, hmain⟩ :=
    clauseThree_of_ftPhaseSupply_of_admissible (ftRootPolyReal c a) r hr1 hhcol hκ₀ hκ₁
      (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc hr1 hnr)
      (continuousOn_ftBranchZLowerAt_Ioo hn ha hr1 hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
      (Bof := fun N => (laurentWeight (ftRootPolyReal c a) r N).map (algebraMap ℝ ℂ))
      (Pof := Pof) (fun _ _ => rfl) (fun N M _ => hPof N M) hsup
  obtain ⟨D₀, D₁, hD⟩ :=
    clauseThree_exceptionalRoots_of_ftPhaseSupply_of_admissible (ftRootPolyReal c a) r
      hr1 hQ0C hhcol hκ₀ hκ₁
      (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc hr1 hnr)
      (continuousOn_ftBranchZLowerAt_Ioo hn ha hr1 hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
      (Bof := fun N => (laurentWeight (ftRootPolyReal c a) r N).map (algebraMap ℝ ℂ))
      (Pof := Pof) (fun _ _ => rfl) (fun N M _ => hPof N M) hsup
  exact ⟨ta, hcol, κ₀, κ₁, Pof, hta, hhcol, hκ₀, hκ₁, hPof, huni,
    fun N hN hproper => hmain N ⟨hN, hproper⟩,
    D₀, D₁, fun N hN hproper => hD N ⟨hN, hproper⟩⟩

/-- **`thm:main` clause 3 at the real numerator, a SIMPLE smallest zero, `r = 1`.**
Three statements in one: the uniformity is `PhaseVariation.NumeratorUniform` itself, the
interior count is `eq:angular-distinct-lower`, and the last conjunct is the manuscript's
`exceptionalRoots` form of the clause.  The three constants, the real coefficient family
`P_{N,M}`, and the two defect constants all stand ahead of `∀ N`; only the onset is bound
after it. -/
theorem clauseThree_numUniform_admissible_rho_one_one (hn3 : 3 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ (ta hcol κ₀ κ₁ : ℝ) (Pof : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℝ),
      0 < ta ∧ 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      (∀ N M, (Pof N M).map (algebraMap ℝ ℂ)
        = ftCoeffPoly (ftRootPoly c a)
            ((laurentWeight (ftRootPolyReal c a) 1 N).map (algebraMap ℝ ℂ)) 1 M) ∧
      NumeratorUniform (ftRootPolyReal c a) 1
        (fun N => ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
          * ((laurentWeight (ftRootPolyReal c a) 1 N).natDegree : ℝ)⌉₊) ∧
      (∀ N : Polynomial (Polynomial ℝ), N ≠ 0 →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPolyReal c a).natDegree 1 : ℕ) : WithBot ℕ)) →
        ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / 1 - ⌈defectC₀ hcol κ₀ + defectC₁ κ₁
            * ((laurentWeight (ftRootPolyReal c a) 1 N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, ((Pof N M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLowerAt a c 1 (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) 0 (π / ((1 : ℕ) : ℝ)))) ∧
      ∃ C₀ C₁ : ℕ, ∀ N : Polynomial (Polynomial ℝ), N ≠ 0 →
        (∀ β, (N.coeff β).degree
          < ((max (ftRootPolyReal c a).natDegree 1 : ℕ) : WithBot ℕ)) →
        ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
          (exceptionalRoots ((Pof N m).map (algebraMap ℝ ℂ))
              (ftWindow (ftBranchZLowerAt a c 1 (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) 0 (π / ((1 : ℕ) : ℝ)))).card
            ≤ C₀ + C₁ * (laurentWeight (ftRootPolyReal c a) 1 N).natDegree := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  have hQ0R : (ftRootPolyReal c a).coeff 0 ≠ 0 := ftRootPolyReal_coeff_zero_ne_zero hc.ne' ha
  have hQ0C : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  choose Pof hPof using fun N : Polynomial (Polynomial ℝ) =>
    exists_real_ftCoeffPoly_family_of_real (Q := ftRootPoly c a)
      (B := (laurentWeight (ftRootPolyReal c a) 1 N).map (algebraMap ℝ ℂ))
      (hasRealCoeffs_ftRootPoly c a) (hasRealCoeffs_map_ofReal _) 1
  obtain ⟨ta, hcol, κ₀, κ₁, hta, hhcol, hκ₀, hκ₁, hs⟩ :=
    ft_ftPhaseSupply_uniform_rho_one_one hn3 ha hc hmin hsim
  have hsup : ∀ N : Polynomial (Polynomial ℝ),
      (N ≠ 0 ∧ ∀ β, (N.coeff β).degree
        < ((max (ftRootPolyReal c a).natDegree 1 : ℕ) : WithBot ℕ)) →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply (ftRootPoly c a)
          ((laurentWeight (ftRootPolyReal c a) 1 N).map (algebraMap ℝ ℂ)) 1
          (ftBranchZLowerAt a c 1 (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) (ftTauArc a 1 (n - 1) ta) hcol κ₀ κ₁ M :=
    fun N hN => hs _ (admissible_map_laurentWeight le_rfl hQ0R hN.1 hN.2).1
      (admissible_map_laurentWeight le_rfl hQ0R hN.1 hN.2).2
  obtain ⟨huni, hmain⟩ :=
    clauseThree_of_ftPhaseSupply_of_admissible (ftRootPolyReal c a) 1 le_rfl hhcol hκ₀ hκ₁
      (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc le_rfl hnr)
      (continuousOn_ftBranchZLowerAt_Ioo hn ha le_rfl hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
      (Bof := fun N => (laurentWeight (ftRootPolyReal c a) 1 N).map (algebraMap ℝ ℂ))
      (Pof := Pof) (fun _ _ => rfl) (fun N M _ => hPof N M) hsup
  obtain ⟨D₀, D₁, hD⟩ :=
    clauseThree_exceptionalRoots_of_ftPhaseSupply_of_admissible (ftRootPolyReal c a) 1
      le_rfl hQ0C hhcol hκ₀ hκ₁
      (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc le_rfl hnr)
      (continuousOn_ftBranchZLowerAt_Ioo hn ha le_rfl hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
      (Bof := fun N => (laurentWeight (ftRootPolyReal c a) 1 N).map (algebraMap ℝ ℂ))
      (Pof := Pof) (fun _ _ => rfl) (fun N M _ => hPof N M) hsup
  exact ⟨ta, hcol, κ₀, κ₁, Pof, hta, hhcol, hκ₀, hκ₁, hPof, huni,
    fun N hN hproper => hmain N ⟨hN, hproper⟩,
    D₀, D₁, fun N hN hproper => hD N ⟨hN, hproper⟩⟩

end ForgacsTran
