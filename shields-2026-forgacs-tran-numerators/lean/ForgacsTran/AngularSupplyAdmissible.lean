/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.AngularDiscrepancyAdmissible
import ForgacsTran.ConsequencesComposition.AngularSupply

/-!
# `prop:equidistribution` and `cor:angular-rigidity` at an admissible pencil

`ConsequencesComposition.ft_equidistribution_of_discrepancy` and
`ft_angular_clock_of_discrepancy` derive the two zero laws from
`FTAngularDiscrepancy`, and `AngularDiscrepancyAdmissible` proves that discrepancy at an
admissible pencil in each of its four corners.  The eight theorems below run the one into
the other, once per corner per law.

**What this changes.**  Both laws have stood on `FTAngularDiscrepancy` as a hypothesis
somebody hands them.  Composed, they carry no analytic hypothesis at all: the binders are
the pencil's own data — the degree, the positivity of the zeros and of the leading
coefficient, the weight `r`, and the multiplicity of the smallest zero — and the two laws
become statements about `Q + zt^r` rather than about a supply.

The four corners are the producer's: a repeated smallest zero with `2 ≤ r` or with `r = 1`,
and a simple smallest zero with `2 ≤ r` or with `r = 1`.  In the simple corners the branch's
lower endpoint is produced rather than named, so the existential the producer carries is
carried through to the conclusion.

Sorry-free.

## Main statements

* `ft_equidistribution_admissible`, `ft_equidistribution_admissible_one`,
  `ft_equidistribution_admissible_rho_one`, `ft_equidistribution_admissible_rho_one_one` —
  `prop:equidistribution` at the pencil, in the four corners.
* `ft_angular_clock_admissible`, `ft_angular_clock_admissible_one`,
  `ft_angular_clock_admissible_rho_one`, `ft_angular_clock_admissible_rho_one_one` —
  `cor:angular-rigidity` at the pencil, in the same four.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `prop:equidistribution`,
`eq:normalized-angular-discrepancy`, `cor:angular-rigidity`, `eq:angular-clock`, off
`prop:angular-discrepancy` and `eq:angular-discrepancy`.

## Tags

equidistribution, angular clock, admissible pencil, angular discrepancy
-/

namespace ForgacsTran

open Polynomial Set Real

variable {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

open scoped Classical in
/-- **`prop:equidistribution` at an admissible pencil, `2 ≤ r` and a repeated smallest
zero.**  The normalized zero counting measure tracks the uniform angular density to
`O(1/d)`, uniformly over windows, with no analytic hypothesis in sight: the binders are the
pencil's. -/
theorem ft_equidistribution_admissible (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ D₀ D₁ : ℝ, 0 ≤ D₀ ∧ 0 ≤ D₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ M₀ : ℕ, ∀ M d s : ℕ, M₀ ≤ M → 1 ≤ d → M = r * d + s → s < r →
          ∀ α β : ℝ, 0 ≤ α → α < β → β ≤ π / r →
            |(Multiset.card ((ftCoeffPoly (ftRootPoly c a) B r M).roots.filter
                  (· ∈ ftWindow (ftBranchZLower a c r (n - 1)) α β)) : ℝ) / (d : ℝ)
                - (r : ℝ) * (β - α) / π|
              ≤ (D₀ + D₁ * (B.natDegree : ℝ) + 1) / (d : ℝ) :=
  ft_equidistribution_of_discrepancy (le_trans one_le_two hr)
    (ftAngularDiscrepancy_admissible hn2 ha hc hr hx₁ hmin hcard hρ)

open scoped Classical in
/-- **`prop:equidistribution` at an admissible pencil, `r = 1` and a repeated smallest
zero.**  `3 ≤ n` is the `(deg Q, r) ≠ (2,1)` exclusion the `r = 1` corner carries. -/
theorem ft_equidistribution_admissible_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ D₀ D₁ : ℝ, 0 ≤ D₀ ∧ 0 ≤ D₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ M₀ : ℕ, ∀ M d s : ℕ, M₀ ≤ M → 1 ≤ d → M = 1 * d + s → s < 1 →
          ∀ α β : ℝ, 0 ≤ α → α < β → β ≤ π / ((1 : ℕ) : ℝ) →
            |(Multiset.card ((ftCoeffPoly (ftRootPoly c a) B 1 M).roots.filter
                  (· ∈ ftWindow (ftBranchZLower a c 1 (n - 1)) α β)) : ℝ) / (d : ℝ)
                - ((1 : ℕ) : ℝ) * (β - α) / π|
              ≤ (D₀ + D₁ * (B.natDegree : ℝ) + 1) / (d : ℝ) :=
  ft_equidistribution_of_discrepancy le_rfl
    (ftAngularDiscrepancy_admissible_one hn3 ha hc hx₁ hmin hcard hρ)

open scoped Classical in
/-- **`prop:equidistribution` at a SIMPLE smallest zero, `2 ≤ r`.**  The branch's lower
endpoint is a critical point produced by the pencil, so it is bound in the conclusion
rather than named by a hypothesis. -/
theorem ft_equidistribution_admissible_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 2 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, 0 < ta ∧
      ∃ D₀ D₁ : ℝ, 0 ≤ D₀ ∧ 0 ≤ D₁ ∧
        ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
          ∃ M₀ : ℕ, ∀ M d s : ℕ, M₀ ≤ M → 1 ≤ d → M = r * d + s → s < r →
            ∀ α β : ℝ, 0 ≤ α → α < β → β ≤ π / r →
              |(Multiset.card ((ftCoeffPoly (ftRootPoly c a) B r M).roots.filter
                    (· ∈ ftWindow (ftBranchZLowerAt a c r (n - 1)
                      (-((ftRootPolyReal c a).eval ta) / ta ^ r)) α β)) : ℝ) / (d : ℝ)
                  - (r : ℝ) * (β - α) / π|
                ≤ (D₀ + D₁ * (B.natDegree : ℝ) + 1) / (d : ℝ) := by
  obtain ⟨ta, hta, hdisc⟩ := ftAngularDiscrepancy_admissible_rho_one hn2 ha hc hr hmin hsim
  exact ⟨ta, hta, ft_equidistribution_of_discrepancy (le_trans one_le_two hr) hdisc⟩

open scoped Classical in
/-- **`prop:equidistribution` at a SIMPLE smallest zero, `r = 1`** — the last of the four
corners. -/
theorem ft_equidistribution_admissible_rho_one_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, 0 < ta ∧
      ∃ D₀ D₁ : ℝ, 0 ≤ D₀ ∧ 0 ≤ D₁ ∧
        ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
          ∃ M₀ : ℕ, ∀ M d s : ℕ, M₀ ≤ M → 1 ≤ d → M = 1 * d + s → s < 1 →
            ∀ α β : ℝ, 0 ≤ α → α < β → β ≤ π / ((1 : ℕ) : ℝ) →
              |(Multiset.card ((ftCoeffPoly (ftRootPoly c a) B 1 M).roots.filter
                    (· ∈ ftWindow (ftBranchZLowerAt a c 1 (n - 1)
                      (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) α β)) : ℝ) / (d : ℝ)
                  - ((1 : ℕ) : ℝ) * (β - α) / π|
                ≤ (D₀ + D₁ * (B.natDegree : ℝ) + 1) / (d : ℝ) := by
  obtain ⟨ta, hta, hdisc⟩ := ftAngularDiscrepancy_admissible_rho_one_one hn3 ha hc hmin hsim
  exact ⟨ta, hta, ft_equidistribution_of_discrepancy le_rfl hdisc⟩

open scoped Classical in
/-- **`cor:angular-rigidity` at an admissible pencil, `2 ≤ r` and a repeated smallest
zero.**  Every index belonging to a zero of angle `θ` sits within
`π(E₀ + E₁\deg B + 1)/(M+1)` of the uniform clock, at constants fixed by the pencil. -/
theorem ft_angular_clock_admissible (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ, 0 < θ → θ < π / r → ∀ j : ℕ,
            Multiset.card ((ftCoeffPoly (ftRootPoly c a) B r M).roots.filter
              (· ∈ ftWindow (ftBranchZLower a c r (n - 1)) 0 θ)) < j →
            j ≤ Multiset.card ((ftCoeffPoly (ftRootPoly c a) B r M).roots.filter
              (· ∈ ftWindowIoc (ftBranchZLower a c r (n - 1)) 0 θ)) →
            |θ - π * (j : ℝ) / ((M : ℝ) + 1)|
              ≤ π * (E₀ + E₁ * (B.natDegree : ℝ) + 1) / ((M : ℝ) + 1) :=
  ft_angular_clock_of_discrepancy (le_trans one_le_two hr)
    (ftAngularDiscrepancy_admissible hn2 ha hc hr hx₁ hmin hcard hρ)

open scoped Classical in
/-- **`cor:angular-rigidity` at an admissible pencil, `r = 1` and a repeated smallest
zero.** -/
theorem ft_angular_clock_admissible_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ, 0 < θ → θ < π / ((1 : ℕ) : ℝ) → ∀ j : ℕ,
            Multiset.card ((ftCoeffPoly (ftRootPoly c a) B 1 M).roots.filter
              (· ∈ ftWindow (ftBranchZLower a c 1 (n - 1)) 0 θ)) < j →
            j ≤ Multiset.card ((ftCoeffPoly (ftRootPoly c a) B 1 M).roots.filter
              (· ∈ ftWindowIoc (ftBranchZLower a c 1 (n - 1)) 0 θ)) →
            |θ - π * (j : ℝ) / ((M : ℝ) + 1)|
              ≤ π * (E₀ + E₁ * (B.natDegree : ℝ) + 1) / ((M : ℝ) + 1) :=
  ft_angular_clock_of_discrepancy le_rfl
    (ftAngularDiscrepancy_admissible_one hn3 ha hc hx₁ hmin hcard hρ)

open scoped Classical in
/-- **`cor:angular-rigidity` at a SIMPLE smallest zero, `2 ≤ r`.**  The branch endpoint is
produced by the pencil and bound in the conclusion. -/
theorem ft_angular_clock_admissible_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 2 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, 0 < ta ∧
      ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧
        ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
          ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ, 0 < θ → θ < π / r → ∀ j : ℕ,
              Multiset.card ((ftCoeffPoly (ftRootPoly c a) B r M).roots.filter
                (· ∈ ftWindow (ftBranchZLowerAt a c r (n - 1)
                  (-((ftRootPolyReal c a).eval ta) / ta ^ r)) 0 θ)) < j →
              j ≤ Multiset.card ((ftCoeffPoly (ftRootPoly c a) B r M).roots.filter
                (· ∈ ftWindowIoc (ftBranchZLowerAt a c r (n - 1)
                  (-((ftRootPolyReal c a).eval ta) / ta ^ r)) 0 θ)) →
              |θ - π * (j : ℝ) / ((M : ℝ) + 1)|
                ≤ π * (E₀ + E₁ * (B.natDegree : ℝ) + 1) / ((M : ℝ) + 1) := by
  obtain ⟨ta, hta, hdisc⟩ := ftAngularDiscrepancy_admissible_rho_one hn2 ha hc hr hmin hsim
  exact ⟨ta, hta, ft_angular_clock_of_discrepancy (le_trans one_le_two hr) hdisc⟩

open scoped Classical in
/-- **`cor:angular-rigidity` at a SIMPLE smallest zero, `r = 1`** — the last of the four
corners. -/
theorem ft_angular_clock_admissible_rho_one_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, 0 < ta ∧
      ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧
        ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
          ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ, 0 < θ → θ < π / ((1 : ℕ) : ℝ) → ∀ j : ℕ,
              Multiset.card ((ftCoeffPoly (ftRootPoly c a) B 1 M).roots.filter
                (· ∈ ftWindow (ftBranchZLowerAt a c 1 (n - 1)
                  (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) 0 θ)) < j →
              j ≤ Multiset.card ((ftCoeffPoly (ftRootPoly c a) B 1 M).roots.filter
                (· ∈ ftWindowIoc (ftBranchZLowerAt a c 1 (n - 1)
                  (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) 0 θ)) →
              |θ - π * (j : ℝ) / ((M : ℝ) + 1)|
                ≤ π * (E₀ + E₁ * (B.natDegree : ℝ) + 1) / ((M : ℝ) + 1) := by
  obtain ⟨ta, hta, hdisc⟩ := ftAngularDiscrepancy_admissible_rho_one_one hn3 ha hc hmin hsim
  exact ⟨ta, hta, ft_angular_clock_of_discrepancy le_rfl hdisc⟩

end ForgacsTran
