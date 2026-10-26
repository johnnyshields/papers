/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Compositions, cut sets, and coarsening inventories

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, the section
`sec:algebra` (`eq:introG`, `eq:K`, `eq:composition-cuts`).

A composition of weight `n` is represented by its cut set `S ⊆ {1, …, n-1}` (the proper
prefix sums).  The paper's operations on lists of parts are defined and identified with the
cut-set formulas in `SkewRibbonCoarsenings.PartsAndCuts`.  A coarsening retains a subset `T ⊆ S` of
the cuts; `gaps n T` is the multiset of resulting block lengths.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open MvPolynomial

/-- The ring `Λ_ℤ = ℤ[h₁, h₂, …]` of the paper. -/
abbrev Lam : Type := MvPolynomial ℕ+ ℤ

/-- The complete homogeneous generator `h_j`, with the paper's convention `h₀ = 1`. -/
noncomputable def hgen (j : ℕ) : Lam :=
  if hj : 0 < j then MvPolynomial.X ⟨j, hj⟩ else 1

/-- The admissible cut sets of weight `n`: subsets of `{1, …, n-1}`. -/
def IsCutSet (n : ℕ) (S : Finset ℕ) : Prop := S ⊆ Finset.Ioo 0 n

/-- Block lengths of the coarsening of weight `n` that retains exactly the cuts `T`, as a
multiset: each element of `T ∪ {n}` minus its predecessor in `T ∪ {0}`.  For
`0 < t₁ < ⋯ < t_k < n` these are the differences `t₁, t₂ - t₁, …, n - t_k`.  Defined without
sorting so that small instances reduce by `decide`. -/
def gaps (n : ℕ) (T : Finset ℕ) : Multiset ℕ :=
  (insert n T).val.map fun x => x - (T.filter (· < x)).sup id

/-- The coarsening polynomial `G_β = ∑_{ρ ⪰ β} h_{sort ρ}` of `eq:introG`, for the composition
of weight `n` with cut set `S`.  Coarsenings correspond to the subsets `T ⊆ S` of retained
cuts.  The empty composition is weight `0`, `S = ∅`, `G = 1`. -/
noncomputable def G (n : ℕ) (S : Finset ℕ) : Lam :=
  ∑ T ∈ S.powerset, ((gaps n T).map hgen).prod

/-- The coarsening multiplicity `m_β(λ) = [h_λ] G_β` of `eq:introG`, defined by counting the
retained subsets whose block lengths sort to the partition `lam`. -/
def mult (n : ℕ) (S : Finset ℕ) (lam : Multiset ℕ) : ℕ :=
  (S.powerset.filter fun T => gaps n T = lam).card

/-- Inventory equivalence `β ∼ γ`: equal coarsening polynomials. -/
def Equivalent (n : ℕ) (S S' : Finset ℕ) : Prop := G n S = G n S'

/-- The cyclic cut indicator `b : ℤ/n → ℤ` with `b(0) = 0`. -/
def cutInd (n : ℕ) (S : Finset ℕ) (x : ZMod n) : ℤ := if x.val ∈ S then 1 else 0

/-- Reversal `β*`: cuts `x ↦ n - x`. -/
def revCuts (n : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (n - ·)

/-- Cut set of the concatenation `α · β` (weights `n` and `n'`; the seam `n` is a cut). -/
def concatCuts (n : ℕ) (S : Finset ℕ) (S' : Finset ℕ) : Finset ℕ :=
  S ∪ {n} ∪ S'.image (n + ·)

/-- Cut set of the near-concatenation `α ⊙ β` (the two meeting parts merge; no seam cut). -/
def nearCuts (n : ℕ) (S : Finset ℕ) (S' : Finset ℕ) : Finset ℕ :=
  S ∪ S'.image (n + ·)

/-- Cut set of the near-power `ε^{⊙ m}` of a composition of weight `n`; weight `m * n`. -/
def nearPowerCuts (n : ℕ) (S : Finset ℕ) (m : ℕ) : Finset ℕ :=
  (Finset.range m).biUnion fun j => S.image (j * n + ·)

/-- Cut set of the composition product `α ∘ ε` of `eq:composition-cuts`: outer `α` of weight
`m` with cuts `A`, inner `ε` of weight `p` with cuts `E`; weight `m * p`. -/
def compCuts (m : ℕ) (A : Finset ℕ) (p : ℕ) (E : Finset ℕ) : Finset ℕ :=
  A.image (p * ·) ∪ (Finset.range m).biUnion fun j => E.image (j * p + ·)

/-- The substitution homomorphism `Ψ_ε` of `eq:introPsi`, `Ψ_ε(h_j) = G_{ε^{⊙ j}}`, for the
inner composition of weight `n` with cut set `E`. -/
noncomputable def Psi (n : ℕ) (E : Finset ℕ) : Lam →+* Lam :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℤ →+* Lam)
    (fun j : ℕ+ => G ((j : ℕ) * n) (nearPowerCuts n E j))

example : mult 4 {1, 2, 3} {2, 1, 1} = 3 := by decide
example : mult 4 {1, 3} {2, 2} = 0 := by decide
example : mult 4 {1, 2, 3} {1, 1, 1, 1} = 1 := by decide
example : gaps 6 {2, 3} = {2, 1, 3} := by decide
example : mult 6 {2, 3} {2, 1, 3} = 1 := by decide

/-- Sum of the first `j` entries of the list `a` read in the order given by `π`. -/
def partialSum {r : ℕ} (a : Fin r → ℕ) (π : Equiv.Perm (Fin r)) (j : ℕ) : ℕ :=
  ∑ i : Fin r with i.val < j, a (π i)

/-- The labeled count `K_b(a)` of `eq:K`: over all orderings `π` of the labeled list `a`, the
number of orderings all of whose proper partial sums are retained cuts.  Labels distinguish
positions even when their numerical values coincide. -/
def K (S : Finset ℕ) {r : ℕ} (a : Fin r → ℕ) : ℕ :=
  (Finset.univ.filter fun π : Equiv.Perm (Fin r) =>
    ∀ j < r, 0 < j → partialSum a π j ∈ S).card

example : K {1, 2} (fun _ : Fin 3 => 1) = 6 := by decide
example : K {1, 3} ![1, 2, 1] = 2 := by decide

end SkewRibbonCoarsenings
