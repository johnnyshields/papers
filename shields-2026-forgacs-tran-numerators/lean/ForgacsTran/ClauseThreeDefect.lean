/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.ClauseThreeComposition
import ForgacsTran.ClauseThreeWitness
import ForgacsTran.ZeroCount
import ForgacsTran.PhaseVariation
import ForgacsTran.ClauseThreeReduction

/-!
# The defect decomposes: `thm:main` clause 3 in the exceptional-count idiom

`Main.main_bound_interval` proves "at most `Cbulk`", where `Bridge.FTInputs.Cbulk` is a single
opaque `ℕ` supplied per bundle.  That says nothing about how the defect decomposes.  Clause 3
asserts constants `C_0 = C_0(Q,r)` and `C_1 = C_1(Q,r)`, **independent of `N`**, with defect at
most `C_0 + C_1deg B_N`, and that independence is the whole of what separates clause 3 from
clause 2.

`exceptionalRoots_numeratorUniform` is that statement.  The content is the quantifier order and
nothing else: `C₀` and `C₁` are bound **before** `∀ N`, so they cannot see the numerator, while
the onset `m₀` is bound after it, which is what `thm:main` allows when it says the onset in
clause 3 may depend on the numerator.  A statement with `C₀`, `C₁` inside the `∀ N` would be
well-typed, provable, and worthless; that is the failure this file exists to avoid, and the
binder list is where a reader checks it.

The proof is short because the linearity is not proved here — it arrives as
`PhaseVariation.NumeratorUniform`, which `cor:linear-phase-variation` supplies over
`ViewingAngle.viewing_angle_bound` (Radon's bound, proved here rather than cited), and which
`ClauseThreeComposition.clauseThree_of_ftGeometry` produces from the branch geometry.  What
this module adds is the passage from the interior-zero supply to the **exceptional** count,
through `ZeroCount.exceptionalRoots_card_le`, with the defect carried across in decomposed
form.

## Main statements

* `exceptionalRoots_numeratorUniform` — the clause, over an interior-zero supply whose defect
  family is numerator-uniform.
* `clauseThree_exceptionalRoots` — the same, over the conclusion
  `clauseThree_of_ftGeometry` actually reaches, so the two compose without a seam.
* `exceptionalRoots_numeratorUniform_witness` — the hypotheses instantiated, so the statement
  is not vacuous.

## Implementation notes

**Differs from the paper's route.**  `subsec:proof` reads the exceptional bound and the defect
decomposition off one phase count: the count produces `deg P_m - (C_0 + C_1deg B_N)` interior
zeros and the complement is bounded in the same breath.  Here the two are separated — the
interior supply is one hypothesis, `lem:eventual-degree`'s upper half `deg P_m ≤ ⌊
m/r⌋` another, and the counting engine a third — because the defect family has to be
carried in a form (`NumeratorUniform`) whose constants are visible outside the quantifier over
numerators.  The manuscript has no reason to separate them; a Lean statement does, for the
reason in the third paragraph.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `thm:main` clause 3 and
`prop:angular-discrepancy` (`eq:angular-distinct-lower`).

## Tags

defect decomposition, exceptional zero, weight degree
-/

namespace ForgacsTran

open Polynomial LaurentPolynomial

/-! ### The clause -/

/-- **Paper `thm:main` clause 3.**  There are constants `C_0` and `C_1` seeing only `Q` and
`r` such that, for every numerator `N` and every sufficiently large index, the coefficient
polynomial has at most `C_0 + C_1deg B_N` zeros outside the Forgács--Tran interval, counted
with multiplicity.

**The quantifier order is the content.**  `C₀` and `C₁` are bound before `∀ N`; `m₀` after it.
Move the constants inside and the statement becomes clause 2 with extra notation.

Three inputs, and none of them mentions an exceptional count:

* `huni` — the defect family is numerator-uniform (`eq:angular-distinct-lower`'s
  `C_0 + C_1K`), which `cor:linear-phase-variation` supplies;
* `hdeg` — `lem:eventual-degree`'s upper half, `deg P_m ≤ ⌊ m/r⌋`;
* `hsupply` — the interior zeros of `prop:angular-discrepancy`, at least
  `⌊ m/r⌋ - F(N)` of them.

**Containment.**  The conclusion bounds `exceptionalRoots`.  No binder mentions
`exceptionalRoots`; `hsupply` speaks of roots *inside* `S` and says nothing about the
complement, `hdeg` is about `natDegree`, and `huni` is about `ℕ`-valued constants alone.  The
passage from an interior count to an exterior bound is `ZeroCount.exceptionalRoots_card_le`,
which is where it is proved rather than assumed. -/
theorem exceptionalRoots_numeratorUniform
    {Q : Polynomial ℝ} {r : ℕ}
    {P : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℂ} {S : Set ℂ}
    {F : Polynomial (Polynomial ℝ) → ℕ}
    (huni : NumeratorUniform Q r F)
    (hdeg : ∀ N m, (P N m).natDegree ≤ m / r)
    (hsupply : ∀ N, ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∃ Z : Finset ℂ,
      m / r - F N ≤ Z.card ∧
      (∀ w ∈ Z, (P N m).IsRoot w) ∧ (∀ w ∈ Z, w ∈ S)) :
    ∃ C₀ C₁ : ℕ, ∀ N : Polynomial (Polynomial ℝ), ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      P N m ≠ 0 →
        (exceptionalRoots (P N m) S).card
          ≤ C₀ + C₁ * (laurentWeight Q r N).natDegree := by
  obtain ⟨C₀, C₁, hC⟩ := huni
  refine ⟨C₀, C₁, fun N => ?_⟩
  obtain ⟨m₀, hm₀⟩ := hsupply N
  refine ⟨m₀, fun m hm hPne => ?_⟩
  obtain ⟨Z, hcard, hroot, hmem⟩ := hm₀ m hm
  have hZ : (P N m).natDegree - F N ≤ Z.card :=
    le_trans (Nat.sub_le_sub_right (hdeg N m) (F N)) hcard
  exact le_trans (exceptionalRoots_card_le hPne hroot hmem hZ) (hC N)

/-! ### Composed with the branch geometry -/

/-- **Paper `thm:main` clause 3, over what `clauseThree_of_ftGeometry` reaches.**  `hcl` is
that theorem's conclusion type verbatim, so the two compose with no seam: whatever discharges
the branch geometry and `eq:dominance-bound` for clause 3's interior count discharges this.

What is added beyond `hcl` is `hdeg` alone — `lem:eventual-degree`'s upper half — and the
`1 ≤ m` guard `clauseThree` carries is absorbed into the onset. -/
theorem clauseThree_exceptionalRoots
    {Q : Polynomial ℝ} {r : ℕ}
    {Pof : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℝ} {T : Set ℝ}
    {hwin κ₀ κ₁ : ℝ}
    (hdeg : ∀ N m, ((Pof N m).map (algebraMap ℝ ℂ)).natDegree ≤ m / r)
    (hcl : NumeratorUniform Q r
        (fun N => ⌈defectC₀ hwin κ₀
          + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊)
      ∧ ∀ N, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / r - ⌈defectC₀ hwin κ₀
            + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, ((Pof N M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ Complex.ofReal '' T)) :
    ∃ C₀ C₁ : ℕ, ∀ N : Polynomial (Polynomial ℝ), ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      (Pof N m).map (algebraMap ℝ ℂ) ≠ 0 →
        (exceptionalRoots ((Pof N m).map (algebraMap ℝ ℂ)) (Complex.ofReal '' T)).card
          ≤ C₀ + C₁ * (laurentWeight Q r N).natDegree := by
  obtain ⟨huni, hsup⟩ := hcl
  refine exceptionalRoots_numeratorUniform huni hdeg (fun N => ?_)
  obtain ⟨M₀, hM₀⟩ := hsup N
  exact ⟨max M₀ 1, fun m hm =>
    hM₀ m (le_trans (le_max_left _ _) hm) (le_trans (le_max_right _ _) hm)⟩

/-! ### The statement is not vacuous -/

/-- **The hypotheses instantiated.**  A statement of this shape is exactly the kind that can be
well-typed, provable and worthless, so the hypothesis list is exhibited satisfied rather than
argued about.  The family is the Favard witness of `ClauseThreeWitness`, indexed so that its
weight degree **is** `deg B_N` and therefore varies with `N` over every value `deg B_N`
takes; the defect comes out as `4 + 3deg B_N`, with `C_0 = 4` and `C_1 = 3` free of `N`.

**Honest reading.**  This certifies that the hypothesis list of
`exceptionalRoots_numeratorUniform` is consistent and its conclusion non-trivial.  It is not a
model of the paper's situation: `P N` here is the Favard sequence at a shifted index, not the
coefficient sequence of `N`, and nothing ties the two — the statement does not ask it to, since
that tie is the caller's to supply through `hsupply`. -/
theorem exceptionalRoots_numeratorUniform_witness (Q : Polynomial ℝ) :
    ∃ C₀ C₁ : ℕ, ∀ N : Polynomial (Polynomial ℝ), ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      (witPpow ((laurentWeight Q 1 N).natDegree) m).map (algebraMap ℝ ℂ) ≠ 0 →
        (exceptionalRoots
            ((witPpow ((laurentWeight Q 1 N).natDegree) m).map (algebraMap ℝ ℂ))
            (ftInterval 1 7)).card
          ≤ C₀ + C₁ * (laurentWeight Q 1 N).natDegree := by
  refine exceptionalRoots_numeratorUniform (Q := Q) (r := 1)
    (F := fun N => 4 + 3 * (laurentWeight Q 1 N).natDegree)
    ⟨4, 3, fun N => le_rfl⟩ (fun N m => ?_) (fun N => ?_)
  · rw [witPpow_natDegree, Nat.div_one]
    exact Nat.sub_le _ _
  · refine ⟨max 1 ((laurentWeight Q 1 N).natDegree), fun m hm => ?_⟩
    have hM1 : 1 ≤ m := le_trans (le_max_left _ _) hm
    have hkm : (laurentWeight Q 1 N).natDegree ≤ m := le_trans (le_max_right _ _) hm
    obtain ⟨Z, hcard, hroot, hmem⟩ := witness_clauseThree_uniform hkm hM1
    exact ⟨Z, by rwa [Nat.div_one], hroot, hmem⟩


/-! ### The `C₁` term is not idle: `deg B_N` is unbounded for a fixed pencil -/


/-! ### The nonvanishing, discharged

`thm:main` clause 2(i) — `P_m ≠ 0` for all large `m` — is not a missing primitive.  Its two
halves are both proved: `EventualDegree.eventual_ne_zero` gives it for the **reduced** sequence
out of the top coefficient (`lem:eventual-degree`'s attainment argument), and
`LaurentReduction.reduction_coeff_eventually` identifies `P_m` with that sequence at the
shifted index `m - λ_N` (`eq:reduction-coeff`).  What was missing is the composition, and
the only care it needs is the index shift: the two thresholds live in different variables and
`Int.toNat` sends a negative value silently to `0`. -/


/-- **Paper `thm:main` clause 3, with clause 2(i) discharged rather than guarded.**  The
`P_m ≠ 0` side condition of `exceptionalRoots_numeratorUniform` is replaced by the eventual
nonvanishing, which `eventual_coeffPoly_ne_zero` supplies from the `sec:reduction` recurrence;
the conclusion then carries no side condition at all.

The two thresholds are combined, so the onset is still a single `m_0` per numerator — which is
what `thm:main` allows and `rem:degree-attainment` shows cannot be bounded by `deg B_N`. -/
theorem exceptionalRoots_numeratorUniform_of_ne_zero
    {Q : Polynomial ℝ} {r : ℕ}
    {P : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℂ} {S : Set ℂ}
    {F : Polynomial (Polynomial ℝ) → ℕ}
    (huni : NumeratorUniform Q r F)
    (hdeg : ∀ N m, (P N m).natDegree ≤ m / r)
    (hne : ∀ N, ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → P N m ≠ 0)
    (hsupply : ∀ N, ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∃ Z : Finset ℂ,
      m / r - F N ≤ Z.card ∧
      (∀ w ∈ Z, (P N m).IsRoot w) ∧ (∀ w ∈ Z, w ∈ S)) :
    ∃ C₀ C₁ : ℕ, ∀ N : Polynomial (Polynomial ℝ), ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      (exceptionalRoots (P N m) S).card
        ≤ C₀ + C₁ * (laurentWeight Q r N).natDegree := by
  obtain ⟨C₀, C₁, hC⟩ := exceptionalRoots_numeratorUniform huni hdeg hsupply
  refine ⟨C₀, C₁, fun N => ?_⟩
  obtain ⟨m₁, hm₁⟩ := hC N
  obtain ⟨m₂, hm₂⟩ := hne N
  exact ⟨max m₁ m₂, fun m hm =>
    hm₁ m (le_trans (le_max_left _ _) hm) (hm₂ m (le_trans (le_max_right _ _) hm))⟩


end ForgacsTran
