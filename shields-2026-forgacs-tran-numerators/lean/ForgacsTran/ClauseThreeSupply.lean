/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.AngularDiscrepancyFT
import ForgacsTran.ClauseThree
import ForgacsTran.ClauseThreeDefect
import ForgacsTran.QuadraticDefect

/-!
# `thm:main` clause 3 off the phase supply

`ClauseThree.clauseThree` reaches clause 3 from `ClauseThree.PhaseSupply`, a per-index
chain of blocks carrying one branch each.  `AngularDiscrepancyFT.FTPhaseSupply` is the
form the Forgács--Tran producers actually conclude in, and
`AngularDiscrepancyFT.exists_windowZeros_of_supply` already counts distinct zeros off it
at the two constants

  `(4h + 1 + κ_0)/π + 2`   and   `κ_1/π + 2`,

which are `ClauseThree.defectC₀ h κ_0` and `ClauseThree.defectC₁ κ_1` written out.  So the
window count and the clause-3 defect are the same two numbers reached along two routes,
and this module joins them: `exists_interiorZeros_of_ftPhaseSupply` puts the window count
in the `ℕ`-valued shape `eq:angular-distinct-lower` is stated in, and
`clauseThree_of_ftPhaseSupply` runs it over a family of numerators whose supply holds at
one fixed triple of constants.

**Why this is the route and `ClauseThreeComposition.FTChainGeom` is not.**  That bundle
asks for its chain inside a single *order-connected* `A` on which the principal amplitude
does not vanish.  The chain's own length clause forces `A` to span all but `2h/M + wid` of
the viewing arc, and order-connectedness then puts the gaps between components inside `A`
as well — so a weight whose reduced form contributes one amplitude zero in the interior of
the arc refutes the bundle.  `ClauseThreeChainObstruction` states that as a theorem.
`FTPhaseSupply` carries one branch per component instead and has no such consequence,
which is why it is what the producers conclude.

Sorry-free.

## Main statements

* `exists_interiorZeros_of_ftPhaseSupply` — `eq:angular-distinct-lower` at one index, from
  the supply the branch producers conclude in.
* `clauseThree_of_ftPhaseSupply_of_admissible` — `thm:main` clause 3 from a supply whose
  constants stand ahead of the numerator, over the numerators a pencil actually admits.
* `clauseThree_of_ftPhaseSupply` — the same with no admissibility predicate, which is the
  type the downstream `exceptionalRoots` theorems are stated against.
* `clauseThree_exceptionalRoots_of_ftPhaseSupply` — the same clause in the `exceptionalRoots`
  form the manuscript states, with the uniformity derived rather than assumed.
* `clauseThree_exceptionalRoots_of_ftPhaseSupply_of_admissible` — that form over the
  numerators a pencil admits, with `lem:eventual-degree`'s upper half and clause 2(i)'s
  nonvanishing both derived rather than carried.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `thm:main` clause 3,
`prop:angular-discrepancy`, `eq:angular-distinct-lower`, `subsec:proof`.

## Tags

clause three, numerator uniform, phase supply, angular discrepancy
-/

namespace ForgacsTran

open Polynomial Set Real

/-- **`⌈·⌉₊` of an affine function is affine in `ℕ`.**  `ClauseThree.numeratorUniform_ceil`
in the form that does not name `laurentWeight`, so it applies to a degree the reduction is
not the source of. -/
theorem ceil_affine_le (C₀ C₁ : ℝ) (K : ℕ) :
    ⌈C₀ + C₁ * (K : ℝ)⌉₊ ≤ ⌈C₀⌉₊ + ⌈C₁⌉₊ * K := by
  calc ⌈C₀ + C₁ * (K : ℝ)⌉₊ ≤ ⌈C₀⌉₊ + ⌈C₁ * (K : ℝ)⌉₊ := Nat.ceil_add_le _ _
    _ ≤ ⌈C₀⌉₊ + ⌈C₁⌉₊ * K := by
        gcongr
        refine Nat.ceil_le.2 ?_
        push_cast
        exact mul_le_mul_of_nonneg_right (Nat.le_ceil C₁) (by positivity)

/-- **`eq:angular-distinct-lower` at one index, off `FTPhaseSupply`.**  The whole viewing
arc is taken as the window, so `exists_windowZeros_of_supply`'s real lower bound reads
`(M+1)/r - C_0 - C_1\deg B`, and `M/r` in `ℕ` is below `(M+1)/r`.

The two constants are `ClauseThree.defectC₀ h κ_0` and `ClauseThree.defectC₁ κ_1`, so the
count is the one `clauseThree` states — reached from the supply the Forgács--Tran branch
produces rather than from a chain of blocks assumed. -/
theorem exists_interiorZeros_of_ftPhaseSupply {Q B : Polynomial ℂ} {r M : ℕ} {z τ : ℝ → ℝ}
    {hcol κ₀ κ₁ : ℝ} (hr : 1 ≤ r) (hh : 0 < hcol) (hκ₀ : 0 ≤ κ₀) (hκ₁ : 0 ≤ κ₁)
    (hzmono : StrictMonoOn z (Ioo 0 (π / r))) (hzcont : ContinuousOn z (Ioo 0 (π / r)))
    (hτ : ∀ θ ∈ Ioo 0 (π / r), 0 < τ θ)
    (hs : FTPhaseSupply Q B r z τ hcol κ₀ κ₁ M) :
    ∃ Z : Finset ℂ,
      M / r - ⌈defectC₀ hcol κ₀ + defectC₁ κ₁ * (B.natDegree : ℝ)⌉₊ ≤ Z.card ∧
      (∀ w ∈ Z, (ftCoeffPoly Q B r M).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' (z '' Ioo 0 (π / r))) := by
  have hπ : (0 : ℝ) < π := pi_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hr
  have harc : (0 : ℝ) ≤ π / r := by positivity
  obtain ⟨Z, hZ, hZr, hZm⟩ :=
    exists_windowZeros_of_supply hh hκ₀ hκ₁ hzmono hzcont hτ hs (α := 0) (β := π / r)
      le_rfl harc le_rfl
  refine ⟨Z, ?_, hZr, hZm⟩
  -- the window count's constants ARE the clause-3 constants
  set K : ℝ := (B.natDegree : ℝ) with hK
  have hD : (4 * hcol + 1 + κ₀) / π + 2 + (κ₁ / π + 2) * K
      = defectC₀ hcol κ₀ + defectC₁ κ₁ * K := by
    rw [defectC₀, defectC₁]; field_simp
  -- `(M+1)(π/r)/π` is `(M+1)/r`
  have hlin : ((M : ℝ) + 1) * (π / r - 0) / π = ((M : ℝ) + 1) / r := by
    rw [sub_zero]
    field_simp
  rw [hlin] at hZ
  have hbig : ((M : ℝ) + 1) / r
      ≤ (Z.card : ℝ) + (defectC₀ hcol κ₀ + defectC₁ κ₁ * K) := by
    rw [← hD]; linarith
  have hdiv : ((M / r : ℕ) : ℝ) ≤ ((M : ℝ) + 1) / r := by
    refine le_trans (Nat.cast_div_le) ?_
    gcongr
    linarith
  have hceil : defectC₀ hcol κ₀ + defectC₁ κ₁ * K
      ≤ (⌈defectC₀ hcol κ₀ + defectC₁ κ₁ * K⌉₊ : ℝ) := Nat.le_ceil _
  refine Nat.sub_le_iff_le_add.2 ?_
  have : ((M / r : ℕ) : ℝ)
      ≤ ((Z.card + ⌈defectC₀ hcol κ₀ + defectC₁ κ₁ * K⌉₊ : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

/-- **`thm:main` clause 3, from a numerator-uniform phase supply.**

The hypotheses fix the pencil `(Q, r)`, the branch `z`, `τ`, and the three constants
`hcol`, `κ_0`, `κ_1` **before** the numerator; `hsupply` then asks only that each numerator
have a supply at those same three.  That is the quantifier order clause 3 asserts, and it
is what the conclusion reads back: `defectC₀ hcol κ_0` and `defectC₁ κ_1` do not mention
`N`, while the threshold `M₀` may.

Same conclusion as `ClauseThreeComposition.clauseThree_of_ftGeometry`, at
`T = z((0, π/r))`, with the supply of the Forgács--Tran producers in place of the chain
geometry. -/
theorem clauseThree_of_ftPhaseSupply_of_admissible
    (Q : Polynomial ℝ) (r : ℕ) (hr : 1 ≤ r)
    {QC : Polynomial ℂ} {z τ : ℝ → ℝ} {hcol κ₀ κ₁ : ℝ}
    (hh : 0 < hcol) (hκ₀ : 0 ≤ κ₀) (hκ₁ : 0 ≤ κ₁)
    (hzmono : StrictMonoOn z (Ioo 0 (π / r))) (hzcont : ContinuousOn z (Ioo 0 (π / r)))
    (hτ : ∀ θ ∈ Ioo 0 (π / r), 0 < τ θ)
    {Adm : Polynomial (Polynomial ℝ) → Prop}
    {Bof : Polynomial (Polynomial ℝ) → Polynomial ℂ}
    {Pof : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℝ}
    (hB : ∀ N, Adm N → Bof N = (laurentWeight Q r N).map (algebraMap ℝ ℂ))
    (hP : ∀ N M, Adm N → (Pof N M).map (algebraMap ℝ ℂ) = ftCoeffPoly QC (Bof N) r M)
    (hsupply : ∀ N, Adm N → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply QC (Bof N) r z τ hcol κ₀ κ₁ M) :
    NumeratorUniform Q r
        (fun N => ⌈defectC₀ hcol κ₀
          + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊)
      ∧ ∀ N, Adm N → ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / r - ⌈defectC₀ hcol κ₀
            + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, ((Pof N M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ Complex.ofReal '' (z '' Ioo 0 (π / r))) := by
  refine ⟨numeratorUniform_defect Q r hcol κ₀ κ₁, fun N hN => ?_⟩
  have hdegB : (Bof N).natDegree = (laurentWeight Q r N).natDegree := by
    rw [hB N hN]
    exact Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective _
  obtain ⟨M₀, hM₀⟩ := hsupply N hN
  refine ⟨M₀, fun M hM _ => ?_⟩
  obtain ⟨Z, hZc, hZr, hZm⟩ :=
    exists_interiorZeros_of_ftPhaseSupply hr hh hκ₀ hκ₁ hzmono hzcont hτ (hM₀ M hM)
  rw [hdegB] at hZc
  exact ⟨Z, hZc, by rw [hP N M hN]; exact hZr, hZm⟩

/-- **The unrestricted form**, which is `ClauseThreeComposition.clauseThree_of_ftGeometry`'s
conclusion type verbatim and is what `ClauseThreeDefect.clauseThree_exceptionalRoots_of_ne_zero`
consumes.

**It is not the form a pencil can supply.**  `laurentCanon 0 = (0, 0)`, so `B_0 = 0` and
`B_0(0) = 0`; no producer gives a supply at `N = 0`, and `hsupply` here demands one.  A
caller instantiating at an actual pencil wants the `_of_admissible` form above with `Adm`
the reduction's own hypotheses.  This one is kept because it is the type the downstream
`exceptionalRoots` theorems are stated against. -/
theorem clauseThree_of_ftPhaseSupply
    (Q : Polynomial ℝ) (r : ℕ) (hr : 1 ≤ r)
    {QC : Polynomial ℂ} {z τ : ℝ → ℝ} {hcol κ₀ κ₁ : ℝ}
    (hh : 0 < hcol) (hκ₀ : 0 ≤ κ₀) (hκ₁ : 0 ≤ κ₁)
    (hzmono : StrictMonoOn z (Ioo 0 (π / r))) (hzcont : ContinuousOn z (Ioo 0 (π / r)))
    (hτ : ∀ θ ∈ Ioo 0 (π / r), 0 < τ θ)
    {Bof : Polynomial (Polynomial ℝ) → Polynomial ℂ}
    {Pof : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℝ}
    (hB : ∀ N, Bof N = (laurentWeight Q r N).map (algebraMap ℝ ℂ))
    (hP : ∀ N M, (Pof N M).map (algebraMap ℝ ℂ) = ftCoeffPoly QC (Bof N) r M)
    (hsupply : ∀ N, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply QC (Bof N) r z τ hcol κ₀ κ₁ M) :
    NumeratorUniform Q r
        (fun N => ⌈defectC₀ hcol κ₀
          + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊)
      ∧ ∀ N, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / r - ⌈defectC₀ hcol κ₀
            + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, ((Pof N M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ Complex.ofReal '' (z '' Ioo 0 (π / r))) := by
  obtain ⟨huni, hmain⟩ :=
    clauseThree_of_ftPhaseSupply_of_admissible Q r hr hh hκ₀ hκ₁ hzmono hzcont hτ
      (Adm := fun _ => True) (fun N _ => hB N) (fun N M _ => hP N M)
      (fun N _ => hsupply N)
  exact ⟨huni, fun N => hmain N trivial⟩

/-- **Paper `thm:main` clause 3 in its `exceptionalRoots` form, off the phase supply.**

`ClauseThreeDefect.clauseThree_exceptionalRoots_of_ne_zero` asks for the conclusion of
`ClauseThreeComposition.clauseThree_of_ftGeometry` as one hypothesis; the theorem above
delivers that type from the supply the Forgács--Tran branch producers conclude in, so the
chain geometry is not on the route.  `NumeratorUniform` is not a binder here: it arrives
inside the derived pair, where `ClauseThree.numeratorUniform_defect` proved it
unconditionally.

The two remaining inputs are clause 2's, not clause 3's: `hdeg` is `deg P_m ≤ m/r` and
`hne` is clause 2(i)'s eventual nonvanishing. -/
theorem clauseThree_exceptionalRoots_of_ftPhaseSupply
    (Q : Polynomial ℝ) (r : ℕ) (hr : 1 ≤ r)
    {QC : Polynomial ℂ} {z τ : ℝ → ℝ} {hcol κ₀ κ₁ : ℝ}
    (hh : 0 < hcol) (hκ₀ : 0 ≤ κ₀) (hκ₁ : 0 ≤ κ₁)
    (hzmono : StrictMonoOn z (Ioo 0 (π / r))) (hzcont : ContinuousOn z (Ioo 0 (π / r)))
    (hτ : ∀ θ ∈ Ioo 0 (π / r), 0 < τ θ)
    {Bof : Polynomial (Polynomial ℝ) → Polynomial ℂ}
    {Pof : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℝ}
    (hB : ∀ N, Bof N = (laurentWeight Q r N).map (algebraMap ℝ ℂ))
    (hP : ∀ N M, (Pof N M).map (algebraMap ℝ ℂ) = ftCoeffPoly QC (Bof N) r M)
    (hdeg : ∀ N m, ((Pof N m).map (algebraMap ℝ ℂ)).natDegree ≤ m / r)
    (hne : ∀ N, ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → (Pof N m).map (algebraMap ℝ ℂ) ≠ 0)
    (hsupply : ∀ N, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply QC (Bof N) r z τ hcol κ₀ κ₁ M) :
    ∃ C₀ C₁ : ℕ, ∀ N : Polynomial (Polynomial ℝ), ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      (exceptionalRoots ((Pof N m).map (algebraMap ℝ ℂ))
          (Complex.ofReal '' (z '' Ioo 0 (π / r)))).card
        ≤ C₀ + C₁ * (laurentWeight Q r N).natDegree :=
  clauseThree_exceptionalRoots_of_ne_zero hdeg hne
    (clauseThree_of_ftPhaseSupply Q r hr hh hκ₀ hκ₁ hzmono hzcont hτ hB hP hsupply)

/-- **Paper `thm:main` clause 3 in its `exceptionalRoots` form, at the numerators a pencil
admits, with nothing left over.**

`ClauseThreeDefect.clauseThree_exceptionalRoots_of_ne_zero` carries two further hypotheses,
`hdeg` and `hne`, and quantifies over every `N`.  Neither survives contact with a pencil in
that shape, and neither has to:

* `hdeg` is `lem:eventual-degree`'s upper half, and `Reduction.eventual_natDegree_le` proves
  it off the denominator recurrence `QuadraticDefect.denomConv_ftCoeffPoly` supplies, for
  every weight and every index.  The supply's own degree clause is one too weak — it gives
  `\deg F_M \le (M+1)/r` where the count needs `\lfloor M/r\rfloor` — so it is this recurrence
  bound that is used;
* `hne` is clause 2(i), and it is a field of `FTPhaseSupply` already;
* `∀ N` becomes `∀ N, Adm N`, because `laurentCanon 0 = (0,0)` puts `B_0 = 0` outside the
  weights any producer covers.

So the only inputs are the pencil's own `Q(0) \ne 0`, the branch regularity on the open arc,
and the supply. -/
theorem clauseThree_exceptionalRoots_of_ftPhaseSupply_of_admissible
    (Q : Polynomial ℝ) (r : ℕ) (hr : 1 ≤ r)
    {QC : Polynomial ℂ} (hQ0 : QC.coeff 0 ≠ 0)
    {z τ : ℝ → ℝ} {hcol κ₀ κ₁ : ℝ}
    (hh : 0 < hcol) (hκ₀ : 0 ≤ κ₀) (hκ₁ : 0 ≤ κ₁)
    (hzmono : StrictMonoOn z (Ioo 0 (π / r))) (hzcont : ContinuousOn z (Ioo 0 (π / r)))
    (hτ : ∀ θ ∈ Ioo 0 (π / r), 0 < τ θ)
    {Adm : Polynomial (Polynomial ℝ) → Prop}
    {Bof : Polynomial (Polynomial ℝ) → Polynomial ℂ}
    {Pof : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℝ}
    (hB : ∀ N, Adm N → Bof N = (laurentWeight Q r N).map (algebraMap ℝ ℂ))
    (hP : ∀ N M, Adm N → (Pof N M).map (algebraMap ℝ ℂ) = ftCoeffPoly QC (Bof N) r M)
    (hsupply : ∀ N, Adm N → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply QC (Bof N) r z τ hcol κ₀ κ₁ M) :
    ∃ C₀ C₁ : ℕ, ∀ N : Polynomial (Polynomial ℝ), Adm N → ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      (exceptionalRoots ((Pof N m).map (algebraMap ℝ ℂ))
          (Complex.ofReal '' (z '' Ioo 0 (π / r)))).card
        ≤ C₀ + C₁ * (laurentWeight Q r N).natDegree := by
  obtain ⟨huni, hmain⟩ :=
    clauseThree_of_ftPhaseSupply_of_admissible Q r hr hh hκ₀ hκ₁ hzmono hzcont hτ hB hP
      hsupply
  obtain ⟨C₀, C₁, hC⟩ := huni
  refine ⟨C₀, C₁, fun N hN => ?_⟩
  -- `lem:eventual-degree`, off the denominator recurrence rather than off the supply
  have hdeg : ∀ m, ((Pof N m).map (algebraMap ℝ ℂ)).natDegree ≤ m / r := by
    intro m
    rw [hP N m hN]
    exact eventual_natDegree_le QC hr hQ0 (fun M => (Bof N).coeff M)
      (ftCoeffPoly QC (Bof N) r) (denomConv_ftCoeffPoly QC (Bof N) hr hQ0) m
  obtain ⟨M₀, hM₀⟩ := hmain N hN
  obtain ⟨M₁, hM₁⟩ := hsupply N hN
  refine ⟨max (max M₀ M₁) 1, fun m hm => ?_⟩
  have hm0 : M₀ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm1 : M₁ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hmm : 1 ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨Z, hZc, hZr, hZm⟩ := hM₀ m hm0 hmm
  -- clause 2(i), read off the supply
  obtain ⟨-, -, -, -, -, -, hPne, -, -, -, -, -, -, -, -, -⟩ := id (hM₁ m hm1)
  have hPne' : (Pof N m).map (algebraMap ℝ ℂ) ≠ 0 := by rw [hP N m hN]; exact hPne
  have hZ : ((Pof N m).map (algebraMap ℝ ℂ)).natDegree
      - ⌈defectC₀ hcol κ₀
          + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊ ≤ Z.card :=
    le_trans (Nat.sub_le_sub_right (hdeg m) _) hZc
  exact le_trans (exceptionalRoots_card_le hPne' hZr hZm hZ) (hC N)

end ForgacsTran
