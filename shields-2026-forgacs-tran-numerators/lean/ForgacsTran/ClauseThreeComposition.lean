/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.ClauseThree
import ForgacsTran.MainClauses
import ForgacsTran.MainComposition

/-!
# `thm:main` clause 3 over the Forgács–Tran branch

`ClauseThree.clauseThree` proves the numerator-uniform *shape*: given a `PhaseSupply` for
every numerator, one `NumeratorUniform` constant family bounds the defect, with
`C₀ = defectC₀ hwin κ₀` and `C₁ = defectC₁ κ₁` bound outside the quantifier over numerators.
It takes the supply as a hypothesis.  `MainComposition.main_of_ftBranch_of_geometry` runs the
Forgács--Tran branch down to clauses 1 and 2, and `DominanceFT.weighted_dominance_of_branch`
supplies `eq:dominance-bound` on the retained range of `eq:retained-range` — but neither
produces a supply, because clause 2 needs only one component and one opaque defect constant
while `prop:angular-discrepancy` needs the whole retained range decomposed into components
and the constant *derived*.

This module builds the missing joint.  Its content is the sign field of `PhaseSupply`:
at a phase point of `eq:Phi-def`, `eq:principal-decomposition` fixes the sign of the
principal term and `eq:dominance-bound` transfers it to the whole coefficient.  That is
`PhaseCount.principal_sign_at_phase_point` read in the named objects of `sec:dominance`,
and it is what turns the analytic conclusion `thm:weighted-dominance` reaches into the
combinatorial input `prop:angular-discrepancy` runs on.

## Main statements

* `stripSign_eq_zpow`, `ftRemainder_eq_abs_principal_gap` — the two conversions:
  `eq:principal-decomposition` solved for `R_M`, and `(-1)^k` in the form `ViewingAngle` uses.
* `sign_at_phase_point_of_ftDominance` — the sign at a phase point, from
  `eq:dominance-bound` alone.
* `FTChainGeom` — the branch geometry on one monotone chain at one index, spelled out: the
  components of `eq:Omega-M` sit inside `eq:retained-range` off the amplitude windows, `z` is
  the strictly monotone reparametrization of `thm:FT-geometry`, `ψ` is a differentiable branch
  of `arg W` with `eq:phase-derivative-bound`, and the three quantitative facts
  `prop:angular-discrepancy` runs on hold.  **No dominance hypothesis is in it**, and neither
  is the coefficient polynomial: the geometry is a fact about the branch.
* `phaseSupply_of_ftChainGeom` — the geometry plus `eq:dominance-bound` on the retained range
  gives the supply.
* `clauseThree_of_ftGeometry` — `thm:main` clause 3 with the supply derived rather than
  assumed, over the branch data of `thm:FT-geometry` and the conclusion
  `weighted_dominance_of_branch` reaches, so the clause rests on what clauses 1 and 2 rest on.

## Implementation notes

**Differs from the paper's route.**  `subsec:proof` runs one narrative: the dominance bound,
the phase count, and the defect split are established in sequence over the same picture.  Here
the branch geometry is isolated from `eq:dominance-bound` — `FTChainGeom` mentions neither the
coefficient polynomial nor the remainder — so that the dominance conclusion enters once, at
`phaseSupply_of_ftChainGeom`, and the numerator-free constants are visible in the binder list
rather than tracked through the prose.  The manuscript has no reason to make that split; a
Lean statement does, because it is what makes the `N`-independence of `C₀` and `C₁` checkable
by reading the quantifier order.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair dominance and the
fixed-numerator theorem» (`subsec:proof`, `prop:angular-discrepancy`) and `thm:main`
clause 3, joined to the branch data `sec:dominance` produces.

## Tags

numerator-uniform defect, Forgacs-Tran branch, composition
-/

namespace ForgacsTran

open Real Set

/-! ### Two conversions -/

/-- `stripSign` is `(-1)^k`, which is the form `PhaseCount.principal_sign_at_phase_point`
concludes in. -/
theorem stripSign_eq_zpow (k : ℤ) : stripSign k = (-1 : ℝ) ^ k := by
  unfold stripSign
  rcases Int.even_or_odd k with hk | hk
  · rw [if_pos hk, hk.neg_one_zpow]
  · rw [if_neg (by rw [Int.not_even_iff_odd]; exact hk), hk.neg_one_zpow]

/-- Paper `eq:principal-decomposition`, solved for the remainder.  `ftRemainder` is defined
as the norm of the gap between the normalized coefficient `τ^{M+1}P_m(z(θ))` and the
principal pair's contribution; dividing `t_+^{M+1}` out of the latter turns it into
`2\operatorname{Re}(W e^{-i(M+1)θ})`, and the gap is then a real number whose absolute
value `ftRemainder` is. -/
theorem ftRemainder_eq_abs_principal_gap {Q B : Polynomial ℂ} {r M : ℕ} {z τ : ℝ → ℝ}
    {P : Polynomial ℝ} {θ : ℝ} (hτ : 0 < τ θ)
    (hP : P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M) :
    ftRemainder Q B r z τ M θ
      = |(τ θ) ^ (M + 1) * P.eval (z θ)
          - 2 * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
              * Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I)).re| := by
  have heval : (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ) = ((P.eval (z θ) : ℝ) : ℂ) := by
    rw [← hP, Polynomial.eval_map,
      show (((z θ : ℝ) : ℂ)) = (algebraMap ℝ ℂ) (z θ) from rfl,
      Polynomial.eval₂_at_apply]
    rfl
  have hratio : ((τ θ : ℝ) : ℂ) ^ (M + 1)
      * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) / (ftPrincipal τ θ) ^ (M + 1))
      = ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
        * Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I) := by
    rw [show ((τ θ : ℝ) : ℂ) ^ (M + 1)
        * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) / (ftPrincipal τ θ) ^ (M + 1))
        = (((τ θ : ℝ) : ℂ) ^ (M + 1) / (ftPrincipal τ θ) ^ (M + 1))
          * ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) by ring,
      ftPrincipal_pow_ratio hτ M]
    ring
  rw [ftRemainder, heval, hratio]
  rw [show (((τ θ : ℝ) : ℂ)) ^ (M + 1) * ((P.eval (z θ) : ℝ) : ℂ)
      = (((τ θ) ^ (M + 1) * P.eval (z θ) : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-! ### The sign at a phase point -/

/-- **The joint.**  Paper `subsec:proof`: at a phase point of `eq:Phi-def` — a `θ` with
`Φ_M(θ) = (M+1)θ - ψ(θ) = kπ` — the principal term of
`eq:principal-decomposition` is `2(-1)^k|W(θ)|`, and `eq:dominance-bound` leaves at least
`\tfrac32|W(θ)|` of it, so `(-1)^kP_m(z(θ))` is strictly positive.

This is the exact input `ClauseThree.PhaseSupply` asks for, produced from what
`thm:weighted-dominance` concludes rather than assumed.  Nothing here is quantitative: the
`\tfrac32` is discarded, and only the sign survives. -/
theorem sign_at_phase_point_of_ftDominance {Q B : Polynomial ℂ} {r M : ℕ}
    {z τ ψ : ℝ → ℝ} {P : Polynomial ℝ} {θ : ℝ} {k : ℤ}
    (hP : P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M)
    (hτ : 0 < τ θ)
    (hWne : ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0)
    (hpolar : ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
      = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I))
    (hdom : ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2)
    (hphase : ((M : ℝ) + 1) * θ - ψ θ = (k : ℝ) * π) :
    0 < stripSign k * P.eval (z θ) := by
  have hnorm : ftPrincipalAmp Q B r z τ θ
      = ‖ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)‖ := rfl
  have hgap := ftRemainder_eq_abs_principal_gap (Q := Q) (B := B) (r := r) (M := M)
    (z := z) (τ := τ) (P := P) (θ := θ) hτ hP
  have hR : |(τ θ) ^ (M + 1) * P.eval (z θ)
      - 2 * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
          * Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I)).re|
      ≤ ‖ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)‖ / 2 := by
    rw [← hgap, ← hnorm]; exact hdom
  have hkey := principal_sign_at_phase_point
    (W := ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ))
    (ψ := ψ θ) (φ := ((M : ℝ) + 1) * θ)
    (Rm := (τ θ) ^ (M + 1) * P.eval (z θ)
      - 2 * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
          * Complex.exp (-(((((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I)).re)
    (G := (τ θ) ^ (M + 1) * P.eval (z θ)) (k := k)
    (by rw [← hnorm]; exact hpolar) hphase (by ring) hR
  have hWpos : 0 < ‖ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)‖ := norm_pos_iff.2 hWne
  have hc : (0 : ℝ) < (τ θ) ^ (M + 1) := pow_pos hτ _
  have hpos : 0 < ((-1 : ℝ) ^ k) * ((τ θ) ^ (M + 1) * P.eval (z θ)) := by linarith
  rw [stripSign_eq_zpow]
  by_contra hcon
  push Not at hcon
  nlinarith [hpos, mul_nonneg hc.le (neg_nonneg.2 hcon)]

/-! ### The branch geometry on one chain -/

/-- Paper `prop:angular-discrepancy`, the geometric side, at one index and one numerator.
The components of `eq:Omega-M` are the odd-to-even steps `[w(2i), w(2i+1)]` of a monotone
chain inside an order-connected `A`, and the deleted windows are the even-to-odd steps.

Every field is a statement of `thm:FT-geometry`, of `eq:retained-range`, or of
`eq:phase-derivative-bound`, on `A`:

* `A` sits inside the retained range of `eq:retained-range` and off the amplitude windows
  `Θ M`, which is what lets `eq:dominance-bound` be evaluated on it;
* `τ > 0` and `z` is the strictly monotone reparametrization into `T`;
* the principal amplitude does not vanish on `A` and has the polar form `|W|e^{iψ}` for a
  differentiable branch `ψ` with `|ψ'| ≤ κ < M+1` — `κ` is
  `κ_{Q,r,B}` and *does* see the numerator, which is why the threshold in `M` is here
  rather than in the discrepancy constants;
* at most `K + 1` components (`eq:amplitude-zero-count`), the retained length of
  `eq:retained-range`, and `eq:linear-phase-variation` bounding `eVariationOn ψ A` by
  `κ_0 + κ_1 K` with both constants free of the numerator.

**Neither the coefficient polynomial nor `eq:dominance-bound` appears**: this is a fact about
the denominator branch and the weight, and the coefficient sequence enters only at
`phaseSupply_of_ftChainGeom`. -/
def FTChainGeom (Q B : Polynomial ℂ) (r : ℕ) (z τ ψ : ℝ → ℝ) (M K : ℕ)
    (hwin wid κ₀ κ₁ h bb : ℝ) (Θ : ℕ → Set ℝ) (T : Set ℝ) : Prop :=
  ∃ (A : Set ℝ) (w : ℕ → ℝ) (n : ℕ) (dψ : ℝ → ℝ) (κ : ℝ),
    A.OrdConnected ∧
    (∀ θ ∈ A, h / M ≤ θ ∧ θ ≤ bb - h / M ∧ θ ∉ Θ M) ∧
    Monotone w ∧ (∀ i, w i ∈ A) ∧
    (∀ i, i + 1 < n → w (2 * i + 1) < w (2 * i + 2)) ∧
    StrictMonoOn z A ∧ (∀ θ ∈ A, z θ ∈ T) ∧
    (∀ θ ∈ A, 0 < τ θ) ∧
    (∀ θ ∈ A, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) ∧
    (∀ θ ∈ A, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
      = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I)) ∧
    (∀ θ ∈ A, HasDerivAt ψ (dψ θ) θ) ∧
    (∀ θ ∈ A, |dψ θ| ≤ κ) ∧ κ < (M : ℝ) + 1 ∧
    n ≤ K + 1 ∧
    (π / r - 2 * hwin / M - wid
      ≤ ∑ i ∈ Finset.range n, (w (2 * i + 1) - w (2 * i))) ∧
    (((M : ℝ) + 1) * wid ≤ 1) ∧
    eVariationOn ψ A ≤ ENNReal.ofReal (κ₀ + κ₁ * K)

/-- **The two halves meet.**  The branch geometry together with `eq:dominance-bound` on the
retained range — the conclusion `DominanceFT.weighted_dominance_of_branch` reaches, verbatim —
gives the phase supply `prop:angular-discrepancy` runs on.

The dominance is *consumed*, not assumed on the components: `FTChainGeom` records that `A`
sits inside `eq:retained-range` off the amplitude windows, and that containment is what makes
`hdom` applicable there.  The continuity and strict monotonicity of `Φ_M` are discharged from
`eq:phase-derivative-bound` through `AngularBookkeeping`, and the sign at each phase point
from `sign_at_phase_point_of_ftDominance`. -/
theorem phaseSupply_of_ftChainGeom {Q B : Polynomial ℂ} {r : ℕ} {z τ ψ : ℝ → ℝ}
    {P : Polynomial ℝ} {M K M₀ : ℕ} {hwin wid κ₀ κ₁ h bb : ℝ}
    {Θ : ℕ → Set ℝ} {T : Set ℝ}
    (hP : P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M)
    (hTconn : T.OrdConnected) (hκ : 0 ≤ κ₀ + κ₁ * K) (hM₀ : M₀ ≤ M)
    (hdom : ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ, h / M ≤ θ → θ ≤ bb - h / M → θ ∉ Θ M →
      ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2)
    (hgeom : FTChainGeom Q B r z τ ψ M K hwin wid κ₀ κ₁ h bb Θ T) :
    PhaseSupply P ψ z M K r hwin wid κ₀ κ₁ T := by
  obtain ⟨A, w, n, dψ, κ, hAconn, hret, hw, hmem, hsep, hzmono, hzT, hτ, hWne, hpolar,
    hψ, hκbd, hMκ, hcard, hlen, hwid, hvar⟩ := hgeom
  -- the components sit inside `A`
  have hsubA : ∀ i j : ℕ, i ≤ j → Icc (w i) (w j) ⊆ A := fun i j _ =>
    hAconn.out (hmem i) (hmem j)
  -- `eq:dominance-bound` on `A`, from the retained-range conclusion
  have hdomA : ∀ θ ∈ A, ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
    intro θ hθ
    exact hdom M hM₀ θ (hret θ hθ).1 (hret θ hθ).2.1 (hret θ hθ).2.2
  refine phaseSupply_of_chain P hAconn hTconn hw hmem hzmono hzT hsep ?_ ?_ ?_
    hcard hlen hwid hκ hvar
  · exact fun i _ => continuousOn_phase_congr (fun θ _ => rfl)
      (fun θ hθ => hψ θ (hsubA _ _ (by omega) hθ))
  · exact fun i _ => strictMonoOn_phase_congr (fun θ _ => rfl)
      (fun θ hθ => hψ θ (hsubA _ _ (by omega) hθ))
      (fun θ hθ => hκbd θ (hsubA _ _ (by omega) hθ)) hMκ
  · intro i _ θ hθ k hk
    have hθA : θ ∈ A := hsubA (2 * i) (2 * i + 1) (by omega) hθ
    exact sign_at_phase_point_of_ftDominance hP (hτ θ hθA) (hWne θ hθA) (hpolar θ hθA)
      (hdomA θ hθA) hk

/-! ### `thm:main` clause 3, over the branch -/

/-- **Paper `thm:main` clause 3, with the phase supply derived.**  Fix `(Q, r)`, the branch
`z`, `τ` of `thm:FT-geometry`, the target interval `T`, and the three constants of the
analysis — `h` from `eq:retained-range` and `κ_0`, `κ_1` from
`cor:linear-phase-variation`.  Every one of them is bound **before** the numerator.  Given, for
each numerator `N`, the dominance conclusion `thm:weighted-dominance` reaches on the retained
range and the branch geometry of `FTChainGeom` at every large index, `thm:main` clause 3 holds:
one `NumeratorUniform` family bounds the defect, and at every large index the coefficient
polynomial has at least `M/r - ⌈ C_0 + C_1deg B_N⌉` distinct zeros in `T`.

What clause 3 adds over clause 2 is exactly the quantifier order, and it is visible in the
statement: `hwin`, `κ₀`, `κ₁`, `z`, `τ`, `r`, `T` and `bb` stand outside `∀ N`, while `B_N`,
`P_{N,m}`, `ψ_{N,m}`, the window width and the deleted windows `Θ N` stand inside.  The
numerator-dependent `κ` of `eq:phase-derivative-bound` is hidden inside `FTChainGeom`,
where it belongs — it may see `N`, and the discrepancy constants may not.

`hgeom` is quantified over `h` and the threshold because `hdom` produces both: the retained
range is not known until the constants are, which is the order `thm:weighted-dominance` fixes
them in.  This mirrors `MainComposition.main_of_ftBranch_of_geometry`, whose `hcomp` is
quantified the same way, so clause 3 here rests on the hypotheses clauses 1 and 2 rest on.

**Containment.**  The conclusion asserts `NumeratorUniform` of the defect family and produces
a `Finset ℂ` of roots of `(Pof N M).map` inside `Complex.ofReal '' T`.  No binder mentions
`NumeratorUniform`, `IsRoot`, `Finset ℂ` or the cardinality of a root set; `hdom` compares two
norms, and `hB`, `hP` identify `B_N` and `P_{N,m}` without saying anything about their zeros.
`hgeom` is `FTChainGeom`, which unfolds to a statement about the branch, the chain and the
weight; the one count in it is the number `n ≤ K + 1` of components.  The family is built by
`ClauseThree.numeratorUniform_defect`, which has no hypotheses at all, and the zero set by
`phaseSupply_of_ftChainGeom` through `exists_interiorZeros_of_phaseSupply`. -/
theorem clauseThree_of_ftGeometry
    (Q : Polynomial ℝ) (r : ℕ) (hr : 1 ≤ r)
    {QC : Polynomial ℂ} {z τ : ℝ → ℝ} {T : Set ℝ} {hwin κ₀ κ₁ bb : ℝ}
    (hh : 0 ≤ hwin) (hκ₀ : 0 ≤ κ₀) (hκ₁ : 0 ≤ κ₁) (hTconn : T.OrdConnected)
    {Bof : Polynomial (Polynomial ℝ) → Polynomial ℂ}
    {Pof : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℝ}
    {ψof : Polynomial (Polynomial ℝ) → ℕ → ℝ → ℝ}
    {widof : Polynomial (Polynomial ℝ) → ℕ → ℝ}
    {Θ : Polynomial (Polynomial ℝ) → ℕ → Set ℝ}
    (hB : ∀ N, Bof N = (laurentWeight Q r N).map (algebraMap ℝ ℂ))
    (hP : ∀ N M, (Pof N M).map (algebraMap ℝ ℂ) = ftCoeffPoly QC (Bof N) r M)
    (hdom : ∀ N, ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ bb - h / M → θ ∉ Θ N M →
        ftRemainder QC (Bof N) r z τ M θ ≤ ftPrincipalAmp QC (Bof N) r z τ θ / 2)
    (hgeom : ∀ (N : Polynomial (Polynomial ℝ)) (h : ℝ), 0 < h → ∀ Mz : ℕ,
      ∃ M₀ : ℕ, Mz ≤ M₀ ∧ ∀ M, M₀ ≤ M → 1 ≤ M →
        FTChainGeom QC (Bof N) r z τ (ψof N M) M (Bof N).natDegree
          hwin (widof N M) κ₀ κ₁ h bb (Θ N) T) :
    NumeratorUniform Q r
        (fun N => ⌈defectC₀ hwin κ₀
          + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊)
      ∧ ∀ N, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / r - ⌈defectC₀ hwin κ₀
            + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, ((Pof N M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ Complex.ofReal '' T) := by
  -- `deg B_N` is the degree of the canonical reduced weight `eq:canonical-Laurent-factorization`
  have hdegB : ∀ N, (Bof N).natDegree = (laurentWeight Q r N).natDegree := by
    intro N
    rw [hB N]
    exact Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective _
  refine clauseThree Q r hr hh (F := Pof) (ψ := ψof) (z := z) (wid := widof) (T := T)
    (fun N => ?_)
  obtain ⟨h, hhpos, M₀, hdomN⟩ := hdom N
  obtain ⟨M₁, hM₁, hgeomN⟩ := hgeom N h hhpos M₀
  refine ⟨M₁, fun M hM hM1 => ?_⟩
  have hκ : (0 : ℝ) ≤ κ₀ + κ₁ * ((laurentWeight Q r N).natDegree : ℝ) := by positivity
  have hsup := phaseSupply_of_ftChainGeom (P := Pof N M) (hP N M) hTconn
    (K := (Bof N).natDegree) (by rw [hdegB N]; exact hκ) (le_trans hM₁ hM) hdomN
    (hgeomN M hM hM1)
  rwa [hdegB N] at hsup

end ForgacsTran
