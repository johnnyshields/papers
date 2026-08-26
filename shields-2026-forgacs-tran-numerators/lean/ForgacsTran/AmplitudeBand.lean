/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.InteriorSupply
import ForgacsTran.AngularBookkeeping

/-!
# `subsec:proof`'s band, produced

`PhaseSupplyProducer.exists_ftPhaseSupply_of_dominance` fixes `ε` first, so that every
zero of the principal amplitude along the arc lies in `[ε, π/r - ε]`, and takes that as a
hypothesis.  Nothing produced it.  The hypothesis is not free -- it is what makes the
amplitude divisor **one** `Finset` for every index, so that every constant derived from it
is `M`-free -- but it is cheap, and this module discharges it.

The zeros of the amplitude along the open arc are finitely many: `ftAmp` vanishes exactly
where `B ∘ t₊` does, `arg t₊(θ) = θ` recovers the parameter, and `B` has finitely many
roots.  A finite subset of an open interval stands off both endpoints, and half that
standoff is a band.

**The hypotheses are on the open arc, not on the band.**  `exists_ftPhaseSupply_of_dominance`
asks for the branch and its simplicity only on `[ε, π/r - ε]`, which is not enough to know
where the zeros outside that interval are; producing `ε` needs them on all of `(0, π/r)`.
That is what `FTGeometryAssembly.ft_branch_root_and_pos` and
`PrincipalSimpleBranch.ft_principal_simple_at_branch` deliver, so the strengthening costs
nothing at the branch instantiation.

## Main statements

* `exists_band_of_amplitude_zeros` -- the band, with `ε > 0` and `ε < π/r - ε`.
* `band_subset_Ioo_pi` -- the band sits inside `(0, π)`, which is
  `exists_ftPhaseSupply_of_dominance`'s `hεband`.
* `windowRadius_le_common` -- a retained set's own deletion window sits inside the common
  one `hdom`'s antecedent deletes, which is the comparison the two sides of
  `eq:amplitude-deletion` meet at.

## Implementation notes

`ftAmp = -(B(t₊)/S(t₊))` and Lean's `x/0 = 0`, so `ftAmp = 0` does **not** on its own give
`B(t₊) = 0`: it also holds where the cofactor vanishes.  `Amplitude.ftAmp_eq_zero_iff` is
what excludes that, and `hsimple` is why it applies.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Angular discrepancy and proof of
the main theorem» (`subsec:proof`) over «Spectral geometry, residues, and the principal
amplitude» (`sec:geometry`, `lem:amplitude-divisor`).

## Tags

amplitude divisor, band, retained range
-/

open Polynomial

namespace ForgacsTran

open Set Real

/-- **Every amplitude zero of the arc is the argument of a zero of `B`.**  The step
`exists_band_of_amplitude_zeros` runs on, isolated because it is where `x/0 = 0` is
excluded. -/
theorem arg_mem_of_ftAmp_eq_zero {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    (hr : 1 ≤ r) (hB0 : B ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / r)) (hτ : 0 < τ θ)
    (hroot : (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hsimple : (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0)
    (hzero : ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0) :
    ftPrincipal τ θ ∈ B.roots ∧ Complex.arg (ftPrincipal τ θ) = θ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hle : π / r ≤ π := by
    rw [div_le_iff₀ hrR]
    nlinarith [pi_pos, (by exact_mod_cast hr : (1 : ℝ) ≤ (r : ℝ))]
  have hopen : θ ∈ Ioo (0 : ℝ) π := ⟨hθ.1, lt_of_lt_of_le hθ.2 hle⟩
  have hBz : B.eval (ftPrincipal τ θ) = 0 := (ftAmp_eq_zero_iff hroot hsimple).1 hzero
  exact ⟨(mem_roots hB0).2 hBz, arg_ftPrincipal hτ hopen⟩

/-- **`subsec:proof`'s band.**  A positive `ε`, below half the arc, outside which the
principal amplitude does not vanish anywhere on `(0, π/r)`.

This is `exists_ftPhaseSupply_of_dominance`'s `hband`, and it is the one binder of that
theorem that neither `thm:weighted-dominance` nor the branch supply produces. -/
theorem exists_band_of_amplitude_zeros {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    (hr : 1 ≤ r) (hB0 : B ≠ 0)
    (hτ : ∀ θ ∈ Ioo (0 : ℝ) (π / r), 0 < τ θ)
    (hroot : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hsimple : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < π / r - ε ∧
      ∀ θ ∈ Ioo (0 : ℝ) (π / r),
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ Icc ε (π / r - ε) := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have harc : (0 : ℝ) < π / r := by positivity
  -- the candidate parameters: arguments of the zeros of `B` that land on the open arc
  set T : Finset ℝ :=
    (B.roots.toFinset.image Complex.arg).filter (fun θ => 0 < θ ∧ θ < π / r) with hT
  have hTmem : ∀ θ ∈ T, 0 < θ ∧ θ < π / r := fun θ hθ => (Finset.mem_filter.1 hθ).2
  -- one always-present element, so the infimum below is over a nonempty family
  set T' : Finset ℝ := insert (π / (2 * r)) T with hT'
  have hT'ne : T'.Nonempty := ⟨π / (2 * r), Finset.mem_insert_self _ _⟩
  set g : ℝ → ℝ := fun θ => min θ (π / r - θ) with hg
  set ε₀ : ℝ := T'.inf' hT'ne g with hε₀
  have hhalf : π / (2 * r) = (π / r) / 2 := by ring
  have hpos : 0 < ε₀ := by
    rw [hε₀, Finset.lt_inf'_iff]
    intro b hb
    rcases Finset.mem_insert.1 hb with hb | hb
    · subst hb
      rw [hg]
      simp only [lt_min_iff]
      constructor
      · positivity
      · rw [hhalf]; linarith
    · obtain ⟨h1, h2⟩ := hTmem b hb
      rw [hg]
      simp only [lt_min_iff]
      exact ⟨h1, by linarith⟩
  have hhalfle : ε₀ ≤ π / (2 * r) := by
    refine le_trans (Finset.inf'_le g (Finset.mem_insert_self _ _)) ?_
    rw [hg]
    exact min_le_left _ _
  refine ⟨ε₀ / 2, by linarith, ?_, ?_⟩
  · rw [hhalf] at hhalfle; linarith
  · intro θ hθ hzero
    obtain ⟨hmem, harg⟩ := arg_mem_of_ftAmp_eq_zero hr hB0 hθ (hτ θ hθ)
      (hroot θ hθ) (hsimple θ hθ) hzero
    have hθT : θ ∈ T := by
      refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨ftPrincipal τ θ, ?_, harg⟩, hθ.1, hθ.2⟩
      exact Multiset.mem_toFinset.2 hmem
    have hle := Finset.inf'_le (s := T') g (Finset.mem_insert_of_mem hθT)
    rw [← hε₀, hg] at hle
    have h1 : ε₀ ≤ θ := le_trans hle (min_le_left _ _)
    have h2 : ε₀ ≤ π / r - θ := le_trans hle (min_le_right _ _)
    exact ⟨by linarith, by linarith⟩

/-- **`exists_ftPhaseSupply_of_dominance`'s `hεband`.**  A band produced by
`exists_band_of_amplitude_zeros` sits inside `(0, π)`: it stands off `0` by `ε` and
off `π/r ≤ π` by the same. -/
theorem band_subset_Ioo_pi {r : ℕ} {ε : ℝ} (hr : 1 ≤ r) (hε : 0 < ε) :
    Icc ε (π / r - ε) ⊆ Ioo (0 : ℝ) π := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hle : π / r ≤ π := by
    rw [div_le_iff₀ hrR]
    nlinarith [pi_pos, (by exact_mod_cast hr : (1 : ℝ) ≤ (r : ℝ))]
  intro x hx
  exact ⟨lt_of_lt_of_le hε hx.1, lt_of_le_of_lt hx.2 (by linarith)⟩

/-! ### The two deletion radii -/

/-- **A retained set's own window is inside the common one.**  `thm:weighted-dominance`
concludes under its own family's radius `exp(-((-log σ)/(2|S|)·M/ν_j))`, and
`exists_ftPhaseSupply_of_dominance`'s `hdom` deletes the common radius
`ftWindowRadius`, taken over the whole divisor at the largest multiplicity.  The
antecedent supplied is the common one, so it has to be the **larger**, and it is: the
retained set is a subset, so its cardinality is smaller and its own constant larger,
and its multiplicity is below the maximum.  Both comparisons push the same way.

**`θj ∈ S` is load-bearing, not decoration.**  At `S = ∅` the constant is `c / 0`, which
Lean evaluates to `0`, so the radius is `exp 0 = 1` and the inequality is false against
any genuine window.  Membership is what forces `1 ≤ |S|`.  The composition never needs
the empty case, because there the clause it feeds is vacuous on both sides.

`AngularBookkeeping.windowRadius_le` is the same comparison at one fixed family; this is
the one across two, which is what the seam between the two theorems actually asks. -/
theorem windowRadius_le_common {σ : ℝ} {S D : Finset ℝ} {ν : ℝ → ℕ} {N M : ℕ} {θj θ0 : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hSD : S ⊆ D) (hθj : θj ∈ S)
    (hν : 1 ≤ ν θj) (hνN : ν θj ≤ N) :
    windowRadius σ S ν M θj ≤ windowRadius σ D (fun _ => N) M θ0 := by
  have hlog : 0 < -Real.log σ := by
    have := Real.log_neg hσ0 hσ1; linarith
  have hScard : 1 ≤ S.card := Finset.card_pos.2 ⟨θj, hθj⟩
  have hDcard : S.card ≤ D.card := Finset.card_le_card hSD
  have hSR : (0 : ℝ) < S.card := by exact_mod_cast hScard
  have hDR : (0 : ℝ) < D.card := by exact_mod_cast le_trans hScard hDcard
  have hDleR : (S.card : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hDcard
  have hνR : (0 : ℝ) < (ν θj : ℝ) := by exact_mod_cast hν
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast le_trans hν hνN
  have hνNR : (ν θj : ℝ) ≤ (N : ℝ) := by exact_mod_cast hνN
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  rw [windowRadius, windowRadius]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  gcongr

end ForgacsTran
