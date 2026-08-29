/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchAngleDerivSum
import ForgacsTran.CubicPhaseSupplyClosed

/-!
# `hstates` at a general pencil

`BranchAngleDerivSum.exists_rootBranchState_ftBranch` produces `RootBranchState`
at every admissible `Q` and `r`, on a compact sub-interval of the **open** arc, and
`BranchSupply`'s `hstates` binder now asks for exactly that shape.  Two gaps
remain between them and both are closed here.

* **`hfree`.**  The binder supplies the amplitude's nonvanishing; the producer wants
  `γ x ≠ β`.  They are the same statement read through `ftAmp = -(B(γ)/cofactor)`:
  a zero of `B` sitting on the branch makes the numerator vanish, hence the whole
  quotient, so the amplitude clause forbids it.
* **The radius spelling.**  The producer states the state at
  `ftPrincipal (ftTau a r (n-1))`, and the supply at its own `τ`, which is an
  extension of it — they agree on the open arc and not beyond.  `RootBranchState`
  is not congruent in `γ` for free: its last clause pins `ψ` to
  `polarAngle γ dγ β a` as a **function on all of `ℝ`**, and the two `γ` differ off
  the arc.  What rescues it is that `logLift` reads `γ` only on `uIcc a s`, so the
  angles agree throughout `[a,b]` and the state can be rebuilt with `ψ` taken from
  the supply's own `γ`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `cor:linear-phase-variation`.

## Tags

root branch state, phase variation, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real

/-- `logLift` reads `γ` only between the base point and the argument. -/
theorem logLift_congr {γ γ' dγ : ℝ → ℂ} {β : ℂ} {a s : ℝ}
    (h : EqOn γ γ' (uIcc a s)) :
    logLift γ dγ β a s = logLift γ' dγ β a s := by
  rw [logLift, logLift, h left_mem_uIcc]
  congr 1
  exact intervalIntegral.integral_congr fun u hu => by rw [h hu]

theorem polarAngle_congr {γ γ' dγ : ℝ → ℂ} {β : ℂ} {a s : ℝ}
    (h : EqOn γ γ' (uIcc a s)) :
    polarAngle γ dγ β a s = polarAngle γ' dγ β a s := by
  rw [polarAngle, polarAngle, logLift_congr h]

/-- **`RootBranchState` transfers along an agreement on `[a,b]`.**  The witness `ψ`
is rebuilt from the target `γ'`, which is what the last clause pins it to; every
other clause is evaluated inside `[a,b]`, where the two agree. -/
theorem rootBranchState_congr {γ γ' dγ d2γ : ℝ → ℂ} {β : ℂ} {a b : ℝ} {k : ℕ}
    {Lb Rb : Fin k → ℝ} {ψ : Fin k → ℝ → ℝ} (hab : a ≤ b)
    (h : EqOn γ γ' (Icc a b)) (hstate : RootBranchState γ dγ d2γ β a b Lb Rb ψ) :
    ∃ ψ' : Fin k → ℝ → ℝ, RootBranchState γ' dγ d2γ β a b Lb Rb ψ' := by
  classical
  have hanga : ∀ x ∈ Icc a b, polarAngle γ dγ β a x = polarAngle γ' dγ β a x := by
    intro x hx
    exact polarAngle_congr (h.mono (uIcc_subset_Icc ⟨le_rfl, hab⟩ hx))
  have hangb : ∀ x ∈ Icc a b, polarAngle γ dγ β b x = polarAngle γ' dγ β b x := by
    intro x hx
    exact polarAngle_congr (h.mono (uIcc_subset_Icc ⟨hab, le_rfl⟩ hx))
  rcases hstate with ⟨S, hne, hSmem, hSfull, -⟩ |
    ⟨m, ham, hmb, S₁, S₂, hm, hne, h1, h2, hsplit⟩
  · refine ⟨fun _ => polarAngle γ' dγ β a, Or.inl ⟨S, fun x hx => ?_, hSmem,
      fun x hx j hj => ?_, fun _ => rfl⟩⟩
    · rw [← h hx]; exact hne x hx
    · refine hSfull x hx j ?_
      rw [hanga x (Ioo_subset_Icc_self hx)]
      exact hj
  · refine ⟨fun i => if Icc (Lb i) (Rb i) ⊆ Ico a m then polarAngle γ' dγ β a
      else polarAngle γ' dγ β b,
      Or.inr ⟨m, ham, hmb, S₁, S₂, ?_, fun x hx hxm => ?_, fun x hx j hj => ?_,
        fun x hx j hj => ?_, fun i => ?_⟩⟩
    · rw [← h ⟨ham, hmb⟩]; exact hm
    · rw [← h hx]; exact hne x hx hxm
    · have hxab : x ∈ Icc a b := ⟨le_of_lt hx.1, le_trans hx.2.le hmb⟩
      refine h1 x hx j ?_
      rw [hanga x hxab]; exact hj
    · have hxab : x ∈ Icc a b := ⟨le_trans ham (le_of_lt hx.1), hx.2.le⟩
      refine h2 x hx j ?_
      rw [hangb x hxab]
      exact hj
    · by_cases hc : Icc (Lb i) (Rb i) ⊆ Ico a m
      · exact Or.inl ⟨hc, by simp [hc]⟩
      · rcases hsplit i with ⟨hi, -⟩ | ⟨hi, -⟩
        · exact absurd hi hc
        · exact Or.inr ⟨hi, by simp [hc]⟩

/-- **`BranchSupply`'s `hstates` at a general admissible pencil.**

The binder's shape and `exists_rootBranchState_ftBranch`'s now match: both work on
a compact sub-interval of the open arc.  Two things are supplied here — `hJ` from
the block bounds, and `hfree` from the amplitude clause, since a zero of `B`
sitting on the branch makes `ftAmp` vanish outright.

`τ` is any extension agreeing with the branch radius on the open arc, which is
what `ftTauArc` and `ftTauArcAt` both are. -/
theorem ft_rootStates_general {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {z τ : ℝ → ℝ}
    {B : Polynomial ℂ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hτ : ∀ θ ∈ Ioo (0 : ℝ) (π / r), τ θ = ftTau a r (n - 1) θ) :
    ∀ (a' b' : ℝ), a' ≤ b' → Icc a' b' ⊆ Ioo (0 : ℝ) (π / r) →
      ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc a' b') → (∀ i, Rb i ∈ Icc a' b') →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, ∀ θ ∈ Icc (Lb i) (Rb i),
        ftAmp (ftRootPoly c a) B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) →
      ∀ β ∈ B.roots, ∃ ψ : Fin k → ℝ → ℝ,
        RootBranchState (ftPrincipal τ) (ftGammaDeriv a r (n - 1))
          (ftGammaDeriv2 a r (n - 1)) β a' b' Lb Rb ψ := by
  intro a' b' hab hsub k Lb Rb hL hR _ hamp β hβ
  have hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ Icc a' b' :=
    fun i => Icc_subset_Icc (hL i).1 (hR i).2
  have hBz : B.eval β = 0 := isRoot_of_mem_roots hβ
  -- `hfree`: the branch cannot meet a zero of `B` where the amplitude is nonzero
  have hfree : ∀ i, ∀ x ∈ Icc (Lb i) (Rb i),
      ftPrincipal (ftTau a r (n - 1)) x ≠ β := by
    intro i x hx hcon
    have hτx : τ x = ftTau a r (n - 1) x := hτ x (hsub (hJ i hx))
    have hpx : ftPrincipal τ x = β := by rw [ftPrincipal_congr hτx]; exact hcon
    refine hamp i x hx ?_
    rw [ftAmp, hpx, hBz, zero_div, neg_zero]
  obtain ⟨ψ, hstate⟩ :=
    exists_rootBranchState_ftBranch hn ha hr hnr hab hsub hJ hfree
  exact rootBranchState_congr hab
    (fun x hx => (ftPrincipal_congr (hτ x (hsub hx))).symm) hstate

end ForgacsTran
