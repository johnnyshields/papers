/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.OrdinaryWeighted
import SkewMarkedFactor.MixedReadout

/-!
# Unified composition covariance

«Composition covariance» (`lem:covariance`, `eq:ordinary-covariance`, `eq:mixed-covariance`) of
`shields-2026-skew-marked-factor.tex`: for a legal mark the read-outer composition map `Φ`
satisfies `Φ(Q) = 𝓝_η(D) s_{D ∘_η E}` and the Hall and weighted covariance identities, in the
ordinary cases with the multiplier `ξ = δ_p s_E` and offset `θ`, in the mixed cases with the Hall
operator annihilating `Φ` and the weighted identity carrying `χ` and `ρ`.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan MvPolynomial

variable {η : MarkedInner}

/-- **Hall vanishing of the mixed composition map** (`eq:mixed-covariance`, first clause). -/
theorem mixed_hall_zero (hη : η.IsLegal) (hm : η.case.IsMixed) {k : ℕ} (hk : 1 ≤ k) (f : Lambda) :
    pDeriv (k * η.period.toNat) (compositionMap η f) = 0 := by
  have h := intertwine_of_generators (compositionMap η) (pDeriv (k * η.period.toNat))
    (0 : Derivation ℚ Lambda Lambda) 0 (fun j => ?_) f
  · simpa using h
  · obtain ⟨n, hn⟩ := j
    have hX : (X (⟨n, hn⟩ : ℕ+) : Lambda) = hPos n := (hPos_pnat ⟨n, hn⟩).symm
    obtain ⟨hAk, -, -⟩ := normalizers_killed hη.readoutLegal (m := k) (by omega)
    have hnz : (0 : ℤ) < n := by exact_mod_cast hn
    have hD := isConnectedSkew_rowCells (s := 0) (e := (n : ℤ)) hnz
    rw [hX, compositionMap_hPos η hn, derivation_mul_killed _ hAk,
      mixed_period_derivative_zero hη.readoutLegal hm hD (by omega : 0 < k)]
    simp

/-- The outer function in the read-outer convention: `s_D` in the horizontal cases and
`ω(s_D)` in the vertical ones. -/
def readoutOuter (η : MarkedInner) (D : Diagram) : Lambda :=
  if η.case = .b then schurInvolution (cellSchur D) else cellSchur D

/-- **`Φ(Q) = 𝓝_η(D) s_{D ∘_η E}`** (`lem:covariance`) in the read-outer convention. -/
theorem readoutMap_outer (hη : η.IsLegal) {D : Diagram} (hD : IsConnectedSkew D) :
    readoutMap η (readoutOuter η D) = fullNormalizer η D * cellSchur (η.compose D) := by
  unfold readoutMap readoutOuter
  by_cases hb : η.case = .b
  · simp only [hb, if_true, AlgHom.comp_apply]
    rw [schurInvolution_involutive (cellSchur D)]
    exact compositionMap_cellSchur hη hD
  · simp only [hb, if_false]
    exact compositionMap_cellSchur hη hD

/-- **Composition covariance** (`lem:covariance`).  For a legal ordinary mark, the read-outer
map `Φ` satisfies `δ_{kp} Φ = ξ^k Φ δ_k` and `V_{kp} Φ = ξ^k Φ (p V_k + θ δ_k)` with
`ξ = δ_p s_E`, `V_p s_E = θ ξ`, `θ` an integer with `|θ| < p`. -/
theorem ordinary_covariance (hη : η.IsLegal) (ho : η.IsOrdinary) :
    (∀ k : ℕ, 1 ≤ k → ∀ f : Lambda,
      pDeriv (k * η.period.toNat) (readoutMap η f) = xi η ^ k * readoutMap η (pDeriv k f)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ f : Lambda,
      wDeriv (k * η.period.toNat) (readoutMap η f) =
        xi η ^ k * readoutMap η (mixedOp (η.period : ℚ) ((readoutOffset η : ℤ) : ℚ) k f)) ∧
    wDeriv η.period.toNat (cellSchur η.E) = C ((readoutOffset η : ℤ) : ℚ) * xi η ∧
    -η.period < readoutOffset η ∧ readoutOffset η < η.period :=
  ⟨fun _ hk f => readout_hall_covariance hη ho hk f,
    fun _ hk f => readout_weighted_covariance hη ho hk f,
    (wDeriv_period_inner_ordinary hη ho).1, (wDeriv_period_inner_ordinary hη ho).2.1,
    (wDeriv_period_inner_ordinary hη ho).2.2⟩

/-- **Composition covariance, mixed marks** (`eq:mixed-covariance`): `δ_{kp} Φ = 0` and
`V_{kp} Φ = χ^k Φ (p V_k + ρ δ_k)`, `ρ = s - t` the positive phase difference of the case-(d) form
obtained by whole rotation, and `V_p s_E = ρ χ`. -/
theorem mixed_covariance_full (hη : η.IsLegal) (hm : η.case.IsMixed) {s t : ℤ}
    (hph : η.dForm.IsPhases s t) :
    (∀ k : ℕ, 1 ≤ k → ∀ f : Lambda, pDeriv (k * η.period.toNat) (compositionMap η f) = 0) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ f : Lambda,
      wDeriv (k * η.period.toNat) (compositionMap η f) =
        mixedChi η ^ k * compositionMap η (mixedOp (η.period : ℚ) ((s - t : ℤ) : ℚ) k f)) ∧
    wDeriv η.period.toNat (cellSchur η.E) = C ((s - t : ℤ) : ℚ) * mixedChi η :=
  ⟨fun _ hk f => mixed_hall_zero hη hm hk f, fun _ hk f => mixed_covariance hη hm hph hk f,
    wDeriv_period_inner_mixed hη hm hph⟩

end SkewMarkedFactor
