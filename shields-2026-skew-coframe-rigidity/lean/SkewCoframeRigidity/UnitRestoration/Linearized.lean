/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.LinearizedInputs
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadData

/-!
# Zero-free linearized fixed-cap rigidity

Formalizes `sc:linearized-cap` in `shields-2026-skew-coframe-rigidity.tex`: for actual connected
zero-free diagrams `B` and `K`, constant weights `ρ` on the genuine vacancies of `B` with
`ṡ_B = 0` and `ṡ_{K ◁ B} = 0` as whole polynomial identities vanish identically.

The proof is the strong induction on the span.  The head step (`linearized_head_step`) produces
either a gap equation `ρ_b s_G = 0`, impossible since `s_G ≠ 0`, or a strict block `E` of smaller
span with `s_E ṡ_N = s_N ṡ_E`; `strict_block_vanishing` turns that into `ṡ_E = ṡ_N = 0`, and the
induction hypothesis on the child `E` with the cap `K_E` gives `ρ_E = 0`, a contradiction.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence MvPolynomial

/-- **Zero-free linearized fixed-cap rigidity** (`sc:linearized-cap`). -/
theorem linearized_cap {k b : ℕ} (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1))
    (hK : IsNorm K) (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected)
    (hKz : ZeroFree K) (hBz : ZeroFree B) (ρ : ℤ →₀ ℚ)
    (hρ : ∀ x ∈ ρ.support, IsVacancy B x)
    (h1 : dotW B ρ = 0) (h2 : dotW (splice K B hK hB) ρ = 0) : ρ = 0 := by
  suffices H : ∀ s : ℕ, ∀ {k b : ℕ} (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1))
      (hK : IsNorm K) (hB : IsNorm B), K.Connected → B.Connected → ZeroFree K → ZeroFree B →
      B.largestLabel.toNat = s → ∀ ρ : ℤ →₀ ℚ, (∀ x ∈ ρ.support, IsVacancy B x) →
      dotW B ρ = 0 → dotW (splice K B hK hB) ρ = 0 → ρ = 0 from
    H _ K B hK hB hKc hBc hKz hBz rfl ρ hρ h1 h2
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro k b K B hK hB hKc hBc hKz hBz hs ρ hρ h1 h2
    by_contra hne
    rcases linearized_head_step K B hK hB hKc hBc hKz hBz ρ hρ hne h1 h2 with
      ⟨g, G, x, hx, hG⟩ | ⟨p, e, hpe, hcut, hin, hρE0, hρt, hsurv⟩
    · exact (mul_ne_zero (by simpa using hx) G.schur_ne_zero) hG
    · have heq := block_equation B hpe hBz hBc hcut ρ hρ hρt hsurv
      have hvacE : ∀ x ∈ (restrictBlock ρ (blockLeast B hpe) (blockHead B hpe)).support,
          IsVacancy (blockBoard B hpe hBz hBc) x := fun x hx => by
        obtain ⟨hs, h0, h1'⟩ := mem_support_restrictBlock hx
        have hv := hρ _ hs
        exact blockBoard_isVacancy B hpe hBz hBc hB h0 h1' hv.2.2.1 hv.2.2.2
      have hvac : ∀ x ∈ (restrictBlock ρ (blockLeast B hpe) (blockHead B hpe)).support,
          (∀ i, (blockBoard B hpe hBz hBc).row i ≠ x) ∧
            ∀ j, (blockBoard B hpe hBz hBc).col j ≠ x :=
        fun x hx => ⟨(hvacE x hx).2.2.1, (hvacE x hx).2.2.2⟩
      have hEn := blockBoard_isNorm B hpe hBz hBc
      have hKn := capOfPrefix_isNorm B (by omega : p + 1 ≤ b) hcut
      have hEc := blockBoard_connected B hpe hBz hBc hin
      have hKEc := capOfPrefix_connected B (by omega : p + 1 ≤ b) hBc hcut
      have hEz := blockBoard_zeroFree B hpe hBz hBc
      have hKEz := capOfPrefix_zeroFree B (by omega : p + 1 ≤ b) hBz hcut
      obtain ⟨hE0, hN0⟩ := strict_block_vanishing (blockBoard B hpe hBz hBc)
        (capOfPrefix B (by omega : p + 1 ≤ b) hcut) hEn hKn hEc hKEc hEz _ hvac heq
      have hlt := blockBoard_largestLabel_lt B hpe hBz hBc hB
      have hBpos := B.largestLabel_pos
      exact hρE0 (ih (blockBoard B hpe hBz hBc).largestLabel.toNat (by omega)
        (capOfPrefix B (by omega : p + 1 ≤ b) hcut) (blockBoard B hpe hBz hBc) hKn hEn hKEc hEc
        hKEz hEz rfl _ hvacE hE0 hN0)
end SkewCoframeRigidity.UnitRestoration
