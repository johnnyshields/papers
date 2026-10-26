/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalPhaseChoice

/-!
# Maximal resolving margin of actual finite occurrence phases

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
A finite family of actual internal states either has identical shifted full
incoming profiles, or produces every uniform first-discrepancy choice, one
positive maximal resolving margin, and a nonzero discrepancy attaining it.
No first-discrepancy, half-height or maximum-margin premise is supplied.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A finite family of actual occurrence phases either has no shifted full
profile discrepancy, or produces all uniform first choices, their positive
maximal resolving margin, and a genuine nonzero discrepancy attaining it. -/
theorem originalInternal_phase_resolving_margin {I : Type*} [Finite I]
    {n b : ℕ} (P : Profile n)
    (idx : I → ZMod b → Fin (originalSelectedCount (hD := hD) P - 1))
    (d : ℕ) (K : I → ℕ)
    (hheight : ∀ i k, originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P (idx i k)) (originalInternalStateIndex P (idx i k)) = (K i : ℤ))
    (hresponse : ∀ i k, c.originalInternalResidue P (idx i k) =
      c.originalInternalResidue P (idx i 0))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    (∀ i k, (c.originalInternalEndpointProfiles P (idx i k)).1 =
      (c.originalInternalEndpointProfiles P (idx i (k + (d : ZMod b)))).1) ∨
    ∃ choices : I → Option ℕ, ∃ J : ℕ+,
      (∀ i, match choices i with
        | none => ∀ k, (c.originalInternalEndpointProfiles P (idx i k)).1 =
            (c.originalInternalEndpointProfiles P (idx i (k + (d : ZMod b)))).1
        | some w => 0 < w ∧ 2 * w < K i ∧
            (∀ k l, l < w → (c.originalInternalEndpointProfiles P (idx i k)).1.coeff l =
              (c.originalInternalEndpointProfiles P (idx i (k + (d : ZMod b)))).1.coeff l) ∧
            (K i : ℤ) - 2 * (w : ℤ) ≤ (J : ℤ)) ∧
      ∃ i w, choices i = some w ∧ (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) ∧
        ∃ k, (c.originalInternalEndpointProfiles P (idx i k)).1.coeff w -
          (c.originalInternalEndpointProfiles P (idx i (k + (d : ZMod b)))).1.coeff w ≠ 0 := by
  classical
  let := Fintype.ofFinite I
  have hex (i : I) := c.originalInternal_phase_discrepancy_choice P (idx i) d (K i : ℤ)
    (hheight i) (hresponse i) hmax
  choose choices hchoices using hex
  by_cases hnone : ∀ i, choices i = none
  · left
    intro i
    have hi := hchoices i
    simpa only [hnone i] using hi
  let margin := fun i => match choices i with
    | none => 0
    | some w => K i - 2 * w
  let maximum := Finset.univ.sup margin
  have hbound (i : I) : margin i ≤ maximum := Finset.le_sup (Finset.mem_univ i)
  have hpos (i : I) (w : ℕ) (hi : choices i = some w) : 0 < margin i := by
    have hs := hchoices i
    rw [hi] at hs
    have hh : 2 * w < K i := by exact_mod_cast hs.2.1
    simp only [margin, hi]
    exact Nat.sub_pos_of_lt hh
  obtain ⟨i0, hi0⟩ := not_forall.mp hnone
  have hmaximum : 0 < maximum := by
    cases hi : choices i0 with
    | none => exact (hi0 hi).elim
    | some w => exact lt_of_lt_of_le (hpos i0 w hi) (hbound i0)
  let J : ℕ+ := ⟨maximum, hmaximum⟩
  have hattain : ∃ i, margin i = maximum := by
    by_contra hn
    have hlower : maximum ≤ maximum - 1 := by
      apply Finset.sup_le
      intro i _
      have hi := hbound i
      have hne : margin i ≠ maximum := fun he => hn ⟨i, he⟩
      omega
    omega
  have hoption (i : I) : match choices i with
      | none => ∀ k, (c.originalInternalEndpointProfiles P (idx i k)).1 =
          (c.originalInternalEndpointProfiles P (idx i (k + (d : ZMod b)))).1
      | some w => 0 < w ∧ 2 * w < K i ∧
          (∀ k l, l < w → (c.originalInternalEndpointProfiles P (idx i k)).1.coeff l =
            (c.originalInternalEndpointProfiles P (idx i (k + (d : ZMod b)))).1.coeff l) ∧
          (K i : ℤ) - 2 * (w : ℤ) ≤ (J : ℤ) := by
    have hs := hchoices i
    cases hi : choices i with
    | none => simpa only [hi] using hs
    | some w =>
      rw [hi] at hs
      have hh : 2 * w < K i := by exact_mod_cast hs.2.1
      refine ⟨hs.1, hh, hs.2.2.1, ?_⟩
      have hb := hbound i
      simp only [margin, hi] at hb
      change (K i : ℤ) - 2 * (w : ℤ) ≤ (maximum : ℤ)
      have hc : ((K i - 2 * w : ℕ) : ℤ) = (K i : ℤ) - 2 * (w : ℤ) := by
        rw [Nat.cast_sub hh.le, Nat.cast_mul, Nat.cast_ofNat]
      have hbZ : ((K i - 2 * w : ℕ) : ℤ) ≤ (maximum : ℤ) := by exact_mod_cast hb
      rwa [hc] at hbZ
  obtain ⟨i, hi⟩ := hattain
  cases hchoice : choices i with
  | none =>
    have hz : margin i = 0 := by simp only [margin, hchoice]
    omega
  | some w =>
    have hs := hchoices i
    rw [hchoice] at hs
    have hh : 2 * w < K i := by exact_mod_cast hs.2.1
    have hm : K i - 2 * w = maximum := by simpa only [margin, hchoice] using hi
    right
    refine ⟨choices, J, hoption, i, w, hchoice, ?_, hs.2.2.2⟩
    change (K i : ℤ) - 2 * (w : ℤ) = (maximum : ℤ)
    have he := congrArg (fun t : ℕ => (t : ℤ)) hm
    rwa [Nat.cast_sub hh.le, Nat.cast_mul, Nat.cast_ofNat] at he

end SkewCornerDescent.Matrix.SelectedCoordinate
