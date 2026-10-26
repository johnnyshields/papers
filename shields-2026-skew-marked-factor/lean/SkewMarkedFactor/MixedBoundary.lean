/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.MixedVanishing

/-!
# The periodic southeast boundary of a mixed composition

Formalizes «Equal functions at a common period» (`sec:transport`,
`eq:mixed-boundary`) of `shields-2026-skew-marked-factor.tex`.
Boundary contents are measured relative to the first occupied diagonal.
-/

namespace SkewMarkedFactor
open Gluing Gluing.MarkedInner

/-- Southeast boundary step on an absolute content diagonal. -/
def southeastStep (F : Diagram) (n : ℤ) : ℤ := diagHi F (n - 1) - diagHi F n

private theorem classRows_hi_shift {F : Diagram} {c q w m M r : ℤ}
    {lo hi : ℤ → ℤ → ℤ} {h : ℤ → ℤ}
    (hc : ClassRows F c q w m M lo hi) (hhi : ∀ j a, hi j a = j * r + h a)
    {n : ℤ} (hn : n ∈ contents F) (hnq : n + q ∈ contents F) :
    diagHi F (n + q) = diagHi F n + r := by
  obtain ⟨j, a, ha0, haq, he⟩ := hc.decomp n
  have heq : n + q = c + ((j + 1) * q + a) := by rw [he]; ring
  have hv := (hc.mem_contents ha0 haq).mp (he ▸ hn)
  have hvq := (hc.mem_contents ha0 haq).mp (heq ▸ hnq)
  rw [heq, he, hc.diagHi_eq ha0 haq hvq, hc.diagHi_eq ha0 haq hv, hhi, hhi]
  ring

/-- The bottom row shifts by the inner row displacement on every occupied period pair. -/
theorem mixed_boundary_hi_shift {η : MarkedInner} (hη : η.IsReadoutLegal)
    (hd : η.case = .d) {D : Diagram} (hD : IsConnectedSkew D)
    {n : ℤ} (hn : n ∈ contents (η.compose D))
    (hnp : n + η.period ∈ contents (η.compose D)) :
    diagHi (η.compose D) (n + η.period) = diagHi (η.compose D) n + η.rowShift := by
  have hl := mixed_readout_legal hη (by rw [hd]; trivial)
  have hW : η.W.Nonempty := by
    rcases hl.1.2 with h | h
    · have hc := h.2.2
      rw [hd] at hc
      cases hc
    · exact h.1
  have h : η.IsLegalNonempty := ⟨hl, hW⟩
  obtain ⟨s, t, hp⟩ := h.exists_phases
  exact classRows_hi_shift (mix_classRows h hD hd hp (h.phases_lt (Or.inr hd) hp))
    (fun _ _ => rfl) hn hnp

/-- Periodicity of the actual southeast boundary, away from both end diagonals. -/
theorem mixed_boundary_periodic {η : MarkedInner} (hη : η.IsReadoutLegal)
    (hd : η.case = .d) {D : Diagram} (hD : IsConnectedSkew D) {n : ℤ}
    (hn0 : n - 1 ∈ contents (η.compose D)) (hn : n ∈ contents (η.compose D))
    (hp0 : n - 1 + η.period ∈ contents (η.compose D))
    (hp : n + η.period ∈ contents (η.compose D)) :
    southeastStep (η.compose D) (n + η.period) = southeastStep (η.compose D) n := by
  have h0 := mixed_boundary_hi_shift hη hd hD hn0 hp0
  have h1 := mixed_boundary_hi_shift hη hd hD hn hp
  unfold southeastStep
  have he : n + η.period - 1 = n - 1 + η.period := by ring
  rw [he, h0, h1]
  ring

/-- The two end steps and the exact span in `eq:mixed-boundary`. -/
theorem mixed_boundary_caps {η : MarkedInner} (hη : η.IsReadoutLegal)
    (hd : η.case = .d) {D : Diagram} (hD : IsConnectedSkew D) :
    southeastStep (η.compose D) (minContent (η.compose D) + η.widthZ) = 1 ∧
      southeastStep (η.compose D) (minContent (η.compose D) + η.period) = 0 ∧
      (span (η.compose D) : ℤ) = η.period * span D + η.widthZ ∧
      0 < η.widthZ ∧ η.widthZ < η.period := by
  have hl := mixed_readout_legal hη (by rw [hd]; trivial)
  have hW : η.W.Nonempty := by
    rcases hl.1.2 with h | h
    · have hc := h.2.2
      rw [hd] at hc
      cases hc
    · exact h.1
  have h : η.IsLegalNonempty := ⟨hl, hW⟩
  obtain ⟨s, t, hp⟩ := h.exists_phases
  have hc := mix_classRows h hD hd hp (h.phases_lt (Or.inr hd) hp)
  have hw := h.width_pos
  have hwq := h.width_lt_period
  have hq := hl.period_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hv : ∀ a : ℤ, ValidClass (minContent D) (maxContent D) η.widthZ
      (minContent D) a := fun _ => Or.inl ⟨le_rfl, hmM⟩
  have hvp : ValidClass (minContent D) (maxContent D) η.widthZ
      (minContent D + 1) 0 := by
    unfold ValidClass
    omega
  have hmin := hl.minContent_compose hD
  have hw0 := hc.diagHi_eq (j := minContent D) (a := η.widthZ - 1)
    (by omega) (by omega) (hv _)
  have hw1 := hc.diagHi_eq (j := minContent D) (a := η.widthZ)
    (by omega) hwq (hv _)
  have hp0 := hc.diagHi_eq (j := minContent D) (a := η.period - 1)
    (by omega) (by omega) (hv _)
  have hp1 := hc.diagHi_eq (j := minContent D + 1) (a := 0)
    (by omega) hq hvp
  obtain ⟨⟨_, hcapw, _⟩, ⟨hc0, _, _⟩⟩ := d_caps h hd
  unfold MarkedInner.dHi at hc0
  simp only [zero_add] at hc0
  simp only [mixHi] at hw0 hw1 hp0 hp1
  have hew : minContent (η.compose D) + η.widthZ - 1 =
      minContent η.E + (minContent D * η.period + (η.widthZ - 1)) := by
    rw [hmin]
    ring
  have hep : minContent (η.compose D) + η.period =
      minContent η.E + ((minContent D + 1) * η.period + 0) := by
    rw [hmin]
    ring
  have hep0 : minContent (η.compose D) + η.period - 1 =
      minContent η.E + (minContent D * η.period + (η.period - 1)) := by
    rw [hmin]
    ring
  have hw0' : diagHi (η.compose D) (minContent (η.compose D) + η.widthZ - 1) =
      minContent D * η.rowShift + η.hi (η.widthZ - 1) := by
    rw [hew]
    exact hw0
  have hw1' : diagHi (η.compose D) (minContent (η.compose D) + η.widthZ) =
      minContent D * η.rowShift + η.hi η.widthZ := by
    rw [hmin, add_assoc]
    exact hw1
  have hp0' : diagHi (η.compose D) (minContent (η.compose D) + η.period - 1) =
      minContent D * η.rowShift + η.hi (η.period - 1) := by
    rw [hep0]
    exact hp0
  have hp1' : diagHi (η.compose D) (minContent (η.compose D) + η.period) =
      (minContent D + 1) * η.rowShift + η.hi 0 := by
    rw [hep]
    exact hp1
  refine ⟨?_, ?_, ?_, by omega, hwq⟩
  · unfold southeastStep
    rw [hw0', hw1']
    omega
  · unfold southeastStep
    rw [hp0', hp1']
    have hcap := (d_caps h hd).2.2.1
    nlinarith
  · simpa only [widthZ, mul_comm] using span_compose hD hl

/-- Periodicity on precisely the southwest-normalized interior range in the paper. -/
theorem mixed_boundary {η : MarkedInner} (hη : η.IsReadoutLegal)
    (hd : η.case = .d) {D : Diagram} (hD : IsConnectedSkew D)
    {t : ℤ} (ht : 1 ≤ t) (htp : t + η.period < span (η.compose D)) :
    southeastStep (η.compose D) (minContent (η.compose D) + t + η.period) =
      southeastStep (η.compose D) (minContent (η.compose D) + t) := by
  have hl := mixed_readout_legal hη (by rw [hd]; trivial)
  have hF := hl.isConnectedSkew_compose hD
  have hs := span_eq_of_isConnectedSkew hF
  have hshape := isConnectedSkew_iff_diagonal.mp hF
  have hq := hl.period_pos
  apply mixed_boundary_periodic hη hd hD
  all_goals
    apply hshape.mem_contents_iff.mpr
    constructor <;> omega

end SkewMarkedFactor
