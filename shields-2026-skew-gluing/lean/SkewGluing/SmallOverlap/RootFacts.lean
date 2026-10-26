import SkewGluing.SmallOverlap.Drift
import SkewGluing.SmallOverlap.FirstBlock
import SkewGluing.SmallOverlap.EmptyFold

/-!
# Heights of a width-one root

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`): the height of a diagram with a proper root of width one and period
`p` is one at the position `p - 1` (the last private diagonal of the inner is a singleton) and at
the position `1`.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

theorem heightWord_congr {A B A' B' : ℕ → ℤ} {n : ℕ} (hA : ∀ k, 1 ≤ k → k ≤ n → A k = A' k)
    (hB : ∀ k, 1 ≤ k → k ≤ n → B k = B' k) : heightWord A B n = heightWord A' B' n := by
  induction n with
  | zero => simp [heightWord]
  | succ n ih =>
    rw [heightWord_succ, heightWord_succ, ih (fun k h1 h2 => hA k h1 (by omega))
      (fun k h1 h2 => hB k h1 (by omega)), hA (n + 1) (by omega) le_rfl,
      hB (n + 1) (by omega) le_rfl]

/-- The height at the position `p - 1` of a diagram with a width-one proper root of period `p`. -/
theorem _root_.SkewGluing.Chart.IsProperRoot.heightWord_pen {χ : Chart} {F : Diagram} {p : ℕ}
    (h : χ.IsProperRoot F p) (hw : χ.ω.width = 1) :
    heightWord (wA F) (wB F) (p - 1) = 1 := by
  have hW := h.W_nonempty_of_width_one hw
  have hlegal : χ.ω.IsLegalNonempty := ⟨h.1.2.2.2, hW⟩
  have hwZ : χ.ω.widthZ = 1 := by unfold MarkedInner.widthZ; omega
  have hD := h.1.1
  obtain ⟨hr, hN, hwq, hp2⟩ := h.arith
  have hperZ : χ.ω.period = (p : ℤ) := h.2.2
  have hE := hlegal.isConnectedSkew_E
  have hEsp : (span χ.ω.E : ℤ) = p + 1 := by
    have := h.1.2.2.2.1.span_eq
    rw [hperZ] at this
    omega
  have hbd := isBitData_of_isConnectedSkew hE
  obtain ⟨-, -, -, hl⟩ := hbd
  have hEn : span χ.ω.E - 1 = p := by omega
  rw [hEn] at hl
  have hsF := h.span_eq
  have hspF : (span F : ℤ) = (span χ.D : ℤ) * p + 1 := by rw [hN, hw]; push_cast; ring
  have hsd : (2 : ℤ) ≤ span χ.D := by exact_mod_cast hr
  have hp2' : (2 : ℤ) ≤ p := by exact_mod_cast hp2
  have hpF : (p : ℤ) < span F := by nlinarith
  have hfirst : ∀ k : ℕ, 1 ≤ k → k ≤ p - 1 →
      wA F k = bitA χ.ω.E (minContent χ.ω.E + k) ∧ wB F k = bitB χ.ω.E (minContent χ.ω.E + k) := by
    intro k hk1 hk2
    have hk2' : (k : ℤ) < span F := by omega
    obtain ⟨e1, e2⟩ := wordAB_compose_first h.1.2.2.2 hD (k := k) (by omega)
      (by rw [show χ.ω.period = p from hperZ]; omega)
    exact ⟨by simpa [wA, h.wordA_eq (k := k) (by omega) hk2', Chart.parent] using e1,
      by simpa [wB, h.wordB_eq (k := k) (by omega) hk2', Chart.parent] using e2⟩
  have hc := heightWord_congr (A := wA F) (B := wB F)
    (A' := fun k => bitA χ.ω.E (minContent χ.ω.E + k))
    (B' := fun k => bitB χ.ω.E (minContent χ.ω.E + k)) (n := p - 1)
    (fun k h1 h2 => (hfirst k h1 h2).1) (fun k h1 h2 => (hfirst k h1 h2).2)
  rw [hc]
  -- the last step of the inner
  have hstep := heightWord_succ (fun k : ℕ => bitA χ.ω.E (minContent χ.ω.E + k))
    (fun k : ℕ => bitB χ.ω.E (minContent χ.ω.E + k)) (p - 1)
  have ep : p - 1 + 1 = p := by omega
  rw [ep] at hstep
  rw [hstep] at hl
  have hbits : bitA χ.ω.E (minContent χ.ω.E + (p : ℕ)) =
      bitB χ.ω.E (minContent χ.ω.E + (p : ℕ)) := by
    have hat := hlegal.attach
    have e1 : minContent χ.ω.E + ((p : ℕ) : ℤ) - 1 = minContent χ.ω.E + (χ.ω.period - 1) := by
      rw [hperZ]; ring
    have e2 : minContent χ.ω.E + ((p : ℕ) : ℤ) = minContent χ.ω.E + χ.ω.period := by
      rw [hperZ]
    have key : χ.ω.lo (χ.ω.period - 1) - χ.ω.lo χ.ω.period =
        χ.ω.hi (χ.ω.period - 1) - χ.ω.hi χ.ω.period := by
      cases hcase : χ.ω.case
      · have := hlegal.upperH_bits_one hwZ ((hat.1 hcase).2); omega
      · have := hlegal.upperV_bits_one hwZ ((hat.2.1 hcase).2); omega
      · have := hlegal.upperV_bits_one hwZ ((hat.2.2.1 hcase).2); omega
      · have := hlegal.upperH_bits_one hwZ ((hat.2.2.2 hcase).2); omega
    unfold bitA bitB
    rw [e1, e2]
    exact key
  omega

end SmallOverlap
end SkewGluing
