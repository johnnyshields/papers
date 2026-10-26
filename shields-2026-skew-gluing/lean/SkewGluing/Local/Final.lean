import SkewGluing.Local.EmptyMark
import SkewGluing.Local.Injective

/-!
# Composition with a legal mark: connectedness and injectivity for every legal mark

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (3), the
paragraph after `eq:gluing-mixed-profile`).

Combines the nonempty and the empty marks: for every legal marked inner `ω` and connected outer
`D`, `D ∘_ω E` is a connected skew diagram, and composition with `ω` is injective on connected
outers up to translation.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner} {D D' : Diagram}

/-- **Fixed-chart injectivity, empty mark.** -/
theorem IsLegalEmpty.injective_compose (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D)
    (hD' : IsConnectedSkew D') {t : ℤ × ℤ}
    (hF : ω.compose D' = translate t (ω.compose D)) : ∃ u, D' = translate u D := by
  have hq := h.period_pos
  have hw := h.width_zero
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, h.case_a]
  obtain ⟨hct, hsp⟩ := h.1.shift_data hD hD' hF
  have hcD := h.classRows hD
  have hcD' := h.classRows hD'
  have key : ∀ J, minContent D ≤ J → J ≤ maxContent D →
      ω.oRowLo D' (J + (minContent D' - minContent D)) = ω.oRowLo D J + t.1 ∧
      ω.oRowHi D' (J + (minContent D' - minContent D)) = ω.oRowHi D J + t.1 := by
    intro J h1 h2
    have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J 0 := Or.inl ⟨h1, h2⟩
    have hv' : ValidClass (minContent D') (maxContent D') ω.widthZ
        (J + (minContent D' - minContent D)) 0 := Or.inl ⟨by omega, by omega⟩
    have r1 := hcD.diagLo_eq (le_refl _) hq hv
    have r1' := hcD.diagHi_eq (le_refl _) hq hv
    have r2 := hcD'.diagLo_eq (le_refl _) hq hv'
    have r2' := hcD'.diagHi_eq (le_refl _) hq hv'
    have hk : minContent ω.E + (J * ω.period + 0) ∈ contents (ω.compose D) :=
      (hcD.mem_contents (le_refl _) hq).mpr hv
    have e : minContent ω.E + ((J + (minContent D' - minContent D)) * ω.period + 0) =
        (minContent ω.E + (J * ω.period + 0)) + content t := by
      rw [hct]; ring
    have d1 := diagLo_translate t _ hk
    have d2 := diagHi_translate t _ hk
    rw [← hF, ← e] at d1 d2
    rw [r1, r2] at d1
    rw [r1', r2'] at d2
    have h0 := h.ends.1
    constructor <;> omega
  have ht := ordT_cases hmix
  have hsp1 := span_eq_of_isConnectedSkew hD
  have hsp2 := span_eq_of_isConnectedSkew hD'
  have hbits : ∀ k : ℕ, 1 ≤ k → k < span D →
      bitA D (minContent D + k) = bitA D' (minContent D' + k) ∧
      bitB D (minContent D + k) = bitB D' (minContent D' + k) := by
    intro k hk1 hk2
    have k1 := key (minContent D + k - 1) (by omega) (by omega)
    have k2 := key (minContent D + k) (by omega) (by omega)
    have e1 : minContent D' + (k : ℤ) = (minContent D + k) + (minContent D' - minContent D) := by
      ring
    have e2 : minContent D' + (k : ℤ) - 1 =
        (minContent D + k - 1) + (minContent D' - minContent D) := by ring
    have b1 := bits_ord hmix D (minContent D + k)
    have b2 := bits_ord hmix D' (minContent D' + k)
    rw [e2, e1] at b2
    rw [e1]
    constructor <;> omega
  exact eq_translate_of_bits hD hD' (by omega) (fun k hk1 hk2 => (hbits k hk1 hk2).1)
    (fun k hk1 hk2 => (hbits k hk1 hk2).2) |>.imp fun u hu => hu

/-- **`lem:gluing-local` (3), connectedness, every legal mark.**  For a legal marked inner `ω`
(empty or nonempty) and a connected outer `D`, `D ∘_ω E` is a connected skew diagram. -/
theorem IsLegal.isConnectedSkew_compose (h : ω.IsLegal) (hD : IsConnectedSkew D) :
    IsConnectedSkew (ω.compose D) := by
  by_cases hW : ω.W = ∅
  · exact IsLegalEmpty.isConnectedSkew_compose ⟨h, hW⟩ hD
  · exact IsLegalNonempty.isConnectedSkew_compose ⟨h, Finset.nonempty_iff_ne_empty.mpr hW⟩ hD

/-- **Fixed-chart injectivity, every legal mark.**  Composition with a fixed legal marked inner is
injective on connected outers up to translation: ordinary marks read the private cells
`e_∘ + L_ω(D_j)`, mixed marks the profile (`eq:gluing-mixed-profile`). -/
theorem IsLegal.injective_compose (h : ω.IsLegal) (hD : IsConnectedSkew D)
    (hD' : IsConnectedSkew D') {t : ℤ × ℤ} (hF : ω.compose D' = translate t (ω.compose D)) :
    ∃ u, D' = translate u D := by
  by_cases hW : ω.W = ∅
  · exact IsLegalEmpty.injective_compose ⟨h, hW⟩ hD hD' hF
  · exact IsLegalNonempty.injective_compose ⟨h, Finset.nonempty_iff_ne_empty.mpr hW⟩ hD hD' hF

end MarkedInner

end SkewGluing
