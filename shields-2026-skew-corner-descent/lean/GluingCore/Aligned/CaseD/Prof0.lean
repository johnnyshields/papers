/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Prof0.lean`. -/
import GluingCore.Aligned.CaseD.Legal2

/-!
# Aligned marks, case (d): the profile of `C ∘_μ V`, preliminaries

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`eq:gluing-nested-count`).

For the lower mark `μ = alD_lowerMark V a θ` (data `alD_Data V a θ`, `b = N_V - a`), the diagonal
rows of `μ`, its offsets `dLo`, `dHi` and the height `Ω_i = alD_Om V a θ i` of its copy `Z` on the
diagonal `i` in terms of `alD_L`, `alD_H`, `alD_zl`, `alD_zh`; the term `alD_CT C e J` of
`eq:gluing-nested-count` (`e = -1, 0, 1`); and `μ` is a legal mark with a nonempty copy.

Sorry-free.
-/

namespace GluingCore

/-- The term of `eq:gluing-nested-count`: `M^C_{J-1}` for `e = -1`, `S^C_J - 1` for `e = 0` and
`M^C_J` for `e = 1`. -/
def alD_CT (C : Diagram) (e J : ℤ) : ℤ :=
  if e = -1 then profM C (J - 1) else if e = 0 then profS C J - 1 else profM C J

/-- The height of `Z` on the diagonal `i`. -/
def alD_Om (V : Diagram) (a θ i : ℤ) : ℤ := alD_zh V a θ i - alD_zl V a θ i + 1

section Basic

variable {V : Diagram} {a θ : ℤ}

theorem alD_hμ (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_lowerMark V a θ).IsLegalNonempty :=
  ⟨alD_lowerMark_isLegal hV hD, alD_Z_nonempty hV hD⟩

theorem alD_μ_widthZ (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_lowerMark V a θ).widthZ = (span V : ℤ) - a := alD_width hV hD

theorem alD_μ_lo (k : ℤ) : (alD_lowerMark V a θ).lo k = alD_L V k := rfl
theorem alD_μ_hi (k : ℤ) : (alD_lowerMark V a θ).hi k = alD_H V k := rfl
theorem alD_μ_rowShift : (alD_lowerMark V a θ).rowShift = θ := rfl
theorem alD_μ_minContent : minContent (alD_lowerMark V a θ).E = minContent V := rfl

theorem alD_μ_dLo (i : ℤ) :
    (alD_lowerMark V a θ).dLo i = alD_L V (i + a) - θ - alD_L V i := by
  unfold MarkedInner.dLo
  rw [alD_lowerMark_period]; rfl

theorem alD_μ_dHi (i : ℤ) :
    (alD_lowerMark V a θ).dHi i = alD_H V (i + a) - θ - alD_H V i := by
  unfold MarkedInner.dHi
  rw [alD_lowerMark_period]; rfl

theorem alD_e_eq (i : ℤ) :
    alD_e V a i = (alD_lowerMark V a θ).dLo i - (alD_lowerMark V a θ).dHi i := by
  rw [alD_μ_dLo, alD_μ_dHi]
  unfold alD_e
  ring

theorem alD_diagHi_Z (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {i : ℤ} (h0 : 0 ≤ i)
    (h1 : i < (span V : ℤ) - a) :
    diagHi (alD_Z V a θ) (minContent V + i) = alD_zh V a θ i := by
  have z := alD_zrows hV hD h0 h1
  apply diagHi_eq_of (l := alD_zh V a θ i)
  · have := (alD_mem_Z hV hD.ha.le (alD_zh V a θ i) i).mpr
      ⟨h0, by omega, z.2.1, le_rfl⟩
    exact this
  · intro r hr
    have := (alD_mem_Z hV hD.ha.le r i).mp (by
      have e : r + (minContent V + i) = r + (minContent V + i) := rfl
      exact hr)
    exact this.2.2.2

theorem alD_diagLo_Z (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {i : ℤ} (h0 : 0 ≤ i)
    (h1 : i < (span V : ℤ) - a) :
    diagLo (alD_Z V a θ) (minContent V + i) = alD_zl V a θ i := by
  have z := alD_zrows hV hD h0 h1
  apply diagLo_eq_of (l := alD_zl V a θ i)
  · exact (alD_mem_Z hV hD.ha.le (alD_zl V a θ i) i).mpr
      ⟨h0, by omega, le_rfl, z.2.1⟩
  · intro r hr
    have := (alD_mem_Z hV hD.ha.le r i).mp hr
    exact this.2.2.1

theorem alD_height_W (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {i : ℤ} (h0 : 0 ≤ i)
    (h1 : i < (span V : ℤ) - a) :
    height (alD_lowerMark V a θ).W (minContent (alD_lowerMark V a θ).E + i) =
      alD_Om V a θ i := by
  unfold height alD_Om
  change diagHi (alD_Z V a θ) (minContent V + i) - diagLo (alD_Z V a θ) (minContent V + i) + 1 = _
  rw [alD_diagHi_Z hV hD h0 h1, alD_diagLo_Z hV hD h0 h1]

end Basic

end GluingCore
