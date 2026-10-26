/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Rot3.lean`. -/
import GluingCore.Aligned.CaseD.Rot2

/-!
# Aligned marks, case (d): the nested count for a lower mark of case (c)

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-nested-count`, case (c) "by rotation").

For `μ` of case (c), `C ∘_μ V` is the rotation of `C* ∘_{μ*} V*` with `μ*` the lower mark of
`V* = rotate V` of case (d) (`alD_lowerMark_rotate`, `compose_rotate_c`), so the nested count
`alD_NC` for `(V, C)` follows from the nested count for `(V*, C*)`, by the reflections of the
profiles (`alD_profM_rotate`, `alD_profS_rotate`).

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {V C : Diagram} {a θ : ℤ}

theorem alD_Om_rotate (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {j : ℤ} (h0 : 0 ≤ j)
    (h1 : j < (span V : ℤ) - a) :
    alD_Om (GluingCore.rotate V) a θ ((span V : ℤ) - a - 1 - j) = alD_Om V a θ j := by
  have hap := hD.ha
  have l1 := alD_L_rotate hV (j := (span V : ℤ) - a - 1 - j) (by omega) (by omega)
  have l2 := alD_L_rotate hV (j := (span V : ℤ) - a - 1 - j + a) (by omega) (by omega)
  have h1' := alD_H_rotate hV (j := (span V : ℤ) - a - 1 - j) (by omega) (by omega)
  have h2 := alD_H_rotate hV (j := (span V : ℤ) - a - 1 - j + a) (by omega) (by omega)
  have i1 : (span V : ℤ) - 1 - ((span V : ℤ) - a - 1 - j) = j + a := by ring
  have i2 : (span V : ℤ) - 1 - ((span V : ℤ) - a - 1 - j + a) = j := by ring
  rw [i1] at l1 h1'
  rw [i2] at l2 h2
  unfold alD_Om alD_zl alD_zh
  omega

theorem alD_d_bounds (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {i : ℤ} (h0 : 0 ≤ i)
    (h1 : i ≤ (span V : ℤ) - a) :
    -1 ≤ walkDelta V a (2 * (minContent V + i)) ∧ walkDelta V a (2 * (minContent V + i)) ≤ 1 := by
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := aligned_span_eq hV
  rw [alD_walk_even_eq]
  by_cases hi0 : i = 0
  · subst hi0
    have e0 : minContent V + 0 + a = minContent V + a := by ring
    have hS0 : profS V (minContent V + 0) = 1 := aligned_profS_eq_one (by omega)
    have hSa : profS V (minContent V + a) = alD_H V (a - 1) - alD_L V a + 1 :=
      alD_profS_V_eq hV (by omega) (by omega)
    rw [e0, hS0, hSa]
    have hsa := hD.singleton_a
    have st := alD_step hV (j := a) (by omega) (by omega)
    omega
  · have e2 : minContent V + i + a = minContent V + (i + a) := by ring
    rw [e2]
    by_cases hib : i = (span V : ℤ) - a
    · subst hib
      have hSb : profS V (minContent V + ((span V : ℤ) - a)) =
          alD_H V ((span V : ℤ) - a - 1) - alD_L V ((span V : ℤ) - a) + 1 :=
        alD_profS_V_eq hV (by omega) (by omega)
      have hSout : profS V (minContent V + (((span V : ℤ) - a) + a)) = 1 :=
        aligned_profS_eq_one (by omega)
      rw [hSb, hSout]
      have hl := hD.d_last
      have hel := alD_e_last hV hD
      unfold alD_e at hl hel
      omega
    · have hSi : profS V (minContent V + i) = alD_H V (i - 1) - alD_L V i + 1 :=
        alD_profS_V_eq hV (by omega) (by omega)
      have hSia : profS V (minContent V + (i + a)) = alD_H V (i + a - 1) - alD_L V (i + a) + 1 :=
        alD_profS_V_eq hV (by omega) (by omega)
      rw [hSi, hSia]
      have hdb := hD.d_bd i (by omega) (by omega)
      have e1 := hD.e_bd i (by omega) (by omega)
      have e0 := hD.e_bd (i - 1) (by omega) (by omega)
      unfold alD_d at hdb
      omega

theorem alD_walk_rotate (hV : IsConnectedSkew V) (k : ℤ) :
    walkDelta (GluingCore.rotate V) a k = - walkDelta V a (2 - k - 2 * a) := by
  unfold walkDelta
  rw [alD_profIL_rotate hV, alD_profIL_rotate hV]
  have e : 2 - (k + 2 * a) + 2 * a = 2 - k := by ring
  have e2 : 2 - (k + 2 * a) = 2 - k - 2 * a := by ring
  rw [e2]
  have e3 : 2 - k - 2 * a + 2 * a = 2 - k := by ring
  rw [e3]
  ring

/-- Common data for the passage from a lower mark of case (c) to its rotation. -/
theorem alD_NCc_setup (hV : IsConnectedSkew V) (hD : alD_Data V a θ) (hC : IsConnectedSkew C)
    (hc : (alD_lowerMark V a θ).case = .c) :
    IsConnectedSkew ((alD_lowerMark (GluingCore.rotate V) a θ).compose (GluingCore.rotate C)) ∧
    (alD_lowerMark V a θ).compose C =
      GluingCore.rotate ((alD_lowerMark (GluingCore.rotate V) a θ).compose
        (GluingCore.rotate C)) := by
  have hV' := isConnectedSkew_rotate hV
  have hD' := alD_data_rotate hV hD
  have hC' := isConnectedSkew_rotate hC
  have hY := (alD_lowerMark_isLegal hV' hD').isConnectedSkew_compose hC'
  refine ⟨hY, ?_⟩
  rw [← alD_lowerMark_rotate]
  exact compose_rotate_c hc hC.2.1

end MarkedInner

end GluingCore
