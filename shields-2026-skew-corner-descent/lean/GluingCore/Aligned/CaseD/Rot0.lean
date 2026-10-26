/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Rot0.lean`. -/
import GluingCore.Aligned.CaseD.NcD

/-!
# Aligned marks, case (d): the rotated lower mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, case (c) "by rotation").

Rotation of `V` reflects the rows of its diagonals, `alD_L (rotate V) j = - alD_H V (N - 1 - j)` and
`alD_H (rotate V) j = - alD_L V (N - 1 - j)` (`alD_L_rotate`, `alD_H_rotate`), and the data
`alD_Data V a θ` of the lower mark are reflected to `alD_Data (rotate V) a θ`
(`alD_data_rotate`).

Sorry-free.
-/

namespace GluingCore

section Rot

variable {V : Diagram} {a θ : ℤ}

theorem alD_minContent_rotate (hV : IsConnectedSkew V) :
    minContent (rotate V) = -(minContent V + ((span V : ℤ) - 1)) := by
  have hne := hV.2.1
  have := minContent_rotate hne
  have hsp := span_eq_of_isConnectedSkew hV
  omega

theorem alD_L_rotate (hV : IsConnectedSkew V) {j : ℤ} (_h0 : 0 ≤ j) (_h1 : j < (span V : ℤ)) :
    alD_L (rotate V) j = - alD_H V ((span V : ℤ) - 1 - j) := by
  unfold alD_L alD_H
  rw [alD_minContent_rotate hV]
  have e : -(minContent V + ((span V : ℤ) - 1)) + j = -(minContent V + ((span V : ℤ) - 1 - j)) := by
    ring
  rw [e, diagLo_rotate]

theorem alD_H_rotate (hV : IsConnectedSkew V) {j : ℤ} (_h0 : 0 ≤ j) (_h1 : j < (span V : ℤ)) :
    alD_H (rotate V) j = - alD_L V ((span V : ℤ) - 1 - j) := by
  unfold alD_L alD_H
  rw [alD_minContent_rotate hV]
  have e : -(minContent V + ((span V : ℤ) - 1)) + j = -(minContent V + ((span V : ℤ) - 1 - j)) := by
    ring
  rw [e, diagHi_rotate]
  simp

theorem alD_span_rotate : (span (rotate V) : ℤ) = (span V : ℤ) := by
  rw [span_rotate]

theorem alD_e_rot (hV : IsConnectedSkew V) (ha : 0 ≤ a) {j : ℤ} (h0 : 0 ≤ j)
    (h1 : j + a < (span V : ℤ)) :
    alD_e (rotate V) a j = - alD_e V a ((span V : ℤ) - 1 - a - j) := by
  have l1 := alD_L_rotate hV (j := j) h0 (by omega)
  have l2 := alD_L_rotate hV (j := j + a) (by omega) h1
  have h1' := alD_H_rotate hV (j := j) h0 (by omega)
  have h2 := alD_H_rotate hV (j := j + a) (by omega) h1
  have i1 : (span V : ℤ) - 1 - (j + a) = (span V : ℤ) - 1 - a - j := by ring
  have i2 : (span V : ℤ) - 1 - a - j + a = (span V : ℤ) - 1 - j := by ring
  rw [i1] at l2 h2
  unfold alD_e
  rw [i2]
  omega

theorem alD_d_rot (hV : IsConnectedSkew V) (ha : 0 ≤ a) {j : ℤ} (h0 : 1 ≤ j)
    (h1 : j + a < (span V : ℤ)) :
    alD_d (rotate V) a j = - alD_d V a ((span V : ℤ) - a - j) := by
  have l1 := alD_L_rotate hV (j := j) (by omega) (by omega)
  have l2 := alD_L_rotate hV (j := j + a) (by omega) (by omega)
  have h1' := alD_H_rotate hV (j := j - 1) (by omega) (by omega)
  have h2 := alD_H_rotate hV (j := j + a - 1) (by omega) (by omega)
  have i1 : (span V : ℤ) - 1 - (j + a) = (span V : ℤ) - a - j - 1 := by ring
  have i2 : (span V : ℤ) - 1 - (j - 1) = (span V : ℤ) - j := by ring
  have i3 : (span V : ℤ) - 1 - (j + a - 1) = (span V : ℤ) - a - j := by ring
  have i4 : (span V : ℤ) - a - j + a - 1 = (span V : ℤ) - j - 1 := by ring
  have i5 : (span V : ℤ) - a - j + a = (span V : ℤ) - j := by ring
  have i6 : (span V : ℤ) - 1 - j = (span V : ℤ) - j - 1 := by ring
  rw [i1] at l2
  rw [i2] at h1'
  rw [i3] at h2
  rw [i6] at l1
  unfold alD_d
  rw [i5]
  omega

theorem alD_data_rotate (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    alD_Data (rotate V) a θ := by
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hsp := alD_span_rotate (V := V)
  have hN : (span V : ℤ) = (span V : ℤ) := rfl
  refine ⟨hap, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [alD_span_rotate (V := V)]
  · intro j h0 h1
    have h1' : j < (span V : ℤ) - a := by omega
    rw [alD_e_rot hV hap.le h0 (by omega)]
    have := hD.e_bd ((span V : ℤ) - 1 - a - j) (by omega) (by omega)
    omega
  · intro j h0 h1
    have h1' : j + 1 < (span V : ℤ) - a := by omega
    rw [alD_e_rot hV hap.le h0 (by omega), alD_e_rot hV hap.le (by omega) (by omega)]
    have := hD.e_mono ((span V : ℤ) - 1 - a - (j + 1)) (by omega) (by omega)
    have e : (span V : ℤ) - 1 - a - (j + 1) + 1 = (span V : ℤ) - 1 - a - j := by ring
    rw [e] at this
    omega
  · intro j h0 h1
    have h1' : j < (span V : ℤ) - a := by omega
    rw [alD_e_rot hV hap.le (by omega : 0 ≤ j - 1) (by omega), alD_d_rot hV hap.le h0 (by omega),
      alD_e_rot hV hap.le (by omega) (by omega)]
    have := hD.d_bd ((span V : ℤ) - a - j) (by omega) (by omega)
    have e : (span V : ℤ) - 1 - a - (j - 1) = (span V : ℤ) - a - j := by ring
    have e2 : (span V : ℤ) - a - j - 1 = (span V : ℤ) - 1 - a - j := by ring
    rw [e]
    rw [e2] at this
    omega
  · -- `d_last`
    have h1' := alD_H_rotate hV (j := (span V : ℤ) - a - 1) (by omega) (by omega)
    have l1 := alD_L_rotate hV (j := (span V : ℤ) - a) (by omega) (by omega)
    have e1 := alD_e_rot hV hap.le (j := (span V : ℤ) - a - 1) (by omega) (by omega)
    have i1 : (span V : ℤ) - 1 - ((span V : ℤ) - a - 1) = a := by ring
    have i2 : (span V : ℤ) - 1 - ((span V : ℤ) - a) = a - 1 := by ring
    have i3 : (span V : ℤ) - 1 - a - ((span V : ℤ) - a - 1) = 0 := by ring
    rw [i1] at h1'
    rw [i2] at l1
    rw [i3] at e1
    have hf := hD.d_first
    have hsa := hD.singleton_a
    have st := alD_step hV (j := a) (by omega) (by omega)
    rw [e1, h1', l1]
    unfold alD_e at hf ⊢
    omega
  · -- `d_first`
    have l1 := alD_L_rotate hV (j := a) (by omega) (by omega)
    have h1' := alD_H_rotate hV (j := a - 1) (by omega) (by omega)
    have e1 := alD_e_rot hV hap.le (j := 0) le_rfl (by omega)
    have i1 : (span V : ℤ) - 1 - a = (span V : ℤ) - a - 1 := by ring
    have i2 : (span V : ℤ) - 1 - (a - 1) = (span V : ℤ) - a := by ring
    rw [i1] at l1
    rw [i2] at h1'
    have := hD.d_last.1
    rw [sub_zero, i1] at e1
    rw [e1, l1, h1']
    unfold alD_e at this ⊢
    omega
  · -- `singleton_b`
    have h1' := alD_H_rotate hV (j := (span V : ℤ) - a) (by omega) (by omega)
    have l1 := alD_L_rotate hV (j := (span V : ℤ) - a) (by omega) (by omega)
    have i2 : (span V : ℤ) - 1 - ((span V : ℤ) - a) = a - 1 := by ring
    rw [i2] at h1' l1
    have := hD.singleton_a
    omega
  · -- `singleton_a`
    have h1' := alD_H_rotate hV (j := a - 1) (by omega) (by omega)
    have l1 := alD_L_rotate hV (j := a - 1) (by omega) (by omega)
    have i2 : (span V : ℤ) - 1 - (a - 1) = (span V : ℤ) - a := by ring
    rw [i2] at h1' l1
    have := hD.singleton_b
    omega
  · intro j h0 h1
    have h1' : j < (span V : ℤ) - a := by omega
    have t := hD.th1 ((span V : ℤ) - 1 - a - j) (by omega) (by omega)
    have i1 : (span V : ℤ) - 1 - a - j + a = (span V : ℤ) - 1 - j := by ring
    have i2 : (span V : ℤ) - 1 - (j + a) = (span V : ℤ) - 1 - a - j := by ring
    rw [i1] at t
    have l1 := alD_L_rotate hV (j := j) h0 (by omega)
    have l2 := alD_L_rotate hV (j := j + a) (by omega) (by omega)
    have h1'' := alD_H_rotate hV (j := j) h0 (by omega)
    have h2 := alD_H_rotate hV (j := j + a) (by omega) (by omega)
    rw [i2] at l2 h2
    omega
  · intro j h0 h1
    have h1' : j < (span V : ℤ) - a := by omega
    have t := hD.th2 ((span V : ℤ) - a - j) (by omega) (by omega)
    have i1 : (span V : ℤ) - a - j - 1 + a = (span V : ℤ) - j - 1 := by ring
    have i2 : (span V : ℤ) - a - j + a = (span V : ℤ) - j := by ring
    rw [i1, i2] at t
    have i3 : (span V : ℤ) - 1 - (j - 1 + a) = (span V : ℤ) - a - j := by ring
    have i4 : (span V : ℤ) - 1 - (j - 1) = (span V : ℤ) - j := by ring
    have i5 : (span V : ℤ) - 1 - (j + a) = (span V : ℤ) - a - j - 1 := by ring
    have i6 : (span V : ℤ) - 1 - j = (span V : ℤ) - j - 1 := by ring
    have h3 := alD_H_rotate hV (j := j - 1 + a) (by omega) (by omega)
    have h4 := alD_H_rotate hV (j := j - 1) (by omega) (by omega)
    have l1 := alD_L_rotate hV (j := j + a) (by omega) (by omega)
    have l2 := alD_L_rotate hV (j := j) (by omega) (by omega)
    rw [i3] at h3
    rw [i4] at h4
    rw [i5] at l1
    rw [i6] at l2
    omega

end Rot

end GluingCore
