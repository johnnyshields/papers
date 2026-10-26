/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Mark0.lean`. -/
import GluingCore.Aligned.CaseD.Data

/-!
# Aligned marks, case (d): the lower copy `Z = V ∩ (V - z)`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`).

For `z = (θ, θ + a)` the lower copy of the mark `μ` on `V` is `Z = V ∩ (V - z)`, the middle is
`O = {x ∈ V : x + z ∉ V, x - z ∉ V}`, and the upper copy is `V ∩ (V + z)`.  On the diagonals of
`V` (indexed from `0`, rows `[alD_L, alD_H]`) the copy `Z` has the rows `[zl_j, zh_j]` for
`0 ≤ j < b = N_V - a`.  Under `alD_Data`, `Z` is a connected skew diagram, the middle is thin on
the marked diagonals, and the diagonals `b`, `a - 1` carry no two cells of the middle.

Sorry-free.
-/

namespace GluingCore

/-- The displacement `z = (θ, θ + a)` of the lower mark. -/
def alD_z (a θ : ℤ) : ℤ × ℤ := (θ, θ + a)

/-- The lower copy `Z = V ∩ (V - z)`. -/
def alD_Z (V : Diagram) (a θ : ℤ) : Diagram := V.filter fun x => x + alD_z a θ ∈ V

/-- The first row of `Z` on the diagonal `j`. -/
def alD_zl (V : Diagram) (a θ j : ℤ) : ℤ := max (alD_L V j) (alD_L V (j + a) - θ)

/-- The last row of `Z` on the diagonal `j`. -/
def alD_zh (V : Diagram) (a θ j : ℤ) : ℤ := min (alD_H V j) (alD_H V (j + a) - θ)

section Basic

variable {V : Diagram} {a θ : ℤ}

theorem alD_cell_add_z (r j : ℤ) :
    ((r, r + (minContent V + j)) : ℤ × ℤ) + alD_z a θ =
      (r + θ, r + θ + (minContent V + (j + a))) := by
  ext <;> simp [alD_z]; ring

theorem alD_cell_sub_z (r j : ℤ) :
    ((r, r + (minContent V + j)) : ℤ × ℤ) - alD_z a θ =
      (r - θ, r - θ + (minContent V + (j - a))) := by
  ext <;> simp [alD_z]; ring

theorem alD_mem_Z (hV : IsConnectedSkew V) (ha : 0 ≤ a) (r j : ℤ) :
    (r, r + (minContent V + j)) ∈ alD_Z V a θ ↔
      0 ≤ j ∧ j + a < (span V : ℤ) ∧ alD_zl V a θ j ≤ r ∧ r ≤ alD_zh V a θ j := by
  unfold alD_Z
  rw [Finset.mem_filter, alD_cell_add_z, alD_mem_V hV, alD_mem_V hV]
  unfold alD_zl alD_zh
  omega

theorem alD_zrows (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {j : ℤ} (h0 : 0 ≤ j)
    (h1 : j < (span V : ℤ) - a) :
    alD_L V j ≤ alD_zl V a θ j ∧ alD_zl V a θ j ≤ alD_zh V a θ j ∧
      alD_zh V a θ j ≤ alD_H V j ∧ alD_L V (j + a) - θ ≤ alD_zl V a θ j ∧
      alD_zh V a θ j ≤ alD_H V (j + a) - θ ∧
      (alD_e V a j ≤ 0 → alD_zl V a θ j = alD_L V j ∧ alD_zh V a θ j = alD_H V j) ∧
      (0 ≤ alD_e V a j → alD_zl V a θ j = alD_L V (j + a) - θ ∧
        alD_zh V a θ j = alD_H V (j + a) - θ) := by
  have hb := hD.hb
  have ha := hD.ha
  have t1 := hD.th1 j h0 h1
  have e1 := hD.e_bd j h0 h1
  have l1 := alD_L_le_H hV (j := j) h0 (by omega)
  have l2 := alD_L_le_H hV (j := j + a) (by omega) (by omega)
  unfold alD_e at e1 ⊢
  unfold alD_zl alD_zh
  omega

theorem alD_Z_sub {x : ℤ × ℤ} (hx : x ∈ alD_Z V a θ) : x ∈ V := by
  unfold alD_Z at hx
  exact (Finset.mem_filter.mp hx).1

theorem alD_Z_connected (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    IsConnectedSkew (alD_Z V a θ) := by
  have hb := hD.hb
  have hba := hD.hba
  have ha := hD.ha
  refine alD_connected_of_rows (alD_Z V a θ) (minContent V) ((span V : ℤ) - a)
    (alD_zl V a θ) (alD_zh V a θ) hb ?_ ?_ ?_ ?_ ?_ ?_
  · intro j r
    rw [alD_mem_Z hV ha.le]
    omega
  · intro j h0 h1
    exact (alD_zrows hV hD h0 h1).2.1
  · intro j h0 h1
    have s1 := alD_step hV (j := j) h0 (by omega)
    have s2 := alD_step hV (j := j + a) (by omega) (by omega)
    have e : j + a - 1 = j - 1 + a := by ring
    rw [e] at s2
    unfold alD_zl
    omega
  · intro j h0 h1
    have s1 := alD_step hV (j := j) h0 (by omega)
    have s2 := alD_step hV (j := j + a) (by omega) (by omega)
    have e : j + a - 1 = j - 1 + a := by ring
    rw [e] at s2
    unfold alD_zh
    omega
  · have z := alD_zrows hV hD (j := 0) le_rfl hb
    have e := alD_end0 hV
    omega
  · have z := alD_zrows hV hD (j := (span V : ℤ) - a - 1) (by omega) (by omega)
    have e := alD_endN hV
    have e2 : (span V : ℤ) - a - 1 + a = (span V : ℤ) - 1 := by ring
    unfold alD_zl alD_zh at z ⊢
    rw [e2] at z ⊢
    omega

end Basic

end GluingCore
