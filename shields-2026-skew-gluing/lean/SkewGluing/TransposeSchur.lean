import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Common
import Mathlib.Tactic.FinCases
import SkewGluing.DualEvaluation
import SkewGluing.Transpose

/-!
# `ι(s_D) = s_{Dᵗ}` and the transpose of a Schur class

Formalizes `shields-2026-skew-gluing.tex`, «Component keys» (`sec:minimal-fibers`), the
sentence `ι(s_D) = s_{Dᵗ} = s_{AT(D)}`, and its use in `lem:gluing-equal`: `s_{AT(D)}` is the
image of `s_D` under the usual involution.

* `schurInvolution_schur_transpose`: `ι(s_P) = s_{Pᵗ}` for every profile `P`.
* `schurInvolution_schur_antitranspose`: `ι(s_P) = s_{AT(P)}`, `AT(P) = (Pᵗ)*`.
* `Profile.transpose_transpose`: transposition is an involution on profiles.
* `schurClass_bijOn_transpose`: the transposition `D ↦ Dᵗ` maps the Schur class of `D` bijectively
  onto the Schur class of `Dᵗ`, and `ι` maps the Schur function of each member to that of its
  transpose.

Route: `ι` is the algebra map `h_j ↦ e_j` of `SkewGluing.SchurFunction`, and the identity is
proved by evaluating at `a` independent variables, where the second Jacobi--Trudi identity
(the mixed-alphabet Jacobi--Trudi theorem of `Shields.Combinatorics.Young.LGVOddTableau` at no
even variables) identifies `ι(s_P)` with the tableau skew Schur polynomial of the conjugate
shape, which is the skew Schur polynomial of the transposed diagram.

Sorry-free.
-/

namespace SkewGluing

open MvPolynomial

/-- **`ι(s_D) = s_{Dᵗ}`.**  The usual involution `ι` (`ι(h_j) = e_j`) sends the skew Schur function
of a connected diagram to that of its transpose. -/
theorem schurInvolution_schur_transpose {n : ℕ} (P : Profile n) :
    schurInvolution P.schur = P.transpose.schur := by
  refine eq_of_evalComplete_eq fun a => ?_
  rw [evalComplete_schurInvolution, Profile.evalElem_schur,
    ← Profile.skewSchur_transpose a (varAlphabet a) P, ← Profile.evalComplete_schur]

namespace Profile

variable {n : ℕ}

/-- The antitranspose `AT(P) = (Pᵗ)*`: transpose followed by rotation through `180` degrees. -/
def antitranspose (P : Profile n) : Profile P.lastCol := P.transpose.rotate

end Profile

/-- **`ι(s_D) = s_{AT(D)}`.** -/
theorem schurInvolution_schur_antitranspose {n : ℕ} (P : Profile n) :
    schurInvolution P.schur = P.antitranspose.schur := by
  rw [schurInvolution_schur_transpose, Profile.antitranspose, Profile.schur_rotate]


/-! ### The Schur class and its transpose -/

/-- A connected diagram with any number of rows, up to translation: its profile. -/
abbrev AnyProfile : Type := Σ n : ℕ, Profile n

/-- The transpose of a connected diagram, as a diagram with any number of rows. -/
def transposeAny (G : AnyProfile) : AnyProfile := ⟨G.2.lastCol, G.2.transpose⟩

/-- **The Schur class of a connected diagram**: the connected diagrams, up to translation, with
the same skew Schur function. -/
def schurClass {n : ℕ} (P : Profile n) : Set AnyProfile := {G | G.2.schur = P.schur}

theorem transposeAny_transposeAny (G : AnyProfile) : transposeAny (transposeAny G) = G := by
  obtain ⟨n, P⟩ := G
  exact Sigma.ext P.lastCol_transpose (Profile.transpose_transpose P)

theorem schur_transposeAny (G : AnyProfile) :
    (transposeAny G).2.schur = schurInvolution G.2.schur :=
  (schurInvolution_schur_transpose G.2).symm

/-- **`ι` maps the Schur class of `D` bijectively onto the Schur class of `Dᵗ`.**  The bijection
is `G ↦ Gᵗ`, and `ι(s_G) = s_{Gᵗ}` for each member (`schur_transposeAny`). -/
theorem schurClass_bijOn_transpose {n : ℕ} (P : Profile n) :
    Set.BijOn transposeAny (schurClass P) (schurClass P.transpose) := by
  refine ⟨fun G hG => ?_, fun G _ G' _ h => ?_, fun H hH => ?_⟩
  · change (transposeAny G).2.schur = P.transpose.schur
    rw [schur_transposeAny, show G.2.schur = P.schur from hG, schurInvolution_schur_transpose]
  · rw [← transposeAny_transposeAny G, h, transposeAny_transposeAny]
  · refine ⟨transposeAny H, ?_, transposeAny_transposeAny H⟩
    change (transposeAny H).2.schur = P.schur
    rw [schur_transposeAny, show H.2.schur = P.transpose.schur from hH,
      ← schurInvolution_schur_transpose, schurInvolution_involutive]

/-! ### Worked examples

The row `(3)` transposes to the column `(1,1,1)`, the hook `(2,1)` is its own transpose, and rows
`3, 2` overlapping in two columns transpose to rows `2, 2, 1` with overlaps `2, 1`. -/

section Examples

theorem colLen_eq_of {μ : YoungDiagram} {c v : ℕ} (h1 : v = 0 ∨ (v - 1, c) ∈ μ)
    (h2 : (v, c) ∉ μ) : μ.colLen c = v := by
  rw [YoungDiagram.mem_iff_lt_colLen] at h2
  rcases h1 with h | h
  · omega
  · rw [YoungDiagram.mem_iff_lt_colLen] at h
    omega

theorem colLen_lam_eq_of {n : ℕ} (P : Profile n) (c v : ℕ)
    (h1 : v = 0 ∨ ∃ i : Fin (n + 1), (i : ℕ) = v - 1 ∧ (c : ℤ) < P.xi i + i)
    (h2 : ∀ i : Fin (n + 1), (i : ℕ) = v → ¬ (c : ℤ) < P.xi i + i) : P.lam.colLen c = v := by
  apply colLen_eq_of
  · rcases h1 with h | ⟨i, hi, hc⟩
    · exact Or.inl h
    · right
      rw [show v - 1 = (i : ℕ) from hi.symm, Profile.mem_lam_fin]
      exact hc
  · intro h
    obtain ⟨hlt, hc⟩ := (Profile.mem_lam P v c).mp h
    exact h2 ⟨v, hlt⟩ rfl hc

theorem colLen_mu_eq_of {n : ℕ} (P : Profile n) (c v : ℕ)
    (h1 : v = 0 ∨ ∃ i : Fin (n + 1), (i : ℕ) = v - 1 ∧ (c : ℤ) < P.zeta i + i)
    (h2 : ∀ i : Fin (n + 1), (i : ℕ) = v → ¬ (c : ℤ) < P.zeta i + i) : P.mu.colLen c = v := by
  apply colLen_eq_of
  · rcases h1 with h | ⟨i, hi, hc⟩
    · exact Or.inl h
    · right
      rw [show v - 1 = (i : ℕ) from hi.symm, Profile.mem_mu_fin]
      exact hc
  · intro h
    obtain ⟨hlt, hc⟩ := (Profile.mem_mu P v c).mp h
    exact h2 ⟨v, hlt⟩ rfl hc

theorem lam_colLen_rowProfile (c : ℕ) (hc : c < 3) : rowProfile.lam.colLen c = 1 := by
  apply colLen_eq_of
  · right
    rw [show (1 - 1, c) = (((0 : Fin (0 + 1)) : ℕ), c) from rfl, Profile.mem_lam_fin]
    have : rowProfile.xi 0 = 3 := by decide
    rw [this]; simpa using hc
  · intro h
    have := ((Profile.mem_lam rowProfile 1 c).mp h).1
    omega

theorem mu_colLen_rowProfile (c : ℕ) : rowProfile.mu.colLen c = 0 := by
  apply colLen_eq_of
  · left; rfl
  · intro h
    obtain ⟨h0, h1⟩ := (Profile.mem_mu rowProfile 0 c).mp h
    have hz : rowProfile.zeta ⟨0, h0⟩ = 0 := rowProfile.zeta_last
    rw [hz] at h1
    omega

/-- The transpose of the row `(3)` is the column `(1,1,1)`. -/
theorem transpose_rowProfile : (rowProfile.transpose : Profile 2) = columnProfile := by
  have hl : rowProfile.lastCol = 2 := by decide
  refine Profile.eq_of_beta_eq ?_ ?_
  · funext j
    rw [Profile.xi_transpose]
    fin_cases j <;> simp +decide [lam_colLen_rowProfile, hl]
  · funext j
    rw [Profile.zeta_transpose]
    fin_cases j <;> simp +decide [mu_colLen_rowProfile, hl]

/-- The hook `(2,1)` is its own transpose. -/
theorem transpose_hookProfile : (hookProfile.transpose : Profile 1) = hookProfile := by
  have hl : hookProfile.lastCol = 1 := by decide
  have l1 : hookProfile.lam.colLen 1 = 2 :=
    colLen_lam_eq_of _ 1 2 (Or.inr (by decide)) (by decide)
  have l2 : hookProfile.lam.colLen 2 = 1 :=
    colLen_lam_eq_of _ 2 1 (Or.inr (by decide)) (by decide)
  have m1 : hookProfile.mu.colLen 1 = 0 :=
    colLen_mu_eq_of _ 1 0 (Or.inl rfl) (by decide)
  have m2 : hookProfile.mu.colLen 2 = 0 :=
    colLen_mu_eq_of _ 2 0 (Or.inl rfl) (by decide)
  refine Profile.eq_of_beta_eq ?_ ?_
  · funext j
    rw [Profile.xi_transpose]
    fin_cases j <;> simp +decide [l1, l2, hl]
  · funext j
    rw [Profile.zeta_transpose]
    fin_cases j <;> simp +decide [m1, m2, hl]

/-- Rows of lengths `3, 2` overlapping in two columns. -/
def twoRowsProfile : Profile 1 where
  r := ![3, 2]
  g := ![1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- Rows of lengths `2, 2, 1` with overlaps `2, 1`. -/
def threeRowsProfile : Profile 2 where
  r := ![2, 2, 1]
  g := ![1, 0]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- The transpose of rows `3, 2` with overlap `2` is rows `2, 2, 1` with overlaps `2, 1`. -/
theorem transpose_twoRowsProfile : (twoRowsProfile.transpose : Profile 2) = threeRowsProfile := by
  have hl : twoRowsProfile.lastCol = 2 := by decide
  have l1 : twoRowsProfile.lam.colLen 1 = 2 :=
    colLen_lam_eq_of _ 1 2 (Or.inr (by decide)) (by decide)
  have l2 : twoRowsProfile.lam.colLen 2 = 2 :=
    colLen_lam_eq_of _ 2 2 (Or.inr (by decide)) (by decide)
  have l3 : twoRowsProfile.lam.colLen 3 = 1 :=
    colLen_lam_eq_of _ 3 1 (Or.inr (by decide)) (by decide)
  have m1 : twoRowsProfile.mu.colLen 1 = 0 :=
    colLen_mu_eq_of _ 1 0 (Or.inl rfl) (by decide)
  have m2 : twoRowsProfile.mu.colLen 2 = 0 :=
    colLen_mu_eq_of _ 2 0 (Or.inl rfl) (by decide)
  have m3 : twoRowsProfile.mu.colLen 3 = 0 :=
    colLen_mu_eq_of _ 3 0 (Or.inl rfl) (by decide)
  refine Profile.eq_of_beta_eq ?_ ?_
  · funext j
    rw [Profile.xi_transpose]
    fin_cases j <;> simp +decide [l1, l2, l3, hl]
  · funext j
    rw [Profile.zeta_transpose]
    fin_cases j <;> simp +decide [m1, m2, m3, hl]

end Examples

end SkewGluing
