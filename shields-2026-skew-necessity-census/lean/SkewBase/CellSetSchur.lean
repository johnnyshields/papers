import SkewBase.CellSetProfile

/-!
# The skew Schur function of a connected cell set does not depend on its presentation

Formalizes `shields-2026-skew-base-computational.tex`, `lem:profiles` and `eq:jt`: the skew Schur
function of a connected diagram with profile `P` is the Jacobi–Trudi determinant `P.schur`.

A cell set `H` has the skew Schur function `f` (`HasSchur H f`) when it is a translate of the cells
of some diagram `B` given by beta lists, with `s_B = f`.  Such a `B` may carry empty rows, above and
below the nonempty ones.  For a connected `H` the nonempty rows of `B` are the rows of the profile
of `H`, with beta lists those of the profile up to one common shift (`BetaRows.beta_of_cells_eq`),
and an empty first or last row is removed from the Jacobi–Trudi determinant by expansion along
its column or row (`betaDet_first_empty`, `betaDet_last_empty`, `betaDet_pad`).  Hence
`HasSchur H f` holds exactly for `f = P.schur` (`hasSchur_iff_of_hasProfile`), and the skew Schur
function of a connected cell set is well defined (`hasSchur_unique`).

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-! ### Empty rows at the ends of a Jacobi–Trudi determinant -/

/-- An empty first row (`ξ_0 = ζ_0`) is removed from the Jacobi–Trudi determinant. -/
theorem betaDet_first_empty {k : ℕ} (ξ ζ : Fin (k + 1) → ℤ) (hξ : StrictAnti ξ)
    (h0 : ξ 0 = ζ 0) :
    betaDet ξ ζ = betaDet (fun i : Fin k => ξ i.succ) (fun i : Fin k => ζ i.succ) := by
  unfold betaDet
  rw [Matrix.det_succ_column_zero]
  rw [Finset.sum_eq_single (0 : Fin (k + 1))]
  · simp [h0, Fin.succAbove_zero]
    rfl
  · intro i _ hi
    have : ξ i < ξ 0 := hξ (Fin.pos_iff_ne_zero.mpr hi)
    simp [hh_of_neg (show ξ i - ζ 0 < 0 by omega)]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- An empty last row (`ξ_last = ζ_last`) is removed from the Jacobi–Trudi determinant. -/
theorem betaDet_last_empty {k : ℕ} (ξ ζ : Fin (k + 1) → ℤ) (hζ : StrictAnti ζ)
    (h0 : ξ (Fin.last k) = ζ (Fin.last k)) :
    betaDet ξ ζ = betaDet (fun i : Fin k => ξ i.castSucc) (fun i : Fin k => ζ i.castSucc) := by
  unfold betaDet
  rw [Matrix.det_succ_row _ (Fin.last k)]
  rw [Finset.sum_eq_single (Fin.last k)]
  · have e : ((Fin.last k : Fin (k + 1)) : ℕ) + ((Fin.last k : Fin (k + 1)) : ℕ) =
        2 * k := by simp [Fin.val_last]; ring
    rw [e, pow_mul]
    simp [h0, Fin.succAbove_last]
    rfl
  · intro j _ hj
    have : ζ (Fin.last k) < ζ j := hζ (lt_of_le_of_ne (Fin.le_last j) hj)
    simp [hh_of_neg (show ξ (Fin.last k) - ζ j < 0 by omega)]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Removing the empty rows above and below the nonempty rows `a, …, a + n` of beta lists
`ξ`, `ζ` on `ℓ` rows leaves the Jacobi–Trudi determinant of those rows unchanged. -/
theorem betaDet_pad {ℓ : ℕ} (ξ ζ : ℕ → ℤ) (hξ : ∀ i j, i < j → j < ℓ → ξ j < ξ i)
    (hζ : ∀ i j, i < j → j < ℓ → ζ j < ζ i) (hle : ∀ i, i < ℓ → ζ i ≤ ξ i) {a n : ℕ}
    (hl : a + n < ℓ) (hrows : ∀ i, i < ℓ → (ζ i < ξ i ↔ a ≤ i ∧ i ≤ a + n)) :
    betaDet (fun i : Fin ℓ => ξ i) (fun i : Fin ℓ => ζ i) =
      betaDet (fun i : Fin (n + 1) => ξ (a + i)) (fun i : Fin (n + 1) => ζ (a + i)) := by
  induction ℓ generalizing ξ ζ a with
  | zero => omega
  | succ ℓ ih =>
    by_cases ha : 0 < a
    · have h0 : ξ 0 = ζ 0 := by
        have := hle 0 (by omega)
        have h2 := (hrows 0 (by omega)).not.mpr (by omega)
        omega
      rw [betaDet_first_empty (fun i : Fin (ℓ + 1) => ξ i) (fun i : Fin (ℓ + 1) => ζ i)
        (fun i j hij => hξ i j hij j.2) (by simpa using h0)]
      have := ih (fun i => ξ (i + 1)) (fun i => ζ (i + 1)) (a := a - 1)
        (fun i j hij hj => hξ _ _ (by omega) (by omega))
        (fun i j hij hj => hζ _ _ (by omega) (by omega))
        (fun i hi => hle _ (by omega)) (by omega)
        (fun i hi => by
          have := hrows (i + 1) (by omega)
          rw [this]; omega)
      refine Eq.trans ?_ (this.trans ?_)
      · rfl
      · congr 1 <;> funext i <;> congr 1 <;> omega
    · obtain rfl : a = 0 := by omega
      by_cases hn : n < ℓ
      · have h0 : ξ ℓ = ζ ℓ := by
          have := hle ℓ (by omega)
          have h2 := (hrows ℓ (by omega)).not.mpr (by omega)
          omega
        rw [betaDet_last_empty _ _ (fun i j hij => hζ i j hij j.2) (by simpa using h0)]
        exact ih ξ ζ (fun i j hij hj => hξ _ _ hij (by omega))
          (fun i j hij hj => hζ _ _ hij (by omega)) (fun i hi => hle _ (by omega)) (by omega)
          (fun i hi => hrows i (by omega))
      · obtain rfl : n = ℓ := by omega
        simp only [zero_add]

/-! ### The beta lists of a presentation of a diagram with a profile -/

namespace BetaRows

variable {ℓ n : ℕ}

/-- If the cells of `B` are a translate of the diagram of a profile `P`, then the nonempty rows of
`B` are `a, …, a + n` for some `a`, and on them the beta lists of `B` are those of `P` plus one
common constant. -/
theorem beta_of_cells_eq (B : BetaRows ℓ) (P : Profile n) (u : ℤ × ℤ)
    (h : B.cells = translate u P.toBetaRows.cells) :
    ∃ (a : ℕ) (c : ℤ), a + n < ℓ ∧
      (∀ i, i < ℓ → (B.zeta i < B.xi i ↔ a ≤ i ∧ i ≤ a + n)) ∧
      ∀ k : Fin (n + 1), B.xi (a + k) = P.xi k + c ∧ B.zeta (a + k) = P.zeta k + c := by
  -- the cells of row `i` of `B`, in terms of `P`
  have hcell : ∀ (i : ℕ) (j : ℤ), ((i : ℤ), j) ∈ B.cells ↔
      ∃ k : ℕ, ∃ hk : k < n + 1, (i : ℤ) - u.1 = k ∧ P.zeta ⟨k, hk⟩ + k ≤ j - u.2 ∧
        j - u.2 < P.xi ⟨k, hk⟩ + k := by
    intro i j
    rw [h, mem_translate_mk]
    constructor
    · intro hx
      obtain ⟨k, hk1, -⟩ := row_of_mem_cells_profile P hx
      rw [hk1] at hx
      obtain ⟨hk, h1, h2⟩ := (mem_cells_profile_iff P).mp hx
      exact ⟨k, hk, hk1, h1, h2⟩
    · rintro ⟨k, hk, hik, h1, h2⟩
      rw [hik]
      exact (mem_cells_profile_iff P).mpr ⟨hk, h1, h2⟩
  have hshift : ∀ (k : ℕ) (hk : k < n + 1) (j : ℤ), ((k : ℤ), j) ∈ P.toBetaRows.cells →
      ∃ i : ℕ, i < ℓ ∧ (i : ℤ) = k + u.1 ∧ ((i : ℤ), j + u.2) ∈ B.cells := by
    intro k hk j hj
    have hm : ((k : ℤ) + u.1, j + u.2) ∈ B.cells := by
      rw [h, mem_translate_mk]
      simpa using hj
    obtain ⟨i, hi1, hiℓ, -, -⟩ := exists_mem_cells hm
    simp only at hi1
    refine ⟨i, hiℓ, hi1.symm, ?_⟩
    rw [← hi1]
    exact hm
  obtain ⟨j0, hj0⟩ := exists_cell_row_profile P (k := 0) (by omega)
  obtain ⟨a, haℓ, ha, -⟩ := hshift 0 (by omega) j0 hj0
  simp only [Nat.cast_zero, zero_add] at ha
  obtain ⟨jn, hjn⟩ := exists_cell_row_profile P (k := n) (by omega)
  obtain ⟨an, hanℓ, han, -⟩ := hshift n (by omega) jn hjn
  have hl : a + n < ℓ := by omega
  have hrows : ∀ i, i < ℓ → (B.zeta i < B.xi i ↔ a ≤ i ∧ i ≤ a + n) := by
    intro i hi
    constructor
    · intro hlt
      have hm : ((i : ℤ), B.zeta i + i) ∈ B.cells := mem_cells.mpr ⟨hi, le_rfl, by omega⟩
      obtain ⟨k, hk, hik, -, -⟩ := (hcell i _).mp hm
      omega
    · rintro ⟨h1, h2⟩
      obtain ⟨j, hj⟩ := exists_cell_row_profile P (k := i - a) (by omega)
      obtain ⟨i', hi'ℓ, hi'e, hm⟩ := hshift (i - a) (by omega) j hj
      have hii : i' = i := by omega
      subst hii
      have := (mem_cells.mp hm).2
      omega
  refine ⟨a, u.2 - u.1, hl, hrows, fun k => ?_⟩
  have hlt : B.zeta (a + k) < B.xi (a + k) := (hrows (a + k) (by omega)).mpr (by omega)
  have hr := P.xi_sub_zeta k
  have hrp := P.r_pos k
  -- the cells of row `a + k` of `B` lie in row `k` of `P`, shifted by `u.2`
  have hsame : ∀ j : ℤ, (((a + (k : ℕ) : ℕ) : ℤ), j) ∈ B.cells ↔
      P.zeta k + k ≤ j - u.2 ∧ j - u.2 < P.xi k + k := by
    intro j
    rw [hcell]
    constructor
    · rintro ⟨k', hk', hik, h1, h2⟩
      obtain rfl : k' = (k : ℕ) := by push_cast at hik; omega
      exact ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨k, k.2, by push_cast; omega, by simpa using h1, by simpa using h2⟩
  have hz1 := (hsame (B.zeta (a + k) + ((a + (k : ℕ) : ℕ) : ℤ))).mp
    (mem_cells.mpr ⟨by omega, le_rfl, by omega⟩)
  have hz2 := mem_cells.mp ((hsame (P.zeta k + k + u.2)).mpr ⟨by omega, by omega⟩)
  have hx1 := (hsame (B.xi (a + k) + ((a + (k : ℕ) : ℕ) : ℤ) - 1)).mp
    (mem_cells.mpr ⟨by omega, by omega, by omega⟩)
  have hx2 := mem_cells.mp ((hsame (P.xi k + k + u.2 - 1)).mpr ⟨by omega, by omega⟩)
  push_cast at hz1 hz2 hx1 hx2
  constructor <;> omega

end BetaRows

/-! ### The skew Schur function of a connected cell set -/

/-- **A presentation of a diagram with profile `P` has the skew Schur function `P.schur`.** -/
theorem hasSchur_eq_of_hasProfile {n : ℕ} {H : Diagram} {P : Profile n} {f : Lambda}
    (hP : HasProfile H P) (hf : HasSchur H f) : f = P.schur := by
  obtain ⟨v, hv⟩ := hP
  obtain ⟨ℓ, B, w, hw, rfl⟩ := hf
  have e : B.cells = translate (-w) (translate w B.cells) := by
    rw [SkewGluing.translate_translate]
    simp [translate_zero]
  have hcells : B.cells = translate (v - w) P.toBetaRows.cells := by
    rw [e, ← hw, hv, SkewGluing.translate_translate]
    congr 1
    abel
  obtain ⟨a, c, hl, hrows, hbeta⟩ := B.beta_of_cells_eq P _ hcells
  calc B.schur = betaDet (fun i : Fin ℓ => B.xi i) (fun i : Fin ℓ => B.zeta i) := rfl
    _ = betaDet (fun i : Fin (n + 1) => B.xi (a + i)) (fun i : Fin (n + 1) => B.zeta (a + i)) :=
      betaDet_pad B.xi B.zeta B.xi_lt B.zeta_lt B.zeta_le hl hrows
    _ = betaDet (fun i : Fin (n + 1) => P.xi i + c) (fun i : Fin (n + 1) => P.zeta i + c) := by
      congr 1
      · funext i; exact (hbeta i).1
      · funext i; exact (hbeta i).2
    _ = P.schur := by
      unfold betaDet Profile.schur
      simp only [add_sub_add_right_eq_sub]

/-- A diagram with profile `P` has the skew Schur function `f` exactly when `f = P.schur`. -/
theorem hasSchur_iff_of_hasProfile {n : ℕ} {H : Diagram} {P : Profile n} {f : Lambda}
    (hP : HasProfile H P) : HasSchur H f ↔ f = P.schur := by
  refine ⟨hasSchur_eq_of_hasProfile hP, ?_⟩
  rintro rfl
  obtain ⟨v, hv⟩ := hP
  exact ⟨n + 1, P.toBetaRows, v, hv, Profile.toBetaRows_schur P⟩

/-- **The skew Schur function of a connected cell set is independent of the presentation.** -/
theorem hasSchur_unique {H : Diagram} (hH : IsConnectedSkew H) {f f' : Lambda}
    (hf : HasSchur H f) (hf' : HasSchur H f') : f = f' := by
  obtain ⟨n, P, hP⟩ := exists_hasProfile hH
  rw [hasSchur_eq_of_hasProfile hP hf, hasSchur_eq_of_hasProfile hP hf']

/-- The skew Schur function of a connected cell set: the Jacobi–Trudi determinant of its profile. -/
noncomputable def schurOf {H : Diagram} (hH : IsConnectedSkew H) : Lambda :=
  (profileOf hH).2.schur

/-- A connected cell set has the skew Schur function `schurOf`, and no other. -/
theorem hasSchur_iff_eq_schurOf {H : Diagram} (hH : IsConnectedSkew H) {f : Lambda} :
    HasSchur H f ↔ f = schurOf hH :=
  hasSchur_iff_of_hasProfile (hasProfile_profileOf hH)

end SkewBase
