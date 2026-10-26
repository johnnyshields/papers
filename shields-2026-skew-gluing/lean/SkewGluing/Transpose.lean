import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Common
import SkewGluing.SchurBridge
import Shields.Combinatorics.Young.SkewSchurPolynomial

/-!
# The transpose of a profile

Formalizes `shields-2026-skew-gluing.tex`, «Component keys» (`sec:minimal-fibers`), the
diagram transpose `Dᵗ` of a connected diagram `D` and its antitranspose `AT(D)`.

A profile `P` records a connected diagram up to translation, with rows indexed from the top.  The
transposed diagram has the columns of `D` as its rows, left to right.  This file defines
`Profile.transpose P`, the profile of `Dᵗ`: a profile with `P.lastCol + 1` rows, where
`P.lastCol + 1` is the number of columns of `D`.  Its beta lists are
`ξ^t_j = λ'_{n+j} - j + lastCol` and `ζ^t_j = μ'_{n+j} - j + lastCol`, where `λ'`, `μ'` are the
column lengths of the Young diagrams `P.lam`, `P.mu` of `SkewGluing.SchurBridge`, and the first
nonempty column of `D` is column `n`.

* `Profile.mem_cells_transpose_iff`: the cells of `Dᵗ` are the cells of `D` with rows and
  columns exchanged and the rows shifted by `lastCol`.
* `Profile.skewSchur_transpose`: the tableau skew Schur polynomial of `Dᵗ` equals that of
  `P.lam' / P.mu'` (Young diagram transposes), in every number of variables.
* `Profile.transpose_transpose`: transposition is an involution (a `HEq`, since the number of
  rows is `n + 1` only propositionally).

Sorry-free.
-/

namespace SkewGluing

namespace Profile

variable {n : ℕ}

/-! ### Column data of a profile -/

theorem xi_add_le_xi_zero (P : Profile n) (i : Fin (n + 1)) : P.xi i + i ≤ P.xi 0 := by
  have h := P.lamRows_antitone (Fin.zero_le i)
  have h1 := P.xi_pos i
  have h2 := P.xi_pos 0
  simp only [lamRows, Fin.val_zero] at h
  omega

theorem n_lt_xi_zero (P : Profile n) : (n : ℤ) < P.xi 0 := by
  have h := P.xi_add_le_xi_zero (Fin.last n)
  have h1 := P.xi_pos (Fin.last n)
  simp only [Fin.val_last] at h
  omega

/-- The index `numCols - 1` of the last nonempty column of the diagram, counted from the first
nonempty column `n`: the diagram occupies the columns `n, …, n + lastCol`, so the transposed
diagram has `lastCol + 1` rows. -/
def lastCol (P : Profile n) : ℕ := (P.xi 0 - n - 1).toNat

theorem lastCol_eq (P : Profile n) : (P.lastCol : ℤ) = P.xi 0 - n - 1 := by
  have := P.n_lt_xi_zero
  simp only [lastCol]
  omega

theorem mem_lam_iff_lt_colLen (P : Profile n) (k c : ℕ) : (k, c) ∈ P.lam ↔ k < P.lam.colLen c :=
  YoungDiagram.mem_iff_lt_colLen

theorem mem_mu_iff_lt_colLen (P : Profile n) (k c : ℕ) : (k, c) ∈ P.mu ↔ k < P.mu.colLen c :=
  YoungDiagram.mem_iff_lt_colLen

/-- The cell `(i, c)` lies in `λ` exactly when `i ≤ n` and `c < ξ_i + i`. -/
theorem mem_lam_fin (P : Profile n) (i : Fin (n + 1)) (c : ℕ) :
    ((i : ℕ), c) ∈ P.lam ↔ (c : ℤ) < P.xi i + i := by
  rw [mem_lam]
  simp [i.isLt]

theorem mem_mu_fin (P : Profile n) (i : Fin (n + 1)) (c : ℕ) :
    ((i : ℕ), c) ∈ P.mu ↔ (c : ℤ) < P.zeta i + i := by
  rw [mem_mu]
  simp [i.isLt]

/-- No cell of `λ` lies in a column beyond `λ_0 - 1 = n + lastCol`. -/
theorem not_mem_lam_of_lt (P : Profile n) {i c : ℕ} (hc : n + P.lastCol < c) : (i, c) ∉ P.lam := by
  intro h
  obtain ⟨hi, hc'⟩ := (mem_lam P i c).mp h
  have h1 := P.xi_add_le_xi_zero ⟨i, hi⟩
  have h2 := P.lastCol_eq
  simp only at h1
  omega

/-- The first `n` columns of `λ / μ` are empty: every cell of `μ` in a row `≤ n` lies in them. -/
theorem mem_mu_of_lt (P : Profile n) {i c : ℕ} (hi : i < n + 1) (hc : c < n) : (i, c) ∈ P.mu := by
  rw [show (i, c) = (((⟨i, hi⟩ : Fin (n + 1)) : ℕ), c) from rfl, mem_mu_fin]
  have h := P.muRows_antitone (Fin.le_last (⟨i, hi⟩ : Fin (n + 1)))
  have h0 := P.zeta_last
  have h1 := P.zeta_nonneg ⟨i, hi⟩
  simp only [muRows, h0, Fin.val_last] at h ⊢
  omega

/-! ### The beta lists of the transpose -/

/-- The beta list `ξ` of the transpose: `λ'_{n+j} - j + lastCol`. -/
def transposeXi (P : Profile n) (j : ℕ) : ℤ :=
  (P.lam.colLen (n + j) : ℤ) - j + P.lastCol

/-- The beta list `ζ` of the transpose: `μ'_{n+j} - j + lastCol`. -/
def transposeZeta (P : Profile n) (j : ℕ) : ℤ :=
  (P.mu.colLen (n + j) : ℤ) - j + P.lastCol

theorem mu_colLen_last (P : Profile n) : P.mu.colLen (n + P.lastCol) = 0 := by
  by_contra hne
  have h : ((0 : ℕ), n + P.lastCol) ∈ P.mu := (mem_mu_iff_lt_colLen P 0 _).mpr (by omega)
  have h' := (mem_mu_fin P 0 (n + P.lastCol)).mp h
  have h1 := P.lastCol_eq
  have h2 := P.r_pos 0
  have h3 := P.xi_sub_zeta 0
  simp only [Fin.val_zero] at h'
  omega

theorem lam_colLen_last_pos (P : Profile n) : 0 < P.lam.colLen (n + P.lastCol) := by
  rw [← mem_lam_iff_lt_colLen]
  rw [show ((0 : ℕ), n + P.lastCol) = (((0 : Fin (n + 1)) : ℕ), n + P.lastCol) from rfl,
    mem_lam_fin]
  have h1 := P.lastCol_eq
  simp only [Fin.val_zero]
  omega

theorem mu_colLen_le (P : Profile n) (c : ℕ) (hc : n ≤ c) : P.mu.colLen c ≤ n := by
  by_contra hne
  have h : (n, c) ∈ P.mu := (mem_mu_iff_lt_colLen P n c).mpr (by omega)
  have h' := (mem_mu_fin P (Fin.last n) c).mp h
  have h0 := P.zeta_last
  simp only [Fin.val_last] at h'
  omega

/-- Adjacent columns of the diagram overlap: `μ'_c < λ'_{c+1}` for `n ≤ c < n + lastCol`. -/
theorem mu_colLen_lt_lam_colLen_succ (P : Profile n) {c : ℕ} (hc : n ≤ c)
    (hc' : c < n + P.lastCol) : P.mu.colLen c < P.lam.colLen (c + 1) := by
  rw [← mem_lam_iff_lt_colLen]
  have hk : P.mu.colLen c < n + 1 := by have := P.mu_colLen_le c hc; omega
  rw [show (P.mu.colLen c, c + 1) = (((⟨P.mu.colLen c, hk⟩ : Fin (n + 1)) : ℕ), c + 1) from rfl,
    mem_lam_fin]
  have h1 := P.lastCol_eq
  rcases Nat.eq_zero_or_pos (P.mu.colLen c) with h0 | hpos
  · simp only [h0]
    have : P.xi ⟨0, by omega⟩ = P.xi 0 := rfl
    simp only [Nat.cast_zero, add_zero]
    rw [show (⟨0, by omega⟩ : Fin (n + 1)) = 0 from rfl]
    omega
  · obtain ⟨k, hk'⟩ : ∃ k, P.mu.colLen c = k + 1 := ⟨P.mu.colLen c - 1, by omega⟩
    have hkn : k < n := by omega
    have hmem : (k, c) ∈ P.mu := (mem_mu_iff_lt_colLen P k c).mpr (by omega)
    have h2 := (mem_mu_fin P (⟨k, hkn⟩ : Fin n).castSucc c).mp hmem
    have h3 := P.zeta_le_xi_succ ⟨k, hkn⟩
    have e : (⟨P.mu.colLen c, hk⟩ : Fin (n + 1)) = (⟨k, hkn⟩ : Fin n).succ :=
      Fin.ext (by simp [hk'])
    rw [e]
    simp only [Fin.val_succ, Fin.val_castSucc] at h2 ⊢
    push_cast at h2 ⊢
    omega

/-- The beta lists of the transpose. -/
def transposeBeta (P : Profile n) : BetaPair P.lastCol where
  xi j := P.transposeXi j
  zeta j := P.transposeZeta j
  xi_strictAnti := by
    rw [Fin.strictAnti_iff_succ_lt]
    intro j
    have := P.lam.colLen_anti (n + j) (n + (j + 1)) (by omega)
    simp only [transposeXi, Fin.val_succ, Fin.val_castSucc]
    push_cast
    omega
  zeta_strictAnti := by
    rw [Fin.strictAnti_iff_succ_lt]
    intro j
    have := P.mu.colLen_anti (n + j) (n + (j + 1)) (by omega)
    simp only [transposeZeta, Fin.val_succ, Fin.val_castSucc]
    push_cast
    omega
  zeta_last := by
    simp only [transposeZeta, Fin.val_last, P.mu_colLen_last]
    omega
  zeta_le_xi_succ j := by
    have h := P.mu_colLen_lt_lam_colLen_succ (c := n + j) (by omega) (by omega)
    rw [show n + (j : ℕ) + 1 = n + ((j : ℕ) + 1) by omega] at h
    simp only [transposeZeta, transposeXi, Fin.val_succ, Fin.val_castSucc]
    push_cast
    omega
  xi_last_pos := by
    have := P.lam_colLen_last_pos
    simp only [transposeXi, Fin.val_last]
    omega

/-- **The transpose of a profile.**  The profile of the transposed diagram `Dᵗ`, whose rows are the
columns of `D` from left to right. -/
def transpose (P : Profile n) : Profile P.lastCol := ofBetaPair P.transposeBeta

theorem xi_transpose (P : Profile n) (j : Fin (P.lastCol + 1)) :
    P.transpose.xi j = (P.lam.colLen (n + j) : ℤ) - j + P.lastCol :=
  congrArg (fun B : BetaPair P.lastCol => B.xi j) (equivBetaPair.right_inv P.transposeBeta)

theorem zeta_transpose (P : Profile n) (j : Fin (P.lastCol + 1)) :
    P.transpose.zeta j = (P.mu.colLen (n + j) : ℤ) - j + P.lastCol :=
  congrArg (fun B : BetaPair P.lastCol => B.zeta j) (equivBetaPair.right_inv P.transposeBeta)

/-! ### The cells of the transpose -/

/-- **The cells of `Dᵗ`.**  Row `i` of the transposed diagram is column `n + i` of `D`: the cell
`(i, k + lastCol)` of `Dᵗ` corresponds to the cell `(k, n + i)` of `D`. -/
theorem mem_cells_transpose_iff (P : Profile n) (i k : ℕ) :
    (i, k + P.lastCol) ∈ Shields.skewCells P.transpose.lam P.transpose.mu ↔
      (k, n + i) ∈ Shields.skewCells P.lam P.mu := by
  rw [Shields.mem_skewCells, Shields.mem_skewCells]
  by_cases hi : i < P.lastCol + 1
  · have e := P.transpose.mem_skewCells_row ⟨i, hi⟩ (k + P.lastCol)
    rw [Shields.mem_skewCells] at e
    rw [e, P.xi_transpose ⟨i, hi⟩, P.zeta_transpose ⟨i, hi⟩,
      mem_lam_iff_lt_colLen, mem_mu_iff_lt_colLen]
    dsimp only
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, by omega⟩
  · have h1 : (i, k + P.lastCol) ∉ P.transpose.lam := fun h => by
      have := ((mem_lam P.transpose i _).mp h).1
      omega
    have h2 : (k, n + i) ∉ P.lam := P.not_mem_lam_of_lt (by omega)
    exact ⟨fun h => absurd h.1 h1, fun h => absurd h.1 h2⟩

theorem le_of_mem_cells_transpose (P : Profile n) {i m : ℕ}
    (h : (i, m) ∈ Shields.skewCells P.transpose.lam P.transpose.mu) : P.lastCol ≤ m := by
  rw [Shields.mem_skewCells] at h
  obtain ⟨hl, hm⟩ := h
  have hi : i < P.lastCol + 1 := ((mem_lam P.transpose i m).mp hl).1
  have e := P.transpose.mem_skewCells_row ⟨i, hi⟩ m
  rw [Shields.mem_skewCells] at e
  have := (e.mp ⟨hl, hm⟩).1
  rw [P.zeta_transpose ⟨i, hi⟩] at this
  omega

theorem lt_of_mem_cells_transpose_lam (P : Profile n) {i k : ℕ}
    (h : (i, k) ∈ Shields.skewCells P.lam.transpose P.mu.transpose) : n ≤ i := by
  rw [Shields.mem_skewCells, YoungDiagram.mem_transpose, YoungDiagram.mem_transpose] at h
  by_contra hlt
  exact h.2 (P.mem_mu_of_lt ((mem_lam P k i).mp h.1).1 (by omega))

/-- **The skew Schur polynomial of the transpose.**  The tableaux of `Dᵗ` and of the Young
diagram transposes `λ' / μ'` correspond by translation: both are the cells of `D` with rows and
columns exchanged, `Dᵗ` normalized to start at the first column. -/
theorem skewSchur_transpose {R : Type*} [CommRing R] (b : ℕ) (x : ℕ → R) (P : Profile n) :
    Shields.skewSchur P.transpose.lam P.transpose.mu b x
      = Shields.skewSchur P.lam.transpose P.mu.transpose b x := by
  have h1 := Shields.skewSchur_translate
    (lam := P.lam.transpose) (mu := P.mu.transpose)
    (lam' := (Shields.dropCols P.lam n).transpose) (mu' := (Shields.dropCols P.mu n).transpose)
    (di := n) (dj := 0) (n := b)
    (fun i j => by
      rw [Shields.mem_skewCells, Shields.mem_skewCells, YoungDiagram.mem_transpose,
        YoungDiagram.mem_transpose, YoungDiagram.mem_transpose, YoungDiagram.mem_transpose,
        Shields.mem_dropCols, Shields.mem_dropCols, Nat.add_zero]
      simp only [Prod.swap_prod_mk])
    (fun i j hc => ⟨P.lt_of_mem_cells_transpose_lam hc, Nat.zero_le _⟩) x
  have h2 := Shields.skewSchur_translate
    (lam := P.transpose.lam) (mu := P.transpose.mu)
    (lam' := (Shields.dropCols P.lam n).transpose) (mu' := (Shields.dropCols P.mu n).transpose)
    (di := 0) (dj := P.lastCol) (n := b)
    (fun i j => by
      rw [Nat.add_zero, mem_cells_transpose_iff, Shields.mem_skewCells, Shields.mem_skewCells,
        YoungDiagram.mem_transpose, YoungDiagram.mem_transpose, Shields.mem_dropCols,
        Shields.mem_dropCols, Nat.add_comm n i]
      simp only [Prod.swap_prod_mk])
    (fun i j hc => ⟨Nat.zero_le _, P.le_of_mem_cells_transpose hc⟩) x
  rw [h2, h1]

/-! ### Transposition is an involution -/

theorem le_of_mem_cells (P : Profile n) {a b : ℕ}
    (h : (a, b) ∈ Shields.skewCells P.lam P.mu) : n ≤ b := by
  rw [Shields.mem_skewCells] at h
  by_contra hlt
  exact h.2 (P.mem_mu_of_lt ((mem_lam P a b).mp h.1).1 (by omega))

/-- **A profile is determined by its cells.**  The cells of `λ / μ` of two profiles with the same
number of rows coincide only if the profiles do. -/
theorem eq_of_cells_eq {P Q : Profile n}
    (h : Shields.skewCells P.lam P.mu = Shields.skewCells Q.lam Q.mu) : P = Q := by
  have hrow : ∀ (i : Fin (n + 1)) (c : ℕ),
      (P.zeta i + i ≤ c ∧ (c : ℤ) < P.xi i + i) ↔ (Q.zeta i + i ≤ c ∧ (c : ℤ) < Q.xi i + i) := by
    intro i c
    rw [← P.mem_skewCells_row i c, ← Q.mem_skewCells_row i c, h]
  have hz : ∀ i : Fin (n + 1), P.zeta i = Q.zeta i := by
    intro i
    have h1 := (hrow i (P.zeta i + i).toNat).mp
    have h2 := (hrow i (Q.zeta i + i).toNat).mpr
    have p1 := P.zeta_nonneg i
    have q1 := Q.zeta_nonneg i
    have p2 := P.r_pos i
    have q2 := Q.r_pos i
    have p3 := P.xi_sub_zeta i
    have q3 := Q.xi_sub_zeta i
    have a1 := h1 (by omega)
    have a2 := h2 (by omega)
    omega
  have hx : ∀ i : Fin (n + 1), P.xi i = Q.xi i := by
    intro i
    have h1 := (hrow i (P.xi i + i - 1).toNat).mp
    have h2 := (hrow i (Q.xi i + i - 1).toNat).mpr
    have p1 := P.zeta_nonneg i
    have q1 := Q.zeta_nonneg i
    have p2 := P.r_pos i
    have q2 := Q.r_pos i
    have p3 := P.xi_sub_zeta i
    have q3 := Q.xi_sub_zeta i
    have a1 := h1 (by omega)
    have a2 := h2 (by omega)
    omega
  exact eq_of_beta_eq (funext hx) (funext hz)

theorem heq_of_cells_eq {m m' : ℕ} (h : m' = m) {R : Profile m'} {P : Profile m}
    (hc : Shields.skewCells R.lam R.mu = Shields.skewCells P.lam P.mu) : HEq R P := by
  subst h
  exact heq_of_eq (eq_of_cells_eq hc)

theorem lam_colLen_n (P : Profile n) : P.lam.colLen n = n + 1 := by
  have h1 : (n, n) ∈ P.lam := by
    rw [show (n, n) = (((Fin.last n : Fin (n + 1)) : ℕ), n) from rfl, mem_lam_fin]
    have := P.xi_pos (Fin.last n)
    simp only [Fin.val_last]
    omega
  have h2 : (n + 1, n) ∉ P.lam := fun h => by have := ((mem_lam P _ _).mp h).1; omega
  have h3 := (mem_lam_iff_lt_colLen P n n).mp h1
  have h4 : ¬ n + 1 < P.lam.colLen n := fun h => h2 ((mem_lam_iff_lt_colLen P _ _).mpr h)
  omega

/-- The transpose of the transpose has the original number of rows. -/
theorem lastCol_transpose (P : Profile n) : P.transpose.lastCol = n := by
  have h := P.lastCol_eq
  have h2 := P.transpose.lastCol_eq
  rw [P.xi_transpose 0] at h2
  have := P.lam_colLen_n
  simp only [Fin.val_zero, Nat.add_zero, this] at h2
  omega

/-- **Transposition is an involution.**  `(Pᵗ)ᵗ` is `P`, as profiles with the number of rows
`n + 1` of `P`; the equality is a `HEq` because the number of rows of `(Pᵗ)ᵗ` is `n + 1` only
propositionally (`lastCol_transpose`). -/
theorem transpose_transpose (P : Profile n) : HEq P.transpose.transpose P := by
  refine heq_of_cells_eq P.lastCol_transpose ?_
  ext ⟨a, b⟩
  by_cases hb : P.transpose.lastCol ≤ b
  · obtain ⟨k, rfl⟩ : ∃ k, b = k + P.transpose.lastCol := ⟨b - P.transpose.lastCol, by omega⟩
    rw [P.transpose.mem_cells_transpose_iff, P.lastCol_transpose, Nat.add_comm P.lastCol a,
      P.mem_cells_transpose_iff k a, Nat.add_comm n k]
  · have h1 : (a, b) ∉ Shields.skewCells P.transpose.transpose.lam P.transpose.transpose.mu :=
      fun h => hb (P.transpose.le_of_mem_cells_transpose h)
    have h2 : (a, b) ∉ Shields.skewCells P.lam P.mu := fun h => by
      have := P.le_of_mem_cells h
      have := P.lastCol_transpose
      omega
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

end Profile

end SkewGluing
