import SkewBase.CellSetPresentation

/-!
# A connected diagram is determined by its profile

Formalizes `shields-2026-skew-base-computational.tex`, `lem:profiles`: a connected diagram with
`n + 1` rows is determined up to translation by its profile `(r; g)`, where `r_i` is the length of
row `i` and `g_i + 1` is the number of columns shared by rows `i` and `i + 1`; a sequence is a
profile exactly when `r_i ≥ 1` and `0 ≤ g_i < min (r_i, r_{i+1})` (the fields of `Profile`).

Diagrams are cell sets (`SkewGluing.Diagram`) and the diagram of a profile `P` is the cell set
`P.toBetaRows.cells` (`HasProfile`).  The statement is proved in four parts.

* The diagram of every profile is a connected skew diagram (`isConnectedSkew_cells_profile`), its
  rows `0, …, n` are those of `P`, and its row `i` has `r_i` cells and shares `g_i + 1` columns
  with row `i + 1` (`sharedColumns_one_profile`, `sharedColumns_two_profile`).  Row `i` occupies
  the contents `ζ_i, …, ξ_i - 1`, the contents of the diagram are `0, …, ξ_0 - 1`, and
  `N_F = ξ_0 = ∑ r_i - ∑ g_i` (`mem_cells_profile_iff_content`, `contents_cells_profile`,
  `HasProfile.span_eq`).  Rotation reverses both sequences: the rotation of a diagram with profile
  `P` has the profile `P.rotate` (`rotate_cells_profile`, `HasProfile.rotated`).
* Every connected skew cell set is a translate of the diagram of some profile
  (`exists_hasProfile`).  The rows are consecutive and adjacent rows share a column, because a
  chain of adjacent cells from the first row to the last crosses from row `i` to row `i + 1` by a
  vertical step; the beta lists of the rows then come from the presentation of a skew cell set
  (`presentation`), normalized so that `ζ_n = 0` (`BetaRows.exists_profile_cells`).
* The profile is unique (`hasProfile_unique`): two profiles whose diagrams are translates of one
  another have the same number of rows and the same `r` and `g`, read off the cells by
  `sharedColumns`.
* Hence two connected diagrams with the same profile are translates of one another
  (`eq_translate_of_hasProfile`), and the translation classes of connected diagrams are in
  bijection with the profiles (`profileEquiv`), the two maps being the profile of a diagram and the
  diagram of a profile.

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-! ### Chains of cells cross between adjacent rows by a vertical step -/

/-- A chain of cells of `D` from a cell in a row `≤ i` to a cell in a row `> i` contains a vertical
step from row `i` to row `i + 1`: some column `c` has `(i, c)` and `(i + 1, c)` in `D`. -/
theorem exists_shared_column_of_reach {D : Diagram} {x y : ℤ × ℤ} {i : ℤ}
    (h : Relation.ReflTransGen (fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b) x y)
    (hx : x.1 ≤ i) (hy : i < y.1) : ∃ c, (i, c) ∈ D ∧ (i + 1, c) ∈ D := by
  revert hy
  induction h with
  | refl => intro hy; omega
  | @tail z y' _ hzy ih =>
    intro hy
    by_cases hz : i < z.1
    · exact ih hz
    · obtain ⟨hzD, hyD, hadj⟩ := hzy
      rw [cellAdj_iff] at hadj
      have h1 : z.1 = i := by omega
      have h2 : y'.1 = i + 1 := by omega
      have h3 : y'.2 = z.2 := by omega
      refine ⟨z.2, ?_, ?_⟩
      · rw [← h1]; exact hzD
      · rw [← h2, ← h3]; exact hyD

/-! ### The diagram of a profile -/

namespace BetaRows

/-- The cell set of a diagram given by beta lists in which every row of `0, …, n` is nonempty and
adjacent rows share a column is a translate, by a shift of columns only, of the diagram of a
profile: the profile has `r_i = ξ_i - ζ_i`, `g_i = ξ_{i+1} - ζ_i`, and its beta lists are those of
`B` with `ζ_n` subtracted. -/
theorem exists_profile_cells {n : ℕ} (B : BetaRows (n + 1))
    (hne : ∀ i, i < n + 1 → B.zeta i < B.xi i) (hov : ∀ k, k < n → 0 < B.overlap 1 k) :
    ∃ P : Profile n, B.cells = translate (0, B.zeta n) P.toBetaRows.cells := by
  have hg : ∀ k, k < n → B.zeta k ≤ B.xi (k + 1) := fun k hk => by
    have := hov k hk
    simp only [overlap] at this
    omega
  let P : Profile n :=
    { r := fun i => (B.xi i - B.zeta i).toNat
      g := fun j => (B.xi (j + 1) - B.zeta j).toNat
      r_pos := fun i => by have := hne i i.2; omega
      g_lt_castSucc := fun j => by
        have h1 := hne j (by omega)
        have h2 := B.xi_lt j (j + 1) (by omega) (by omega)
        simp only [Fin.val_castSucc]
        omega
      g_lt_succ := fun j => by
        have h1 := hne (j + 1) (by omega)
        have h2 := B.zeta_lt j (j + 1) (by omega) (by omega)
        simp only [Fin.val_succ]
        omega }
  have hbeta := P.eq_beta_of_equations
    (x := fun i => B.xi i - B.zeta n) (z := fun i => B.zeta i - B.zeta n)
    (by simp [Fin.val_last]) (fun i => by
      have := hne i i.2
      simp only [P]
      omega) (fun j => by
      have := hg j j.2
      simp only [P, Fin.val_succ, Fin.val_castSucc]
      omega)
  have hxi : ∀ i, i < n + 1 → P.toBetaRows.xi i = B.xi i - B.zeta n := fun i hi => by
    have h1 := congrFun hbeta.1 ⟨i, hi⟩
    have h2 := Profile.toBetaRows_xi P ⟨i, hi⟩
    simp only at h1 h2
    omega
  have hzeta : ∀ i, i < n + 1 → P.toBetaRows.zeta i = B.zeta i - B.zeta n := fun i hi => by
    have h1 := congrFun hbeta.2 ⟨i, hi⟩
    have h2 := Profile.toBetaRows_zeta P ⟨i, hi⟩
    simp only at h1 h2
    omega
  refine ⟨P, ?_⟩
  ext ⟨a, b⟩
  rw [mem_translate_mk]
  simp only [sub_zero]
  constructor
  · intro hx
    obtain ⟨i, hi1, hiℓ, h1, h2⟩ := exists_mem_cells hx
    simp only at hi1
    subst hi1
    refine mem_cells.mpr ⟨hiℓ, ?_, ?_⟩
    · rw [hzeta i hiℓ]; omega
    · rw [hxi i hiℓ]; omega
  · intro hx
    obtain ⟨i, hi1, hiℓ, h1, h2⟩ := exists_mem_cells hx
    simp only at hi1
    subst hi1
    refine mem_cells.mpr ⟨hiℓ, ?_, ?_⟩
    · rw [hzeta i hiℓ] at h1; omega
    · rw [hxi i hiℓ] at h2; omega

end BetaRows

section ProfileCells

variable {n : ℕ} (P : Profile n)

theorem mem_cells_profile_iff {i : ℕ} {j : ℤ} :
    ((i : ℤ), j) ∈ P.toBetaRows.cells ↔
      ∃ h : i < n + 1, P.zeta ⟨i, h⟩ + i ≤ j ∧ j < P.xi ⟨i, h⟩ + i := by
  rw [BetaRows.mem_cells]
  constructor
  · rintro ⟨h, h1, h2⟩
    refine ⟨h, ?_, ?_⟩
    · have := Profile.toBetaRows_zeta P ⟨i, h⟩
      simp only at this
      omega
    · have := Profile.toBetaRows_xi P ⟨i, h⟩
      simp only at this
      omega
  · rintro ⟨h, h1, h2⟩
    refine ⟨h, ?_, ?_⟩
    · have := Profile.toBetaRows_zeta P ⟨i, h⟩
      simp only at this
      omega
    · have := Profile.toBetaRows_xi P ⟨i, h⟩
      simp only at this
      omega

/-- Row `i` of the diagram of a profile occupies the contents `ζ_i, …, ξ_i - 1`
(`y_i, …, x_i - 1` in the notation of the paper). -/
theorem mem_cells_profile_iff_content {i : ℕ} {j : ℤ} :
    ((i : ℤ), j) ∈ P.toBetaRows.cells ↔
      ∃ h : i < n + 1, P.zeta ⟨i, h⟩ ≤ content ((i : ℤ), j) ∧
        content ((i : ℤ), j) < P.xi ⟨i, h⟩ := by
  rw [mem_cells_profile_iff]
  simp only [content]
  constructor
  · rintro ⟨h, h1, h2⟩
    exact ⟨h, by omega, by omega⟩
  · rintro ⟨h, h1, h2⟩
    exact ⟨h, by omega, by omega⟩

/-- Every row `i ≤ n` of the diagram of a profile has a cell. -/
theorem exists_cell_row_profile {k : ℕ} (hk : k < n + 1) :
    ∃ j, ((k : ℤ), j) ∈ P.toBetaRows.cells := by
  refine ⟨P.zeta ⟨k, hk⟩ + k, (mem_cells_profile_iff P).mpr ⟨hk, le_rfl, ?_⟩⟩
  have := P.xi_sub_zeta ⟨k, hk⟩
  have := P.r_pos ⟨k, hk⟩
  omega

/-- The rows of the diagram of a profile are `0, …, n`. -/
theorem row_of_mem_cells_profile {a b : ℤ} (h : (a, b) ∈ P.toBetaRows.cells) :
    ∃ k : ℕ, a = k ∧ k < n + 1 := by
  obtain ⟨i, hi1, hiℓ, -, -⟩ := BetaRows.exists_mem_cells h
  exact ⟨i, hi1, hiℓ⟩

/-- The length of row `k` of the diagram of a profile, counted on cells, is `r_k`. -/
theorem sharedColumns_one_profile (k : Fin (n + 1)) :
    sharedColumns P.toBetaRows.cells 1 (k : ℕ) = P.r k := by
  rw [BetaRows.sharedColumns_cells _ le_rfl]
  simp only [Nat.sub_self, add_zero, k.2, ↓reduceIte, BetaRows.overlap, Nat.cast_zero,
    Profile.toBetaRows_xi, Profile.toBetaRows_zeta]
  have h1 := Profile.toBetaRows_xi P k
  have h2 := Profile.toBetaRows_zeta P k
  have := P.xi_sub_zeta k
  omega

/-- Rows `k` and `k + 1` of the diagram of a profile share `g_k + 1` columns. -/
theorem sharedColumns_two_profile (k : Fin n) :
    sharedColumns P.toBetaRows.cells 2 (k : ℕ) = P.g k + 1 := by
  rw [BetaRows.sharedColumns_cells _ (by norm_num)]
  have hk : (k : ℕ) + (2 - 1) < n + 1 := by have := k.2; omega
  simp only [hk, ↓reduceIte, BetaRows.overlap]
  have h1 := Profile.toBetaRows_xi P k.succ
  have h2 := Profile.toBetaRows_zeta P k.castSucc
  have := P.xi_succ_sub_zeta_castSucc k
  simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
  norm_num
  omega

/-- The contents of the diagram of a profile are `0, …, ξ_0 - 1`. -/
theorem contents_cells_profile : contents P.toBetaRows.cells = Finset.Ico 0 (P.xi 0) := by
  have hcover : ∀ i : ℕ, ∀ hi : i < n + 1, ∀ k : ℤ, P.zeta ⟨i, hi⟩ ≤ k → k < P.xi 0 →
      ∃ (r : ℕ) (hr : r < n + 1), P.zeta ⟨r, hr⟩ ≤ k ∧ k < P.xi ⟨r, hr⟩ := by
    intro i
    induction i with
    | zero => exact fun hi k h1 h2 => ⟨0, hi, h1, h2⟩
    | succ i ih =>
      intro hi k h1 h2
      by_cases h : P.zeta ⟨i, by omega⟩ ≤ k
      · exact ih (by omega) k h h2
      · have := P.zeta_le_xi_succ ⟨i, by omega⟩
        simp only [Fin.succ_mk, Fin.castSucc_mk] at this
        exact ⟨i + 1, hi, h1, by omega⟩
  ext k
  simp only [contents, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi1, hiℓ, h1, h2⟩ := BetaRows.exists_mem_cells hx
    have e1 := Profile.toBetaRows_zeta P ⟨i, hiℓ⟩
    have e2 := Profile.toBetaRows_xi P ⟨i, hiℓ⟩
    simp only at e1 e2
    have hz := P.zeta_nonneg ⟨i, hiℓ⟩
    have hx0 : P.xi ⟨i, hiℓ⟩ ≤ P.xi 0 := P.xi_strictAnti.antitone (Fin.zero_le _)
    simp only [content]
    omega
  · rintro ⟨hk0, hk1⟩
    obtain ⟨r, hr, h1, h2⟩ := hcover n (by omega) k
      (by
        have e : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
        rw [e, P.zeta_last]
        exact hk0) hk1
    refine ⟨((r : ℤ), k + r), ?_, by simp [content]⟩
    exact (mem_cells_profile_iff P).mpr ⟨hr, by omega, by omega⟩

/-- `N_F = ξ_0`: the number of contents of the diagram of a profile. -/
theorem span_cells_profile : (span P.toBetaRows.cells : ℤ) = P.xi 0 := by
  unfold span
  rw [contents_cells_profile, Int.card_Ico]
  have := P.xi_pos 0
  omega

/-- `ξ_0 = ∑ r_i - ∑ g_i`. -/
theorem xi_zero_eq_sum : P.xi 0 = ∑ i, (P.r i : ℤ) - ∑ j, (P.g j : ℤ) := by
  have h : P.zeta 0 = ∑ k : Fin n, ((P.r k.succ : ℤ) - P.g k) := by
    unfold Profile.zeta
    simp
  rw [Finset.sum_sub_distrib] at h
  simp only [Profile.xi, h]
  rw [Fin.sum_univ_succ (fun i => (P.r i : ℤ))]
  ring

/-- **Rotation reverses both sequences of the profile.**  The rotation of the diagram of `P`,
translated by `(n, ξ_0 + n - 1)`, is the diagram of the rotated profile `P.rotate`. -/
theorem rotate_cells_profile :
    translate (n, P.xi 0 + n - 1) (rotate P.toBetaRows.cells) = P.rotate.toBetaRows.cells := by
  have hrev : ∀ (i : ℕ) (hi : i < n + 1),
      (⟨i, hi⟩ : Fin (n + 1)).rev = ⟨n - i, by omega⟩ := fun i hi =>
    Fin.ext (by simp only [Fin.val_rev]; omega)
  have e : ∀ a b : ℤ, -(a - n, b - (P.xi 0 + n - 1)) = ((n : ℤ) - a, P.xi 0 + n - 1 - b) :=
    fun a b => by ext <;> simp
  ext ⟨a, b⟩
  rw [mem_translate_mk, mem_rotate, e]
  constructor
  · intro h
    obtain ⟨k, hk1, hk⟩ := row_of_mem_cells_profile P h
    rw [hk1] at h
    obtain ⟨hk, h1, h2⟩ := (mem_cells_profile_iff P).mp h
    obtain rfl : a = ((n - k : ℕ) : ℤ) := by omega
    refine (mem_cells_profile_iff P.rotate).mpr ⟨by omega, ?_, ?_⟩
    · rw [Profile.zeta_rotate, hrev (n - k) (by omega)]
      have e2 : (⟨n - (n - k), by omega⟩ : Fin (n + 1)) = ⟨k, hk⟩ := Fin.ext (by simp; omega)
      rw [e2]
      push_cast [Nat.cast_sub (show k ≤ n by omega)] at *
      omega
    · rw [Profile.xi_rotate, hrev (n - k) (by omega)]
      have e2 : (⟨n - (n - k), by omega⟩ : Fin (n + 1)) = ⟨k, hk⟩ := Fin.ext (by simp; omega)
      rw [e2]
      push_cast [Nat.cast_sub (show k ≤ n by omega)] at *
      omega
  · intro h
    obtain ⟨i, hi1, hi⟩ := row_of_mem_cells_profile P.rotate h
    rw [hi1] at h
    obtain ⟨hi', h1, h2⟩ := (mem_cells_profile_iff P.rotate).mp h
    have hk : (n : ℤ) - a = ((n - i : ℕ) : ℤ) := by omega
    rw [hk]
    refine (mem_cells_profile_iff P).mpr ⟨by omega, ?_, ?_⟩
    · rw [Profile.xi_rotate, hrev i hi'] at h2
      push_cast [Nat.cast_sub (show i ≤ n by omega)] at *
      omega
    · rw [Profile.zeta_rotate, hrev i hi'] at h1
      push_cast [Nat.cast_sub (show i ≤ n by omega)] at *
      omega

/-- The diagram of a profile is a connected skew diagram. -/
theorem isConnectedSkew_cells_profile : IsConnectedSkew P.toBetaRows.cells := by
  refine ⟨P.toBetaRows.isSkew_cells, P.toBetaRows.isEdgeConnected_cells (a := 0) (n := n)
    (by omega) (fun i hi => ?_) (fun j hj => ?_)⟩
  · have h1 := Profile.toBetaRows_xi P ⟨i, hi⟩
    have h2 := Profile.toBetaRows_zeta P ⟨i, hi⟩
    have := P.xi_sub_zeta ⟨i, hi⟩
    have := P.r_pos ⟨i, hi⟩
    simp only at h1 h2
    constructor
    · intro _; omega
    · intro _; omega
  · have h1 := Profile.toBetaRows_xi P ⟨j + 1, by omega⟩
    have h2 := Profile.toBetaRows_zeta P ⟨j, by omega⟩
    have := P.xi_succ_sub_zeta_castSucc ⟨j, hj⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at this
    simp only [BetaRows.overlap, zero_add, Nat.cast_one]
    simp only at h1 h2
    omega

end ProfileCells

/-! ### Diagrams with a given profile -/

/-- A cell set `D` has profile `P` when it is a translate of the diagram of `P`: its rows are
consecutive, row `i` has `r_i` cells and rows `i` and `i + 1` share `g_i + 1` columns
(`HasProfile.sharedColumns_one`, `HasProfile.sharedColumns_two`). -/
def HasProfile {n : ℕ} (D : Diagram) (P : Profile n) : Prop :=
  ∃ v : ℤ × ℤ, D = translate v P.toBetaRows.cells

theorem hasProfile_cells {n : ℕ} (P : Profile n) : HasProfile P.toBetaRows.cells P :=
  ⟨0, translate_zero.symm⟩

theorem HasProfile.isConnectedSkew {n : ℕ} {D : Diagram} {P : Profile n} (h : HasProfile D P) :
    IsConnectedSkew D := by
  obtain ⟨v, rfl⟩ := h
  exact isConnectedSkew_translate v (isConnectedSkew_cells_profile P)

/-- A translate of a diagram with profile `P` has profile `P`. -/
theorem HasProfile.translated {n : ℕ} {D : Diagram} {P : Profile n} (h : HasProfile D P)
    (w : ℤ × ℤ) : HasProfile (translate w D) P := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨w + v, SkewGluing.translate_translate w v⟩

/-- **A diagram is determined by its profile.**  Two cell sets with the same profile are
translates of one another. -/
theorem eq_translate_of_hasProfile {n : ℕ} {D E : Diagram} {P : Profile n} (hD : HasProfile D P)
    (hE : HasProfile E P) : ∃ v : ℤ × ℤ, E = translate v D := by
  obtain ⟨v, rfl⟩ := hD
  obtain ⟨w, rfl⟩ := hE
  refine ⟨w - v, ?_⟩
  rw [SkewGluing.translate_translate]
  simp

/-- **Rotation reverses both sequences.**  The rotation of a diagram with profile `P` has the
profile `P.rotate`, whose `r` and `g` are those of `P` reversed. -/
theorem HasProfile.rotated {n : ℕ} {D : Diagram} {P : Profile n} (h : HasProfile D P) :
    HasProfile (rotate D) P.rotate := by
  obtain ⟨v, rfl⟩ := h
  have h1 : rotate (translate v P.toBetaRows.cells) =
      translate (-v) (rotate P.toBetaRows.cells) := by
    ext y
    rw [mem_rotate, mem_translate, mem_translate, mem_rotate]
    simp [sub_eq_add_neg, add_comm]
  have h2 : rotate P.toBetaRows.cells =
      translate (-((n : ℤ), P.xi 0 + n - 1)) P.rotate.toBetaRows.cells := by
    rw [← rotate_cells_profile P, SkewGluing.translate_translate, neg_add_cancel, translate_zero]
  exact ⟨-v + -((n : ℤ), P.xi 0 + n - 1), by rw [h1, h2, SkewGluing.translate_translate]⟩

/-- `N_F = ξ_0 = ∑ r_i - ∑ g_i` for a diagram with profile `P`. -/
theorem HasProfile.span_eq {n : ℕ} {D : Diagram} {P : Profile n} (h : HasProfile D P) :
    (span D : ℤ) = P.xi 0 ∧ P.xi 0 = ∑ i, (P.r i : ℤ) - ∑ j, (P.g j : ℤ) := by
  obtain ⟨v, rfl⟩ := h
  rw [span_translate]
  exact ⟨span_cells_profile P, xi_zero_eq_sum P⟩

/-- A diagram with profile `P` whose first row is row `v₁` has row `v₁ + k` of length `r_k`. -/
theorem HasProfile.sharedColumns_one {n : ℕ} {D : Diagram} {P : Profile n} {v : ℤ × ℤ}
    (h : D = translate v P.toBetaRows.cells) (k : Fin (n + 1)) :
    sharedColumns D 1 ((k : ℤ) + v.1) = P.r k := by
  subst h
  rw [sharedColumns_translate]
  exact sharedColumns_one_profile P k

/-- A diagram with profile `P` whose first row is row `v₁` has rows `v₁ + k` and `v₁ + k + 1`
sharing `g_k + 1` columns. -/
theorem HasProfile.sharedColumns_two {n : ℕ} {D : Diagram} {P : Profile n} {v : ℤ × ℤ}
    (h : D = translate v P.toBetaRows.cells) (k : Fin n) :
    sharedColumns D 2 ((k : ℤ) + v.1) = P.g k + 1 := by
  subst h
  rw [sharedColumns_translate]
  exact sharedColumns_two_profile P k

/-- The diagrams of two profiles that are translates of one another have the same profile. -/
theorem profile_eq_of_cells_eq_translate {n m : ℕ} (P : Profile n) (Q : Profile m) (u : ℤ × ℤ)
    (h : P.toBetaRows.cells = translate u Q.toBetaRows.cells) :
    (⟨n, P⟩ : Σ n, Profile n) = ⟨m, Q⟩ := by
  have hu : u.1 = 0 := by
    obtain ⟨j, hj⟩ := exists_cell_row_profile P (k := 0) (by omega)
    obtain ⟨j', hj'⟩ := exists_cell_row_profile Q (k := 0) (by omega)
    have h1 := hj
    rw [h, mem_translate_mk] at h1
    obtain ⟨k1, hk1, -⟩ := row_of_mem_cells_profile Q h1
    have h3 : (((0 : ℕ) : ℤ) + u.1, j' + u.2) ∈ P.toBetaRows.cells := by
      rw [h, mem_translate_mk]
      simpa using hj'
    obtain ⟨k2, hk2, -⟩ := row_of_mem_cells_profile P h3
    simp only [Nat.cast_zero, zero_sub, zero_add] at hk1 hk2
    omega
  have hnm : n = m := by
    obtain ⟨j, hj⟩ := exists_cell_row_profile P (k := n) (by omega)
    obtain ⟨j', hj'⟩ := exists_cell_row_profile Q (k := m) (by omega)
    have h1 := hj
    rw [h, mem_translate_mk] at h1
    obtain ⟨k1, hk1, hk1'⟩ := row_of_mem_cells_profile Q h1
    have h3 : (((m : ℕ) : ℤ) + u.1, j' + u.2) ∈ P.toBetaRows.cells := by
      rw [h, mem_translate_mk]
      simpa using hj'
    obtain ⟨k2, hk2, hk2'⟩ := row_of_mem_cells_profile P h3
    omega
  subst hnm
  have key : ∀ (d : ℕ) (i : ℕ), sharedColumns P.toBetaRows.cells d i =
      sharedColumns Q.toBetaRows.cells d i := fun d i => by
    have := sharedColumns_translate Q.toBetaRows.cells u d (i : ℤ)
    rw [hu, add_zero] at this
    rw [h, this]
  have hr : P.r = Q.r := funext fun k => by
    rw [← sharedColumns_one_profile P k, ← sharedColumns_one_profile Q k]
    exact key 1 (k : ℕ)
  have hg : P.g = Q.g := funext fun k => by
    have := key 2 (k : ℕ)
    rw [sharedColumns_two_profile P k, sharedColumns_two_profile Q k] at this
    omega
  rw [Profile.ext hr hg]

/-- **A profile is determined by the diagram.**  A cell set has at most one profile. -/
theorem hasProfile_unique {n m : ℕ} {D : Diagram} {P : Profile n} {Q : Profile m}
    (hP : HasProfile D P) (hQ : HasProfile D Q) : (⟨n, P⟩ : Σ n, Profile n) = ⟨m, Q⟩ := by
  obtain ⟨v, hv⟩ := hP
  obtain ⟨w, hw⟩ := hQ
  refine profile_eq_of_cells_eq_translate P Q (w - v) ?_
  have e : v + (w - v) = w := by abel
  apply translate_injective v
  rw [SkewGluing.translate_translate, e]
  exact hv.symm.trans hw

/-! ### Every connected diagram has a profile -/

/-- **Every connected skew cell set is a translate of the diagram of a profile.** -/
theorem exists_hasProfile {D : Diagram} (hD : IsConnectedSkew D) :
    ∃ (n : ℕ) (P : Profile n), HasProfile D P := by
  obtain ⟨hs, hne, hconn⟩ := hD
  have hrows : (D.image Prod.fst).Nonempty := hne.image _
  set r0 := (D.image Prod.fst).min' hrows with hr0
  set N := (D.image Prod.fst).max' hrows with hN
  have hrN : r0 ≤ N := Finset.min'_le_max' _ hrows
  set w : ℤ × ℤ := (r0, 0) with hw
  set n : ℕ := (N - r0).toNat with hn
  have hmem : ∀ x : ℤ × ℤ, x ∈ translate (-w) D ↔ (x.1 + r0, x.2) ∈ D := by
    intro x
    rw [mem_translate]
    have : x - -w = (x.1 + r0, x.2) := by ext <;> simp [hw]
    rw [this]
  have hD0 : IsConnectedSkew (translate (-w) D) :=
    isConnectedSkew_translate _ ⟨hs, hne, hconn⟩
  have hnn : ∀ x ∈ translate (-w) D, 0 ≤ x.1 := by
    intro x hx
    have := Finset.min'_le (D.image Prod.fst) _
      (Finset.mem_image_of_mem Prod.fst ((hmem x).mp hx))
    simp only at this
    omega
  have hℓ : ∀ x ∈ translate (-w) D, x.1 < ((n + 1 : ℕ) : ℤ) := by
    intro x hx
    have := Finset.le_max' (D.image Prod.fst) _
      (Finset.mem_image_of_mem Prod.fst ((hmem x).mp hx))
    simp only at this
    push_cast
    omega
  obtain ⟨y0, hy0, hy01⟩ := Finset.mem_image.mp (Finset.min'_mem (D.image Prod.fst) hrows)
  obtain ⟨y1, hy1, hy11⟩ := Finset.mem_image.mp (Finset.max'_mem (D.image Prod.fst) hrows)
  have hx0 : (((0 : ℕ) : ℤ), y0.2) ∈ translate (-w) D := by
    rw [hmem]
    simp only [Nat.cast_zero, zero_add]
    have e : y0 = (r0, y0.2) := Prod.ext hy01 rfl
    rw [← e]
    exact hy0
  have hxn : ((n : ℤ), y1.2) ∈ translate (-w) D := by
    rw [hmem]
    have : (n : ℤ) + r0 = y1.1 := by omega
    simp only [this, Prod.mk.eta]
    exact hy1
  have h0 : ∃ c, ((0 : ℤ), c) ∈ translate (-w) D := ⟨y0.2, by simpa using hx0⟩
  -- consecutive rows share a column
  have hshare : ∀ k : ℕ, k < n → ∃ c, ((k : ℤ), c) ∈ translate (-w) D ∧
      ((k : ℤ) + 1, c) ∈ translate (-w) D := fun k hk =>
    exists_shared_column_of_reach (hD0.2.2 _ hx0 _ hxn) (by simp) (by omega)
  have hrowne : ∀ k : ℕ, k < n + 1 → ∃ c, ((k : ℤ), c) ∈ translate (-w) D := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨_, hx0⟩
    · obtain ⟨c, -, hc⟩ := hshare (k - 1) (by omega)
      refine ⟨c, ?_⟩
      have : ((k - 1 : ℕ) : ℤ) + 1 = k := by omega
      rwa [this] at hc
  let B := presentation hD0.1 h0 (n + 1)
  have hB : B.cells = translate (-w) D := cells_presentation hD0.1 h0 hnn hℓ
  have hzx : ∀ k, k < n + 1 → B.zeta k < B.xi k := by
    intro k hk
    obtain ⟨c, hc⟩ := hrowne k hk
    have hrow : (columnsOfRow (translate (-w) D) k).Nonempty := ⟨c, mem_columnsOfRow.mpr hc⟩
    have h1 := leftEdge_le (D := translate (-w) D) (i := (k : ℤ)) le_rfl hc
    have h2 := Finset.le_max' _ _ (mem_columnsOfRow.mpr hc)
    simp only [B, presentation, rightEdge, hrow, ↓reduceDIte]
    omega
  have hov : ∀ k, k < n → 0 < B.overlap 1 k := by
    intro k hk
    obtain ⟨c, hc1, hc2⟩ := hshare k hk
    have hrow : (columnsOfRow (translate (-w) D) ((k : ℤ) + 1)).Nonempty :=
      ⟨c, mem_columnsOfRow.mpr hc2⟩
    have h1 := leftEdge_le (D := translate (-w) D) (i := (k : ℤ)) le_rfl hc1
    have h2 := Finset.le_max' _ _ (mem_columnsOfRow.mpr hc2)
    simp only [BetaRows.overlap, B, presentation, Nat.cast_add, Nat.cast_one, rightEdge, hrow,
      ↓reduceDIte]
    omega
  obtain ⟨P, hP⟩ := B.exists_profile_cells hzx hov
  have hP' : translate (-w) D = translate (0, B.zeta n) P.toBetaRows.cells := hB.symm.trans hP
  have e1 : translate w (translate (-w) D) = D := by
    rw [SkewGluing.translate_translate]
    simp [translate_zero]
  refine ⟨n, P, w + (0, B.zeta n), ?_⟩
  calc D = translate w (translate (-w) D) := e1.symm
    _ = translate w (translate (0, B.zeta n) P.toBetaRows.cells) := by rw [hP']
    _ = translate (w + (0, B.zeta n)) P.toBetaRows.cells := SkewGluing.translate_translate _ _

/-- The profile of a connected cell set: the number of rows minus one, and the profile. -/
noncomputable def profileOf {D : Diagram} (hD : IsConnectedSkew D) : Σ n, Profile n :=
  ⟨Classical.choose (exists_hasProfile hD),
    Classical.choose (Classical.choose_spec (exists_hasProfile hD))⟩

theorem hasProfile_profileOf {D : Diagram} (hD : IsConnectedSkew D) :
    HasProfile D (profileOf hD).2 :=
  Classical.choose_spec (Classical.choose_spec (exists_hasProfile hD))

theorem profileOf_eq_of_hasProfile {D : Diagram} (hD : IsConnectedSkew D) {n : ℕ} {P : Profile n}
    (h : HasProfile D P) : profileOf hD = ⟨n, P⟩ :=
  hasProfile_unique (hasProfile_profileOf hD) h

/-! ### The translation classes of connected diagrams are the profiles -/

/-- Two connected skew cell sets are equivalent when they are translates of one another. -/
def translationSetoid : Setoid {D : Diagram // IsConnectedSkew D} where
  r D E := ∃ v : ℤ × ℤ, E.1 = translate v D.1
  iseqv :=
    { refl := fun D => ⟨0, translate_zero.symm⟩
      symm := fun {D E} ⟨v, hv⟩ =>
        ⟨-v, by rw [hv, SkewGluing.translate_translate]; simp [translate_zero]⟩
      trans := fun {D E F} ⟨v, hv⟩ ⟨w, hw⟩ =>
        ⟨w + v, by rw [hw, hv, SkewGluing.translate_translate]⟩ }

/-- The connected diagrams up to translation. -/
abbrev ConnectedDiagramClass : Type := Quotient translationSetoid

/-- **`lem:profiles`.**  The connected diagrams up to translation are in bijection with the
profiles.  The map from diagrams sends a diagram to its profile (`profileOf`), whose `r` and `g`
are the row lengths and the numbers of shared columns of adjacent rows minus one
(`HasProfile.sharedColumns_one`, `HasProfile.sharedColumns_two`); the inverse sends a profile to
the class of its diagram `P.toBetaRows.cells`. -/
noncomputable def profileEquiv : ConnectedDiagramClass ≃ Σ n, Profile n where
  toFun := Quotient.lift (fun D => profileOf D.2) fun D E ⟨v, hv⟩ =>
    (profileOf_eq_of_hasProfile E.2 (by
      rw [hv]
      exact (hasProfile_profileOf D.2).translated v)).symm
  invFun p := Quotient.mk translationSetoid
    ⟨p.2.toBetaRows.cells, isConnectedSkew_cells_profile p.2⟩
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h D =>
      obtain ⟨v, hv⟩ := hasProfile_profileOf D.2
      exact Quotient.sound ⟨v, hv⟩
  right_inv := by
    rintro ⟨n, P⟩
    exact profileOf_eq_of_hasProfile _ (hasProfile_cells P)

end SkewBase
