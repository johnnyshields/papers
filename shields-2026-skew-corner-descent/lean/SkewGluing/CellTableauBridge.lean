import SkewGluing.SchurBridge
import SkewGluing.DiagramSchur

/-!
# Connected cell diagrams and tableau specialization

TODO-COPIED: Young-shape translation is adapted from
`skew-factor-gluing/lean/SkewGluing/CellSchur.lean`.
Supports `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `eq:jt`, `lem:cofactor`). Sorry-free.
-/

namespace SkewGluing

namespace Profile

variable {n : ℕ}

theorem mem_cells_top (P : Profile n) : (0, P.zeta 0) ∈ P.cells := by
  simpa using P.row_left_mem_cells 0

theorem row_of_mem_cells (P : Profile n) {x : ℤ × ℤ} (hx : x ∈ P.cells) : 0 ≤ x.1 := by
  obtain ⟨i, hi, _⟩ := P.mem_cells.mp hx
  omega

theorem nonneg_col_of_mem_cells (P : Profile n) {x : ℤ × ℤ} (hx : x ∈ P.cells) : 0 ≤ x.2 := by
  obtain ⟨i, _, h⟩ := P.mem_cells.mp hx
  have := P.zeta_nonneg i
  omega

theorem mem_cells_nat (P : Profile n) (i j : ℕ) :
    ((i : ℤ), (j : ℤ)) ∈ P.cells ↔ (i, j) ∈ Shields.skewCells P.lam P.mu := by
  rw [P.mem_cells, Shields.mem_skewCells, P.mem_lam, P.mem_mu]
  constructor
  · rintro ⟨k, hk, hlow, hhi⟩
    have hi : k.val = i := by exact_mod_cast hk
    subst hi
    exact ⟨⟨k.isLt, hhi⟩, fun ⟨_, hj⟩ => (not_lt_of_ge hlow) hj⟩
  · rintro ⟨⟨hi, hhi⟩, hlow⟩
    refine ⟨⟨i, hi⟩, rfl, ?_, hhi⟩
    exact le_of_not_gt fun hj => hlow ⟨hi, hj⟩

end Profile

/-- The Young diagram `lam` with every row of its first `L` rows moved `c` columns to the right
and the vacated cells filled in: the rows of the result are `lam_i + c` for `i < L`. -/
def shiftRows (lam : YoungDiagram) (L c : ℕ) (hL : ∀ x ∈ lam, x.1 < L) : YoungDiagram where
  cells := lam.cells.image (fun x => (x.1, x.2 + c)) ∪ (Finset.range L ×ˢ Finset.range c)
  isLowerSet := by
    intro x y hyx hx
    rw [Finset.mem_coe, Finset.mem_union] at hx ⊢
    obtain ⟨h1, h2⟩ := Prod.mk_le_mk.mp (show (y.1, y.2) ≤ (x.1, x.2) from hyx)
    rcases hx with hx | hx
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      by_cases hy : y.2 < c
      · right
        have := hL z hz
        simp only [Finset.mem_product, Finset.mem_range]
        exact ⟨by omega, hy⟩
      · left
        refine Finset.mem_image.mpr ⟨(y.1, y.2 - c), ?_, by ext <;> simp; omega⟩
        exact lam.isLowerSet (show (y.1, y.2 - c) ≤ z from
          Prod.mk_le_mk.mpr ⟨h1, by simp at h2; omega⟩) hz
    · right
      simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
      exact ⟨by omega, by omega⟩

/-- Membership in `shiftRows`. -/
theorem mem_shiftRows {lam : YoungDiagram} {L c : ℕ} {hL : ∀ x ∈ lam, x.1 < L} {a b : ℕ} :
    (a, b) ∈ shiftRows lam L c hL ↔ (a < L ∧ b < c) ∨ (c ≤ b ∧ (a, b - c) ∈ lam) := by
  change (a, b) ∈ (lam.cells.image (fun x => (x.1, x.2 + c)) ∪
    (Finset.range L ×ˢ Finset.range c)) ↔ _
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Prod.mk.injEq]
  constructor
  · rintro (⟨z, hz, rfl, rfl⟩ | h)
    · right; exact ⟨by omega, by simpa using hz⟩
    · left; exact h
  · rintro (h | ⟨h1, h2⟩)
    · right; exact h
    · left; exact ⟨(a, b - c), h2, rfl, by omega⟩

/-- The cell diagram of the skew shape `λ / μ`, as a set of cells of `ℤ × ℤ`. -/
def skewDiagram (lam mu : YoungDiagram) : Diagram :=
  (Shields.skewCells lam mu).image fun c => ((c.1 : ℤ), (c.2 : ℤ))

/-- Membership in the cell diagram of a skew shape. -/
theorem mem_skewDiagram_nat {lam mu : YoungDiagram} (i j : ℕ) :
    ((i : ℤ), (j : ℤ)) ∈ skewDiagram lam mu ↔ (i, j) ∈ Shields.skewCells lam mu := by
  simp only [skewDiagram, Finset.mem_image, Prod.mk.injEq, Nat.cast_inj]
  constructor
  · rintro ⟨⟨a, b⟩, h, rfl, rfl⟩; exact h
  · intro h; exact ⟨(i, j), h, rfl, rfl⟩

theorem nat_cell_of_mem_skewDiagram {lam mu : YoungDiagram} {x : ℤ × ℤ}
    (h : x ∈ skewDiagram lam mu) : ∃ i j : ℕ, x = ((i : ℤ), (j : ℤ)) := by
  simp only [skewDiagram, Finset.mem_image] at h
  obtain ⟨⟨i, j⟩, -, rfl⟩ := h
  exact ⟨i, j, rfl⟩

/-- The skew cells of the shifted shapes are those of the shape moved `c` columns to the right. -/
theorem skewCells_shiftRows {lam mu : YoungDiagram} (hmu : mu ≤ lam) (L c : ℕ)
    (hL : ∀ x ∈ lam, x.1 < L) (a b : ℕ) :
    (a, b) ∈ Shields.skewCells (shiftRows lam L c hL) (shiftRows mu L c fun x hx => hL x (hmu hx))
      ↔ c ≤ b ∧ (a, b - c) ∈ Shields.skewCells lam mu := by
  rw [Shields.mem_skewCells, Shields.mem_skewCells, mem_shiftRows, mem_shiftRows]
  by_cases hb : b < c
  · constructor
    · rintro ⟨h1, h2⟩
      exfalso
      apply h2
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · omega
    · rintro ⟨h, -⟩; omega
  · push Not at hb
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨hb, ?_, ?_⟩
      · rcases h1 with h1 | h1
        · omega
        · exact h1.2
      · intro hm
        exact h2 (Or.inr ⟨hb, hm⟩)
    · rintro ⟨-, h1, h2⟩
      refine ⟨Or.inr ⟨hb, h1⟩, ?_⟩
      rintro (h | h)
      · omega
      · exact h2 h.2

/-- The tableau skew Schur polynomial of `λ / μ` depends only on the cell diagram up to
translation: if the cell diagram of `λ / μ` is a translate of the cell diagram of a profile,
it is the tableau polynomial of the profile's shape. -/
theorem skewSchur_eq_of_translate {R : Type*} [CommRing R] {lam mu : YoungDiagram} (hmu : mu ≤ lam)
    {n : ℕ} (P : Profile n) (v : ℤ × ℤ) (hv : skewDiagram lam mu = translate v P.cells)
    (b : ℕ) (β : ℕ → R) : Shields.skewSchur lam mu b β = Shields.skewSchur P.lam P.mu b β := by
  set L := lam.colLen 0 with hLdef
  have hL : ∀ x ∈ lam, x.1 < L := by
    intro x hx
    rw [hLdef, ← YoungDiagram.mem_iff_lt_colLen]
    exact lam.isLowerSet
      (show ((x.1, 0) : ℕ × ℕ) ≤ x from Prod.mk_le_mk.mpr ⟨le_refl _, Nat.zero_le _⟩) hx
  set c : ℕ := (-v.2).toNat with hc
  have hvc : 0 ≤ v.2 + c := by omega
  have hv1 : 0 ≤ v.1 := by
    have e : (v.1, v.2 + P.zeta 0) - v = (0, P.zeta 0) := by ext <;> simp
    have h1 : (v.1, v.2 + P.zeta 0) ∈ skewDiagram lam mu := by
      rw [hv, mem_translate, e]; exact P.mem_cells_top
    obtain ⟨i, j, hij⟩ := nat_cell_of_mem_skewDiagram h1
    have := congrArg Prod.fst hij
    simp only at this
    omega
  set lam' := shiftRows lam L c hL with hlam'
  set mu' := shiftRows mu L c (fun x hx => hL x (hmu hx)) with hmu'
  -- step 1: shift `λ / μ` to the right by `c`
  have step1 : Shields.skewSchur lam' mu' b β = Shields.skewSchur lam mu b β := by
    refine Shields.skewSchur_translate (lam := lam') (mu := mu') (lam' := lam) (mu' := mu)
      (di := 0) (dj := c) (fun i j => ?_) (fun i j hc' => ?_) β
    · rw [Nat.add_zero, skewCells_shiftRows hmu L c hL i (j + c), Nat.add_sub_cancel]
      simp
    · have := (skewCells_shiftRows hmu L c hL i j).mp hc'
      exact ⟨Nat.zero_le _, this.1⟩
  -- the shifted shape is a translate of the cell diagram of the profile
  have hdiag : ∀ i j : ℕ, (i, j) ∈ Shields.skewCells lam' mu' ↔
      ((i : ℤ) - v.1, (j : ℤ) - (v.2 + c)) ∈ P.cells := by
    intro i j
    rw [skewCells_shiftRows hmu L c hL]
    have e : ((i : ℤ) - v.1, (j : ℤ) - (v.2 + c)) =
        ((i : ℤ), (j : ℤ) - c) - v := by ext <;> simp; ring
    rw [e, ← mem_translate, ← hv]
    constructor
    · rintro ⟨hj, h⟩
      have : ((j : ℤ) - c) = ((j - c : ℕ) : ℤ) := by push_cast [Nat.cast_sub hj]; ring
      rw [this]
      exact (mem_skewDiagram_nat i (j - c)).mpr h
    · intro h
      obtain ⟨i', j', hij⟩ := nat_cell_of_mem_skewDiagram h
      have h1 : (i : ℤ) = i' := congrArg Prod.fst hij
      have h2 : (j : ℤ) - c = j' := congrArg Prod.snd hij
      have hj : c ≤ j := by omega
      have hi : i = i' := by omega
      have hj' : j - c = j' := by omega
      subst hi hj'
      exact ⟨hj, (mem_skewDiagram_nat i (j - c)).mp (by
        have : ((j : ℤ) - c) = ((j - c : ℕ) : ℤ) := by push_cast [Nat.cast_sub hj]; ring
        rw [this] at h; exact h)⟩
  -- step 2: compare with the shape of the profile
  have step2 : Shields.skewSchur lam' mu' b β = Shields.skewSchur P.lam P.mu b β := by
    refine Shields.skewSchur_translate (lam := lam') (mu := mu') (lam' := P.lam) (mu' := P.mu)
      (di := v.1.toNat) (dj := (v.2 + c).toNat) (fun i j => ?_) (fun i j hc' => ?_) β
    · rw [hdiag]
      have e : (((i + v.1.toNat : ℕ) : ℤ) - v.1, ((j + (v.2 + c).toNat : ℕ) : ℤ) - (v.2 + c)) =
          ((i : ℤ), (j : ℤ)) := by
        push_cast
        rw [Int.toNat_of_nonneg hv1, Int.toNat_of_nonneg hvc]
        ext <;> simp
      rw [e, P.mem_cells_nat]
    · have h := (hdiag i j).mp hc'
      have h1 := P.row_of_mem_cells h
      have h2 := P.nonneg_col_of_mem_cells h
      simp only at h1 h2
      omega
  rw [← step1, step2]

/-- Connected cell Schur functions specialize to the tableau sum in any finite alphabet. -/
theorem aeval_cellSchur_skewDiagram {R : Type*} [CommRing R] [Algebra ℚ R]
    {lam mu : YoungDiagram} (hmu : mu ≤ lam)
    (hD : IsConnectedSkew (skewDiagram lam mu)) (b : ℕ) (β : ℕ → R) :
    MvPolynomial.aeval (fun k : ℕ+ => Shields.completeHom b k β)
      (cellSchur (skewDiagram lam mu) hD.1) = Shields.skewSchur lam mu b β := by
  obtain ⟨n, P, v, hv⟩ := hD.exists_profile_cells
  rw [cellSchur_eq_profile hD P v hv, Profile.aeval_schur_eq_skewSchur]
  exact (skewSchur_eq_of_translate hmu P v hv b β).symm

end SkewGluing
