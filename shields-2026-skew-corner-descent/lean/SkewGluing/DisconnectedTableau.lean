import SkewGluing.CellTableauBridge

/-!
# Component products and tableau sums

TODO-COPIED: the tableau split and quadrant constructions are adapted from
`skew-factor-gluing/lean/SkewGluing/CellSchurTableau.lean`.
Supports `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `eq:corner-factors`, `lem:cofactor`). Sorry-free.
-/

namespace SkewGluing

open Shields

/-! ### The tableau sum over a split shape -/

section Split

variable {lam mu lam₁ mu₁ lam₂ mu₂ : YoungDiagram} {b : ℕ}

/-- The skew shape `λ / μ` is the disjoint union of `λ₁ / μ₁` and `λ₂ / μ₂`, and no cell of the
first shares a row or a column with a cell of the second. -/
structure SkewSplit (lam mu lam₁ mu₁ lam₂ mu₂ : YoungDiagram) : Prop where
  /-- The cells of `λ / μ` are those of the two pieces. -/
  union : skewCells lam mu = skewCells lam₁ mu₁ ∪ skewCells lam₂ mu₂
  /-- The two pieces have no common cell. -/
  disjoint : Disjoint (skewCells lam₁ mu₁) (skewCells lam₂ mu₂)
  /-- No row meets both pieces. -/
  row : ∀ i j₁ j₂ : ℕ, (i, j₁) ∈ skewCells lam₁ mu₁ → (i, j₂) ∈ skewCells lam₂ mu₂ → False
  /-- No column meets both pieces. -/
  col : ∀ i₁ i₂ j : ℕ, (i₁, j) ∈ skewCells lam₁ mu₁ → (i₂, j) ∈ skewCells lam₂ mu₂ → False

namespace SkewSplit

variable (S : SkewSplit lam mu lam₁ mu₁ lam₂ mu₂)
include S

theorem notMem₂ {c : ℕ × ℕ} (h : c ∈ skewCells lam₁ mu₁) : c ∉ skewCells lam₂ mu₂ :=
  Finset.disjoint_left.mp S.disjoint h

theorem notMem₁ {c : ℕ × ℕ} (h : c ∈ skewCells lam₂ mu₂) : c ∉ skewCells lam₁ mu₁ :=
  fun h' => Finset.disjoint_left.mp S.disjoint h' h

/-- The pointwise sum of a tableau of each piece is a tableau of the whole shape. -/
def sumTableau (T₁ : BoundedSkewSSYT lam₁ mu₁ b) (T₂ : BoundedSkewSSYT lam₂ mu₂ b) :
    BoundedSkewSSYT lam mu b := by
  have h1 : ∀ i j, (i, j) ∈ skewCells lam₁ mu₁ → T₂ i j = 0 :=
    fun i j h => T₂.zeros (S.notMem₂ h)
  have h2 : ∀ i j, (i, j) ∈ skewCells lam₂ mu₂ → T₁ i j = 0 :=
    fun i j h => T₁.zeros (S.notMem₁ h)
  refine ⟨{ entry := fun i j => T₁ i j + T₂ i j, row_weak' := ?_, col_strict' := ?_,
            zeros' := ?_ }, ?_⟩
  · intro i j₁ j₂ hj hlam hmu
    obtain ⟨hc₁, hc₂⟩ := mem_skewCells_of_row hj hlam hmu
    rw [S.union, Finset.mem_union] at hc₁ hc₂
    rcases hc₁ with hc₁ | hc₁ <;> rcases hc₂ with hc₂ | hc₂
    · have := T₁.1.row_weak hj (mem_skewCells.mp hc₂).1 (mem_skewCells.mp hc₁).2
      change T₁ i j₁ + T₂ i j₁ ≤ T₁ i j₂ + T₂ i j₂
      rw [h1 _ _ hc₁, h1 _ _ hc₂]; omega
    · exact (S.row i j₁ j₂ hc₁ hc₂).elim
    · exact (S.row i j₂ j₁ hc₂ hc₁).elim
    · have := T₂.1.row_weak hj (mem_skewCells.mp hc₂).1 (mem_skewCells.mp hc₁).2
      change T₁ i j₁ + T₂ i j₁ ≤ T₁ i j₂ + T₂ i j₂
      rw [h2 _ _ hc₁, h2 _ _ hc₂]; omega
  · intro i₁ i₂ j hi hlam hmu
    obtain ⟨hc₁, hc₂⟩ := mem_skewCells_of_col hi hlam hmu
    rw [S.union, Finset.mem_union] at hc₁ hc₂
    rcases hc₁ with hc₁ | hc₁ <;> rcases hc₂ with hc₂ | hc₂
    · have := T₁.1.col_strict hi (mem_skewCells.mp hc₂).1 (mem_skewCells.mp hc₁).2
      change T₁ i₁ j + T₂ i₁ j < T₁ i₂ j + T₂ i₂ j
      rw [h1 _ _ hc₁, h1 _ _ hc₂]; omega
    · exact (S.col i₁ i₂ j hc₁ hc₂).elim
    · exact (S.col i₂ i₁ j hc₂ hc₁).elim
    · have := T₂.1.col_strict hi (mem_skewCells.mp hc₂).1 (mem_skewCells.mp hc₁).2
      change T₁ i₁ j + T₂ i₁ j < T₁ i₂ j + T₂ i₂ j
      rw [h2 _ _ hc₁, h2 _ _ hc₂]; omega
  · intro i j hc
    have h₁ : (i, j) ∉ skewCells lam₁ mu₁ := fun h =>
      hc (by rw [S.union]; exact Finset.mem_union_left _ h)
    have h₂ : (i, j) ∉ skewCells lam₂ mu₂ := fun h =>
      hc (by rw [S.union]; exact Finset.mem_union_right _ h)
    change T₁ i j + T₂ i j = 0
    rw [T₁.zeros h₁, T₂.zeros h₂]
  · intro i j hc
    rw [S.union, Finset.mem_union] at hc
    change T₁ i j + T₂ i j < b
    rcases hc with hc | hc
    · rw [h1 _ _ hc]; exact T₁.lt_of_mem_cells hc
    · rw [h2 _ _ hc, zero_add]; exact T₂.lt_of_mem_cells hc

end SkewSplit

/-- The restriction of a tableau to a sub-shape: keep the entries on the cells of `λ' / μ'` and
set the others to zero. -/
def restrictTableau {lam' mu' : YoungDiagram} (T : BoundedSkewSSYT lam mu b)
    (hsub : skewCells lam' mu' ⊆ skewCells lam mu) : BoundedSkewSSYT lam' mu' b := by
  refine ⟨{ entry := fun i j => if (i, j) ∈ skewCells lam' mu' then T i j else 0,
            row_weak' := ?_, col_strict' := ?_, zeros' := ?_ }, ?_⟩
  · intro i j₁ j₂ hj hlam hmu
    obtain ⟨hc₁, hc₂⟩ := mem_skewCells_of_row hj hlam hmu
    rw [ite_eq_left hc₁, ite_eq_left hc₂]
    exact T.1.row_weak hj (mem_skewCells.mp (hsub hc₂)).1 (mem_skewCells.mp (hsub hc₁)).2
  · intro i₁ i₂ j hi hlam hmu
    obtain ⟨hc₁, hc₂⟩ := mem_skewCells_of_col hi hlam hmu
    rw [ite_eq_left hc₁, ite_eq_left hc₂]
    exact T.1.col_strict hi (mem_skewCells.mp (hsub hc₂)).1 (mem_skewCells.mp (hsub hc₁)).2
  · intro i j hc
    exact ite_eq_right hc
  · intro i j hc
    change (if (i, j) ∈ skewCells lam' mu' then T i j else 0) < b
    rw [ite_eq_left hc]
    exact T.lt_of_mem_cells (hsub hc)

theorem restrictTableau_apply {lam' mu' : YoungDiagram} (T : BoundedSkewSSYT lam mu b)
    (hsub : skewCells lam' mu' ⊆ skewCells lam mu) (i j : ℕ) :
    restrictTableau T hsub i j = if (i, j) ∈ skewCells lam' mu' then T i j else 0 := rfl

namespace SkewSplit

variable (S : SkewSplit lam mu lam₁ mu₁ lam₂ mu₂)
include S

theorem sub₁ : skewCells lam₁ mu₁ ⊆ skewCells lam mu := by
  rw [S.union]; exact Finset.subset_union_left

theorem sub₂ : skewCells lam₂ mu₂ ⊆ skewCells lam mu := by
  rw [S.union]; exact Finset.subset_union_right

/-- A tableau of a split shape is a pair of tableaux of the pieces. -/
def tableauEquiv :
    BoundedSkewSSYT lam₁ mu₁ b × BoundedSkewSSYT lam₂ mu₂ b ≃ BoundedSkewSSYT lam mu b where
  toFun p := S.sumTableau p.1 p.2
  invFun T := (restrictTableau T S.sub₁, restrictTableau T S.sub₂)
  left_inv p := by
    obtain ⟨T₁, T₂⟩ := p
    refine Prod.ext ?_ ?_
    · apply BoundedSkewSSYT.ext
      intro i j
      rw [restrictTableau_apply]
      change (if (i, j) ∈ skewCells lam₁ mu₁ then T₁ i j + T₂ i j else 0) = T₁ i j
      by_cases h : (i, j) ∈ skewCells lam₁ mu₁
      · rw [ite_eq_left h, T₂.zeros (S.notMem₂ h)]; rfl
      · rw [ite_eq_right h, T₁.zeros h]
    · apply BoundedSkewSSYT.ext
      intro i j
      rw [restrictTableau_apply]
      change (if (i, j) ∈ skewCells lam₂ mu₂ then T₁ i j + T₂ i j else 0) = T₂ i j
      by_cases h : (i, j) ∈ skewCells lam₂ mu₂
      · rw [ite_eq_left h, T₁.zeros (S.notMem₁ h)]; simp
      · rw [ite_eq_right h, T₂.zeros h]
  right_inv T := by
    apply BoundedSkewSSYT.ext
    intro i j
    change (restrictTableau T S.sub₁ i j) + (restrictTableau T S.sub₂ i j) = T i j
    rw [restrictTableau_apply, restrictTableau_apply]
    by_cases h₁ : (i, j) ∈ skewCells lam₁ mu₁
    · rw [ite_eq_left h₁, ite_eq_right (S.notMem₂ h₁)]; rfl
    · by_cases h₂ : (i, j) ∈ skewCells lam₂ mu₂
      · rw [ite_eq_right h₁, ite_eq_left h₂]; simp
      · have : (i, j) ∉ skewCells lam mu := by
          rw [S.union]
          simp only [Finset.mem_union, not_or]
          exact ⟨h₁, h₂⟩
        rw [ite_eq_right h₁, ite_eq_right h₂, T.zeros this]

variable {R : Type*} [CommSemiring R]

/-- **The tableau sum of a split shape is the product of the tableau sums of its pieces.** -/
theorem skewSchur_mul (x : ℕ → R) :
    skewSchur lam mu b x = skewSchur lam₁ mu₁ b x * skewSchur lam₂ mu₂ b x := by
  unfold skewSchur
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type' (f := fun
    (T₁ : BoundedSkewSSYT lam₁ mu₁ b) (T₂ : BoundedSkewSSYT lam₂ mu₂ b) =>
    (∏ c ∈ skewCells lam₁ mu₁, x (T₁.1 c.1 c.2)) * ∏ c ∈ skewCells lam₂ mu₂, x (T₂.1 c.1 c.2))]
  refine (Fintype.sum_equiv S.tableauEquiv _ _ fun p => ?_).symm
  change _ = ∏ c ∈ skewCells lam mu, x ((S.sumTableau p.1 p.2) c.1 c.2)
  have h := Finset.prod_union
    (f := fun c : ℕ × ℕ => x ((S.sumTableau p.1 p.2).1 c.1 c.2)) S.disjoint
  rw [← S.union] at h
  refine Eq.trans ?_ h.symm
  congr 1
  · refine Finset.prod_congr rfl fun c hc => ?_
    change x (p.1 c.1 c.2) = x (p.1 c.1 c.2 + p.2 c.1 c.2)
    rw [p.2.zeros (S.notMem₂ hc), add_zero]
  · refine Finset.prod_congr rfl fun c hc => ?_
    change x (p.2 c.1 c.2) = x (p.1 c.1 c.2 + p.2 c.1 c.2)
    rw [p.1.zeros (S.notMem₁ hc), zero_add]

end SkewSplit

end Split

/-! ### Skew diagrams in the quadrant are shapes `λ / μ` -/

section Pair

/-- The cell diagram of `λ / μ` is a skew diagram. -/
theorem isSkew_skewDiagram (lam mu : YoungDiagram) : IsSkew (skewDiagram lam mu) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨a, b, rfl⟩ := nat_cell_of_mem_skewDiagram hx
  obtain ⟨c, d, rfl⟩ := nat_cell_of_mem_skewDiagram hy
  simp only [Finset.mem_Icc] at hi hj
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = (i' : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = (j' : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hac : a ≤ c := by simpa using h1
  have hbd : b ≤ d := by simpa using h2
  have hai : a ≤ i' := by exact_mod_cast hi.1
  have hic : i' ≤ c := by exact_mod_cast hi.2
  have hbj : b ≤ j' := by exact_mod_cast hj.1
  have hjd : j' ≤ d := by exact_mod_cast hj.2
  rw [mem_skewDiagram_nat, mem_skewCells] at hx hy ⊢
  exact ⟨lam.up_left_mem hic hjd hy.1, fun h => hx.2 (mu.up_left_mem hai hbj h)⟩

/-- A skew diagram in the quadrant is the cell diagram of a skew shape `λ / μ` of Young
diagrams: `λ` is the set of cells weakly northwest of a cell of the diagram, and `μ` is `λ`
without the diagram. -/
theorem exists_young_pair_of_isSkew {D : Diagram} (hD : IsSkew D)
    (hnn : ∀ x ∈ D, 0 ≤ x.1 ∧ 0 ≤ x.2) :
    ∃ lam mu : YoungDiagram, mu ≤ lam ∧ skewDiagram lam mu = D := by
  classical
  set N : Finset (ℕ × ℕ) := D.image (fun x => (x.1.toNat, x.2.toNat)) with hNdef
  have hN : ∀ a b : ℕ, (a, b) ∈ N ↔ ((a : ℤ), (b : ℤ)) ∈ D := by
    intro a b
    constructor
    · intro h
      obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h
      have h1 := hnn x hx
      have ha : x.1.toNat = a := congrArg Prod.fst hxe
      have hb : x.2.toNat = b := congrArg Prod.snd hxe
      have : x = ((a : ℤ), (b : ℤ)) := by ext <;> simp <;> omega
      rwa [← this]
    · intro h
      exact Finset.mem_image.mpr ⟨_, h, by simp⟩
  have hconv : ∀ p q r : ℕ × ℕ, p ∈ N → q ∈ N → p ≤ r → r ≤ q → r ∈ N := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨i, j⟩ hp hq hpr hrq
    obtain ⟨hai, hbj⟩ := Prod.mk_le_mk.mp hpr
    obtain ⟨hic, hjd⟩ := Prod.mk_le_mk.mp hrq
    rw [hN] at hp hq ⊢
    exact hD.mem hp hq (by exact_mod_cast hai.trans hic) (by exact_mod_cast hbj.trans hjd)
      (by exact_mod_cast hai) (by exact_mod_cast hic) (by exact_mod_cast hbj)
      (by exact_mod_cast hjd)
  set L : Finset (ℕ × ℕ) := N.biUnion (fun p => Finset.Iic p) with hLdef
  have hL : ∀ r, r ∈ L ↔ ∃ p ∈ N, r ≤ p := by
    intro r
    simp only [hLdef, Finset.mem_biUnion, Finset.mem_Iic]
  have hNL : N ⊆ L := fun p hp => (hL p).mpr ⟨p, hp, le_rfl⟩
  let lam : YoungDiagram := ⟨L, fun a b hba ha => by
    rw [Finset.mem_coe, hL] at ha ⊢
    obtain ⟨p, hp, hap⟩ := ha
    exact ⟨p, hp, hba.trans hap⟩⟩
  let mu : YoungDiagram := ⟨L \ N, fun a b hba ha => by
    rw [Finset.mem_coe, Finset.mem_sdiff] at ha ⊢
    obtain ⟨haL, haN⟩ := ha
    obtain ⟨p, hp, hap⟩ := (hL a).mp haL
    refine ⟨(hL b).mpr ⟨p, hp, hba.trans hap⟩, fun hb => haN ?_⟩
    exact hconv b p a hb hp hba hap⟩
  refine ⟨lam, mu, fun x hx => (Finset.mem_sdiff.mp hx).1, ?_⟩
  have hcells : skewCells lam mu = N := by
    ext c
    rw [mem_skewCells]
    change c ∈ L ∧ c ∉ L \ N ↔ c ∈ N
    rw [Finset.mem_sdiff]
    constructor
    · rintro ⟨hc, hc'⟩
      by_contra hcN
      exact hc' ⟨hc, hcN⟩
    · intro hc
      exact ⟨hNL hc, fun h => h.2 hc⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, j, rfl⟩ := nat_cell_of_mem_skewDiagram hx
    rw [mem_skewDiagram_nat, hcells, hN] at hx
    exact hx
  · intro hx
    obtain ⟨a, b⟩ := x
    obtain ⟨hx1, hx2⟩ := hnn _ hx
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, a = (i : ℤ) := ⟨a.toNat, (Int.toNat_of_nonneg hx1).symm⟩
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, b = (j : ℤ) := ⟨b.toNat, (Int.toNat_of_nonneg hx2).symm⟩
    rw [mem_skewDiagram_nat, hcells, hN]
    exact hx

end Pair
/-! ### `s` over a union without adjacent cells -/

section Union

attribute [local instance 10] Classical.propDecidable

theorem DiagReach.mem_of_mem {D : Diagram} {x y : ℤ × ℤ} (hx : x ∈ D) (h : DiagReach D x y) :
    y ∈ D := by
  induction h with
  | refl => exact hx
  | tail _ hab _ => exact hab.2.1

variable {A B : Diagram}

/-- Restrict a reachability path to a larger diagram. -/
theorem DiagReach.mono {D D' : Diagram} (hD : D ⊆ D') {x y : ℤ × ℤ}
    (h : DiagReach D x y) : DiagReach D' x y :=
  Relation.ReflTransGen.mono (fun _ _ hab => ⟨hD hab.1, hD hab.2.1, hab.2.2⟩) x y h

theorem diagReach_union_left (hadj : ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) {x y : ℤ × ℤ}
    (hx : x ∈ A) (h : DiagReach (A ∪ B) x y) : DiagReach A x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hxb hbc ih =>
    have hbA : b ∈ A := DiagReach.mem_of_mem hx ih
    have hcA : c ∈ A := by
      rcases Finset.mem_union.mp hbc.2.1 with h | h
      · exact h
      · exact absurd hbc.2.2 (hadj b hbA c h)
    exact Relation.ReflTransGen.tail ih ⟨hbA, hcA, hbc.2.2⟩

theorem filter_union_left (hadj : ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) {x : ℤ × ℤ} (hx : x ∈ A) :
    (A ∪ B).filter (DiagReach (A ∪ B) x) = A.filter (DiagReach A x) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨-, hr⟩
    have := diagReach_union_left hadj hx hr
    exact ⟨DiagReach.mem_of_mem hx this, this⟩
  · rintro ⟨hy, hr⟩
    exact ⟨Or.inl hy, hr.mono Finset.subset_union_left⟩

/-- The components of a union of two diagrams with no adjacent cells are the components of the
two diagrams. -/
theorem edgeComponents_union (hadj : ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) :
    edgeComponents (A ∪ B) = edgeComponents A ∪ edgeComponents B := by
  have hadj' : ∀ b ∈ B, ∀ a ∈ A, ¬ CellAdj b a := fun b hb a ha h => hadj a ha b hb h.symm'
  ext C
  simp only [Finset.mem_union, mem_edgeComponents]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with hxA | hxB
    · exact Or.inl ⟨x, hxA, filter_union_left hadj hxA⟩
    · refine Or.inr ⟨x, hxB, ?_⟩
      rw [Finset.union_comm]
      exact filter_union_left hadj' hxB
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, (filter_union_left hadj hx).symm⟩
    · refine ⟨x, Or.inr hx, ?_⟩
      rw [Finset.union_comm]
      exact (filter_union_left hadj' hx).symm

/-- Functions multiply over a skew union with no adjacent cells between the pieces. -/
theorem cellSchur_union (ha : IsSkew A) (hb : IsSkew B) (hu : IsSkew (A ∪ B))
    (hdisj : Disjoint A B) (hadj : ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) :
    cellSchur (A ∪ B) hu = cellSchur A ha * cellSchur B hb := by
  let f : Diagram → Lambda := fun C => if hC : C ∈ edgeComponents (A ∪ B)
    then connectedSchur C (isConnectedSkew_component hu hC) else 1
  have he (D : Diagram) (hs : IsSkew D) (hd : edgeComponents D ⊆ edgeComponents (A ∪ B)) :
      cellSchur D hs = ∏ C ∈ edgeComponents D, f C := by
    rw [← Finset.prod_attach]
    unfold cellSchur
    refine Finset.prod_congr rfl fun C _ => ?_
    dsimp only [f]
    rw [dite_eq_left (hd C.2)]
  have heu := edgeComponents_union hadj
  rw [he _ hu (by rfl), he _ ha (by rw [heu]; exact Finset.subset_union_left),
    he _ hb (by rw [heu]; exact Finset.subset_union_right), heu]
  apply Finset.prod_union
  rw [Finset.disjoint_left]
  intro C hCA hCB
  obtain ⟨z, hz⟩ := (isEdgeConnected_component hCA).1
  exact Finset.disjoint_left.mp hdisj (component_subset hCA hz) (component_subset hCB hz)

/-- Reachability from a member cannot leave its component. -/
theorem mem_component_of_reach {D C : Diagram} (hC : C ∈ edgeComponents D) {x y : ℤ × ℤ}
    (hx : x ∈ C) (h : DiagReach D x y) : y ∈ C := by
  rw [component_eq_of_mem hC hx]
  exact Finset.mem_filter.mpr ⟨DiagReach.mem_of_mem (component_subset hC hx) h, h⟩

/-- Removing an entire component preserves skew convexity. -/
theorem isSkew_sdiff_component {D C : Diagram} (hs : IsSkew D) (hC : C ∈ edgeComponents D) :
    IsSkew (D \ C) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨hxD, hxC⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyD, _⟩ := Finset.mem_sdiff.mp hy
  have hz := hs x hxD y hyD h1 h2 i hi j hj
  refine Finset.mem_sdiff.mpr ⟨hz, fun hzC => hxC ?_⟩
  exact mem_component_of_reach hC hzC
    (hs.reach_of_le hxD hz (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1).symm

/-- Cells in one column of a skew diagram are joined in that column. -/
theorem IsSkew.reach_col {D : Diagram} (hs : IsSkew D) {i k j : ℤ}
    (hi : (i, j) ∈ D) (hk : (k, j) ∈ D) : DiagReach D (i, j) (k, j) := by
  rcases le_total i k with h | h
  · exact hs.reach_of_le hi hk h le_rfl
  · exact (hs.reach_of_le hk hi h le_rfl).symm

end Union

end SkewGluing
