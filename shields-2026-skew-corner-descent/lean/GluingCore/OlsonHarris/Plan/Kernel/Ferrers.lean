-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/Kernel/Ferrers.lean
import GluingCore.OlsonHarris.Plan.Defs
import GluingCore.CellSchurTableau

/-!
# Ferrers diagrams as cell diagrams

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the cell-diagram vocabulary used in the proof of the kernel of
`schur` (thesis Thm. 5.2.2, `OlsonHarris2024HopfApplications`).

The cell diagram `skewDiagram λ ⊥` of a Young diagram `λ` and the skew diagram `skewDiagram λ μ`
for `μ ≤ λ` are compared as finite sets of cells of `ℤ × ℤ`: membership, differences, cardinality,
and the construction of a Young diagram from a lower set of cells.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace KernelAux

open Shields

theorem mem_skewDiagram_iff {lam mu : YoungDiagram} {x : ℤ × ℤ} :
    x ∈ skewDiagram lam mu ↔ ∃ i j : ℕ, x = ((i : ℤ), (j : ℤ)) ∧ (i, j) ∈ lam ∧ (i, j) ∉ mu := by
  constructor
  · intro h
    obtain ⟨i, j, rfl⟩ := nat_cell_of_mem_skewDiagram h
    rw [mem_skewDiagram_nat, mem_skewCells] at h
    exact ⟨i, j, rfl, h⟩
  · rintro ⟨i, j, rfl, h1, h2⟩
    rw [mem_skewDiagram_nat, mem_skewCells]
    exact ⟨h1, h2⟩

theorem mem_skewDiagram_bot {lam : YoungDiagram} {i j : ℕ} :
    ((i : ℤ), (j : ℤ)) ∈ skewDiagram lam ⊥ ↔ (i, j) ∈ lam := by
  rw [mem_skewDiagram_nat, mem_skewCells]
  simp

theorem nonneg_of_mem_skewDiagram {lam mu : YoungDiagram} {x : ℤ × ℤ}
    (h : x ∈ skewDiagram lam mu) : 0 ≤ x.1 ∧ 0 ≤ x.2 := by
  obtain ⟨i, j, rfl⟩ := nat_cell_of_mem_skewDiagram h
  exact ⟨Int.natCast_nonneg i, Int.natCast_nonneg j⟩

theorem skewDiagram_bot_subset_iff {rho sigma : YoungDiagram} :
    skewDiagram rho ⊥ ⊆ skewDiagram sigma ⊥ ↔ rho ≤ sigma := by
  constructor
  · intro h c hc
    have := h ((mem_skewDiagram_bot (lam := rho)).mpr hc)
    exact mem_skewDiagram_bot.mp (by simpa using this)
  · intro h x hx
    obtain ⟨i, j, rfl⟩ := nat_cell_of_mem_skewDiagram hx
    exact mem_skewDiagram_bot.mpr (h (mem_skewDiagram_bot.mp hx))

theorem skewDiagram_bot_injective :
    Function.Injective fun rho : YoungDiagram => skewDiagram rho ⊥ := fun _ _ h =>
  le_antisymm (skewDiagram_bot_subset_iff.mp h.subset) (skewDiagram_bot_subset_iff.mp h.superset)

theorem skewDiagram_eq_sdiff {lam mu : YoungDiagram} (_ : mu ≤ lam) :
    skewDiagram lam mu = skewDiagram lam ⊥ \ skewDiagram mu ⊥ := by
  ext x
  rw [Finset.mem_sdiff, mem_skewDiagram_iff]
  constructor
  · rintro ⟨i, j, rfl, h1, h2⟩
    exact ⟨mem_skewDiagram_bot.mpr h1, fun h => h2 (mem_skewDiagram_bot.mp h)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨i, j, rfl⟩ := nat_cell_of_mem_skewDiagram h1
    exact ⟨i, j, rfl, mem_skewDiagram_bot.mp h1, fun h => h2 (mem_skewDiagram_bot.mpr h)⟩

theorem card_skewDiagram {lam mu : YoungDiagram} (h : mu ≤ lam) :
    (skewDiagram lam mu).card + mu.card = lam.card := by
  have h1 : (skewDiagram lam mu).card = (skewCells lam mu).card := by
    unfold skewDiagram
    exact Finset.card_image_of_injective _ (fun a b hab => by
      simp only [Prod.mk.injEq, Nat.cast_inj] at hab
      exact Prod.ext hab.1 hab.2)
  rw [h1]
  unfold skewCells
  rw [Finset.card_sdiff_of_subset (YoungDiagram.cells_subset_iff.mpr h)]
  have : mu.cells.card ≤ lam.cells.card := Finset.card_le_card (YoungDiagram.cells_subset_iff.mpr h)
  have h2 : mu.card = mu.cells.card := rfl
  have h3 : lam.card = lam.cells.card := rfl
  omega

theorem skewDiagram_sdiff {rho sigma lam : YoungDiagram} (h1 : rho ≤ sigma) :
    skewDiagram lam rho \ skewDiagram sigma rho = skewDiagram lam sigma := by
  ext x
  rw [Finset.mem_sdiff, mem_skewDiagram_iff, mem_skewDiagram_iff, mem_skewDiagram_iff]
  constructor
  · rintro ⟨⟨i, j, rfl, a, b⟩, hn⟩
    refine ⟨i, j, rfl, a, fun hs => hn ⟨i, j, rfl, hs, b⟩⟩
  · rintro ⟨i, j, rfl, a, b⟩
    refine ⟨⟨i, j, rfl, a, fun hr => b (h1 hr)⟩, ?_⟩
    rintro ⟨i', j', he, c, d⟩
    simp only [Prod.mk.injEq, Nat.cast_inj] at he
    obtain ⟨rfl, rfl⟩ := he
    exact b c

theorem isSkew_skewDiagram_bot (lam : YoungDiagram) : IsSkew (skewDiagram lam ⊥) := by
  intro x hx y hy h1 h2 i hi j hj
  obtain ⟨a, b, rfl⟩ := nat_cell_of_mem_skewDiagram hx
  obtain ⟨c, d, rfl⟩ := nat_cell_of_mem_skewDiagram hy
  rw [Finset.mem_Icc] at hi hj
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = (i' : ℤ) :=
    ⟨i.toNat, (Int.toNat_of_nonneg (by simp at hi; omega)).symm⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = (j' : ℤ) :=
    ⟨j.toNat, (Int.toNat_of_nonneg (by simp at hj; omega)).symm⟩
  rw [mem_skewDiagram_bot] at hy ⊢
  exact lam.up_left_mem (by simp at hi; omega) (by simp at hj; omega) hy

/-- A set of cells in the quadrant that is closed under moving northwest is the cell diagram of a
Young diagram. -/
theorem exists_young_of_lowerSet {P : Diagram} (hnn : ∀ x ∈ P, 0 ≤ x.1 ∧ 0 ≤ x.2)
    (hlow : ∀ x ∈ P, ∀ i j : ℕ, (i : ℤ) ≤ x.1 → (j : ℤ) ≤ x.2 → ((i : ℤ), (j : ℤ)) ∈ P) :
    ∃ sigma : YoungDiagram, skewDiagram sigma ⊥ = P := by
  classical
  let N : Finset (ℕ × ℕ) := P.image (fun x => (x.1.toNat, x.2.toNat))
  have hN : ∀ a b : ℕ, (a, b) ∈ N ↔ ((a : ℤ), (b : ℤ)) ∈ P := by
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
  let sigma : YoungDiagram := ⟨N, fun a b hba ha => by
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    obtain ⟨h1, h2⟩ := Prod.mk_le_mk.mp hba
    rw [Finset.mem_coe, hN] at ha ⊢
    exact hlow _ ha b1 b2 (by simpa using h1) (by simpa using h2)⟩
  refine ⟨sigma, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, j, rfl⟩ := nat_cell_of_mem_skewDiagram hx
    exact (hN i j).mp (mem_skewDiagram_bot.mp hx)
  · intro hx
    obtain ⟨a, b⟩ := x
    obtain ⟨hx1, hx2⟩ := hnn _ hx
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, a = (i : ℤ) := ⟨a.toNat, (Int.toNat_of_nonneg hx1).symm⟩
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, b = (j : ℤ) := ⟨b.toNat, (Int.toNat_of_nonneg hx2).symm⟩
    exact mem_skewDiagram_bot.mpr ((hN i j).mpr hx)

end KernelAux

end Plan

end GluingCore
