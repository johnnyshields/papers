import SkewGluing.DisconnectedSpecialization
import SkewGluing.AlphabetSeparation
import SkewGluing.InteriorProfile

/-!
# Jacobi--Trudi determinants with empty rows

Supports `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `eq:minor-shape`, `eq:corner-factors`, `lem:cofactor`).
Strictly decreasing admissible beta lists describe a skew diagram even when rows are empty.
The tableau specialization and finite-alphabet separation identify its determinant with the
product over its actual connected components. Sorry-free.
-/

namespace SkewGluing

open MvPolynomial

variable {m : ℕ}

/-- Row lengths of a Young diagram presented in beta coordinates. -/
def betaRows (ξ : Fin (m + 1) → ℤ) (i : Fin (m + 1)) : ℕ := (ξ i + i).toNat

theorem betaRows_antitone {ξ : Fin (m + 1) → ℤ} (hξ : StrictAnti ξ) :
    Antitone (betaRows ξ) := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  have := hξ (Fin.castSucc_lt_succ (i := i))
  simp only [betaRows, Fin.val_succ, Fin.val_castSucc]
  omega

/-- The Young diagram associated to a strictly decreasing beta list. -/
def betaYoung (ξ : Fin (m + 1) → ℤ) (hξ : StrictAnti ξ) : YoungDiagram :=
  youngOfRows (betaRows ξ) (betaRows_antitone hξ)

theorem betaYoung_le {ξ ζ : Fin (m + 1) → ℤ} (hξ : StrictAnti ξ) (hζ : StrictAnti ζ)
    (hle : ∀ i, ζ i ≤ ξ i) : betaYoung ζ hζ ≤ betaYoung ξ hξ := by
  intro c hc
  obtain ⟨hi, hj⟩ := (mem_youngOfRows _ _ _).mp hc
  refine (mem_youngOfRows _ _ _).mpr ⟨hi, ?_⟩
  have := hle ⟨c.1, hi⟩
  simp only [betaRows] at hj ⊢
  omega

/-- The beta row intervals, retaining empty rows. -/
def betaCells (ξ ζ : Fin (m + 1) → ℤ) : Diagram :=
  Finset.univ.biUnion fun i : Fin (m + 1) =>
    (Finset.Ico (ζ i + i) (ξ i + i)).image fun j => ((i : ℤ), j)

theorem betaCells_eq_skewDiagram {ξ ζ : Fin (m + 1) → ℤ}
    (hξ : StrictAnti ξ) (hζ : StrictAnti ζ) (hz : ∀ i, 0 ≤ ζ i) :
    betaCells ξ ζ = skewDiagram (betaYoung ξ hξ) (betaYoung ζ hζ) := by
  ext ⟨a, b⟩
  simp only [betaCells, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨i, j, ⟨hl, hh⟩, rfl, rfl⟩
    have hn : 0 ≤ j := by have := hz i; omega
    have he : j = (j.toNat : ℤ) := (Int.toNat_of_nonneg hn).symm
    rw [he, mem_skewDiagram_nat, Shields.mem_skewCells]
    constructor
    · apply (mem_youngOfRows _ _ _).mpr
      refine ⟨i.isLt, ?_⟩
      change j.toNat < (ξ i + (i : ℤ)).toNat
      omega
    · intro hm
      obtain ⟨_, hj⟩ := (mem_youngOfRows _ _ _).mp hm
      change j.toNat < (ζ i + (i : ℤ)).toNat at hj
      omega
  · intro h
    obtain ⟨i, j, he⟩ := nat_cell_of_mem_skewDiagram h
    have ha : a = i := congrArg Prod.fst he
    have hb : b = j := congrArg Prod.snd he
    subst a b
    rw [mem_skewDiagram_nat, Shields.mem_skewCells] at h
    obtain ⟨hi, hj⟩ := (mem_youngOfRows _ _ _).mp h.1
    have hlo : (ζ ⟨i, hi⟩ + i).toNat ≤ j := by
      apply le_of_not_gt
      intro hlt
      exact h.2 ((mem_youngOfRows _ _ _).mpr ⟨hi, hlt⟩)
    refine ⟨⟨i, hi⟩, (j : ℤ), ?_, rfl, rfl⟩
    change ζ ⟨i, hi⟩ + (i : ℤ) ≤ (j : ℤ) ∧
      (j : ℤ) < ξ ⟨i, hi⟩ + (i : ℤ)
    simp only [betaRows] at hj
    have := hz ⟨i, hi⟩
    omega

/-- The two-list determinant specializes to its tableau sum in every finite alphabet. -/
theorem aeval_betaDet_eq_skewSchur {R : Type*} [CommRing R] [Algebra ℚ R]
    {ξ ζ : Fin (m + 1) → ℤ} (hξ : StrictAnti ξ) (hζ : StrictAnti ζ)
    (hz : ∀ i, 0 ≤ ζ i) (hle : ∀ i, ζ i ≤ ξ i) (b : ℕ) (β : ℕ → R) :
    aeval (fun k : ℕ+ => Shields.completeHom b k β) (betaDet ξ ζ) =
      Shields.skewSchur (betaYoung ξ hξ) (betaYoung ζ hζ) b β := by
  rw [← Shields.jacobiTrudiDet_eq_skewSchur (b := b) (m := m + 1) β
    (betaYoung ξ hξ) (betaYoung ζ hζ) (betaYoung_le hξ hζ hle)
    (fun i hi => rowLen_youngOfRows_of_le _ _ hi)]
  rw [betaDet, AlgHom.map_det, Shields.jacobiTrudiDet]
  congr 1
  funext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Profile.aeval_hh,
    Shields.jtCoeff, betaYoung, rowLen_youngOfRows, betaRows]
  have hzi := hz i
  have hzj := hz j
  have hxi : 0 ≤ ξ i := (hz i).trans (hle i)
  split_ifs with ha hb hb
  · omega
  · rfl
  · congr 2
    omega
  · omega

/-- A general admissible beta determinant is the actual component Schur product. -/
theorem betaDet_eq_cellSchur {ξ ζ : Fin (m + 1) → ℤ}
    (hξ : StrictAnti ξ) (hζ : StrictAnti ζ) (hz : ∀ i, 0 ≤ ζ i)
    (hle : ∀ i, ζ i ≤ ξ i) :
    betaDet ξ ζ = cellSchur (betaCells ξ ζ)
      (by rw [betaCells_eq_skewDiagram hξ hζ hz]; exact isSkew_skewDiagram _ _) := by
  apply eq_of_evalComplete_eq
  intro b
  change aeval (fun k : ℕ+ => Shields.completeHom b k (varAlphabet b)) (betaDet ξ ζ) = _
  rw [aeval_betaDet_eq_skewSchur hξ hζ hz hle]
  have he := aeval_cellSchur_skewDiagram_all (betaYoung_le hξ hζ hle) b (varAlphabet b)
  have hs : IsSkew (betaCells ξ ζ) := by
    rw [betaCells_eq_skewDiagram hξ hζ hz]
    exact isSkew_skewDiagram _ _
  rw [cellSchur_congr (betaCells_eq_skewDiagram hξ hζ hz).symm
    (isSkew_skewDiagram _ _) hs] at he
  exact he.symm

end SkewGluing
