/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.PartsAndCuts

/-!
# The composition product and its cut set

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:algebra`
(`eq:composition-cuts` and the consequences listed after it).

The cut set of `α ∘ ε` is `compCuts` (`composition_cuts`); the product is associative
(`compose_assoc`), compatible with reversal (`compose_reverse`), satisfies
`(α ∘ ε)^{⊙ j} = α^{⊙ j} ∘ ε` (`nearPow_compose`), and a near-power has no cut at an internal
seam (`nearPow_no_seam`).  Each list statement rests on a cut-set identity proved without
reference to lists (`compCuts_assoc`, `revCuts_compCuts`, `nearPowerCuts_compCuts`).  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

lemma mem_nearPowerCuts {n : ℕ} {S : Finset ℕ} {m x : ℕ} :
    x ∈ nearPowerCuts n S m ↔ ∃ j < m, ∃ e ∈ S, j * n + e = x := by
  simp [nearPowerCuts]

/-- Associativity of `compCuts` (no hypotheses needed). -/
theorem compCuts_assoc (m : ℕ) (A : Finset ℕ) (p : ℕ) (E : Finset ℕ) (q : ℕ) (F : Finset ℕ) :
    compCuts (m * p) (compCuts m A p E) q F = compCuts m A (p * q) (compCuts p E q F) := by
  ext x
  simp only [mem_compCuts]
  constructor
  · rintro (⟨y, (⟨a, ha, rfl⟩ | ⟨j, hj, e, he, rfl⟩), rfl⟩ | ⟨l, hl, f, hf, rfl⟩)
    · exact Or.inl ⟨a, ha, by ring⟩
    · exact Or.inr ⟨j, hj, q * e, Or.inl ⟨e, he, rfl⟩, by ring⟩
    · have hp : 0 < p := by
        rcases Nat.eq_zero_or_pos p with rfl | hp
        · simp at hl
        · exact hp
      refine Or.inr ⟨l / p, ?_, (l % p) * q + f, Or.inr ⟨l % p, Nat.mod_lt _ hp, f, hf, rfl⟩, ?_⟩
      · exact (Nat.div_lt_iff_lt_mul hp).mpr hl
      · have := Nat.div_add_mod l p
        calc l / p * (p * q) + (l % p * q + f) = (p * (l / p) + l % p) * q + f := by ring
          _ = l * q + f := by rw [this]
  · rintro (⟨a, ha, rfl⟩ | ⟨j, hj, z, (⟨e, he, rfl⟩ | ⟨i, hi, f, hf, rfl⟩), rfl⟩)
    · exact Or.inl ⟨p * a, Or.inl ⟨a, ha, rfl⟩, by ring⟩
    · exact Or.inl ⟨j * p + e, Or.inr ⟨j, hj, e, he, rfl⟩, by ring⟩
    · refine Or.inr ⟨j * p + i, ?_, f, hf, by ring⟩
      calc j * p + i < j * p + p := by omega
        _ = (j + 1) * p := by ring
        _ ≤ m * p := Nat.mul_le_mul_right _ hj

/-- Reversal of `compCuts`: `(α ∘ ε)* = α* ∘ ε*` at the level of cut sets. -/
theorem revCuts_compCuts (m : ℕ) (A : Finset ℕ) (p : ℕ) (E : Finset ℕ)
    (hA : IsCutSet m A) (hE : IsCutSet p E) :
    revCuts (m * p) (compCuts m A p E) = compCuts m (revCuts m A) p (revCuts p E) := by
  ext x
  rw [revCuts_mem, mem_compCuts]
  simp only [revCuts_mem, mem_compCuts]
  constructor
  · rintro ⟨y, (⟨a, ha, rfl⟩ | ⟨j, hj, e, he, rfl⟩), rfl⟩
    · have := (Finset.mem_Ioo.mp (hA ha)).2
      exact Or.inl ⟨m - a, ⟨a, ha, rfl⟩, by rw [Nat.mul_sub, mul_comm]⟩
    · have hep := (Finset.mem_Ioo.mp (hE he)).2
      obtain ⟨t, rfl⟩ : ∃ t, m = j + 1 + t := ⟨m - (j + 1), by omega⟩
      obtain ⟨s, rfl⟩ : ∃ s, p = e + 1 + s := ⟨p - (e + 1), by omega⟩
      refine Or.inr ⟨t, by omega, e + 1 + s - e, ⟨e, he, rfl⟩, ?_⟩
      have : (j + 1 + t) * (e + 1 + s) =
          (j * (e + 1 + s) + e) + (t * (e + 1 + s) + (e + 1 + s - e)) := by
        have : e + 1 + s - e = 1 + s := by omega
        rw [this]; ring
      omega
  · rintro (⟨z, ⟨a, ha, rfl⟩, rfl⟩ | ⟨j, hj, z, ⟨e, he, rfl⟩, rfl⟩)
    · have := (Finset.mem_Ioo.mp (hA ha)).2
      exact ⟨p * a, Or.inl ⟨a, ha, rfl⟩, by rw [Nat.mul_sub, mul_comm p m]⟩
    · have hep := (Finset.mem_Ioo.mp (hE he)).2
      obtain ⟨t, rfl⟩ : ∃ t, m = j + 1 + t := ⟨m - (j + 1), by omega⟩
      obtain ⟨s, rfl⟩ : ∃ s, p = e + 1 + s := ⟨p - (e + 1), by omega⟩
      refine ⟨t * (e + 1 + s) + e, Or.inr ⟨t, by omega, e, he, rfl⟩, ?_⟩
      have : (j + 1 + t) * (e + 1 + s) =
          (j * (e + 1 + s) + (e + 1 + s - e)) + (t * (e + 1 + s) + e) := by
        have : e + 1 + s - e = 1 + s := by omega
        rw [this]; ring
      omega

/-- `nearPowerCuts` of `compCuts`: `(α ∘ ε)^{⊙ j} = α^{⊙ j} ∘ ε` at the level of cut sets. -/
theorem nearPowerCuts_compCuts (m : ℕ) (A : Finset ℕ) (p : ℕ) (E : Finset ℕ) (j : ℕ) :
    nearPowerCuts (m * p) (compCuts m A p E) j
      = compCuts (j * m) (nearPowerCuts m A j) p E := by
  ext x
  simp only [mem_nearPowerCuts, mem_compCuts]
  constructor
  · rintro ⟨i, hi, y, (⟨a, ha, rfl⟩ | ⟨k, hk, e, he, rfl⟩), rfl⟩
    · exact Or.inl ⟨i * m + a, ⟨i, hi, a, ha, rfl⟩, by ring⟩
    · refine Or.inr ⟨i * m + k, ?_, e, he, by ring⟩
      calc i * m + k < i * m + m := by omega
        _ = (i + 1) * m := by ring
        _ ≤ j * m := Nat.mul_le_mul_right _ hi
  · rintro (⟨z, ⟨i, hi, a, ha, rfl⟩, rfl⟩ | ⟨l, hl, e, he, rfl⟩)
    · exact ⟨i, hi, p * a, Or.inl ⟨a, ha, rfl⟩, by ring⟩
    · have hm : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp at hl
        · exact hm
      refine ⟨l / m, (Nat.div_lt_iff_lt_mul hm).mpr hl, (l % m) * p + e,
        Or.inr ⟨l % m, Nat.mod_lt _ hm, e, he, rfl⟩, ?_⟩
      have := Nat.div_add_mod l m
      calc l / m * (m * p) + (l % m * p + e) = (m * (l / m) + l % m) * p + e := by ring
        _ = l * p + e := by rw [this]

/-- No cut of a near-power `ε^{⊙ m}` of a composition of weight `n` is a multiple `j n` of `n`; in
particular there is no cut at an internal seam. -/
theorem nearPowerCuts_no_seam {n : ℕ} {S : Finset ℕ} (hS : IsCutSet n S) {m : ℕ} (j : ℕ) :
    j * n ∉ nearPowerCuts n S m := by
  intro h
  obtain ⟨i, _, e, he, hx⟩ := mem_nearPowerCuts.mp h
  have he' := Finset.mem_Ioo.mp (hS he)
  rcases lt_or_ge i j with hij | hij
  · have : (i + 1) * n ≤ j * n := Nat.mul_le_mul_right _ hij
    nlinarith
  · have : j * n ≤ i * n := Nat.mul_le_mul_right _ hij
    omega

/-! ### Statements for lists of parts -/

@[simp] lemma nearPow_nil (j : ℕ) : nearPow [] j = [] := by
  induction j with
  | zero => rfl
  | succ j ih => rw [nearPow_succ, ih]; rfl

@[simp] lemma compose_nil_right (α : List ℕ) : compose α [] = [] := by
  simp [compose]

/-- `eq:composition-cuts`: `S(α ∘ ε) = p S(α) ∪ ⋃_{j < |α|} (j p + S(ε))` with `p = |ε|`. -/
theorem composition_cuts {α ε : List ℕ} (hα : IsParts α) (hε : ε ≠ []) :
    partsCuts (compose α ε)
      = (partsCuts α).image (ε.sum * ·) ∪
        (Finset.range α.sum).biUnion fun j => (partsCuts ε).image (j * ε.sum + ·) := by
  rw [partsCuts_compose hα hε]
  rfl

/-- `eq:composition-cuts` in terms of `compCuts`. -/
theorem partsCuts_compose_eq {α ε : List ℕ} (hα : IsParts α) (hε : ε ≠ []) :
    partsCuts (compose α ε) = compCuts α.sum (partsCuts α) ε.sum (partsCuts ε) :=
  partsCuts_compose hα hε

/-- Associativity of the composition product. -/
theorem compose_assoc {α β γ : List ℕ} (hα : IsParts α) (hβ : IsParts β) (hγ : IsParts γ) :
    compose (compose α β) γ = compose α (compose β γ) := by
  by_cases hβ0 : β = []
  · subst hβ0; simp
  by_cases hγ0 : γ = []
  · subst hγ0; simp
  have hβγ : compose β γ ≠ [] := compose_ne_nil hβ0 hγ0 hβ
  apply partsCuts_injective (isParts_compose hγ) (isParts_compose (isParts_compose hγ))
  · simp only [sum_compose]; ring
  · rw [partsCuts_compose (isParts_compose hβ) hγ0, partsCuts_compose hα hβ0,
      partsCuts_compose hα hβγ, partsCuts_compose hβ hγ0, sum_compose, sum_compose]
    exact compCuts_assoc _ _ _ _ _ _

/-- `(α ∘ ε)* = α* ∘ ε*` (consequence of `eq:composition-cuts`). -/
theorem compose_reverse {α ε : List ℕ} (hα : IsParts α) (hε : IsParts ε) :
    (compose α ε).reverse = compose α.reverse ε.reverse := by
  by_cases hε0 : ε = []
  · subst hε0; simp
  have hε0' : ε.reverse ≠ [] := by simpa using hε0
  have hαr : IsParts α.reverse := fun x hx => hα x (List.mem_reverse.mp hx)
  have hεr : IsParts ε.reverse := fun x hx => hε x (List.mem_reverse.mp hx)
  apply partsCuts_injective (fun x hx => isParts_compose hε x (List.mem_reverse.mp hx))
    (isParts_compose hεr)
  · simp [sum_compose]
  · rw [partsCuts_reverse (isParts_compose hε), partsCuts_compose hα hε0,
      partsCuts_compose hαr hε0', sum_compose, List.sum_reverse, List.sum_reverse,
      partsCuts_reverse hα, partsCuts_reverse hε]
    exact revCuts_compCuts _ _ _ _ (partsCuts_isCutSet hα) (partsCuts_isCutSet hε)

/-- `(α ∘ ε)^{⊙ j} = α^{⊙ j} ∘ ε`. -/
theorem nearPow_compose {α ε : List ℕ} (hα : IsParts α) (hε : IsParts ε) (j : ℕ) :
    nearPow (compose α ε) j = compose (nearPow α j) ε := by
  by_cases hε0 : ε = []
  · subst hε0; simp
  apply partsCuts_injective (isParts_nearPow (isParts_compose hε) j)
    (isParts_compose hε)
  · simp only [sum_nearPow, sum_compose]; ring
  · rw [partsCuts_nearPow, partsCuts_compose hα hε0,
      partsCuts_compose (isParts_nearPow hα j) hε0, partsCuts_nearPow, sum_compose,
      sum_nearPow]
    exact nearPowerCuts_compCuts _ _ _ _ _

/-- The cut set of a near-power `S(β^{⊙ m}) = ⋃_{j<m} (j n + S(β))`, with no cut at an internal
seam `j n`. -/
theorem nearPow_cuts {β : List ℕ} (m : ℕ) :
    partsCuts (nearPow β m)
      = (Finset.range m).biUnion fun j => (partsCuts β).image (j * β.sum + ·) :=
  partsCuts_nearPow β m

/-- A near-power of a composition has no cut at an internal seam `j n`. -/
theorem nearPow_no_seam {β : List ℕ} (hβ : IsParts β) (m j : ℕ) :
    j * β.sum ∉ partsCuts (nearPow β m) := by
  rw [partsCuts_nearPow]
  exact nearPowerCuts_no_seam (partsCuts_isCutSet hβ) j

end SkewRibbonCoarsenings
