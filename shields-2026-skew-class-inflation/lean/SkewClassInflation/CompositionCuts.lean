/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CompositionSuffixes

/-!
# Literal composition cut sets and their product

The cut-word representation of `eq:ribbon-composition` and
`lem:overlap-power-rigidity` in
`shields-2026-skew-class-inflation.tex`.  A composition is represented
by all its proper prefix cuts.  Product cuts at nonmultiples of the
inner size are the repeated internal cut word; multiples retain the
outer boundaries.  Sorry-free.
-/

namespace SkewClassInflation

/-- Proper prefix cuts in the top-to-bottom composition convention. -/
def properCuts {n : ℕ} (α : Composition n) : Finset ℕ :=
  ((α.boundaries.erase 0).erase (Fin.last n)).image Fin.val

/-- Prefix cuts are exactly suffix cuts of the reversed composition. -/
theorem properCuts_eq_suffixSet {n : ℕ} (α : Composition n) :
    properCuts α = suffixSet α.reverse := by
  simp only [properCuts, suffixSet, Composition.reverse_reverse]

/-- Every proper cut is a genuinely positive, nonterminal position. -/
theorem properCuts_bounds {n : ℕ} (α : Composition n) :
    ∀ x ∈ properCuts α, 0 < x ∧ x < n := by
  rw [properCuts_eq_suffixSet]
  intro x hx
  exact Finset.mem_Ioo.mp (suffixSet_subset α.reverse hx)

/-- At an internal position, proper-cut membership is literal boundary membership. -/
theorem mem_properCuts_iff {n : ℕ} (α : Composition n) (x : ℕ)
    (hx : 0 < x) (hxn : x < n) :
    x ∈ properCuts α ↔ (⟨x, by omega⟩ : Fin (n + 1)) ∈ α.boundaries := by
  constructor
  · intro he
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp he
    have hm := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2
    have hh : i = (⟨x, by omega⟩ : Fin (n + 1)) := Fin.ext he
    simpa only [hh] using hm
  · intro he
    refine Finset.mem_image.mpr ⟨⟨x, by omega⟩, ?_, rfl⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨?_, he⟩⟩
    · intro hh
      have hv := congrArg Fin.val hh
      change x = n at hv
      omega
    · intro hh
      have hv := congrArg Fin.val hh
      change x = 0 at hv
      omega

/-- A multipart positive composition has at least one actual proper cut. -/
theorem properCuts_nonempty {n : ℕ} (α : Composition n) (hn : 0 < n)
    (hα : 2 ≤ α.length) : (properCuts α).Nonempty := by
  rw [properCuts_eq_suffixSet]
  have hc := suffixSet_card α.reverse hn
  have hlen : α.reverse.length = α.length := by simp [Composition.length]
  rw [hlen] at hc
  exact Finset.card_pos.mp (by omega)

/-- Proper cut equality recovers the complete composition at its fixed weight. -/
theorem properCuts_injective {N : ℕ} : Function.Injective (@properCuts N) := by
  intro α β he
  rw [properCuts_eq_suffixSet, properCuts_eq_suffixSet] at he
  exact Composition.reverse_injective (suffixSet_injective he)

/-- Transporting the total weight changes no actual natural proper cut position. -/
theorem properCuts_cast {m n : ℕ} (α : Composition m) (h : m = n) :
    properCuts (α.cast h) = properCuts α := by
  subst n
  rfl

/-- Equal literal words identify the natural cut sets even across indexed total weights. -/
theorem properCuts_eq_of_blocks_eq {m n : ℕ} (α : Composition m) (β : Composition n)
    (he : α.blocks = β.blocks) : properCuts α = properCuts β := by
  have hh : (⟨m, α⟩ : (N : ℕ) × Composition N) = ⟨n, β⟩ :=
    Composition.sigma_eq_iff_blocks_eq.mpr he
  exact congrArg (fun D : (N : ℕ) × Composition N => properCuts D.2) hh

/-- Cut-based composition product, retaining both full-word endpoints. -/
noncomputable def compositionProduct {m n : ℕ} (γ : Composition m) (β : Composition n) :
    Composition (m * n) :=
  (compositionEquiv (m * n)).symm
    { boundaries := Finset.univ.filter (fun i : Fin (m * n + 1) =>
        i = 0 ∨ i = Fin.last (m * n) ∨
          (if i.val % n = 0 then i.val / n ∈ properCuts γ else i.val % n ∈ properCuts β))
      zero_mem := by simp
      getLast_mem := by simp }

/-- At every proper position, the product keeps outer multiples and repeats inner cuts. -/
theorem compositionProduct_cuts {m n : ℕ} (γ : Composition m) (β : Composition n)
    (x : ℕ) (hx : 0 < x) (hxm : x < m * n) :
    x ∈ properCuts (compositionProduct γ β) ↔
      if x % n = 0 then x / n ∈ properCuts γ else x % n ∈ properCuts β := by
  classical
  rw [mem_properCuts_iff _ x hx hxm]
  let S : CompositionAsSet (m * n) :=
    { boundaries := Finset.univ.filter (fun i : Fin (m * n + 1) =>
        i = 0 ∨ i = Fin.last (m * n) ∨
          (if i.val % n = 0 then i.val / n ∈ properCuts γ else i.val % n ∈ properCuts β))
      zero_mem := by simp
      getLast_mem := by simp }
  have hb := congrArg CompositionAsSet.boundaries ((compositionEquiv (m * n)).apply_symm_apply S)
  change (compositionProduct γ β).boundaries = S.boundaries at hb
  rw [hb]
  have hz : (⟨x, by omega⟩ : Fin (m * n + 1)) ≠ 0 := by
    intro he
    have hh := congrArg Fin.val he
    change x = 0 at hh
    omega
  have hl : (⟨x, by omega⟩ : Fin (m * n + 1)) ≠ Fin.last (m * n) := by
    intro he
    have hh := congrArg Fin.val he
    change x = m * n at hh
    omega
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hz, hl, false_or]

/-- Away from whole-inner boundaries, the product repeats exactly the inner proper-cut word. -/
theorem compositionProduct_internal {m n : ℕ} (γ : Composition m) (β : Composition n)
    (x : ℕ) (hx : 0 < x) (hxm : x < m * n) (hmod : x % n ≠ 0) :
    x ∈ properCuts (compositionProduct γ β) ↔ x % n ∈ properCuts β := by
  rw [compositionProduct_cuts γ β x hx hxm, ite_eq_right hmod]

end SkewClassInflation
