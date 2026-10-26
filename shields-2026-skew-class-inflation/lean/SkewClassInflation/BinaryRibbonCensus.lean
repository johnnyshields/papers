/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BinaryRibbonFamilies
import SkewClassInflation.FactorInnerInventory
import SkewClassInflation.SmallRibbonReconstruction

/-!
# The exact census of the iterated weight-three ribbon family

Formalizes the exact count in the proof of `cor:unbounded-class-splitting` of
`shields-2026-skew-class-inflation.tex`.  Every composition with the ribbon function of the
reference word `binaryRibbon e (fun _ => false)` is one of the \(2^e\) binary choices.  Each
level applies the unconditional factor transport of an ordinary product and the reconstruction
of weight-three sources, so no factor-reversal classification is used.  Sorry-free.
-/

namespace SkewClassInflation

/-- Equality of canonical compositions of one weight is equality of their words. -/
theorem composition_ext_of_blocks {N : ℕ} (α β : Composition N) (h : α.blocks = β.blocks) :
    α = β := by
  cases α
  cases β
  cases h
  rfl

/-- The only positive composition of weight one is the single part one. -/
theorem composition_one_blocks (θ : Composition 1) : θ.blocks = [1] := by
  have hs := θ.blocks_sum
  rcases hb : θ.blocks with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rw [hb] at hs
    simp at hs
  · rw [hb] at hs
    simp at hs
    simp [hs]
  · rw [hb] at hs
    have ha : 0 < a := θ.blocks_pos (by rw [hb]; simp)
    have hb' : 0 < b := θ.blocks_pos (by rw [hb]; simp)
    simp at hs
    omega

/-- The weight-three composition `(1, 2)`, the seed of each level of the family. -/
def binaryRibbonSeed : Composition 3 := ⟨[1, 2], by simp, rfl⟩

/-- Every composition with the ribbon function of the reference word is a binary choice. -/
theorem binaryRibbon_census : ∀ (e : ℕ) (θ : Composition (3 ^ e)),
    ribbonWord θ.blocks = ribbonWord (binaryRibbonWord e (fun _ => false)) →
      ∃ b : Fin e → Bool, θ = binaryRibbon e b := by
  intro e
  induction e with
  | zero =>
    intro θ _
    refine ⟨fun i => i.elim0, composition_ext_of_blocks _ _ ?_⟩
    rw [composition_one_blocks θ]
    rfl
  | succ e ih =>
    intro θ he
    have hpos : 0 < 3 ^ e := pow_pos (by decide) e
    have hpos' : 0 < 3 * 3 ^ e := Nat.mul_pos (by decide) hpos
    let θ' : Composition (3 * 3 ^ e) :=
      ⟨θ.blocks, fun h => θ.blocks_pos h, by rw [θ.blocks_sum]; ring⟩
    have hprod : (compositionProduct binaryRibbonSeed (binaryRibbon e (fun _ => false))).blocks =
        binaryRibbonWord (e + 1) (fun _ => false) := by
      rw [compositionProduct_blocks _ _ hpos, ← wordCompose_eq_flatten]
      rfl
    have hInv : coarseningInventory θ' = coarseningInventory
        (compositionProduct binaryRibbonSeed (binaryRibbon e (fun _ => false))) := by
      apply (ribbon_eq_iff_coarseningInventory _ _ hpos' hpos').mp
      change ribbonWord θ.blocks = ribbonWord
        (compositionProduct binaryRibbonSeed (binaryRibbon e (fun _ => false))).blocks
      rw [hprod]
      exact he
    obtain ⟨hfac, hout, hinn⟩ := inventory_mate_factor_transport binaryRibbonSeed
      (binaryRibbon e (fun _ => false)) (by decide) hpos θ' hInv
    have hrec := ribbonReconstructible_of_small_weight binaryRibbonSeed (by decide)
      (periodicOuter θ') hout
    obtain ⟨b0, hb0⟩ : ∃ b0 : Bool, (periodicOuter θ').blocks = binaryRibbonFactor b0 := by
      rcases hrec with h | h
      · exact ⟨false, by rw [h]; rfl⟩
      · exact ⟨true, by rw [h, Composition.reverse_blocks]; rfl⟩
    obtain ⟨b', hb'⟩ := ih (periodicInner θ')
      ((ribbon_eq_iff_coarseningInventory _ _ hpos hpos).mpr hinn)
    refine ⟨Fin.cons b0 b', composition_ext_of_blocks _ _ ?_⟩
    have hblocks : θ.blocks = (compositionProduct (periodicOuter θ') (periodicInner θ')).blocks :=
      (congrArg Composition.blocks hfac).symm
    rw [hblocks, compositionProduct_blocks _ _ hpos, ← wordCompose_eq_flatten, hb0, hb']
    simp [binaryRibbon, binaryRibbonWord]

/-- The reference word's full ribbon class is exactly the range of the binary family. -/
theorem binaryRibbon_class_eq (e : ℕ) :
    ribbonClass (binaryRibbon e (fun _ => false)) = Set.range (binaryRibbon e) := by
  ext θ
  constructor
  · intro h
    obtain ⟨b, hb⟩ := binaryRibbon_census e θ h
    exact ⟨b, hb.symm⟩
  · rintro ⟨b, rfl⟩
    exact binaryRibbon_mem_class e b

/-- The ribbon class of the reference word has exactly \(2^e\) members. -/
theorem binaryRibbon_class_card (e : ℕ) :
    (ribbonClass (binaryRibbon e (fun _ => false))).ncard = 2 ^ e := by
  rw [binaryRibbon_class_eq, Set.ncard_range_of_injective (binaryRibbon_injective e)]
  simp [Nat.card_eq_fintype_card]

end SkewClassInflation
