/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonProductAlgebra
import Mathlib.Data.Set.Card

/-!
# Binary choices of ordinary ribbon factors

The constructive outer family for `cor:unbounded-class-splitting`
of `shields-2026-skew-class-inflation.tex`.  Each factor is the literal
word `(1,2)` or `(2,1)` and every choice produces an actual positive
composition.  Near-power equivalence is produced algebraically, not
assumed from ribbon classification.  Sorry-free.
-/

namespace SkewClassInflation

/-- The two orientations of the positive factor of weight three. -/
def binaryRibbonFactor (b : Bool) : List ℕ := if b then [2, 1] else [1, 2]

/-- Both actual factor words have the same exact weight. -/
theorem binaryRibbonFactor_sum (b : Bool) : (binaryRibbonFactor b).sum = 3 := by
  cases b <;> rfl

/-- Every part of either factor orientation is positive. -/
theorem binaryRibbonFactor_pos (b : Bool) : ∀ a ∈ binaryRibbonFactor b, 0 < a := by
  cases b <;> intro a ha <;>
    simp only [binaryRibbonFactor, Bool.false_eq_true, ite_false, ite_true,
      List.mem_cons, List.not_mem_nil, or_false] at ha <;>
    rcases ha with rfl | rfl <;> decide

/-- The two factor orientations have equal ribbon functions at every ordinary near power. -/
theorem binaryRibbonFactor_powerEquiv (b : Bool) :
    ribbonPowerEquiv (binaryRibbonFactor b) (binaryRibbonFactor false) := by
  cases b with
  | false => exact ribbonPowerEquiv_refl _
  | true => exact ribbonPowerEquiv_reverse [1, 2] (binaryRibbonFactor_pos false)

/-- Iterated ordinary composition with an independent literal orientation at each level. -/
def binaryRibbonWord : (e : ℕ) → (Fin e → Bool) → List ℕ
  | 0, _ => [1]
  | e + 1, b => wordCompose (binaryRibbonWord e (fun i => b i.succ))
      (binaryRibbonFactor (b 0))

/-- Every orientation choice gives the same exact total size. -/
theorem binaryRibbonWord_sum (e : ℕ) (b : Fin e → Bool) :
    (binaryRibbonWord e b).sum = 3 ^ e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [binaryRibbonWord, wordCompose_sum, binaryRibbonFactor_sum, ih, pow_succ]
    omega

/-- The family supplies all positive parts required by the ribbon and composition APIs. -/
theorem binaryRibbonWord_pos (e : ℕ) (b : Fin e → Bool) :
    ∀ a ∈ binaryRibbonWord e b, 0 < a := by
  induction e with
  | zero => intro a ha; rcases List.mem_singleton.mp ha with rfl; decide
  | succ e ih =>
    exact wordCompose_pos _ _ (ih _) (binaryRibbonFactor_pos _)

/-- All binary choices supply genuine near-power equivalence with the reference word. -/
theorem binaryRibbonWord_powerEquiv (e : ℕ) (b : Fin e → Bool) :
    ribbonPowerEquiv (binaryRibbonWord e b) (binaryRibbonWord e (fun _ => false)) := by
  induction e with
  | zero => exact ribbonPowerEquiv_refl _
  | succ e ih =>
    apply ribbonPowerEquiv_compose
    · rw [binaryRibbonWord_sum]; exact pow_pos (by decide) _
    · rw [binaryRibbonWord_sum]; exact pow_pos (by decide) _
    · exact binaryRibbonFactor_pos _
    · exact binaryRibbonFactor_pos _
    · exact ih _
    · exact binaryRibbonFactor_powerEquiv _

/-- The actual positive composition at the fixed full family weight. -/
def binaryRibbon (e : ℕ) (b : Fin e → Bool) : Composition (3 ^ e) where
  blocks := binaryRibbonWord e b
  blocks_pos := by intro a ha; exact binaryRibbonWord_pos e b a ha
  blocks_sum := binaryRibbonWord_sum e b

/-- The first unit cut reads exactly the chosen orientation of a weight-three factor. -/
theorem binaryRibbonFactor_first_cut (b : Bool) :
    1 ∈ wordProperCuts (binaryRibbonFactor b) ↔ b = false := by
  cases b <;> decide +kernel

/-- The whole-inner boundary recovers the outermost orientation bit. -/
theorem binaryRibbonWord_head_cut (e : ℕ) (b : Fin (e + 1) → Bool) :
    3 ^ e ∈ wordProperCuts (binaryRibbonWord (e + 1) b) ↔ b 0 = false := by
  have hn : 0 < 3 ^ e := pow_pos (by decide) _
  change 3 ^ e ∈ wordProperCuts (wordCompose
    (binaryRibbonWord e (fun i => b i.succ)) (binaryRibbonFactor (b 0))) ↔ _
  rw [wordCompose_cuts_mod _ _ (binaryRibbonWord_pos e _) (by
      rw [binaryRibbonWord_sum]; exact hn) (binaryRibbonFactor_pos _) _ (by
      rw [binaryRibbonFactor_sum, binaryRibbonWord_sum]; omega)]
  simp only [binaryRibbonWord_sum, Nat.mod_self, Nat.div_self hn, ite_true]
  exact binaryRibbonFactor_first_cut _

/-- Every proper position of the first inner copy retains exactly that inner word's cuts. -/
theorem binaryRibbonWord_internal_cut (e : ℕ) (b : Fin (e + 1) → Bool)
    (x : ℕ) (hx : 0 < x) (hxn : x < 3 ^ e) :
    x ∈ wordProperCuts (binaryRibbonWord (e + 1) b) ↔
      x ∈ wordProperCuts (binaryRibbonWord e (fun i => b i.succ)) := by
  have hn : 0 < 3 ^ e := pow_pos (by decide) _
  change x ∈ wordProperCuts (wordCompose
    (binaryRibbonWord e (fun i => b i.succ)) (binaryRibbonFactor (b 0))) ↔ _
  rw [wordCompose_cuts_mod _ _ (binaryRibbonWord_pos e _) (by
      rw [binaryRibbonWord_sum]; exact hn) (binaryRibbonFactor_pos _) _ (by
      rw [binaryRibbonFactor_sum, binaryRibbonWord_sum]; omega)]
  simp only [binaryRibbonWord_sum, Nat.mod_eq_of_lt hxn,
    ite_eq_right (ne_of_gt hx)]

/-- Every binary orientation choice gives a distinct actual composition. -/
theorem binaryRibbon_injective (e : ℕ) : Function.Injective (binaryRibbon e) := by
  induction e with
  | zero => intro b c he; exact Subsingleton.elim _ _
  | succ e ih =>
    intro b c he
    have hword : binaryRibbonWord (e + 1) b = binaryRibbonWord (e + 1) c :=
      congrArg Composition.blocks he
    have hcuts := congrArg wordProperCuts hword
    have hhead : b 0 = c 0 := by
      have hh : 3 ^ e ∈ wordProperCuts (binaryRibbonWord (e + 1) b) ↔
          3 ^ e ∈ wordProperCuts (binaryRibbonWord (e + 1) c) := by rw [hcuts]
      rw [binaryRibbonWord_head_cut, binaryRibbonWord_head_cut] at hh
      cases hb : b 0 <;> cases hc : c 0 <;> simp_all
    have hinner : wordProperCuts (binaryRibbonWord e (fun i => b i.succ)) =
        wordProperCuts (binaryRibbonWord e (fun i => c i.succ)) := by
      ext x
      by_cases hx : 0 < x ∧ x < 3 ^ e
      · have hb := binaryRibbonWord_internal_cut e b x hx.1 hx.2
        have hc := binaryRibbonWord_internal_cut e c x hx.1 hx.2
        have hh : x ∈ wordProperCuts (binaryRibbonWord (e + 1) b) ↔
            x ∈ wordProperCuts (binaryRibbonWord (e + 1) c) := by rw [hcuts]
        exact hb.symm.trans (hh.trans hc)
      · constructor <;> intro hm
        · have hb := wordProperCuts_bounds _ (binaryRibbonWord_pos e _) x hm
          rw [binaryRibbonWord_sum] at hb
          exact (hx hb).elim
        · have hc := wordProperCuts_bounds _ (binaryRibbonWord_pos e _) x hm
          rw [binaryRibbonWord_sum] at hc
          exact (hx hc).elim
    have htailComp : binaryRibbon e (fun i => b i.succ) =
        binaryRibbon e (fun i => c i.succ) := by
      apply properCuts_injective
      exact (wordProperCuts_blocks (binaryRibbon e (fun i => b i.succ))).symm.trans
        (hinner.trans (wordProperCuts_blocks (binaryRibbon e (fun i => c i.succ))))
    have htail := ih htailComp
    funext i
    refine Fin.cases hhead (fun j => ?_) i
    exact congrFun htail j

/-- Every distinct binary choice belongs to the reference word's actual full ribbon class. -/
theorem binaryRibbon_mem_class (e : ℕ) (b : Fin e → Bool) :
    binaryRibbon e b ∈ ribbonClass (binaryRibbon e (fun _ => false)) := by
  change ribbonWord (binaryRibbonWord e b) = ribbonWord (binaryRibbonWord e (fun _ => false))
  simpa only [wordNearPower, (wordNear_nil _).1] using
    binaryRibbonWord_powerEquiv e b 1

/-- The actual ribbon classes contain at least one member for each binary factor choice. -/
theorem binaryRibbon_class_lower_bound (e : ℕ) :
    2 ^ e ≤ (ribbonClass (binaryRibbon e (fun _ => false))).ncard := by
  have hs : Set.range (binaryRibbon e) ⊆ ribbonClass (binaryRibbon e (fun _ => false)) := by
    rintro _ ⟨b, rfl⟩
    exact binaryRibbon_mem_class e b
  have hc := Set.ncard_le_ncard hs
  rw [Set.ncard_range_of_injective (binaryRibbon_injective e)] at hc
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool] using hc

end SkewClassInflation
