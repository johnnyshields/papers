/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.PrefixSpliceCuts

/-!
# One-tour residues of a crossing window splice

The residue obstruction in the ordered window-comparison step for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
A strict increase in matching prefix positions creates one additional
positive residue while the complete residue sum remains one inner weight.
Sorry-free.
-/

namespace SkewClassInflation

/-- Taking residues commutes with literal concatenation, including zero residues. -/
theorem residueWord_append (u v : List ℕ) (n : ℕ) :
    residueWord (u ++ v) n = residueWord u n ++ residueWord v n := by
  simp only [residueWord, List.map_append, List.filter_append]

/-- A positive word whose parts are smaller than the modulus is unchanged. -/
theorem residueWord_eq_self (w : List ℕ) (n : ℕ)
    (hw : ∀ a ∈ w, 0 < a ∧ a < n) : residueWord w n = w := by
  have hm : w.map (fun x => x % n) = w := by
    calc
      _ = w.map id := List.map_congr_left (fun a ha => Nat.mod_eq_of_lt (hw a ha).2)
      _ = w := List.map_id w
  rw [residueWord, hm]
  apply List.filter_eq_self.mpr
  intro a ha
  exact decide_eq_true (Nat.ne_of_gt (hw a ha).1)

/-- The connecting part contributes exactly the positive difference of the two prefix positions. -/
theorem splice_residue_word {N : ℕ} (u v : Composition N) (hN : 0 < N)
    (t q : ℕ) (hu : 2 ≤ u.length) (hv : 2 ≤ v.length)
    (hab : (u.blocks.take t).sum < (v.blocks.take t).sum) :
    residueWord (u.blocks.take t ++
        (q * N + ((v.blocks.take t).sum - (u.blocks.take t).sum)) :: v.blocks.drop t) N =
      u.blocks.take t ++
        ((v.blocks.take t).sum - (u.blocks.take t).sum) :: v.blocks.drop t := by
  have hparts (w : Composition N) (hl : 2 ≤ w.length) :
      ∀ a ∈ w.blocks, 0 < a ∧ a < N := by
    intro a ha
    exact ⟨w.blocks_pos ha, composition_part_lt_of_multipart w hl a ha⟩
  have htake : residueWord (u.blocks.take t) N = u.blocks.take t :=
    residueWord_eq_self _ N (fun a ha => hparts u hu a (List.mem_of_mem_take ha))
  have hdrop : residueWord (v.blocks.drop t) N = v.blocks.drop t :=
    residueWord_eq_self _ N (fun a ha => hparts v hv a (List.mem_of_mem_drop ha))
  have hb : (v.blocks.take t).sum ≤ N := by
    have hh := List.sum_take_add_sum_drop v.blocks t
    rw [v.blocks_sum] at hh
    omega
  have hd : (v.blocks.take t).sum - (u.blocks.take t).sum < N := by
    by_cases hz : (u.blocks.take t).sum = 0
    · have ht : t = 0 := by
        cases t with
        | zero => rfl
        | succ s =>
          have hne : u.blocks ≠ [] := fun he => (Nat.ne_of_gt hN) (u.blocks_eq_nil.mp he)
          obtain ⟨a, w, he⟩ := List.exists_cons_of_ne_nil hne
          have ha := u.blocks_pos (by rw [he]; exact List.mem_cons_self)
          rw [he, List.take_succ_cons, List.sum_cons] at hz
          omega
      subst t
      simp at hab
    · omega
  rw [residueWord_append, htake]
  change _ ++ (((q * N + ((v.blocks.take t).sum - (u.blocks.take t).sum)) % N) ::
    ((v.blocks.drop t).map (fun x => x % N))).filter (fun x => decide (x ≠ 0)) = _
  have hmod : (q * N + ((v.blocks.take t).sum - (u.blocks.take t).sum)) % N =
      (v.blocks.take t).sum - (u.blocks.take t).sum := by
    simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt hd]
  rw [hmod, List.filter_cons_of_pos (p := fun x : ℕ => decide (x ≠ 0))
    (decide_eq_true (Nat.ne_of_gt (Nat.sub_pos_of_lt hab)))]
  exact congrArg (fun w => u.blocks.take t ++
    ((v.blocks.take t).sum - (u.blocks.take t).sum) :: w) hdrop

/-- A crossing splice has one-tour residue weight, rather than an extra wrap. -/
theorem splice_residue_sum {N : ℕ} (u v : Composition N) (hN : 0 < N)
    (t q : ℕ) (hu : 2 ≤ u.length) (hv : 2 ≤ v.length)
    (hab : (u.blocks.take t).sum < (v.blocks.take t).sum) :
    (residueWord (u.blocks.take t ++
      (q * N + ((v.blocks.take t).sum - (u.blocks.take t).sum)) :: v.blocks.drop t) N).sum = N := by
  rw [splice_residue_word u v hN t q hu hv hab, List.sum_append, List.sum_cons]
  have hh := List.sum_take_add_sum_drop v.blocks t
  rw [v.blocks_sum] at hh
  omega

/-- At matching internal ranks, a crossing splice has one more residue than either window. -/
theorem splice_residue_length {N : ℕ} (u v : Composition N) (hN : 0 < N)
    (t q : ℕ) (hu : 2 ≤ u.length) (hv : 2 ≤ v.length)
    (hlen : u.length = v.length) (ht : t < u.length)
    (hab : (u.blocks.take t).sum < (v.blocks.take t).sum) :
    (residueWord (u.blocks.take t ++
      (q * N + ((v.blocks.take t).sum - (u.blocks.take t).sum)) :: v.blocks.drop t) N).length =
        u.length + 1 := by
  rw [splice_residue_word u v hN t q hu hv hab, List.length_append,
    List.length_cons, List.length_take, List.length_drop]
  change min t u.length + (v.length - t + 1) = u.length + 1
  omega

/-- Whole-weight endpoint padding preserves the complete positive residue word. -/
theorem residueWord_wordPadEnds (w : List ℕ) (L R n : ℕ) (hne : w ≠ [])
    (hL : n ∣ L) (hR : n ∣ R) :
    residueWord (wordPadEnds w L R) n = residueWord w n := by
  unfold residueWord
  rw [wordPadEnds_mod w L R n hne hL hR]

end SkewClassInflation
