/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.WordPrefixCuts
import SkewClassInflation.PeriodicCutPowers

/-!
# Literal overlapped words and their periodic cuts

Formalizes `eq:overlap-cut-set` of `shields-2026-skew-class-inflation.tex`.
The composition is the displayed endpoint-merging word, not a composition
postulated to have the desired cuts.  Its actual proper cuts are recovered
from the word and identified with the periodic construction.  Sorry-free.
-/

namespace SkewClassInflation

/-- The paper's positive inner word with at least its two endpoint parts. -/
structure OverlapWord where
  /-- The first endpoint part of the original word. -/
  first : ℕ
  /-- The last endpoint part of the original word. -/
  last : ℕ
  /-- The original parts strictly between the two endpoints. -/
  middle : List ℕ
  /-- The amount removed when the last and first parts merge across copies. -/
  delta : ℕ
  delta_pos : 0 < delta
  first_bound : delta < first
  last_bound : delta < last
  middle_pos : ∀ a ∈ middle, 0 < a

namespace OverlapWord

variable (R : OverlapWord)

/-- The amount by which a further overlapped copy increases the weight. -/
def period : ℕ := R.first + R.middle.sum + R.last - R.delta

/-- The actual merged endpoint part. -/
def merged : ℕ := R.first + R.last - R.delta

/-- The literal word preceding the final endpoint, with `m` additional copies. -/
def wordPrefix (m : ℕ) : List ℕ :=
  (R.first :: R.middle) ++ (List.replicate m (R.merged :: R.middle)).flatten

/-- Proper cuts of the original one-copy word. -/
def cuts : Finset ℕ := prefixEnds (R.first :: R.middle)

/-- The endpoint inequality makes the merger an actual positive increase of the first part. -/
theorem merged_eq : R.merged = R.first + (R.last - R.delta) := by
  have := R.last_bound
  dsimp only [merged]
  omega

/-- One repeated block has exactly the claimed period weight. -/
theorem merged_sum : R.merged + R.middle.sum = R.period := by
  have := R.last_bound
  dsimp only [merged, period]
  omega

/-- The literal endpoint word has the same tail at every positive copy count. -/
theorem prefix_succ (m : ℕ) :
    R.wordPrefix (m + 1) =
      (R.first :: R.middle) ++ (R.merged :: (R.wordPrefix m).tail) := by
  simp only [wordPrefix, List.replicate_succ, List.flatten_cons, List.cons_append,
    List.tail_cons]

/-- All entries of the displayed overlapped word are positive. -/
theorem prefix_pos (m : ℕ) : ∀ a ∈ R.wordPrefix m, 0 < a := by
  intro a ha
  have hm : 0 < R.merged := by rw [R.merged_eq]; have := R.first_bound; omega
  simp only [wordPrefix, List.mem_append, List.mem_cons, List.mem_flatten,
    List.mem_replicate] at ha
  rcases ha with (rfl | ha) | ⟨l, ⟨_, rfl⟩, ha⟩
  · have := R.first_bound; omega
  · exact R.middle_pos a ha
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact hm
    · exact R.middle_pos a ha

/-- The complete prefix has its original weight plus one period per additional copy. -/
theorem prefix_sum (m : ℕ) :
    (R.wordPrefix m).sum = R.first + R.middle.sum + m * R.period := by
  simp only [wordPrefix, List.sum_append, List.sum_cons, List.sum_flatten,
    List.map_replicate, List.sum_replicate]
  rw [R.merged_sum, nsmul_eq_mul]
  rfl

/-- The actual positive composition with `m+1` copies of the inner word. -/
def composition (m : ℕ) : Composition ((m + 1) * R.period + R.delta) where
  blocks := R.wordPrefix m ++ [R.last]
  blocks_pos := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact R.prefix_pos m a ha
    · have he := List.mem_singleton.mp ha
      rw [he]
      have := R.last_bound
      omega
  blocks_sum := by
    rw [List.sum_append, R.prefix_sum, List.sum_singleton]
    have h : R.period + R.delta = R.first + R.middle.sum + R.last := by
      dsimp only [period]
      have := R.last_bound
      omega
    nlinarith

/-- Every one-copy cut lies strictly between the overlap and the next period. -/
theorem cuts_bounds : ∀ x ∈ R.cuts, R.delta < x ∧ x < R.period := by
  intro x hx
  have hb := prefixEnds_bounds (R.first :: R.middle)
    (by intro a ha; rcases List.mem_cons.mp ha with rfl | ha
        · have := R.first_bound; omega
        · exact R.middle_pos a ha) x hx
  have hlow : R.first ≤ x := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      omega
  have hlast := R.last_bound
  have hfirst := R.first_bound
  dsimp only [period]
  simp only [List.sum_cons] at hb
  omega

/-- The periodic increment is positive and strictly exceeds the overlap. -/
theorem delta_lt_period : R.delta < R.period := by
  have ha := R.first_bound
  have hb := R.last_bound
  dsimp only [period]
  omega

/-- Adding one copy inserts the old cuts and translates every previous cut by one period. -/
theorem prefix_cuts_succ (m : ℕ) :
    prefixEnds (R.wordPrefix (m + 1)) = R.cuts ∪
      (prefixEnds (R.wordPrefix m)).image (fun x => R.period + x) := by
  classical
  rw [R.prefix_succ, prefixEnds_append]
  have hp : R.wordPrefix m = R.first :: (R.wordPrefix m).tail := by
    simp only [wordPrefix, List.cons_append, List.tail_cons]
  rw [R.merged_eq, prefixEnds_head_add]
  rw [← hp, Finset.image_image]
  change R.cuts ∪ _ = R.cuts ∪ _
  congr 1
  apply Finset.image_congr
  intro x hx
  have hh : R.first + R.middle.sum + (R.last - R.delta) = R.period := by
    have := R.last_bound
    dsimp only [period]
    omega
  simp only [List.sum_cons, Function.comp_apply]
  omega

/-- Actual cuts of the displayed word are the bounded translates of the original cuts. -/
theorem properCuts_composition (m x : ℕ) :
    x ∈ properCuts (R.composition m) ↔
      ∃ j, j ≤ m ∧ ∃ y ∈ R.cuts, x = j * R.period + y := by
  rw [properCuts_blocks_append_single (R.composition m) (R.wordPrefix m) R.last rfl]
  induction m generalizing x with
  | zero =>
    simp only [wordPrefix, List.replicate_zero, List.flatten_nil, List.append_nil,
      Nat.le_zero, zero_mul, zero_add, exists_eq_left]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  | succ m ih =>
    rw [R.prefix_cuts_succ]
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (hx | ⟨z, hz, rfl⟩)
      · exact ⟨0, by omega, x, hx, by simp⟩
      · obtain ⟨j, hj, y, hy, rfl⟩ := ih z |>.mp hz
        exact ⟨j + 1, by omega, y, hy, by ring⟩
    · rintro ⟨j, hj, y, hy, rfl⟩
      cases j with
      | zero => exact Or.inl (by simpa only [zero_mul, zero_add] using hy)
      | succ j =>
        refine Or.inr ⟨j * R.period + y, (ih _).mpr ⟨j, by omega, y, hy, rfl⟩, ?_⟩
        ring

/-- The literal overlap word satisfies the exact periodic membership test. -/
theorem properCuts_periodic (m x : ℕ) (hx : 0 < x)
    (hT : x < (m + 1) * R.period + R.delta) :
    x ∈ properCuts (R.composition m) ↔ x % R.period ∈ R.cuts := by
  rw [R.properCuts_composition]
  have hQ : 0 < R.period := by have := R.delta_lt_period; omega
  constructor
  · rintro ⟨j, hj, y, hy, rfl⟩
    have hyQ := (R.cuts_bounds y hy).2
    simpa only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt hyQ] using hy
  · intro hc
    have hy := R.cuts_bounds (x % R.period) hc
    have hd := Nat.div_add_mod x R.period
    have hj : x / R.period ≤ m := by
      by_contra hn
      have hh : (m + 1) * R.period ≤ R.period * (x / R.period) := by
        nlinarith
      omega
    exact ⟨x / R.period, hj, x % R.period, hc, by nlinarith⟩

/-- The periodic cut construction is the actual displayed endpoint-merging word. -/
theorem composition_eq_periodic (m : ℕ) :
    R.composition m = periodicCutPower (m + 1) R.period R.delta R.cuts := by
  apply properCuts_injective
  ext x
  by_cases hx : 0 < x ∧ x < (m + 1) * R.period + R.delta
  · rw [R.properCuts_periodic m x hx.1 hx.2,
      periodicCutPower_internal _ _ _ _ x hx.1 hx.2]
  · constructor <;> intro h <;> exact (hx (properCuts_bounds _ x h)).elim

/-- No multipart right factor can produce the actual overlapped word with at least two copies. -/
theorem no_right_factor (m : ℕ) (hm : 1 ≤ m) {n q : ℕ}
    (γ : Composition n) (β : Composition q) (hγ : 2 ≤ n) (hβ : 2 ≤ β.length) :
    (⟨n * q, compositionProduct γ β⟩ : (N : ℕ) × Composition N) ≠
      ⟨(m + 1) * R.period + R.delta, R.composition m⟩ := by
  rw [R.composition_eq_periodic]
  exact periodicCutPower_no_right_factor (m + 1) R.period R.delta (by omega)
    R.delta_pos R.delta_lt_period R.cuts R.cuts_bounds γ β hγ hβ

private theorem repeat_slide (u v : List ℕ) (m : ℕ) :
    (List.replicate m (u ++ v)).flatten ++ u =
      u ++ (List.replicate m (v ++ u)).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    calc
      (u ++ v) ++ (List.replicate m (u ++ v)).flatten ++ u =
          (u ++ v) ++ ((List.replicate m (u ++ v)).flatten ++ u) :=
        List.append_assoc _ _ _
      _ = (u ++ v) ++ (u ++ (List.replicate m (v ++ u)).flatten) :=
        congrArg (List.append (u ++ v)) ih
      _ = u ++ ((v ++ u) ++ (List.replicate m (v ++ u)).flatten) := by
        simp only [List.append_assoc]

/-- A symmetric inner word produces a genuinely symmetric literal overlapped word at every order. -/
theorem composition_palindrome (m : ℕ) (hends : R.first = R.last)
    (hmid : R.middle.reverse = R.middle) :
    (R.composition m).blocks.reverse = (R.composition m).blocks := by
  have hc : (R.middle ++ (List.replicate m (R.merged :: R.middle)).flatten).reverse =
      R.middle ++ (List.replicate m (R.merged :: R.middle)).flatten := by
    rw [List.reverse_append]
    simp only [List.reverse_flatten, List.map_replicate, List.reverse_replicate,
      List.reverse_cons, hmid]
    exact repeat_slide R.middle [R.merged] m
  have hw : (R.composition m).blocks =
      (R.first :: (R.middle ++ (List.replicate m (R.merged :: R.middle)).flatten)) ++
        [R.last] := by
    simp only [composition, wordPrefix, List.cons_append, List.append_assoc]
  rw [hw, List.reverse_append, List.reverse_singleton, List.reverse_cons, hc]
  simp only [List.cons_append, List.nil_append, List.append_assoc, hends]

/-- Palindromicity of the actual one-copy word supplies every higher overlap's symmetry. -/
theorem composition_palindrome_of_base (m : ℕ)
    (hbase : (R.composition 0).blocks.reverse = (R.composition 0).blocks) :
    (R.composition m).blocks.reverse = (R.composition m).blocks := by
  have hw : (R.composition 0).blocks = (R.first :: R.middle) ++ [R.last] := by
    simp only [composition, wordPrefix, List.replicate_zero, List.flatten_nil, List.append_nil]
  rw [hw, List.reverse_append, List.reverse_singleton, List.reverse_cons] at hbase
  simp only [List.cons_append, List.nil_append] at hbase
  have hends : R.last = R.first := (List.cons.inj hbase).1
  have hm : R.middle.reverse ++ [R.first] = R.middle ++ [R.last] := (List.cons.inj hbase).2
  rw [hends] at hm
  have hmid : R.middle.reverse = R.middle := List.append_cancel_right hm
  exact R.composition_palindrome m hends.symm hmid

end OverlapWord
end SkewClassInflation
