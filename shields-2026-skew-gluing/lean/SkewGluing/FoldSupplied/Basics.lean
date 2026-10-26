import SkewGluing.SmallOverlap.EmptyFold
import SkewGluing.Aligned

/-!
# Occupied area, line outers and completed words

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:empty-fold`, `ge:ordinary-fold`, `ge:mixed-fold`): the bookkeeping shared by the
residue folds of a supplied inner.

* `card_fromBits`, `card_eq_sum_heightWord`: the occupied area is the sum of the heights of the
  word of the diagram;
* `lineOuter m lam`: the outer whose `m - 1` bit pairs all equal `lam`, the row for `lam = 0`
  and the column for `lam = 1` (`lineOuter_zero`, `lineOuter_one`);
* `completedA`, `completedB`: the closed native words with the value at the returned residue zero
  replaced by `lam`.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

theorem fromBits_congr {N : ℕ} {A B A' B' : ℕ → ℤ}
    (hA : ∀ k, 1 ≤ k → k < N → A k = A' k) (hB : ∀ k, 1 ≤ k → k < N → B k = B' k) :
    fromBits N A B = fromBits N A' B' := by
  have hlo : ∀ k, k < N → bitsLo A k = bitsLo A' k := by
    intro k hk
    unfold bitsLo
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    exact hA (m + 1) (by omega) (by omega)
  have hh : ∀ k, k < N → heightWord A B k = heightWord A' B' k := by
    intro k hk
    unfold heightWord
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    rw [hA (m + 1) (by omega) (by omega), hB (m + 1) (by omega) (by omega)]
  unfold fromBits
  apply Finset.biUnion_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [hlo k hk, hh k hk]

/-- The occupied area of the diagram of a bit word is the sum of its heights. -/
theorem card_fromBits {N : ℕ} {A B : ℕ → ℤ} (h : IsBitData N A B) :
    ((fromBits N A B).card : ℤ) = ∑ k ∈ Finset.range N, heightWord A B k := by
  unfold fromBits
  rw [Finset.card_biUnion]
  · push_cast
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.fst hab)]
    rw [Int.card_Icc]
    have := h.2.2.1 k hk
    have := bitsLo_add_heightWord A B k
    omega
  · intro k hk l hl hkl
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image] at hx hx'
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨j, -, hj⟩ := hx'
    simp only [Prod.mk.injEq] at hj
    apply hkl
    have : (k : ℤ) = l := by omega
    exact_mod_cast this

/-- The occupied area of a connected skew diagram: the sum of the heights of its bit words. -/
theorem card_eq_sum_heightWord {D : Diagram} (hD : IsConnectedSkew D) :
    ((D.card : ℕ) : ℤ) = ∑ k ∈ Finset.range (span D),
      heightWord (fun k : ℕ => wordA D k) (fun k : ℕ => wordB D k) k := by
  have hb : IsBitData (span D) (fun k : ℕ => wordA D k) (fun k : ℕ => wordB D k) :=
    isBitData_of_isConnectedSkew hD
  have huniq := (exists_unique_connectedSkew_of_bits hb).2.2.2.2 D hD rfl
    (fun k hk1 hk2 => ⟨by simp only [wordA], by simp only [wordB]⟩)
  obtain ⟨v, hv⟩ := huniq
  have hc : D.card = (fromBits (span D) (fun k : ℕ => wordA D k)
      (fun k : ℕ => wordB D k)).card := by
    refine (congrArg Finset.card hv).trans ?_
    exact Finset.card_image_of_injective _ (add_left_injective _)
  rw [hc]
  exact card_fromBits hb

/-- The outer whose `m - 1` interior bit pairs all equal `lam`. -/
def lineOuter (m : ℕ) (lam : ℤ) : Diagram := fromBits m (fun _ => lam) (fun _ => lam)

theorem isBitData_line {m : ℕ} (hm : 1 ≤ m) {lam : ℤ} (hl : lam = 0 ∨ lam = 1) :
    IsBitData m (fun _ => lam) (fun _ => lam) := by
  refine ⟨hm, fun k _ _ => ⟨hl, hl⟩, fun k _ => ?_, ?_⟩ <;>
    simp [heightWord]

/-- The row of `m` cells is the outer with all bits zero. -/
theorem lineOuter_zero (m : ℕ) : lineOuter m 0 = skewOf [m] [] := by
  ext ⟨i, j⟩
  unfold lineOuter
  rw [mem_fromBits']
  simp only [skewOf, List.length_singleton, Finset.range_one, Finset.singleton_biUnion,
    Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq, List.getD_cons_zero, List.getD_nil,
    Nat.cast_zero, bitsLo, Finset.sum_const_zero, neg_zero]
  constructor
  · rintro ⟨k, hk, hj, h1, h2⟩
    exact ⟨j, ⟨by omega, by omega⟩, by omega, rfl⟩
  · rintro ⟨j', ⟨h1, h2⟩, hi, rfl⟩
    refine ⟨j'.toNat, by omega, by omega, by omega, by omega⟩

/-- The column of `m` cells is, up to translation, the outer with all bits one. -/
theorem lineOuter_one (m : ℕ) :
    lineOuter m 1 = translate (-((m : ℤ) - 1), 0) (skewOf (List.replicate m 1) []) := by
  ext ⟨i, j⟩
  unfold lineOuter
  rw [mem_fromBits', mem_translate]
  have hb : ∀ k : ℕ, bitsLo (fun _ => (1 : ℤ)) k = -(k : ℤ) := by
    intro k; simp [bitsLo]
  have hcell : ∀ r c : ℤ, (r, c) ∈ skewOf (List.replicate m 1) [] ↔
      0 ≤ r ∧ r < m ∧ c = 0 := by
    intro r c
    simp only [skewOf, List.length_replicate, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
    constructor
    · rintro ⟨r', hr', c', ⟨h1, h2⟩, hr, hc⟩
      have e : (List.replicate m 1).getD r' 0 = 1 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hr']
      rw [e] at h2
      have hz : (0 : ℤ) ≤ c' := by simpa using h1
      have : c' < 1 := by simpa using h2
      subst hr
      exact ⟨by omega, by omega, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨r.toNat, by omega, 0, ⟨by simp, ?_⟩, by omega, by omega⟩
      have hlt : r.toNat < m := by omega
      have e : (List.replicate m 1).getD r.toNat 0 = 1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hlt]; rfl
      rw [e]; simp
  have := hcell (i - -((m : ℤ) - 1)) (j - 0)
  simp only [hb]
  rw [show ((i, j) - (-((m : ℤ) - 1), 0) : ℤ × ℤ) = (i - -((m : ℤ) - 1), j - 0) from rfl, this]
  constructor
  · rintro ⟨k, hk, hj, h1, h2⟩
    omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(m - 1 - (i + (m - 1))).toNat, by omega, by omega, by omega, by omega⟩

/-- The completed native column word of a connected diagram `K`: the closed word with the value
at the returned residue zero replaced by `lam`. -/
def completedA (K : Diagram) (lam : ℤ) (k : ℕ) : ℤ := if k = 0 then lam else wordA K k

/-- The completed native row word of a connected diagram `K`. -/
def completedB (K : Diagram) (lam : ℤ) (k : ℕ) : ℤ := if k = 0 then lam else wordB K k

end FoldSupplied
end SkewGluing
