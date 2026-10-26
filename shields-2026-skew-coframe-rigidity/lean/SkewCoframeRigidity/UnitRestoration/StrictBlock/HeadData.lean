/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock
import SkewCoframeRigidity.Unshifted.Components

/-!
# The data of one head step: prefix, strict block, recursive cap

Formalizes the combinatorial objects of the proof of `sc:linearized-cap` in
`shields-2026-skew-coframe-rigidity.tex`.  Fix a connected zero-free board `B` with `n + 1` rows,
the prefix of the proper matrix consisting of its first `p` proper indices, and the next strict
block `E` on the proper indices `[p, p + e + 1)`.

* `capOfPrefix` is the cap `K_E` of `sc:fcp-recursive-cap`: its rows are `X_i - t` for `i ≤ p`
  and its columns `Y_j - t` for `j < p` together with `0`, where `t` is the head row of `E`.
* `blockBoard` is `E`, translated so that its last column is `0`.
* `numeratorBoard` is the board with rows `X_N` and columns `Y_N` of the top row-replacement
  quotient.
* `splice_capOfPrefix` identifies `K_E ◁ E` with `numeratorBoard` as a literal diagram.

Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe

variable {n p e : ℕ}

/-- The prefix `P` of the proper indices `[0, p)` is closed: a cut sits at `p`. -/
def PrefixCut (B : BetaDiagram (n + 1)) (p : ℕ) (hp : p + 1 ≤ n) : Prop :=
  0 < p → B.row ⟨p + 1, by omega⟩ < B.col ⟨p - 1, by omega⟩

/-- No cut inside the block: consecutive indices of the block overlap. -/
def BlockInside (B : BetaDiagram (n + 1)) (p e : ℕ) (hpe : p + e + 1 ≤ n) : Prop :=
  ∀ i : ℕ, ∀ hi : i < e, B.col ⟨p + i, by omega⟩ ≤ B.row ⟨p + i + 2, by omega⟩

section Cap

variable (B : BetaDiagram (n + 1)) (hp : p + 1 ≤ n)

/-- The rows of the recursive cap `K_E`: `X_i - t` for `0 ≤ i ≤ p`, `t` the head row of `E`. -/
def capRow (i : Fin (p + 1)) : ℤ := B.row ⟨i.val, by omega⟩ - B.row ⟨p + 1, by omega⟩

/-- The columns of the recursive cap: `Y_j - t` for `j < p`, then `0`. -/
def capCol (j : Fin (p + 1)) : ℤ :=
  if h : j.val < p then B.col ⟨j.val, by omega⟩ - B.row ⟨p + 1, by omega⟩ else 0

/-- The recursive cap `K_E` of `sc:fcp-recursive-cap`, an actual diagram when the prefix is
closed. -/
def capOfPrefix (hcut : PrefixCut B p hp) : BetaDiagram (p + 1) where
  row := capRow B hp
  col := capCol B hp
  row_strictAnti := by
    intro i j hij
    have := B.row_strictAnti (show (⟨i.val, by omega⟩ : Fin (n + 1)) < ⟨j.val, by omega⟩ from hij)
    simp only [capRow]; omega
  col_strictAnti := by
    intro i j hij
    have hij' : i.val < j.val := hij
    by_cases hj : j.val < p
    · have hi : i.val < p := by omega
      have := B.col_strictAnti (show (⟨i.val, by omega⟩ : Fin (n + 1)) < ⟨j.val, by omega⟩ from hij')
      simp only [capCol, hi, hj, ↓reduceDIte]; omega
    · have hi : i.val < p := by omega
      have hpos : 0 < p := by omega
      have h1 := hcut hpos
      have h2 := B.col_strictAnti.antitone
        (show (⟨i.val, by omega⟩ : Fin (n + 1)) ≤ ⟨p - 1, by omega⟩ from by
          rw [Fin.le_iff_val_le_val]; simp only; omega)
      simp only [capCol, hi, hj, ↓reduceDIte, ↓reduceDIte]; omega
  row_nonempty := by
    intro i
    by_cases hi : i.val < p
    · have := B.row_nonempty ⟨i.val, by omega⟩
      simp only [capCol, capRow, hi, ↓reduceDIte]; omega
    · have hip : i.val = p := by omega
      have := B.row_strictAnti (show (⟨p + 1, by omega⟩ : Fin (n + 1)) > ⟨i.val, by omega⟩ from by
        rw [gt_iff_lt, Fin.lt_def]; simp only; omega)
      simp only [capCol, capRow, hi, ↓reduceDIte]; omega

theorem capOfPrefix_isNorm (hcut : PrefixCut B p hp) : IsNorm (capOfPrefix B hp hcut) := by
  show capCol B hp (Fin.last p) = 0
  simp [capCol]

theorem capOfPrefix_connected (hB : B.Connected) (hcut : PrefixCut B p hp) :
    (capOfPrefix B hp hcut).Connected := by
  refine ⟨by omega, fun i hi => ?_⟩
  change capCol B hp i ≤ capRow B hp ⟨i.val + 1, hi⟩
  have h : B.col ⟨i.val, by omega⟩ ≤ B.row ⟨i.val + 1, by omega⟩ :=
    hB.2 ⟨i.val, by omega⟩ (by simp only; omega)
  by_cases hip : i.val < p
  · simp only [capCol, capRow, hip, ↓reduceDIte]; omega
  · omega

theorem capOfPrefix_zeroFree (hz : ZeroFree B) (hcut : PrefixCut B p hp) :
    ZeroFree (capOfPrefix B hp hcut) := by
  intro i j
  change capRow B hp i ≠ capCol B hp j
  have ht : B.row ⟨i.val, by omega⟩ ≠ B.row ⟨p + 1, by omega⟩ := by
    intro h
    have := B.row_strictAnti.injective h
    have := congrArg Fin.val this
    simp only at this
    have hi := i.isLt
    omega
  by_cases hj : j.val < p
  · simp only [capRow, capCol, hj, ↓reduceDIte]
    have := hz ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    omega
  · simp only [capRow, capCol, hj, ↓reduceDIte]
    omega

end Cap


section Block

variable (B : BetaDiagram (n + 1)) (hpe : p + e + 1 ≤ n)

/-- The least column `a₀` of the block on the proper indices `[p, p + e + 1)`. -/
def blockLeast : ℤ := B.col ⟨p + e, by omega⟩

/-- The strict block `E`, translated so that its last column is `0`. -/
def blockBoard (hz : ZeroFree B) (hB : B.Connected) : BetaDiagram (e + 1) where
  row i := B.row ⟨p + 1 + i.val, by omega⟩ - blockLeast B hpe
  col i := B.col ⟨p + i.val, by omega⟩ - blockLeast B hpe
  row_strictAnti := by
    intro i j hij
    have := B.row_strictAnti
      (show (⟨p + 1 + i.val, by omega⟩ : Fin (n + 1)) < ⟨p + 1 + j.val, by omega⟩ from by
        rw [Fin.lt_def]; simp only; exact Nat.add_lt_add_left hij _)
    exact sub_lt_sub_right this _
  col_strictAnti := by
    intro i j hij
    have := B.col_strictAnti
      (show (⟨p + i.val, by omega⟩ : Fin (n + 1)) < ⟨p + j.val, by omega⟩ from by
        rw [Fin.lt_def]; simp only; exact Nat.add_lt_add_left hij _)
    exact sub_lt_sub_right this _
  row_nonempty := by
    intro i
    have h1 : B.col ⟨p + i.val, by omega⟩ ≤ B.row ⟨p + i.val + 1, by omega⟩ :=
      hB.2 ⟨p + i.val, by omega⟩ (by simp only; omega)
    have h2 := hz ⟨p + i.val + 1, by omega⟩ ⟨p + i.val, by omega⟩
    have h3 : B.row ⟨p + 1 + i.val, by omega⟩ = B.row ⟨p + i.val + 1, by omega⟩ := by
      congr 2; omega
    omega

theorem blockBoard_isNorm (hz : ZeroFree B) (hB : B.Connected) : IsNorm (blockBoard B hpe hz hB) := by
  show B.col ⟨p + (Fin.last e).val, by omega⟩ - blockLeast B hpe = 0
  simp [blockLeast]

theorem blockBoard_connected (hz : ZeroFree B) (hB : B.Connected) (hin : BlockInside B p e hpe) :
    (blockBoard B hpe hz hB).Connected := by
  refine ⟨by omega, fun i hi => ?_⟩
  change B.col ⟨p + i.val, by omega⟩ - blockLeast B hpe ≤
    B.row ⟨p + 1 + (i.val + 1), by omega⟩ - blockLeast B hpe
  have h := hin i.val (by omega)
  have h3 : B.row ⟨p + 1 + (i.val + 1), by omega⟩ = B.row ⟨p + i.val + 2, by omega⟩ := by
    congr 2; omega
  omega

theorem blockBoard_zeroFree (hz : ZeroFree B) (hB : B.Connected) :
    ZeroFree (blockBoard B hpe hz hB) := by
  intro i j
  change B.row ⟨p + 1 + i.val, by omega⟩ - blockLeast B hpe ≠
    B.col ⟨p + j.val, by omega⟩ - blockLeast B hpe
  have := hz ⟨p + 1 + i.val, by omega⟩ ⟨p + j.val, by omega⟩
  omega

variable (hz : ZeroFree B) (hB : B.Connected) (hcut : PrefixCut B p (by omega : p + 1 ≤ n))

/-- `K_E ◁ E` as a literal splice of the recursive cap onto the translated block. -/
def numeratorBoard : BetaDiagram (p + e + 1) :=
  splice (capOfPrefix B (by omega : p + 1 ≤ n) hcut) (blockBoard B hpe hz hB)
    (capOfPrefix_isNorm B _ hcut) (blockBoard_isNorm B hpe hz hB)

theorem numeratorBoard_row (i : Fin (p + e + 1)) :
    (numeratorBoard B hpe hz hB hcut).row i =
      if i.val < p + 1 then B.row ⟨i.val, by omega⟩ - blockLeast B hpe
      else B.row ⟨i.val + 1, by omega⟩ - blockLeast B hpe := by
  change spliceRow _ _ i = _
  unfold spliceRow
  by_cases hi : i.val < p + 1
  · simp only [hi, dite_true, if_true, capOfPrefix, capRow, blockBoard]
    have : (⟨p + 1 + (0 : Fin (e + 1)).val, by omega⟩ : Fin (n + 1)) = ⟨p + 1, by omega⟩ := rfl
    rw [this]; ring
  · simp only [hi, dite_false, if_false, blockBoard]
    congr 2
    · ext; simp; omega

theorem numeratorBoard_col (j : Fin (p + e + 1)) :
    (numeratorBoard B hpe hz hB hcut).col j = B.col ⟨j.val, by omega⟩ - blockLeast B hpe := by
  change spliceCol _ _ j = _
  unfold spliceCol
  by_cases hj : j.val < p
  · simp only [hj, dite_true, capOfPrefix, capCol, blockBoard]
    have : (⟨p + 1 + (0 : Fin (e + 1)).val, by omega⟩ : Fin (n + 1)) = ⟨p + 1, by omega⟩ := rfl
    rw [this]; ring
  · simp only [hj, dite_false, blockBoard]
    congr 2
    ext; simp; omega

end Block


section Restriction

/-- The weights of `ρ` on the positions strictly between `a₀` and `t`, translated by `-a₀`. -/
noncomputable def restrictBlock (ρ : ℤ →₀ ℚ) (a₀ t : ℤ) : ℤ →₀ ℚ :=
  Finsupp.mapDomain (fun x => x - a₀) (ρ.filter fun x => a₀ < x ∧ x < t)

theorem mem_support_restrictBlock {ρ : ℤ →₀ ℚ} {a₀ t x : ℤ}
    (hx : x ∈ (restrictBlock ρ a₀ t).support) : x + a₀ ∈ ρ.support ∧ 0 < x ∧ x < t - a₀ := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hx)
  have := (Finsupp.mem_support_iff).mp hy
  rw [Finsupp.filter_apply] at this
  split_ifs at this with h
  · refine ⟨?_, by omega, by omega⟩
    rw [Finsupp.mem_support_iff]; simpa using this
  · exact absurd rfl this

end Restriction


section Vacancies

variable (B : BetaDiagram (n + 1)) (hpe : p + e + 1 ≤ n) (hz : ZeroFree B) (hB : B.Connected)

/-- The head row `t` of the block. -/
def blockHead : ℤ := B.row ⟨p + 1, by omega⟩

theorem blockBoard_largestLabel :
    (blockBoard B hpe hz hB).largestLabel = blockHead B hpe - blockLeast B hpe := by
  rw [largestLabel_of_norm _ (blockBoard_isNorm B hpe hz hB)]
  rfl

/-- A genuine vacancy of `B` strictly between the least column and head row of the block is a
genuine vacancy of the translated block. -/
theorem blockBoard_isVacancy (hBn : IsNorm B) {x : ℤ} (h0 : 0 < x)
    (h1 : x < blockHead B hpe - blockLeast B hpe) (hr : ∀ i, B.row i ≠ x + blockLeast B hpe)
    (hc : ∀ j, B.col j ≠ x + blockLeast B hpe) : IsVacancy (blockBoard B hpe hz hB) x := by
  refine ⟨h0, ?_, fun i => ?_, fun j => ?_⟩
  · rw [blockBoard_largestLabel]; exact h1
  · intro h
    exact hr ⟨p + 1 + i.val, by omega⟩ (by
      change B.row ⟨p + 1 + i.val, by omega⟩ - blockLeast B hpe = x at h
      omega)
  · intro h
    exact hc ⟨p + j.val, by omega⟩ (by
      change B.col ⟨p + j.val, by omega⟩ - blockLeast B hpe = x at h
      omega)

/-- The block is of smaller span than `B`. -/
theorem blockBoard_largestLabel_lt (hBn : IsNorm B) :
    (blockBoard B hpe hz hB).largestLabel < B.largestLabel := by
  rw [blockBoard_largestLabel, largestLabel_of_norm B hBn]
  have h1 : B.row ⟨p + 1, by omega⟩ < B.row 0 :=
    B.row_strictAnti (show (0 : Fin (n + 1)) < ⟨p + 1, by omega⟩ from by
      rw [Fin.lt_def]; simp)
  have h2 := col_nonneg B hBn ⟨p + e, by omega⟩
  unfold blockHead blockLeast
  omega

end Vacancies

end SkewCoframeRigidity.UnitRestoration
