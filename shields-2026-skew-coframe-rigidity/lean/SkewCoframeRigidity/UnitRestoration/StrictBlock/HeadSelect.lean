/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.StrictBlock.HeadData

/-!
# Selection of the next head: a gap or a strict block

The combinatorial half of the head step of `sc:linearized-cap` in
`shields-2026-skew-coframe-rigidity.tex`.  Fix a connected zero-free normalized board `B` with
`n + 1` rows and nonzero weights `ρ` on its genuine vacancies, and let `b` be the largest position
of the support of `ρ`; every higher weight is zero.  Every vacancy of `B` lies either in a gap
between strict blocks or inside a strict block, and the prefix `P` of the paper consists of the
proper indices above it.

* Gap case.  `b` lies above the head row of the next block and below the least column of the
  prefix: the rows `X_0, …, X_p` and the columns `Y_0, …, Y_{p-1}` are exactly the labels above
  `b`.  The numerator `h_{m-b} - H_{m,cols P} P⁻¹ H_{rows P,b}` of `sc:gap-coface` is then the
  Schur function of the diagram with rows `X_0, …, X_p` and columns `Y_0, …, Y_{p-1}, b`.
* Block case.  `b` lies strictly between the least column and the head row of the strict block
  on the proper indices `[p, p + e + 1)`, after the closed prefix of `p` proper indices.  Every
  weight lies below the head row, and the restriction of `ρ` to the block is nonzero, and a cut sits at `p + e + 1` (the block is a
full strict component).

`head_select` is the exact dichotomy; it involves no derivative.  The prefix and block are the
inputs of `numeratorBoard`, `blockBoard` and `capOfPrefix` in `HeadData.lean`.

Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe

/-- The gap and block cases for the largest weighted vacancy `b` of a connected zero-free board. -/
theorem head_select {n : ℕ} (B : BetaDiagram (n + 1)) (hB : IsNorm B) (hBc : B.Connected)
    (hBz : ZeroFree B) (ρ : ℤ →₀ ℚ) (hρ : ∀ x ∈ ρ.support, IsVacancy B x) (hne : ρ ≠ 0) :
    (∃ (p : ℕ) (b : ℤ), p ≤ n ∧ ρ b ≠ 0 ∧ (∀ x ∈ ρ.support, x ≤ b) ∧
        (∀ i : Fin (n + 1), i.val ≤ p → b < B.row i) ∧
        (∀ i : Fin (n + 1), p < i.val → B.row i < b) ∧
        (∀ j : Fin (n + 1), j.val < p → b < B.col j) ∧
        (∀ j : Fin (n + 1), p ≤ j.val → B.col j < b) ∧
        ∀ hp : p + 1 ≤ n, PrefixCut B p hp) ∨
    (∃ (p e : ℕ) (hpe : p + e + 1 ≤ n) (_ : PrefixCut B p (by omega))
        (_ : BlockInside B p e hpe),
        restrictBlock ρ (blockLeast B hpe) (blockHead B hpe) ≠ 0 ∧
        (∀ x ∈ ρ.support, x < blockHead B hpe) ∧
        ∀ hq : p + e + 1 < n, B.row ⟨p + e + 2, by omega⟩ < B.col ⟨p + e, by omega⟩) := by
  have hsupp : ρ.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  set b := ρ.support.max' hsupp with hbdef
  have hbmem : b ∈ ρ.support := Finset.max'_mem _ _
  have hρb : ρ b ≠ 0 := Finsupp.mem_support_iff.mp hbmem
  have hle : ∀ x ∈ ρ.support, x ≤ b := fun x hx => Finset.le_max' _ _ hx
  obtain ⟨hb0, hbL, hbr, hbc⟩ := hρ b hbmem
  -- ℕ-indexed copies of the rows and columns
  let X : ℕ → ℤ := fun i => if h : i < n + 1 then B.row ⟨i, h⟩ else 0
  let Y : ℕ → ℤ := fun i => if h : i < n + 1 then B.col ⟨i, h⟩ else 0
  have hX : ∀ i (h : i < n + 1), X i = B.row ⟨i, h⟩ := fun i h => dite_eq_left_of_eq_true (eq_true h)
  have hY : ∀ i (h : i < n + 1), Y i = B.col ⟨i, h⟩ := fun i h => dite_eq_left_of_eq_true (eq_true h)
  have hXa : ∀ i j, i < j → j ≤ n → X j < X i := fun i j hij hj => by
    rw [hX i (by omega), hX j (by omega)]
    exact B.row_strictAnti (show (⟨i, by omega⟩ : Fin (n + 1)) < ⟨j, by omega⟩ from hij)
  have hYa : ∀ i j, i < j → j ≤ n → Y j < Y i := fun i j hij hj => by
    rw [hY i (by omega), hY j (by omega)]
    exact B.col_strictAnti (show (⟨i, by omega⟩ : Fin (n + 1)) < ⟨j, by omega⟩ from hij)
  have hYX : ∀ i, i ≤ n → Y i < X i := fun i hi => by
    rw [hX i (by omega), hY i (by omega)]; exact B.row_nonempty _
  have hcon : ∀ i, i + 1 ≤ n → Y i ≤ X (i + 1) := fun i hi => by
    rw [hX (i + 1) (by omega), hY i (by omega)]
    exact hBc.2 ⟨i, by omega⟩ (by simp only; omega)
  have hYn : Y n = 0 := by
    rw [hY n (by omega)]; exact hB
  have hXY : ∀ i j, i ≤ n → j ≤ n → X i ≠ Y j := fun i j hi hj => by
    rw [hX i (by omega), hY j (by omega)]; exact hBz _ _
  have hbX : ∀ i, i ≤ n → X i ≠ b := fun i hi => by
    rw [hX i (by omega)]; exact hbr _
  have hbY : ∀ j, j ≤ n → Y j ≠ b := fun j hj => by
    rw [hY j (by omega)]; exact hbc _
  have hX0 : b < X 0 := by
    rw [hX 0 (by omega)]
    have := hbL; unfold BetaDiagram.largestLabel at this
    have h0 : B.col (Fin.last n) = 0 := hB
    rw [h0, sub_zero] at this; exact this
  -- the rows above `b`: indices `0 … p₀`
  have hp0 : ∃ i, i ≤ n ∧ b < X i := ⟨0, by omega, hX0⟩
  set p₀ := Nat.findGreatest (fun i => b < X i) n with hp₀
  have hp₀spec : b < X p₀ := Nat.findGreatest_spec (P := fun i => b < X i) (Nat.zero_le n) hX0
  have hp₀n : p₀ ≤ n := Nat.findGreatest_le n
  have hp₀gt : ∀ i, p₀ < i → i ≤ n → X i < b := fun i hi hin => by
    have h1 := Nat.findGreatest_is_greatest (P := fun i => b < X i) hi hin
    have h2 := hbX i hin
    omega
  have hXabove : ∀ i, i ≤ p₀ → b < X i := fun i hi => by
    rcases Nat.eq_or_lt_of_le hi with h | h
    · rw [h]; exact hp₀spec
    · have := hXa i p₀ h hp₀n; omega
  -- the columns above `b`: indices `0 … w - 1`
  have hw : ∃ j, Y j < b := ⟨n, by rw [hYn]; omega⟩
  set w := Nat.find hw with hwdef
  have hwspec : Y w < b := Nat.find_spec hw
  have hwn : w ≤ n := Nat.find_min' hw (show Y n < b by rw [hYn]; omega)
  have hwlt : ∀ j, j < w → b < Y j := fun j hj => by
    have h1 := Nat.find_min hw hj
    have h2 := hbY j (by omega)
    omega
  have hwp : w ≤ p₀ := by
    rcases Nat.eq_zero_or_pos w with h0 | hpos
    · omega
    · have h1 := hwlt (w - 1) (by omega)
      have h2 := hcon (w - 1) (by omega)
      have h3 : b < X w := by
        have : w - 1 + 1 = w := by omega
        rw [this] at h2; omega
      by_contra hcon'
      have := hp₀gt w (by omega) hwn
      omega
  rcases Nat.eq_or_lt_of_le hwp with hwe | hwlt'
  · -- gap case
    left
    refine ⟨p₀, b, hp₀n, hρb, hle, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have := hXabove i.val hi
      rwa [hX i.val (by omega)] at this
    · intro i hi
      have := hp₀gt i.val hi (by omega)
      rwa [hX i.val (by omega)] at this
    · intro j hj
      have := hwlt j.val (by omega)
      rwa [hY j.val (by omega)] at this
    · rintro ⟨jv, hjv⟩ hj
      have h1 : Y jv ≤ Y w := by
        rcases Nat.eq_or_lt_of_le (show w ≤ jv by have hj' : p₀ ≤ jv := hj; omega) with h | h
        · rw [← h]
        · exact (hYa w jv h (by omega)).le
      have := hwspec
      rw [hY jv hjv] at h1
      rw [hY w (by omega)] at this h1
      exact lt_of_le_of_lt h1 this
    · intro hp
      change 0 < p₀ → _
      intro hpos
      have h1 := hp₀gt (p₀ + 1) (by omega) hp
      have h2 := hwlt (p₀ - 1) (by omega)
      rw [hX (p₀ + 1) (by omega)] at h1
      rw [hY (p₀ - 1) (by omega)] at h2
      exact lt_trans h1 h2
  · -- block case
    right
    have hwn' : w + 1 ≤ n := by omega
    -- the start `p` of the block containing index `w`
    set p := Nat.findGreatest (fun k => k = 0 ∨ X (k + 1) < Y (k - 1)) w with hpdef
    have hpw : p ≤ w := Nat.findGreatest_le w
    have hpspec : p = 0 ∨ X (p + 1) < Y (p - 1) :=
      Nat.findGreatest_spec (P := fun k => k = 0 ∨ X (k + 1) < Y (k - 1)) (Nat.zero_le w)
        (Or.inl rfl)
    have hpmax : ∀ k, p < k → k ≤ w → Y (k - 1) ≤ X (k + 1) := fun k hk hkw => by
      have h1 := Nat.findGreatest_is_greatest (P := fun k => k = 0 ∨ X (k + 1) < Y (k - 1)) hk hkw
      have h2 := hXY (k + 1) (k - 1) (by omega) (by omega)
      simp only [not_or] at h1
      omega
    -- the end `q` of that block
    have hq : ∃ q, w ≤ q ∧ (q = n - 1 ∨ X (q + 2) < Y q) := ⟨n - 1, by omega, Or.inl rfl⟩
    set q := Nat.find hq with hqdef
    have hqspec := Nat.find_spec hq
    have hqle : q ≤ n - 1 := Nat.find_min' hq ⟨by omega, Or.inl rfl⟩
    have hqw : w ≤ q := hqspec.1
    have hqmin : ∀ k, w ≤ k → k < q → Y k ≤ X (k + 2) := fun k hwk hkq => by
      have h1 := Nat.find_min hq hkq
      have h2 := hXY (k + 2) k (by omega) (by omega)
      simp only [not_and, not_or] at h1
      have := (h1 hwk).2
      omega
    have hpe : p + (q - p) + 1 ≤ n := by omega
    have hcut : PrefixCut B p (by omega) := by
      intro hpos
      rcases hpspec with h | h
      · omega
      · rw [hX (p + 1) (by omega)] at h
        rw [hY (p - 1) (by omega)] at h
        exact h
    have hin : BlockInside B p (q - p) hpe := by
      intro i hi
      have hk : Y (p + i) ≤ X (p + i + 2) := by
        by_cases hlt : p + i < w
        · have := hpmax (p + i + 1) (by omega) (by omega)
          simpa using this
        · exact hqmin (p + i) (by omega) (by omega)
      rw [hY (p + i) (by omega), hX (p + i + 2) (by omega)] at hk
      exact hk
    refine ⟨p, q - p, hpe, hcut, hin, ?_, ?_, ?_⟩
    · have hhead : b < blockHead B hpe := by
        unfold blockHead
        have := hXabove (p + 1) (by omega)
        rwa [hX (p + 1) (by omega)] at this
      have hleast : blockLeast B hpe < b := by
        unfold blockLeast
        have h1 : Y q ≤ Y w := by
          rcases Nat.eq_or_lt_of_le hqw with h | h
          · rw [← h]
          · exact (hYa w q h (by omega)).le
        rw [hY q (by omega)] at h1
        rw [hY w (by omega)] at hwspec h1
        have e1 : p + (q - p) = q := by omega
        simp only [e1]
        omega
      intro h0
      have hmem : b - blockLeast B hpe ∈
          (restrictBlock ρ (blockLeast B hpe) (blockHead B hpe)).support := by
        unfold restrictBlock
        have hinj : Function.Injective (fun x : ℤ => x - blockLeast B hpe) :=
          fun x y h => by simpa using h
        rw [Finsupp.mem_support_iff]
        have := Finsupp.mapDomain_apply_of_injective hinj
          (ρ.filter fun x => blockLeast B hpe < x ∧ x < blockHead B hpe) b
        rw [this, Finsupp.filter_apply, if_pos (And.intro hleast hhead)]
        exact hρb
      rw [h0] at hmem
      simp at hmem
    · intro x hx
      have := hle x hx
      have hhead : b < B.row ⟨p + 1, by omega⟩ := by
        have := hXabove (p + 1) (by omega)
        rwa [hX (p + 1) (by omega)] at this
      unfold blockHead
      omega
    · intro hq'
      have e1 : p + (q - p) = q := by omega
      have h2 : X (q + 2) < Y q := by
        rcases hqspec.2 with h | h
        · omega
        · exact h
      rw [hX (q + 2) (by omega), hY q (by omega)] at h2
      simp only [e1]
      exact h2

end SkewCoframeRigidity.UnitRestoration
