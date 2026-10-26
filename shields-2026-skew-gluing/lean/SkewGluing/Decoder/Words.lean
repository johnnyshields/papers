import SkewGluing.Coding
import SkewGluing.OrdinaryFold.Antitranspose
import SkewGluing.Lines.WordFacts

/-!
# Closed boundary words of a connected diagram

Formalizes `shields-2026-skew-gluing.tex`, «Reconstructing a chart from its two words»
(the full row and column flag sets `X_P`, `Y_P` and the height `h_P`).

The closed membership words of a connected diagram `P` of span `N` are `X_P(k) = 1_{k ∈ X_P}` and
`Y_P(k) = 1_{k ∈ Y_P}` for `0 ≤ k ≤ N`: on the interior positions they are the boundary words
`B_k` and `A_k`, and the four caps `X_P(0) = 0`, `Y_P(0) = 1`, `X_P(N) = 1`, `Y_P(N) = 0` are added
separately.  `hwd P k = ∑_{i ≤ k} (Y_P(i) - X_P(i))` is the height `h_P(k)`; it equals the height of
the diagonal of content `c₀ + k` for `0 ≤ k < N` and vanishes at `k = N`.  Antitransposition
exchanges the two words, `Y_{AT P} = 1 - X_P` and `X_{AT P} = 1 - Y_P`, and fixes `hwd`.

Sorry-free.
-/

namespace SkewGluing

/-- The closed row-membership word `X_P(k)`: the caps `X_P(0) = 0`, `X_P(N) = 1`, and `B_k`
between them. -/
def Xw (P : Diagram) (k : ℤ) : ℤ :=
  if k = 0 then 0 else if k = (span P : ℤ) then 1 else wordB P k

/-- The closed column-membership word `Y_P(k)`: the caps `Y_P(0) = 1`, `Y_P(N) = 0`, and `A_k`
between them. -/
def Yw (P : Diagram) (k : ℤ) : ℤ :=
  if k = 0 then 1 else if k = (span P : ℤ) then 0 else wordA P k

/-- The height `h_P(k) = ∑_{i ≤ k} (Y_P(i) - X_P(i))`. -/
def hwd (P : Diagram) (k : ℤ) : ℤ := ∑ i ∈ Finset.Icc (0 : ℤ) k, (Yw P i - Xw P i)

theorem span_pos {P : Diagram} (hP : IsConnectedSkew P) : 1 ≤ (span P : ℤ) := by
  have := span_eq_of_isConnectedSkew hP
  have h3 : minContent P ≤ maxContent P := minContent_le (maxContent_mem hP.2.1)
  omega

theorem Xw_of_mem {P : Diagram} {k : ℤ} (h1 : 1 ≤ k) (h2 : k < (span P : ℤ)) :
    Xw P k = wordB P k := by
  unfold Xw
  simp only [show k ≠ 0 by omega, show k ≠ (span P : ℤ) by omega, ite_false]

theorem Yw_of_mem {P : Diagram} {k : ℤ} (h1 : 1 ≤ k) (h2 : k < (span P : ℤ)) :
    Yw P k = wordA P k := by
  unfold Yw
  simp only [show k ≠ 0 by omega, show k ≠ (span P : ℤ) by omega, ite_false]

theorem Xw_zero (P : Diagram) : Xw P 0 = 0 := by simp [Xw]

theorem Yw_zero (P : Diagram) : Yw P 0 = 1 := by simp [Yw]

theorem Xw_span {P : Diagram} (h : 1 ≤ (span P : ℤ)) : Xw P (span P : ℤ) = 1 := by
  unfold Xw
  simp only [show (span P : ℤ) ≠ 0 by omega, ite_false, ite_true]

theorem Yw_span {P : Diagram} (h : 1 ≤ (span P : ℤ)) : Yw P (span P : ℤ) = 0 := by
  unfold Yw
  simp only [show (span P : ℤ) ≠ 0 by omega, ite_false, ite_true]

/-- The closed words of a connected diagram take values in `{0, 1}`. -/
theorem Xw_bit {P : Diagram} (hP : IsConnectedSkew P) {k : ℤ} (h1 : 0 ≤ k)
    (h2 : k ≤ (span P : ℤ)) : Xw P k = 0 ∨ Xw P k = 1 := by
  have hsp := span_pos hP
  by_cases hk0 : k = 0
  · left; subst hk0; exact Xw_zero P
  · by_cases hk : k = (span P : ℤ)
    · right; subst hk; exact Xw_span hsp
    · rw [Xw_of_mem (by omega) (by omega)]
      exact Lines.wordB_bit hP (by omega) (by omega)

theorem Yw_bit {P : Diagram} (hP : IsConnectedSkew P) {k : ℤ} (h1 : 0 ≤ k)
    (h2 : k ≤ (span P : ℤ)) : Yw P k = 0 ∨ Yw P k = 1 := by
  have hsp := span_pos hP
  by_cases hk0 : k = 0
  · right; subst hk0; exact Yw_zero P
  · by_cases hk : k = (span P : ℤ)
    · left; subst hk; exact Yw_span hsp
    · rw [Yw_of_mem (by omega) (by omega)]
      exact Lines.wordA_bit hP (by omega) (by omega)

theorem hwd_zero (P : Diagram) : hwd P 0 = 1 := by
  simp [hwd, Yw_zero, Xw_zero]

theorem hwd_succ (P : Diagram) {k : ℤ} (hk : 0 ≤ k) :
    hwd P (k + 1) = hwd P k + (Yw P (k + 1) - Xw P (k + 1)) := by
  unfold hwd
  have e : Finset.Icc (0 : ℤ) (k + 1) = insert (k + 1) (Finset.Icc (0 : ℤ) k) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [e, Finset.sum_insert (by simp)]
  ring

/-- The height `h_P(k)` is the height of the diagonal of content `c₀ + k`, for `0 ≤ k < N`. -/
theorem hwd_eq_height {P : Diagram} (hP : IsConnectedSkew P) {k : ℤ} (h1 : 0 ≤ k)
    (h2 : k < (span P : ℤ)) : hwd P k = height P (minContent P + k) := by
  have hc : ∀ {j : ℤ}, j ∈ contents P ↔ minContent P ≤ j ∧ j ≤ maxContent P :=
    fun {j} => (isConnectedSkew_iff_diagonal.mp hP).mem_contents_iff (k := j)
  have hsp := span_eq_of_isConnectedSkew hP
  have hs0 : diagLo P (minContent P) = diagHi P (minContent P) :=
    (isConnectedSkew_iff_diagonal.mp hP).2.2.2.2 _ (minContent_mem hP.2.1)
      (Or.inl (fun hm => by have := minContent_le hm; omega))
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h1
  induction n with
  | zero =>
    rw [Nat.cast_zero, hwd_zero]
    simp only [add_zero, height]
    omega
  | succ n ih =>
    have e : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, hwd_succ P (by omega), ih (by omega) (by omega)]
    rw [Yw_of_mem (by omega) (by omega), Xw_of_mem (by omega) (by omega)]
    unfold wordA wordB bitA bitB height
    have e2 : minContent P + ((n : ℤ) + 1) - 1 = minContent P + n := by ring
    have e3 : minContent P + ((n : ℤ) + 1) = minContent P + n + 1 := by ring
    rw [e2, e3]
    omega

theorem hwd_span {P : Diagram} (hP : IsConnectedSkew P) : hwd P (span P : ℤ) = 0 := by
  have hsp := span_pos hP
  have hm := span_eq_of_isConnectedSkew hP
  have h1 : hwd P ((span P : ℤ) - 1) = 1 := by
    rw [hwd_eq_height hP (by omega) (by omega)]
    have := (isConnectedSkew_iff_diagonal.mp hP).2.2.2.2 _ (maxContent_mem hP.2.1)
      (Or.inr (fun hm' => by have := le_maxContent hm'; omega))
    unfold height
    have e : minContent P + ((span P : ℤ) - 1) = maxContent P := by omega
    rw [e]
    omega
  have := hwd_succ P (k := (span P : ℤ) - 1) (by omega)
  rw [show (span P : ℤ) - 1 + 1 = span P by ring, Yw_span hsp, Xw_span hsp, h1] at this
  omega

/-! ### Antitransposition -/

theorem span_antitranspose' (P : Diagram) : span (antitranspose P) = span P := span_antitranspose

theorem Xw_antitranspose {P : Diagram} (hP : IsConnectedSkew P) {k : ℤ} (h1 : 0 ≤ k)
    (h2 : k ≤ (span P : ℤ)) : Xw (antitranspose P) k = 1 - Yw P k := by
  have hsp := span_pos hP
  have hs : span (antitranspose P) = span P := span_antitranspose
  by_cases hk0 : k = 0
  · subst hk0; simp [Xw_zero, Yw_zero]
  · by_cases hk : k = (span P : ℤ)
    · subst hk
      have := Xw_span (P := antitranspose P) (by rw [hs]; exact hsp)
      rw [hs] at this
      rw [this, Yw_span hsp]
      norm_num
    · have h3 : k < (span (antitranspose P) : ℤ) := by rw [span_antitranspose]; omega
      rw [Xw_of_mem (by omega) h3, Yw_of_mem (by omega) (by omega)]
      have := ordFold_wordB_antitranspose hP (k := k) (by omega) (by omega)
      omega

theorem Yw_antitranspose {P : Diagram} (hP : IsConnectedSkew P) {k : ℤ} (h1 : 0 ≤ k)
    (h2 : k ≤ (span P : ℤ)) : Yw (antitranspose P) k = 1 - Xw P k := by
  have hsp := span_pos hP
  have hs : span (antitranspose P) = span P := span_antitranspose
  by_cases hk0 : k = 0
  · subst hk0; simp [Xw_zero, Yw_zero]
  · by_cases hk : k = (span P : ℤ)
    · subst hk
      have := Yw_span (P := antitranspose P) (by rw [hs]; exact hsp)
      rw [hs] at this
      rw [this, Xw_span hsp]
      norm_num
    · have h3 : k < (span (antitranspose P) : ℤ) := by rw [span_antitranspose]; omega
      rw [Yw_of_mem (by omega) h3, Xw_of_mem (by omega) (by omega)]
      have := ordFold_wordA_antitranspose hP (k := k) (by omega) (by omega)
      omega

theorem hwd_antitranspose {P : Diagram} (hP : IsConnectedSkew P) {k : ℤ} (_h1 : 0 ≤ k)
    (_h2 : k ≤ (span P : ℤ)) : hwd (antitranspose P) k = hwd P k := by
  unfold hwd
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [Yw_antitranspose hP hi.1 (by omega), Xw_antitranspose hP hi.1 (by omega)]
  ring

end SkewGluing
