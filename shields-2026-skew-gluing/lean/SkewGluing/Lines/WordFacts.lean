import SkewGluing.Coding
import SkewGluing.CommonFactorGraph

/-!
# Boundary words of a connected skew diagram

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`eq:gluing-bits`).

Facts about `wordA`, `wordB` used in the proof of `lem:gluing-lines`: translation invariance on the
positions `1, …, N - 1`, bits in `{0, 1}`, and the telescoping of the prefix sums, which give
`A_1 + ⋯ + A_n - B_1 - ⋯ - B_n = h_n - ℓ_n + 1 - 1` (the height of the diagonal `n` minus one),
so that the sums over `[1, n]` agree exactly when the diagonal `n` is a singleton.

Sorry-free.
-/

namespace SkewGluing

namespace Lines

variable {X : Diagram}

theorem wordA_normalize (hX : IsConnectedSkew X) {k : ℤ} (h1 : 1 ≤ k) (h2 : k < span X) :
    wordA (normalize X) k = wordA X k := by
  have hbd := isBitData_of_isConnectedSkew hX
  have e := normalize_eq_fromBits hX
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
  have := bitA_fromBits hbd (k := n) (by omega) (by omega)
  unfold wordA
  rw [e]
  simpa [wordA] using this

theorem wordB_normalize (hX : IsConnectedSkew X) {k : ℤ} (h1 : 1 ≤ k) (h2 : k < span X) :
    wordB (normalize X) k = wordB X k := by
  have hbd := isBitData_of_isConnectedSkew hX
  have e := normalize_eq_fromBits hX
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
  have := bitB_fromBits hbd (k := n) (by omega) (by omega)
  unfold wordB
  rw [e]
  simpa [wordB] using this

/-- The bits of a connected skew diagram lie in `{0, 1}`. -/
theorem wordA_bit (hX : IsConnectedSkew X) {k : ℤ} (h1 : 1 ≤ k) (h2 : k < span X) :
    wordA X k = 0 ∨ wordA X k = 1 := by
  have := (isBitData_of_isConnectedSkew hX).2.1
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
  exact (this n (by omega) (by omega)).1

theorem wordB_bit (hX : IsConnectedSkew X) {k : ℤ} (h1 : 1 ≤ k) (h2 : k < span X) :
    wordB X k = 0 ∨ wordB X k = 1 := by
  have := (isBitData_of_isConnectedSkew hX).2.1
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
  exact (this n (by omega) (by omega)).2

/-- The first row of the diagonal `n` is the first row of the diagonal `0` minus `A_1 + ⋯ + A_n`. -/
theorem sum_wordA (X : Diagram) (n : ℕ) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, wordA X k =
      diagLo X (minContent X) - diagLo X (minContent X + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : Finset.Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) =
        insert ((n : ℤ) + 1) (Finset.Icc (1 : ℤ) (n : ℤ)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [e, Finset.sum_insert (by simp), ih]
    unfold wordA bitA
    push_cast
    have e2 : minContent X + ((n : ℤ) + 1) - 1 = minContent X + n := by ring
    rw [e2]
    ring

theorem sum_wordB (X : Diagram) (n : ℕ) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, wordB X k =
      diagHi X (minContent X) - diagHi X (minContent X + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : Finset.Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) =
        insert ((n : ℤ) + 1) (Finset.Icc (1 : ℤ) (n : ℤ)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [e, Finset.sum_insert (by simp), ih]
    unfold wordB bitB
    push_cast
    have e2 : minContent X + ((n : ℤ) + 1) - 1 = minContent X + n := by ring
    rw [e2]
    ring

/-- The sums of the two words over `[1, n]` agree exactly when the diagonal `n` is a singleton. -/
theorem sum_wordA_eq_sum_wordB_iff (hX : IsConnectedSkew X) (n : ℕ) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, wordA X k = ∑ k ∈ Finset.Icc (1 : ℤ) n, wordB X k ↔
      diagLo X (minContent X + n) = diagHi X (minContent X + n) := by
  have h' := isConnectedSkew_iff_diagonal.mp hX
  have sing : diagLo X (minContent X) = diagHi X (minContent X) :=
    h'.2.2.2.2 _ (minContent_mem h'.1) (Or.inl (fun hm => by have := minContent_le hm; omega))
  rw [sum_wordA, sum_wordB]
  omega

/-- The two words have the same sum over all positions `1, …, N - 1`. -/
theorem sum_wordA_eq_sum_wordB (hX : IsConnectedSkew X) :
    ∑ k ∈ Finset.Icc (1 : ℤ) ((span X : ℤ) - 1), wordA X k =
      ∑ k ∈ Finset.Icc (1 : ℤ) ((span X : ℤ) - 1), wordB X k := by
  have h' := isConnectedSkew_iff_diagonal.mp hX
  have hsp := span_eq_of_isConnectedSkew hX
  have hspan : 1 ≤ span X := by
    have := minContent_le (maxContent_mem h'.1)
    omega
  have e : (((span X - 1 : ℕ)) : ℤ) = (span X : ℤ) - 1 := by omega
  rw [← e]
  rw [sum_wordA_eq_sum_wordB_iff hX]
  have e2 : minContent X + (((span X - 1 : ℕ)) : ℤ) = maxContent X := by omega
  rw [e2]
  exact h'.2.2.2.2 _ (maxContent_mem h'.1) (Or.inr (fun hm => by have := le_maxContent hm; omega))

end Lines

end SkewGluing
