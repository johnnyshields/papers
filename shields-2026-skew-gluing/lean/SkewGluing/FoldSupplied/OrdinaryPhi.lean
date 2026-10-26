import SkewGluing.FoldSupplied.OrdinaryEmpty

/-!
# Native heights of an ordinary inner

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`): the heights of the inner read through the completed native
words.

With `f i = natC A i - natB B s i` and `Φ m = f 0 + ⋯ + f m`, the height of the inner is
`H_m = Φ m + [s ≤ m]` on the contents `m < r` (`OrdWords.height_native`: `Φ` is the height of
the lower mark) and `H_{r+z} = 1 + Φ z - [t ≤ z]` on the contents of the upper band
(`OrdWords.height_second`).  The positivity and singleton constraints of the inner become
`OrdWords.phi_constraints`.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open OrdinaryDrift

variable {A B : ℕ → ℤ} {r v s t : ℕ}

/-- The native increment at position `i`. -/
def fN (A B : ℕ → ℤ) (s i : ℕ) : ℤ := natC A i - natB B s i

/-- The native height `Φ m`: the sum of the increments at the positions `0, …, m`. -/
def Phi (A B : ℕ → ℤ) (s m : ℕ) : ℤ := ∑ i ∈ Finset.range (m + 1), fN A B s i

theorem Phi_succ (A B : ℕ → ℤ) (s m : ℕ) : Phi A B s (m + 1) = Phi A B s m + fN A B s (m + 1) := by
  unfold Phi
  rw [Finset.sum_range_succ]

theorem Phi_zero (A B : ℕ → ℤ) (s : ℕ) : Phi A B s 0 = 1 := by
  simp [Phi, fN, natC, natB]

theorem OrdWords.A_native (h : OrdWords A B r v s t) {i : ℕ} (h1 : 1 ≤ i) : natC A i = A i := by
  unfold natC; simp only [show i ≠ 0 by omega, if_false]

theorem OrdWords.B_native (h : OrdWords A B r v s t) {i : ℕ} (h1 : 1 ≤ i) :
    natB B s i = B i + (if i = s then 1 else 0) := by
  unfold natB
  simp only [show i ≠ 0 by omega, if_false]
  by_cases hi : i = s
  · subst hi; simp [h.capB]
  · simp [hi]

/-- The height of the inner on the contents below the period. -/
theorem OrdWords.height_native (h : OrdWords A B r v s t) {m : ℕ} (hm : m < r) :
    heightWord A B m = Phi A B s m + (if s ≤ m then 1 else 0) := by
  induction m with
  | zero =>
    have := h.s_pos
    simp [Phi_zero, heightWord]; omega
  | succ m ih =>
    rw [heightWord_succ, ih (by omega), Phi_succ]
    have e1 := h.A_native (i := m + 1) (by omega)
    have e2 := h.B_native (i := m + 1) (by omega)
    unfold fN
    rw [e1, e2]
    split_ifs <;> omega

/-- The height of the inner on the upper band. -/
theorem OrdWords.height_second (h : OrdWords A B r v s t) {z : ℕ} (hz : z < v) :
    heightWord A B (r + z) = 1 + Phi A B s z - (if t ≤ z then 1 else 0) := by
  have hvr := h.v_lt
  induction z with
  | zero =>
    have e : r + 0 = (r - 1) + 1 := by omega
    rw [e, heightWord_succ, h.sing_r]
    have e2 : r - 1 + 1 = r := by omega
    rw [e2, h.A_r, h.B_r, Phi_zero]
    by_cases ht : 1 ≤ t
    · have : ¬ t ≤ 0 := by omega
      simp [ht, this]
    · have : t ≤ 0 := by omega
      simp [ht, this]
  | succ z ih =>
    rw [← add_assoc, heightWord_succ, ih (by omega), Phi_succ]
    have c1 := h.copyA (z + 1) (by omega) hz
    have c2 := h.copyB (z + 1) (by omega) hz
    rw [show r + z + 1 = r + (z + 1) by ring, c1, c2]
    have e1 := h.A_native (i := z + 1) (by omega)
    have e2 := h.B_native (i := z + 1) (by omega)
    unfold fN
    rw [e1, e2]
    split_ifs <;> omega

/-- **The constraints on `Φ`** from the positivity and the singleton diagonals of the inner. -/
theorem OrdWords.phi_constraints (h : OrdWords A B r v s t) :
    Phi A B s 0 = 1 ∧ (∀ z, z < v → 1 ≤ Phi A B s z) ∧ Phi A B s v = 0 ∧
    (∀ m, v ≤ m → m < r → 0 ≤ Phi A B s m) ∧ Phi A B s (r - 1) = 0 ∧ Phi A B s (v - 1) = 1 := by
  have hvr := h.v_lt
  have hv1 := h.v_pos
  have hs1 := h.s_pos
  have hs2 := h.s_le
  have ht := h.t_lt
  refine ⟨Phi_zero A B s, fun z hz => ?_, ?_, fun m hm1 hm2 => ?_, ?_, ?_⟩
  · have := h.mpos z hz
    rw [h.height_native (by omega)] at this
    split_ifs at this <;> omega
  · have := h.sing_v
    rw [h.height_native hvr] at this
    simp only [hs2, if_true] at this
    omega
  · have := h.words.pos m (by omega)
    rw [h.height_native hm2] at this
    have h2 : s ≤ m := by omega
    simp only [h2, if_true] at this
    omega
  · have := h.sing_r
    rw [h.height_native (by omega)] at this
    have h2 : s ≤ r - 1 := by omega
    simp only [h2, if_true] at this
    omega
  · have := h.words.last
    have e : r + v - 1 = r + (v - 1) := by omega
    rw [e, h.height_second (by omega)] at this
    have h2 : t ≤ v - 1 := by omega
    simp only [h2, if_true] at this
    omega

end FoldSupplied
end SkewGluing
