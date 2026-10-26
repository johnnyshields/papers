import SkewGluing.FoldSupplied.MixedWindow

/-!
# The exceptional bits of a case-(d) inner

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:mixed-fold`): the first window and the position of the two projected contacts.

With `P j = mnA (j g + t mod g)` and `Q j = mnA (j g + s mod g)` the bits of the two exceptional
classes in block `j`, the first window forces `P 0 = Q 0 = 1`, every block differs from the first
only in these two bits (`MixCtx.sg_block`), and the upper copy changes the partial sums by the two
phases (`MixCtx.sg_upper`).  Writing `v = d g + a`, the heights at the private diagonal `v` and
the positivity of the first window at `a` place both projected contacts in `[0, a]`
(`MixCtx.contacts`), force the exceptional bits of block `d`, and give the heights one at `a`
and at the last complete block (`MixCtx.exc_facts`).

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

variable {A B : ℤ → ℤ} {r v s t g : ℕ}

namespace MixCtx

theorem Sg_pos (h : MixCtx A B r v s t g) {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ r + v) :
    1 ≤ Sg A B n := by
  have := h.w.pos (n - 1) (by omega)
  rw [mixFold_ht_eq_Sg] at this
  rw [show n - 1 + 1 = n by omega] at this
  omega

theorem Sg_end (h : MixCtx A B r v s t g) : Sg A B (r + v) = 1 := by
  have := h.w.last
  rw [mixFold_ht_eq_Sg] at this
  rwa [show r + v - 1 + 1 = r + v by have := h.w.v_pos; omega] at this

theorem first (h : MixCtx A B r v s t g) :
    mnA A (t % g) = 1 ∧ mnA A (s % g) = 1 ∧ Sg A B g = 1 := by
  have hg := h.g_pos
  have ht := Nat.mod_lt t hg
  have hs := Nat.mod_lt s hg
  have hgN : g ≤ r + v := by have := h.glt; omega
  obtain ⟨hne, hw⟩ := h.win
  have e := hw 0 (t % g) (s % g) (by omega) (by omega) (by omega) (by simp) (by omega) (by omega)
    (by simp)
  simp only [zero_add] at e
  have e2 : Sg A B g = ∑ i ∈ Finset.range g, mEps A B i := rfl
  have p := h.Sg_pos (n := g) (by omega) hgN
  have b1 := h.mnA_bit (k := t % g) (by omega)
  have b2 := h.mnA_bit (k := s % g) (by omega)
  rw [e2, e] at p
  refine ⟨by omega, by omega, ?_⟩
  rw [e2, e]
  omega

theorem eps_block (h : MixCtx A B r v s t g) {j i : ℕ} (hi : i < g) (hji : j * g + i < r + v) :
    mEps A B (j * g + i) = mEps A B i + (if i = t % g then mnA A (j * g + t % g) - 1 else 0) +
      (if i = s % g then mnA A (j * g + s % g) - 1 else 0) := by
  have hg := h.g_pos
  obtain ⟨hne, -⟩ := h.win
  obtain ⟨f1, f2, -⟩ := h.first
  have hi' : i < r + v := by have := h.glt; omega
  have hmod : (j * g + i) % g = i := mod_blk hi
  have hB : mnB B (j * g + i) = mnB B i := by
    rw [h.mnB_mod hji, hmod, h.mnB_mod hi', Nat.mod_eq_of_lt hi]
  unfold mEps
  rw [hB]
  by_cases h1 : i = t % g
  · have h2 : i ≠ s % g := fun e => hne (h1.symm.trans e)
    rw [if_pos h1, if_neg h2]
    subst h1
    rw [f1]
    ring
  · by_cases h2 : i = s % g
    · rw [if_neg h1, if_pos h2]
      subst h2
      rw [f2]
      ring
    · rw [if_neg h1, if_neg h2]
      have e1 := h.mnA_mod hji (by rw [hmod]; exact h1) (by rw [hmod]; exact h2)
      have e2 := h.mnA_mod hi' (by rw [Nat.mod_eq_of_lt hi]; exact h1)
        (by rw [Nat.mod_eq_of_lt hi]; exact h2)
      rw [e1, hmod, ← Nat.mod_eq_of_lt hi, ← e2]
      ring

theorem sg_block (h : MixCtx A B r v s t g) {j z : ℕ} (hz : z < g) (hjz : j * g + z < r + v) :
    Sg A B (j * g + z + 1) = Sg A B (j * g) + Sg A B (z + 1) +
      (if t % g ≤ z then mnA A (j * g + t % g) - 1 else 0) +
      (if s % g ≤ z then mnA A (j * g + s % g) - 1 else 0) := by
  have e : j * g + z + 1 = j * g + (z + 1) := by ring
  rw [e, Sg_add]
  have e3 : ∑ i ∈ Finset.range (z + 1), mEps A B (j * g + i) =
      ∑ i ∈ Finset.range (z + 1), (mEps A B i + (if i = t % g then mnA A (j * g + t % g) - 1 else 0)
        + (if i = s % g then mnA A (j * g + s % g) - 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.mp hi
    exact h.eps_block (by omega) (by omega)
  rw [e3, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e4 : Sg A B (z + 1) = ∑ i ∈ Finset.range (z + 1), mEps A B i := rfl
  rw [e4]
  simp only [Finset.sum_ite_eq', Finset.mem_range]
  have a1 : (t % g < z + 1) ↔ t % g ≤ z := by omega
  have a2 : (s % g < z + 1) ↔ s % g ≤ z := by omega
  simp only [a1, a2]
  ring

theorem sg_upper (h : MixCtx A B r v s t g) {n : ℕ} (hn : n ≤ v) :
    Sg A B (r + n) = 1 + Sg A B n - (if s < n then 1 else 0) - (if t < n then 1 else 0) := by
  induction n with
  | zero => simp [h.Sg_r, Sg_zero]
  | succ n ih =>
    have ih := ih (by omega)
    rw [← add_assoc, Sg_succ, ih, Sg_succ]
    have e : mEps A B (r + n) = mEps A B n - (if n = s then 1 else 0) - (if n = t then 1 else 0) := by
      unfold mEps
      rw [h.mnA_upper (by omega), h.mnB_upper (by omega)]
      ring
    rw [e]
    split_ifs <;> omega

end MixCtx

end FoldSupplied
end SkewGluing
