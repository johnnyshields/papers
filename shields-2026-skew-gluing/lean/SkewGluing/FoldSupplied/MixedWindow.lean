import SkewGluing.FoldSupplied.MixedPeriod

/-!
# Window sums of the boundary words of a case-(d) inner

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:mixed-fold`): the rank identity that the two exceptional residue classes of the
completed column word carry total occupancy one more than the number of blocks, and the window
identity it gives.

With `Sg A B n` the sum of the first `n` increments, the sum over any window of `g` consecutive
increments is `mnA y₁ + mnA y₂ - 1`, where `y₁, y₂` are the positions of the window in the two
exceptional residue classes `t mod g` and `s mod g` (`MixCtx.win_one`); the two classes are
distinct (`MixCtx.classes_ne`).  The rank identity `|B| = |C|` of the paper is the case of the
complete first `r` increments.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

/-- The sum of the first `n` increments of the completed words. -/
def Sg (A B : ℤ → ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, mEps A B i

theorem Sg_zero (A B : ℤ → ℤ) : Sg A B 0 = 0 := by simp [Sg]

theorem mixFold_ht_eq_Sg (A B : ℤ → ℤ) (n : ℕ) : mixFold_ht A B n = Sg A B (n + 1) :=
  mixFold_ht_eq_sum A B n

theorem Sg_add (A B : ℤ → ℤ) (n k : ℕ) :
    Sg A B (n + k) = Sg A B n + ∑ i ∈ Finset.range k, mEps A B (n + i) :=
  Finset.sum_range_add _ _ _

theorem Sg_succ (A B : ℤ → ℤ) (n : ℕ) : Sg A B (n + 1) = Sg A B n + mEps A B n := by
  simp [Sg, Finset.sum_range_succ]

theorem mod_blk {j e g : ℕ} (he : e < g) : (j * g + e) % g = e := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt he

theorem sum_bits_bounds {f : ℕ → ℤ} {m : ℕ} (hb : ∀ i < m, f i = 0 ∨ f i = 1) {i0 : ℕ}
    (hi0 : i0 < m) (h1 : f i0 = 1) :
    1 ≤ ∑ i ∈ Finset.range m, f i ∧ ∑ i ∈ Finset.range m, f i ≤ m := by
  constructor
  · have := Finset.single_le_sum (f := f) (s := Finset.range m)
      (fun i hi => by have := hb i (Finset.mem_range.mp hi); omega) (Finset.mem_range.mpr hi0)
    omega
  · calc ∑ i ∈ Finset.range m, f i ≤ ∑ _i ∈ Finset.range m, (1 : ℤ) :=
          Finset.sum_le_sum (fun i hi => by have := hb i (Finset.mem_range.mp hi); omega)
      _ = m := by simp

theorem sum_bits_two {f : ℕ → ℤ} {m : ℕ} (hb : ∀ i < m, f i = 0 ∨ f i = 1) {i0 i1 : ℕ}
    (h0 : i0 < m) (h1 : i1 < m) (hne : i0 ≠ i1) (e0 : f i0 = 1) (e1 : f i1 = 1) :
    2 ≤ ∑ i ∈ Finset.range m, f i := by
  have hsub : ({i0, i1} : Finset ℕ) ⊆ Finset.range m := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub
    (fun i hi _ => by have := hb i (Finset.mem_range.mp hi); omega)
  rw [Finset.sum_pair hne] at this
  omega

/-- The block sums, summed over the first `j` blocks. -/
theorem Sg_blocks {A B : ℤ → ℤ} {g N : ℕ} (D : ℤ) (F : ℕ → ℤ)
    (hw : ∀ j, (j + 1) * g ≤ N → Sg A B ((j + 1) * g) = Sg A B (j * g) + D + F j) :
    ∀ j, j * g ≤ N → Sg A B (j * g) = j * D + ∑ i ∈ Finset.range j, F i := by
  intro j
  induction j with
  | zero => intro _; simp [Sg_zero]
  | succ j ih =>
    intro hj
    have h1 := ih (by nlinarith)
    rw [hw j hj, h1, Finset.sum_range_succ]
    push_cast
    ring

namespace MixCtx

variable {A B : ℤ → ℤ} {r v s t g : ℕ}

theorem r_pos (h : MixCtx A B r v s t g) : 0 < r := by
  have := h.w.v_lt; have := h.w.v_pos; omega

theorem g_pos (h : MixCtx A B r v s t g) : 0 < g := by
  have := h.g2; omega

theorem Sg_r (h : MixCtx A B r v s t g) : Sg A B r = 1 := by
  have h1 := h.w.sing_r
  rw [mixFold_ht_eq_Sg] at h1
  have e : r - 1 + 1 = r := by have := h.r_pos; omega
  rwa [e] at h1

theorem win_D (h : MixCtx A B r v s t g) (hne : t % g ≠ s % g) :
    ∃ D : ℤ, ∀ n y1 y2 : ℕ, n + g ≤ r + v → n ≤ y1 → y1 < n + g → y1 % g = t % g →
      n ≤ y2 → y2 < n + g → y2 % g = s % g →
      ∑ i ∈ Finset.range g, mEps A B (n + i) = D + mnA A y1 + mnA A y2 := by
  have hg := h.g_pos
  have hrv : 1 ≤ r + v := by have := h.w.v_pos; omega
  obtain ⟨D, hD⟩ := window_inc (f := mEps A B) (g := g) (L := r + v - 1) (R₁ := t % g)
    (R₂ := s % g) hg (Nat.mod_lt _ hg) (Nat.mod_lt _ hg) hne
    (fun n hn h1 h2 => h.per_eps (by omega) h1 h2)
  refine ⟨D - mnB B (t % g) - mnB B (s % g), fun n y1 y2 hn a1 a2 a3 b1 b2 b3 => ?_⟩
  obtain ⟨z1, z2, c1, c2, c3, d1, d2, d3, hs⟩ := hD n (by omega)
  have e1 := eq_of_mod_window c1 c2 a1 a2 (c3.trans a3.symm)
  have e2 := eq_of_mod_window d1 d2 b1 b2 (d3.trans b3.symm)
  subst e1
  subst e2
  rw [hs]
  simp only [mEps]
  rw [h.mnB_mod (by omega : z1 < r + v), h.mnB_mod (by omega : z2 < r + v), a3, b3]
  ring

theorem win_D_eq (h : MixCtx A B r v s t g) (heq : t % g = s % g) :
    ∃ D : ℤ, ∀ n y1 : ℕ, n + g ≤ r + v → n ≤ y1 → y1 < n + g → y1 % g = t % g →
      ∑ i ∈ Finset.range g, mEps A B (n + i) = D + mnA A y1 := by
  have hg := h.g_pos
  have hg2 := h.g2
  have hrv : 1 ≤ r + v := by have := h.w.v_pos; omega
  set R2 := (t % g + 1) % g with hR2
  have hR2lt : R2 < g := Nat.mod_lt _ hg
  have hR2ne : t % g ≠ R2 := by
    have ht := Nat.mod_lt t hg
    rw [hR2]
    by_cases hlt : t % g + 1 < g
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have : t % g + 1 = g := by omega
      rw [this, Nat.mod_self]; omega
  obtain ⟨D, hD⟩ := window_inc (f := mEps A B) (g := g) (L := r + v - 1) (R₁ := t % g)
    (R₂ := R2) hg (Nat.mod_lt _ hg) hR2lt hR2ne
    (fun n hn h1 h2 => h.per_eps (by omega) h1 (by rw [← heq]; exact h1))
  refine ⟨D - mnB B (t % g) + (mnA A R2 - mnB B R2), fun n y1 hn a1 a2 a3 => ?_⟩
  obtain ⟨z1, z2, c1, c2, c3, d1, d2, d3, hs⟩ := hD n (by omega)
  have e1 := eq_of_mod_window c1 c2 a1 a2 (c3.trans a3.symm)
  subst e1
  rw [hs]
  have hz2 : z2 < r + v := by omega
  have m1 : mnA A z2 = mnA A (z2 % g) :=
    h.mnA_mod hz2 (by rw [d3]; exact fun e => hR2ne e.symm)
      (by rw [d3, ← heq]; exact fun e => hR2ne e.symm)
  have m2 : mnB B z2 = mnB B (z2 % g) := h.mnB_mod hz2
  simp only [mEps]
  rw [h.mnB_mod (by omega : z1 < r + v), m1, m2, d3, a3]
  ring

theorem m_pos (h : MixCtx A B r v s t g) : 0 < r / g := by
  obtain ⟨c, hc⟩ := h.gr
  have hg := h.g_pos
  have : r / g = c := by rw [hc]; exact Nat.mul_div_cancel_left c hg
  rw [this]
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · have := h.r_pos; rw [hc, h0] at this; simp at this
  · exact h0

theorem r_eq (h : MixCtx A B r v s t g) : r = r / g * g := (Nat.div_mul_cancel h.gr).symm

theorem t_lt_r (h : MixCtx A B r v s t g) : t < r := by
  have := h.w.t_lt; have := h.w.s_le; have := h.w.v_lt; omega

theorem s_lt_r (h : MixCtx A B r v s t g) : s < r := by
  have := h.w.s_le; have := h.w.v_lt; omega

theorem t_block (h : MixCtx A B r v s t g) : t = t / g * g + t % g := by
  have := Nat.div_add_mod' t g; omega

theorem s_block (h : MixCtx A B r v s t g) : s = s / g * g + s % g := by
  have := Nat.div_add_mod' s g; omega

theorem div_lt_m_t (h : MixCtx A B r v s t g) : t / g < r / g :=
  Nat.div_lt_div_of_lt_of_dvd h.gr h.t_lt_r

theorem div_lt_m_s (h : MixCtx A B r v s t g) : s / g < r / g :=
  Nat.div_lt_div_of_lt_of_dvd h.gr h.s_lt_r

/-- The sum of the first `m` block-values of an exceptional class. -/
theorem blocks_sum (h : MixCtx A B r v s t g) (D : ℤ) (F : ℕ → ℤ)
    (hD : ∀ j, (j + 1) * g ≤ r → ∑ i ∈ Finset.range g, mEps A B (j * g + i) = D + F j) :
    ((r / g : ℕ) : ℤ) * D + ∑ j ∈ Finset.range (r / g), F j = 1 := by
  have hr := h.r_eq
  have key := Sg_blocks (A := A) (B := B) (g := g) (N := r) D F (fun j hj => by
      rw [show (j + 1) * g = j * g + g by ring, Sg_add]
      have := hD j hj
      rw [this]; ring) (r / g) (by rw [← hr])
  rw [← hr] at key
  rw [h.Sg_r] at key
  exact key.symm

theorem sum_exc_lower (h : MixCtx A B r v s t g) {e : ℕ} (he : e < g) :
    ∑ j ∈ Finset.range (r / g), mnA A (j * g + e) ≤ ((r / g : ℕ) : ℤ) := by
  calc ∑ j ∈ Finset.range (r / g), mnA A (j * g + e) ≤ ∑ _j ∈ Finset.range (r / g), (1 : ℤ) :=
        Finset.sum_le_sum (fun j hj => by
          have hj' := Finset.mem_range.mp hj
          have := h.mnA_bit (k := j * g + e) (by
            have : (j + 1) * g ≤ r / g * g := Nat.mul_le_mul_right g hj'
            have := h.r_eq
            nlinarith [h.w.v_pos])
          omega)
    _ = ((r / g : ℕ) : ℤ) := by simp

theorem exc_term_t (h : MixCtx A B r v s t g) : mnA A (t / g * g + t % g) = 1 := by
  rw [← h.t_block]; exact h.mnA_t

theorem exc_term_s (h : MixCtx A B r v s t g) : mnA A (s / g * g + s % g) = 1 := by
  rw [← h.s_block]; exact h.mnA_s

/-- **The rank identity and the window increment.**  The two exceptional residues are distinct,
and every window of `g` consecutive increments sums to minus one plus the two exceptional bits. -/
theorem win (h : MixCtx A B r v s t g) :
    t % g ≠ s % g ∧ ∀ n y1 y2 : ℕ, n + g ≤ r + v → n ≤ y1 → y1 < n + g → y1 % g = t % g →
      n ≤ y2 → y2 < n + g → y2 % g = s % g →
      ∑ i ∈ Finset.range g, mEps A B (n + i) = -1 + mnA A y1 + mnA A y2 := by
  have hg := h.g_pos
  have hm := h.m_pos
  have hv := h.w.v_pos
  have hr := h.r_eq
  have hbit : ∀ e : ℕ, e < g → ∀ j ∈ Finset.range (r / g),
      mnA A (j * g + e) = 0 ∨ mnA A (j * g + e) = 1 := by
    intro e he j hj
    have hj' := Finset.mem_range.mp hj
    apply h.mnA_bit
    have : (j + 1) * g ≤ r / g * g := Nat.mul_le_mul_right g hj'
    nlinarith
  have hblk : ∀ j, j < r / g → j * g + g ≤ r := by
    intro j hj
    have : (j + 1) * g ≤ r / g * g := Nat.mul_le_mul_right g hj
    nlinarith
  have hblk' : ∀ j, (j + 1) * g ≤ r → j * g + g ≤ r := by
    intro j hj; nlinarith
  have ht := Nat.mod_lt t hg
  have hs := Nat.mod_lt s hg
  have hmz : (0 : ℤ) < ((r / g : ℕ) : ℤ) := by exact_mod_cast hm
  have hmt : (1 : ℤ) ≤ ∑ j ∈ Finset.range (r / g), mnA A (j * g + t % g) := by
    have := Finset.single_le_sum (f := fun j => mnA A (j * g + t % g))
      (s := Finset.range (r / g)) (fun j hj => by have := hbit _ ht j hj; omega)
      (Finset.mem_range.mpr h.div_lt_m_t)
    rw [h.exc_term_t] at this
    exact this
  by_cases heq : t % g = s % g
  · exfalso
    obtain ⟨D, hD⟩ := h.win_D_eq heq
    have key := h.blocks_sum D (fun j => mnA A (j * g + t % g)) (fun j hj => by
      have := hD (j * g) (j * g + t % g) (by have := hblk' j hj; omega) (by omega)
        (by omega) (mod_blk ht)
      exact this)
    beta_reduce at key
    have h2 : 2 ≤ ∑ j ∈ Finset.range (r / g), mnA A (j * g + t % g) := by
      apply sum_bits_two (i0 := t / g) (i1 := s / g) (fun i hi => hbit _ ht i (Finset.mem_range.mpr hi))
        h.div_lt_m_t h.div_lt_m_s
      · intro e
        have h1 := h.t_block
        have h2 := h.s_block
        have h3 := h.w.t_lt
        rw [e] at h1
        omega
      · exact h.exc_term_t
      · have := h.exc_term_s
        rw [← heq] at this
        exact this
    have h3 := h.sum_exc_lower ht
    rcases le_or_gt 0 D with hD0 | hD0
    · have := mul_nonneg hmz.le hD0
      linarith
    · have : ((r / g : ℕ) : ℤ) * D ≤ ((r / g : ℕ) : ℤ) * (-1) := by
        apply mul_le_mul_of_nonneg_left (by omega) hmz.le
      linarith
  · refine ⟨heq, fun n y1 y2 hn a1 a2 a3 b1 b2 b3 => ?_⟩
    obtain ⟨D, hD⟩ := h.win_D heq
    have key := h.blocks_sum D (fun j => mnA A (j * g + t % g) + mnA A (j * g + s % g))
      (fun j hj => by
        have := hD (j * g) (j * g + t % g) (j * g + s % g) (by have := hblk' j hj; omega)
          (by omega) (by omega) (mod_blk ht) (by omega) (by omega) (mod_blk hs)
        rw [this]; ring)
    have hs1 : (1 : ℤ) ≤ ∑ j ∈ Finset.range (r / g), mnA A (j * g + s % g) := by
      have := Finset.single_le_sum (f := fun j => mnA A (j * g + s % g))
        (s := Finset.range (r / g)) (fun j hj => by have := hbit _ hs j hj; omega)
        (Finset.mem_range.mpr h.div_lt_m_s)
      rw [h.exc_term_s] at this
      exact this
    have h3 := h.sum_exc_lower ht
    have h4 := h.sum_exc_lower hs
    beta_reduce at key
    rw [Finset.sum_add_distrib] at key
    have hDm : D = -1 := by
      rcases le_or_gt 0 D with hD0 | hD0
      · have := mul_nonneg hmz.le hD0
        linarith
      · rcases le_or_gt D (-2) with hD1 | hD1
        · have : ((r / g : ℕ) : ℤ) * D ≤ ((r / g : ℕ) : ℤ) * (-2) :=
            mul_le_mul_of_nonneg_left hD1 hmz.le
          linarith
        · omega
    rw [hD n y1 y2 hn a1 a2 a3 b1 b2 b3, hDm]

end MixCtx

end FoldSupplied
end SkewGluing
