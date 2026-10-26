import SkewGluing.FoldSupplied.MixedWords

/-!
# Periodicity of the boundary words of a case-(d) inner

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:mixed-fold`): the word-level consequences of the hypotheses that every residue
class of the native row list modulo `g` is full or empty, and every class of the native column
list outside the residues of `t` and `s` is full or empty.

`MixCtx A B r v s t g` carries the case-(d) word facts `MixWords` and the two class conditions on
the completed words `mnA` (the column word with the returned zero filled by one) and `mnB` (the
row word with the returned zero filled by zero).  The upper copy relations carry the classes to
the whole word of span `r + v` (`MixCtx.mnB_mod`, `MixCtx.mnA_mod`), and `window_inc` is the
increment of a window of `g` consecutive increments, which is constant up to the values of the
bits at the two exceptional residues.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

/-- The completed native column word: the returned zero is filled by one. -/
def mnA (A : ℤ → ℤ) (k : ℕ) : ℤ := if k = 0 then 1 else A k

/-- The completed native row word: the returned zero is filled by zero. -/
def mnB (B : ℤ → ℤ) (k : ℕ) : ℤ := if k = 0 then 0 else B k

/-- The increment of the height word at the position `k`. -/
def mEps (A B : ℤ → ℤ) (k : ℕ) : ℤ := mnA A k - mnB B k

theorem mixFold_ht_eq_sum (A B : ℤ → ℤ) (n : ℕ) :
    mixFold_ht A B n = ∑ i ∈ Finset.range (n + 1), mEps A B i := by
  induction n with
  | zero => simp [mixFold_ht_zero, mEps, mnA, mnB]
  | succ n ih =>
    rw [mixFold_ht_succ, ih, Finset.sum_range_succ _ (n + 1)]
    simp [mEps, mnA, mnB]

theorem sum_range_mul_split (f : ℕ → ℤ) (g m : ℕ) :
    ∑ i ∈ Finset.range (m * g), f i = ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range g, f (j * g + i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, show (m + 1) * g = m * g + g by ring, Finset.sum_range_add]

theorem eq_of_mod_window {n y y' g : ℕ} (hy : n ≤ y) (hy' : y < n + g) (hz : n ≤ y')
    (hz' : y' < n + g) (h : y % g = y' % g) : y = y' := by
  rcases le_total y y' with hle | hle
  · have h0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    have hk : y' - y < g := by omega
    rw [Nat.mod_eq_of_lt hk] at h0
    omega
  · have h0 := Nat.sub_mod_eq_zero_of_mod_eq h
    have hk : y - y' < g := by omega
    rw [Nat.mod_eq_of_lt hk] at h0
    omega

/-- The sum of `g` consecutive increments is constant up to the values at the two exceptional
residues `R₁ ≠ R₂`. -/
theorem window_inc {f : ℕ → ℤ} {g L R₁ R₂ : ℕ} (hg : 0 < g) (h1 : R₁ < g) (h2 : R₂ < g)
    (hne : R₁ ≠ R₂)
    (hper : ∀ n, n + g ≤ L → n % g ≠ R₁ → n % g ≠ R₂ → f n = f (n + g)) :
    ∃ D : ℤ, ∀ n, n + g ≤ L + 1 → ∃ y₁ y₂ : ℕ, n ≤ y₁ ∧ y₁ < n + g ∧ y₁ % g = R₁ ∧
      n ≤ y₂ ∧ y₂ < n + g ∧ y₂ % g = R₂ ∧
      ∑ i ∈ Finset.range g, f (n + i) = D + f y₁ + f y₂ := by
  refine ⟨(∑ i ∈ Finset.range g, f i) - f R₁ - f R₂, ?_⟩
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨R₁, R₂, by omega, by omega, Nat.mod_eq_of_lt h1, by omega, by omega,
      Nat.mod_eq_of_lt h2, by simp only [zero_add]; ring⟩
  | succ n ih =>
    intro hn
    obtain ⟨y₁, y₂, a1, a2, a3, b1, b2, b3, hs⟩ := ih (by omega)
    have hshift : ∑ i ∈ Finset.range g, f (n + 1 + i) + f n =
        f (n + g) + ∑ i ∈ Finset.range g, f (n + i) := by
      have e1 := Finset.sum_range_succ (fun i => f (n + i)) g
      have e2 := Finset.sum_range_succ' (fun i => f (n + i)) g
      have e3 : ∑ i ∈ Finset.range g, f (n + (i + 1)) = ∑ i ∈ Finset.range g, f (n + 1 + i) :=
        Finset.sum_congr rfl (fun i _ => by rw [show n + (i + 1) = n + 1 + i by ring])
      rw [e3] at e2
      simp only [add_zero] at e1 e2
      linarith
    have hmod1 : (n + g) % g = n % g := by simp
    by_cases c1 : y₁ = n
    · have hr1 : n % g = R₁ := by rw [← a3, c1]
      have c2 : y₂ ≠ n := by
        intro h; apply hne; rw [← b3, h, hr1]
      refine ⟨n + g, y₂, by omega, by omega, by rw [hmod1, hr1], by omega, by omega, b3, ?_⟩
      subst c1
      linarith
    · by_cases c2 : y₂ = n
      · have hr2 : n % g = R₂ := by rw [← b3, c2]
        refine ⟨y₁, n + g, by omega, by omega, a3, by omega, by omega, by rw [hmod1, hr2], ?_⟩
        subst c2
        linarith
      · have hn1 : n % g ≠ R₁ := by
          intro h
          apply c1
          refine eq_of_mod_window a1 a2 (le_refl n) (by omega) ?_
          rw [a3, h]
        have hn2 : n % g ≠ R₂ := by
          intro h
          apply c2
          refine eq_of_mod_window b1 b2 (le_refl n) (by omega) ?_
          rw [b3, h]
        have := hper n (by omega) hn1 hn2
        refine ⟨y₁, y₂, by omega, by omega, a3, by omega, by omega, b3, ?_⟩
        linarith

/-- The word facts and class conditions of the inner of a case-(d) mark. -/
structure MixCtx (A B : ℤ → ℤ) (r v s t g : ℕ) : Prop where
  w : MixWords A B r v s t
  g2 : 2 ≤ g
  gr : g ∣ r
  glt : g < r
  hB : ∀ x y, x < r → y < r → x % g = y % g → mnB B x = mnB B y
  hC : ∀ x y, x < r → y < r → x % g = y % g → x % g ≠ t % g → x % g ≠ s % g →
    mnA A x = mnA A y

namespace MixCtx

variable {A B : ℤ → ℤ} {r v s t g : ℕ}

theorem mnA_bit (h : MixCtx A B r v s t g) {k : ℕ} (hk : k < r + v) :
    mnA A k = 0 ∨ mnA A k = 1 := by
  unfold mnA
  by_cases h0 : k = 0
  · simp [h0]
  · simp only [h0, if_false]
    have := (h.w.bits k (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0) (by
      have : (k : ℤ) + 1 ≤ ((r + v : ℕ) : ℤ) := by exact_mod_cast hk
      omega)).1
    exact this

theorem mnB_bit (h : MixCtx A B r v s t g) {k : ℕ} (hk : k < r + v) :
    mnB B k = 0 ∨ mnB B k = 1 := by
  unfold mnB
  by_cases h0 : k = 0
  · simp [h0]
  · simp only [h0, if_false]
    have := (h.w.bits k (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0) (by
      have : (k : ℤ) + 1 ≤ ((r + v : ℕ) : ℤ) := by exact_mod_cast hk
      omega)).2
    exact this

/-- The upper copy of the column word. -/
theorem mnA_upper (h : MixCtx A B r v s t g) {b : ℕ} (hb : b < v) :
    mnA A (r + b) = mnA A b - (if b = s then 1 else 0) - (if b = t then 1 else 0) := by
  have hs1 := h.w.s_pos
  have hr : r ≠ 0 := by have := h.w.v_lt; have := h.w.v_pos; omega
  by_cases hb0 : b = 0
  · subst hb0
    have e := h.w.A_r
    have : (0 : ℕ) ≠ s := by omega
    simp only [mnA, add_zero, hr, if_false, if_true, this]
    rw [e]
    split_ifs <;> omega
  · have e := h.w.copyA b (by omega) hb
    have hrb : r + b ≠ 0 := by omega
    simp only [mnA, hrb, hb0, if_false]
    push_cast
    rw [e]

theorem mnB_upper (h : MixCtx A B r v s t g) {b : ℕ} (hb : b < v) : mnB B (r + b) = mnB B b := by
  have hr : r ≠ 0 := by have := h.w.v_lt; have := h.w.v_pos; omega
  by_cases hb0 : b = 0
  · subst hb0
    have e := h.w.B_r
    simp only [mnB, add_zero, hr, if_false, if_true]
    exact e
  · have e := h.w.copyB b (by omega) hb
    have hrb : r + b ≠ 0 := by omega
    simp only [mnB, hrb, hb0, if_false]
    push_cast
    rw [e]

/-- The position of the lower copy of a position of the whole word. -/
def red (r i : ℕ) : ℕ := if i < r then i else i - r

theorem red_lt (h : MixCtx A B r v s t g) {i : ℕ} (hi : i < r + v) : red r i < r := by
  have := h.w.v_lt
  unfold red; split_ifs <;> omega

theorem red_mod (h : MixCtx A B r v s t g) (i : ℕ) : red r i % g = i % g := by
  unfold red
  split_ifs with hi
  · rfl
  · obtain ⟨c, hc⟩ := h.gr
    have : i = (i - r) + g * c := by omega
    conv_rhs => rw [this]
    simp

theorem mnB_red (h : MixCtx A B r v s t g) {i : ℕ} (hi : i < r + v) :
    mnB B i = mnB B (red r i) := by
  unfold red
  split_ifs with hir
  · rfl
  · have := h.mnB_upper (b := i - r) (by omega)
    rw [show r + (i - r) = i by omega] at this
    exact this

theorem mnA_red (h : MixCtx A B r v s t g) {i : ℕ} (hi : i < r + v) (h1 : i % g ≠ t % g)
    (h2 : i % g ≠ s % g) : mnA A i = mnA A (red r i) := by
  unfold red
  split_ifs with hir
  · rfl
  · have := h.mnA_upper (b := i - r) (by omega)
    rw [show r + (i - r) = i by omega] at this
    have hm := h.red_mod i
    unfold red at hm
    rw [if_neg hir] at hm
    have e1 : i - r ≠ s := fun e => h2 (by rw [← hm, e])
    have e2 : i - r ≠ t := fun e => h1 (by rw [← hm, e])
    rw [this]
    simp [e1, e2]

theorem mnB_mod (h : MixCtx A B r v s t g) {i : ℕ} (hi : i < r + v) :
    mnB B i = mnB B (i % g) := by
  have hg : 0 < g := by have := h.g2; omega
  rw [h.mnB_red hi]
  exact h.hB _ _ (h.red_lt hi) (lt_of_lt_of_le (Nat.mod_lt _ hg) h.glt.le)
    (by rw [h.red_mod, Nat.mod_mod])

theorem mnA_mod (h : MixCtx A B r v s t g) {i : ℕ} (hi : i < r + v) (h1 : i % g ≠ t % g)
    (h2 : i % g ≠ s % g) : mnA A i = mnA A (i % g) := by
  have hg : 0 < g := by have := h.g2; omega
  rw [h.mnA_red hi h1 h2]
  have hm := h.red_mod i
  exact h.hC _ _ (h.red_lt hi) (lt_of_lt_of_le (Nat.mod_lt _ hg) h.glt.le)
    (by rw [hm, Nat.mod_mod]) (by rw [hm]; exact h1) (by rw [hm]; exact h2)

theorem per_eps (h : MixCtx A B r v s t g) {n : ℕ} (hn : n + g < r + v) (h1 : n % g ≠ t % g)
    (h2 : n % g ≠ s % g) : mEps A B n = mEps A B (n + g) := by
  have e : (n + g) % g = n % g := by simp
  unfold mEps
  rw [h.mnB_mod (by omega), h.mnB_mod hn, h.mnA_mod (by omega) h1 h2,
    h.mnA_mod hn (by rw [e]; exact h1) (by rw [e]; exact h2), e]

theorem mnA_t (h : MixCtx A B r v s t g) : mnA A t = 1 := by
  have hts := h.w.t_lt
  have hsv := h.w.s_le
  have hvr := h.w.v_lt
  by_cases ht0 : t = 0
  · simp [mnA, ht0]
  · have h1 := h.mnA_upper (b := t) (by omega)
    have h2 := h.mnA_bit (k := r + t) (by omega)
    have h3 := h.mnA_bit (k := t) (by omega)
    have : t ≠ s := by omega
    simp only [this, if_false, if_true] at h1
    omega

theorem mnA_s (h : MixCtx A B r v s t g) : mnA A s = 1 := by
  have hts := h.w.t_lt
  have hsv := h.w.s_le
  have hvr := h.w.v_lt
  have hs1 := h.w.s_pos
  by_cases hsv' : s = v
  · have e := h.w.A_v
    have hs0 : s ≠ 0 := by omega
    simp only [mnA, hs0, if_false]
    rw [hsv'] at e ⊢
    simp [e]
  · have h1 := h.mnA_upper (b := s) (by omega)
    have h2 := h.mnA_bit (k := r + s) (by omega)
    have h3 := h.mnA_bit (k := s) (by omega)
    have : s ≠ t := by omega
    simp only [this, if_false, if_true] at h1
    omega

end MixCtx

end FoldSupplied
end SkewGluing
