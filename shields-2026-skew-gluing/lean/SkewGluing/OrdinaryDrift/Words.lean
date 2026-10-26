import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import SkewGluing.Diagram

/-!
# Boundary words of two ordinary roots: the arithmetic of the drift lemma

Formalizes `shields-2026-skew-gluing.tex`, «Two ordinary roots»
(`eq:gluing-gcd-data`, `lem:gluing-ordinary-drift`, `eq:gluing-pinch-equations`,
`eq:gluing-pinches`).

This file proves the drift lemma at the level of boundary words.  A word is a function `ℕ → ℤ`
read on the positions `1, …, N - 1`; `WordData` records that the pair `(A, B)` is the pair of
bit words of a connected skew diagram, `RootWords` the facts one ordinary root contributes
(its caps `eq:gluing-caps` and the private singletons), and `GcdPair` the setting of
`eq:gluing-gcd-data` for two such roots, with the generic bits `A⁰`, `B⁰` of
`lem:gluing-periods` (ii).  `GcdPair.drift_full` is the conclusion of `lem:gluing-ordinary-drift`.
The terminal half is obtained from the initial half by reading all words backwards
(`GcdPair.reverse`).

Sorry-free.
-/

namespace SkewGluing
namespace OrdinaryDrift

/-- The sum `C 1 + ⋯ + C n` of the first `n` increments. -/
def genSum (C : ℕ → ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, C (i + 1)



theorem genSum_add_period {C : ℕ → ℤ} {g : ℕ} (hC : ∀ n, C (n + g) = C n) :
    ∀ n, genSum C (n + g) = genSum C n + genSum C g := by
  intro n
  induction n with
  | zero => simp [genSum]
  | succ n ih =>
    have e : n + 1 + g = (n + g) + 1 := by omega
    rw [e]
    unfold genSum at ih ⊢
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have := hC (n + 1)
    rw [show n + 1 + g = n + g + 1 by omega] at this
    rw [this]; ring

theorem genSum_mul_add {C : ℕ → ℤ} {g : ℕ} (hC : ∀ n, C (n + g) = C n) (m r : ℕ) :
    genSum C (m * g + r) = m * genSum C g + genSum C r := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (m + 1) * g + r = (m * g + r) + g := by ring
    rw [e, genSum_add_period hC, ih]; push_cast; ring

theorem genSum_period_eq_sum {C : ℕ → ℤ} {g : ℕ} (hC : C g = C 0) :
    genSum C g = ∑ j ∈ Finset.range g, C j := by
  unfold genSum
  have h1 := Finset.sum_range_succ' C g
  have h2 := Finset.sum_range_succ C g
  rw [hC] at h2
  linarith


/-- The generic increment at the position `n`. -/
def incr (A0 B0 : ℕ → ℤ) (g n : ℕ) : ℤ := A0 (n % g) - B0 (n % g)

/-- The pair `(A, B)` is the pair of bit words of a connected skew diagram of span `N`: the bits
lie in `{0, 1}`, the heights `heightWord A B k` are positive, and the last one is `1`. -/
structure WordData (A B : ℕ → ℤ) (N : ℕ) : Prop where
  bits : ∀ k, 1 ≤ k → k < N → (A k = 0 ∨ A k = 1) ∧ (B k = 0 ∨ B k = 1)
  pos : ∀ k, k < N → 0 < heightWord A B k
  last : heightWord A B (N - 1) = 1

/-- The facts about the parent words `(A, B)` that one ordinary root of period `q` and width `w`
contributes: the span law `N = r q + w` with `r ≥ 2`, the exceptional residues `ha` (of `A`) and
`hb` (of `B`) with their initial and terminal cap bits (`eq:gluing-caps`), and the four private
singletons `H_w = H_{q-1} = H_{N-q} = H_{N-1-w} = 1` (`lem:gluing-local` (1), (3)). -/
structure RootWords (A B : ℕ → ℤ) (N q w ha hb : ℕ) : Prop where
  hwq : w < q
  rep : ∃ r, 2 ≤ r ∧ N = r * q + w
  ha_le : ha ≤ w
  hb_le : hb ≤ w
  capA_init : 1 ≤ ha → A ha = 1
  capB_init : 1 ≤ hb → B hb = 0
  capA_term : ha < w → A (N - w + ha) = 0
  capB_term : hb < w → B (N - w + hb) = 1
  sing_w : heightWord A B w = 1
  sing_q : heightWord A B (q - 1) = 1
  sing_Nw : heightWord A B (N - 1 - w) = 1
  sing_Nq : heightWord A B (N - q) = 1

/-- The deviation, in height, of the northwest word at its initial cap `A_{ha} = 1` from the generic
bit: `1 - A⁰_{ha}` (a northwest deviation changes zero to one). -/
def devA (A0 : ℕ → ℤ) (g ha : ℕ) : ℤ := if 1 ≤ ha then 1 - A0 (ha % g) else 0

/-- The deviation, in height, of the southeast word at its initial cap `B_{hb} = 0` from the
generic bit: `B⁰_{hb}` (a southeast deviation changes one to zero). -/
def devB (B0 : ℕ → ℤ) (g hb : ℕ) : ℤ := if 1 ≤ hb then B0 (hb % g) else 0

/-- The height of the parent on the first diagonals: generic increments plus the initial
deviations. -/
theorem height_formula {A B A0 B0 : ℕ → ℤ} {N g q w ha hb : ℕ}
    (hR : RootWords A B N q w ha hb)
    (hgenA : ∀ x, 1 ≤ x → x < q → x < N → x ≠ ha → A x = A0 (x % g))
    (hgenB : ∀ x, 1 ≤ x → x < q → x < N → x ≠ hb → B x = B0 (x % g)) :
    ∀ k, k < q → k < N → heightWord A B k =
      1 + genSum (incr A0 B0 g) k + (if ha ≤ k then devA A0 g ha else 0) +
        (if hb ≤ k then devB B0 g hb else 0) := by
  intro k
  induction k with
  | zero =>
    intro _ _
    simp only [heightWord, genSum, Finset.range_zero, Finset.sum_empty, add_zero,
      nonpos_iff_eq_zero]
    by_cases h1 : ha = 0
    · by_cases h2 : hb = 0
      · simp [h1, h2, devA, devB]
      · simp [h1, h2, devA]
    · by_cases h2 : hb = 0
      · simp [h1, h2, devB]
      · simp [h1, h2]
  | succ k ih =>
    intro hk1 hk2
    have ih := ih (by omega) (by omega)
    rw [heightWord_succ, ih]
    have hA : A (k + 1) - A0 ((k + 1) % g) = if k + 1 = ha then devA A0 g ha else 0 := by
      by_cases h : k + 1 = ha
      · subst h
        rw [hR.capA_init (by omega)]
        simp [devA]
      · rw [hgenA (k + 1) (by omega) hk1 hk2 h]
        simp [h]
    have hB : B (k + 1) - B0 ((k + 1) % g) = -(if k + 1 = hb then devB B0 g hb else 0) := by
      by_cases h : k + 1 = hb
      · subst h
        rw [hR.capB_init (by omega)]
        simp [devB]
      · rw [hgenB (k + 1) (by omega) hk1 hk2 h]
        simp [h]
    unfold genSum
    rw [Finset.sum_range_succ]
    unfold incr
    have e1 : (if ha ≤ k + 1 then devA A0 g ha else 0) =
        (if ha ≤ k then devA A0 g ha else 0) + (if k + 1 = ha then devA A0 g ha else 0) := by
      by_cases h : k + 1 = ha
      · subst h; simp
      · by_cases h' : ha ≤ k
        · simp [h, h', show ha ≤ k + 1 by omega]
        · simp [h, h', show ¬ ha ≤ k + 1 by omega]
    have e2 : (if hb ≤ k + 1 then devB B0 g hb else 0) =
        (if hb ≤ k then devB B0 g hb else 0) + (if k + 1 = hb then devB B0 g hb else 0) := by
      by_cases h : k + 1 = hb
      · subst h; simp
      · by_cases h' : hb ≤ k
        · simp [h, h', show hb ≤ k + 1 by omega]
        · simp [h, h', show ¬ hb ≤ k + 1 by omega]
    rw [e1, e2]
    linarith


theorem incr_periodic (A0 B0 : ℕ → ℤ) {g : ℕ} :
    ∀ n, incr A0 B0 g (n + g) = incr A0 B0 g n := by
  intro n; simp [incr, Nat.add_mod_right]

theorem incr_self (A0 B0 : ℕ → ℤ) {g : ℕ} :
    incr A0 B0 g g = A0 0 - B0 0 := by
  simp [incr]

theorem genSum_pred_period (A0 B0 : ℕ → ℤ) {g : ℕ} (hg : 0 < g) :
    genSum (incr A0 B0 g) (g - 1) = genSum (incr A0 B0 g) g - (A0 0 - B0 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, g = m + 1 := ⟨g - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold genSum
  rw [Finset.sum_range_succ]
  simp [incr]

theorem genSum_mul_pred (A0 B0 : ℕ → ℤ) {g a : ℕ} (hg : 0 < g) (ha : 1 ≤ a) :
    genSum (incr A0 B0 g) (a * g - 1) =
      a * genSum (incr A0 B0 g) g - (A0 0 - B0 0) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have e : (a' + 1) * g - 1 = a' * g + (g - 1) := by
    rw [Nat.succ_mul]; generalize a' * g = t; omega
  rw [e, genSum_mul_add (incr_periodic A0 B0), genSum_pred_period A0 B0 hg]
  push_cast; ring

/-- The arithmetic of the pinch equations `eq:gluing-pinch-equations` for two ordinary roots. -/
theorem drift_arith {a c : ℕ} {Δ ε δ₁ δ₂ : ℤ} (ha : 2 ≤ a) (hc : 2 ≤ c)
    (hcop : Nat.Coprime a c)
    (e2 : a * Δ - ε + δ₁ = 0) (e2' : c * Δ - ε + δ₂ = 0)
    (hε1 : -1 ≤ ε) (hε2 : ε ≤ 1) (hδ₁ : 0 ≤ δ₁ ∧ δ₁ ≤ 2) (hδ₂ : 0 ≤ δ₂ ∧ δ₂ ≤ 2) :
    Δ = 0 ∨ (Δ = -1 ∧ ε = -1 ∧ ((a = 2 ∧ c = 3) ∨ (a = 3 ∧ c = 2))) := by
  have ha' : (2 : ℤ) ≤ a := by exact_mod_cast ha
  have hc' : (2 : ℤ) ≤ c := by exact_mod_cast hc
  by_cases hΔ : Δ = 0
  · exact Or.inl hΔ
  right
  rcases lt_or_gt_of_ne hΔ with hneg | hpos
  · have h1 : (a : ℤ) * Δ ≤ -a := by nlinarith
    have h2 : (c : ℤ) * Δ ≤ -c := by nlinarith
    have hΔ1 : Δ = -1 := by
      by_contra hne
      have : Δ ≤ -2 := by omega
      nlinarith
    subst hΔ1
    have ha3 : a ≤ 3 := by omega
    have hc3 : c ≤ 3 := by omega
    have hne : a ≠ c := by
      rintro rfl
      simp [Nat.coprime_self] at hcop
      omega
    interval_cases a <;> interval_cases c <;> simp_all <;> omega
  · exfalso
    have h1 : (a : ℤ) * Δ ≥ a := by nlinarith
    nlinarith


theorem RootWords.two_q_le {A B : ℕ → ℤ} {N q w ha hb : ℕ} (h : RootWords A B N q w ha hb) :
    2 * q ≤ N := by
  obtain ⟨r, hr, hN⟩ := h.rep
  have := Nat.mul_le_mul_right q hr
  omega

/-- **`eq:gluing-pinch-equations`** for one root: the two private singletons at `w = b g + w_g` and
at `q - 1 = a g - 1` give `b Δ + P_{w_g} + δ = 0` and `a Δ - ε + δ = 0`, with `δ` the sum of the
two initial deviations. -/
theorem chart_eqs {A B A0 B0 : ℕ → ℤ} {N g a b wg ha hb : ℕ} (hg : 0 < g) (ha1 : 1 ≤ a)
    (hR : RootWords A B N (a * g) (b * g + wg) ha hb)
    (hgenA : ∀ x, 1 ≤ x → x < a * g → x < N → x ≠ ha → A x = A0 (x % g))
    (hgenB : ∀ x, 1 ≤ x → x < a * g → x < N → x ≠ hb → B x = B0 (x % g)) :
    b * genSum (incr A0 B0 g) g + genSum (incr A0 B0 g) wg +
        (devA A0 g ha + devB B0 g hb) = 0 ∧
      a * genSum (incr A0 B0 g) g - (A0 0 - B0 0) + (devA A0 g ha + devB B0 g hb) = 0 := by
  have hN2 := hR.two_q_le
  have hwq := hR.hwq
  have hha := hR.ha_le
  have hhb := hR.hb_le
  have hag : 1 ≤ a * g := Nat.mul_pos (by omega) hg
  constructor
  · have h := height_formula hR hgenA hgenB (b * g + wg) hwq (by omega)
    rw [hR.sing_w] at h
    simp only [hha, hhb, ↓reduceIte] at h
    have e := genSum_mul_add (incr_periodic A0 B0 (g := g)) b wg
    linarith
  · have h := height_formula hR hgenA hgenB (a * g - 1) (by omega) (by omega)
    rw [hR.sing_q] at h
    have hh1 : ha ≤ a * g - 1 := by omega
    have hh2 : hb ≤ a * g - 1 := by omega
    simp only [hh1, hh2, ↓reduceIte] at h
    rw [genSum_mul_pred A0 B0 hg ha1] at h
    linarith


theorem devA_bounds {A0 : ℕ → ℤ} {g ha : ℕ} (h : A0 (ha % g) = 0 ∨ A0 (ha % g) = 1) :
    0 ≤ devA A0 g ha ∧ devA A0 g ha ≤ 1 := by
  unfold devA
  split_ifs <;> rcases h with h | h <;> simp [h]

theorem devB_bounds {B0 : ℕ → ℤ} {g hb : ℕ} (h : B0 (hb % g) = 0 ∨ B0 (hb % g) = 1) :
    0 ≤ devB B0 g hb ∧ devB B0 g hb ≤ 1 := by
  unfold devB
  split_ifs <;> rcases h with h | h <;> simp [h]

theorem height_split (A B A0 B0 : ℕ → ℤ) (g : ℕ) (k : ℕ) :
    heightWord A B k = 1 + genSum (incr A0 B0 g) k +
      (∑ i ∈ Finset.range k, (A (i + 1) - A0 ((i + 1) % g))) +
      (∑ i ∈ Finset.range k, (B0 ((i + 1) % g) - B (i + 1))) := by
  induction k with
  | zero => simp [heightWord, genSum]
  | succ k ih =>
    rw [heightWord_succ, ih]
    unfold genSum
    simp only [Finset.sum_range_succ]
    unfold incr
    ring

/-- At most one simultaneous hole below the lcm bounds the accumulated deviation by one. -/
theorem dev_sum_le {f : ℕ → ℤ} {N L : ℕ} {SH : ℕ → Prop}
    (huniq : ∀ x y, 1 ≤ x → x < L → 1 ≤ y → y < L → SH x → SH y → x = y)
    (hzero : ∀ x, 1 ≤ x → x < N → ¬ SH x → f x = 0)
    (hle : ∀ x, 1 ≤ x → x < N → f x ≤ 1) :
    ∀ k, k < N → k < L → (∑ i ∈ Finset.range k, f (i + 1)) ≤ 1 ∧
      ((∀ x, 1 ≤ x → x ≤ k → ¬ SH x) → (∑ i ∈ Finset.range k, f (i + 1)) ≤ 0) := by
  intro k
  induction k with
  | zero => intro _ _; simp
  | succ k ih =>
    intro hk1 hk2
    obtain ⟨ih1, ih2⟩ := ih (by omega) (by omega)
    rw [Finset.sum_range_succ]
    by_cases hS : SH (k + 1)
    · have hno : ∀ x, 1 ≤ x → x ≤ k → ¬ SH x := by
        intro x hx1 hx2 hSx
        have := huniq x (k + 1) hx1 (by omega) (by omega) hk2 hSx hS
        omega
      have h0 := ih2 hno
      have h1 := hle (k + 1) (by omega) hk1
      refine ⟨by linarith, fun hall => absurd hS (hall (k + 1) (by omega) le_rfl)⟩
    · have h0 := hzero (k + 1) (by omega) hk1 hS
      refine ⟨by linarith, fun hall => ?_⟩
      have := ih2 (fun x hx1 hx2 => hall x hx1 (by omega))
      linarith


/-- Once `Δ = 0`, `δ = ε` and `P_{w_g} = -ε`, the words of one root are generic on `(w_g, q)` and
the pinches `H_{w_g} = H_{g-1} = 1` hold. -/
theorem chart_final {A B A0 B0 : ℕ → ℤ} {N g a b wg ha hb : ℕ} (hg : 0 < g) (ha1 : 1 ≤ a)
    (hwg : wg < g) (hword : WordData A B N)
    (hR : RootWords A B N (a * g) (b * g + wg) ha hb)
    (hgenA : ∀ x, 1 ≤ x → x < a * g → x < N → x ≠ ha → A x = A0 (x % g))
    (hgenB : ∀ x, 1 ≤ x → x < a * g → x < N → x ≠ hb → B x = B0 (x % g))
    (hA0 : ∀ j, j < g → A0 j = 0 ∨ A0 j = 1) (hB0 : ∀ j, j < g → B0 j = 0 ∨ B0 j = 1)
    (hΔ : genSum (incr A0 B0 g) g = 0)
    (hP : genSum (incr A0 B0 g) wg = -(A0 0 - B0 0))
    (hδ : devA A0 g ha + devB B0 g hb = A0 0 - B0 0) :
    (∀ x, wg < x → x < a * g → x < N → A x = A0 (x % g) ∧ B x = B0 (x % g)) ∧
      heightWord A B wg = 1 ∧ heightWord A B (g - 1) = 1 := by
  have hN2 := hR.two_q_le
  have hag : g ≤ a * g := Nat.le_mul_of_pos_left g (by omega)
  obtain ⟨hdA0, hdA1⟩ := devA_bounds (A0 := A0) (g := g) (ha := ha) (hA0 _ (Nat.mod_lt _ hg))
  obtain ⟨hdB0, hdB1⟩ := devB_bounds (B0 := B0) (g := g) (hb := hb) (hB0 _ (Nat.mod_lt _ hg))
  have hf := height_formula hR hgenA hgenB wg (by omega) (by omega)
  have hpos := hword.pos wg (by omega)
  have hifA : (if ha ≤ wg then devA A0 g ha else 0) ≤ devA A0 g ha := by
    split_ifs <;> linarith
  have hifB : (if hb ≤ wg then devB B0 g hb else 0) ≤ devB B0 g hb := by
    split_ifs <;> linarith
  have hifA0 : 0 ≤ (if ha ≤ wg then devA A0 g ha else 0) := by split_ifs <;> linarith
  have hifB0 : 0 ≤ (if hb ≤ wg then devB B0 g hb else 0) := by split_ifs <;> linarith
  rw [hf, hP] at hpos
  have heA : (if ha ≤ wg then devA A0 g ha else 0) = devA A0 g ha := by linarith
  have heB : (if hb ≤ wg then devB B0 g hb else 0) = devB B0 g hb := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x hx1 hx2 hx3
    refine ⟨?_, ?_⟩
    · by_cases hxa : x = ha
      · subst hxa
        have hd : devA A0 g x = 0 := by
          rw [← heA]; simp [show ¬ x ≤ wg by omega]
        have h1 : 1 ≤ x := by omega
        simp only [devA, h1, ↓reduceIte] at hd
        rw [hR.capA_init h1]; linarith
      · exact hgenA x (by omega) hx2 hx3 hxa
    · by_cases hxb : x = hb
      · subst hxb
        have hd : devB B0 g x = 0 := by
          rw [← heB]; simp [show ¬ x ≤ wg by omega]
        have h1 : 1 ≤ x := by omega
        simp only [devB, h1, ↓reduceIte] at hd
        rw [hR.capB_init h1]; linarith
      · exact hgenB x (by omega) hx2 hx3 hxb
  · rw [hf, hP, heA, heB]; linarith
  · have hf2 := height_formula hR hgenA hgenB (g - 1) (by omega) (by omega)
    rw [hf2, genSum_pred_period A0 B0 hg, hΔ]
    have e1 : (if ha ≤ g - 1 then devA A0 g ha else 0) = devA A0 g ha := by
      by_cases h : ha ≤ wg
      · simp [show ha ≤ g - 1 by omega]
      · have : devA A0 g ha = 0 := by rw [← heA]; simp [h]
        simp [this]
    have e2 : (if hb ≤ g - 1 then devB B0 g hb else 0) = devB B0 g hb := by
      by_cases h : hb ≤ wg
      · simp [show hb ≤ g - 1 by omega]
      · have : devB B0 g hb = 0 := by rw [← heB]; simp [h]
        simp [this]
    rw [e1, e2]; linarith


/-- The northwest or southeast word is `g`-periodic off the simultaneous holes: positions in
`1, …, N - 1` whose residues modulo the two periods are not both the exceptional ones carry the
generic bit of their residue class modulo `g`. -/
def IsGenericWord (W W0 : ℕ → ℤ) (N g q₁ q₂ h₁ h₂ : ℕ) : Prop :=
  ∀ x, 1 ≤ x → x < N → ¬ (x % q₁ = h₁ ∧ x % q₂ = h₂) → W x = W0 (x % g)

/-- The setting `eq:gluing-gcd-data` read on the boundary words of the parent: two ordinary roots
of periods `a g`, `c g` (`a, c ≥ 2` coprime), widths `b g + w_g`, `d g + w_g`, with exceptional
residues `ha₁, hb₁` and `ha₂, hb₂` of the two words, and generic bits `A0`, `B0`. -/
structure GcdPair (A B A0 B0 : ℕ → ℤ) (N g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ) : Prop where
  words : WordData A B N
  g_pos : 0 < g
  a_ge : 2 ≤ a
  c_ge : 2 ≤ c
  coprime : Nat.Coprime a c
  wg_lt : wg < g
  root₁ : RootWords A B N (a * g) (b * g + wg) ha₁ hb₁
  root₂ : RootWords A B N (c * g) (d * g + wg) ha₂ hb₂
  A0_bit : ∀ j, j < g → A0 j = 0 ∨ A0 j = 1
  B0_bit : ∀ j, j < g → B0 j = 0 ∨ B0 j = 1
  genA : IsGenericWord A A0 N g (a * g) (c * g) ha₁ ha₂
  genB : IsGenericWord B B0 N g (a * g) (c * g) hb₁ hb₂

theorem lcm_dvd_of_coprime {a c g z : ℕ} (hg : 0 < g) (hcop : Nat.Coprime a c)
    (h1 : a * g ∣ z) (h2 : c * g ∣ z) : a * c * g ∣ z := by
  obtain ⟨z1, rfl⟩ : g ∣ z := Dvd.dvd.trans (Dvd.intro_left a rfl) h1
  have h1' : a ∣ z1 := by
    have : a * g ∣ z1 * g := by rwa [mul_comm z1 g]
    exact Nat.dvd_of_mul_dvd_mul_right hg this
  have h2' : c ∣ z1 := by
    have : c * g ∣ z1 * g := by rwa [mul_comm z1 g]
    exact Nat.dvd_of_mul_dvd_mul_right hg this
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1' h2'
  obtain ⟨u, hu⟩ := this
  exact ⟨u, by rw [hu]; ring⟩


/-- **`eq:gluing-pinch-equations`** for both roots of a `GcdPair`, with
`Δ = ∑_{j<g} C_j`, `ε = C_0`, `P_{w_g} = ∑_{j=1}^{w_g} C_j` and `δ` the sum of the two initial
deviations of the root: `b Δ + P_{w_g} + δ = 0` and `a Δ - ε + δ = 0` with `0 ≤ δ ≤ 2`. -/
theorem GcdPair.pinch_equations {A B A0 B0 : ℕ → ℤ} {N g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ}
    (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) :
    (b * genSum (incr A0 B0 g) g + genSum (incr A0 B0 g) wg +
        (devA A0 g ha₁ + devB B0 g hb₁) = 0 ∧
      a * genSum (incr A0 B0 g) g - (A0 0 - B0 0) + (devA A0 g ha₁ + devB B0 g hb₁) = 0 ∧
      0 ≤ devA A0 g ha₁ + devB B0 g hb₁ ∧ devA A0 g ha₁ + devB B0 g hb₁ ≤ 2) ∧
    (d * genSum (incr A0 B0 g) g + genSum (incr A0 B0 g) wg +
        (devA A0 g ha₂ + devB B0 g hb₂) = 0 ∧
      c * genSum (incr A0 B0 g) g - (A0 0 - B0 0) + (devA A0 g ha₂ + devB B0 g hb₂) = 0 ∧
      0 ≤ devA A0 g ha₂ + devB B0 g hb₂ ∧ devA A0 g ha₂ + devB B0 g hb₂ ≤ 2) := by
  have hg := h.g_pos
  have gA1 : ∀ x, 1 ≤ x → x < a * g → x < N → x ≠ ha₁ → A x = A0 (x % g) := by
    intro x hx1 hx2 hx3 hx4
    apply h.genA x hx1 hx3
    rintro ⟨h1, -⟩
    rw [Nat.mod_eq_of_lt hx2] at h1; exact hx4 h1
  have gB1 : ∀ x, 1 ≤ x → x < a * g → x < N → x ≠ hb₁ → B x = B0 (x % g) := by
    intro x hx1 hx2 hx3 hx4
    apply h.genB x hx1 hx3
    rintro ⟨h1, -⟩
    rw [Nat.mod_eq_of_lt hx2] at h1; exact hx4 h1
  have gA2 : ∀ x, 1 ≤ x → x < c * g → x < N → x ≠ ha₂ → A x = A0 (x % g) := by
    intro x hx1 hx2 hx3 hx4
    apply h.genA x hx1 hx3
    rintro ⟨-, h1⟩
    rw [Nat.mod_eq_of_lt hx2] at h1; exact hx4 h1
  have gB2 : ∀ x, 1 ≤ x → x < c * g → x < N → x ≠ hb₂ → B x = B0 (x % g) := by
    intro x hx1 hx2 hx3 hx4
    apply h.genB x hx1 hx3
    rintro ⟨-, h1⟩
    rw [Nat.mod_eq_of_lt hx2] at h1; exact hx4 h1
  obtain ⟨E1, E2⟩ := chart_eqs hg (by have := h.a_ge; omega) h.root₁ gA1 gB1
  obtain ⟨E1', E2'⟩ := chart_eqs hg (by have := h.c_ge; omega) h.root₂ gA2 gB2
  have bA : ∀ y, A0 (y % g) = 0 ∨ A0 (y % g) = 1 := fun y => h.A0_bit _ (Nat.mod_lt _ hg)
  have bB : ∀ y, B0 (y % g) = 0 ∨ B0 (y % g) = 1 := fun y => h.B0_bit _ (Nat.mod_lt _ hg)
  obtain ⟨dA1a, dA1b⟩ := devA_bounds (g := g) (ha := ha₁) (bA ha₁)
  obtain ⟨dB1a, dB1b⟩ := devB_bounds (g := g) (hb := hb₁) (bB hb₁)
  obtain ⟨dA2a, dA2b⟩ := devA_bounds (g := g) (ha := ha₂) (bA ha₂)
  obtain ⟨dB2a, dB2b⟩ := devB_bounds (g := g) (hb := hb₂) (bB hb₂)
  exact ⟨⟨E1, E2, by linarith, by linarith⟩, ⟨E1', E2', by linarith, by linarith⟩⟩

/-- The initial half of the drift lemma. -/
theorem GcdPair.drift {A B A0 B0 : ℕ → ℤ} {N g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ}
    (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) :
    genSum (incr A0 B0 g) g = 0 ∧
    (A0 0 - B0 0 = 0 ∨ A0 0 - B0 0 = 1) ∧
    genSum (incr A0 B0 g) wg = -(A0 0 - B0 0) ∧
    (∀ x, wg < x → x < max (a * g) (c * g) → x < N → A x = A0 (x % g) ∧ B x = B0 (x % g)) ∧
    heightWord A B wg = 1 ∧ heightWord A B (g - 1) = 1 := by
  have hg := h.g_pos
  have ha2 := h.a_ge
  have hc2 := h.c_ge
  have gA1 : ∀ x, 1 ≤ x → x < a * g → x < N → x ≠ ha₁ → A x = A0 (x % g) := by
    intro x hx1 hx2 hx3 hx4
    apply h.genA x hx1 hx3
    rintro ⟨h1, -⟩
    rw [Nat.mod_eq_of_lt hx2] at h1; exact hx4 h1
  have gB1 : ∀ x, 1 ≤ x → x < a * g → x < N → x ≠ hb₁ → B x = B0 (x % g) := by
    intro x hx1 hx2 hx3 hx4
    apply h.genB x hx1 hx3
    rintro ⟨h1, -⟩
    rw [Nat.mod_eq_of_lt hx2] at h1; exact hx4 h1
  have gA2 : ∀ x, 1 ≤ x → x < c * g → x < N → x ≠ ha₂ → A x = A0 (x % g) := by
    intro x hx1 hx2 hx3 hx4
    apply h.genA x hx1 hx3
    rintro ⟨-, h1⟩
    rw [Nat.mod_eq_of_lt hx2] at h1; exact hx4 h1
  have gB2 : ∀ x, 1 ≤ x → x < c * g → x < N → x ≠ hb₂ → B x = B0 (x % g) := by
    intro x hx1 hx2 hx3 hx4
    apply h.genB x hx1 hx3
    rintro ⟨-, h1⟩
    rw [Nat.mod_eq_of_lt hx2] at h1; exact hx4 h1
  obtain ⟨E1, E2⟩ := chart_eqs hg (by omega) h.root₁ gA1 gB1
  obtain ⟨E1', E2'⟩ := chart_eqs hg (by omega) h.root₂ gA2 gB2
  have bA : ∀ y, A0 (y % g) = 0 ∨ A0 (y % g) = 1 := fun y => h.A0_bit _ (Nat.mod_lt _ hg)
  have bB : ∀ y, B0 (y % g) = 0 ∨ B0 (y % g) = 1 := fun y => h.B0_bit _ (Nat.mod_lt _ hg)
  obtain ⟨dA1a, dA1b⟩ := devA_bounds (g := g) (ha := ha₁) (bA ha₁)
  obtain ⟨dB1a, dB1b⟩ := devB_bounds (g := g) (hb := hb₁) (bB hb₁)
  obtain ⟨dA2a, dA2b⟩ := devA_bounds (g := g) (ha := ha₂) (bA ha₂)
  obtain ⟨dB2a, dB2b⟩ := devB_bounds (g := g) (hb := hb₂) (bB hb₂)
  have hA00 : A0 0 = 0 ∨ A0 0 = 1 := by simpa using bA 0
  have hB00 : B0 0 = 0 ∨ B0 0 = 1 := by simpa using bB 0
  have key := drift_arith h.a_ge h.c_ge h.coprime E2 E2' (ε := A0 0 - B0 0)
    (by rcases hA00 with h | h <;> rcases hB00 with h' | h' <;> simp [h, h'])
    (by rcases hA00 with h | h <;> rcases hB00 with h' | h' <;> simp [h, h'])
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  have huniq : ∀ (h₁ h₂ : ℕ) x y, 1 ≤ x → x < a * c * g → 1 ≤ y → y < a * c * g →
      (x % (a * g) = h₁ ∧ x % (c * g) = h₂) → (y % (a * g) = h₁ ∧ y % (c * g) = h₂) → x = y := by
    intro h₁ h₂ x y hx1 hx2 hy1 hy2 ⟨hx3, hx4⟩ ⟨hy3, hy4⟩
    have main : ∀ x y, x ≤ y → y < a * c * g → (x % (a * g) = h₁ ∧ x % (c * g) = h₂) →
        (y % (a * g) = h₁ ∧ y % (c * g) = h₂) → x = y := by
      intro x y hxy hy ⟨hx3, hx4⟩ ⟨hy3, hy4⟩
      have d1 : a * g ∣ y - x :=
        (Nat.modEq_iff_dvd' hxy).mp (show x ≡ y [MOD a * g] by unfold Nat.ModEq; rw [hx3, hy3])
      have d2 : c * g ∣ y - x :=
        (Nat.modEq_iff_dvd' hxy).mp (show x ≡ y [MOD c * g] by unfold Nat.ModEq; rw [hx4, hy4])
      have := Nat.eq_zero_of_dvd_of_lt (lcm_dvd_of_coprime hg h.coprime d1 d2) (by omega)
      omega
    rcases le_total x y with hxy | hxy
    · exact main x y hxy hy2 ⟨hx3, hx4⟩ ⟨hy3, hy4⟩
    · exact (main y x hxy hx2 ⟨hy3, hy4⟩ ⟨hx3, hx4⟩).symm
  rcases key with hΔ | ⟨hΔ, hε, hac⟩
  swap
  · exfalso
    have h6 : 6 * g ≤ N := by
      have n1 := h.root₁.two_q_le
      have n2 := h.root₂.two_q_le
      rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    have hacg : a * c * g = 6 * g := by
      rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring
    have hH := h.words.pos (6 * g - 1) (by omega)
    rw [height_split A B A0 B0 g] at hH
    have s1 : ∑ i ∈ Finset.range (6 * g - 1), (A (i + 1) - A0 ((i + 1) % g)) ≤ 1 :=
      (dev_sum_le (f := fun x => A x - A0 (x % g)) (N := N) (L := a * c * g)
        (SH := fun x => x % (a * g) = ha₁ ∧ x % (c * g) = ha₂) (huniq ha₁ ha₂)
        (fun x hx1 hx2 hS => sub_eq_zero.mpr (h.genA x hx1 hx2 hS))
        (fun x hx1 hx2 => by
          have := (h.words.bits x hx1 hx2).1
          rcases this with h1 | h1 <;> rcases bA x with h2 | h2 <;> simp [h1, h2])
        (6 * g - 1) (by omega) (by omega)).1
    have s2 : ∑ i ∈ Finset.range (6 * g - 1), (B0 ((i + 1) % g) - B (i + 1)) ≤ 1 :=
      (dev_sum_le (f := fun x => B0 (x % g) - B x) (N := N) (L := a * c * g)
        (SH := fun x => x % (a * g) = hb₁ ∧ x % (c * g) = hb₂) (huniq hb₁ hb₂)
        (fun x hx1 hx2 hS => sub_eq_zero.mpr (h.genB x hx1 hx2 hS).symm)
        (fun x hx1 hx2 => by
          have := (h.words.bits x hx1 hx2).2
          rcases this with h1 | h1 <;> rcases bB x with h2 | h2 <;> simp [h1, h2])
        (6 * g - 1) (by omega) (by omega)).1
    have e6 := genSum_mul_pred A0 B0 hg (a := 6) (by norm_num)
    rw [hΔ, hε] at e6
    push_cast at e6
    linarith
  · have hε : A0 0 - B0 0 = 0 ∨ A0 0 - B0 0 = 1 := by
      have := E2; rw [hΔ] at this; omega
    have hδ₁ : devA A0 g ha₁ + devB B0 g hb₁ = A0 0 - B0 0 := by
      rw [hΔ] at E2; linarith
    have hδ₂ : devA A0 g ha₂ + devB B0 g hb₂ = A0 0 - B0 0 := by
      rw [hΔ] at E2'; linarith
    have hP : genSum (incr A0 B0 g) wg = -(A0 0 - B0 0) := by
      rw [hΔ] at E1; linarith
    have hP' : genSum (incr A0 B0 g) wg = -(A0 0 - B0 0) := by
      rw [hΔ] at E1'; linarith
    obtain ⟨c1, p1, q1⟩ := chart_final hg (by omega) h.wg_lt h.words h.root₁ gA1 gB1 h.A0_bit
      h.B0_bit hΔ hP hδ₁
    obtain ⟨c2, p2, q2⟩ := chart_final hg (by omega) h.wg_lt h.words h.root₂ gA2 gB2 h.A0_bit
      h.B0_bit hΔ hP' hδ₂
    refine ⟨hΔ, hε, hP, ?_, p1, q1⟩
    intro x hx1 hx2 hx3
    by_cases hxa : x < a * g
    · exact c1 x hx1 hxa hx3
    · exact c2 x hx1 (by omega) hx3


/-! ### Reversal of the words -/

/-- The word `W` read backwards from the end: the position `x` carries `W (N - x)`. -/
def revWord (N : ℕ) (W : ℕ → ℤ) (x : ℕ) : ℤ := W (N - x)

/-- Heights of the reversed words. -/
theorem heightWord_rev {A B : ℕ → ℤ} {N : ℕ} (hN : 1 ≤ N) (hlast : heightWord A B (N - 1) = 1) :
    ∀ k, k ≤ N - 1 → heightWord (revWord N B) (revWord N A) k = heightWord A B (N - 1 - k) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [show N - 1 - 0 = N - 1 by rfl, hlast]
    simp [heightWord]
  | succ k ih =>
    intro hk
    rw [heightWord_succ, ih (by omega)]
    have e : N - 1 - k = (N - 1 - (k + 1)) + 1 := by omega
    rw [e, heightWord_succ]
    have e2 : N - 1 - (k + 1) + 1 = N - (k + 1) := by omega
    unfold revWord
    rw [e2]
    ring

/-- Reversal preserves `WordData`. -/
theorem WordData.reverse {A B : ℕ → ℤ} {N : ℕ} (hN : 1 ≤ N) (h : WordData A B N) :
    WordData (revWord N B) (revWord N A) N := by
  refine ⟨fun k hk1 hk2 => ?_, fun k hk => ?_, ?_⟩
  · have := h.bits (N - k) (by omega) (by omega)
    exact ⟨this.2, this.1⟩
  · rw [heightWord_rev hN h.last k (by omega)]
    exact h.pos _ (by omega)
  · rw [heightWord_rev hN h.last (N - 1) le_rfl]
    simp [heightWord]

/-- Reversal exchanges the initial and terminal caps: the reversed words have the exceptional
residues `w - hb` and `w - ha`. -/
theorem RootWords.reverse {A B : ℕ → ℤ} {N q w ha hb : ℕ} (hword : WordData A B N)
    (h : RootWords A B N q w ha hb) :
    RootWords (revWord N B) (revWord N A) N q w (w - hb) (w - ha) := by
  have hN2 := h.two_q_le
  have hwq := h.hwq
  have hN : 1 ≤ N := by omega
  have hh1 := h.ha_le
  have hh2 := h.hb_le
  have hr := heightWord_rev hN hword.last
  refine ⟨hwq, h.rep, by omega, by omega, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_,
    fun h1 => ?_, ?_, ?_, ?_, ?_⟩
  · unfold revWord
    have e : N - (w - hb) = N - w + hb := by omega
    rw [e]; exact h.capB_term (by omega)
  · unfold revWord
    have e : N - (w - ha) = N - w + ha := by omega
    rw [e]; exact h.capA_term (by omega)
  · unfold revWord
    have e : N - (N - w + (w - hb)) = hb := by omega
    rw [e]; exact h.capB_init (by omega)
  · unfold revWord
    have e : N - (N - w + (w - ha)) = ha := by omega
    rw [e]; exact h.capA_init (by omega)
  · rw [hr w (by omega)]; exact h.sing_Nw
  · rw [hr (q - 1) (by omega), show N - 1 - (q - 1) = N - q by omega]; exact h.sing_Nq
  · rw [hr (N - 1 - w) (by omega), show N - 1 - (N - 1 - w) = w by omega]; exact h.sing_w
  · rw [hr (N - q) (by omega), show N - 1 - (N - q) = q - 1 by omega]; exact h.sing_q

/-- Reflection of a residue under `x ↦ N - x`, for `N = r m + w`. -/
theorem reflect_mod {m N r w hb x : ℕ} (hwm : w < m) (hbw : hb ≤ w)
    (hN : N = r * m + w) (hx : x ≤ N) (h : (N - x) % m = hb) : x % m = w - hb := by
  have h1 : (N - x) + x = N := by omega
  have h2 : (N - x) ≡ hb [MOD m] := by
    unfold Nat.ModEq; rw [h, Nat.mod_eq_of_lt (by omega)]
  have h3 : N ≡ w [MOD m] := by
    unfold Nat.ModEq; rw [hN, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hwm]
  have h4 : hb + x ≡ hb + (w - hb) [MOD m] := by
    have := h2.add_right x
    rw [h1] at this
    have h5 : hb + (w - hb) = w := by omega
    rw [h5]
    exact this.symm.trans h3
  have h6 := Nat.ModEq.add_left_cancel' hb h4
  unfold Nat.ModEq at h6
  rw [h6, Nat.mod_eq_of_lt (by omega)]


theorem sub_mod_mod {N g x : ℕ} (hx : x ≤ N) (hxg : x % g ≤ N) :
    (N - x) % g = (N - x % g) % g := by
  have h1 : (N - x) + x = N := by omega
  have h2 : (N - x % g) + x % g = N := by omega
  have h3 : x ≡ x % g [MOD g] := (Nat.mod_modEq x g).symm
  have h4 : (N - x) + x ≡ (N - x % g) + x % g [MOD g] := by rw [h1, h2]
  have h5 : (N - x) + x ≡ (N - x % g) + x [MOD g] := by
    have := h3.add_left (N - x % g)
    exact h4.trans this.symm
  exact Nat.ModEq.add_right_cancel' x h5

theorem GcdPair.N_mod {A B A0 B0 : ℕ → ℤ} {N g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ}
    (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) : N % g = wg := by
  obtain ⟨r, -, hr⟩ := h.root₁.rep
  have : N = (r * a + b) * g + wg := by rw [hr]; ring
  rw [this, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt h.wg_lt]

/-- Reversing the words of a `GcdPair` gives a `GcdPair`, with generic bits read backwards. -/
theorem GcdPair.reverse {A B A0 B0 : ℕ → ℤ} {N g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ}
    (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) :
    GcdPair (revWord N B) (revWord N A) (fun j => B0 ((N - j) % g))
      (fun j => A0 ((N - j) % g)) N g a b c d wg ((b * g + wg) - hb₁) ((b * g + wg) - ha₁)
      ((d * g + wg) - hb₂) ((d * g + wg) - ha₂) := by
  have hg := h.g_pos
  have hN2 := h.root₁.two_q_le
  have hag : 1 ≤ a * g := Nat.mul_pos (by have := h.a_ge; omega) hg
  have hN : 1 ≤ N := by omega
  obtain ⟨r₁, -, hr₁⟩ := h.root₁.rep
  obtain ⟨r₂, -, hr₂⟩ := h.root₂.rep
  have hxg : ∀ x, x % g ≤ N := fun x => by
    have := Nat.mod_lt x hg
    have : g ≤ a * g := Nat.le_mul_of_pos_left g (by have := h.a_ge; omega)
    omega
  refine ⟨h.words.reverse hN, hg, h.a_ge, h.c_ge, h.coprime, h.wg_lt,
    RootWords.reverse h.words h.root₁, RootWords.reverse h.words h.root₂,
    fun j _ => h.B0_bit _ (Nat.mod_lt _ hg), fun j _ => h.A0_bit _ (Nat.mod_lt _ hg), ?_, ?_⟩
  · intro x hx1 hx2 hnot
    have hxN : x ≤ N := by omega
    change B (N - x) = B0 ((N - x % g) % g)
    rw [← sub_mod_mod hxN (hxg x)]
    refine h.genB (N - x) (by omega) (by omega) ?_
    rintro ⟨e1, e2⟩
    apply hnot
    exact ⟨reflect_mod h.root₁.hwq h.root₁.hb_le hr₁ hxN e1,
      reflect_mod h.root₂.hwq h.root₂.hb_le hr₂ hxN e2⟩
  · intro x hx1 hx2 hnot
    have hxN : x ≤ N := by omega
    change A (N - x) = A0 ((N - x % g) % g)
    rw [← sub_mod_mod hxN (hxg x)]
    refine h.genA (N - x) (by omega) (by omega) ?_
    rintro ⟨e1, e2⟩
    apply hnot
    exact ⟨reflect_mod h.root₁.hwq h.root₁.ha_le hr₁ hxN e1,
      reflect_mod h.root₂.hwq h.root₂.ha_le hr₂ hxN e2⟩


/-- **The drift lemma at the level of words** (`lem:gluing-ordinary-drift`).  For two ordinary
roots in the setting `GcdPair`, with `C_j = A⁰_j - B⁰_j`: `Δ = ∑_{j<g} C_j = 0`, the initial budget
`ε = C_0` is a bit and `P_{w_g} = ∑_{j=1}^{w_g} C_j = -ε`, the terminal budget `-C_{w_g}` is a bit,
the words are generic past the first `w_g` and before the last `w_g` steps (off the first `max`
period), and the four pinches `H_{w_g} = H_{g-1} = H_{N-g} = H_{N-w_g-1} = 1` hold. -/
theorem GcdPair.drift_full {A B A0 B0 : ℕ → ℤ} {N g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ}
    (h : GcdPair A B A0 B0 N g a b c d wg ha₁ hb₁ ha₂ hb₂) :
    genSum (incr A0 B0 g) g = 0 ∧ (A0 0 - B0 0 = 0 ∨ A0 0 - B0 0 = 1) ∧
    genSum (incr A0 B0 g) wg = -(A0 0 - B0 0) ∧ (B0 wg - A0 wg = 0 ∨ B0 wg - A0 wg = 1) ∧
    (∀ x, wg < x → x < max (a * g) (c * g) → x < N → A x = A0 (x % g) ∧ B x = B0 (x % g)) ∧
    (∀ y, N < y + max (a * g) (c * g) → y + wg < N →
      A y = A0 (y % g) ∧ B y = B0 (y % g)) ∧
    heightWord A B wg = 1 ∧ heightWord A B (g - 1) = 1 ∧ heightWord A B (N - g) = 1 ∧
    heightWord A B (N - 1 - wg) = 1 := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h.drift
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h.reverse.drift
  have hg := h.g_pos
  have hN2 := h.root₁.two_q_le
  have hN2' := h.root₂.two_q_le
  have hwg := h.wg_lt
  have hag : g ≤ a * g := Nat.le_mul_of_pos_left g (by have := h.a_ge; omega)
  have hNg := h.N_mod
  have hN := h.words.last
  have hlast : heightWord A B (N - 1) = 1 := h.words.last
  have hr := heightWord_rev (by omega : 1 ≤ N) hlast
  refine ⟨d1, d2, d3, ?_, d4, ?_, d5, d6, ?_, ?_⟩
  · have : (N - 0) % g = wg := by simpa using hNg
    simp only [this] at e2
    rcases e2 with e | e
    · left; linarith
    · right; linarith
  · intro y hy1 hy2
    have := e4 (N - y) (by omega) (by omega) (by omega)
    unfold revWord at this
    rw [show N - (N - y) = y by omega] at this
    have hm : (N - (N - y) % g) % g = y % g := by
      rw [← sub_mod_mod (by omega) (by have := Nat.mod_lt (N - y) hg; omega)]
      rw [show N - (N - y) = y by omega]
    rw [hm] at this
    exact ⟨this.2, this.1⟩
  · have := e6
    rw [hr (g - 1) (by omega)] at this
    rwa [show N - 1 - (g - 1) = N - g by omega] at this
  · have := e5
    rwa [hr wg (by omega)] at this


/-- Heights only read the words on the positions up to the index. -/
theorem heightWord_congr {A B A' B' : ℕ → ℤ} {n : ℕ}
    (h : ∀ x, 1 ≤ x → x ≤ n → A x = A' x ∧ B x = B' x) :
    heightWord A B n = heightWord A' B' n := by
  unfold heightWord
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have := h (i + 1) (by omega) (by omega)
  rw [this.1, this.2]

/-- `WordData` and `RootWords` only read the words on `1, …, N - 1`. -/
theorem WordData.congr {A B A' B' : ℕ → ℤ} {N : ℕ}
    (h : ∀ x, 1 ≤ x → x < N → A x = A' x ∧ B x = B' x) (hw : WordData A B N) :
    WordData A' B' N := by
  refine ⟨fun k hk1 hk2 => ?_, fun k hk => ?_, ?_⟩
  · have := h k hk1 hk2
    rw [← this.1, ← this.2]; exact hw.bits k hk1 hk2
  · rw [← heightWord_congr (fun x hx1 hx2 => h x hx1 (by omega))]; exact hw.pos k hk
  · rw [← heightWord_congr (fun x hx1 hx2 => h x hx1 (by omega))]; exact hw.last

theorem RootWords.congr {A B A' B' : ℕ → ℤ} {N q w ha hb : ℕ}
    (h : ∀ x, 1 ≤ x → x < N → A x = A' x ∧ B x = B' x) (hr : RootWords A B N q w ha hb) :
    RootWords A' B' N q w ha hb := by
  have hN2 := hr.two_q_le
  have hq := hr.hwq
  have hh1 := hr.ha_le
  have hh2 := hr.hb_le
  have hc : ∀ n, n < N → heightWord A B n = heightWord A' B' n := fun n hn =>
    heightWord_congr (fun x hx1 hx2 => h x hx1 (by omega))
  refine ⟨hq, hr.rep, hh1, hh2, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← (h ha h1 (by omega)).1]; exact hr.capA_init h1
  · rw [← (h hb h1 (by omega)).2]; exact hr.capB_init h1
  · rw [← (h (N - w + ha) (by omega) (by omega)).1]; exact hr.capA_term h1
  · rw [← (h (N - w + hb) (by omega) (by omega)).2]; exact hr.capB_term h1
  · rw [← hc w (by omega)]; exact hr.sing_w
  · rw [← hc (q - 1) (by omega)]; exact hr.sing_q
  · rw [← hc (N - 1 - w) (by omega)]; exact hr.sing_Nw
  · rw [← hc (N - q) (by omega)]; exact hr.sing_Nq

end OrdinaryDrift
end SkewGluing
