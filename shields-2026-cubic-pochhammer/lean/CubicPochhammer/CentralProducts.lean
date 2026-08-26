/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The central-product characterization of log-concavity

Formalizes `shields-2026-cubic-pochhammer.tex`, `sec:reduction` «Exact
reduction to a residue kernel», `lem:central-products` and
`eq:central-products`: for
a nonnegative sequence `(f_n)_{n≥1}`,

  `f` is log-concave with no internal zeros
    ⟺  for every `m ≥ 2`, `f_k f_{m-k} ≤ f_{k+1} f_{m-k-1}` for `1 ≤ k < ⌊m/2⌋`.

The right-hand condition is the anti-diagonal chain the weights `w_k = f_k
f_{m-k}` of `eq:w-from-f` need, and is the degree-local form of
`rem:local-weight`; it is what `Main.turan_coeff_nonneg` consumes, so this module
is what lets a reader holding the paper's own sequence hypothesis instantiate
`thm:main`.

Forward direction: the ratio `ρ_j = f_{j+1}/f_j` is nonincreasing where it is
defined, which `ratio_antitone` states division-free as
`f_{l+1} f_k ≤ f_{k+1} f_l`.  Interval support supplies the positivity that makes
the cancellation legal, and the vanishing case is immediate.  Converse:
`m = 2j+2`, `k = j` gives log-concavity, and `m = a+b`, `k = a` pushes positivity
inward from both ends, filling every gap by induction on `c - a`.

Sorry-free, no project axioms.

## Main definitions

* `LogConcaveSeq` --- `f_j f_{j+2} ≤ f_{j+1}^2` for a sequence indexed from `1`.
* `IntervalSupport` --- the positive support is an interval: no internal zeros.
* `CentralProducts` --- the anti-diagonal chain `eq:central-products`.

## Main statements

* `centralProducts_of_logConcave`, `intervalSupport_of_centralProducts`,
  `logConcaveSeq_of_centralProducts` --- the two directions, in the pieces the
  induction needs them.
* `centralProducts_iff` --- `lem:central-products`: the equivalence itself.

## References

* `shields-2026-cubic-pochhammer.tex`, `sec:reduction` «Exact reduction to a
  residue kernel»: `lem:central-products`, `eq:central-products`,
  `eq:w-from-f`, `rem:local-weight`.
-/

namespace CubicPochhammer

/-- Log-concavity of a sequence indexed from `1`: `f_j f_{j+2} ≤ f_{j+1}^2`. -/
def LogConcaveSeq (f : ℕ → ℝ) : Prop :=
  ∀ j, 1 ≤ j → f j * f (j + 2) ≤ f (j + 1) * f (j + 1)

/-- No internal zeros: the positive support is an interval. -/
def IntervalSupport (f : ℕ → ℝ) : Prop :=
  ∀ a b c : ℕ, 1 ≤ a → a ≤ b → b ≤ c → 0 < f a → 0 < f c → 0 < f b

/-- The anti-diagonal chain `eq:central-products`: for every `m`, the products
`f_k f_{m-k}` are nondecreasing as `k` moves toward `m/2`. -/
def CentralProducts (f : ℕ → ℝ) : Prop :=
  ∀ m k : ℕ, 1 ≤ k → k < m / 2 → f k * f (m - k) ≤ f (k + 1) * f (m - k - 1)

variable {f : ℕ → ℝ}

/-- The ratio `ρ_j = f_{j+1}/f_j` is nonincreasing, stated division-free: for
`k ≤ l` with `f` positive on `[k,l]`, `f_{l+1} f_k ≤ f_{k+1} f_l`.  Induction on
`l`, the step multiplying the previous bound by `f_{l+2}` and canceling the
positive `f_{l+1}`. -/
theorem ratio_antitone (hnn : ∀ n, 0 ≤ f n) (hlc : LogConcaveSeq f)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) (hpos : ∀ j, k ≤ j → j ≤ l → 0 < f j) :
    f (l + 1) * f k ≤ f (k + 1) * f l := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hl ih =>
    have hih := ih (fun j hj1 hj2 => hpos j hj1 (by omega))
    have hlcl : f l * f (l + 2) ≤ f (l + 1) * f (l + 1) := hlc l (by omega)
    have hpl : 0 < f (l + 1) := hpos (l + 1) (by omega) (by omega)
    have s1 : f (l + 2) * (f (l + 1) * f k) ≤ f (l + 2) * (f (k + 1) * f l) :=
      mul_le_mul_of_nonneg_left hih (hnn (l + 2))
    have s2 : f (k + 1) * (f l * f (l + 2)) ≤ f (k + 1) * (f (l + 1) * f (l + 1)) :=
      mul_le_mul_of_nonneg_left hlcl (hnn (k + 1))
    have hchain : f (l + 1) * (f (l + 1 + 1) * f k) ≤ f (l + 1) * (f (k + 1) * f (l + 1)) := by
      have hsucc : l + 1 + 1 = l + 2 := rfl
      rw [hsucc]; nlinarith [s1, s2]
    exact le_of_mul_le_mul_left hchain hpl

/-- **`lem:central-products`, (1) ⇒ (2)** at one index (`eq:central-products`).
If `f_k f_{m-k} = 0` the inequality is immediate; otherwise interval support
gives `f_j > 0` for `k ≤ j ≤ m-k`, and `ratio_antitone` at `l = m-k-1` is the
claim. -/
theorem centralProducts_of_logConcave (hnn : ∀ n, 0 ≤ f n)
    (hlc : LogConcaveSeq f) (hint : IntervalSupport f) :
    CentralProducts f := by
  intro m k hk hkm
  rcases (hnn k).lt_or_eq with hfk | hfk
  · rcases (hnn (m - k)).lt_or_eq with hfmk | hfmk
    · have hkl : k ≤ m - k - 1 := by omega
      have hpos : ∀ j, k ≤ j → j ≤ m - k - 1 → 0 < f j := fun j h1 h2 =>
        hint k j (m - k) hk h1 (by omega) hfk hfmk
      have := ratio_antitone hnn hlc hk hkl hpos
      rw [show m - k - 1 + 1 = m - k from by omega] at this
      linarith [this]
    · rw [← hfmk, mul_zero]
      exact mul_nonneg (hnn _) (hnn _)
  · rw [← hfk, zero_mul]
    exact mul_nonneg (hnn _) (hnn _)

/-- The chain form `turan_coeff_nonneg` consumes: the anti-diagonal products are
nondecreasing from any `i` up to `⌊m/2⌋`.  Iterating
`centralProducts_of_logConcave`. -/
theorem centralProducts_chain (h : CentralProducts f) (m : ℕ) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → f i * f (m - i) ≤ f j * f (m - j) := by
  intro i j hi hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hj ih =>
    intro hjm
    have hstep := h m j (by omega) (by omega)
    rw [show m - j - 1 = m - (j + 1) from by omega] at hstep
    exact le_trans (ih (by omega)) hstep

/-- **`lem:central-products`, (2) ⇒ (1)**, log-concavity half: `m = 2j+2`,
`k = j`. -/
theorem logConcaveSeq_of_centralProducts (h : CentralProducts f) :
    LogConcaveSeq f := by
  intro j hj
  have := h (2 * j + 2) j hj (by omega)
  rw [show 2 * j + 2 - j = j + 2 from by omega, show j + 2 - 1 = j + 1 from by omega] at this
  exact this

/-- The inward step of the support half: from `f_a, f_c > 0` with `c ≥ a+2`,
`m = a+c` and `k = a` give `f_a f_c ≤ f_{a+1} f_{c-1}`, so both inward neighbors
are positive. -/
private theorem support_step (hnn : ∀ n, 0 ≤ f n) (h : CentralProducts f)
    {a c : ℕ} (ha : 1 ≤ a) (hac : a + 2 ≤ c) (hfa : 0 < f a) (hfc : 0 < f c) :
    0 < f (a + 1) ∧ 0 < f (c - 1) := by
  have hkey := h (a + c) a ha (by omega)
  rw [show a + c - a = c from by omega] at hkey
  have hprod : 0 < f (a + 1) * f (c - 1) := lt_of_lt_of_le (mul_pos hfa hfc) hkey
  constructor
  · rcases (hnn (a + 1)).lt_or_eq with hx | hx
    · exact hx
    · rw [← hx, zero_mul] at hprod; exact absurd hprod (lt_irrefl 0)
  · rcases (hnn (c - 1)).lt_or_eq with hx | hx
    · exact hx
    · rw [← hx, mul_zero] at hprod; exact absurd hprod (lt_irrefl 0)

/-- **`lem:central-products`, (2) ⇒ (1)**, interval-support half: iterating
`support_step` fills every gap between two positive terms.  Induction on the
width `c - a`. -/
theorem intervalSupport_of_centralProducts (hnn : ∀ n, 0 ≤ f n)
    (h : CentralProducts f) : IntervalSupport f := by
  have hfill : ∀ d a b c : ℕ, c - a ≤ d → 1 ≤ a → a ≤ b → b ≤ c →
      0 < f a → 0 < f c → 0 < f b := by
    intro d
    induction d with
    | zero =>
      intro a b c hd _ hab hbc hfa _
      rw [show b = a from by omega]; exact hfa
    | succ d ih =>
      intro a b c hd ha hab hbc hfa hfc
      rcases eq_or_lt_of_le hab with hb | hb
      · rw [← hb]; exact hfa
      rcases eq_or_lt_of_le hbc with hb' | hb'
      · rw [hb']; exact hfc
      obtain ⟨hfa1, hfc1⟩ := support_step hnn h ha (by omega) hfa hfc
      exact ih (a + 1) b (c - 1) (by omega) (by omega) (by omega) (by omega) hfa1 hfc1
  intro a b c ha hab hbc hfa hfc
  exact hfill (c - a) a b c le_rfl ha hab hbc hfa hfc

/-- **`lem:central-products`**, both directions, as `eq:central-products`.  For a nonnegative
sequence, log-concavity together with interval support is equivalent to the
anti-diagonal chain `eq:central-products`. -/
theorem centralProducts_iff (hnn : ∀ n, 0 ≤ f n) :
    (LogConcaveSeq f ∧ IntervalSupport f) ↔ CentralProducts f :=
  ⟨fun ⟨hlc, hint⟩ => centralProducts_of_logConcave hnn hlc hint,
   fun h => ⟨logConcaveSeq_of_centralProducts h, intervalSupport_of_centralProducts hnn h⟩⟩

end CubicPochhammer
