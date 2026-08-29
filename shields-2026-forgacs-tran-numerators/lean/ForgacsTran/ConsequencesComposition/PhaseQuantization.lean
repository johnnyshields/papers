/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Consequences
import ForgacsTran.MainComposition
import ForgacsTran.EventualDegree
import ForgacsTran.PhaseVariation

/-!
# The angular window, and the phase quantization on it

`sec:consequences` on the proven count, first half: the counting inequalities the
zero laws are read off, the angular window as a set of zeros of the phase, and
`eq:local-phase-quantization` on that window.  The signs are resolved explicitly
rather than assumed, because the window is where the cosine changes sign and the
quantization is exactly the statement that it does so once per zero.

## Main statements

* `count_lower_of_phase_turning`, `angular_discrepancy_of_counts`,
  `equidistribution_of_counts`, `angular_clock_of_bracketing` — the counting
  inequalities `sec:consequences` reads its global laws off, stated over bare
  real bounds so that nothing analytic enters them.
* the statements of `### The angular window as a set of zeros` — the window is a
  zero set of the phase, which is what makes the count a cardinality.
* the statements of `### subsec:strong-clock` and
  `### prop:local-strong-clock` — the rate the spacing law claims, and the first
  display of its proof, with its two hypotheses met at the real objects.
* the statements of `### The window, with its signs resolved` and
  `### Two consecutive zeros, jointly` — the sign bookkeeping, and the pair of
  consecutive zeros the spacing statement is about.
* the statements of `### eq:local-phase-quantization, the quantitative half`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero laws» —
  `sec:consequences`, `subsec:strong-clock`, `prop:local-strong-clock`,
  `eq:local-phase-quantization`.

## Tags

angular window, phase quantization, clock spacing, zero counting, sign resolution
-/

namespace ForgacsTran

open Real

/-- **The count in one angular window.**  `PhaseCount.exists_interiorZeros_of_dominance`
returns at least `L/π - 2` distinct zeros whenever `Φ` turns by `L` across
the window; `eq:Phi-def` makes that turning at least
`(M+1)(β-α) - V` with `V` the variation of `ψ`, which is
`cor:linear-phase-variation`.  This is the arithmetic in between. -/
theorem count_lower_of_phase_turning {Zcard : ℕ} {n : ℕ} {L V α β : ℝ} {M : ℕ}
    (hn : L / π - 2 ≤ (n : ℝ)) (hZ : n ≤ Zcard)
    (hturn : ((M : ℝ) + 1) * (β - α) - V ≤ L) :
    ((M : ℝ) + 1) * (β - α) / π - (V / π + 2) ≤ (Zcard : ℝ) := by
  have hπ : (0 : ℝ) < π := pi_pos
  have hZr : (n : ℝ) ≤ (Zcard : ℝ) := by exact_mod_cast hZ
  have hdiv : (((M : ℝ) + 1) * (β - α) - V) / π ≤ L / π := by gcongr
  have hsplit : (((M : ℝ) + 1) * (β - α) - V) / π
      = ((M : ℝ) + 1) * (β - α) / π - V / π := by ring
  linarith [hn, hZr, hdiv, hsplit ▸ hdiv]

/-- **`eq:angular-discrepancy`, both sides.**  The lower bound on the window is
the count itself; the upper bound is the same count on the two complementary
windows, subtracted from the degree.  `C₁` is the window's own defect, `C₂` the
complement's, and `C₃` the gap between `deg F_M` and the total angular measure
— `lem:eventual-degree` gives `deg F_M = ⌊ M/r⌋`, so `C₃` is the
rounding.

This is exactly the paper's own upper-bound argument: "apply
`eq:angular-distinct-lower` to the two complementary angular intervals". -/
theorem angular_discrepancy_of_counts {Zin Zout D T Tab C₁ C₂ C₃ : ℝ}
    (hin : Tab - C₁ ≤ Zin) (hout : (T - Tab) - C₂ ≤ Zout)
    (hsum : Zin + Zout ≤ D) (hD : D ≤ T + C₃) :
    |Zin - Tab| ≤ max C₁ (C₂ + C₃) := by
  rw [abs_le]
  constructor
  · have : Tab - Zin ≤ C₁ := by linarith
    have := le_max_left C₁ (C₂ + C₃)
    linarith
  · have : Zin - Tab ≤ C₂ + C₃ := by linarith
    have := le_max_right C₁ (C₂ + C₃)
    linarith

/-- **`eq:normalized-angular-discrepancy` on the proven count.**  The two-sided
discrepancy of `angular_discrepancy_of_counts` fed to
`Consequences.equidistribution_of_angular_discrepancy`: dividing by
`deg F_M = ⌊ M/r⌋` costs one unit, and what is left is the
normalized statement of `prop:equidistribution`. -/
theorem equidistribution_of_counts {Zin Zout D T Tab C₁ C₂ C₃ α β : ℝ} {M r d s : ℕ}
    (hr : 1 ≤ r) (hd : 1 ≤ d) (hM : M = r * d + s) (hs : s < r)
    (hab : 0 ≤ β - α) (hab' : β - α ≤ π / r)
    (hTab : Tab = ((M : ℝ) + 1) * (β - α) / π)
    (hin : Tab - C₁ ≤ Zin) (hout : (T - Tab) - C₂ ≤ Zout)
    (hsum : Zin + Zout ≤ D) (hD : D ≤ T + C₃) :
    |Zin / (d : ℝ) - (r : ℝ) * (β - α) / π| ≤ (max C₁ (C₂ + C₃) + 1) / (d : ℝ) := by
  refine equidistribution_of_angular_discrepancy hr hd hM hs hab hab' ?_
  rw [← hTab]
  exact angular_discrepancy_of_counts hin hout hsum hD

/-- **`eq:angular-clock` on the proven count.**  `Consequences.angular_rigidity`
carries the discrepancy from two bracketing indices to every index between them,
and `Consequences.angular_clock` turns the index bound into the angular one at
`L = M + 1`: every bulk-zero angle sits within `π(Δ+1)/(M+1)` of the
uniform clock `π j/(M+1)`. -/
theorem angular_clock_of_bracketing {jm jp j M : ℕ} {θ Δ : ℝ}
    (hjm : |(jm : ℝ) - ((M : ℝ) + 1) * θ / π| ≤ Δ)
    (hjp : |(jp : ℝ) - ((M : ℝ) + 1) * θ / π| ≤ Δ)
    (h1 : jm < j) (h2 : j ≤ jp) :
    |θ - π * (j : ℝ) / ((M : ℝ) + 1)| ≤ π * (Δ + 1) / ((M : ℝ) + 1) :=
  angular_clock (by positivity) (angular_rigidity hjm hjp h1 h2)


/-! ### The angular window as a set of zeros

`angular_discrepancy_of_counts` and its two corollaries are stated over abstract
reals.  What follows instantiates them at `F_M`: the counts become root counts of
the coefficient polynomial inside the `z`-image of an angular window, the degree
becomes `lem:eventual-degree`'s `⌊ M/r⌋`, and the disjointness the
upper bound needs is read off the strict monotonicity of `z`. -/

/-- **Paper `eq:angular-subinterval`.**  The image `z(I_{α,β})` of an
angular window, as a subset of `ℂ` — the set the zeros of `F_M` are
counted in. -/
def ftWindow (z : ℝ → ℝ) (α β : ℝ) : Set ℂ := Complex.ofReal '' (z '' Set.Ioo α β)

/-- A window sits inside the whole angular interval, which is
`AngularBookkeeping.subset_ftInterval_image` pushed through `Complex.ofReal`. -/
theorem ftWindow_subset {z : ℝ → ℝ} {c d α β : ℝ} (hcα : c ≤ α) (hβd : β ≤ d) :
    ftWindow z α β ⊆ ftWindow z c d :=
  Set.image_mono (subset_ftInterval_image hcα hβd)

/-- Windows over disjoint angular intervals are disjoint, because `z` is
injective there.  This is the only geometric input the upper half of
`eq:angular-discrepancy` needs: the complementary windows must not re-count the
zeros the inner window already carries. -/
theorem notMem_ftWindow {z : ℝ → ℝ} {s : Set ℝ} (hz : Set.InjOn z s)
    {p q p' q' : ℝ} (h : Set.Ioo p q ⊆ s) (h' : Set.Ioo p' q' ⊆ s)
    (hd : ∀ x ∈ Set.Ioo p q, x ∉ Set.Ioo p' q')
    {w : ℂ} (hw : w ∈ ftWindow z p q) : w ∉ ftWindow z p' q' := by
  intro hw'
  obtain ⟨y, hy, hyw⟩ := hw
  obtain ⟨θ, hθ, hθy⟩ := hy
  obtain ⟨y', hy', hyw'⟩ := hw'
  obtain ⟨θ', hθ', hθy'⟩ := hy'
  have hyy : y = y' := by
    have : ((y : ℝ) : ℂ) = ((y' : ℝ) : ℂ) := by rw [hyw, hyw']
    exact_mod_cast this
  have hzz : z θ = z θ' := by rw [hθy, hyy, hθy']
  have : θ = θ' := hz (h hθ) (h' hθ') hzz
  exact hd θ hθ (this ▸ hθ')

/-- **The half-open angular window `z(I_{α,β}]`.**  `cor:angular-rigidity`
brackets a zero's index between the number of interval zeros of angle *strictly*
below `θ` and the number of angle *at most* `θ`; the first is `ftWindow z a θ`
and the second is `ftWindowIoc z a θ`.  The two differ by the zeros at the angle
`θ` itself, which is exactly the multiple zero the bracketing localizes. -/
def ftWindowIoc (z : ℝ → ℝ) (α β : ℝ) : Set ℂ := Complex.ofReal '' (z '' Set.Ioc α β)

theorem ftWindow_subset_ftWindowIoc {z : ℝ → ℝ} {α β : ℝ} :
    ftWindow z α β ⊆ ftWindowIoc z α β :=
  Set.image_mono (Set.image_mono Set.Ioo_subset_Ioc_self)

/-- Windows over disjoint angular sets are disjoint when `z` is injective across
them.  `notMem_ftWindow` is the case of two open intervals; the bracketing of
`cor:angular-rigidity` needs one of them half-open. -/
theorem notMem_image_of_disjoint {z : ℝ → ℝ} {s A B : Set ℝ} (hz : Set.InjOn z s)
    (hA : A ⊆ s) (hB : B ⊆ s) (hd : ∀ x ∈ A, x ∉ B)
    {w : ℂ} (hw : w ∈ Complex.ofReal '' (z '' A)) :
    w ∉ Complex.ofReal '' (z '' B) := by
  intro hw'
  obtain ⟨y, hy, hyw⟩ := hw
  obtain ⟨θ, hθ, hθy⟩ := hy
  obtain ⟨y', hy', hyw'⟩ := hw'
  obtain ⟨θ', hθ', hθy'⟩ := hy'
  have hyy : y = y' := by
    have : ((y : ℝ) : ℂ) = ((y' : ℝ) : ℂ) := by rw [hyw, hyw']
    exact_mod_cast this
  have hzz : z θ = z θ' := by rw [hθy, hyy, hθy']
  exact hd θ hθ (hz (hA hθ) (hB hθ') hzz ▸ hθ')

/-- The multiplicity count is monotone in the window, which is what carries the
lower half of `eq:angular-discrepancy` from the open window to the half-open
one. -/
theorem count_filter_mono {P : Polynomial ℂ} {A B : Set ℂ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (hAB : A ⊆ B) :
    Multiset.card (P.roots.filter (· ∈ A))
      ≤ Multiset.card (P.roots.filter (· ∈ B)) := by
  refine Multiset.card_le_card (Multiset.monotone_filter_right _ ?_)
  intro w hw
  exact hAB hw

/-- **`lem:eventual-degree` against the angular measure.**  `deg F_M = ⌊ M/r⌋`
is at most `(M+1)|I_{Q,r}|/π` when the whole angular interval has length
`π/r`, so the `C_3` of `angular_discrepancy_of_counts` — the gap between the
degree and the total angular measure — is zero and the rounding costs nothing. -/
theorem natDegree_le_angular_measure (M : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    ((M / r : ℕ) : ℝ) ≤ ((M : ℝ) + 1) * (π / r) / π := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have h2 : ((M : ℝ) + 1) * (π / r) / π = ((M : ℝ) + 1) / r := by
    field_simp
  have h1 : ((M / r : ℕ) : ℝ) ≤ (M : ℝ) / (r : ℝ) := Nat.cast_div_le
  rw [h2]
  refine le_trans h1 ?_
  exact div_le_div_of_nonneg_right (by linarith) hr0.le

/-- **`eq:angular-discrepancy` at the paper's objects.**  The two-sided bound of
`angular_discrepancy_of_counts`, with the counts instantiated as root counts of
the coefficient polynomial: the inner count is
`\#\{w : F_M(w) = 0,\ w ∈ z(I_{α,β})\}` with multiplicity, and the
outer one is the two complementary windows, which
`PhaseCount.count_add_card_le_natDegree` subtracts from the degree.

The zeros the two complementary windows contribute are genuinely new, because
`z` is injective on the angular interval — that is `notMem_ftWindow`, and it is
what makes "apply `eq:angular-distinct-lower` to the two complementary angular
intervals" a proof rather than a slogan.

`hin` names both objects the conclusion relates, so the mechanical containment
check fires here and is a false positive: `hin` is `eq:angular-distinct-lower`
on the inner window, one side of a two-sided bound, and it cannot imply the
other.  Delete `hout` and the statement is false — nothing then stops the inner
count from exceeding `T_{αβ}` without limit.  The upper side is
`hout`, `hsum` and `hD` together, and it is where the degree enters. -/
theorem ft_angular_discrepancy {P : Polynomial ℂ} (hP : P ≠ 0) {z : ℝ → ℝ}
    {a b α β T Tab C₁ C₂ C₃ : ℝ}
    (hzinj : Set.InjOn z (Set.Ioo a b))
    (haα : a ≤ α) (hαβ : α ≤ β) (hβb : β ≤ b)
    [DecidablePred (· ∈ ftWindow z α β)]
    {Zlo Zhi : Finset ℂ}
    (hlo : ∀ w ∈ Zlo, P.IsRoot w) (hlomem : ∀ w ∈ Zlo, w ∈ ftWindow z a α)
    (hhi : ∀ w ∈ Zhi, P.IsRoot w) (hhimem : ∀ w ∈ Zhi, w ∈ ftWindow z β b)
    (hin : Tab - C₁ ≤ (Multiset.card (P.roots.filter (· ∈ ftWindow z α β)) : ℝ))
    (hout : T - Tab - C₂ ≤ (Zlo.card : ℝ) + (Zhi.card : ℝ))
    (hD : (P.natDegree : ℝ) ≤ T + C₃) :
    |(Multiset.card (P.roots.filter (· ∈ ftWindow z α β)) : ℝ) - Tab|
      ≤ max C₁ (C₂ + C₃) := by
  classical
  have hab : a ≤ b := le_trans haα (le_trans hαβ hβb)
  have hIlo : Set.Ioo a α ⊆ Set.Ioo a b :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le (lt_of_lt_of_le hx.2 hαβ) hβb⟩
  have hIin : Set.Ioo α β ⊆ Set.Ioo a b :=
    fun x hx => ⟨lt_of_le_of_lt haα hx.1, lt_of_lt_of_le hx.2 hβb⟩
  have hIhi : Set.Ioo β b ⊆ Set.Ioo a b :=
    fun x hx => ⟨lt_of_le_of_lt (le_trans haα hαβ) hx.1, hx.2⟩
  -- the complementary windows carry no zero of the inner one
  have hnotlo : ∀ w ∈ Zlo, w ∉ ftWindow z α β := fun w hw =>
    notMem_ftWindow hzinj hIlo hIin (fun x hx hx' => absurd (lt_of_lt_of_le hx.2 hx'.1.le)
      (lt_irrefl _)) (hlomem w hw)
  have hnothi : ∀ w ∈ Zhi, w ∉ ftWindow z α β := fun w hw =>
    notMem_ftWindow hzinj hIhi hIin (fun x hx hx' => absurd (lt_of_lt_of_le hx'.2 hx.1.le)
      (lt_irrefl _)) (hhimem w hw)
  -- and they carry none of each other's
  have hdisjU : Disjoint Zlo Zhi := by
    refine Finset.disjoint_left.mpr fun w hw hw' => ?_
    exact notMem_ftWindow hzinj hIlo hIhi
      (fun x hx hx' => absurd (lt_of_lt_of_le (lt_of_lt_of_le hx.2 hαβ) hx'.1.le)
        (lt_irrefl _)) (hlomem w hw) (hhimem w hw')
  have hcard : (Zlo ∪ Zhi).card = Zlo.card + Zhi.card := Finset.card_union_of_disjoint hdisjU
  have hroots : ∀ w ∈ Zlo ∪ Zhi, P.IsRoot w := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact hlo w h
    · exact hhi w h
  have hout' : ∀ w ∈ Zlo ∪ Zhi, w ∉ ftWindow z α β := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact hnotlo w h
    · exact hnothi w h
  have hsumN := count_add_card_le_natDegree hP (ftWindow z α β) hroots hout'
  rw [hcard] at hsumN
  have hsum : (Multiset.card (P.roots.filter (· ∈ ftWindow z α β)) : ℝ)
      + ((Zlo.card : ℝ) + (Zhi.card : ℝ)) ≤ (P.natDegree : ℝ) := by
    exact_mod_cast hsumN
  exact angular_discrepancy_of_counts hin hout hsum hD

/-- **`prop:equidistribution` at the paper's objects.**
`eq:normalized-angular-discrepancy` for the zeros of `F_M`: normalized by
`deg F_M = ⌊ M/r⌋` — which `EventualDegree.eventual_natDegree_eq`
supplies for all large `M` — the count in `z(I_{α,β})` tracks the
uniform density `r(β-α)/π` with an error `O(1/d)`.

The angular interval is `(0,π/r)`, so `T = (M+1)/r` and the degree gap `C_3` of
`ft_angular_discrepancy` vanishes: `⌊ M/r⌋ ≤ (M+1)/r` outright. -/
theorem ft_equidistribution {P : Polynomial ℂ} (hP : P ≠ 0) {z : ℝ → ℝ}
    {a b α β C₁ C₂ : ℝ} {M r d s : ℕ}
    (hr : 1 ≤ r) (hd : 1 ≤ d) (hM : M = r * d + s) (hs : s < r)
    (hdeg : P.natDegree = M / r) (hlen : b - a = π / r)
    (hzinj : Set.InjOn z (Set.Ioo a b))
    (haα : a ≤ α) (hαβ : α ≤ β) (hβb : β ≤ b)
    [DecidablePred (· ∈ ftWindow z α β)]
    {Zlo Zhi : Finset ℂ}
    (hlo : ∀ w ∈ Zlo, P.IsRoot w) (hlomem : ∀ w ∈ Zlo, w ∈ ftWindow z a α)
    (hhi : ∀ w ∈ Zhi, P.IsRoot w) (hhimem : ∀ w ∈ Zhi, w ∈ ftWindow z β b)
    (hin : ((M : ℝ) + 1) * (β - α) / π - C₁
      ≤ (Multiset.card (P.roots.filter (· ∈ ftWindow z α β)) : ℝ))
    (hout : ((M : ℝ) + 1) * (b - a) / π - ((M : ℝ) + 1) * (β - α) / π - C₂
      ≤ (Zlo.card : ℝ) + (Zhi.card : ℝ)) :
    |(Multiset.card (P.roots.filter (· ∈ ftWindow z α β)) : ℝ) / (d : ℝ)
        - (r : ℝ) * (β - α) / π|
      ≤ (max C₁ C₂ + 1) / (d : ℝ) := by
  have hdeg' : (P.natDegree : ℝ) ≤ ((M : ℝ) + 1) * (b - a) / π + 0 := by
    rw [hdeg, hlen, add_zero]
    exact natDegree_le_angular_measure M hr
  have hdisc := ft_angular_discrepancy (C₃ := 0) hP hzinj haα hαβ hβb hlo hlomem hhi hhimem
    hin hout hdeg'
  rw [add_zero] at hdisc
  refine equidistribution_of_angular_discrepancy hr hd hM hs (by linarith) ?_ hdisc
  rw [← hlen]
  linarith

/-- **`cor:angular-rigidity` at the paper's objects.**  Bracketing the index of a
bulk zero between the counts on `z(I_{a,θ})` and `z(I_{a,θ'})` and
feeding both discrepancies to `angular_clock_of_bracketing` gives
`eq:angular-clock` for the zeros of `F_M` themselves. -/
theorem ft_angular_clock {P : Polynomial ℂ} {z : ℝ → ℝ} {a θ θ' : ℝ} {M j : ℕ} {Δ : ℝ}
    [DecidablePred (· ∈ ftWindow z a θ)] [DecidablePred (· ∈ ftWindow z a θ')]
    (hm : |(Multiset.card (P.roots.filter (· ∈ ftWindow z a θ)) : ℝ)
        - ((M : ℝ) + 1) * θ / π| ≤ Δ)
    (hp : |(Multiset.card (P.roots.filter (· ∈ ftWindow z a θ')) : ℝ)
        - ((M : ℝ) + 1) * θ / π| ≤ Δ)
    (h1 : Multiset.card (P.roots.filter (· ∈ ftWindow z a θ)) < j)
    (h2 : j ≤ Multiset.card (P.roots.filter (· ∈ ftWindow z a θ'))) :
    |θ - π * (j : ℝ) / ((M : ℝ) + 1)| ≤ π * (Δ + 1) / ((M : ℝ) + 1) :=
  angular_clock_of_bracketing hm hp h1 h2

/-- **`eq:angular-clock` with a numerator-uniform defect** — `thm:main` clause 3's
shape applied to `cor:angular-rigidity`.  When the defect is
`PhaseVariation.NumeratorUniform`, the clock's slack prints as
`π(E_0 + E_1deg B_N + 1)/(M+1)` with `E_0`, `E_1` fixed before the numerator,
which is what makes the rigidity statement uniform over the numerator family
rather than over one weight at a time. -/
theorem ft_angular_clock_numeratorUniform {Q : Polynomial ℝ} {r : ℕ}
    {Fdef : Polynomial (Polynomial ℝ) → ℕ} (hFU : NumeratorUniform Q r Fdef) :
    ∃ E₀ E₁ : ℕ, ∀ (N : Polynomial (Polynomial ℝ)) (M j : ℕ) (θ : ℝ)
      {P : Polynomial ℂ} {z : ℝ → ℝ} {a θ' : ℝ}
      [DecidablePred (· ∈ ftWindow z a θ)] [DecidablePred (· ∈ ftWindow z a θ')],
      |(Multiset.card (P.roots.filter (· ∈ ftWindow z a θ)) : ℝ)
          - ((M : ℝ) + 1) * θ / π| ≤ (Fdef N : ℝ) →
      |(Multiset.card (P.roots.filter (· ∈ ftWindow z a θ')) : ℝ)
          - ((M : ℝ) + 1) * θ / π| ≤ (Fdef N : ℝ) →
      Multiset.card (P.roots.filter (· ∈ ftWindow z a θ)) < j →
      j ≤ Multiset.card (P.roots.filter (· ∈ ftWindow z a θ')) →
      |θ - π * (j : ℝ) / ((M : ℝ) + 1)|
        ≤ π * (((E₀ : ℝ) + (E₁ : ℝ) * ((laurentWeight Q r N).natDegree : ℝ)) + 1)
            / ((M : ℝ) + 1) := by
  obtain ⟨E₀, E₁, hE⟩ := hFU
  refine ⟨E₀, E₁, fun N M j θ P z a θ' _ _ hm hp h1 h2 => ?_⟩
  have hclock := ft_angular_clock hm hp h1 h2
  refine le_trans hclock ?_
  have hbd : (Fdef N : ℝ)
      ≤ (E₀ : ℝ) + (E₁ : ℝ) * ((laurentWeight Q r N).natDegree : ℝ) := by
    have := hE N
    exact_mod_cast this
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  exact div_le_div_of_nonneg_right (by nlinarith [pi_pos]) hM.le

/-! ### `subsec:strong-clock` — the rate the spacing law claims -/

/-- **`eq:local-strong-clock`'s error is `O(M^{-3})`.**  `local_clock_spacing`
returns the spacing error in the raw form
`(2E + κ_2\barΔ^2)/(L-κ) + πκ^2/(L^2(L-κ))`.  With
`L = M+1` and the phase error `E` exponentially small, that collapses to the
`O_{Q,r,B,𝒥(M^{-3})` the proposition states: the two `κ` terms are
cubic in `1/L` outright, and the `E` term beats every power.

The constant is exhibited rather than existential — `1` for the exponential
term, `8κ_2(π+2A)^2` for the Taylor term and `2πκ^2` for the
curvature term — so nothing about it depends on `M`. -/
private theorem clock_rate_aux {L κ κ₂ A E c : ℝ} (_hκ : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂)
    (hA : 0 ≤ A) (hE0 : 0 ≤ E) (hEA : E ≤ A) (hL1 : 1 ≤ L) (hκL : 2 * κ ≤ L)
    (_hc0 : 0 ≤ c) (hEc : E ≤ A * c) (hgeom : 4 * A * (L ^ 2 * c) ≤ 1) :
    (2 * E + κ₂ * ((π + 2 * E) / (L - κ)) ^ 2) / (L - κ)
        + π * κ ^ 2 / (L ^ 2 * (L - κ))
      ≤ (1 + 8 * κ₂ * (π + 2 * A) ^ 2 + 2 * π * κ ^ 2) / L ^ 3 := by
  have hπ : (0 : ℝ) < π := pi_pos
  have hL0 : (0 : ℝ) < L := by linarith
  have hhalf : L / 2 ≤ L - κ := by linarith
  have hLκ0 : (0 : ℝ) < L - κ := by linarith
  have hterm1 : 2 * E / (L - κ) ≤ 1 / L ^ 3 := by
    rw [div_le_div_iff₀ hLκ0 (by positivity)]
    have hL3 : (0 : ℝ) ≤ L ^ 3 := by positivity
    have h1 : 2 * E * L ^ 3 ≤ 2 * (A * c) * L ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) hL3
    calc 2 * E * L ^ 3 ≤ 2 * (A * c) * L ^ 3 := h1
      _ = (4 * A * (L ^ 2 * c)) * (L / 2) := by ring
      _ ≤ 1 * (L / 2) := mul_le_mul_of_nonneg_right hgeom (by linarith)
      _ ≤ 1 * (L - κ) := by linarith
  have hcube2 : L ^ 3 ≤ 8 * (L - κ) ^ 3 := by
    have h := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ L / 2) hhalf 3
    have hh : (L / 2) ^ 3 = L ^ 3 / 8 := by ring
    rw [hh] at h; linarith
  have hterm2 : κ₂ * ((π + 2 * E) / (L - κ)) ^ 2 / (L - κ)
      ≤ 8 * κ₂ * (π + 2 * A) ^ 2 / L ^ 3 := by
    have hrw : κ₂ * ((π + 2 * E) / (L - κ)) ^ 2 / (L - κ)
        = κ₂ * (π + 2 * E) ^ 2 / (L - κ) ^ 3 := by
      rw [div_pow]; field_simp
    rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (π + 2 * E) ^ 2 ≤ (π + 2 * A) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hL3 : (0 : ℝ) ≤ L ^ 3 := by positivity
    have hcoef : (0 : ℝ) ≤ κ₂ * (π + 2 * A) ^ 2 := by positivity
    calc κ₂ * (π + 2 * E) ^ 2 * L ^ 3 ≤ κ₂ * (π + 2 * A) ^ 2 * L ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hκ₂) hL3
      _ ≤ κ₂ * (π + 2 * A) ^ 2 * (8 * (L - κ) ^ 3) :=
          mul_le_mul_of_nonneg_left hcube2 hcoef
      _ = 8 * κ₂ * (π + 2 * A) ^ 2 * (L - κ) ^ 3 := by ring
  have hterm3 : π * κ ^ 2 / (L ^ 2 * (L - κ)) ≤ 2 * π * κ ^ 2 / L ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hstep := mul_le_mul_of_nonneg_left hhalf (sq_nonneg L)
    have heq : L ^ 3 = 2 * (L ^ 2 * (L / 2)) := by ring
    have hcube : L ^ 3 ≤ 2 * (L ^ 2 * (L - κ)) := by rw [heq]; linarith
    have hcoef : (0 : ℝ) ≤ π * κ ^ 2 := by positivity
    calc π * κ ^ 2 * L ^ 3 ≤ π * κ ^ 2 * (2 * (L ^ 2 * (L - κ))) :=
          mul_le_mul_of_nonneg_left hcube hcoef
      _ = 2 * π * κ ^ 2 * (L ^ 2 * (L - κ)) := by ring
  have hsplit : (2 * E + κ₂ * ((π + 2 * E) / (L - κ)) ^ 2) / (L - κ)
      = 2 * E / (L - κ) + κ₂ * ((π + 2 * E) / (L - κ)) ^ 2 / (L - κ) := by
    rw [add_div]
  have hsum : 1 / L ^ 3 + 8 * κ₂ * (π + 2 * A) ^ 2 / L ^ 3 + 2 * π * κ ^ 2 / L ^ 3
      = (1 + 8 * κ₂ * (π + 2 * A) ^ 2 + 2 * π * κ ^ 2) / L ^ 3 := by ring
  rw [hsplit, ← hsum]
  linarith [hterm1, hterm2, hterm3]

/-- **`eq:local-strong-clock`'s error is `O(M^{-3})`.**  `local_clock_spacing`
returns the spacing error in the raw form
`(2E + κ_2\barΔ^2)/(L-κ) + πκ^2/(L^2(L-κ))`.  With
`L = M+1` and the phase error `E` exponentially small, that collapses to the
`O_{Q,r,B,𝒥(M^{-3})` the proposition states: the two `κ` terms are
cubic in `1/L` outright, and the `E` term beats every power.

The constant is exhibited rather than existential — `1` for the exponential
term, `8κ_2(π+2A)^2` for the Taylor term and `2πκ^2` for the
curvature term — so nothing in it moves with `M`. -/
theorem local_clock_rate {κ κ₂ A σ : ℝ} (hκ : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂) (hA : 0 ≤ A)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ E : ℝ, 0 ≤ E → E ≤ A * σ ^ M →
      (2 * E + κ₂ * ((π + 2 * E) / (((M : ℝ) + 1) - κ)) ^ 2) / (((M : ℝ) + 1) - κ)
          + π * κ ^ 2 / (((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 1) - κ))
        ≤ (1 + 8 * κ₂ * (π + 2 * A) ^ 2 + 2 * π * κ ^ 2) / ((M : ℝ) + 1) ^ 3 := by
  obtain ⟨M₁, hM₁⟩ :=
    exists_succ_pow_mul_geometric_le (K := 4 * A) hσ0 hσ1 (by positivity) one_pos 2
  refine ⟨max M₁ ⌈2 * κ⌉₊, fun M hM E hE0 hEA => ?_⟩
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hκL : 2 * κ ≤ (M : ℝ) + 1 := by
    have h1 : (⌈2 * κ⌉₊ : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast le_trans (le_max_right M₁ _) hM
    have := Nat.le_ceil (2 * κ)
    linarith
  have hσp : (0 : ℝ) ≤ σ ^ M := by positivity
  have hσ1p : σ ^ M ≤ 1 := pow_le_one₀ hσ0 hσ1.le
  have hEA' : E ≤ A := le_trans hEA (by nlinarith)
  exact clock_rate_aux hκ hκ₂ hA hE0 hEA' (by linarith) hκL hσp hEA
    (hM₁ M (le_trans (le_max_left _ _) hM))

/-- **`eq:numerator-clock-correction` along the Forgács--Tran branch.**  The
principal amplitude factors as `W = B(γ)· D` with `D` the
denominator-only factor — for `ftAmp` that is
`D(s) = -1/∂_tD(z(s))(γ(s))`, which is what `hDeq` records — so
`Consequences.numerator_clock_correction` splits `ψ' = Im(W'/W)` into a
numerator term and a term in which `B` does not appear.  That split is why the
leading clock of `eq:local-strong-clock` is denominator-universal and the weight
first enters at order `M^{-2}`.

`hDeq` is an identity, not an analytic input: it fixes `D` as `W/B(γ)`.
What the caller still owes is `hD`, the derivative of that factor. -/
theorem ft_clock_correction {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {D : ℝ → ℂ}
    {γ' D' : ℂ} {θ : ℝ}
    (hDeq : ∀ s : ℝ, ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)
      = B.eval (ftPrincipal τ s) * D s)
    (hγ : HasDerivAt (ftPrincipal τ) γ' θ) (hD : HasDerivAt D D' θ)
    (hB0 : B.eval (ftPrincipal τ θ) ≠ 0) (hD0 : D θ ≠ 0) :
    (deriv (fun s : ℝ => ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)) θ
        / ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)).im
      = ((B.derivative.eval (ftPrincipal τ θ) * γ') / B.eval (ftPrincipal τ θ)).im
        + (D' / D θ).im := by
  have hfun : (fun s : ℝ => ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s))
      = fun s : ℝ => B.eval (ftPrincipal τ s) * D s := funext hDeq
  rw [hfun, hDeq θ]
  exact numerator_clock_correction hγ hD hB0 hD0

/-! ### `prop:local-strong-clock` — the first display of its proof

`G_M(θ) = 2|W(θ)|cosΦ_M(θ) + R_M(θ)` on a compact
zero-free subarc.  The tree carries the two halves separately and in the wrong
shape for each other: the principal term as `2Re(Wζ^{-M-1})`, which is what
the sign alternation of `prop:angular-discrepancy` consumes, and the remainder as
`ftRemainder`, a *norm*.  What the strong clock needs is a signed real equation
`cosΦ_M + e_M = 0` with `e_M` small, because that is the shape
`Consequences.exists_unique_zero_near_phase_point` localizes a zero in. -/

/-- **The principal term in cosine form.**  With `t_+ = τ e^{iθ}` the
normalization `τ^{M+1}/t_+^{M+1}` is `e^{-i(M+1)θ}`
(`Amplitude.ofReal_pow_div_principal_pow`), so the pair's contribution
`2Re(Wζ^{-M-1})` of `eq:principal-decomposition` is `2|W|cosΦ_M` with
`Φ_M = (M+1)θ - ψ` of `eq:Phi-def`. -/
theorem principal_term_cos {Q B : Polynomial ℂ} {r M : ℕ} {z τ ψ : ℝ → ℝ} {θ : ℝ}
    (hτ : 0 < τ θ)
    (hpolar : ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
      = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I)) :
    2 * ((((τ θ : ℝ) : ℂ)) ^ (M + 1)
        * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
            / (ftPrincipal τ θ) ^ (M + 1))).re
      = 2 * ftPrincipalAmp Q B r z τ θ * Real.cos (((M : ℝ) + 1) * θ - ψ θ) := by
  have hnorm : (((τ θ : ℝ) : ℂ)) ^ (M + 1) / (ftPrincipal τ θ) ^ (M + 1)
      = Complex.exp (((-(((M : ℝ) + 1) * θ) : ℝ) : ℂ) * Complex.I) := by
    rw [ftPrincipal]
    exact ofReal_pow_div_principal_pow hτ
  have hprod : (((τ θ : ℝ) : ℂ)) ^ (M + 1)
      * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) / (ftPrincipal τ θ) ^ (M + 1))
      = ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
          * ((((τ θ : ℝ) : ℂ)) ^ (M + 1) / (ftPrincipal τ θ) ^ (M + 1)) := by
    ring
  have harg : ((ψ θ : ℝ) : ℂ) * Complex.I
      + ((-(((M : ℝ) + 1) * θ) : ℝ) : ℂ) * Complex.I
      = (((ψ θ - ((M : ℝ) + 1) * θ : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hprod, hnorm, hpolar, mul_assoc, ← Complex.exp_add, harg,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    ← Real.cos_neg (ψ θ - ((M : ℝ) + 1) * θ), neg_sub]
  ring

/-- **The remainder in signed real form.**  `ftRemainder` is the *modulus* of the
difference between the normalized coefficient and the principal term.  Taking
real parts loses nothing that matters: the real error in the cosine equation is
bounded by that modulus, because `|Re w| ≤ \|w\|`. -/
theorem abs_interior_cos_error_le {Q B : Polynomial ℂ} {r M : ℕ} {z τ ψ : ℝ → ℝ} {θ : ℝ}
    (hτ : 0 < τ θ)
    (hpolar : ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
      = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I)) :
    |((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
        - 2 * ftPrincipalAmp Q B r z τ θ * Real.cos (((M : ℝ) + 1) * θ - ψ θ)|
      ≤ ftRemainder Q B r z τ M θ := by
  have hcos := principal_term_cos (M := M) hτ hpolar
  have hre : ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
      - 2 * ftPrincipalAmp Q B r z τ θ * Real.cos (((M : ℝ) + 1) * θ - ψ θ)
      = ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)
          - ((2 * ((((τ θ : ℝ) : ℂ)) ^ (M + 1)
              * (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
                  / (ftPrincipal τ θ) ^ (M + 1))).re : ℝ) : ℂ)).re := by
    rw [Complex.sub_re, Complex.ofReal_re, hcos]
  rw [hre, ftRemainder]
  exact Complex.abs_re_le_norm _

/-- **`prop:local-strong-clock`, the first display.**  On a subarc where the
amplitude does not vanish, the normalized coefficient is `cosΦ_M` plus an
error controlled by the contour remainder relative to `2|W|` — the equation whose
zeros `Consequences.exists_unique_zero_near_phase_point` localizes, one to a
phase point.

The hypotheses are met at the real objects: `hpolar` is the polar form
`MainComposition`'s branch data already carries, `hτ` is
`thm:FT-geometry`'s positivity of the principal modulus, and `hW` is the floor
`Amplitude`'s compactness argument gives on a compact zero-free subarc — no
window deletion, because the deleted windows of `eq:amplitude-deletion` exist to
handle the amplitude's *zeros* and this subarc has none. -/
theorem interior_cos_decomposition {Q B : Polynomial ℂ} {r M : ℕ} {z τ ψ : ℝ → ℝ} {θ : ℝ}
    (hτ : 0 < τ θ) (hW : 0 < ftPrincipalAmp Q B r z τ θ)
    (hpolar : ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
      = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I)) :
    ∃ e : ℝ,
      ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
          / (2 * ftPrincipalAmp Q B r z τ θ)
        = Real.cos (((M : ℝ) + 1) * θ - ψ θ) + e ∧
      |e| ≤ ftRemainder Q B r z τ M θ / (2 * ftPrincipalAmp Q B r z τ θ) := by
  have h2W : (0 : ℝ) < 2 * ftPrincipalAmp Q B r z τ θ := by linarith
  refine ⟨(((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
      - 2 * ftPrincipalAmp Q B r z τ θ * Real.cos (((M : ℝ) + 1) * θ - ψ θ))
      / (2 * ftPrincipalAmp Q B r z τ θ), ?_, ?_⟩
  · field
  · rw [abs_div, abs_of_pos h2W]
    exact div_le_div_of_nonneg_right (abs_interior_cos_error_le hτ hpolar) h2W.le

/-- **The error is `O(σ^M)`, uniformly on the subarc.**  Composing the
decomposition with `DominanceFTSupply.interior_remainder_uniform`'s bound and the
amplitude floor: the constant is `C_I/(2A)` and the ratio is the interior
`σ`, neither carrying `M`.  This is `eq:C1-interior-remainder`'s `C^0` half
in the coordinate the quantization runs in. -/
theorem interior_cos_error_geometric {Q B : Polynomial ℂ} {r M : ℕ} {z τ ψ : ℝ → ℝ}
    {θ CI A σ : ℝ} (hτ : 0 < τ θ) (hA : 0 < A) (_hσ : 0 ≤ σ)
    (hW : A ≤ ftPrincipalAmp Q B r z τ θ)
    (hrem : |ftRemainder Q B r z τ M θ| ≤ CI * σ ^ M)
    (hpolar : ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
      = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I)) :
    ∃ e : ℝ,
      ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
          / (2 * ftPrincipalAmp Q B r z τ θ)
        = Real.cos (((M : ℝ) + 1) * θ - ψ θ) + e ∧
      |e| ≤ CI / (2 * A) * σ ^ M := by
  have hWpos : 0 < ftPrincipalAmp Q B r z τ θ := lt_of_lt_of_le hA hW
  obtain ⟨e, heq, hle⟩ := interior_cos_decomposition (M := M) hτ hWpos hpolar
  refine ⟨e, heq, le_trans hle ?_⟩
  have hrem' : ftRemainder Q B r z τ M θ ≤ CI * σ ^ M :=
    le_trans (le_abs_self _) hrem
  have hnn : (0 : ℝ) ≤ ftRemainder Q B r z τ M θ := norm_nonneg _
  have hCI : (0 : ℝ) ≤ CI * σ ^ M := le_trans hnn hrem'
  calc ftRemainder Q B r z τ M θ / (2 * ftPrincipalAmp Q B r z τ θ)
      ≤ CI * σ ^ M / (2 * ftPrincipalAmp Q B r z τ θ) :=
        div_le_div_of_nonneg_right hrem' (by linarith)
    _ ≤ CI * σ ^ M / (2 * A) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [hCI, hW]
    _ = CI / (2 * A) * σ ^ M := by ring

/-! ### The two hypotheses, met at the real objects

`lake build` cannot tell whether a hypothesis is satisfiable, so both of the
decomposition's non-trivial ones are discharged here rather than assumed to be
discharge*able*. -/

/-- **The polar form is available at every parameter**, so `hpolar` is not a
restriction on `Q`, `B` or the branch: it names `ψ = arg W`, and
`ψ` is a genuine choice only in *which* branch of the argument is taken.
The witness is `Complex.norm_mul_exp_arg_mul_I`, and it works at the zeros of
`W` too, where both sides vanish. -/
theorem exists_polar_phase (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) :
    ∃ ψ : ℝ → ℝ, ∀ θ : ℝ,
      ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
        = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I) := by
  refine ⟨fun θ => (ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)).arg, fun θ => ?_⟩
  exact (Complex.norm_mul_exp_arg_mul_I _).symm

/-- **The amplitude floor on a compact zero-free subarc**, which is what
`prop:local-strong-clock`'s `𝒥` is chosen to be.  Continuity and
compactness, nothing else — in particular **not** `eq:amplitude-deletion`, whose
windows exist to handle the amplitude's zeros and which a subarc with none does
not need.

This supplies the `A ≤ |W|` that `interior_cos_error_geometric` takes; without
it that hypothesis would have no producer anywhere in the tree. -/
theorem exists_amplitude_floor_on_subarc {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {a b : ℝ}
    (hWc : ContinuousOn (fun θ => ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ))
      (Set.Icc a b))
    (hne : ∀ θ ∈ Set.Icc a b, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) :
    ∃ A > (0 : ℝ), ∀ θ ∈ Set.Icc a b, A ≤ ftPrincipalAmp Q B r z τ θ := by
  rcases (Set.Icc a b).eq_empty_or_nonempty with hemp | hne'
  · exact ⟨1, one_pos, fun θ hθ => absurd hθ (by rw [hemp]; exact fun h => h)⟩
  obtain ⟨θ₀, hθ₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne' hWc.norm
  exact ⟨ftPrincipalAmp Q B r z τ θ₀, norm_pos_iff.mpr (hne θ₀ hθ₀), fun θ hθ => hmin hθ⟩

/-- **`prop:local-strong-clock`'s first display, on the whole subarc.**  Every
constant produced rather than assumed: the floor `A` by compactness, the phase
`ψ` by the polar form, and the error's `C_Iσ^M` by
`DominanceFTSupply.interior_remainder_uniform`.  What is left to reach
`eq:local-phase-quantization` is the `C^1` half, which
`PoleExpansion.norm_smul_ftContourRemDeriv_le` now supplies, and the change of
variable of `Consequences.norm_le_of_mul_eq`. -/
theorem interior_cos_decomposition_on_subarc {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {a b CI σ : ℝ} (hσ : 0 ≤ σ)
    (hτ : ∀ θ ∈ Set.Icc a b, 0 < τ θ)
    (hWc : ContinuousOn (fun θ => ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ))
      (Set.Icc a b))
    (hne : ∀ θ ∈ Set.Icc a b, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0)
    (hrem : ∀ (M : ℕ), ∀ θ ∈ Set.Icc a b, |ftRemainder Q B r z τ M θ| ≤ CI * σ ^ M) :
    ∃ (A : ℝ) (ψ : ℝ → ℝ), 0 < A ∧ ∀ (M : ℕ), ∀ θ ∈ Set.Icc a b, ∃ e : ℝ,
      ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
          / (2 * ftPrincipalAmp Q B r z τ θ)
        = Real.cos (((M : ℝ) + 1) * θ - ψ θ) + e ∧
      |e| ≤ CI / (2 * A) * σ ^ M := by
  obtain ⟨A, hA, hfloor⟩ := exists_amplitude_floor_on_subarc hWc hne
  obtain ⟨ψ, hψ⟩ := exists_polar_phase Q B r z τ
  refine ⟨A, ψ, hA, fun M θ hθ => ?_⟩
  exact interior_cos_error_geometric (ψ := ψ) (hτ θ hθ) hA hσ (hfloor θ hθ)
    (hrem M θ hθ) (hψ θ)

/-- **`prop:local-strong-clock`'s first display with the error as a function.**
Same content as `interior_cos_decomposition_on_subarc`, with the error carried as
`e : ℕ → ℝ → ℝ` rather than produced one point at a time.  A derivative bound on
the error cannot even be *stated* against a pointwise existential, which is what
`eq:C1-interior-remainder` and everything downstream of it need.

**The error is determined, not chosen.**  The decomposition clause pins
`e M θ` to `LHS - cos Φ_M(θ)`, so there is exactly one candidate at every point
and the function is written down rather than selected: no choice principle is
involved in passing from the pointwise form to this one, and the two statements
carry the same information.

What this does **not** supply is regularity.  The hypotheses constrain `z` and
`τ` only through continuity, and `e M` inherits `τ^{M+1}` from the numerator, so
nothing here makes `e M` differentiable; that needs `HasDerivAt` hypotheses on
`z` and `τ`, and a *differentiable* branch of the phase in place of
`exists_polar_phase`'s `arg`, which is `eq:phase-derivative-bound`. -/
theorem exists_interior_cos_error_function {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {a b CI σ : ℝ} (hσ : 0 ≤ σ)
    (hτ : ∀ θ ∈ Set.Icc a b, 0 < τ θ)
    (hWc : ContinuousOn (fun θ => ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ))
      (Set.Icc a b))
    (hne : ∀ θ ∈ Set.Icc a b, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0)
    (hrem : ∀ (M : ℕ), ∀ θ ∈ Set.Icc a b, |ftRemainder Q B r z τ M θ| ≤ CI * σ ^ M) :
    ∃ (A : ℝ) (ψ : ℝ → ℝ) (e : ℕ → ℝ → ℝ), 0 < A ∧
      (∀ (M : ℕ), ∀ θ ∈ Set.Icc a b,
        ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
            / (2 * ftPrincipalAmp Q B r z τ θ)
          = Real.cos (((M : ℝ) + 1) * θ - ψ θ) + e M θ) ∧
      (∀ (M : ℕ), ∀ θ ∈ Set.Icc a b, |e M θ| ≤ CI / (2 * A) * σ ^ M) := by
  obtain ⟨A, ψ, hA, hdec⟩ := interior_cos_decomposition_on_subarc hσ hτ hWc hne hrem
  refine ⟨A, ψ, fun M θ =>
    ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
        / (2 * ftPrincipalAmp Q B r z τ θ)
      - Real.cos (((M : ℝ) + 1) * θ - ψ θ),
    hA, fun M θ _ => by ring, fun M θ hθ => ?_⟩
  obtain ⟨e, heq, hbd⟩ := hdec M θ hθ
  have hE : ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
        / (2 * ftPrincipalAmp Q B r z τ θ)
      - Real.cos (((M : ℝ) + 1) * θ - ψ θ) = e := by
    rw [heq]; ring
  dsimp only
  rw [hE]
  exact hbd

/-! ### Toward `eq:local-phase-quantization` — the links, with their suppliers

`Consequences.exists_unique_zero_near_phase_point` localizes a zero of
`cos u + ε(u)` once `|ε| < sinδ` and
`|ε'| ≤ 1/4`.  `interior_cos_decomposition_on_subarc` supplies the
first at large `M`.  The second travels through
`Consequences.norm_le_of_mul_eq`, and the two lemmas on either side of it do
**not** compose as written: one produces `(M+1)A_τ A + B_d`, the other consumes
`CM`, and `Φ_M'` has to be bounded below before either applies.  Both gaps are
arithmetic, and both are closed here rather than assumed away. -/

/-- **The `τ`-slope bound on a compact subarc**, which
`Consequences.norm_deriv_scaled_remainder_le` takes as `hslope` and nothing in
the tree produced.  Continuity of `τ'` and positivity of `τ` on a compact
interval, nothing else — the same shape as the amplitude floor, and missing for
the same reason. -/
theorem exists_tau_slope_bound_on_subarc {τ τ' : ℝ → ℝ} {a b : ℝ}
    (hτc : ContinuousOn τ' (Set.Icc a b)) (hτcont : ContinuousOn τ (Set.Icc a b))
    (hτpos : ∀ θ ∈ Set.Icc a b, 0 < τ θ) :
    ∃ Aτ ≥ (0 : ℝ), ∀ θ ∈ Set.Icc a b, |τ' θ| / τ θ ≤ Aτ := by
  rcases (Set.Icc a b).eq_empty_or_nonempty with hemp | hne
  · exact ⟨0, le_refl 0, fun θ hθ => absurd hθ (by rw [hemp]; exact fun h => h)⟩
  have hcont : ContinuousOn (fun θ => |τ' θ| / τ θ) (Set.Icc a b) :=
    (hτc.abs).div hτcont fun θ hθ => (hτpos θ hθ).ne'
  obtain ⟨Aτ, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max Aτ 0, le_max_right _ _, fun θ hθ => le_trans ?_ (le_max_left _ _)⟩
  have := hA θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) (hτpos θ hθ).le)] at this
  exact this

/-- **The first shape mismatch.**  `norm_deriv_scaled_remainder_le` returns
`((M+1)A_τ A + B_d)σ^M`; `norm_le_of_mul_eq` consumes `CMσ^M`.  For
`M ≥ 1` the two are reconciled at `C = 2A_τ A + B_d`, and only there: the
constant has to absorb the `+1` as well as the `M`-free term, which is why the
bridge is not `C = A_τ A + B_d`. -/
theorem succ_coeff_le_mul {Aτ A Bd : ℝ} {M : ℕ} (hM : 1 ≤ M) (hAA : 0 ≤ Aτ * A)
    (hBd : 0 ≤ Bd) :
    ((M : ℝ) + 1) * Aτ * A + Bd ≤ (2 * (Aτ * A) + Bd) * (M : ℝ) := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  nlinarith [hAA, hBd, hM1]

/-- **The second shape mismatch — `Φ_M'` bounded below.**  `eq:Phi-def` gives
`Φ_M' = (M+1) - ψ'`, so `eq:phase-derivative-bound`'s `|ψ'| ≤ κ`
puts `Φ_M'` above `M/2` as soon as `M ≥ 2κ`.  That is
`norm_le_of_mul_eq`'s `hu` at `c = 1/2`, and it is what makes the `M` in the
numerator cancel exactly rather than approximately.

`κ` itself is `eq:phase-derivative-bound`, which the branch data of
`MainComposition` already carries; it is not invented here. -/
theorem phase_deriv_lower {dψ κ : ℝ} {M : ℕ} (hκ : |dψ| ≤ κ) (hM : 2 * κ ≤ (M : ℝ)) :
    (1 / 2 : ℝ) * (M : ℝ) ≤ |((M : ℝ) + 1) - dψ| := by
  have hκ0 : 0 ≤ κ := le_trans (abs_nonneg _) hκ
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hd : dψ ≤ κ := le_trans (le_abs_self _) hκ
  have hpos : (0 : ℝ) < ((M : ℝ) + 1) - dψ := by linarith
  rw [abs_of_pos hpos]
  linarith

/-- **`eq:C1-interior-remainder` transported to the phase coordinate.**  The two
bridges applied to `norm_le_of_mul_eq`: the derivative of the transported error
is `O(σ^M)` with **no `M`**, which is the "exactly absorbed" step of the
paper and the `hde` that
`Consequences.exists_unique_zero_near_phase_point` consumes.

What is still owed before this closes `eq:local-phase-quantization` is the
transport itself — a function `ε` on the phase interval with
`ε(Φ_M(θ)) = e(θ)`, whose existence needs `Φ_M` inverted on the
subarc.  `hchain` is that inverse's chain rule and is the one hypothesis here
with no producer in the tree yet. -/
theorem transported_error_deriv_bound {dR du dε Aτ A Bd κ dψ σ : ℝ} {M : ℕ}
    (hM : 1 ≤ M) (hσ : 0 ≤ σ) (hAA : 0 ≤ Aτ * A) (hBd : 0 ≤ Bd)
    (hR : |dR| ≤ (((M : ℝ) + 1) * Aτ * A + Bd) * σ ^ M)
    (hκ : |dψ| ≤ κ) (hMκ : 2 * κ ≤ (M : ℝ)) (hdu : du = ((M : ℝ) + 1) - dψ)
    (hchain : dε * du = dR) :
    |dε| ≤ (2 * (2 * (Aτ * A) + Bd)) * σ ^ M := by
  have hC0 : (0 : ℝ) ≤ 2 * (Aτ * A) + Bd := by linarith
  have hR' : |dR| ≤ (2 * (Aτ * A) + Bd) * (M : ℝ) * σ ^ M := by
    refine le_trans hR ?_
    have := succ_coeff_le_mul (Aτ := Aτ) (A := A) (Bd := Bd) hM hAA hBd
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hu : (1 / 2 : ℝ) * (M : ℝ) ≤ |du| := by
    rw [hdu]; exact phase_deriv_lower hκ hMκ
  have hfinal := norm_le_of_mul_eq (C := 2 * (Aτ * A) + Bd) (c := 1 / 2)
    hM (by norm_num) hσ hC0 hR' hu hchain
  simpa [div_eq_iff, mul_comm] using hfinal

/-! ### The phase is strictly monotone, and the transport is avoidable

`hchain` was the last hypothesis with no producer, and the route to it runs
through inverting `Φ_M`.  Both halves of that are addressed here, and the
second is a finding rather than a construction: the localization does not need
the inverse.

`Consequences.exists_unique_zero_near_phase_point` is stated in the phase
coordinate, so reaching it does require transporting the error through
`Φ_M^{-1}`.  But the tool *underneath* it,
`Consequences.exists_unique_zero_of_deriv_pos`, is coordinate-free: it asks for
strict monotonicity and a sign change on an interval, and both are available in
`θ` directly.  In `θ` the chain rule multiplies by `Φ_M'` instead of
dividing by it, so the estimate that has to be made is
`|sinΦ_M|\,Φ_M' > |e'|` — the same inequality
`Consequences.norm_le_of_mul_eq` produces after absorption, with the factor on
the other side and no inverse function anywhere. -/

/-- **`eq:Phi-def` is strictly monotone on the subarc.**  `Φ_M' = (M+1) - ψ'`
is positive as soon as `eq:phase-derivative-bound`'s `κ` is below `M+1`,
which is the same condition `MainComposition`'s branch data already carries.

This is the precondition for every route to `eq:local-phase-quantization`,
whether or not `Φ_M` is inverted. -/
theorem strictMonoOn_ftPhase {ψ dψ : ℝ → ℝ} {a b κ : ℝ} {M : ℕ}
    (hψc : ContinuousOn ψ (Set.Icc a b))
    (hψd : ∀ θ ∈ Set.Icc a b, HasDerivAt ψ (dψ θ) θ)
    (hκ : ∀ θ ∈ Set.Icc a b, |dψ θ| ≤ κ) (hM : κ < (M : ℝ) + 1) :
    StrictMonoOn (fun θ => ((M : ℝ) + 1) * θ - ψ θ) (Set.Icc a b) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b)
    (f' := fun θ => ((M : ℝ) + 1) - dψ θ)
    ((continuousOn_const.mul continuousOn_id).sub hψc) (fun θ hθ => ?_) (fun θ hθ => ?_)
  · have hmem : θ ∈ Set.Icc a b := interior_subset hθ
    have h1 : HasDerivAt (fun x : ℝ => ((M : ℝ) + 1) * x) ((M : ℝ) + 1) θ := by
      simpa using (hasDerivAt_id θ).const_mul ((M : ℝ) + 1)
    exact (h1.sub (hψd θ hmem)).hasDerivWithinAt
  · have hmem : θ ∈ Set.Icc a b := interior_subset hθ
    have := (abs_le.1 (hκ θ hmem)).2
    linarith

/-- **The derivative estimate that removes the need to invert `Φ_M`.**  Near a
phase point `|sinΦ_M|` is bounded below, so the `θ`-derivative of
`cosΦ_M + e` is bounded away from zero as soon as `|e'|` is below
`|sinΦ_M|\,Φ_M'` — and `Φ_M' ≳ M` while `|e'| = O(Mσ^M)`, so
the inequality holds for every large `M` with room to spare.

That is exactly what `Consequences.exists_unique_zero_of_deriv_pos` consumes, in
the `θ` coordinate, with no local inverse and no chain rule through one. -/
theorem abs_phase_cos_deriv_lower {Φ dΦ de s Ce : ℝ}
    (hsin : s ≤ |Real.sin Φ|) (hΦ : 0 < dΦ) (hde : |de| ≤ Ce) (hlt : Ce < s * dΦ) :
    0 < s * dΦ - Ce ∧ s * dΦ - Ce ≤ |-Real.sin Φ * dΦ + de| := by
  refine ⟨by linarith, ?_⟩
  have h1 : |(-Real.sin Φ * dΦ)| = |Real.sin Φ| * dΦ := by
    rw [abs_mul, abs_neg, abs_of_pos hΦ]
  have h2 : s * dΦ ≤ |(-Real.sin Φ * dΦ)| := by
    rw [h1]
    exact mul_le_mul_of_nonneg_right hsin hΦ.le
  have h3 : |(-Real.sin Φ * dΦ)| - |de| ≤ |-Real.sin Φ * dΦ + de| := by
    have h := abs_sub_abs_le_abs_sub (-Real.sin Φ * dΦ) (-de)
    rwa [abs_neg, sub_neg_eq_add] at h
  linarith [h3, h2, hde]

/-- **The estimate holds for every large `M`.**  `|sinΦ_M|\,Φ_M' ≳ sM/2`
while `|e'| = O(Mσ^M)`, so the gap the previous lemma needs opens for all
`M` beyond a threshold and never closes again — which is what makes the
`θ`-coordinate localization unconditional rather than a large-`M` hope. -/
theorem eventually_phase_cos_deriv_gap {s C σ : ℝ} (hs : 0 < s)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → C * (M : ℝ) * σ ^ M < s * ((1 / 2 : ℝ) * (M : ℝ)) ∨ M = 0 := by
  obtain ⟨M₁, hM₁⟩ := exists_pow_mul_geometric_le (K := C) hσ0 hσ1 (by positivity : (0:ℝ) < s / 4) 1
  refine ⟨max 1 M₁, fun M hM => Or.inl ?_⟩
  have hM1 : 1 ≤ M := le_trans (le_max_left _ _) hM
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hgeom := hM₁ M (le_trans (le_max_right _ _) hM)
  have hrw : C * ((M : ℝ) ^ 1 * σ ^ M) = C * (M : ℝ) * σ ^ M := by ring
  rw [hrw] at hgeom
  nlinarith [hgeom, hMr, hs]

/-! ### The window, with its signs resolved

`abs_phase_cos_deriv_lower` bounds the derivative's *modulus*, and
`Consequences.exists_unique_zero_of_deriv_pos` needs its *sign* — together with a
sign change across the window.  Both come from the same identity: with
`cos u_0 = 0` and `σ = sin u_0`, `sin u = σcos(u - u_0)`, so `σ`
carries every sign in the argument and no case split on the parity of the phase
index appears. -/

private theorem sin_eq_sigma_mul_cos {u₀ u : ℝ} (hcos : Real.cos u₀ = 0) :
    Real.sin u = Real.sin u₀ * Real.cos (u - u₀) := by
  have h := Real.sin_add u₀ (u - u₀)
  rw [hcos, zero_mul, add_zero] at h
  simpa using h

private theorem sigma_sq (u₀ : ℝ) (hcos : Real.cos u₀ = 0) :
    Real.sin u₀ ^ 2 = 1 := by
  have h := Real.sin_sq_add_cos_sq u₀
  rw [hcos] at h
  nlinarith [h]

/-- **The derivative's sign on the window.**  `-σ(cosΦ + e)'` is positive
throughout `|Φ - u_0| ≤ π/4`, because `cos(Φ - u_0) ≥ √2/2` there and
`|e'|` is below `(√2/2)Φ_M'`.  This is
`Consequences.exists_unique_zero_of_deriv_pos`'s `hpos`, in the `θ`
coordinate. -/
theorem phase_cos_deriv_pos {u₀ Φ dΦ de Ce : ℝ}
    (hcos : Real.cos u₀ = 0) (hnear : |Φ - u₀| ≤ Real.pi / 4) (hΦ : 0 < dΦ)
    (hde : |de| ≤ Ce) (hlt : Ce < Real.sqrt 2 / 2 * dΦ) :
    0 < -Real.sin u₀ * (-Real.sin Φ * dΦ + de) := by
  have hσ2 := sigma_sq u₀ hcos
  have hsin := sin_eq_sigma_mul_cos (u₀ := u₀) (u := Φ) hcos
  have hcosv : Real.sqrt 2 / 2 ≤ Real.cos (Φ - u₀) := by
    rw [← Real.cos_pi_div_four, ← Real.cos_abs (Φ - u₀)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by nlinarith [Real.pi_pos]) (le_trans hnear (le_refl _))
  have hσabs : |Real.sin u₀| = 1 := by
    rw [← Real.sqrt_sq_eq_abs, hσ2, Real.sqrt_one]
  have hσde : |Real.sin u₀ * de| ≤ Ce := by
    rw [abs_mul, hσabs, one_mul]; exact hde
  have hrw : -Real.sin u₀ * (-Real.sin Φ * dΦ + de)
      = Real.cos (Φ - u₀) * dΦ - Real.sin u₀ * de := by
    rw [hsin]; linear_combination (Real.cos (Φ - u₀) * dΦ) * hσ2
  have hlow : Real.sqrt 2 / 2 * dΦ ≤ Real.cos (Φ - u₀) * dΦ :=
    mul_le_mul_of_nonneg_right hcosv hΦ.le
  rw [hrw]
  have := (abs_le.1 hσde).2
  linarith

/-- **The sign change across the window.**  At `Φ = u_0 ∓ δ` the cosine is
`±σsinδ`, so once `|e| < sinδ` the function `-σ(cosΦ + e)`
is negative at the lower end and positive at the upper one — which is
`exists_unique_zero_of_deriv_pos`'s `hfa` and `hfb`, and the last link of the
localization that had no producer. -/
theorem phase_cos_sign_change {u₀ δ elo ehi : ℝ} (hcos : Real.cos u₀ = 0)
    (helo : |elo| < Real.sin δ) (hehi : |ehi| < Real.sin δ) :
    -Real.sin u₀ * (Real.cos (u₀ - δ) + elo) < 0
      ∧ 0 < -Real.sin u₀ * (Real.cos (u₀ + δ) + ehi) := by
  have hσ2 := sigma_sq u₀ hcos
  have hσabs : |Real.sin u₀| = 1 := by
    rw [← Real.sqrt_sq_eq_abs, hσ2, Real.sqrt_one]
  have hlo : Real.cos (u₀ - δ) = Real.sin u₀ * Real.sin δ := by
    rw [Real.cos_sub, hcos, zero_mul, zero_add]
  have hhi : Real.cos (u₀ + δ) = -(Real.sin u₀ * Real.sin δ) := by
    rw [Real.cos_add, hcos, zero_mul, zero_sub]
  have hblo : |Real.sin u₀ * elo| < Real.sin δ := by
    rw [abs_mul, hσabs, one_mul]; exact helo
  have hbhi : |Real.sin u₀ * ehi| < Real.sin δ := by
    rw [abs_mul, hσabs, one_mul]; exact hehi
  constructor
  · rw [hlo]
    have h1 : -Real.sin u₀ * (Real.sin u₀ * Real.sin δ + elo)
        = -Real.sin δ - Real.sin u₀ * elo := by
      linear_combination (-Real.sin δ) * hσ2
    rw [h1]
    linarith [(abs_lt.1 hblo).1]
  · rw [hhi]
    have h2 : -Real.sin u₀ * (-(Real.sin u₀ * Real.sin δ) + ehi)
        = Real.sin δ - Real.sin u₀ * ehi := by
      linear_combination (Real.sin δ) * hσ2
    rw [h2]
    linarith [(abs_lt.1 hbhi).2]

/-- **The window exists.**  `Φ_M` attains `u_0 ∓ δ` on the subarc, by the
intermediate value theorem applied twice — the second time on `[θ_-, b]`, so
the two parameters come out ordered.  This was the last link of the localization
with no producer. -/
theorem exists_phase_window {Φ : ℝ → ℝ} {a b u₀ δ : ℝ} (hab : a ≤ b) (hδ : 0 ≤ δ)
    (hΦc : ContinuousOn Φ (Set.Icc a b))
    (hlo : Φ a ≤ u₀ - δ) (hhi : u₀ + δ ≤ Φ b) :
    ∃ θlo ∈ Set.Icc a b, ∃ θhi ∈ Set.Icc θlo b,
      Φ θlo = u₀ - δ ∧ Φ θhi = u₀ + δ := by
  have hmid : u₀ - δ ≤ u₀ + δ := by linarith
  obtain ⟨θlo, hθlo, hΦlo⟩ :=
    intermediate_value_Icc hab hΦc ⟨hlo, le_trans hmid hhi⟩
  have hθb : θlo ≤ b := hθlo.2
  have hΦc' : ContinuousOn Φ (Set.Icc θlo b) :=
    hΦc.mono (Set.Icc_subset_Icc hθlo.1 le_rfl)
  obtain ⟨θhi, hθhi, hΦhi⟩ :=
    intermediate_value_Icc hθb hΦc' ⟨by rw [hΦlo]; exact hmid, hhi⟩
  exact ⟨θlo, hθlo, θhi, hθhi, hΦlo, hΦhi⟩

/-- **`eq:local-phase-quantization`, the existence-and-uniqueness half, in the
`θ` coordinate.**  Every hypothesis has a named producer:
`hmono` is `strictMonoOn_ftPhase`, `he` is
`interior_cos_decomposition_on_subarc`, `hCe` is
`eventually_phase_cos_deriv_gap` against the `C^1` bound that
`PoleExpansion.norm_smul_ftContourRemDeriv_le` supplies, and the window is
`exists_phase_window`.

No local inverse of `Φ_M` appears: the sign work is
`phase_cos_deriv_pos` and `phase_cos_sign_change`, and the zero is produced by
`Consequences.exists_unique_zero_of_deriv_pos`, which is coordinate-free. -/
theorem exists_unique_phase_zero {Φ dΦ e de : ℝ → ℝ} {a b u₀ δ Ce : ℝ}
    (hab : a ≤ b) (hcos : Real.cos u₀ = 0) (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4)
    (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hΦd : ∀ θ ∈ Set.Icc a b, HasDerivAt Φ (dΦ θ) θ)
    (hed : ∀ θ ∈ Set.Icc a b, HasDerivAt e (de θ) θ)
    (hΦpos : ∀ θ ∈ Set.Icc a b, 0 < dΦ θ)
    (hde : ∀ θ ∈ Set.Icc a b, |de θ| ≤ Ce)
    (hCe : ∀ θ ∈ Set.Icc a b, Ce < Real.sqrt 2 / 2 * dΦ θ)
    (he : ∀ θ ∈ Set.Icc a b, |e θ| < Real.sin δ)
    (hlo : Φ a ≤ u₀ - δ) (hhi : u₀ + δ ≤ Φ b) :
    ∃ θlo ∈ Set.Icc a b, ∃ θhi ∈ Set.Icc θlo b, θlo < θhi ∧
      Φ θlo = u₀ - δ ∧ Φ θhi = u₀ + δ ∧
      ∃ θ ∈ Set.Ioo θlo θhi, Real.cos (Φ θ) + e θ = 0 ∧
        ∀ y ∈ Set.Icc θlo θhi, Real.cos (Φ y) + e y = 0 → y = θ := by
  have hΦc : ContinuousOn Φ (Set.Icc a b) :=
    fun θ hθ => (hΦd θ hθ).continuousAt.continuousWithinAt
  obtain ⟨θlo, hθlo, θhi, hθhi, hΦlo, hΦhi⟩ :=
    exists_phase_window hab hδ.le hΦc hlo hhi
  have hsub : Set.Icc θlo θhi ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc hθlo.1 (le_trans hθhi.2 le_rfl)
  have hlt : θlo < θhi := by
    rcases lt_or_eq_of_le hθhi.1 with h | h
    · exact h
    · exfalso; rw [← h, hΦlo] at hΦhi; linarith
  -- `Φ` stays in the phase window, so `|Φ - u₀| ≤ δ` there
  have hrange : ∀ θ ∈ Set.Icc θlo θhi, |Φ θ - u₀| ≤ δ := by
    intro θ hθ
    have h1 : Φ θlo ≤ Φ θ :=
      hmono.monotoneOn hθlo (hsub hθ) hθ.1
    have h2 : Φ θ ≤ Φ θhi :=
      hmono.monotoneOn (hsub hθ) (hsub ⟨hθhi.1, le_rfl⟩) hθ.2
    rw [hΦlo] at h1; rw [hΦhi] at h2
    rw [abs_le]; constructor <;> linarith
  -- the sign-resolved function and its derivative
  set g : ℝ → ℝ := fun θ => -Real.sin u₀ * (Real.cos (Φ θ) + e θ) with hg
  set g' : ℝ → ℝ := fun θ => -Real.sin u₀ * (-Real.sin (Φ θ) * dΦ θ + de θ) with hg'
  have hgd : ∀ θ ∈ Set.Icc θlo θhi, HasDerivAt g (g' θ) θ := by
    intro θ hθ
    have hc : HasDerivAt (fun s => Real.cos (Φ s)) (-Real.sin (Φ θ) * dΦ θ) θ :=
      (Real.hasDerivAt_cos (Φ θ)).comp θ (hΦd θ (hsub hθ))
    exact ((hc.add (hed θ (hsub hθ))).const_mul (-Real.sin u₀))
  have hgpos : ∀ θ ∈ Set.Icc θlo θhi, 0 < g' θ := by
    intro θ hθ
    exact phase_cos_deriv_pos hcos (le_trans (hrange θ hθ) hδ4)
      (hΦpos θ (hsub hθ)) (hde θ (hsub hθ)) (hCe θ (hsub hθ))
  obtain ⟨hsa, hsb⟩ := phase_cos_sign_change (u₀ := u₀) (δ := δ) hcos
    (he θlo (hsub ⟨le_rfl, hθhi.1⟩)) (he θhi (hsub ⟨hθhi.1, le_rfl⟩))
  have hga : g θlo < 0 := by rw [hg]; simpa [hΦlo] using hsa
  have hgb : 0 < g θhi := by rw [hg]; simpa [hΦhi] using hsb
  obtain ⟨θ, hθ, hz, huniq⟩ := exists_unique_zero_of_deriv_pos hlt hgd hgpos hga hgb
  have hσne : Real.sin u₀ ≠ 0 := by
    intro h
    have := sigma_sq u₀ hcos
    rw [h] at this; norm_num at this
  refine ⟨θlo, hθlo, θhi, hθhi, hlt, hΦlo, hΦhi, θ, hθ, ?_, ?_⟩
  · have : -Real.sin u₀ * (Real.cos (Φ θ) + e θ) = 0 := hz
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (neg_eq_zero.1 h) hσne
    · exact h
  · intro y hy hy0
    refine huniq y hy ?_
    rw [hg]
    simp [hy0]

/-- **The hypothesis set is jointly satisfiable**, checked by instantiating it
rather than by inspecting it: at `Φ = \mathrm{id}`, `e ≡ 0`,
`u_0 = π/2` and `δ = π/4` every binder holds and the conclusion is the
true statement that `cos` has exactly one zero in `(π/4, 3π/4)`.

A theorem whose hypotheses cannot be met together builds green and says nothing;
this is the cheapest test that `exists_unique_phase_zero` is not that. -/
theorem exists_unique_phase_zero_nonvacuous :
    ∃ θlo ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 4),
      ∃ θhi ∈ Set.Icc θlo (3 * Real.pi / 4), θlo < θhi ∧
        θlo = Real.pi / 2 - Real.pi / 4 ∧ θhi = Real.pi / 2 + Real.pi / 4 ∧
        ∃ θ ∈ Set.Ioo θlo θhi, Real.cos θ + 0 = 0 ∧
          ∀ y ∈ Set.Icc θlo θhi, Real.cos y + 0 = 0 → y = θ := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have hs2 : (0 : ℝ) < Real.sqrt 2 / 2 := by
    have := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
    linarith
  exact exists_unique_phase_zero (Φ := fun x => x) (dΦ := fun _ => 1)
    (e := fun _ => 0) (de := fun _ => 0) (u₀ := Real.pi / 2) (δ := Real.pi / 4)
    (Ce := 0) (by linarith) Real.cos_pi_div_two (by linarith) le_rfl
    (fun x _ y _ h => h) (fun θ _ => hasDerivAt_id θ)
    (fun θ _ => hasDerivAt_const θ 0) (fun _ _ => one_pos)
    (fun _ _ => by norm_num) (fun _ _ => by rw [mul_one]; exact hs2)
    (fun _ _ => by rw [hs]; simp)
    (by linarith) (by linarith)

/-! ### Two consecutive zeros, jointly

Localizing one zero per phase point is not the same as the zeros existing
*together in the right order*: the window for `k` and the window for `k+1` are
each satisfiable on their own, and what makes them joint is that `δ ≤ π/4`
keeps them disjoint while `Φ_M` is monotone, so `θ_k < θ_{k+1}`
follows rather than being assumed.  `Consequences.local_clock_spacing` consumes
exactly a consecutive pair, so this is the shape the spacing law needs. -/

/-- **`eq:local-phase-quantization` at two consecutive indices.**  The phase
points are `π` apart and the windows have half-width `δ ≤ π/4`, so the
two windows are separated by at least `π/2` and the zeros they carry inherit
that order through the strict monotonicity of `Φ_M`.

The subarc has to be long enough to hold both windows, which is the single
strengthened hypothesis `hhi`; everything else is `exists_unique_phase_zero`'s
own list, applied twice. -/
theorem exists_two_consecutive_phase_zeros {Φ dΦ e de : ℝ → ℝ} {a b u₀ δ Ce : ℝ}
    (hab : a ≤ b) (hcos : Real.cos u₀ = 0) (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4)
    (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hΦd : ∀ θ ∈ Set.Icc a b, HasDerivAt Φ (dΦ θ) θ)
    (hed : ∀ θ ∈ Set.Icc a b, HasDerivAt e (de θ) θ)
    (hΦpos : ∀ θ ∈ Set.Icc a b, 0 < dΦ θ)
    (hde : ∀ θ ∈ Set.Icc a b, |de θ| ≤ Ce)
    (hCe : ∀ θ ∈ Set.Icc a b, Ce < Real.sqrt 2 / 2 * dΦ θ)
    (he : ∀ θ ∈ Set.Icc a b, |e θ| < Real.sin δ)
    (hlo : Φ a ≤ u₀ - δ) (hhi : u₀ + Real.pi + δ ≤ Φ b) :
    ∃ θk ∈ Set.Icc a b, ∃ θk1 ∈ Set.Icc a b, θk < θk1 ∧
      Real.cos (Φ θk) + e θk = 0 ∧ Real.cos (Φ θk1) + e θk1 = 0 ∧
      |Φ θk - u₀| < δ ∧ |Φ θk1 - (u₀ + Real.pi)| < δ := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcos1 : Real.cos (u₀ + Real.pi) = 0 := by rw [Real.cos_add_pi, hcos, neg_zero]
  -- the first window
  obtain ⟨lo, hlo', hi, hhi', hlt, hΦlo, hΦhi, θk, hθk, hzk, -⟩ :=
    exists_unique_phase_zero hab hcos hδ hδ4 hmono hΦd hed hΦpos hde hCe he hlo
      (by linarith)
  -- the second, at the next phase point
  obtain ⟨lo1, hlo1, hi1, hhi1, hlt1, hΦlo1, hΦhi1, θk1, hθk1, hzk1, -⟩ :=
    exists_unique_phase_zero hab hcos1 hδ hδ4 hmono hΦd hed hΦpos hde hCe he
      (by linarith) (by linarith)
  have hsub : Set.Icc lo hi ⊆ Set.Icc a b := Set.Icc_subset_Icc hlo'.1 hhi'.2
  have hsub1 : Set.Icc lo1 hi1 ⊆ Set.Icc a b := Set.Icc_subset_Icc hlo1.1 hhi1.2
  have hmemk : θk ∈ Set.Icc a b := hsub ⟨hθk.1.le, hθk.2.le⟩
  have hmemk1 : θk1 ∈ Set.Icc a b := hsub1 ⟨hθk1.1.le, hθk1.2.le⟩
  -- each zero sits inside its own phase window
  have hrk : |Φ θk - u₀| < δ := by
    have h1 : Φ lo < Φ θk := hmono (hsub ⟨le_rfl, hlt.le⟩) hmemk hθk.1
    have h2 : Φ θk < Φ hi := hmono hmemk (hsub ⟨hlt.le, le_rfl⟩) hθk.2
    rw [hΦlo] at h1; rw [hΦhi] at h2
    rw [abs_lt]; constructor <;> linarith
  have hrk1 : |Φ θk1 - (u₀ + Real.pi)| < δ := by
    have h1 : Φ lo1 < Φ θk1 := hmono (hsub1 ⟨le_rfl, hlt1.le⟩) hmemk1 hθk1.1
    have h2 : Φ θk1 < Φ hi1 := hmono hmemk1 (hsub1 ⟨hlt1.le, le_rfl⟩) hθk1.2
    rw [hΦlo1] at h1; rw [hΦhi1] at h2
    rw [abs_lt]; constructor <;> linarith
  -- the windows are separated, so the zeros are ordered
  have hord : θk < θk1 := by
    have hsep : Φ θk < Φ θk1 := by
      have h1 := (abs_lt.1 hrk).2
      have h2 := (abs_lt.1 hrk1).1
      linarith
    exact (hmono.lt_iff_lt hmemk hmemk1).1 hsep
  exact ⟨θk, hmemk, θk1, hmemk1, hord, hzk, hzk1, hrk, hrk1⟩

/-- **At most one zero per window**, without needing the window's endpoints to be
constructed.  `exists_unique_phase_zero` gets uniqueness by building `θlo`, `θhi`
with `Φθlo = u - δ` and `Φθhi = u + δ`, which needs the window to fit inside
`[Φa, Φb]`.  Here the two zeros supply their own interval: `Φ` carries `[θ, θ']`
into the window by monotonicity, and on the window
`|cosΦ| = |sin(Φ - u)| < sinδ` forces `|sinΦ| > cosδ ≥ √2/2`, so
`cosΦ + e` is strictly monotone there and cannot vanish twice.

This is what makes the *index* of a zero well defined, which is the half of
`prop:local-strong-clock`'s "for a unique `θ_{k,M}`" that is about the zeros
rather than about `z`. -/
theorem phase_zero_index_unique {Φ dΦ e de : ℝ → ℝ} {a b δ Ce : ℝ}
    (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4)
    (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hΦd : ∀ θ ∈ Set.Icc a b, HasDerivAt Φ (dΦ θ) θ)
    (hed : ∀ θ ∈ Set.Icc a b, HasDerivAt e (de θ) θ)
    (hΦpos : ∀ θ ∈ Set.Icc a b, 0 < dΦ θ)
    (hde : ∀ θ ∈ Set.Icc a b, |de θ| ≤ Ce)
    (hCe : ∀ θ ∈ Set.Icc a b, Ce < Real.sqrt 2 / 2 * dΦ θ)
    {u : ℝ} (hu : Real.cos u = 0)
    {θ θ' : ℝ} (hθ : θ ∈ Set.Icc a b) (hθ' : θ' ∈ Set.Icc a b)
    (hz : Real.cos (Φ θ) + e θ = 0) (hz' : Real.cos (Φ θ') + e θ' = 0)
    (hk : |Φ θ - u| < δ) (hk' : |Φ θ' - u| < δ) :
    θ = θ' := by
  have hπ := Real.pi_pos
  have hs2 : Real.sqrt 2 / 2 ≤ Real.cos δ := by
    rw [← Real.cos_pi_div_four]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hδ.le (by linarith) hδ4
  have hsq : |Real.sin u| = 1 := by
    have h := Real.sin_sq_add_cos_sq u
    rw [hu] at h
    have hs : Real.sin u ^ 2 = 1 := by nlinarith
    rw [← Real.sqrt_sq_eq_abs, hs, Real.sqrt_one]
  -- on any `s` whose phase sits in the window, the equation's slope is bounded away from 0
  have hslope : ∀ s ∈ Set.Icc a b, |Φ s - u| < δ →
      |Real.sin (Φ s)| * dΦ s - Ce > 0 := by
    intro s hs hw
    have hsin : Real.sin (Φ s) = Real.sin u * Real.cos (Φ s - u) := by
      have h := Real.sin_add u (Φ s - u)
      rw [show u + (Φ s - u) = Φ s by ring, hu, zero_mul, add_zero] at h
      exact h
    have hcw : Real.cos δ ≤ Real.cos (Φ s - u) := by
      rw [← Real.cos_abs (Φ s - u)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hw.le
    have hcpos : 0 < Real.cos δ := lt_of_lt_of_le (by positivity) hs2
    have habs : Real.cos δ ≤ |Real.sin (Φ s)| := by
      rw [hsin, abs_mul, hsq, one_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.cos (Φ s - u))]
      exact hcw
    have h1 : Real.sqrt 2 / 2 * dΦ s ≤ |Real.sin (Φ s)| * dΦ s :=
      mul_le_mul_of_nonneg_right (le_trans hs2 habs) (hΦpos s hs).le
    linarith [hCe s hs]
  -- Rolle: two zeros with a nonvanishing derivative between them is impossible.
  -- This is why no continuity of `dΦ` or `de` is needed — a sign argument would
  -- have wanted it, and Rolle does not.
  have key : ∀ x y : ℝ, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x < y →
      Real.cos (Φ x) + e x = 0 → Real.cos (Φ y) + e y = 0 →
      |Φ x - u| < δ → |Φ y - u| < δ → False := by
    intro x y hx hy hxy hzx hzy hwx hwy
    have hsub : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 hy.2
    have hwin : ∀ s ∈ Set.Icc x y, |Φ s - u| < δ := by
      intro s hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h]; exact hwx
      rcases eq_or_lt_of_le hs.2 with h2 | h2
      · rw [h2]; exact hwy
      have hlo := hmono hx (hsub hs) h
      have hhi := hmono (hsub hs) hy h2
      rw [abs_lt] at hwx hwy ⊢
      exact ⟨by linarith [hwx.1], by linarith [hwy.2]⟩
    have hg : ∀ s ∈ Set.Icc x y,
        HasDerivAt (fun w => Real.cos (Φ w) + e w)
          (-Real.sin (Φ s) * dΦ s + de s) s := fun s hs =>
      ((hΦd s (hsub hs)).cos).add (hed s (hsub hs))
    have hne : ∀ s ∈ Set.Icc x y, -Real.sin (Φ s) * dΦ s + de s ≠ 0 := by
      intro s hs hcon
      have h := hslope s (hsub hs) (hwin s hs)
      have hd := hde s (hsub hs)
      have heqd : Real.sin (Φ s) * dΦ s = de s := by linarith [hcon]
      have : |Real.sin (Φ s) * dΦ s| = |de s| := by rw [heqd]
      rw [abs_mul, abs_of_pos (hΦpos s (hsub hs))] at this
      rw [this] at h
      linarith
    have hgc : ContinuousOn (fun w => Real.cos (Φ w) + e w) (Set.Icc x y) :=
      fun s hs => (hg s hs).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero hxy hgc (by rw [hzx, hzy])
      (fun w hw => hg w ⟨hw.1.le, hw.2.le⟩)
    exact hne ξ ⟨hξ.1.le, hξ.2.le⟩ hξ0
  rcases lt_trichotomy θ θ' with hlt | heq | hgt
  · exact absurd (key θ θ' hθ hθ' hlt hz hz' hk hk') not_false
  · exact heq
  · exact absurd (key θ' θ hθ' hθ hgt hz' hz hk' hk) not_false

/-! ### The pair is CONSECUTIVE

`exists_two_consecutive_phase_zeros` produces two zeros a half turn apart, and
its name says consecutive, but its conclusion does not: nothing there rules out a
third zero between them.  That gap is the difference between a spacing estimate
and a clock — `eq:local-strong-clock` is a statement about *successive* zero
angles, and a pair with unaccounted zeros between them satisfies the inequality
without satisfying the proposition.

The argument is the quantization read backwards.  With `cos u_0 = 0`,
`|cos(u_0 + t)| = |sin t|`, so a zero of `cos Φ + e` forces `|sin t| < sinδ`
at `t = Φ - u_0` — which on `(-δ, π+δ)` confines `t` to the two windows
`(-δ, δ)` and `(π-δ, π+δ)`.  In the middle there is no room, and in each window
`exists_unique_phase_zero`'s uniqueness leaves only the endpoint already
produced. -/

theorem abs_cos_shift {u₀ t : ℝ} (hcos : Real.cos u₀ = 0) :
    |Real.cos (u₀ + t)| = |Real.sin t| := by
  have hs : |Real.sin u₀| = 1 := by
    have h := Real.sin_sq_add_cos_sq u₀
    rw [hcos] at h
    have hsq : Real.sin u₀ ^ 2 = 1 := by nlinarith
    rw [← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_one]
  rw [Real.cos_add, hcos, zero_mul, zero_sub, abs_neg, abs_mul, hs, one_mul]

/-- On `[δ, π-δ]` the sine stays at or above `sinδ`, which is what leaves no
room for a zero between the two windows. -/
private theorem sin_le_sin_of_mem_middle {δ t : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ Real.pi / 2) (h1 : δ ≤ t) (h2 : t ≤ Real.pi - δ) :
    Real.sin δ ≤ Real.sin t := by
  have hπ := Real.pi_pos
  rcases le_total t (Real.pi / 2) with ht | ht
  · exact Real.strictMonoOn_sin.monotoneOn ⟨by linarith, hδ2⟩ ⟨by linarith, ht⟩ h1
  · have hsub : Real.sin t = Real.sin (Real.pi - t) := (Real.sin_pi_sub t).symm
    rw [hsub]
    exact Real.strictMonoOn_sin.monotoneOn ⟨by linarith, hδ2⟩
      ⟨by linarith, by linarith⟩ (by linarith)

/-- **`exists_two_consecutive_phase_zeros`, with the pair shown consecutive.**
Same two zeros, plus the clause that makes them successive: no zero of
`cosΦ + e` lies strictly between them. -/
theorem exists_two_consecutive_phase_zeros_isolated {Φ dΦ e de : ℝ → ℝ}
    {a b u₀ δ Ce : ℝ}
    (hab : a ≤ b) (hcos : Real.cos u₀ = 0) (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4)
    (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hΦd : ∀ θ ∈ Set.Icc a b, HasDerivAt Φ (dΦ θ) θ)
    (hed : ∀ θ ∈ Set.Icc a b, HasDerivAt e (de θ) θ)
    (hΦpos : ∀ θ ∈ Set.Icc a b, 0 < dΦ θ)
    (hde : ∀ θ ∈ Set.Icc a b, |de θ| ≤ Ce)
    (hCe : ∀ θ ∈ Set.Icc a b, Ce < Real.sqrt 2 / 2 * dΦ θ)
    (he : ∀ θ ∈ Set.Icc a b, |e θ| < Real.sin δ)
    (hlo : Φ a ≤ u₀ - δ) (hhi : u₀ + Real.pi + δ ≤ Φ b) :
    ∃ θk ∈ Set.Icc a b, ∃ θk1 ∈ Set.Icc a b, θk < θk1 ∧
      Real.cos (Φ θk) + e θk = 0 ∧ Real.cos (Φ θk1) + e θk1 = 0 ∧
      |Φ θk - u₀| < δ ∧ |Φ θk1 - (u₀ + Real.pi)| < δ ∧
      ∀ θ ∈ Set.Icc a b, θk < θ → θ < θk1 → Real.cos (Φ θ) + e θ ≠ 0 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcos1 : Real.cos (u₀ + Real.pi) = 0 := by rw [Real.cos_add_pi, hcos, neg_zero]
  -- the two windows, with their uniqueness clauses KEPT
  obtain ⟨lo, hlo', hi, hhi', hlt, hΦlo, hΦhi, θk, hθk, hzk, huk⟩ :=
    exists_unique_phase_zero hab hcos hδ hδ4 hmono hΦd hed hΦpos hde hCe he hlo
      (by linarith)
  obtain ⟨lo1, hlo1, hi1, hhi1, hlt1, hΦlo1, hΦhi1, θk1, hθk1, hzk1, huk1⟩ :=
    exists_unique_phase_zero hab hcos1 hδ hδ4 hmono hΦd hed hΦpos hde hCe he
      (by linarith) (by linarith)
  have hsub : Set.Icc lo hi ⊆ Set.Icc a b := Set.Icc_subset_Icc hlo'.1 hhi'.2
  have hsub1 : Set.Icc lo1 hi1 ⊆ Set.Icc a b := Set.Icc_subset_Icc hlo1.1 hhi1.2
  have hmemk : θk ∈ Set.Icc a b := hsub ⟨hθk.1.le, hθk.2.le⟩
  have hmemk1 : θk1 ∈ Set.Icc a b := hsub1 ⟨hθk1.1.le, hθk1.2.le⟩
  have hrk : |Φ θk - u₀| < δ := by
    have h1 : Φ lo < Φ θk := hmono (hsub ⟨le_rfl, hlt.le⟩) hmemk hθk.1
    have h2 : Φ θk < Φ hi := hmono hmemk (hsub ⟨hlt.le, le_rfl⟩) hθk.2
    rw [hΦlo] at h1; rw [hΦhi] at h2
    rw [abs_lt]; exact ⟨by linarith, by linarith⟩
  have hrk1 : |Φ θk1 - (u₀ + Real.pi)| < δ := by
    have h1 : Φ lo1 < Φ θk1 := hmono (hsub1 ⟨le_rfl, hlt1.le⟩) hmemk1 hθk1.1
    have h2 : Φ θk1 < Φ hi1 := hmono hmemk1 (hsub1 ⟨hlt1.le, le_rfl⟩) hθk1.2
    rw [hΦlo1] at h1; rw [hΦhi1] at h2
    rw [abs_lt]; exact ⟨by linarith, by linarith⟩
  have hrkb := abs_lt.1 hrk
  have hrk1b := abs_lt.1 hrk1
  have hkk1 : θk < θk1 :=
    (hmono.lt_iff_lt hmemk hmemk1).1 (by linarith [hrkb.2, hrk1b.1])
  refine ⟨θk, hmemk, θk1, hmemk1, hkk1, hzk, hzk1, hrk, hrk1, ?_⟩
  -- the isolation
  intro θ hθ hgt hltθ hzero
  have hΦgt : Φ θk < Φ θ := hmono hmemk hθ hgt
  have hΦlt : Φ θ < Φ θk1 := hmono hθ hmemk1 hltθ
  set t : ℝ := Φ θ - u₀ with ht
  have hshift : Real.cos (Φ θ) = Real.cos (u₀ + t) := by rw [ht]; ring_nf
  have habs : |Real.sin t| < Real.sin δ := by
    have h0 : Real.cos (Φ θ) = -e θ := by linarith
    have := he θ hθ
    rw [← abs_cos_shift (t := t) hcos, ← hshift, h0, abs_neg]
    exact this
  have htlo : -δ < t := by rw [ht]; linarith [hrkb.1]
  have hthi : t < Real.pi + δ := by rw [ht]; linarith [hrk1b.2]
  have hδ2 : δ ≤ Real.pi / 2 := by linarith
  -- the middle is excluded outright
  rcases lt_or_ge t δ with hcase | hcase
  · -- the first window: uniqueness gives `θ = θk`, contradicting `θk < θ`
    have hmem : θ ∈ Set.Icc lo hi := by
      constructor
      · by_contra hc
        push Not at hc
        have := hmono hθ (hsub ⟨le_rfl, hlt.le⟩) hc
        rw [hΦlo] at this; rw [ht] at htlo; linarith
      · by_contra hc
        push Not at hc
        have := hmono (hsub ⟨hlt.le, le_rfl⟩) hθ hc
        rw [hΦhi] at this; rw [ht] at hcase; linarith
    exact absurd (huk θ hmem hzero) (ne_of_gt hgt)
  · rcases le_or_gt t (Real.pi - δ) with hcase2 | hcase2
    · -- the middle: `|sin t| ≥ sinδ > |e|`, so there is no zero at all
      have := sin_le_sin_of_mem_middle hδ hδ2 hcase hcase2
      have hpos : 0 ≤ Real.sin t := le_trans (Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith) (by linarith)) le_rfl
      rw [abs_of_nonneg hpos] at habs
      linarith
    · -- the second window: uniqueness gives `θ = θk1`, contradicting `θ < θk1`
      have hmem : θ ∈ Set.Icc lo1 hi1 := by
        constructor
        · by_contra hc
          push Not at hc
          have := hmono hθ (hsub1 ⟨le_rfl, hlt1.le⟩) hc
          rw [hΦlo1] at this; rw [ht] at hcase2; linarith
        · by_contra hc
          push Not at hc
          have := hmono (hsub1 ⟨hlt1.le, le_rfl⟩) hθ hc
          rw [hΦhi1] at this; rw [ht] at hthi; linarith
      exact absurd (huk1 θ hmem hzero) (ne_of_lt hltθ)

/-- **The consecutive pair is jointly satisfiable**, instantiated rather than
inspected: at `Φ = \mathrm{id}`, `e ≡ 0`, `u_0 = π/2` and
`δ = π/4` on `[π/4, 7π/4]` both windows fit, and the conclusion is the
true statement that `cos` has zeros at `π/2` and `3π/2` in that order.

Per-`k` satisfiability would not have shown this: the point of the instance is
that the *same* parameters carry both windows at once. -/
theorem exists_two_consecutive_phase_zeros_nonvacuous :
    ∃ θk ∈ Set.Icc (Real.pi / 4) (7 * Real.pi / 4),
      ∃ θk1 ∈ Set.Icc (Real.pi / 4) (7 * Real.pi / 4), θk < θk1 ∧
        Real.cos θk + 0 = 0 ∧ Real.cos θk1 + 0 = 0 ∧
        |θk - Real.pi / 2| < Real.pi / 4 ∧
        |θk1 - (Real.pi / 2 + Real.pi)| < Real.pi / 4 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have hs2 : (0 : ℝ) < Real.sqrt 2 / 2 := by
    have := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
    linarith
  exact exists_two_consecutive_phase_zeros (Φ := fun x => x) (dΦ := fun _ => 1)
    (e := fun _ => 0) (de := fun _ => 0) (u₀ := Real.pi / 2) (δ := Real.pi / 4)
    (Ce := 0) (by linarith) Real.cos_pi_div_two (by linarith) le_rfl
    (fun x _ y _ h => h) (fun θ _ => hasDerivAt_id θ)
    (fun θ _ => hasDerivAt_const θ 0) (fun _ _ => one_pos)
    (fun _ _ => by norm_num) (fun _ _ => by rw [mul_one]; exact hs2)
    (fun _ _ => by rw [hs]; simp)
    (by linarith) (by linarith)

/-! ### `eq:local-phase-quantization`, the quantitative half

The localization puts `Φ_M(θ_k)` inside the window around its phase
point; what the spacing law needs is *how far* inside, and that it is
`O(σ^M)` rather than `O(δ)`.  The step is Jordan's inequality: near a
zero of `cos` the cosine is a sine of the offset, so a small cosine forces a
small offset with a constant that does not move with `M`. -/

/-- Jordan's inequality in the form the quantization uses: on `|x| ≤ π/2` a
small `sin` forces a small argument, at the cost of `π/2`. -/
theorem abs_le_of_abs_sin_le {x c : ℝ} (hx : |x| ≤ Real.pi / 2)
    (hsin : |Real.sin x| ≤ c) : |x| ≤ Real.pi / 2 * c := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hj := Real.mul_abs_le_abs_sin hx
  have h : 2 / Real.pi * |x| ≤ c := le_trans hj hsin
  rw [div_mul_eq_mul_div, div_le_iff₀ hπ] at h
  linarith [h]

/-- **`eq:local-phase-quantization`, the error bound.**  At a zero of
`cosΦ_M + ε` inside the window, `Φ_M` sits within
`(π/2)\|ε\|` of its phase point — so with
`\|ε\| = O(σ^M)` from `interior_cos_decomposition_on_subarc`, the
quantization error is exponentially small and its constant carries no `M`.

The identity behind it is the one that runs through this whole section: with
`cos u_0 = 0` and `σ = sin u_0`, `cos(u_0 + t) = -σsin t`, so the
cosine at the zero *is* the sine of the offset. -/
theorem phase_quantization_error {u₀ u ε C : ℝ} (hcos : Real.cos u₀ = 0)
    (hnear : |u - u₀| ≤ Real.pi / 2) (hz : Real.cos u + ε = 0) (hε : |ε| ≤ C) :
    |u - u₀| ≤ Real.pi / 2 * C := by
  have hσ2 := sigma_sq u₀ hcos
  have hσabs : |Real.sin u₀| = 1 := by
    rw [← Real.sqrt_sq_eq_abs, hσ2, Real.sqrt_one]
  have hcu : Real.cos u = -(Real.sin u₀ * Real.sin (u - u₀)) := by
    have h := Real.cos_add u₀ (u - u₀)
    rw [hcos, zero_mul, zero_sub] at h
    simpa using h
  have hsin : |Real.sin (u - u₀)| ≤ C := by
    have h1 : |Real.sin u₀ * Real.sin (u - u₀)| = |Real.sin (u - u₀)| := by
      rw [abs_mul, hσabs, one_mul]
    have h2 : Real.sin u₀ * Real.sin (u - u₀) = ε := by
      have : -(Real.sin u₀ * Real.sin (u - u₀)) + ε = 0 := by rw [← hcu]; exact hz
      linarith
    rw [← h1, h2]; exact hε
  exact abs_le_of_abs_sin_le hnear hsin

/-- **`hquant` is an identity, not an estimate.**  With the quantization errors
*defined* as the offsets of `Φ_M` from its two phase points, the relation
`Consequences.local_clock_spacing` consumes is `eq:Phi-def` rearranged and
nothing more — the analytic content sits entirely in
`phase_quantization_error`'s bound on those offsets.

Recording it as a theorem rather than inlining it is deliberate: it is exactly
the kind of step that reads as an assumption when it is written as a hypothesis,
and it has no content to assume. -/
theorem phase_quantization_identity {Φ ψ : ℝ → ℝ} {L θk θk1 u₀ : ℝ}
    (hΦ : ∀ θ : ℝ, Φ θ = L * θ - ψ θ) :
    Real.pi + ((Φ θk1 - (u₀ + Real.pi)) - (Φ θk - u₀))
      = L * (θk1 - θk) - (ψ θk1 - ψ θk) := by
  rw [hΦ θk, hΦ θk1]; ring

end ForgacsTran
