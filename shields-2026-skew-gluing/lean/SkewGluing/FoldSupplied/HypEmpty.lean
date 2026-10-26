import SkewGluing.FoldSupplied.EmptyLift
import SkewGluing.SmallOverlap.EmptyFold
import SkewGluing.Lines.FirstWindow

/-!
# `lem:gluing-small`, empty root: the periodicity of the completed words from the partner root

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small overlaps»
(`lem:gluing-small`, the paragraph on the actual supplied empty inner): a proper root of width zero
with supplied inner `E` of span `p`, and a second proper root of period `Q` with neither period
dividing the other and `g = gcd (p, Q) > 1`.  By `lem:gluing-periods` (ii) the joining positions
`g, 2g, …, p - g` of the first `p`-window carry one common value in each word.  The equal full
flag ranks of `E` (the heights at `0` and `p - 1` both equal one) then give
`R Δ + (R - 1)(λ_Y - λ_X) = 0` with `R = p / g`, which forces `λ_X = λ_Y`.

* `FoldSupplied.common_value_of_heights`: the arithmetic of that equation;
* `FoldSupplied.partner_holes`: the second root contributes one exceptional residue to each word;
* `FoldSupplied.empty_fold_of_partner_root`: the empty fold of the supplied inner, lifted to the
  parent, with no hypothesis beyond the two roots.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open MarkedInner SmallOverlap

/-- The arithmetic of `R Δ + (R - 1)(λ_Y - λ_X) = 0`.  Two bit words on `1, …, p - 1`, `p = R g`,
`R ≥ 2`, which repeat with step `g` off the multiples of `g`, take the common values `a g` and
`b g` at the positive multiples of `g`, and have heights one at both ends, have `a g = b g`. -/
theorem common_value_of_heights {a b : ℕ → ℤ} {g R : ℕ} (hg : 0 < g) (hR : 2 ≤ R)
    (ha : ∀ k, 1 ≤ k → k < R * g → a k = 0 ∨ a k = 1)
    (hb : ∀ k, 1 ≤ k → k < R * g → b k = 0 ∨ b k = 1)
    (hsum : ∑ m ∈ Finset.range (R * g - 1), (a (m + 1) - b (m + 1)) = 0)
    (hstep : ∀ k, g < k → k < R * g → k % g ≠ 0 → a k = a (k - g) ∧ b k = b (k - g))
    (hmul : ∀ j, 1 ≤ j → j < R → a (j * g) = a g ∧ b (j * g) = b g) : a g = b g := by
  obtain ⟨c0, hc0⟩ : ∃ c : ℤ, c = a g - b g := ⟨_, rfl⟩
  let P : ℕ → ℤ := fun m => if m % g = 0 then c0 else a (m % g) - b (m % g)
  have hg1 : 1 ≤ g * 1 := by omega
  have hgR : g ≤ R * g := by nlinarith
  have hP : ∀ m, 1 ≤ m → m < R * g → a m - b m = P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm1 hm2
      by_cases h0 : m % g = 0
      · obtain ⟨j, hj⟩ := Nat.dvd_of_mod_eq_zero h0
        have hj1 : 1 ≤ j := by
          rcases Nat.eq_zero_or_pos j with h | h
          · subst h; omega
          · exact h
        have hjR : j < R := by
          by_contra hcon
          have : R * g ≤ j * g := Nat.mul_le_mul_right g (by omega)
          rw [hj] at hm2
          nlinarith
        have := hmul j hj1 hjR
        have e : m = j * g := by rw [hj]; ring
        rw [e, this.1, this.2]
        simp only [P, Nat.mul_mod_left, ite_true]
        omega
      · by_cases hlt : m < g
        · simp only [P]
          rw [ite_eq_right_of_eq_false _ _ (eq_false h0), Nat.mod_eq_of_lt hlt]
        · have hgm : g < m := by
            rcases Nat.lt_or_ge g m with h | h
            · exact h
            · exfalso; apply h0; have : m = g := by omega
              rw [this]; exact Nat.mod_self g
          have hs := hstep m hgm hm2 h0
          have ih' := ih (m - g) (by omega) (by omega) (by omega)
          have e : (m - g) % g = m % g := by
            have : m = (m - g) + g := by omega
            conv_rhs => rw [this]
            rw [Nat.add_mod_right]
          have e0 : ¬ ((m - g) % g = 0) := by rw [e]; exact h0
          rw [hs.1, hs.2, ih']
          simp [P, h0, e]
  have hperiodic : ∀ n x, P (n * g + x) = P x := by
    intro n x
    simp only [P, Nat.mul_comm n g, Nat.mul_add_mod]
  have hblocks : ∀ n, ∑ m ∈ Finset.range (n * g), P m = n * ∑ m ∈ Finset.range g, P m := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have : ∑ x ∈ Finset.range g, P (n * g + x) = ∑ m ∈ Finset.range g, P m :=
        Finset.sum_congr rfl fun x _ => hperiodic n x
      rw [this]; push_cast; ring
  -- the sum over a full period, split at zero
  have hpos : R * g - 1 + 1 = R * g := by omega
  have hsum2 : ∑ m ∈ Finset.range (R * g - 1), P (m + 1) = 0 := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    exact (hP (m + 1) (by omega) (by omega)).symm
  have hsplit : ∑ m ∈ Finset.range (R * g), P m =
      ∑ m ∈ Finset.range (R * g - 1), P (m + 1) + P 0 := by
    have := Finset.sum_range_succ' P (R * g - 1)
    rw [hpos] at this
    exact this
  have hP0 : P 0 = c0 := by simp [P]
  have hgsplit : ∑ m ∈ Finset.range g, P m =
      ∑ m ∈ Finset.range (g - 1), P (m + 1) + P 0 := by
    have := Finset.sum_range_succ' P (g - 1)
    rw [show g - 1 + 1 = g by omega] at this
    exact this
  rw [hsum2, zero_add, hP0, hblocks R, hgsplit, hP0] at hsplit
  set S := ∑ m ∈ Finset.range (g - 1), P (m + 1)
  -- R * (S + c0) = c0
  have hdiv : (R : ℤ) ∣ c0 := by
    refine ⟨S + c0 - 0, ?_⟩
    nlinarith [hsplit]
  have hc0b : c0 = 0 ∨ c0 = 1 ∨ c0 = -1 := by
    have h1 := ha g (by omega) (by nlinarith)
    have h2 := hb g (by omega) (by nlinarith)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [hc0, h1, h2]
  rcases hc0b with h | h | h
  · linarith
  · exfalso
    rw [h] at hdiv
    have := Int.le_of_dvd one_pos hdiv
    omega
  · exfalso
    rw [h] at hdiv
    have := Int.le_of_dvd one_pos ((Int.dvd_neg).mp hdiv)
    omega

variable {χ₁ χ₂ : Chart} {F : Diagram} {p Q : ℕ}

/-- The second root contributes one exceptional residue `h ∈ [0, u]` modulo `Q` to each boundary
word of the diagram, `u` the width of its mark, when its mark is empty or ordinary. -/
theorem partner_holes (h₂ : χ₂.IsProperRoot F Q) (hord : χ₂.ω.W = ∅ ∨ ¬ χ₂.ω.case.IsMixed) :
    ∃ hA hB : ℤ, (0 ≤ hA ∧ hA ≤ (χ₂.ω.width : ℤ)) ∧ (0 ≤ hB ∧ hB ≤ (χ₂.ω.width : ℤ)) ∧
      PeriodWords.PeriodExcept (span F - 1) Q {hA} (wordA F) ∧
      PeriodWords.PeriodExcept (span F - 1) Q {hB} (wordB F) := by
  by_cases hW₂ : χ₂.ω.W = ∅
  · have e2 := h₂.periodic_empty hW₂
    have hw2 : χ₂.ω.width = 0 := width_eq_zero_of_eq_empty hW₂
    exact ⟨0, 0, by omega, by omega, e2.1, e2.2⟩
  · have hWne : χ₂.ω.W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hW₂
    have hmix : ¬ χ₂.ω.case.IsMixed := hord.resolve_left hW₂
    have hlegal2 : χ₂.ω.IsLegalNonempty := ⟨h₂.1.2.2.2, hWne⟩
    obtain ⟨s, t, hph⟩ := hlegal2.exists_phases
    obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
    have e2 := h₂.periodic_nonempty hWne hph
    have hwZ : χ₂.ω.widthZ = (χ₂.ω.width : ℤ) := rfl
    have hcc : χ₂.ω.case = .a ∨ χ₂.ω.case = .b := by
      unfold AttachCase.IsMixed at hmix
      cases hh : χ₂.ω.case <;> simp_all
    rcases hcc with hc | hc
    · simp only [holesA, holesB, hc] at e2
      exact ⟨t, s, by omega, by omega, e2.1, e2.2⟩
    · simp only [holesA, holesB, hc] at e2
      exact ⟨s, t, by omega, by omega, e2.1, e2.2⟩

/-- The periodicity of the completed native words of the supplied empty inner `E` of `χ₁`, from the
second root: with `g = gcd (p, Q)`, there is `lam ∈ {0, 1}` for which both completed words are
`g`-periodic, and `g` divides the span of `E` with `g < span E`. -/
theorem empty_partner_periodic (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q)
    (hW₁ : χ₁.ω.W = ∅) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) (hg : 1 < Nat.gcd p Q) :
    ∃ lam : ℤ, (lam = 0 ∨ lam = 1) ∧ span χ₁.ω.E = p ∧
      (∀ k, Nat.gcd p Q ≤ k → k < p →
        completedA χ₁.ω.E lam k = completedA χ₁.ω.E lam (k - Nat.gcd p Q)) ∧
      (∀ k, Nat.gcd p Q ≤ k → k < p →
        completedB χ₁.ω.E lam k = completedB χ₁.ω.E lam (k - Nat.gcd p Q)) := by
  set g := Nat.gcd p Q with hgdef
  obtain ⟨hr, hN1, -, hp2⟩ := h₁.arith
  obtain ⟨hm, hN2, hwQ, hQ2⟩ := h₂.arith
  have hw1 : χ₁.ω.width = 0 := width_eq_zero_of_eq_empty hW₁
  have hNp : span F = span χ₁.D * p := by
    have : (span F : ℤ) = (span χ₁.D : ℤ) * p := by rw [hN1, hw1]; simp
    exact_mod_cast this
  have hNQ : span F = span χ₂.D * Q + χ₂.ω.width := by exact_mod_cast hN2
  have hwQ' : χ₂.ω.width < Q := by exact_mod_cast hwQ
  have hp0 : 0 < p := by omega
  have hQ0 : 0 < Q := by omega
  have hord : χ₂.ω.W = ∅ ∨ ¬ χ₂.ω.case.IsMixed := by
    by_cases hW₂ : χ₂.ω.W = ∅
    · exact Or.inl hW₂
    · refine Or.inr fun hmix => ?_
      exact h₁.empty_mixed_false h₂ hW₁ (Finset.nonempty_iff_ne_empty.mpr hW₂) hmix hpQ hQp
  have hper := h₁.empty_ordinary_periodic h₂ hW₁ hord hpQ hQp
  have e1 := h₁.periodic_empty hW₁
  obtain ⟨hA, hB, hhA, hhB, eA, eB⟩ := partner_holes h₂ hord
  -- the shape of the root
  have hgp : g ∣ p := Nat.gcd_dvd_left p Q
  have hg0 : 0 < g := by omega
  have hgle : g ≤ p := Nat.le_of_dvd hp0 hgp
  have hglt : g < p := by
    rcases hgle.lt_or_eq with h | h
    · exact h
    · exfalso; apply hpQ; rw [← h]; exact Nat.gcd_dvd_right p Q
  obtain ⟨R, hR⟩ := hgp
  have hR2 : 2 ≤ R := by
    by_contra hcon
    have : R ≤ 1 := by omega
    interval_cases R <;> omega
  have hpR : R * g = p := by rw [hR]; ring
  -- the inner E and its words
  have hE : IsConnectedSkew χ₁.ω.E := h₁.1.2.2.2.1.1
  have hmark : χ₁.ω = emptyMarkH χ₁.ω.E := h₁.1.eq_emptyMarkH hW₁
  have hperZ : χ₁.period = (span χ₁.ω.E : ℤ) := by
    change χ₁.ω.period = _
    rw [hmark]; exact OrdinaryFold.emptyMarkH_period hE
  have hpZ : χ₁.period = (p : ℤ) := h₁.2.2
  have hspE : span χ₁.ω.E = p := by
    have : (span χ₁.ω.E : ℤ) = p := by rw [← hperZ, hpZ]
    exact_mod_cast this
  have hbd : IsBitData (span χ₁.ω.E) (fun k : ℕ => wordA χ₁.ω.E k)
      (fun k : ℕ => wordB χ₁.ω.E k) := isBitData_of_isConnectedSkew hE
  rw [hspE] at hbd
  have hpm : p - 1 + 1 = p := by omega
  -- words of F against words of E on the first window
  have hFE_A : ∀ k : ℕ, 1 ≤ k → k < p → wordA F (k : ℤ) = wordA χ₁.ω.E (k : ℤ) := by
    intro k hk1 hk2
    rw [h₁.wordA_eq (by exact_mod_cast hk1) (by
      have : p < span F := by rw [hNp]; nlinarith
      exact_mod_cast (by omega : k < span F))]
    exact h₁.1.2.2.2.wordA_compose_first h₁.1.1 (by exact_mod_cast hk1) (by
      have : χ₁.ω.period = p := hpZ
      omega)
  have hFE_B : ∀ k : ℕ, 1 ≤ k → k < p → wordB F (k : ℤ) = wordB χ₁.ω.E (k : ℤ) := by
    intro k hk1 hk2
    rw [h₁.wordB_eq (by exact_mod_cast hk1) (by
      have : p < span F := by rw [hNp]; nlinarith
      exact_mod_cast (by omega : k < span F))]
    exact h₁.1.2.2.2.wordB_compose_first h₁.1.1 (by exact_mod_cast hk1) (by
      have : χ₁.ω.period = p := hpZ
      omega)
  -- the periodicity facts
  have hpN : p < span F := by rw [hNp]; nlinarith
  have hL : span F - 1 + 1 = span F := by omega
  have win : ∀ (f : ℤ → ℤ) (h : ℤ), (0 ≤ h ∧ h ≤ (χ₂.ω.width : ℤ)) →
      PeriodWords.PeriodExcept (span F - 1) p {(0 : ℤ)} f →
      PeriodWords.PeriodExcept (span F - 1) Q {h} f → ∀ x y : ℕ, 1 ≤ x → x < p → 1 ≤ y → y < p →
      g ∣ x → g ∣ y → f (x : ℤ) = f (y : ℤ) := by
    intro f h hh hfp hfQ x y hx1 hx2 hy1 hy2 hgx hgy
    have hsh : ∀ z : ℕ, 1 ≤ z → z < p →
        ¬ PeriodWords.IsSimultaneousHole p Q {(0 : ℤ)} {h} (z : ℤ) := by
      intro z hz1 hz2 hsh'
      have h0 : (z : ℤ) % (p : ℤ) = 0 := by simpa using hsh'.1
      rw [Int.emod_eq_of_lt (by omega) (by omega)] at h0
      omega
    refine PeriodWords.eq_of_periods_two_holes (p := p) (Q := Q) (N := span F) (r := span χ₁.D)
      (m := span χ₂.D) (w := 0) (u := χ₂.ω.width) (h₁ := 0) (h₂ := h)
      hp0 hQ0 hr hm hp0 hwQ' (by rw [hNp]; simp) hNQ hpQ hQp (by simp) hh hL hfp hfQ
      (Finset.mem_Icc.mpr ⟨by exact_mod_cast hx1, by
        push_cast [Nat.cast_sub (show 1 ≤ span F by omega)]; omega⟩)
      (Finset.mem_Icc.mpr ⟨by exact_mod_cast hy1, by
        push_cast [Nat.cast_sub (show 1 ≤ span F by omega)]; omega⟩)
      ?_ (hsh x hx1 hx2) (hsh y hy1 hy2)
    have : (g : ℤ) ∣ (y : ℤ) - x := dvd_sub (Int.natCast_dvd_natCast.mpr hgy)
      (Int.natCast_dvd_natCast.mpr hgx)
    simpa using this
  have stepA : ∀ k : ℕ, g < k → k < p → k % g ≠ 0 →
      wordA F (k : ℤ) = wordA F ((k - g : ℕ) : ℤ) := by
    intro k hk1 hk2 hk3
    have hx : ((k - g : ℕ) : ℤ) ∈ Finset.Icc (1 : ℤ) (((span F - 1 : ℕ) : ℤ) - g) := by
      rw [Finset.mem_Icc]; push_cast [Nat.cast_sub (show 1 ≤ span F by omega),
        Nat.cast_sub (show g ≤ k by omega)]; omega
    have hS : ((k - g : ℕ) : ℤ) % (g : ℤ) ∉ ({0} : Finset ℤ) := by
      simp only [Finset.mem_singleton]
      intro h; apply hk3
      have : (g : ℤ) ∣ ((k - g : ℕ) : ℤ) := Int.dvd_of_emod_eq_zero h
      have h2 : g ∣ k - g := Int.natCast_dvd_natCast.mp this
      have h3 : g ∣ k := by
        have := Nat.dvd_add h2 (dvd_refl g)
        rwa [Nat.sub_add_cancel (by omega)] at this
      exact Nat.mod_eq_zero_of_dvd h3
    have := hper.1 _ hx hS
    rw [show ((k - g : ℕ) : ℤ) + g = k by
      push_cast [Nat.cast_sub (show g ≤ k by omega)]; ring] at this
    exact this.symm
  have stepB : ∀ k : ℕ, g < k → k < p → k % g ≠ 0 →
      wordB F (k : ℤ) = wordB F ((k - g : ℕ) : ℤ) := by
    intro k hk1 hk2 hk3
    have hx : ((k - g : ℕ) : ℤ) ∈ Finset.Icc (1 : ℤ) (((span F - 1 : ℕ) : ℤ) - g) := by
      rw [Finset.mem_Icc]; push_cast [Nat.cast_sub (show 1 ≤ span F by omega),
        Nat.cast_sub (show g ≤ k by omega)]; omega
    have hS : ((k - g : ℕ) : ℤ) % (g : ℤ) ∉ ({0} : Finset ℤ) := by
      simp only [Finset.mem_singleton]
      intro h; apply hk3
      have : (g : ℤ) ∣ ((k - g : ℕ) : ℤ) := Int.dvd_of_emod_eq_zero h
      have h2 : g ∣ k - g := Int.natCast_dvd_natCast.mp this
      have h3 : g ∣ k := by
        have := Nat.dvd_add h2 (dvd_refl g)
        rwa [Nat.sub_add_cancel (by omega)] at this
      exact Nat.mod_eq_zero_of_dvd h3
    have := hper.2 _ hx hS
    rw [show ((k - g : ℕ) : ℤ) + g = k by
      push_cast [Nat.cast_sub (show g ≤ k by omega)]; ring] at this
    exact this.symm
  have mulA : ∀ k : ℕ, 1 ≤ k → k < p → g ∣ k → wordA F (k : ℤ) = wordA F (g : ℤ) :=
    fun k hk1 hk2 hk3 => win _ hA hhA e1.1 eA k g hk1 hk2 (by omega) hglt hk3 (dvd_refl g)
  have mulB : ∀ k : ℕ, 1 ≤ k → k < p → g ∣ k → wordB F (k : ℤ) = wordB F (g : ℤ) :=
    fun k hk1 hk2 hk3 => win _ hB hhB e1.2 eB k g hk1 hk2 (by omega) hglt hk3 (dvd_refl g)
  -- the words of E
  have hbitE : ∀ k : ℕ, 1 ≤ k → k < p →
      (wordA χ₁.ω.E (k : ℤ) = 0 ∨ wordA χ₁.ω.E (k : ℤ) = 1) ∧
      (wordB χ₁.ω.E (k : ℤ) = 0 ∨ wordB χ₁.ω.E (k : ℤ) = 1) := fun k hk1 hk2 =>
    hbd.2.1 k hk1 hk2
  have hcommon : wordA χ₁.ω.E (g : ℤ) = wordB χ₁.ω.E (g : ℤ) := by
    refine common_value_of_heights (a := fun k : ℕ => wordA χ₁.ω.E (k : ℤ))
      (b := fun k : ℕ => wordB χ₁.ω.E (k : ℤ)) (g := g) (R := R) hg0 hR2
      (fun k hk1 hk2 => (hbitE k hk1 (by rw [← hpR]; exact hk2)).1)
      (fun k hk1 hk2 => (hbitE k hk1 (by rw [← hpR]; exact hk2)).2) ?_ ?_ ?_
    · have h1 : 1 + ∑ m ∈ Finset.range (p - 1),
          (wordA χ₁.ω.E ((m + 1 : ℕ) : ℤ) - wordB χ₁.ω.E ((m + 1 : ℕ) : ℤ)) = 1 := hbd.2.2.2
      rw [hpR]
      linarith
    · intro k hk1 hk2 hk3
      have hkp : k < p := by rw [← hpR]; exact hk2
      rw [← hFE_A k (by omega) hkp, ← hFE_B k (by omega) hkp,
        ← hFE_A (k - g) (by omega) (by omega), ← hFE_B (k - g) (by omega) (by omega)]
      exact ⟨stepA k hk1 hkp hk3, stepB k hk1 hkp hk3⟩
    · intro j hj1 hjR
      have hjg : j * g < p := hpR ▸ Nat.mul_lt_mul_of_pos_right hjR hg0
      have hjg1 : 1 ≤ j * g := Nat.mul_pos hj1 hg0
      have hgp' : g < p := hglt
      rw [← hFE_A (j * g) hjg1 hjg, ← hFE_B (j * g) hjg1 hjg, ← hFE_A g (by omega) hgp',
        ← hFE_B g (by omega) hgp']
      exact ⟨mulA (j * g) hjg1 hjg (Dvd.intro_left j rfl), mulB (j * g) hjg1 hjg
        (Dvd.intro_left j rfl)⟩
  obtain ⟨lam, hlamdef⟩ : ∃ l : ℤ, l = wordA χ₁.ω.E (g : ℤ) := ⟨_, rfl⟩
  have hlam : lam = 0 ∨ lam = 1 := by rw [hlamdef]; exact (hbitE g (by omega) hglt).1
  -- the completed words are g-periodic
  have key : ∀ k : ℕ, g ≤ k → k < p →
      (if k = 0 then lam else wordA χ₁.ω.E (k : ℤ)) =
        (if k - g = 0 then lam else wordA χ₁.ω.E ((k - g : ℕ) : ℤ)) ∧
      (if k = 0 then lam else wordB χ₁.ω.E (k : ℤ)) =
        (if k - g = 0 then lam else wordB χ₁.ω.E ((k - g : ℕ) : ℤ)) := by
    intro k hk1 hk2
    have hk0 : k ≠ 0 := by omega
    by_cases hkg : k = g
    · subst hkg
      simp only [hk0, Nat.sub_self, ite_false, ite_true]
      exact ⟨hlamdef.symm, by rw [← hcommon]; exact hlamdef.symm⟩
    · have hgk : g < k := by omega
      have hkm1 : 1 ≤ k - g := by omega
      have hkgne : k - g ≠ 0 := by omega
      simp only [hk0, hkgne, ite_false]
      rw [← hFE_A k (by omega) hk2, ← hFE_B k (by omega) hk2,
        ← hFE_A (k - g) hkm1 (by omega), ← hFE_B (k - g) hkm1 (by omega)]
      by_cases hmod : k % g = 0
      · have hgdk : g ∣ k := Nat.dvd_of_mod_eq_zero hmod
        have hgdk' : g ∣ k - g := by
          have := Nat.dvd_sub hgdk (dvd_refl g)
          exact this
        rw [mulA k (by omega) hk2 hgdk, mulA (k - g) hkm1 (by omega) hgdk',
          mulB k (by omega) hk2 hgdk, mulB (k - g) hkm1 (by omega) hgdk']
        exact ⟨rfl, rfl⟩
      · exact ⟨stepA k hgk hk2 hmod, stepB k hgk hk2 hmod⟩
  refine ⟨lam, hlam, hspE, fun k hk1 hk2 => ?_, fun k hk1 hk2 => ?_⟩
  · simpa [completedA] using (key k hk1 hk2).1
  · simpa [completedB] using (key k hk1 hk2).2

/-- **The empty fold of a supplied empty inner, from the two roots** (`lem:gluing-small`).  Let
`χ₁` be a proper legal root of `F` of period `p` whose mark is empty, and `χ₂` a proper legal root
of period `Q`, neither period dividing the other, with `g = gcd (p, Q) > 1`.  Then there are a
common value `λ ∈ {0, 1}` of the joining positions of the supplied inner `E` of `χ₁`, a proper
legal chart `ψ` of `E` of period `g` with the empty mark and outer the row or column of `p / g`
cells, and a proper legal chart `χ'` of `F` of period `g` with empty mark, whose inner is that of
`ψ` up to translation and whose outer is the composite of a legal mark on `ψ.D` with `γ (χ₁.D)`,
`γ ∈ {id, AT}`.  No periodicity hypothesis is taken: it is derived from the second root. -/
theorem empty_fold_of_partner_root (h₁ : χ₁.IsProperRoot F p) (h₂ : χ₂.IsProperRoot F Q)
    (hW₁ : χ₁.ω.W = ∅) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) (hg : 1 < Nat.gcd p Q) :
    ∃ (lam : ℤ) (χ' ψ : Chart) (μ : MarkedInner) (γ : Diagram → Diagram) (u : ℤ × ℤ),
      (lam = 0 ∨ lam = 1) ∧
      ψ.IsProperLegal ∧ ψ.IsChartOf χ₁.ω.E ∧ ψ.period = (Nat.gcd p Q : ℤ) ∧ ψ.ω.W = ∅ ∧
      ψ.D = lineOuter (p / Nat.gcd p Q) lam ∧
      χ'.IsProperLegal ∧ χ'.IsChartOf F ∧ χ'.ω = ψ.ω.translate u ∧
        χ'.period = (Nat.gcd p Q : ℤ) ∧ χ'.ω.W = ∅ ∧
      μ.IsLegal ∧ μ.E = ψ.D ∧ (γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)) ∧
      χ'.D = μ.compose (γ χ₁.D) := by
  obtain ⟨lam, hlam, hspE, hA, hB⟩ := empty_partner_periodic h₁ h₂ hW₁ hpQ hQp hg
  have hp0 : 0 < p := by have := h₁.arith.2.2.2; omega
  have hgp : Nat.gcd p Q ∣ p := Nat.gcd_dvd_left p Q
  have hglt : Nat.gcd p Q < p := by
    rcases (Nat.le_of_dvd hp0 hgp).lt_or_eq with h | h
    · exact h
    · exfalso; apply hpQ; rw [← h]; exact Nat.gcd_dvd_right p Q
  obtain ⟨χ', ψ, μ, γ, u, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13⟩ :=
    empty_fold_lift h₁.1 h₁.2.1 hW₁ hg (by rw [hspE]; exact hglt) (by rw [hspE]; exact hgp) hlam
      (fun k hk1 hk2 => hA k hk1 (by rwa [hspE] at hk2))
      (fun k hk1 hk2 => hB k hk1 (by rwa [hspE] at hk2))
  refine ⟨lam, χ', ψ, μ, γ, u, hlam, k1, k2, k3, k4, by rw [k5, hspE], k6, k7, k8, k9, k10, k11,
    k12, k13⟩

end FoldSupplied
end SkewGluing
