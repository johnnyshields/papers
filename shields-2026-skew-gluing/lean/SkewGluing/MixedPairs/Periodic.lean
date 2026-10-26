import SkewGluing.MixedPairs.Bridge

/-!
# Pairs involving mixed charts, on bit words

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`lem:gluing-collision`, `lem:gluing-incompatible`, and the paragraph opening the subsection).

Everything here is a statement about two boundary codings (`MixFoldCoding`) of the same pair of
bit words `A, B` of a parent of span `N`.  For a case-(d) chart `c₁` of period `p` and a second
chart `c₂` of period `Q`, with neither period dividing the other, the word `B` is `gcd p Q`-periodic
(`mixFold_B_periodic`: `lem:gluing-periods` (i) against an ordinary or empty chart, the two full
periods against another case-(d) chart, and (iii) against a case-(c) chart of larger period).  The
private bits `B_w = 1`, `B_q = 0` of `c₁` then contradict the periodicity at remainder zero
(`mixFold_remainder_zero_words`) and against every ordinary chart (`mixFold_mixed_ordinary_words`);
`mixFold_collision_words` is `lem:gluing-collision`, and `mixFold_opposite_words` is the
opposite-mixed half of `lem:gluing-incompatible`.

Sorry-free.
-/

namespace SkewGluing

open PeriodWords

theorem mixFold_periodExcept_mono {α : Type*} {L p : ℕ} {S S' : Finset ℤ} {f : ℤ → α}
    (hS : S ⊆ S') (h : PeriodExcept L p S f) : PeriodExcept L p S' f :=
  fun x hx hx' => h x hx (fun hh => hx' (hS hh))

/-- The position-`x`, position-`y` equality of a word with a full period `g`, in range. -/
theorem mixFold_eq_of_gcd_dvd {f : ℤ → ℤ} {N g : ℕ} (hg : 0 < g) (hf : PeriodExcept (N - 1) g ∅ f)
    {x y : ℤ} (hx1 : 1 ≤ x) (hx2 : x ≤ (N : ℤ) - 1) (hy1 : 1 ≤ y) (hy2 : y ≤ (N : ℤ) - 1)
    (hxy : (g : ℤ) ∣ y - x) : f x = f y := by
  have hN : 1 ≤ N := by omega
  refine mixFold_eq_of_period_empty hg hf ?_ ?_ hxy
  · rw [Finset.mem_Icc]; push_cast [hN]; omega
  · rw [Finset.mem_Icc]; push_cast [hN]; omega

namespace MixFoldCoding

variable {A B : ℤ → ℤ} {N q w : ℕ} {case : AttachCase} {s t : ℤ}

/-- A coding leaves `B` at most two exceptional residues in `[0, w]`, and at most one unless the
case is (c). -/
theorem exists_holesB (h : MixFoldCoding A B N q w case s t) :
    ∃ T : Finset ℤ, (∀ x ∈ T, 0 ≤ x ∧ x ≤ (w : ℤ)) ∧ T.card ≤ 2 ∧ (case ≠ .c → T.card ≤ 1) ∧
      PeriodExcept (N - 1) q T B := by
  by_cases hw : w = 0
  · refine ⟨{0}, by simp [hw], by simp, fun _ => by simp, ?_⟩
    simpa [codingHolesB, hw] using h.perB
  · obtain ⟨hs1, hs2, ht1, ht2, -⟩ := h.phases (Nat.pos_of_ne_zero hw)
    have hp := h.perB
    simp only [codingHolesB, hw, ite_false] at hp
    cases hc : case
    · rw [hc] at hp
      exact ⟨{s}, by simp [holesB] at *; omega, by simp, fun _ => by simp, hp⟩
    · rw [hc] at hp
      exact ⟨{t}, by simp [holesB] at *; omega, by simp, fun _ => by simp, hp⟩
    · rw [hc] at hp
      refine ⟨{t, s}, ?_, Finset.card_le_two, fun hh => absurd rfl hh, hp⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      omega
    · rw [hc] at hp
      exact ⟨∅, by simp, by simp, fun _ => by simp, hp⟩

end MixFoldCoding

/-- **The fixed boundary of a mixed chart becomes `g`-periodic.**  A case-(d) chart of period `p`
and positive width, and a second chart of period `Q`, neither period dividing the other, with the
second chart of case (c) only when its period is the larger: the word `B` has period
`g = gcd p Q`.  This is `lem:gluing-periods` (i) against an ordinary or empty chart, the two full
periods against a case-(d) chart, and (iii) against a case-(c) chart. -/
theorem mixFold_B_periodic {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {case₂ : AttachCase} {s₁ t₁ s₂ t₂ : ℤ}
    (c₁ : MixFoldCoding A B N p w₁ .d s₁ t₁) (hw₁ : 0 < w₁)
    (c₂ : MixFoldCoding A B N Q w₂ case₂ s₂ t₂) (hcase : case₂ = .c → p < Q)
    (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) : PeriodExcept (N - 1) (Nat.gcd p Q) ∅ B := by
  have hN1 := c₁.two_q_add_w_le
  have hN2 := c₂.two_q_add_w_le
  have hp := c₁.q_pos
  have hQ := c₂.q_pos
  have hfp : PeriodExcept (N - 1) p ∅ B := by
    have := c₁.perB
    simpa [codingHolesB, hw₁.ne', holesB] using this
  obtain ⟨T, hTb, hTc, hT1, hfQ⟩ := c₂.exists_holesB
  rcases lt_or_gt_of_ne (show p ≠ Q from fun h => hpQ (h ▸ dvd_refl p)) with hlt | hgt
  · exact periodExcept_gcd_full_two_holes (u := w₂) hp hlt c₂.w_lt hTb hTc (by omega) hfp hfQ
  · have hcase' : case₂ ≠ .c := fun hc => by have := hcase hc; omega
    have hc1 := hT1 hcase'
    obtain ⟨h, hh⟩ := Finset.card_le_one_iff_subset_singleton.mp hc1
    have hfQ' : PeriodExcept (N - 1) Q {h} B := mixFold_periodExcept_mono hh hfQ
    have := periodExcept_gcd_one_hole hp hQ hpQ hQp h (by rw [max_eq_left hgt.le]; omega) hfp hfQ'
    exact this

/-- The widths of two charts of one parent are congruent modulo the gcd of their periods, to the
span: `N ≡ w₁ ≡ w₂ (mod g)`. -/
theorem mixFold_gcd_dvd_N_sub {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {case₁ case₂ : AttachCase}
    {s₁ t₁ s₂ t₂ : ℤ} (c₁ : MixFoldCoding A B N p w₁ case₁ s₁ t₁)
    (c₂ : MixFoldCoding A B N Q w₂ case₂ s₂ t₂) :
    ((Nat.gcd p Q : ℕ) : ℤ) ∣ (N : ℤ) - w₁ ∧ ((Nat.gcd p Q : ℕ) : ℤ) ∣ (N : ℤ) - w₂ := by
  obtain ⟨r₁, -, h₁⟩ := c₁.span_eq
  obtain ⟨r₂, -, h₂⟩ := c₂.span_eq
  have hp : ((Nat.gcd p Q : ℕ) : ℤ) ∣ p := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)
  have hQ : ((Nat.gcd p Q : ℕ) : ℤ) ∣ Q := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right p Q)
  constructor
  · have : (N : ℤ) - w₁ = r₁ * p := by rw [h₁]; push_cast; ring
    rw [this]; exact dvd_mul_of_dvd_right hp _
  · have : (N : ℤ) - w₂ = r₂ * Q := by rw [h₂]; push_cast; ring
    rw [this]; exact dvd_mul_of_dvd_right hQ _

/-- **Mixed pairs at remainder zero are impossible** (words).  A case-(d) chart of positive width
and a second chart, neither period dividing the other, the second of case (c) only if its period is
larger: if `g = gcd p Q` divides `N`, the private bits `B_w = 1`, `B_q = 0` contradict the
`g`-periodicity of `B`. -/
theorem mixFold_remainder_zero_words {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {case₂ : AttachCase}
    {s₁ t₁ s₂ t₂ : ℤ} (c₁ : MixFoldCoding A B N p w₁ .d s₁ t₁) (hw₁ : 0 < w₁)
    (c₂ : MixFoldCoding A B N Q w₂ case₂ s₂ t₂) (hcase : case₂ = .c → p < Q)
    (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) (hrem : N % Nat.gcd p Q = 0) : False := by
  have hper := mixFold_B_periodic c₁ hw₁ c₂ hcase hpQ hQp
  have hg : 0 < Nat.gcd p Q := Nat.gcd_pos_of_pos_left _ c₁.q_pos
  have hN1 := c₁.two_q_add_w_le
  obtain ⟨hd1, -⟩ := mixFold_gcd_dvd_N_sub c₁ c₂
  have hdN : ((Nat.gcd p Q : ℕ) : ℤ) ∣ (N : ℤ) :=
    Int.natCast_dvd_natCast.2 (Nat.dvd_of_mod_eq_zero hrem)
  have hdw : ((Nat.gcd p Q : ℕ) : ℤ) ∣ (w₁ : ℤ) := by
    have := dvd_sub hdN hd1
    simpa using this
  have hdp : ((Nat.gcd p Q : ℕ) : ℤ) ∣ (p : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)
  obtain ⟨-, -, -, -, hBw, hBq⟩ := c₁.caps_d hw₁ rfl
  have hwq := c₁.w_lt
  have := mixFold_eq_of_gcd_dvd hg hper (x := w₁) (y := p) (by omega) (by omega) (by omega)
    (by omega) (by simpa using dvd_sub hdp hdw)
  omega

/-- **`lem:gluing-incompatible`, mixed/ordinary, words.**  A case-(d) chart of positive width and a
nonempty ordinary chart of period `Q`, neither period dividing the other, cannot code one parent.
-/
theorem mixFold_mixed_ordinary_words {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {case₂ : AttachCase}
    {s₁ t₁ s₂ t₂ : ℤ} (c₁ : MixFoldCoding A B N p w₁ .d s₁ t₁) (hw₁ : 0 < w₁)
    (c₂ : MixFoldCoding A B N Q w₂ case₂ s₂ t₂) (hw₂ : 0 < w₂) (hord : ¬ case₂.IsMixed)
    (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) : False := by
  have hper := mixFold_B_periodic c₁ hw₁ c₂ (fun hc => absurd (Or.inl hc) hord) hpQ hQp
  have hg : 0 < Nat.gcd p Q := Nat.gcd_pos_of_pos_left _ c₁.q_pos
  have hN1 := c₁.two_q_add_w_le
  have hN2 := c₂.two_q_add_w_le
  obtain ⟨hd1, hd2⟩ := mixFold_gcd_dvd_N_sub c₁ c₂
  have hdp : ((Nat.gcd p Q : ℕ) : ℤ) ∣ (p : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)
  have hdw : ((Nat.gcd p Q : ℕ) : ℤ) ∣ (w₂ : ℤ) - w₁ := by
    have := dvd_sub hd1 hd2
    have e : (N : ℤ) - w₁ - ((N : ℤ) - w₂) = (w₂ : ℤ) - w₁ := by ring
    rwa [e] at this
  obtain ⟨-, -, -, -, hBw, hBq⟩ := c₁.caps_d hw₁ rfl
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := c₂.phases hw₂
  have hwq := c₁.w_lt
  have hwq2 := c₂.w_lt
  have hcc : case₂ = .a ∨ case₂ = .b := by
    cases hc : case₂
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (Or.inl hc) hord
    · exact absurd (Or.inr hc) hord
  have e1 : ((Nat.gcd p Q : ℕ) : ℤ) ∣ (N : ℤ) - w₂ := hd2
  rcases hcc with hca | hcb
  · obtain ⟨-, c2, c3, c4⟩ := c₂.caps_a hw₂ hca
    by_cases hlt : s₂ < (w₂ : ℤ)
    · have := mixFold_eq_of_gcd_dvd hg hper (x := s₂) (y := (N : ℤ) - w₂ + s₂) (by omega)
        (by omega) (by omega) (by omega) (by simpa using e1)
      have := c4 hlt
      omega
    · have hs : s₂ = (w₂ : ℤ) := by omega
      have := mixFold_eq_of_gcd_dvd hg hper (x := (w₁ : ℤ)) (y := w₂) (by omega) (by omega)
        (by omega) (by omega) hdw
      rw [hs] at c2
      omega
  · obtain ⟨c1, -, c3, -⟩ := c₂.caps_b hw₂ hcb
    by_cases ht : 1 ≤ t₂
    · have := mixFold_eq_of_gcd_dvd hg hper (x := t₂) (y := (N : ℤ) - w₂ + t₂) (by omega)
        (by omega) (by omega) (by omega) (by simpa using e1)
      have := c1 ht
      omega
    · have ht0 : t₂ = 0 := by omega
      rw [ht0] at c3
      simp only [add_zero] at c3
      have hdp' : ((Nat.gcd p Q : ℕ) : ℤ) ∣ (p : ℤ) - ((N : ℤ) - w₂) := dvd_sub hdp e1
      have := mixFold_eq_of_gcd_dvd hg hper (x := (N : ℤ) - w₂) (y := p) (by omega) (by omega)
        (by omega) (by omega) (by simpa using hdp')
      omega

/-- The facts about the bit words of a connected skew diagram that the drift argument uses: the
bits of `A` lie in `{0, 1}`, and the heights are positive and end at one. -/
structure MixFoldWordsOK (A B : ℤ → ℤ) (N : ℕ) : Prop where
  bitA : ∀ k : ℤ, 1 ≤ k → k ≤ (N : ℤ) - 1 → A k = 0 ∨ A k = 1
  pos : ∀ n : ℕ, n < N → 0 < mixFold_ht A B n
  last : mixFold_ht A B (N - 1) = 1

theorem MixFoldWordsOK.of_isConnectedSkew {X : Diagram} (hX : IsConnectedSkew X) :
    MixFoldWordsOK (wordA X) (wordB X) (span X) := by
  obtain ⟨hN, hbits, hpos, hlast⟩ := isBitData_of_isConnectedSkew hX
  refine ⟨fun k hk1 hk2 => ?_, fun n hn => hpos n hn, hlast⟩
  obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
  have := (hbits k' (by omega) (by omega)).1
  exact this

/-- **`lem:gluing-collision`** (words).  Let `N = M g + w_g` with `0 < w_g < g`, let `B` be
`g`-periodic and `A` be `g`-periodic outside the single residue `R`.  A case-(d) chart of positive
width whose period is a multiple of `g` cannot have both middle phases congruent to `R`. -/
theorem mixFold_collision_words {A B : ℤ → ℤ} {N p w g : ℕ} {s t R : ℤ}
    (c : MixFoldCoding A B N p w .d s t) (hw : 0 < w) (hF : MixFoldWordsOK A B N) (hg : 0 < g)
    (hgp : g ∣ p) (hrem : 0 < N % g) (hB : PeriodExcept (N - 1) g ∅ B)
    (hA : PeriodExcept (N - 1) g {R} A) (hs : s % (g : ℤ) = R) (ht : t % (g : ℤ) = R) : False := by
  have hN2 := c.two_q_add_w_le
  have hwp := c.w_lt
  obtain ⟨r, hr, hNr⟩ := c.span_eq
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := c.phases hw
  have hlt : t < s := hts (Or.inr rfl)
  obtain ⟨-, hAs, hAt, -, -, -⟩ := c.caps_d hw rfl
  have hRg : 0 ≤ R ∧ R < g := by
    rw [← hs]; exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  -- `s ≡ t` forces `s ≥ t + g`
  have hgst : (g : ℤ) ∣ s - t := PeriodWords.dvd_sub_of_emod_eq (by rw [hs, ht])
  obtain ⟨m, hm⟩ := hgst
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have : m ≤ 0 := by omega
    nlinarith
  have hsg : (g : ℤ) ≤ s - t := by nlinarith
  -- the decomposition `N = M g + w_g`
  obtain ⟨M, wg, hNeq, hwg0, hwgg⟩ : ∃ M wg : ℕ, N = M * g + wg ∧ 0 < wg ∧ wg < g :=
    ⟨N / g, N % g, (Nat.div_add_mod' N g).symm, hrem, Nat.mod_lt _ hg⟩
  have hdp : (g : ℤ) ∣ (p : ℤ) := Int.natCast_dvd_natCast.2 hgp
  have hdw : (g : ℤ) ∣ (N : ℤ) - w := by
    have : (N : ℤ) - w = r * p := by rw [hNr]; push_cast; ring
    rw [this]; exact dvd_mul_of_dvd_right hdp _
  subst hNeq
  have hbit : ∀ k : ℤ, 1 ≤ k → k ≤ ((M * g + wg : ℕ) : ℤ) - 1 → A k = 0 ∨ A k = 1 := hF.bitA
  have hcore := mixFold_collision_core (g := g) (M := M) (wg := wg) (R := R) hg hwg0 hRg hbit
    hF.pos hF.last hB hA
  rcases hcore with h0 | h1
  · -- nonnegative drift: `A_s = 0`
    have := h0 s (by omega) (by push_cast at *; omega) hs
    omega
  · -- negative drift: `A_{N - w + t} = 1`
    have hy : ((M * g + wg : ℕ) : ℤ) - w + t ≤ ((M * g : ℕ) : ℤ) := by push_cast at *; omega
    have := h1 (((M * g + wg : ℕ) : ℤ) - w + t) (by push_cast at *; omega) hy (by
      rw [← ht]
      have : (g : ℤ) ∣ (((M * g + wg : ℕ) : ℤ) - w + t) - t := by
        have e : (((M * g + wg : ℕ) : ℤ) - w + t) - t = ((M * g + wg : ℕ) : ℤ) - w := by ring
        rw [e]; exact hdw
      exact (PeriodWords.emod_eq_of_dvd_sub this))
    omega

/-- With full period `g` on `A` and `B`, every block of `g` positions raises the height by the same
amount `H_g - 1`. -/
theorem mixFold_inc_const {A B : ℤ → ℤ} {L g : ℕ} (hA : PeriodExcept L g ∅ A)
    (hB : PeriodExcept L g ∅ B) :
    ∀ n : ℕ, n + g ≤ L → mixFold_inc A B g n = mixFold_ht A B g - 1 := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [mixFold_inc, mixFold_ht_zero]
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := mixFold_inc_succ A B g n
    have ha := hA ((n : ℤ) + 1) (by rw [Finset.mem_Icc]; omega) (by simp)
    have hb := hB ((n : ℤ) + 1) (by rw [Finset.mem_Icc]; omega) (by simp)
    have e : ((n + g : ℕ) : ℤ) + 1 = (n : ℤ) + 1 + g := by push_cast; ring
    rw [e] at h2
    linarith

theorem mixFold_ht_mul {A B : ℤ → ℤ} {L g : ℕ} (hA : PeriodExcept L g ∅ A)
    (hB : PeriodExcept L g ∅ B) : ∀ k : ℕ, k * g ≤ L →
    mixFold_ht A B (k * g) = 1 + k * (mixFold_ht A B g - 1) := by
  intro k
  induction k with
  | zero => intro _; simp [mixFold_ht_zero]
  | succ k ih =>
    intro hk
    have h1 := ih (by nlinarith)
    have h2 := mixFold_inc_const hA hB (k * g) (by nlinarith)
    unfold mixFold_inc at h2
    have e : (k + 1) * g = k * g + g := by ring
    rw [e]
    push_cast
    linarith

/-- **`lem:gluing-incompatible`, opposite mixed, words.**  A case-(d) chart of period `p` and a
case-(c) chart of larger period `Q`, both of positive width, neither period dividing the other,
cannot code one parent. -/
theorem mixFold_opposite_words {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {s₁ t₁ s₂ t₂ : ℤ}
    (c₁ : MixFoldCoding A B N p w₁ .d s₁ t₁) (hw₁ : 0 < w₁)
    (c₂ : MixFoldCoding A B N Q w₂ .c s₂ t₂) (hw₂ : 0 < w₂) (hF : MixFoldWordsOK A B N)
    (hlt : p < Q) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) : False := by
  have hper := mixFold_B_periodic c₁ hw₁ c₂ (fun _ => hlt) hpQ hQp
  have hg : 0 < Nat.gcd p Q := Nat.gcd_pos_of_pos_left _ c₁.q_pos
  by_cases hrem : N % Nat.gcd p Q = 0
  · exact mixFold_remainder_zero_words c₁ hw₁ c₂ (fun _ => hlt) hpQ hQp hrem
  have hrem' : 0 < N % Nat.gcd p Q := Nat.pos_of_ne_zero hrem
  set g := Nat.gcd p Q with hgdef
  have hN1 := c₁.two_q_add_w_le
  have hN2 := c₂.two_q_add_w_le
  have hwp := c₁.w_lt
  have hwQ := c₂.w_lt
  have hp := c₁.q_pos
  obtain ⟨hs1, hs2, ht1, ht2, hts⟩ := c₁.phases hw₁
  have hgp : g ∣ p := Nat.gcd_dvd_left p Q
  have hfp : PeriodExcept (N - 1) p {t₁, s₁} A := by
    have := c₁.perA
    simpa [codingHolesA, hw₁.ne', holesA] using this
  have hfQ : PeriodExcept (N - 1) Q ∅ A := by
    have := c₂.perA
    simpa [codingHolesA, hw₂.ne', holesA] using this
  -- the word `A` is `g`-periodic outside the class of the phases of the smaller chart
  have hAclass : ∀ x : ℤ, x ∈ Finset.Icc (1 : ℤ) ((N - 1 : ℕ) - g : ℤ) →
      (({t₁, s₁} : Finset ℤ).filter (fun a => a % (g : ℤ) = x % (g : ℤ))).card ≤ 1 →
      A x = A (x + g) := by
    intro x hx hcard
    rw [Finset.mem_Icc] at hx
    have hL : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
    exact mixFold_class_one_hole (L := N - 1) (S := {t₁, s₁}) hp hlt hpQ (by omega) hfQ hfp
      (x := x) (y := x + g) (by rw [Finset.mem_Icc]; omega) (by rw [Finset.mem_Icc]; omega)
      (by rw [add_sub_cancel_left]) hcard
  by_cases hcol : t₁ % (g : ℤ) = s₁ % (g : ℤ)
  · -- collision of the phases of the smaller chart
    refine mixFold_collision_words c₁ hw₁ hF hg hgp hrem' hper
      (R := t₁ % (g : ℤ)) ?_ hcol.symm rfl
    intro x hx hxR
    have hxR' : x % (g : ℤ) ≠ t₁ % (g : ℤ) := by simpa using hxR
    apply hAclass x (by rw [Finset.mem_Icc] at hx ⊢; omega)
    have : ({t₁, s₁} : Finset ℤ).filter (fun a => a % (g : ℤ) = x % (g : ℤ)) = ∅ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        iff_false, not_and]
      rintro (rfl | rfl)
      · intro h; exact hxR' h.symm
      · intro h; exact hxR' (by rw [hcol]; exact h.symm)
    rw [this]; simp
  · -- `A` is `g`-periodic
    have hAper : PeriodExcept (N - 1) g ∅ A := by
      intro x hx _
      apply hAclass x hx
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ha hb
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      rcases ha1 with rfl | rfl <;> rcases hb1 with rfl | rfl
      · rfl
      · exact absurd (ha2.trans hb2.symm) hcol
      · exact absurd (hb2.trans ha2.symm) hcol
      · rfl
    obtain ⟨hdN1, hdN2⟩ := mixFold_gcd_dvd_N_sub c₁ c₂
    have hdp : (g : ℤ) ∣ (p : ℤ) := Int.natCast_dvd_natCast.2 hgp
    obtain ⟨-, -, -, -, -, hAw⟩ : True ∧ True ∧ True ∧ True ∧ True ∧
        A ((N : ℤ) - w₂) = 1 := by
      obtain ⟨-, -, -, -, h5, -⟩ := c₂.caps_c hw₂ rfl
      exact ⟨trivial, trivial, trivial, trivial, trivial, h5⟩
    obtain ⟨-, -, -, -, -, hBq⟩ := c₁.caps_d hw₁ rfl
    have hgp1 : (g : ℤ) ≤ p := by exact_mod_cast Nat.le_of_dvd hp hgp
    have hAg : A (g : ℤ) = 1 := by
      have := mixFold_eq_of_gcd_dvd hg hAper (x := (g : ℤ)) (y := (N : ℤ) - w₂) (by omega)
        (by omega) (by omega) (by omega) (by simpa using hdN2)
      omega
    have hAp : A (p : ℤ) = 1 := by
      have := mixFold_eq_of_gcd_dvd hg hAper (x := (g : ℤ)) (y := p) (by omega) (by omega)
        (by omega) (by omega) (by simpa using hdp)
      omega
    -- the height at `p` computed in two ways
    obtain ⟨a, ha⟩ := hgp
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · rw [h0] at ha; omega
      · exact h0
    have hmul := mixFold_ht_mul hAper hper a (by
      have : a * g = p := by rw [ha]; ring
      omega)
    have hag : a * g = p := by rw [ha]; ring
    rw [hag] at hmul
    have hsingle := c₁.single_d hw₁ rfl
    have hstep := mixFold_ht_succ A B (p - 1)
    have e1 : p - 1 + 1 = p := by omega
    have e2 : ((p - 1 : ℕ) : ℤ) + 1 = p := by omega
    rw [e1, e2] at hstep
    rw [hsingle, hAp, hBq] at hstep
    have hx : (a : ℤ) * (mixFold_ht A B g - 1) = 1 := by linarith
    have hapos : (0 : ℤ) < a := by exact_mod_cast ha1
    have hxpos : 0 < mixFold_ht A B g - 1 := by
      by_contra hcon
      nlinarith
    have ha1' : a = 1 := by
      have : (a : ℤ) ≤ 1 := by nlinarith
      omega
    apply hpQ
    have hpg : p = g := by rw [ha, ha1']; ring
    rw [hpg]
    exact Nat.gcd_dvd_right p Q

end SkewGluing
