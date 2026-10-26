import SkewGluing.OrdinaryFold.Mark
import SkewGluing.OrdinaryDrift.Words

/-!
# The inner of the fold, from the generic words

Formalizes `shields-2026-skew-gluing.tex`, «Two ordinary roots»
(`prop:gluing-ordinary-fold`),
the construction of the inner `G` as the diagram whose boundary words are the generic `g`-periodic
words of `lem:gluing-periods` (ii) with the exceptional bits of `eq:gluing-caps` imposed at the
slot residues `τ` (northwest word) and `σ` (southeast word).

* `innerA`, `innerB`: the words of `G`; the diagram they define is
  `fromBits (g + w_g) innerA innerB`;
* `window_sum_innerA`, `window_sum_innerB`: the sums of `g` consecutive bits, which give the
  congruence of the two copies (`eq:gluing-ordinary-slot` and the identity `Δ = 0`);
* `slotGeom_of_generic`: the diagonal data `SlotGeom` of `SkewGluing.OrdinaryFold.Mark`.

Sorry-free.
-/

namespace SkewGluing
namespace OrdinaryFold

/-- A periodic function summed over `g` consecutive positions. -/
theorem sum_window_periodic (f : ℕ → ℤ) (g : ℕ) (r : ℕ) :
    ∑ i ∈ Finset.range g, f ((r + i) % g) = ∑ j ∈ Finset.range g, f j := by
  induction r with
  | zero =>
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp [Nat.mod_eq_of_lt hi]
  | succ r ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ (fun i => f ((r + i) % g)) g
    have h2 := Finset.sum_range_succ' (fun i => f ((r + i) % g)) g
    have e : ∀ i, f ((r + 1 + i) % g) = f ((r + (i + 1)) % g) := by
      intro i; congr 1; ring_nf
    simp only [e]
    have h3 : f ((r + g) % g) = f ((r + 0) % g) := by simp
    linarith

/-- A single marked position inside a window of `g` consecutive positions. -/
theorem sum_window_ite (c r g : ℕ) (x : ℤ) :
    ∑ i ∈ Finset.range g, (if r + 1 + i = c then x else 0) =
      if r + 1 ≤ c ∧ c < r + 1 + g then x else 0 := by
  by_cases h : r + 1 ≤ c ∧ c < r + 1 + g
  · simp only [h, and_self, ite_true]
    rw [Finset.sum_eq_single (c - (r + 1))]
    · simp only [show r + 1 + (c - (r + 1)) = c by omega, ite_true]
    · intro i _ hi
      simp only [show ¬ (r + 1 + i = c) by omega, ite_false]
    · intro hn
      exact absurd (Finset.mem_range.mpr (by omega)) hn
  · simp only [h, ite_false]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [show ¬ (r + 1 + i = c) by omega, ite_false]

/-- The northwest word of the inner: generic, with the bit `1` at `τ` and `0` at `g + τ`. -/
def innerA (A0 : ℕ → ℤ) (g τ : ℕ) (k : ℕ) : ℤ :=
  if 1 ≤ τ ∧ k = τ then 1 else if k = g + τ then 0 else A0 (k % g)

/-- The southeast word of the inner: generic, with the bit `0` at `σ` and `1` at `g + σ`. -/
def innerB (B0 : ℕ → ℤ) (g wg σ : ℕ) (k : ℕ) : ℤ :=
  if k = σ then 0 else if σ < wg ∧ k = g + σ then 1 else B0 (k % g)

theorem innerA_eq (A0 : ℕ → ℤ) {g τ : ℕ} (hτ : τ < g) (k : ℕ) :
    innerA A0 g τ k = A0 (k % g) + (if 1 ≤ τ ∧ k = τ then 1 - A0 τ else 0) +
      (if k = g + τ then -A0 τ else 0) := by
  by_cases h1 : 1 ≤ τ ∧ k = τ
  · obtain ⟨h1a, rfl⟩ := h1
    have hg0 : g ≠ 0 := by omega
    simp [innerA, h1a, hg0, Nat.mod_eq_of_lt hτ]
  · by_cases h2 : k = g + τ
    · have e : (g + τ) % g = τ := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hτ]
      have h3 : ¬ (1 ≤ τ ∧ g + τ = τ) := by omega
      have hg0 : g ≠ 0 := by omega
      subst h2
      simp [innerA, e, hg0]
    · simp [innerA, h1, h2]

theorem innerB_eq (B0 : ℕ → ℤ) {g wg σ : ℕ} (hσ : σ < g) (k : ℕ) :
    innerB B0 g wg σ k = B0 (k % g) + (if k = σ then -B0 σ else 0) +
      (if σ < wg ∧ k = g + σ then 1 - B0 σ else 0) := by
  by_cases h1 : k = σ
  · subst h1
    have hg0 : g ≠ 0 := by omega
    simp [innerB, hg0, Nat.mod_eq_of_lt hσ]
  · by_cases h2 : σ < wg ∧ k = g + σ
    · have e : (g + σ) % g = σ := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hσ]
      obtain ⟨h2a, rfl⟩ := h2
      have hg0 : g ≠ 0 := by omega
      simp [innerB, hg0, h2a, e]
    · simp [innerB, h1, h2]

/-- **The window sum of the northwest bits.**  `g` consecutive bits of the inner starting after
the position `r < wg` add up to `ΣA⁰ - A⁰_τ + [r < τ]`. -/
theorem window_sum_innerA (A0 : ℕ → ℤ) {g wg τ : ℕ} (hτ : τ < wg) (hwg : wg < g) {r : ℕ}
    (hr : r < wg) :
    ∑ i ∈ Finset.range g, innerA A0 g τ (r + 1 + i) =
      ∑ j ∈ Finset.range g, A0 j - A0 τ + (if r < τ then 1 else 0) := by
  have hτg : τ < g := by omega
  simp only [innerA_eq A0 hτg, Finset.sum_add_distrib]
  have h1 := sum_window_periodic A0 g (r + 1)
  have h2 := sum_window_ite τ r g (1 - A0 τ)
  have h3 := sum_window_ite (g + τ) r g (-A0 τ)
  have e : ∀ i, (1 ≤ τ ∧ r + 1 + i = τ) ↔ r + 1 + i = τ := by
    intro i; omega
  simp only [e]
  rw [h1, h2, h3]
  split_ifs <;> omega

/-- **The window sum of the southeast bits.**  `g` consecutive bits of the inner starting after
the position `r < wg` add up to `ΣB⁰ - B⁰_σ + [σ ≤ r]`. -/
theorem window_sum_innerB (B0 : ℕ → ℤ) {g wg σ : ℕ} (hσ : σ ≤ wg) (hσ1 : 1 ≤ σ) (hwg : wg < g)
    {r : ℕ} (hr : r < wg) :
    ∑ i ∈ Finset.range g, innerB B0 g wg σ (r + 1 + i) =
      ∑ j ∈ Finset.range g, B0 j - B0 σ + (if σ ≤ r then 1 else 0) := by
  have hσg : σ < g := by omega
  simp only [innerB_eq B0 hσg, Finset.sum_add_distrib]
  have h1 := sum_window_periodic B0 g (r + 1)
  have h2 := sum_window_ite σ r g (-B0 σ)
  have h3 := sum_window_ite (g + σ) r g (1 - B0 σ)
  by_cases hσw : σ < wg
  · simp only [hσw, true_and]
    rw [h1, h2, h3]
    split_ifs <;> omega
  · have e : ∀ i, ¬ (σ < wg ∧ r + 1 + i = g + σ) := fun i h => hσw h.1
    simp only [e, ite_false, Finset.sum_const_zero, add_zero]
    rw [h1, h2]
    split_ifs <;> omega


/-- The first row `ℓ_k` of a diagram reconstructed from bit words, indexed by `ℤ`. -/
def loZ (A : ℕ → ℤ) (k : ℤ) : ℤ := bitsLo A k.toNat

theorem loZ_natCast (A : ℕ → ℤ) (n : ℕ) : loZ A (n : ℤ) = bitsLo A n := by
  simp [loZ]

theorem diagSet_fromBits {N : ℕ} {A B : ℕ → ℤ} (_h : IsBitData N A B) :
    DiagSet (fromBits N A B) 0 ((N : ℤ) - 1) (loZ A) (loZ B) := by
  intro i k
  rw [mem_fromBits']
  constructor
  · rintro ⟨k', hk', hjk, h1, h2⟩
    have : k = k' := by omega
    subst this
    refine ⟨by omega, by omega, ?_, ?_⟩ <;> simpa [loZ] using ‹_›
  · rintro ⟨h0, h1, h2, h3⟩
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨n, by omega, rfl, ?_, ?_⟩
    · simpa [loZ] using h2
    · simpa [loZ] using h3

theorem diagShape_fromBits {N : ℕ} {A B : ℕ → ℤ} (h : IsBitData N A B) :
    DiagShape 0 ((N : ℤ) - 1) (loZ A) (loZ B) := by
  have hN := h.1
  have hbits := h.2.1
  have hlast := h.2.2.2
  refine ⟨by omega, fun k h0 h1 => ?_, fun k h0 h1 => ?_, fun k h0 h1 => ?_, ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    simpa [loZ] using bitsLo_le_of_isBitData h (k := n) (by omega)
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ k - 1)
    have hk : k = (n : ℤ) + 1 := by omega
    subst hk
    simp only [loZ, show ((n : ℤ) + 1 - 1) = n by ring, Int.toNat_natCast]
    have e : ((n : ℤ) + 1).toNat = n + 1 := by omega
    rw [e, bitsLo_succ]
    have := (hbits (n + 1) (by omega) (by omega)).1
    omega
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ k - 1)
    have hk : k = (n : ℤ) + 1 := by omega
    subst hk
    simp only [loZ, show ((n : ℤ) + 1 - 1) = n by ring, Int.toNat_natCast]
    have e : ((n : ℤ) + 1).toNat = n + 1 := by omega
    rw [e, bitsLo_succ]
    have := (hbits (n + 1) (by omega) (by omega)).2
    omega
  · simp [loZ, bitsLo]
  · have e : ((N : ℤ) - 1).toNat = N - 1 := by omega
    simp only [loZ, e]
    have := bitsLo_add_heightWord A B (N - 1)
    omega


theorem bitsLo_add_window (A : ℕ → ℤ) (n m : ℕ) :
    bitsLo A (m + n) = bitsLo A n - ∑ i ∈ Finset.range m, A (n + 1 + i) := by
  unfold bitsLo
  rw [add_comm m n, Finset.sum_range_add]
  have : ∑ x ∈ Finset.range m, A (n + x + 1) = ∑ i ∈ Finset.range m, A (n + 1 + i) := by
    apply Finset.sum_congr rfl; intro i _; congr 1; ring
  rw [this]; ring

theorem loZ_cast_add (A : ℕ → ℤ) (g n : ℕ) : loZ A ((g : ℤ) + n) = bitsLo A (g + n) := by
  rw [← Nat.cast_add, loZ_natCast]

theorem heightWord_eq_one_iff {A B : ℕ → ℤ} {k : ℕ} (h : heightWord A B k = 1) :
    bitsLo A k = bitsLo B k := by
  have := bitsLo_add_heightWord A B k
  omega

/-- The diagonal data of the inner of the fold.  The inner has the words `innerA`, `innerB`, built
from the generic bits `A⁰`, `B⁰` and the slots `τ`, `σ`.  Its heights are positive (`IsBitData`),
its diagonals `w_g` and `g - 1` are singletons, and the retained lower copy has positive
heights; `A⁰_{w_g} = 0` and `B⁰_0 = 0` are the private-endpoint bits of the two horizontal
attachments. -/
theorem slotGeom_of_generic {A0 B0 : ℕ → ℤ} {g wg τ σ : ℕ} (hwg1 : 1 ≤ wg) (hwg : wg < g)
    (hτ : τ < wg) (hσ1 : 1 ≤ σ) (hσ : σ ≤ wg)
    (hΔ : ∑ j ∈ Finset.range g, A0 j = ∑ j ∈ Finset.range g, B0 j) (hρ : A0 τ = B0 σ)
    (hbd : IsBitData (g + wg) (innerA A0 g τ) (innerB B0 g wg σ))
    (hsw : heightWord (innerA A0 g τ) (innerB B0 g wg σ) wg = 1)
    (hsq : heightWord (innerA A0 g τ) (innerB B0 g wg σ) (g - 1) = 1)
    (hpos : ∀ r, r < wg →
      1 + (if σ ≤ r then 1 else 0) ≤ heightWord (innerA A0 g τ) (innerB B0 g wg σ) r)
    (hAlow : A0 wg = 0) (hBup : B0 0 = 0) :
    SlotGeom (g : ℤ) (wg : ℤ) (τ : ℤ) (σ : ℤ) (A0 τ - ∑ j ∈ Finset.range g, A0 j)
      (loZ (innerA A0 g τ)) (loZ (innerB B0 g wg σ)) := by
  set AG := innerA A0 g τ with hAG
  set BG := innerB B0 g wg σ with hBG
  have hτg : τ < g := by omega
  have hσg : σ < g := by omega
  have hbits := hbd.2.1
  have hsh := diagShape_fromBits hbd
  have e1 : ((g + wg : ℕ) : ℤ) - 1 = (g : ℤ) + wg - 1 := by push_cast; ring
  rw [e1] at hsh
  have hne : ∀ n : ℕ, n < g + wg → bitsLo AG n ≤ bitsLo BG n :=
    fun n hn => bitsLo_le_of_isBitData hbd hn
  have wa := fun r (hr : r < wg) => window_sum_innerA A0 hτ hwg hr
  have wb := fun r (hr : r < wg) => window_sum_innerB B0 hσ hσ1 hwg hr
  have ea : ∀ r, r < wg → bitsLo AG (g + r) = bitsLo AG r -
      (∑ j ∈ Finset.range g, A0 j - A0 τ + (if r < τ then 1 else 0)) := by
    intro r hr
    rw [bitsLo_add_window AG r g, wa r hr]
  have eb : ∀ r, r < wg → bitsLo BG (g + r) = bitsLo BG r -
      (∑ j ∈ Finset.range g, B0 j - B0 σ + (if σ ≤ r then 1 else 0)) := by
    intro r hr
    rw [bitsLo_add_window BG r g, wb r hr]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, hsh, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro r h0 hr
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have hr' : n < τ := by omega
    rw [loZ_cast_add, loZ_natCast, ea n (by omega)]
    simp only [hr', ite_true]
    ring
  · intro r hr h2
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ r)
    have hr' : ¬ n < τ := by omega
    rw [loZ_cast_add, loZ_natCast, ea n (by omega)]
    simp only [hr', ite_false]
    ring
  · intro r h0 hr
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have hr' : ¬ σ ≤ n := by omega
    rw [loZ_cast_add, loZ_natCast, eb n (by omega)]
    simp only [hr', ite_false]
    have := hρ
    have := hΔ
    omega
  · intro r hr h2
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ r)
    have hr' : σ ≤ n := by omega
    rw [loZ_cast_add, loZ_natCast, eb n (by omega)]
    simp only [hr', ite_true]
    have := hρ
    have := hΔ
    omega
  · simpa [loZ] using heightWord_eq_one_iff hsw
  · have e : ((g : ℤ) - 1).toNat = g - 1 := by omega
    simp only [loZ, e]
    exact heightWord_eq_one_iff hsq
  · intro r h0 hr
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have := hpos n (by omega)
    have h3 := bitsLo_add_heightWord AG BG n
    simp only [loZ_natCast]
    split_ifs at this ⊢ <;> omega
  · intro h
    have e : σ = (σ - 1) + 1 := by omega
    have h0 : BG σ = 0 := by simp [hBG, innerB]
    have h1 := bitsLo_succ BG (σ - 1)
    rw [← e] at h1
    have e2 : ((σ : ℤ) - 1).toNat = σ - 1 := by omega
    simp only [loZ, e2, Int.toNat_natCast]
    omega
  · -- lower attachment
    have e2 : ((σ : ℤ) - 1).toNat = σ - 1 := by omega
    simp only [loZ, e2, Int.toNat_natCast]
    have h1 := hne (σ - 1) (by omega)
    by_cases hlt : σ < wg
    · have h0 : BG σ = 0 := by simp [hBG, innerB]
      have h2 := bitsLo_succ BG (σ - 1)
      have e3 : σ - 1 + 1 = σ := by omega
      rw [e3] at h2
      omega
    · have hσw : σ = wg := by omega
      subst hσw
      have hs := heightWord_eq_one_iff hsw
      have h0 : AG σ = 0 := by
        simp only [hAG, innerA]
        have : ¬ (1 ≤ τ ∧ σ = τ) := by omega
        have h4 : σ ≠ g + τ := by omega
        simp [this, h4, Nat.mod_eq_of_lt hwg, hAlow]
      have h2 := bitsLo_succ AG (σ - 1)
      have e3 : σ - 1 + 1 = σ := by omega
      rw [e3] at h2
      omega
  · -- upper attachment
    by_cases hτ0 : τ = 0
    · subst hτ0
      have e2 : ((g : ℤ) + (0 : ℕ) - 1).toNat = g - 1 := by push_cast; omega
      have e3 : ((g : ℤ) + (0 : ℕ)).toNat = g := by push_cast; omega
      simp only [loZ, e2, e3]
      have hs := heightWord_eq_one_iff hsq
      have h0 : BG g = 0 := by
        simp only [hBG, innerB]
        have h4 : g ≠ σ := by omega
        have h5 : ¬ (σ < wg ∧ g = g + σ) := by omega
        have h6 : σ ≠ 0 := by omega
        simp [h4, h6, hBup]
      have h2 := bitsLo_succ BG (g - 1)
      have e4 : g - 1 + 1 = g := by omega
      rw [e4] at h2
      omega
    · have e2 : ((g : ℤ) + τ - 1).toNat = g + τ - 1 := by omega
      have e3 : ((g : ℤ) + τ).toNat = g + τ := by omega
      simp only [loZ, e2, e3]
      have h0 : AG (g + τ) = 0 := by
        simp only [hAG, innerA]
        have : ¬ (1 ≤ τ ∧ g + τ = τ) := by omega
        have hg0 : g ≠ 0 := by omega
        simp [hg0]
      have h2 := bitsLo_succ AG (g + τ - 1)
      have e4 : g + τ - 1 + 1 = g + τ := by omega
      rw [e4] at h2
      have h1 := hne (g + τ) (by omega)
      omega

end OrdinaryFold
end SkewGluing
