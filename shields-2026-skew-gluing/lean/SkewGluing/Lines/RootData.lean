import SkewGluing.Lines.Words

/-!
# Coprime periods of two roots: the word-level argument

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-lines`), first assertion, as a statement about boundary words only.

`RootData A B N q rowE colE mix` collects what the coding lemma (`lem:gluing-coding`) and the local
geometry (`lem:gluing-local`) say about a proper root of period `q` of a parent of span `N` whose
boundary words are `A`, `B`:

* ordinary roots (`OrdRoot`): both words have period `q` except at one residue, with the initial
  exceptional bits of `eq:gluing-caps`, and the private singleton at `q - 1` makes the sums of the
  two words agree over `[1, q - 1]`; `rowE` (`colE`) is the statement that the inner diagram is a
  row (a column), which the geometry derives when both words are `0` (`1`) on `[1, q - 1]`;
* mixed roots (`MixedRoot`): one word has the full period `q`, takes the values `1` and `0` at two
  positions (the private-endpoint bits of `eq:gluing-holes`, `eq:gluing-interface`), and the other
  has at most two exceptional residues.

`coprime_pair` is the proof of `lem:gluing-lines` (1) from these data.

Sorry-free.
-/

namespace SkewGluing

namespace Lines

open PeriodWords

/-- The data of an ordinary root of period `q` and width `w` on the words `A`, `B` of a parent of
span `N`.  `rowE` and `colE` say that the inner is a row, respectively a column. -/
def OrdRoot (A B : ℤ → ℤ) (N q w : ℕ) (rowE colE : Prop) : Prop :=
  ∃ hA hB : ℤ, 0 ≤ hA ∧ hA ≤ w ∧ 0 ≤ hB ∧ hB ≤ w ∧
    PeriodExcept (N - 1) q {hA} A ∧ PeriodExcept (N - 1) q {hB} B ∧
    (1 ≤ hA → A hA = 1) ∧ (1 ≤ hB → B hB = 0) ∧
    ∑ x ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), A x = ∑ x ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), B x ∧
    ((∀ x ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), A x = 0 ∧ B x = 0) → rowE) ∧
    ((∀ x ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), A x = 1 ∧ B x = 1) → colE)

/-- The data of a mixed root of period `q` and width `w ≥ 1`: the word `f` has the full period `q`
and takes the values `1`, `0` at the positions `x₁`, `x₂`; the word `g` has period `q` except at at
most two residues in `[0, w]`. -/
def MixedRoot (f g : ℤ → ℤ) (N q w : ℕ) (x₁ x₂ : ℤ) : Prop :=
  1 ≤ w ∧ (∃ T : Finset ℤ, T.card ≤ 2 ∧ (∀ t ∈ T, 0 ≤ t ∧ t ≤ w) ∧ PeriodExcept (N - 1) q T g) ∧
    PeriodExcept (N - 1) q ∅ f ∧ x₁ ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1) ∧
    x₂ ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1) ∧ f x₁ = 1 ∧ f x₂ = 0

/-- The data of a proper root of period `q` of a parent of span `N` with boundary words `A`, `B`:
`N = r q + w` with `r ≥ 2`, `w < q`, and either an ordinary root (`¬ mix`) or a mixed root
(`mix`) of case (d) (full period on `B`, private bits `B_w = 1`, `B_q = 0`) or of case (c) (full
period on `A`, private bits `A_{N-w} = 1`, `A_{N-q} = 0`). -/
def RootData (A B : ℤ → ℤ) (N q : ℕ) (rowE colE mix : Prop) : Prop :=
  2 ≤ q ∧ ∃ w r : ℕ, w < q ∧ 2 ≤ r ∧ N = r * q + w ∧
    ((¬ mix ∧ OrdRoot A B N q w rowE colE) ∨
      (mix ∧ (MixedRoot B A N q w (w : ℤ) (q : ℤ) ∨
        MixedRoot A B N q w ((N : ℤ) - w) ((N : ℤ) - q))))

theorem emod_eq_self_of_mem {x : ℤ} {q : ℕ} (h1 : 1 ≤ x) (h2 : x ≤ (q : ℤ) - 1) :
    x % (q : ℤ) = x := Int.emod_eq_of_lt (by omega) (by omega)

/-- A mixed root against any other root of a coprime period: the full-period word of the mixed
root is constant, contradicting its two private bits.  The mixed root is the first. -/
theorem MixedRoot.false_of_period {f g : ℤ → ℤ} {N p Q w w' r' : ℕ} {x₁ x₂ : ℤ}
    (hm : MixedRoot f g N p w x₁ x₂) (hr : ∃ r, 2 ≤ r ∧ N = r * p + w) (hp : 2 ≤ p) (hQ : 2 ≤ Q)
    (hr' : 2 ≤ r') (hNQ : N = r' * Q + w') (hcop : Nat.Coprime p Q)
    {h : ℤ} (hfQ : PeriodExcept (N - 1) Q {h} f) : False := by
  obtain ⟨hw, -, hfp, hx₁, hx₂, h1, h0⟩ := hm
  obtain ⟨r, hr2, hNp⟩ := hr
  have hL : (N - 1) + 1 = N := by
    have := Nat.mul_le_mul_right p hr2
    omega
  have hcast : (((N - 1 : ℕ)) : ℤ) = (N : ℤ) - 1 := by omega
  have := const_of_full_one_hole hp hQ hr2 hr' hw hNp hNQ hcop hL hfp hfQ
    (x := x₁) (y := x₂) (by rwa [hcast]) (by rwa [hcast])
  omega

/-- Two mixed roots of opposite kinds (the full-period word of each is the holed word of the other)
with `p < Q` coprime: the full-period word of the smaller root is constant. -/
theorem MixedRoot.false_opposite {f g : ℤ → ℤ} {N p Q w₁ w₂ r₂ : ℕ} {x₁ x₂ y₁ y₂ : ℤ}
    (hm₁ : MixedRoot f g N p w₁ x₁ x₂) (hm₂ : MixedRoot g f N Q w₂ y₁ y₂) (hpQ : p < Q)
    (hp : 2 ≤ p) (hw₂ : w₂ < Q) (hr₂ : 2 ≤ r₂) (hN₂ : N = r₂ * Q + w₂)
    (hcop : Nat.Coprime p Q) : False := by
  obtain ⟨-, -, hfp, hx₁, hx₂, h1, h0⟩ := hm₁
  obtain ⟨-, ⟨T, hTc, hT, hfQ⟩, -⟩ := hm₂
  have hL : (N - 1) + 1 = N := by
    have := Nat.mul_le_mul_right Q hr₂
    omega
  have hcast : (((N - 1 : ℕ)) : ℤ) = (N : ℤ) - 1 := by omega
  have := const_of_full_two_holes hp hpQ hw₂ hr₂ hN₂ hcop hL hT hTc hfp hfQ
    (x := x₁) (y := x₂) (by rwa [hcast]) (by rwa [hcast])
  omega

/-- A mixed root against an ordinary root of a coprime period. -/
theorem false_mixed_ord {A B : ℤ → ℤ} {N p Q w₁ w₂ r₁ r₂ : ℕ} {rowE colE : Prop}
    {x₁ x₂ y₁ y₂ : ℤ} (hm : MixedRoot B A N p w₁ x₁ x₂ ∨ MixedRoot A B N p w₁ y₁ y₂)
    (ho : OrdRoot A B N Q w₂ rowE colE) (hp : 2 ≤ p) (hQ : 2 ≤ Q) (hr₁ : 2 ≤ r₁)
    (hN₁ : N = r₁ * p + w₁) (hr₂ : 2 ≤ r₂) (hN₂ : N = r₂ * Q + w₂) (hcop : Nat.Coprime p Q) :
    False := by
  obtain ⟨hA, hB, -, -, -, -, perA, perB, -⟩ := ho
  rcases hm with hm | hm
  · exact hm.false_of_period ⟨r₁, hr₁, hN₁⟩ hp hQ hr₂ hN₂ hcop perB
  · exact hm.false_of_period ⟨r₁, hr₁, hN₁⟩ hp hQ hr₂ hN₂ hcop perA

/-- Two mixed roots of coprime periods. -/
theorem false_mixed_mixed {A B : ℤ → ℤ} {N p Q w₁ w₂ r₁ r₂ : ℕ} {x₁ x₂ y₁ y₂ z₁ z₂ u₁ u₂ : ℤ}
    (hm₁ : MixedRoot B A N p w₁ x₁ x₂ ∨ MixedRoot A B N p w₁ y₁ y₂)
    (hm₂ : MixedRoot B A N Q w₂ z₁ z₂ ∨ MixedRoot A B N Q w₂ u₁ u₂) (hp : 2 ≤ p) (hQ : 2 ≤ Q)
    (hr₁ : 2 ≤ r₁) (hN₁ : N = r₁ * p + w₁) (hw₁ : w₁ < p) (hr₂ : 2 ≤ r₂)
    (hN₂ : N = r₂ * Q + w₂) (hw₂ : w₂ < Q) (hcop : Nat.Coprime p Q) : False := by
  have hne : p ≠ Q := fun h => by
    subst h
    have := Nat.Coprime.eq_one_of_dvd hcop (dvd_refl p)
    omega
  have hmono : ∀ {f : ℤ → ℤ}, PeriodExcept (N - 1) Q ∅ f → PeriodExcept (N - 1) Q {0} f :=
    fun h => periodExcept_mono (by simp) h
  rcases hm₁ with hm₁ | hm₁ <;> rcases hm₂ with hm₂ | hm₂
  · exact hm₁.false_of_period ⟨r₁, hr₁, hN₁⟩ hp hQ hr₂ hN₂ hcop (hmono hm₂.2.2.1)
  · rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hm₁.false_opposite hm₂ h hp hw₂ hr₂ hN₂ hcop
    · exact hm₂.false_opposite hm₁ h hQ hw₁ hr₁ hN₁ hcop.symm
  · rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hm₁.false_opposite hm₂ h hp hw₂ hr₂ hN₂ hcop
    · exact hm₂.false_opposite hm₁ h hQ hw₁ hr₁ hN₁ hcop.symm
  · exact hm₁.false_of_period ⟨r₁, hr₁, hN₁⟩ hp hQ hr₂ hN₂ hcop (hmono hm₂.2.2.1)

theorem periodExcept_congr {f g : ℤ → ℤ} {L p : ℕ} {S : Finset ℤ}
    (h : ∀ x ∈ Finset.Icc (1 : ℤ) L, f x = g x) (hf : PeriodExcept L p S f) :
    PeriodExcept L p S g := by
  intro x hx hS
  have hx' := Finset.mem_Icc.mp hx
  rw [← h x (by rw [Finset.mem_Icc]; omega), ← h (x + p) (by rw [Finset.mem_Icc]; omega)]
  exact hf x hx hS

/-- Root data only depends on the words on the positions `1, …, N - 1`. -/
theorem RootData.congr {A B A' B' : ℤ → ℤ} {N q : ℕ} {row col mix : Prop}
    (hA : ∀ x ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1), A x = A' x)
    (hB : ∀ x ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1), B x = B' x)
    (h : RootData A B N q row col mix) : RootData A' B' N q row col mix := by
  obtain ⟨hq, w, r, hw, hr, hN, hd⟩ := h
  have hrq : 2 * q ≤ r * q := Nat.mul_le_mul_right q hr
  have hcast : (((N - 1 : ℕ)) : ℤ) = (N : ℤ) - 1 := by omega
  have hA' : ∀ x ∈ Finset.Icc (1 : ℤ) (((N - 1 : ℕ)) : ℤ), A x = A' x := by
    rw [hcast]; exact hA
  have hB' : ∀ x ∈ Finset.Icc (1 : ℤ) (((N - 1 : ℕ)) : ℤ), B x = B' x := by
    rw [hcast]; exact hB
  have hpre : ∀ x ∈ Finset.Icc (1 : ℤ) ((q : ℤ) - 1), x ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1) := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    omega
  refine ⟨hq, w, r, hw, hr, hN, ?_⟩
  rcases hd with ⟨hm, ⟨hA0, hB0, h1, h2, h3, h4, perA, perB, capA, capB, hs, hrow, hcol⟩⟩ |
      ⟨hm, hmx⟩
  · refine Or.inl ⟨hm, hA0, hB0, h1, h2, h3, h4, periodExcept_congr hA' perA,
      periodExcept_congr hB' perB, fun h => ?_, fun h => ?_, ?_, ?_, ?_⟩
    · rw [← hA hA0 (by rw [Finset.mem_Icc]; omega)]; exact capA h
    · rw [← hB hB0 (by rw [Finset.mem_Icc]; omega)]; exact capB h
    · rw [Finset.sum_congr rfl fun x hx => (hA x (hpre x hx)).symm,
        Finset.sum_congr rfl (fun x hx => (hB x (hpre x hx)).symm)]
      exact hs
    · intro hz
      exact hrow fun x hx => by
        rw [hA x (hpre x hx), hB x (hpre x hx)]; exact hz x hx
    · intro hz
      exact hcol fun x hx => by
        rw [hA x (hpre x hx), hB x (hpre x hx)]; exact hz x hx
  · refine Or.inr ⟨hm, ?_⟩
    rcases hmx with ⟨hw1, ⟨T, hTc, hT, per⟩, hf, hx1, hx2, e1, e2⟩ |
        ⟨hw1, ⟨T, hTc, hT, per⟩, hf, hx1, hx2, e1, e2⟩
    · refine Or.inl ⟨hw1, ⟨T, hTc, hT, periodExcept_congr hA' per⟩, periodExcept_congr hB' hf,
        hx1, hx2, ?_, ?_⟩
      · rw [← hB _ hx1]; exact e1
      · rw [← hB _ hx2]; exact e2
    · refine Or.inr ⟨hw1, ⟨T, hTc, hT, periodExcept_congr hB' per⟩, periodExcept_congr hA' hf,
        hx1, hx2, ?_, ?_⟩
      · rw [← hA _ hx1]; exact e1
      · rw [← hA _ hx2]; exact e2

/-- **`lem:gluing-lines` (1), word level.**  Let `A`, `B` be the boundary words of a parent of span
`N`: `{0, 1}`-valued on `[1, N - 1]`, with equal sums (the two end diagonals are singletons).  If
two roots of the parent have coprime periods `p`, `Q`, then neither is mixed, and the inners of both
are rows or the inners of both are columns. -/
theorem coprime_pair {A B : ℤ → ℤ} {N p Q : ℕ} {row₁ col₁ mix₁ row₂ col₂ mix₂ : Prop}
    (hbit : ∀ x ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1), (A x = 0 ∨ A x = 1) ∧ (B x = 0 ∨ B x = 1))
    (hsum : ∑ x ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1), A x =
      ∑ x ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - 1), B x)
    (hcop : Nat.Coprime p Q) (d₁ : RootData A B N p row₁ col₁ mix₁)
    (d₂ : RootData A B N Q row₂ col₂ mix₂) :
    ¬ mix₁ ∧ ¬ mix₂ ∧ ((row₁ ∧ row₂) ∨ (col₁ ∧ col₂)) := by
  obtain ⟨hp, w₁, r₁, hw₁, hr₁, hN₁, h₁⟩ := d₁
  obtain ⟨hQ, w₂, r₂, hw₂, hr₂, hN₂, h₂⟩ := d₂
  rcases h₁ with ⟨hm₁, o₁⟩ | ⟨hm₁, m₁⟩
  · rcases h₂ with ⟨hm₂, o₂⟩ | ⟨hm₂, m₂⟩
    swap
    · exact (false_mixed_ord (A := A) (B := B) m₂ o₁ hQ hp hr₂ hN₂ hr₁ hN₁ hcop.symm).elim
    refine ⟨hm₁, hm₂, ?_⟩
    obtain ⟨hA, hB, hA0, hAw, hB0, hBw, perA, perB, capA, capB, sing, hrow, hcol⟩ := o₁
    obtain ⟨kA, kB, kA0, kAw, kB0, kBw, perA', perB', capA', capB', sing', hrow', hcol'⟩ := o₂
    have hne : p ≠ Q := fun h => by
      subst h
      have := Nat.Coprime.eq_one_of_dvd hcop (dvd_refl p)
      omega
    have hmp : 2 * p ≤ r₁ * p := Nat.mul_le_mul_right p hr₁
    have hmQ : 2 * Q ≤ r₂ * Q := Nat.mul_le_mul_right Q hr₂
    have hL5 : 5 ≤ N - 1 := by
      rcases Nat.lt_or_gt_of_ne hne with h | h <;> omega
    have hL : (N - 1) + 1 = N := by omega
    have hcast : (((N - 1 : ℕ)) : ℤ) = (N : ℤ) - 1 := by omega
    have hbit' : ∀ x ∈ Finset.Icc (1 : ℤ) ((N - 1 : ℕ) : ℤ), (A x = 0 ∨ A x = 1) ∧
        (B x = 0 ∨ B x = 1) := by
      rw [hcast]; exact hbit
    have hsum' : ∑ x ∈ Finset.Icc (1 : ℤ) ((N - 1 : ℕ) : ℤ), A x =
        ∑ x ∈ Finset.Icc (1 : ℤ) ((N - 1 : ℕ) : ℤ), B x := by
      rw [hcast]; exact hsum
    obtain ⟨a, ha, hgA, hA0', hA1'⟩ := generic_word (f := A) (L := N - 1) hp hQ hr₁ hr₂ hw₁ hw₂
      hN₁ hN₂ hcop ⟨hA0, hAw⟩ ⟨kA0, kAw⟩ hL hL5 perA perA' (fun x hx => (hbit' x hx).1)
    obtain ⟨b, hb, hgB, hB0', hB1'⟩ := generic_word (f := B) (L := N - 1) hp hQ hr₁ hr₂ hw₁ hw₂
      hN₁ hN₂ hcop ⟨hB0, hBw⟩ ⟨kB0, kBw⟩ hL hL5 perB perB' (fun x hx => (hbit' x hx).2)
    have hM : (6 : ℤ) ≤ (p : ℤ) * Q := by exact_mod_cast six_le_mul_of_coprime hp hQ hcop
    have hq6 := six_mul_div_le (L := ((N - 1 : ℕ) : ℤ)) (M := (p : ℤ) * Q) (by omega) hM
    have hq0 : 0 ≤ (((N - 1 : ℕ) : ℤ) - 1) / (p * Q) :=
      Int.ediv_nonneg (by omega) (by omega)
    have hab : a = b := generic_eq (L := N - 1) (c := (((N - 1 : ℕ) : ℤ) - 1) / (p * Q) + 1)
      (by omega) hsum' ha hb hA0' hA1' hB0' hB1'
    subst hab
    have hp1 : (p : ℤ) - 1 ≤ ((N - 1 : ℕ) : ℤ) := by omega
    have hQ1 : (Q : ℤ) - 1 ≤ ((N - 1 : ℕ) : ℤ) := by omega
    have pre₁ := prefix_of_generic (n := (p : ℤ) - 1) (hA := hA) (hB := hB) ha
      (fun x hx => (hbit' x (Finset.Icc_subset_Icc_right hp1 hx)).1)
      (fun x hx => (hbit' x (Finset.Icc_subset_Icc_right hp1 hx)).2) sing
      (fun x hx hxA => hgA x (Finset.Icc_subset_Icc_right hp1 hx) (Or.inl (by
        rw [emod_eq_self_of_mem (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2]; exact hxA)))
      (fun x hx hxB => hgB x (Finset.Icc_subset_Icc_right hp1 hx) (Or.inl (by
        rw [emod_eq_self_of_mem (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2]; exact hxB)))
      capA capB
    have pre₂ := prefix_of_generic (n := (Q : ℤ) - 1) (hA := kA) (hB := kB) ha
      (fun x hx => (hbit' x (Finset.Icc_subset_Icc_right hQ1 hx)).1)
      (fun x hx => (hbit' x (Finset.Icc_subset_Icc_right hQ1 hx)).2) sing'
      (fun x hx hxA => hgA x (Finset.Icc_subset_Icc_right hQ1 hx) (Or.inr (by
        rw [emod_eq_self_of_mem (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2]; exact hxA)))
      (fun x hx hxB => hgB x (Finset.Icc_subset_Icc_right hQ1 hx) (Or.inr (by
        rw [emod_eq_self_of_mem (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2]; exact hxB)))
      capA' capB'
    rcases ha with rfl | rfl
    · exact Or.inl ⟨hrow fun x hx => pre₁ x hx, hrow' fun x hx => pre₂ x hx⟩
    · exact Or.inr ⟨hcol fun x hx => pre₁ x hx, hcol' fun x hx => pre₂ x hx⟩
  · exfalso
    rcases h₂ with ⟨hm₂, o₂⟩ | ⟨hm₂, m₂⟩
    · exact false_mixed_ord (A := A) (B := B) m₁ o₂ hp hQ hr₁ hN₁ hr₂ hN₂ hcop
    · exact false_mixed_mixed (A := A) (B := B) m₁ m₂ hp hQ hr₁ hN₁ hw₁ hr₂ hN₂ hw₂ hcop

end Lines

end SkewGluing
