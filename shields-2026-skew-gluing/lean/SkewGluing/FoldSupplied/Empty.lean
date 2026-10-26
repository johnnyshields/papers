import SkewGluing.FoldSupplied.Basics

/-!
# `ge:empty-fold`: the empty residue fold of a supplied inner

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in each
word» (`ge:empty-fold`).

`FoldSupplied.empty_fold`: let `K` be a connected diagram of span `g`, read as an inner with its
horizontal empty mark, and let `2 ≤ d < g`, `d ∣ g`.  Replace the value of both native words at the
returned residue zero by one common `lam ∈ {0, 1}`.  If the two completed words are
`d`-periodic, then `K` is the empty composition of the row (`lam = 0`) or the column (`lam = 1`)
of `g / d` cells with an inner `K₀` of span `d`: the chart is proper and legal, its mark is the
horizontal empty mark, both factors have strictly smaller occupied area, and `K₀` retains the
native words of `K` on `1, …, d - 1`.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open SmallOverlap

theorem sum_range_height_split {H : ℕ → ℤ} (hpos : ∀ k, 0 < H k) (d n : ℕ) :
    ∑ k ∈ Finset.range d, H k + 0 ≤ ∑ k ∈ Finset.range (d + n), H k := by
  rw [Finset.sum_range_add]
  have : 0 ≤ ∑ k ∈ Finset.range n, H (d + k) :=
    Finset.sum_nonneg fun k _ => (hpos _).le
  linarith

/-- `Σ_{j<M} H(j d) + M ≤ Σ_{k<M d} H(k)` for positive heights and `d ≥ 2`. -/
theorem sum_blocks_lt {H : ℕ → ℤ} {d : ℕ} (hd : 2 ≤ d) (hpos : ∀ k, 0 < H k) (M : ℕ) :
    ∑ j ∈ Finset.range M, H (j * d) + M ≤ ∑ k ∈ Finset.range (M * d), H k := by
  induction M with
  | zero => simp
  | succ M ih =>
    have e : (M + 1) * d = M * d + d := by ring
    rw [e, Finset.sum_range_add H (M * d) d, Finset.sum_range_succ]
    have h2 : H (M * d + 0) + H (M * d + 1) ≤ ∑ c ∈ Finset.range d, H (M * d + c) := by
      have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range d := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_range]; omega
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun c => H (M * d + c)) hsub
        (fun i _ _ => (hpos _).le)
      simpa using this
    have h3 := hpos (M * d + 1)
    simp only [add_zero] at h2
    push_cast
    linarith

theorem empty_fold {K : Diagram} (hK : IsConnectedSkew K) {g d : ℕ} (hd : 2 ≤ d) (hdg : d < g)
    (hdvd : d ∣ g) (hspan : span K = g) {lam : ℤ} (hlam : lam = 0 ∨ lam = 1)
    (hA : ∀ k, d ≤ k → k < g → completedA K lam k = completedA K lam (k - d))
    (hB : ∀ k, d ≤ k → k < g → completedB K lam k = completedB K lam (k - d)) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf K ∧ χ.period = d ∧ χ.ω = emptyMarkH χ.ω.E ∧
      χ.ω.W = ∅ ∧ χ.D = lineOuter (g / d) lam ∧ χ.D.card < K.card ∧ χ.ω.E.card < K.card ∧
      (∀ k, 1 ≤ k → k < d → wordA χ.ω.E k = wordA K k ∧ wordB χ.ω.E k = wordB K k) := by
  obtain ⟨M, hM⟩ := hdvd
  have hd0 : 0 < d := by omega
  have hNM : g / d = M := by rw [hM]; exact Nat.mul_div_cancel_left M hd0
  have hbitsK : IsBitData (span K) (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) :=
    isBitData_of_isConnectedSkew hK
  rw [hspan] at hbitsK
  have hbd : BlockData d g (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) := by
    refine ⟨hbitsK, ?_, ⟨M, hM⟩, hd, hdg⟩
    intro n hn1 hn2 hmod
    have h1 := hA (n + d) (by omega) (by omega)
    have h2 := hB (n + d) (by omega) (by omega)
    simp only [completedA, completedB, Nat.add_sub_cancel] at h1 h2
    have e1 : n + d ≠ 0 := by omega
    have e2 : n ≠ 0 := by omega
    simp only [e1, e2, ite_false] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  -- the interior positions at multiples of `d` hold `lam`
  have hmult : ∀ j : ℕ, 1 ≤ j → j < M →
      wordA K ((j * d : ℕ) : ℤ) = lam ∧ wordB K ((j * d : ℕ) : ℤ) = lam := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro _ hj
      have h1 := hA ((j + 1) * d) (by nlinarith) (by nlinarith)
      have h2 := hB ((j + 1) * d) (by nlinarith) (by nlinarith)
      have e : (j + 1) * d - d = j * d := by rw [Nat.succ_mul, Nat.add_sub_cancel]
      rw [e] at h1 h2
      have hne : (j + 1) * d ≠ 0 := by positivity
      simp only [completedA, completedB, hne, ite_false] at h1 h2
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        simp only [zero_mul, ite_true] at h1 h2
        simp only [zero_add, one_mul] at h1 h2 ⊢
        exact ⟨h1, h2⟩
      · have hne' : j * d ≠ 0 := by positivity
        simp only [hne', ite_false] at h1 h2
        have := ih (by omega) (by omega)
        rw [h1, h2]; exact this
  obtain ⟨E', hE'⟩ : ∃ E' : Diagram, E' = fromBits d (fun k : ℕ => wordA K k)
    (fun k : ℕ => wordB K k) := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : Diagram, D' = fromBits (span K / d)
    (BlockData.outerA d (fun k : ℕ => wordA K k)) (BlockData.outerA d (fun k : ℕ => wordB K k)) :=
    ⟨_, rfl⟩
  obtain ⟨ω', hω'⟩ : ∃ ω' : MarkedInner, ω' = MarkedInner.mk E' ∅ (vH E') .a := ⟨_, rfl⟩
  obtain ⟨hE'c, hD'c, hleg, hper, hF'⟩ := emptyRoot_core hK (fun k => rfl) (fun k => rfl)
    (hspan ▸ hbd) hE' hD' hω'
  have hspan' : span K / d = M := by rw [hspan]; exact hNM
  have hM2 : 2 ≤ M := by
    by_contra hcon
    have : d * M ≤ d * 1 := Nat.mul_le_mul_left d (by omega)
    omega
  have houter : IsBitData M (BlockData.outerA d (fun k : ℕ => wordA K k))
      (BlockData.outerA d (fun k : ℕ => wordB K k)) := by
    have := hbd.isBitData_outer
    rwa [hNM] at this
  have hDline : D' = lineOuter M lam := by
    rw [hD', hspan']
    unfold lineOuter
    apply fromBits_congr
    · intro k hk1 hk2
      exact (hmult k hk1 hk2).1
    · intro k hk1 hk2
      exact (hmult k hk1 hk2).2
  have hinner : IsBitData d (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) := hbd.bits_inner
  have hE'sp : span E' = d := by rw [hE']; exact span_fromBits hinner
  have hD'sp : span D' = M := by rw [hD']; rw [hspan']; exact span_fromBits houter
  have hωE : ω'.E = E' := by rw [hω']
  have hpos : ∀ k, k < g → 0 < heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) k :=
    fun k hk => hbitsK.2.2.1 k hk
  have hpos' : ∀ k, 0 < heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k)
      (if k < g then k else 0) := by
    intro k
    by_cases hk : k < g
    · simp only [hk, ite_true]; exact hpos k hk
    · simp only [hk, ite_false]; exact hpos 0 (by omega)
  -- areas
  have hKcard := card_eq_sum_heightWord hK
  rw [hspan] at hKcard
  have hE'card : ((E'.card : ℕ) : ℤ) = ∑ k ∈ Finset.range d,
      heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) k := by
    rw [hE']; exact card_fromBits hinner
  have hD'card : ((D'.card : ℕ) : ℤ) = ∑ j ∈ Finset.range M,
      heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) (j * d) := by
    rw [hD', hspan']
    rw [card_fromBits houter]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have : j * d ≤ (M - 1) * d := Nat.mul_le_mul_right d (by omega)
    have h3 : (M - 1) * d + d = g := by
      rw [hM, Nat.mul_comm d M, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    have hjd : j * d ≤ g - 1 := by omega
    rw [hbd.heightWord_outer hjd]
  have hlt1 : E'.card < K.card := by
    have hsplit : ∑ k ∈ Finset.range g,
        heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) k =
        ∑ k ∈ Finset.range d, heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) k +
        ∑ k ∈ Finset.range (g - d),
          heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) (d + k) := by
      have hdg' : d + (g - d) = g := by omega
      rw [← Finset.sum_range_add, hdg']
    have hp : 0 < ∑ k ∈ Finset.range (g - d),
        heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) (d + k) := by
      apply Finset.sum_pos
      · intro k hk; rw [Finset.mem_range] at hk; exact hpos _ (by omega)
      · exact ⟨0, by rw [Finset.mem_range]; omega⟩
    have : (E'.card : ℤ) < K.card := by rw [hKcard, hE'card, hsplit]; linarith
    exact_mod_cast this
  have hlt2 : D'.card < K.card := by
    have hb := sum_blocks_lt (H := fun k => if k < g then
      heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) k else 1) hd
      (fun k => by by_cases hk : k < g <;> simp [hk, hpos k]) M
    have e1 : ∑ j ∈ Finset.range M, (fun k => if k < g then
        heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) k else 1) (j * d) =
        ∑ j ∈ Finset.range M,
          heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) (j * d) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have : j * d < g := by rw [hM]; exact Nat.mul_lt_mul_of_pos_right hj hd0 |>.trans_eq (by ring)
      simp [this]
    have e2 : ∑ k ∈ Finset.range (M * d), (fun k => if k < g then
        heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) k else 1) k =
        ∑ k ∈ Finset.range g,
          heightWord (fun k : ℕ => wordA K k) (fun k : ℕ => wordB K k) k := by
      have : M * d = g := by rw [hM]; ring
      rw [this]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      simp [hk]
    rw [e1, e2] at hb
    have : (D'.card : ℤ) < K.card := by rw [hKcard, hD'card]; omega
    exact_mod_cast this
  refine ⟨⟨D', ω'⟩, ⟨hD'c, ?_, ?_, hleg⟩, hF', hper, ?_, ?_, ?_, hlt2, ?_, ?_⟩
  · change 2 ≤ D'.card
    have h1 : span D' ≤ D'.card := SmallOverlap.card_ge_span
    omega
  · change 2 ≤ ω'.E.card
    have h1 : span ω'.E ≤ ω'.E.card := SmallOverlap.card_ge_span
    rw [hωE] at h1 ⊢
    omega
  · change ω' = emptyMarkH ω'.E
    rw [hω']; rfl
  · rw [hω']
  · change D' = lineOuter (g / d) lam
    rw [hNM]; exact hDline
  · change ω'.E.card < K.card
    rw [hωE]; exact hlt1
  · intro k hk1 hk2
    change wordA ω'.E k = _ ∧ wordB ω'.E k = _
    rw [hωE, hE']
    exact ⟨bitA_fromBits hinner hk1 hk2, bitB_fromBits hinner hk1 hk2⟩

end FoldSupplied
end SkewGluing
