import SkewGluing.Decoder.Words
import SkewGluing.Decoder.Defs
import SkewGluing.Decoder.Util
import SkewGluing.Decoder.Native
import SkewGluing.Decoder.Ports
import SkewGluing.Decoder.Heights

/-!
# Recovery of the outer factor from the two generic words

Formalizes `shields-2026-skew-gluing.tex`, «Reconstructing a chart from its two words»
(`ge:decoder`, `ge:eq:ports`, `ge:eq:sample`, `ge:remark:cut`).

`MarkedInner.decoder` is `ge:decoder`.  Let `ω` be a full legal marked inner of period `f ≥ 2`,
with phases `(s, t)` (the middle phases of a nonempty mark, `(0, 0)` for the empty mark), and let
`P` be a connected diagram of span `m f + a`, `m ≥ 1`, whose closed boundary words `Xw`, `Yw`
agree with the native words of the inner at every nonvariable slot (the variable slots are the
residues `holesB` of the row word and `holesA` of the column word, the table `ge:eq:ports`; the
interior variable strings are unconstrained).  Then `P` is a translate of `A ∘_ω E` for a
connected outer `A` of span `m`, unique up to translation; its heights are the private heights
`h_A(j) = h_P(j f + a) = h_P((j + 1) f - 1) > 0` (`ge:eq:sample`); for `m ≥ 2` both factors have
at least two cells and strictly smaller occupied area than `P`; for `m = 1` the outer is a cell
and `P` is a translate of the inner.

The compiler direction is proved in three modules: `compose_native` (every nonvariable position of a
composite repeats the native word of the inner), `compose_ports` (the table `ge:eq:ports`, read by
`portDecode`) and `hwd_compose_private` (`ge:eq:sample` for a composite).  The decoder compares `P`
with a composite on a reference outer to obtain the height increments of its blocks, which gives the
binary interval criterion for the decoded words, builds the outer with `fromBits`, and
identifies `P` with the composite by `eq_translate_of_bits`.

`MarkedInner.decoder_of_cut_windows` is `ge:remark:cut`: the nonvariable-slot hypothesis may be
checked on two position ranges that cover the words.

Sorry-free.
-/

namespace SkewGluing

/-- The generic `(Y - X)` charge of the table `ge:eq:ports`, with the sign that makes the variable
contribution of a block equal to `y_j - x_j` plus this charge. -/
def caseCharge : AttachCase → ℤ
  | .a => 0
  | .b => 0
  | .c => -1
  | .d => 1

/-- The contribution of the variable slots of block `j` to the height increment of a closed pair
of words. -/
def varSum (x : AttachCase) (s t f : ℤ) (P : Diagram) (j : ℤ) : ℤ :=
  ∑ r ∈ holesA x s t, Yw P (j * f + r) - ∑ r ∈ holesB x s t, Xw P (j * f + r)

theorem varSum_eq (x : AttachCase) (s t f : ℤ) (P : Diagram) (j : ℤ)
    (hd : x.IsMixed → s ≠ t) :
    varSum x s t f P j =
      (portDecode x s t f P j).2 - (portDecode x s t f P j).1 + caseCharge x := by
  cases x
  · simp [varSum, holesA, holesB, portDecode, caseCharge]
  · simp [varSum, holesA, holesB, portDecode, caseCharge]
  · have h' : t ≠ s := fun h => hd (Or.inl rfl) h.symm
    simp only [varSum, holesA, holesB, portDecode, caseCharge, Finset.sum_pair h',
      Finset.sum_empty]
    ring
  · have h' : t ≠ s := fun h => hd (Or.inr rfl) h.symm
    simp only [varSum, holesA, holesB, portDecode, caseCharge, Finset.sum_pair h',
      Finset.sum_empty]
    ring

namespace MarkedInner

theorem IsLegal.exists_hasPhases {ω : MarkedInner} (hω : ω.IsLegal) : ∃ s t, ω.HasPhases s t := by
  by_cases hW : ω.W = ∅
  · exact ⟨0, 0, Or.inl ⟨hW, rfl, rfl⟩⟩
  · obtain ⟨s, t, hp⟩ := (show ω.IsLegalNonempty from
      ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩).exists_phases
    exact ⟨s, t, Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr hW, hp⟩⟩

/-- The slots lie among the marked residues, `s ≠ t` in the mixed cases, and the width is below
the period. -/
theorem HasPhases.facts {ω : MarkedInner} (hω : ω.IsLegal) {s t : ℤ} (hph : ω.HasPhases s t) :
    (0 ≤ s ∧ s ≤ ω.widthZ ∧ 0 ≤ t ∧ t ≤ ω.widthZ) ∧
    (∀ r ∈ holesA ω.case s t, 0 ≤ r ∧ r ≤ ω.widthZ) ∧
    (∀ r ∈ holesB ω.case s t, 0 ≤ r ∧ r ≤ ω.widthZ) ∧ (ω.case.IsMixed → s ≠ t) ∧
    0 ≤ ω.widthZ ∧ ω.widthZ < ω.period := by
  have hn : 0 ≤ ω.widthZ ∧ ω.widthZ < ω.period := hω.2.2.1
  rcases hph with ⟨hW, rfl, rfl⟩ | ⟨hW, hp⟩
  · have hE : ω.IsLegalEmpty := ⟨hω, hW⟩
    have hc := hE.case_a
    have hw := hE.width_zero
    refine ⟨by omega, ?_, ?_, ?_, hn⟩
    · intro r hr
      rw [hc] at hr
      simp only [holesA, Finset.mem_singleton] at hr
      omega
    · intro r hr
      rw [hc] at hr
      simp only [holesB, Finset.mem_singleton] at hr
      omega
    · intro h
      rw [hc] at h
      simp [AttachCase.IsMixed] at h
  · have hl : ω.IsLegalNonempty := ⟨hω, hW⟩
    obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hp
    refine ⟨⟨by omega, hs2, ht1, by omega⟩, ?_, ?_, ?_, hn⟩
    · intro r hr
      cases hc : ω.case <;> simp only [hc, holesA, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty] at hr <;> omega
    · intro r hr
      cases hc : ω.case <;> simp only [hc, holesB, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty] at hr <;> omega
    · intro hmix
      have := hl.phases_lt hmix hp
      omega

end MarkedInner

/-- The height increment of the block `j`: `h(j f + a) - h((j - 1) f + a)`, with `h(-1) = 0`. -/
def blk (P : Diagram) (f a j : ℤ) : ℤ :=
  hwd P (j * f + a) - if j = 0 then 0 else hwd P ((j - 1) * f + a)

/-- The first position of the window of block `j`. -/
def blkLo (f a j : ℤ) : ℤ := if j = 0 then 0 else (j - 1) * f + a + 1

theorem blkLo_bounds {f a j : ℤ} (hj : 0 ≤ j) (hf : 0 < f) (haf : a < f) (ha : 0 ≤ a) :
    j * f - (f - a - 1) ≤ blkLo f a j ∧ blkLo f a j ≤ j * f ∧ 0 ≤ blkLo f a j := by
  unfold blkLo
  by_cases h0 : j = 0
  · subst h0; simp; omega
  · have hj1 : 0 ≤ j - 1 := by omega
    have hp : 0 ≤ (j - 1) * f := mul_nonneg hj1 hf.le
    have e : j * f = (j - 1) * f + f := by ring
    simp only [h0, ite_false]
    omega

theorem blk_sum (P : Diagram) {f a j : ℤ} (hj : 0 ≤ j) (hf : 0 < f) (ha : 0 ≤ a) :
    blk P f a j = ∑ i ∈ Finset.Icc (blkLo f a j) (j * f + a), (Yw P i - Xw P i) := by
  by_cases h0 : j = 0
  · subst h0
    simp [blk, blkLo, hwd]
  · have hj1 : 0 ≤ j - 1 := by omega
    have hp : 0 ≤ (j - 1) * f := mul_nonneg hj1 hf.le
    have e : j * f = (j - 1) * f + f := by ring
    simp only [blk, blkLo, h0, ite_false]
    rw [hwd_sub P (by omega) (by omega)]

theorem window_diff {P C : Diagram} {x : AttachCase} {s t f a j lo N : ℤ}
    (hA : ∀ r ∈ holesA x s t, 0 ≤ r ∧ r ≤ a) (hB : ∀ r ∈ holesB x s t, 0 ≤ r ∧ r ≤ a)
    (haf : a < f) (hf : 0 < f) (hlo1 : j * f - (f - a - 1) ≤ lo) (hlo2 : lo ≤ j * f)
    (hlo0 : 0 ≤ lo) (hjN : j * f + a ≤ N)
    (hY : ∀ i, 0 ≤ i → i ≤ N → i % f ∉ holesA x s t → Yw P i = Yw C i)
    (hX : ∀ i, 0 ≤ i → i ≤ N → i % f ∉ holesB x s t → Xw P i = Xw C i) :
    ∑ i ∈ Finset.Icc lo (j * f + a), (Yw P i - Xw P i) -
        ∑ i ∈ Finset.Icc lo (j * f + a), (Yw C i - Xw C i) =
      varSum x s t f P j - varSum x s t f C j := by
  have e1 := sum_block (g := fun i => Yw P i - Yw C i) hA haf hlo1 hlo2
    (fun i h1 h2 h3 => by simp only [hY i (by omega) (by omega) h3, sub_self]) hf
  have e2 := sum_block (g := fun i => Xw P i - Xw C i) hB haf hlo1 hlo2
    (fun i h1 h2 h3 => by simp only [hX i (by omega) (by omega) h3, sub_self]) hf
  have e3 : ∑ i ∈ Finset.Icc lo (j * f + a), (Yw P i - Xw P i) -
        ∑ i ∈ Finset.Icc lo (j * f + a), (Yw C i - Xw C i) =
      ∑ i ∈ Finset.Icc lo (j * f + a), (Yw P i - Yw C i) -
        ∑ i ∈ Finset.Icc lo (j * f + a), (Xw P i - Xw C i) := by
    simp only [Finset.sum_sub_distrib]; ring
  rw [e3, e1, e2]
  unfold varSum
  simp only [Finset.sum_sub_distrib]
  ring

end SkewGluing
namespace SkewGluing

namespace MarkedInner

theorem blk_compose {ω : MarkedInner} (hω : ω.IsLegal) (hf : 2 ≤ ω.period) {A : Diagram}
    (hA : IsConnectedSkew A) {j : ℤ} (hj0 : 0 ≤ j) (hj : j ≤ (span A : ℤ)) :
    blk (ω.compose A) ω.period ω.widthZ j = Yw A j - Xw A j := by
  have hC := hω.isConnectedSkew_compose hA
  have hspC : (span (ω.compose A) : ℤ) = span A * ω.period + ω.widthZ := by
    rw [span_compose hA hω]; rfl
  have hn : 0 ≤ ω.widthZ ∧ ω.widthZ < ω.period := hω.2.2.1
  have hs : ∀ i : ℤ, 0 ≤ i → i < (span A : ℤ) →
      hwd (ω.compose A) (i * ω.period + ω.widthZ) = hwd A i := fun i h1 h2 =>
    (hω.hwd_compose_private hf hA h1 h2).1
  have hlast : hwd (ω.compose A) ((span A : ℤ) * ω.period + ω.widthZ) = hwd A (span A : ℤ) := by
    rw [← hspC, hwd_span hC, hwd_span hA]
  have hs' : ∀ i : ℤ, 0 ≤ i → i ≤ (span A : ℤ) →
      hwd (ω.compose A) (i * ω.period + ω.widthZ) = hwd A i := by
    intro i h1 h2
    rcases lt_or_eq_of_le h2 with h | h
    · exact hs i h1 h
    · rw [h]; exact hlast
  unfold blk
  by_cases h0 : j = 0
  · subst h0
    simp only [ite_true, sub_zero, zero_mul, zero_add]
    have := hs' 0 (le_refl _) (by omega)
    simp only [zero_mul, zero_add] at this
    rw [this, hwd_zero, Yw_zero, Xw_zero]
    norm_num
  · simp only [h0, ite_false]
    rw [hs' j hj0 hj, hs' (j - 1) (by omega) (by omega)]
    have := hwd_succ A (k := j - 1) (by omega)
    rw [show j - 1 + 1 = j by ring] at this
    omega

theorem decoder_blocks {ω : MarkedInner} (hω : ω.IsLegal) (hf : 2 ≤ ω.period) {s t : ℤ}
    (hph : ω.HasPhases s t) {P : Diagram} {m : ℕ} (hm : 1 ≤ m)
    (hN : (span P : ℤ) = m * ω.period + ω.widthZ)
    (hnat : ∀ k : ℤ, 0 ≤ k → k ≤ (span P : ℤ) →
      (k % ω.period ∉ holesB ω.case s t →
        Xw P k = Xw ω.E (natPos ω.period m k)) ∧
      (k % ω.period ∉ holesA ω.case s t →
        Yw P k = Yw ω.E (natPos ω.period m k))) :
    ∀ j : ℤ, 0 ≤ j → j ≤ m →
      blk P ω.period ω.widthZ j =
        (portDecode ω.case s t ω.period P j).2 - (portDecode ω.case s t ω.period P j).1 := by
  obtain ⟨hst, hA, hB, hmix, ha0, haf⟩ := hph.facts hω
  have hf0 : 0 < ω.period := by omega
  obtain ⟨A0, hA0, hsA0⟩ := exists_outer_span hm
  have hC0 := hω.isConnectedSkew_compose hA0
  have hspC0 : (span (ω.compose A0) : ℤ) = m * ω.period + ω.widthZ := by
    rw [span_compose hA0 hω, hsA0]; rfl
  have nat0 := hω.compose_native hph hf hA0
  rw [hsA0] at nat0
  intro j hj0 hj
  obtain ⟨h1, h2, h3⟩ := blkLo_bounds hj0 hf0 haf ha0
  have hjN : j * ω.period + ω.widthZ ≤ (span P : ℤ) := by
    have : j * ω.period ≤ m * ω.period := mul_le_mul_of_nonneg_right hj hf0.le
    omega
  have hdiff := window_diff (P := P) (C := ω.compose A0) (x := ω.case) (s := s) (t := t)
    (f := ω.period) (a := ω.widthZ) (j := j) (lo := blkLo ω.period ω.widthZ j)
    (N := (span P : ℤ)) hA hB haf hf0 h1 h2 h3 hjN
    (fun i hi0 hiN hi => by
      rw [(hnat i hi0 hiN).2 hi, (nat0 i hi0 (by omega)).2 hi])
    (fun i hi0 hiN hi => by
      rw [(hnat i hi0 hiN).1 hi, (nat0 i hi0 (by omega)).1 hi])
  rw [← blk_sum P hj0 hf0 ha0, ← blk_sum (ω.compose A0) hj0 hf0 ha0,
    blk_compose hω hf hA0 hj0 (by omega), varSum_eq _ _ _ _ _ _ hmix,
    varSum_eq _ _ _ _ _ _ hmix, hω.compose_ports hph hA0 j hj0 (by omega)] at hdiff
  simp only at hdiff
  omega

end MarkedInner

end SkewGluing
namespace SkewGluing

namespace MarkedInner

/-- **`ge:decoder`, the construction.**  Let `(ω, s, t)` be a legal marked inner of period `f ≥ 2`
with its phases, and let `P` be connected of span `m f + a`, `m ≥ 1`, whose closed boundary words
agree with the native words of `ω.E` off the variable slots.  Then `P` is a translate of `A ∘_ω E`
for a connected outer `A` of span `m`, unique up to translation, whose heights are the private
heights of `P`. -/
theorem decoder_exists {ω : MarkedInner} (hω : ω.IsLegal) (hf : 2 ≤ ω.period) {s t : ℤ}
    (hph : ω.HasPhases s t) {P : Diagram} (hP : IsConnectedSkew P) {m : ℕ} (hm : 1 ≤ m)
    (hN : (span P : ℤ) = m * ω.period + ω.widthZ)
    (hnat : ∀ k : ℤ, 0 ≤ k → k ≤ (span P : ℤ) →
      (k % ω.period ∉ holesB ω.case s t →
        Xw P k = Xw ω.E (natPos ω.period m k)) ∧
      (k % ω.period ∉ holesA ω.case s t →
        Yw P k = Yw ω.E (natPos ω.period m k))) :
    ∃ A : Diagram, IsConnectedSkew A ∧ span A = m ∧
      (∃ u, P = SkewGluing.translate u (ω.compose A)) ∧
      (∀ j : ℤ, 0 ≤ j → j < m →
        hwd A j = hwd P (j * ω.period + ω.widthZ) ∧
        hwd P (j * ω.period + ω.widthZ) = hwd P ((j + 1) * ω.period - 1) ∧ 0 < hwd A j) ∧
      (∀ A' : Diagram, IsConnectedSkew A' → ∀ u', P = SkewGluing.translate u' (ω.compose A') →
        ∃ w, A' = SkewGluing.translate w A) := by
  obtain ⟨hst, hHA, hHB, hmix, ha0, haf⟩ := hph.facts hω
  have hf0 : 0 < ω.period := by omega
  have hblk := decoder_blocks hω hf hph hm hN hnat
  set f := ω.period with hfdef
  set a := ω.widthZ with hadef
  obtain ⟨x, hx⟩ : ∃ x : ℤ → ℤ, ∀ j, x j = (portDecode ω.case s t f P j).1 := ⟨_, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℤ → ℤ, ∀ j, y j = (portDecode ω.case s t f P j).2 := ⟨_, fun _ => rfl⟩
  -- the bits of the decoded words
  have hbit : ∀ j : ℤ, 0 ≤ j → j ≤ m → (x j = 0 ∨ x j = 1) ∧ (y j = 0 ∨ y j = 1) := by
    intro j hj0 hj
    have hjf : j * f ≤ m * f := mul_le_mul_of_nonneg_right hj hf0.le
    have hjf0 : 0 ≤ j * f := mul_nonneg hj0 hf0.le
    have BX : ∀ r : ℤ, 0 ≤ r → r ≤ a → (Xw P (j * f + r) = 0 ∨ Xw P (j * f + r) = 1) :=
      fun r h1 h2 => Xw_bit hP (by omega) (by omega)
    have BY : ∀ r : ℤ, 0 ≤ r → r ≤ a → (Yw P (j * f + r) = 0 ∨ Yw P (j * f + r) = 1) :=
      fun r h1 h2 => Yw_bit hP (by omega) (by omega)
    have bs := BX s hst.1 hst.2.1
    have bt := BX t hst.2.2.1 hst.2.2.2
    have cs := BY s hst.1 hst.2.1
    have ct := BY t hst.2.2.1 hst.2.2.2
    rw [hx j, hy j]
    cases ω.case <;> simp only [portDecode] <;> omega
  -- the heights at the private diagonals
  set H : ℤ → ℤ := fun j => hwd P (j * f + a) with hH
  have hHstep : ∀ j : ℤ, 1 ≤ j → j ≤ m → H j = H (j - 1) + (y j - x j) := by
    intro j hj1 hj
    have := hblk j (by omega) hj
    rw [← hx j, ← hy j] at this
    unfold blk at this
    simp only [show j ≠ 0 by omega, ite_false] at this
    simp only [hH]
    omega
  have hH0 : H 0 = y 0 - x 0 := by
    have := hblk 0 (le_refl _) (by omega)
    rw [← hx 0, ← hy 0] at this
    simpa [blk, hH] using this
  have hHpos : ∀ j : ℤ, 0 ≤ j → j < m → 0 < H j := by
    intro j hj0 hj
    have hjf : j * f ≤ (m - 1) * f := mul_le_mul_of_nonneg_right (by omega) hf0.le
    have e : (m - 1 : ℤ) * f = m * f - f := by ring
    exact hwd_pos hP (by have := mul_nonneg hj0 hf0.le; omega) (by omega)
  have hHm : H m = 0 := by
    have : (m : ℤ) * f + a = span P := by omega
    simp only [hH, this]
    exact hwd_span hP
  have hm1 : (0 : ℤ) ≤ (m : ℤ) - 1 := by omega
  have hx0 : x 0 = 0 ∧ y 0 = 1 := by
    have := hHpos 0 (le_refl _) (by omega)
    have := hbit 0 (le_refl _) (by omega)
    omega
  have hxm : x m = 1 ∧ y m = 0 ∧ H ((m : ℤ) - 1) = 1 := by
    have h1 := hHstep m (by omega) (le_refl _)
    have h2 := hHpos ((m : ℤ) - 1) hm1 (by omega)
    have := hbit m (by omega) (le_refl _)
    omega
  -- the outer
  have hbd : IsBitData m (fun k : ℕ => y k) (fun k : ℕ => x k) := by
    have hheight : ∀ k : ℕ, k ≤ m → heightWord (fun k : ℕ => y k) (fun k : ℕ => x k) k = H k := by
      intro k
      induction k with
      | zero =>
        intro _
        simp only [heightWord, Finset.range_zero, Finset.sum_empty, add_zero, Nat.cast_zero]
        omega
      | succ k ih =>
        intro hk
        rw [heightWord_succ, ih (by omega)]
        have := hHstep ((k : ℤ) + 1) (by omega) (by exact_mod_cast hk)
        push_cast at this ⊢
        rw [show (k : ℤ) + 1 - 1 = k by ring] at this
        omega
    refine ⟨by omega, fun k hk1 hk2 => ?_, fun k hk => ?_, ?_⟩
    · have := hbit k (by omega) (by exact_mod_cast hk2.le)
      exact ⟨this.2, this.1⟩
    · rw [hheight k hk.le]
      exact hHpos k (by omega) (by exact_mod_cast hk)
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [hheight m' (by omega)]
      have := hxm.2.2
      simpa using this
  set A := fromBits m (fun k : ℕ => y k) (fun k : ℕ => x k) with hAdef
  have hAc : IsConnectedSkew A := isConnectedSkew_fromBits hbd
  have hspA : span A = m := span_fromBits hbd
  have hXA : ∀ j : ℤ, 0 ≤ j → j ≤ m → Xw A j = x j := by
    intro j hj0 hj
    by_cases h0 : j = 0
    · subst h0; rw [Xw_zero, hx0.1]
    · by_cases hm' : j = m
      · subst hm'
        have := Xw_span (P := A) (by rw [hspA]; exact_mod_cast hm)
        rw [hspA] at this
        rw [this, hxm.1]
      · rw [Xw_of_mem (by omega) (by rw [hspA]; omega)]
        obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
        unfold wordB
        rw [bitB_fromBits hbd (by omega) (by omega)]
  have hYA : ∀ j : ℤ, 0 ≤ j → j ≤ m → Yw A j = y j := by
    intro j hj0 hj
    by_cases h0 : j = 0
    · subst h0; rw [Yw_zero, hx0.2]
    · by_cases hm' : j = m
      · subst hm'
        have := Yw_span (P := A) (by rw [hspA]; exact_mod_cast hm)
        rw [hspA] at this
        rw [this, hxm.2.1]
      · rw [Yw_of_mem (by omega) (by rw [hspA]; omega)]
        obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
        unfold wordA
        rw [bitA_fromBits hbd (by omega) (by omega)]
  -- the composite
  have hC := hω.isConnectedSkew_compose hAc
  have hspC : (span (ω.compose A) : ℤ) = m * f + a := by
    rw [span_compose hAc hω, hspA]; rfl
  have natC := hω.compose_native hph hf hAc
  rw [hspA] at natC
  have portC := hω.compose_ports hph hAc
  have hslot : ∀ j : ℤ, 0 ≤ j → j ≤ m →
      (∀ r ∈ holesB ω.case s t, Xw P (j * f + r) = Xw (ω.compose A) (j * f + r)) ∧
      (∀ r ∈ holesA ω.case s t, Yw P (j * f + r) = Yw (ω.compose A) (j * f + r)) := by
    intro j hj0 hj
    have e := portC j hj0 (by rw [hspA]; exact hj)
    rw [hXA j hj0 hj, hYA j hj0 hj] at e
    have hPC : portDecode ω.case s t f P j = portDecode ω.case s t f (ω.compose A) j := by
      rw [e]; exact Prod.ext (hx j).symm (hy j).symm
    revert hPC
    cases ω.case <;> intro hPC <;> simp only [portDecode, Prod.mk.injEq] at hPC <;>
      refine ⟨fun r hr => ?_, fun r hr => ?_⟩ <;>
      simp only [holesA, holesB, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty] at hr <;>
      first
        | exact hr.elim
        | (subst hr; omega)
        | (rcases hr with rfl | rfl <;> omega)
  have hXeq : ∀ k : ℤ, 0 ≤ k → k ≤ m * f + a → Xw P k = Xw (ω.compose A) k := by
    intro k hk0 hk
    by_cases hmem : k % f ∈ holesB ω.case s t
    · have hj0 : 0 ≤ k / f := Int.ediv_nonneg hk0 hf0.le
      have hjm : k / f ≤ m := by
        have : k / f < m + 1 := by
          rw [Int.ediv_lt_iff_lt_mul hf0]; nlinarith
        omega
      have e : k / f * f + k % f = k := by
        have := Int.mul_ediv_add_emod k f; linarith
      have := (hslot (k / f) hj0 hjm).1 (k % f) hmem
      rwa [e] at this
    · rw [(hnat k hk0 (by omega)).1 hmem, (natC k hk0 (by omega)).1 hmem]
  have hYeq : ∀ k : ℤ, 0 ≤ k → k ≤ m * f + a → Yw P k = Yw (ω.compose A) k := by
    intro k hk0 hk
    by_cases hmem : k % f ∈ holesA ω.case s t
    · have hj0 : 0 ≤ k / f := Int.ediv_nonneg hk0 hf0.le
      have hjm : k / f ≤ m := by
        have : k / f < m + 1 := by
          rw [Int.ediv_lt_iff_lt_mul hf0]; nlinarith
        omega
      have e : k / f * f + k % f = k := by
        have := Int.mul_ediv_add_emod k f; linarith
      have := (hslot (k / f) hj0 hjm).2 (k % f) hmem
      rwa [e] at this
    · rw [(hnat k hk0 (by omega)).2 hmem, (natC k hk0 (by omega)).2 hmem]
  have hspeq : span (ω.compose A) = span P := by omega
  obtain ⟨v, hv⟩ := eq_translate_of_bits hC hP hspeq
    (fun k hk1 hk2 => by
      have h := hYeq k (by omega) (by omega)
      rw [Yw_of_mem (by omega) (by omega), Yw_of_mem (by omega) (by omega)] at h
      exact h.symm)
    (fun k hk1 hk2 => by
      have h := hXeq k (by omega) (by omega)
      rw [Xw_of_mem (by omega) (by omega), Xw_of_mem (by omega) (by omega)] at h
      exact h.symm)
  have hwdPC : ∀ k : ℤ, 0 ≤ k → k ≤ m * f + a → hwd P k = hwd (ω.compose A) k := by
    intro k hk0 hk
    unfold hwd
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    rw [hYeq i hi.1 (by omega), hXeq i hi.1 (by omega)]
  refine ⟨A, hAc, hspA, ⟨v, hv⟩, ?_, ?_⟩
  · intro j hj0 hj
    have hjA : j < (span A : ℤ) := by rw [hspA]; exact hj
    have hpriv := hω.hwd_compose_private hf hAc hj0 hjA
    have hjf : j * f + f - 1 = (j + 1) * f - 1 := by ring
    have hjN : (j + 1) * f ≤ m * f := mul_le_mul_of_nonneg_right (by omega) hf0.le
    have hjf0 : 0 ≤ j * f := mul_nonneg hj0 hf0.le
    refine ⟨?_, ?_, hwd_pos hAc hj0 hjA⟩
    · rw [hwdPC _ (by omega) (by omega)]; exact hpriv.1.symm
    · rw [hwdPC _ (by omega) (by omega), hwdPC _ (by omega) (by omega), ← hjf]
      rw [hpriv.1]
      have := hpriv.2
      rw [show j * ω.period + ω.period - 1 = j * f + f - 1 from rfl] at this
      exact this.symm
  · intro A' hA' u' hu'
    have h1 : ω.compose A' = SkewGluing.translate (v - u') (ω.compose A) := by
      have := congrArg (SkewGluing.translate (-u')) (hu'.symm.trans hv)
      rw [SkewGluing.translate_translate, SkewGluing.translate_translate, neg_add_cancel,
        SkewGluing.translate_zero] at this
      rw [this]
      congr 1
      abel
    exact hω.injective_compose hAc hA' h1

end MarkedInner

end SkewGluing
namespace SkewGluing

namespace MarkedInner

theorem compose_singleton' (ω : MarkedInner) (d : ℤ × ℤ) :
    ω.compose {d} = SkewGluing.translate (ω.origin {d} d) ω.E := by
  have hne : ({d} : Diagram).Nonempty := Finset.singleton_nonempty d
  ext x
  rw [mem_compose hne]
  simp only [Finset.mem_singleton, exists_eq_left]
  constructor
  · rintro (h | ⟨⟨h, -⟩, -⟩)
    · exact h
    · exfalso
      have := congrArg Prod.fst (Finset.mem_singleton.mp h)
      simp at this
  · exact Or.inl

/-- A connected diagram of span one is a cell. -/
theorem eq_singleton_of_span_one {A : Diagram} (hA : IsConnectedSkew A) (h : span A = 1) :
    ∃ c, A = {c} := by
  have hc := card_eq_sum_height hA
  rw [h] at hc
  have hsp := span_eq_of_isConnectedSkew hA
  have hs := (isConnectedSkew_iff_diagonal.mp hA).2.2.2.2 _ (minContent_mem hA.2.1)
    (Or.inl (fun hm => by have := minContent_le hm; omega))
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, add_zero] at hc
  unfold height at hc
  exact Finset.card_eq_one.mp (by omega)

theorem decoder_sizes {ω : MarkedInner} (hω : ω.IsLegal) (hf : 2 ≤ ω.period) {A P : Diagram}
    (hA : IsConnectedSkew A) (hP : IsConnectedSkew P) {u : ℤ × ℤ}
    (hu : P = SkewGluing.translate u (ω.compose A))
    (hhw : ∀ j : ℤ, 0 ≤ j → j < (span A : ℤ) → hwd A j = hwd P (j * ω.period + ω.widthZ))
    (hm : 2 ≤ span A) :
    2 ≤ A.card ∧ 2 ≤ ω.E.card ∧ A.card < P.card ∧ ω.E.card < P.card := by
  have hn : 0 ≤ ω.widthZ ∧ ω.widthZ < ω.period := hω.2.2.1
  have hC := hω.isConnectedSkew_compose hA
  have hEc : IsConnectedSkew ω.E := hω.1.1
  have hspC : (span (ω.compose A) : ℤ) = span A * ω.period + ω.widthZ := by
    rw [span_compose hA hω]; rfl
  have hspP : (span P : ℤ) = span A * ω.period + ω.widthZ := by
    rw [hu, span_translate, hspC]
  have hcardP : P.card = (ω.compose A).card := by
    rw [hu]; exact Finset.card_image_of_injective _ (add_left_injective _)
  have hspE : (span ω.E : ℤ) = ω.period + ω.widthZ := hω.1.span_eq
  have spc : ∀ D : Diagram, span D ≤ D.card := fun D => Finset.card_image_le
  refine ⟨le_trans hm (spc A), ?_, ?_, ?_⟩
  · have := spc ω.E
    omega
  · -- the area of the outer is a sum of private heights
    obtain ⟨fn, hfn⟩ : ∃ fn : ℕ, (fn : ℤ) = ω.period :=
      ⟨ω.period.toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨an, han⟩ : ∃ an : ℕ, (an : ℤ) = ω.widthZ := ⟨ω.widthZ.toNat, Int.toNat_of_nonneg hn.1⟩
    have hcA := card_eq_sum_height hA
    have hcP := card_eq_sum_height hP
    have e1 : ∑ k ∈ Finset.range (span A), height A (minContent A + k) =
        ∑ k ∈ Finset.range (span A), hwd P (((k * fn + an : ℕ) : ℤ)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [← hwd_eq_height hA (by positivity) (by exact_mod_cast hk), hhw k (by positivity)
        (by exact_mod_cast hk)]
      push_cast
      rw [hfn, han]
    have e2 : ∑ k ∈ Finset.range (span P), height P (minContent P + k) =
        ∑ k ∈ Finset.range (span P), hwd P k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [← hwd_eq_height hP (by positivity) (by exact_mod_cast hk)]
    have hspPn : span P = span A * fn + an := by
      have : (span P : ℤ) = ((span A * fn + an : ℕ) : ℤ) := by push_cast; rw [hfn, han]; exact hspP
      exact_mod_cast this
    have hfn2 : 2 ≤ fn := by omega
    have hinj : Function.Injective (fun k : ℕ => k * fn + an) := by
      intro a b hab
      have hab' : a * fn + an = b * fn + an := hab
      have : a * fn = b * fn := by omega
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    have hsum : ∑ k ∈ Finset.range (span A), hwd P (((k * fn + an : ℕ) : ℤ)) =
        ∑ i ∈ (Finset.range (span A)).image (fun k : ℕ => k * fn + an), hwd P (i : ℤ) := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    have hsub : (Finset.range (span A)).image (fun k : ℕ => k * fn + an) ⊆
        Finset.range (span P) := by
      intro i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      rw [Finset.mem_range] at hk ⊢
      rw [hspPn]
      have : k * fn < span A * fn := Nat.mul_lt_mul_of_pos_right hk (by omega)
      omega
    have hi0 : an + 1 ∈ Finset.range (span P) := by
      rw [Finset.mem_range, hspPn]
      have : 2 * fn ≤ span A * fn := Nat.mul_le_mul_right fn hm
      omega
    have hi0' : an + 1 ∉ (Finset.range (span A)).image (fun k : ℕ => k * fn + an) := by
      intro h
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · omega
      · have : fn ≤ k * fn := Nat.le_mul_of_pos_left fn hk0
        omega
    have hlt : ∑ i ∈ (Finset.range (span A)).image (fun k : ℕ => k * fn + an), hwd P (i : ℤ) <
        ∑ i ∈ Finset.range (span P), hwd P (i : ℤ) := by
      refine Finset.sum_lt_sum_of_subset hsub hi0 hi0' ?_ ?_
      · exact hwd_pos hP (by positivity) (by
          have : an + 1 < span P := Finset.mem_range.mp hi0
          exact_mod_cast this)
      · intro j hj _
        exact (hwd_pos hP (by positivity) (by exact_mod_cast Finset.mem_range.mp hj)).le
    have : (A.card : ℤ) < P.card := by
      rw [hcA, hcP, e1, e2, hsum]; exact hlt
    exact_mod_cast this
  · -- two distinct copies of the inner lie in the composite
    have hAne : A.Nonempty := hA.2.1
    have hEne : ω.E.Nonempty := hEc.2.1
    have hspA : (2 : ℤ) ≤ span A := by exact_mod_cast hm
    have hsp := span_eq_of_isConnectedSkew hA
    have cp1 : SkewGluing.translate (ω.origin A (sw A)) ω.E ⊆ ω.compose A := by
      intro x hx
      rw [mem_compose hAne]
      exact Or.inl ⟨sw A, sw_mem hAne, hx⟩
    have cp2 : SkewGluing.translate (ω.origin A (ne A)) ω.E ⊆ ω.compose A := by
      intro x hx
      rw [mem_compose hAne]
      exact Or.inl ⟨ne A, ne_mem hAne, hx⟩
    have c1 : (SkewGluing.translate (ω.origin A (sw A)) ω.E).card = ω.E.card :=
      Finset.card_image_of_injective _ (add_left_injective _)
    have c2 : (SkewGluing.translate (ω.origin A (ne A)) ω.E).card = ω.E.card :=
      Finset.card_image_of_injective _ (add_left_injective _)
    have hne12 : SkewGluing.translate (ω.origin A (sw A)) ω.E ≠
        SkewGluing.translate (ω.origin A (ne A)) ω.E := by
      intro h
      have := congrArg minContent h
      rw [minContent_translate hEne, minContent_translate hEne, content_origin, content_origin,
        content_sw hAne, content_ne hAne] at this
      have h2 : (maxContent A - minContent A) * ω.period = 0 := by linarith
      have h3 : 0 < ω.period := by omega
      have : maxContent A - minContent A = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · omega
      omega
    by_contra hcon
    rw [not_lt] at hcon
    rw [hcardP] at hcon
    have e1 := Finset.eq_of_subset_of_card_le cp1 (by omega)
    have e2 := Finset.eq_of_subset_of_card_le cp2 (by omega)
    exact hne12 (e1.trans e2.symm)

end MarkedInner

end SkewGluing
namespace SkewGluing

namespace MarkedInner

/-- **`ge:decoder`.**  Let `(ω, s, t)` be a full legal marked inner of period `f ≥ 2` with its
phases, and let `P` be a connected diagram of span `m f + a`, `m ≥ 1`, such that in each closed
boundary word every nonvariable slot agrees with the native word of `ω.E` (`natPos` is the position
of the inner word read at a given position; the variable slots are the residues `holesA`, `holesB`
of the table `ge:eq:ports`).  No condition is imposed on the variable slots.  Then there is a
connected outer `A` of span `m`, unique up to translation, with `P` a translate of `A ∘_ω E`.
Its heights are the private heights `h_A(j) = h_P(j f + a) = h_P((j + 1) f - 1) > 0`.  If `m ≥ 2`,
both factors have at least two cells and strictly smaller occupied area than `P`; if `m = 1`, `A`
is a cell and `P` is a translate of `E`. -/
theorem decoder {ω : MarkedInner} (hω : ω.IsLegal) (hf : 2 ≤ ω.period) {s t : ℤ}
    (hph : ω.HasPhases s t) {P : Diagram} (hP : IsConnectedSkew P) {m : ℕ} (hm : 1 ≤ m)
    (hN : (span P : ℤ) = m * ω.period + ω.widthZ)
    (hnat : ∀ k : ℤ, 0 ≤ k → k ≤ (span P : ℤ) →
      (k % ω.period ∉ holesB ω.case s t →
        Xw P k = Xw ω.E (natPos ω.period m k)) ∧
      (k % ω.period ∉ holesA ω.case s t →
        Yw P k = Yw ω.E (natPos ω.period m k))) :
    ∃ A : Diagram, IsConnectedSkew A ∧ span A = m ∧
      (∃ u, P = SkewGluing.translate u (ω.compose A)) ∧
      (∀ A' : Diagram, IsConnectedSkew A' → ∀ u', P = SkewGluing.translate u' (ω.compose A') →
        ∃ w, A' = SkewGluing.translate w A) ∧
      (∀ j : ℤ, 0 ≤ j → j < m →
        hwd A j = hwd P (j * ω.period + ω.widthZ) ∧
        hwd P (j * ω.period + ω.widthZ) = hwd P ((j + 1) * ω.period - 1) ∧ 0 < hwd A j) ∧
      (2 ≤ m → 2 ≤ A.card ∧ 2 ≤ ω.E.card ∧ A.card < P.card ∧ ω.E.card < P.card) ∧
      (m = 1 → (∃ c, A = {c}) ∧ ∃ u, P = SkewGluing.translate u ω.E) := by
  obtain ⟨A, hA, hspA, ⟨u, hu⟩, hsamp, huniq⟩ := decoder_exists hω hf hph hP hm hN hnat
  refine ⟨A, hA, hspA, ⟨u, hu⟩, huniq, hsamp, fun h2 => ?_, fun h1 => ?_⟩
  · exact decoder_sizes hω hf hA hP hu
      (fun j hj hj' => (hsamp j hj (by rw [hspA] at hj'; exact hj')).1) (by omega)
  · obtain ⟨c, hc⟩ := eq_singleton_of_span_one hA (by omega)
    refine ⟨⟨c, hc⟩, u + ω.origin {c} c, ?_⟩
    rw [hu, hc, compose_singleton', SkewGluing.translate_translate]

/-- Every legal marked inner has phases. -/
theorem exists_hasPhases' {ω : MarkedInner} (hω : ω.IsLegal) : ∃ s t, ω.HasPhases s t :=
  IsLegal.exists_hasPhases hω

/-- **`ge:remark:cut`.**  The nonvariable-slot hypothesis of `ge:decoder` may be verified on two
position ranges that cover the closed words, one at a time; the conclusion is the same
reconstruction of `P`. -/
theorem decoder_of_cut_windows {ω : MarkedInner} (hω : ω.IsLegal) (hf : 2 ≤ ω.period) {s t : ℤ}
    (hph : ω.HasPhases s t) {P : Diagram} (hP : IsConnectedSkew P) {m : ℕ} (hm : 1 ≤ m)
    (hN : (span P : ℤ) = m * ω.period + ω.widthZ) (c : ℤ)
    (hfirst : ∀ k : ℤ, 0 ≤ k → k ≤ c →
      (k % ω.period ∉ holesB ω.case s t →
        Xw P k = Xw ω.E (natPos ω.period m k)) ∧
      (k % ω.period ∉ holesA ω.case s t →
        Yw P k = Yw ω.E (natPos ω.period m k)))
    (hlast : ∀ k : ℤ, c ≤ k → k ≤ (span P : ℤ) →
      (k % ω.period ∉ holesB ω.case s t →
        Xw P k = Xw ω.E (natPos ω.period m k)) ∧
      (k % ω.period ∉ holesA ω.case s t →
        Yw P k = Yw ω.E (natPos ω.period m k))) :
    ∃ A : Diagram, IsConnectedSkew A ∧ span A = m ∧
      ∃ u, P = SkewGluing.translate u (ω.compose A) := by
  obtain ⟨A, hA, hspA, hu, -⟩ := decoder hω hf hph hP hm hN (fun k hk0 hk => by
    by_cases hkc : k ≤ c
    · exact hfirst k hk0 hkc
    · exact hlast k (by omega) hk)
  exact ⟨A, hA, hspA, hu⟩

end MarkedInner

end SkewGluing
