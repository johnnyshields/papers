import SkewGluing.Coding
import SkewGluing.CommonFactorGraph
import SkewGluing.MixedPairs.Classes

/-!
# The boundary coding of a proper chart, as data on words

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts» and
«Diagonal geometry» (`lem:gluing-coding`: `eq:gluing-holes`, `eq:gluing-caps`).

`MixFoldCoding A B N q w case s t` collects, for two bit words `A, B` of a parent of span `N`, the
statements of `lem:gluing-coding` that the arguments on pairs of charts use: the period `q` except
at the residues of `eq:gluing-holes` (for the empty mark, the residue zero), the end bits
`eq:gluing-caps` of the case, the private bits `B_w = 1`, `B_q = 0` of case (d), and the
private singleton `H_{q-1} = 1`.  `Chart.IsProperLegal.mixFoldCoding` proves that every proper
legal chart of `F` has such a coding on the words of `F`; the words of a translate of the parent
are the same (`wordA_translate`).

Sorry-free.
-/

namespace SkewGluing

/-- The exceptional residues of `A` read off a chart of width `w`: the residue zero for the empty
mark and the table `eq:gluing-holes` otherwise. -/
def codingHolesA (x : AttachCase) (w : ℕ) (s t : ℤ) : Finset ℤ :=
  if w = 0 then {0} else holesA x s t

/-- The exceptional residues of `B` read off a chart of width `w`. -/
def codingHolesB (x : AttachCase) (w : ℕ) (s t : ℤ) : Finset ℤ :=
  if w = 0 then {0} else holesB x s t

/-- The boundary coding of a proper legal chart on the bit words `A, B` of its parent of span `N`:
period `q`, width `w`, attachment case `case`, middle phases `s, t`. -/
structure MixFoldCoding (A B : ℤ → ℤ) (N q w : ℕ) (case : AttachCase) (s t : ℤ) : Prop where
  q_pos : 0 < q
  w_lt : w < q
  span_eq : ∃ r : ℕ, 2 ≤ r ∧ N = r * q + w
  empty : w = 0 → case = .a
  phases : 0 < w → 1 ≤ s ∧ s ≤ (w : ℤ) ∧ 0 ≤ t ∧ t < (w : ℤ) ∧ (case.IsMixed → t < s)
  perA : PeriodWords.PeriodExcept (N - 1) q (codingHolesA case w s t) A
  perB : PeriodWords.PeriodExcept (N - 1) q (codingHolesB case w s t) B
  caps_a : 0 < w → case = .a → (1 ≤ t → A t = 1) ∧ B s = 0 ∧ A ((N : ℤ) - w + t) = 0 ∧
    (s < (w : ℤ) → B ((N : ℤ) - w + s) = 1)
  caps_b : 0 < w → case = .b → (1 ≤ t → B t = 0) ∧ A s = 1 ∧ B ((N : ℤ) - w + t) = 1 ∧
    (s < (w : ℤ) → A ((N : ℤ) - w + s) = 0)
  caps_c : 0 < w → case = .c → (1 ≤ t → B t = 0) ∧ B s = 0 ∧ B ((N : ℤ) - w + t) = 1 ∧
    (s < (w : ℤ) → B ((N : ℤ) - w + s) = 1) ∧ A ((N : ℤ) - w) = 1 ∧ A ((N : ℤ) - q) = 0
  caps_d : 0 < w → case = .d → (1 ≤ t → A t = 1) ∧ A s = 1 ∧ A ((N : ℤ) - w + t) = 0 ∧
    (s < (w : ℤ) → A ((N : ℤ) - w + s) = 0) ∧ B (w : ℤ) = 1 ∧ B (q : ℤ) = 0
  single_d : 0 < w → case = .d → mixFold_ht A B (q - 1) = 1

/-- The height word of the bit words of a connected skew diagram is its height sequence:
`H_n = height X (c₀ + n)`. -/
theorem mixFold_ht_eq_height {X : Diagram} (hX : IsConnectedSkew X) {n : ℕ} (hn : n < span X) :
    mixFold_ht (wordA X) (wordB X) n = height X (minContent X + n) := by
  have hsing : diagLo X (minContent X) = diagHi X (minContent X) :=
    MarkedInner.D_ends hX |>.1
  induction n with
  | zero => simp [mixFold_ht_zero, height, hsing]
  | succ n ih =>
    rw [mixFold_ht_succ, ih (by omega)]
    simp only [wordA, wordB, bitA, bitB, height]
    have e : minContent X + ((n + 1 : ℕ) : ℤ) - 1 = minContent X + n := by push_cast; ring
    have e' : minContent X + (((n : ℤ) + 1 : ℤ)) - 1 = minContent X + n := by ring
    have e'' : minContent X + ((n : ℤ) + 1) = minContent X + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e', e'']
    ring

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem IsLegalNonempty.mixFold_single_d (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hcd : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t) :
    mixFold_ht (wordA (ω.compose D)) (wordB (ω.compose D)) (ω.period.toNat - 1) = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hlt := h.phases_lt (Or.inr hcd) hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hmin := h.minContent_compose' hD
  have hN := h.span_compose_eq hD
  have hqz : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg (by omega)
  have hn : ω.period.toNat - 1 < span (ω.compose D) := by
    have := mul_le_mul_of_nonneg_right (show 1 ≤ maxContent D - minContent D + 1 by omega)
      (show 0 ≤ ω.period by omega)
    omega
  rw [mixFold_ht_eq_height (h.1.isConnectedSkew_compose hD) hn]
  have hp : ((ω.period.toNat - 1 : ℕ) : ℤ) = ω.period - 1 := by omega
  have e : minContent (ω.compose D) + ((ω.period.toNat - 1 : ℕ) : ℤ) =
      minContent ω.E + (minContent D * ω.period + (ω.period - 1)) := by
    rw [hmin, hp]; ring
  rw [e]
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D) (ω.period - 1) :=
    Or.inl ⟨le_refl _, hmM⟩
  have hprof := (h.mixed_profile hD hcd hph hlt (by omega) (by omega) hv).2.1 (by omega)
  rw [hprof]
  have hs1 := h.lo_pred_period_eq_hi
  have hse := (MarkedInner.D_ends hD).1
  unfold height profM
  simp only [hmM, le_refl, and_self, ite_true]
  rw [hse]
  unfold SkewGluing.MarkedInner.hi SkewGluing.MarkedInner.lo at *
  omega

end MarkedInner

/-- **`lem:gluing-coding`, as word data, for given middle phases.**  A proper legal chart with a
nonempty mark and middle phases `s, t` has the boundary coding with those phases on the bit words
of its parent. -/
theorem Chart.IsProperLegal.mixFoldCoding_nonempty {χ : Chart} (h : χ.IsProperLegal)
    (hW : χ.ω.W.Nonempty) {s t : ℤ} (hph : χ.ω.IsPhases s t) :
    MixFoldCoding (wordA χ.parent) (wordB χ.parent) (span χ.parent)
      χ.ω.period.toNat χ.ω.width χ.ω.case s t := by
  obtain ⟨hD, hc, hE, hω⟩ := h
  have hq := hω.period_pos
  have hwq := hω.2.2.1.2
  have hqz : ((χ.ω.period.toNat : ℕ) : ℤ) = χ.ω.period := Int.toNat_of_nonneg (by omega)
  have hspan := MarkedInner.span_compose hD hω
  have hD2 := two_le_span_of_two_le_card hD hc
  have hr : ∃ r : ℕ, 2 ≤ r ∧ span χ.parent = r * χ.ω.period.toNat + χ.ω.width := by
    refine ⟨span χ.D, hD2, ?_⟩
    have : (span χ.parent : ℤ) = (span χ.D * χ.ω.period.toNat + χ.ω.width : ℕ) := by
      push_cast; rw [hqz]; exact hspan
    exact_mod_cast this
  have hwqn : χ.ω.width < χ.ω.period.toNat := by omega
  have hl : χ.ω.IsLegalNonempty := ⟨hω, hW⟩
  have hw1 := hl.width_pos
  have hw1' : 0 < χ.ω.width := by unfold MarkedInner.widthZ at hw1; omega
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  obtain ⟨hA, hB⟩ := hl.gluing_coding_periodic hD hph
  have hwz : (χ.ω.width : ℤ) = χ.ω.widthZ := rfl
  refine ⟨by omega, hwqn, hr, fun h0 => by omega, fun _ => ⟨hs1, hs2, ht1, ht2,
    fun hm => hl.phases_lt hm hph⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [codingHolesA, hw1'.ne', Chart.parent] using hA
  · simpa [codingHolesB, hw1'.ne', Chart.parent] using hB
  · intro _ hca
    have := hl.caps_a hD hca hph
    rw [← hwz] at this
    exact this
  · intro _ hcb
    have := hl.caps_b hD hcb hph
    rw [← hwz] at this
    exact this
  · intro _ hcc
    have := hl.caps_c hD hcc hph
    rw [← hwz] at this
    rw [hqz]
    exact this
  · intro _ hcd
    have := hl.caps_d hD hcd hph
    rw [← hwz] at this
    rw [hqz]
    exact this
  · intro _ hcd
    exact hl.mixFold_single_d hD hcd hph

/-- **`lem:gluing-coding`, as word data.**  Every proper legal chart has a boundary coding on the
bit words of its parent. -/
theorem Chart.IsProperLegal.mixFoldCoding {χ : Chart} (h : χ.IsProperLegal) :
    ∃ s t : ℤ, MixFoldCoding (wordA χ.parent) (wordB χ.parent) (span χ.parent)
      χ.ω.period.toNat χ.ω.width χ.ω.case s t := by
  by_cases hW : χ.ω.W = ∅
  · obtain ⟨hD, hc, hE, hω⟩ := h
    have hq := hω.period_pos
    have hwq := hω.2.2.1.2
    have hqz : ((χ.ω.period.toNat : ℕ) : ℤ) = χ.ω.period := Int.toNat_of_nonneg (by omega)
    have hspan := MarkedInner.span_compose hD hω
    have hD2 := two_le_span_of_two_le_card hD hc
    have hr : ∃ r : ℕ, 2 ≤ r ∧ span χ.parent = r * χ.ω.period.toNat + χ.ω.width := by
      refine ⟨span χ.D, hD2, ?_⟩
      have : (span χ.parent : ℤ) = (span χ.D * χ.ω.period.toNat + χ.ω.width : ℕ) := by
        push_cast; rw [hqz]; exact hspan
      exact_mod_cast this
    have hwqn : χ.ω.width < χ.ω.period.toNat := by omega
    have hle : χ.ω.IsLegalEmpty := ⟨hω, hW⟩
    have hw0 := MarkedInner.width_eq_zero_of_eq_empty hW
    obtain ⟨hA, hB⟩ := hle.periodExcept hD
    refine ⟨0, 0, ⟨by omega, hwqn, hr, fun _ => hle.case_a, fun h0 => by omega, ?_, ?_,
      fun h0 => by omega, fun h0 => by omega, fun h0 => by omega, fun h0 => by omega,
      fun h0 => by omega⟩⟩
    · simpa [codingHolesA, hw0, Chart.parent] using hA
    · simpa [codingHolesB, hw0, Chart.parent] using hB
  · have hWn : χ.ω.W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hW
    obtain ⟨s, t, hph⟩ := (show χ.ω.IsLegalNonempty from ⟨h.2.2.2, hWn⟩).exists_phases
    exact ⟨s, t, h.mixFoldCoding_nonempty hWn hph⟩

theorem MixFoldCoding.two_q_add_w_le {A B : ℤ → ℤ} {N q w : ℕ} {case : AttachCase} {s t : ℤ}
    (h : MixFoldCoding A B N q w case s t) : 2 * q + w ≤ N := by
  obtain ⟨r, hr, hN⟩ := h.span_eq
  have := Nat.mul_le_mul_right q hr
  omega

theorem mixFold_ht_congr {A B A' B' : ℤ → ℤ} {n : ℕ}
    (h : ∀ k : ℤ, 1 ≤ k → k ≤ n → A k = A' k ∧ B k = B' k) :
    mixFold_ht A B n = mixFold_ht A' B' n := by
  induction n with
  | zero => simp [mixFold_ht_zero]
  | succ n ih =>
    rw [mixFold_ht_succ, mixFold_ht_succ, ih (fun k hk1 hk2 => h k hk1 (by push_cast; omega))]
    have := h ((n : ℤ) + 1) (by omega) (by push_cast; omega)
    rw [this.1, this.2]

/-- The coding of a chart depends only on the words at the positions `1, …, N - 1`. -/
theorem MixFoldCoding.of_agree {A B A' B' : ℤ → ℤ} {N q w : ℕ} {case : AttachCase} {s t : ℤ}
    (h : MixFoldCoding A B N q w case s t) (hA : ∀ k : ℤ, 1 ≤ k → k ≤ (N : ℤ) - 1 → A k = A' k)
    (hB : ∀ k : ℤ, 1 ≤ k → k ≤ (N : ℤ) - 1 → B k = B' k) : MixFoldCoding A' B' N q w case s t := by
  have hN2 := h.two_q_add_w_le
  have hq := h.q_pos
  have hwq := h.w_lt
  obtain ⟨r, hr, hNr⟩ := h.span_eq
  refine ⟨hq, hwq, h.span_eq, h.empty, h.phases, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hS
    rw [Finset.mem_Icc] at hx
    have := h.perA x (by rw [Finset.mem_Icc]; omega) hS
    rw [← hA x (by omega) (by omega), ← hA (x + q) (by omega) (by omega)]
    exact this
  · intro x hx hS
    rw [Finset.mem_Icc] at hx
    have := h.perB x (by rw [Finset.mem_Icc]; omega) hS
    rw [← hB x (by omega) (by omega), ← hB (x + q) (by omega) (by omega)]
    exact this
  · intro hw hc
    obtain ⟨hs1, hs2, ht1, ht2, -⟩ := h.phases hw
    obtain ⟨c1, c2, c3, c4⟩ := h.caps_a hw hc
    refine ⟨fun h1 => ?_, ?_, ?_, fun h1 => ?_⟩
    · rw [← hA t (by omega) (by omega)]; exact c1 h1
    · rw [← hB s (by omega) (by omega)]; exact c2
    · rw [← hA _ (by omega) (by omega)]; exact c3
    · rw [← hB _ (by omega) (by omega)]; exact c4 h1
  · intro hw hc
    obtain ⟨hs1, hs2, ht1, ht2, -⟩ := h.phases hw
    obtain ⟨c1, c2, c3, c4⟩ := h.caps_b hw hc
    refine ⟨fun h1 => ?_, ?_, ?_, fun h1 => ?_⟩
    · rw [← hB t (by omega) (by omega)]; exact c1 h1
    · rw [← hA s (by omega) (by omega)]; exact c2
    · rw [← hB _ (by omega) (by omega)]; exact c3
    · rw [← hA _ (by omega) (by omega)]; exact c4 h1
  · intro hw hc
    obtain ⟨hs1, hs2, ht1, ht2, -⟩ := h.phases hw
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h.caps_c hw hc
    refine ⟨fun h1 => ?_, ?_, ?_, fun h1 => ?_, ?_, ?_⟩
    · rw [← hB t (by omega) (by omega)]; exact c1 h1
    · rw [← hB s (by omega) (by omega)]; exact c2
    · rw [← hB _ (by omega) (by omega)]; exact c3
    · rw [← hB _ (by omega) (by omega)]; exact c4 h1
    · rw [← hA _ (by omega) (by omega)]; exact c5
    · rw [← hA _ (by omega) (by omega)]; exact c6
  · intro hw hc
    obtain ⟨hs1, hs2, ht1, ht2, -⟩ := h.phases hw
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h.caps_d hw hc
    refine ⟨fun h1 => ?_, ?_, ?_, fun h1 => ?_, ?_, ?_⟩
    · rw [← hA t (by omega) (by omega)]; exact c1 h1
    · rw [← hA s (by omega) (by omega)]; exact c2
    · rw [← hA _ (by omega) (by omega)]; exact c3
    · rw [← hA _ (by omega) (by omega)]; exact c4 h1
    · rw [← hB _ (by omega) (by omega)]; exact c5
    · rw [← hB _ (by omega) (by omega)]; exact c6
  · intro hw hc
    calc mixFold_ht A' B' (q - 1) = mixFold_ht A B (q - 1) :=
          (mixFold_ht_congr (n := q - 1) (fun k hk1 hk2 => ⟨hA k hk1 (by omega),
            hB k hk1 (by omega)⟩)).symm
      _ = 1 := h.single_d hw hc

end SkewGluing
