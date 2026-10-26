import SkewGluing.Decoder.Defs
import SkewGluing.Lines.FirstWindow
import SkewGluing.Local

/-!
# The nonvariable positions of a composite repeat the native word

Formalizes `shields-2026-skew-gluing.tex`, «Reconstructing a chart from its two words»
(`ge:eq:ports`: "every other word position repeats its native `K`-value").

For a legal marked inner `ω` of period `f` and width `a`, and a connected outer of span `m`, the
closed words of `D ∘_ω E` at a position whose residue modulo `f` is not a variable slot equal the
closed words of `E` at the native position `natPos f m k`.  The first `f - 1` positions are the
first window, the last positions beyond `(m - 1) f + a` are the last window, and every other
nonvariable position is reached from one of them along the periodicity of the words except at the
variable residues.

Sorry-free.
-/

namespace SkewGluing

/-- Floor division by a positive integer is pinned by the two bounds. -/
theorem ediv_eq_of_bounds {f x q : ℤ} (hf : 0 < f) (h1 : q * f ≤ x) (h2 : x < (q + 1) * f) :
    x / f = q := by
  have := (Int.ediv_emod_unique hf (a := x) (b := f) (q := q) (r := x - q * f)).mpr
    ⟨by ring, by omega, by nlinarith⟩
  exact this.1

/-- Moving a position up by whole periods along a word that is periodic off the residues `S`. -/
theorem chain_up (word : ℤ → ℤ) {f N : ℤ} {S : Finset ℤ} (hf0 : 0 ≤ f)
    (hper : ∀ x, 1 ≤ x → x + f ≤ N - 1 → x % f ∉ S → word x = word (x + f)) :
    ∀ j : ℕ, ∀ x, 1 ≤ x → x % f ∉ S → x + j * f ≤ N - 1 → word (x + j * f) = word x := by
  intro j
  induction j with
  | zero => intro x _ _ _; simp
  | succ j ih =>
    intro x hx hS hN
    have e : x + ((j + 1 : ℕ) : ℤ) * f = (x + j * f) + f := by push_cast; ring
    have hmod : (x + j * f) % f = x % f := Int.add_mul_emod_self_right x (j : ℤ) f
    have hj : (0 : ℤ) ≤ j := by positivity
    have hjf : 0 ≤ (j : ℤ) * f := by positivity
    rw [e, ← hper (x + j * f) (by omega) (by rw [← e]; exact hN) (by rw [hmod]; exact hS)]
    exact ih x hx hS (by rw [e] at hN; omega)

/-- The nonvariable positions of a word, in integer form; the native position lies strictly
inside the span `f + a` of the inner. -/
theorem native_gen (word_C word_E : ℤ → ℤ) {f a m N : ℤ} {S : Finset ℤ} (hf : 2 ≤ f)
    (ha0 : 0 ≤ a) (haf : a < f) (hN : N = m * f + a) (h0 : 0 ∉ S → 1 ≤ a)
    (hper : ∀ x, 1 ≤ x → x + f ≤ N - 1 → x % f ∉ S → word_C x = word_C (x + f))
    (hfirst : ∀ k, 1 ≤ k → k ≤ f - 1 → word_C k = word_E k)
    (hlast : ∀ k, (m - 1) * f + a + 1 ≤ k → k ≤ N - 1 → word_C k = word_E (k - (m - 1) * f))
    {k : ℤ} (hk1 : 1 ≤ k) (hk2 : k ≤ N - 1) (hS : k % f ∉ S) :
    word_C k = word_E (natPos f m k) ∧ 1 ≤ natPos f m k ∧ natPos f m k < f + a := by
  have hf0 : 0 < f := by omega
  have hmf : (m - 1) * f = m * f - f := by ring
  by_cases hl : (m - 1) * f + a + 1 ≤ k
  · have h1 : (m - 1) ≤ (k - 1) / f := by
      rw [Int.le_ediv_iff_mul_le hf0]; omega
    have hn : natPos f m k = k - (m - 1) * f := by
      unfold natPos
      simp only [show ¬ (k ≤ 0) by omega, ↓reduceIte]
      rw [min_eq_right h1]
      ring
    rw [hn]
    exact ⟨hlast k hl hk2, by omega, by omega⟩
  · push Not at hl
    by_cases hr : k % f = 0
    · have ha1 : 1 ≤ a := h0 (by rw [← hr]; exact hS)
      obtain ⟨j, hj⟩ : ∃ j, k = j * f := ⟨k / f, by
        have := Int.mul_ediv_add_emod k f
        rw [hr] at this; linarith⟩
      have hj1 : 1 ≤ j := by
        by_contra hc
        push Not at hc
        nlinarith
      have hjm : j + 1 ≤ m := by
        by_contra hc
        push Not at hc
        have : m * f ≤ j * f := by nlinarith
        nlinarith
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m - j := ⟨(m - j).toNat, by omega⟩
      have hup := chain_up word_C hf0.le hper n k hk1 hS (by rw [hj]; nlinarith)
      have e : k + (n : ℤ) * f = m * f := by rw [hn, hj]; ring
      rw [e] at hup
      have hd : (k - 1) / f = j - 1 :=
        ediv_eq_of_bounds hf0 (by rw [hj]; nlinarith) (by rw [hj]; nlinarith)
      have hnat : natPos f m k = f := by
        unfold natPos
        simp only [show ¬ (k ≤ 0) by omega, ↓reduceIte]
        rw [hd, min_eq_left (by omega), hj]
        ring
      rw [hnat]
      refine ⟨?_, by omega, by omega⟩
      rw [← hup, hlast (m * f) (by nlinarith) (by nlinarith)]
      congr 1
      ring
    · have hrpos : 1 ≤ k % f := by
        have := Int.emod_nonneg k hf0.ne'
        omega
      have hrlt : k % f < f := Int.emod_lt_of_pos k hf0
      obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = k / f := ⟨(k / f).toNat, by
        have := Int.ediv_nonneg (show 0 ≤ k by omega) hf0.le
        omega⟩
      have hkd : k = k % f + (j : ℤ) * f := by
        rw [hj]; have := Int.mul_ediv_add_emod k f; linarith
      have hup := chain_up word_C hf0.le hper j (k % f) hrpos
        (by rw [Int.emod_emod_of_dvd _ dvd_rfl]; exact hS) (by rw [← hkd]; exact hk2)
      rw [← hkd] at hup
      have hd : (k - 1) / f = j :=
        ediv_eq_of_bounds hf0 (by rw [hj]; nlinarith) (by rw [hj]; nlinarith)
      have hjm : (j : ℤ) ≤ m - 1 := by
        by_contra hc
        push Not at hc
        have : m * f ≤ j * f := by nlinarith
        nlinarith
      have hnat : natPos f m k = k % f := by
        unfold natPos
        simp only [show ¬ (k ≤ 0) by omega, ↓reduceIte]
        rw [hd, min_eq_left hjm]
        linarith [mul_comm f (j : ℤ)]
      rw [hnat]
      exact ⟨by rw [hup, hfirst _ hrpos (by omega)], hrpos, by omega⟩

/-- A window at the top: if `Y` and `X` agree up to the translation `o` on the contents `≥ c`, then
their diagonals agree there. -/
theorem diag_of_window_last {X Y : Diagram} {o : ℤ × ℤ} {c : ℤ}
    (h : ∀ y : ℤ × ℤ, c ≤ content y → (y ∈ Y ↔ y - o ∈ X)) {k : ℤ} (hk : c ≤ k)
    (hkX : k - content o ∈ contents X) :
    diagLo Y k = diagLo X (k - content o) + o.1 ∧ diagHi Y k = diagHi X (k - content o) + o.1 := by
  have hc : content o = o.2 - o.1 := rfl
  have key : ∀ i : ℤ, (i, i + k) ∈ Y ↔ (i - o.1, (i - o.1) + (k - content o)) ∈ X := by
    intro i
    have e : ((i, i + k) : ℤ × ℤ) - o = (i - o.1, (i - o.1) + (k - content o)) := by
      ext
      · simp
      · simp only [Prod.snd_sub]; omega
    rw [← e]
    exact h _ (by simp only [content]; omega)
  constructor
  · apply diagLo_eq_of
    · rw [key]
      have := diagLo_mem hkX
      convert this using 2 <;> ring
    · intro i hi
      have := diagLo_le (D := X) (k := k - content o) ((key i).mp hi) (by ring)
      omega
  · apply diagHi_eq_of
    · rw [key]
      have := diagHi_mem hkX
      convert this using 2 <;> ring
    · intro i hi
      have := le_diagHi (D := X) (k := k - content o) ((key i).mp hi) (by ring)
      omega

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- The boundary words of the composite on the last window are those of the inner, shifted by
`(m - 1) f`. -/
theorem IsLegal.words_compose_last (hω : ω.IsLegal) (hD : IsConnectedSkew D) {k : ℤ}
    (hk1 : ((span D : ℤ) - 1) * ω.period + ω.width + 1 ≤ k)
    (hk2 : k ≤ (span (ω.compose D) : ℤ) - 1) :
    wordA (ω.compose D) k = wordA ω.E (k - ((span D : ℤ) - 1) * ω.period) ∧
    wordB (ω.compose D) k = wordB ω.E (k - ((span D : ℤ) - 1) * ω.period) := by
  have hq := hω.period_pos
  have hDne := hD.2.1
  have hsD := span_eq_of_isConnectedSkew hD
  have hmin := hω.minContent_compose hD
  have hN := span_compose hD hω
  have hcE := hω.1.contents_eq
  have hw : (0 : ℤ) ≤ ω.width := by positivity
  have hco : content (ω.origin D (ne D)) = maxContent D * ω.period := by
    rw [content_origin, content_ne hDne]
  have win := fun y (hy : minContent ω.E + maxContent D * ω.period + ω.width ≤ content y) =>
    hω.mem_compose_last hD hy
  have m1 : minContent (ω.compose D) + (k - 1) - content (ω.origin D (ne D)) ∈ contents ω.E := by
    rw [hco, hcE, Finset.mem_Icc, hmin]
    constructor <;> nlinarith
  have m2 : minContent (ω.compose D) + k - content (ω.origin D (ne D)) ∈ contents ω.E := by
    rw [hco, hcE, Finset.mem_Icc, hmin]
    constructor <;> nlinarith
  have d1 := diag_of_window_last win (k := minContent (ω.compose D) + (k - 1))
    (by rw [hmin]; nlinarith) m1
  have d2 := diag_of_window_last win (k := minContent (ω.compose D) + k)
    (by rw [hmin]; nlinarith) m2
  have e1 : minContent (ω.compose D) + (k - 1) - content (ω.origin D (ne D)) =
      minContent ω.E + (k - ((span D : ℤ) - 1) * ω.period) - 1 := by
    rw [hco, hmin]; nlinarith
  have e2 : minContent (ω.compose D) + k - content (ω.origin D (ne D)) =
      minContent ω.E + (k - ((span D : ℤ) - 1) * ω.period) := by
    rw [hco, hmin]; nlinarith
  have e3 : minContent (ω.compose D) + k - 1 = minContent (ω.compose D) + (k - 1) := by ring
  rw [e1] at d1
  rw [e2] at d2
  unfold wordA wordB bitA bitB
  rw [e3, d1.1, d2.1, d1.2, d2.2]
  constructor <;> ring

/-- Both words of the composite have period `f` except at the variable residues. -/
theorem IsLegal.periodExcept_both (hω : ω.IsLegal) {s t : ℤ} (hph : ω.HasPhases s t)
    (hD : IsConnectedSkew D) :
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat (holesA ω.case s t)
      (wordA (ω.compose D)) ∧
    PeriodWords.PeriodExcept (span (ω.compose D) - 1) ω.period.toNat (holesB ω.case s t)
      (wordB (ω.compose D)) := by
  rcases hph with ⟨hW, rfl, rfl⟩ | ⟨hW, hp⟩
  · have h : ω.IsLegalEmpty := ⟨hω, hW⟩
    have hc := h.case_a
    have := h.periodExcept hD
    rw [hc]
    simpa [holesA, holesB] using this
  · exact (IsLegalNonempty.gluing_coding_periodic ⟨hω, hW⟩ hD hp)

/-- **The nonvariable positions repeat the native word** (`ge:eq:ports`).  For a legal marked
inner `ω` with phases `(s, t)` and a connected outer `A` of span `m`, the closed words of
`A ∘_ω E` at a position whose residue modulo the period is not a variable slot equal the closed
words of `E` at the native position `natPos f m k`. -/
theorem IsLegal.compose_native (hω : ω.IsLegal) {s t : ℤ} (hph : ω.HasPhases s t)
    (hf : 2 ≤ ω.period) {A : Diagram} (hA : IsConnectedSkew A) :
    ∀ k : ℤ, 0 ≤ k → k ≤ (span (ω.compose A) : ℤ) →
      (k % ω.period ∉ holesB ω.case s t →
        Xw (ω.compose A) k = Xw ω.E (natPos ω.period (span A) k)) ∧
      (k % ω.period ∉ holesA ω.case s t →
        Yw (ω.compose A) k = Yw ω.E (natPos ω.period (span A) k)) := by
  intro k hk0 hkN
  have hnar := hω.2.2.1
  unfold IsNarrow at hnar
  have hspA := span_pos hA
  have hN := span_compose hA hω
  have hspE : (span ω.E : ℤ) = ω.period + ω.width := hω.1.span_eq
  have hEc : IsConnectedSkew ω.E := hω.1.1
  have hCc := hω.isConnectedSkew_compose hA
  have hspE1 := span_pos hEc
  have hspC1 := span_pos hCc
  have hf0 : 0 < ω.period := by omega
  have hA0 : 0 ∉ holesA ω.case s t → 1 ≤ (ω.width : ℤ) := by
    intro h0
    rcases hph with ⟨hW, rfl, rfl⟩ | ⟨hW, hp⟩
    · have := (show ω.IsLegalEmpty from ⟨hω, hW⟩).case_a
      simp [holesA, this] at h0
    · exact (show ω.IsLegalNonempty from ⟨hω, hW⟩).width_pos
  have hB0 : 0 ∉ holesB ω.case s t → 1 ≤ (ω.width : ℤ) := by
    intro h0
    rcases hph with ⟨hW, rfl, rfl⟩ | ⟨hW, hp⟩
    · have := (show ω.IsLegalEmpty from ⟨hω, hW⟩).case_a
      simp [holesB, this] at h0
    · exact (show ω.IsLegalNonempty from ⟨hω, hW⟩).width_pos
  obtain ⟨pA, pB⟩ := hω.periodExcept_both hph hA
  have hL : (((span (ω.compose A) - 1 : ℕ)) : ℤ) = (span (ω.compose A) : ℤ) - 1 := by omega
  have hp : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg hf0.le
  have perA : ∀ x, 1 ≤ x → x + ω.period ≤ (span (ω.compose A) : ℤ) - 1 →
      x % ω.period ∉ holesA ω.case s t →
      wordA (ω.compose A) x = wordA (ω.compose A) (x + ω.period) := by
    intro x h1 h2 h3
    have hx : x ∈ Finset.Icc (1 : ℤ) (((span (ω.compose A) - 1 : ℕ) : ℤ) -
        ((ω.period.toNat : ℕ) : ℤ)) := by
      rw [Finset.mem_Icc, hL, hp]; omega
    have h3' : x % ((ω.period.toNat : ℕ) : ℤ) ∉ holesA ω.case s t := by
      rw [hp]; exact h3
    have := pA x hx h3'
    rwa [hp] at this
  have perB : ∀ x, 1 ≤ x → x + ω.period ≤ (span (ω.compose A) : ℤ) - 1 →
      x % ω.period ∉ holesB ω.case s t →
      wordB (ω.compose A) x = wordB (ω.compose A) (x + ω.period) := by
    intro x h1 h2 h3
    have hx : x ∈ Finset.Icc (1 : ℤ) (((span (ω.compose A) - 1 : ℕ) : ℤ) -
        ((ω.period.toNat : ℕ) : ℤ)) := by
      rw [Finset.mem_Icc, hL, hp]; omega
    have h3' : x % ((ω.period.toNat : ℕ) : ℤ) ∉ holesB ω.case s t := by
      rw [hp]; exact h3
    have := pB x hx h3'
    rwa [hp] at this
  have genA : ∀ k : ℤ, 1 ≤ k → k ≤ (span (ω.compose A) : ℤ) - 1 →
      k % ω.period ∉ holesA ω.case s t →
      wordA (ω.compose A) k = wordA ω.E (natPos ω.period (span A) k) ∧
      1 ≤ natPos ω.period (span A) k ∧ natPos ω.period (span A) k < ω.period + ω.width := by
    intro k h1 h2 h3
    exact native_gen (wordA (ω.compose A)) (wordA ω.E) (f := ω.period) (a := ω.width)
      (m := span A) (N := span (ω.compose A)) (S := holesA ω.case s t) hf hnar.1 hnar.2 hN
      hA0 perA (fun k h1 h2 => hω.wordA_compose_first hA h1 h2)
      (fun k h1 h2 => (hω.words_compose_last hA h1 h2).1) h1 h2 h3
  have genB : ∀ k : ℤ, 1 ≤ k → k ≤ (span (ω.compose A) : ℤ) - 1 →
      k % ω.period ∉ holesB ω.case s t →
      wordB (ω.compose A) k = wordB ω.E (natPos ω.period (span A) k) ∧
      1 ≤ natPos ω.period (span A) k ∧ natPos ω.period (span A) k < ω.period + ω.width := by
    intro k h1 h2 h3
    exact native_gen (wordB (ω.compose A)) (wordB ω.E) (f := ω.period) (a := ω.width)
      (m := span A) (N := span (ω.compose A)) (S := holesB ω.case s t) hf hnar.1 hnar.2 hN
      hB0 perB (fun k h1 h2 => hω.wordB_compose_first hA h1 h2)
      (fun k h1 h2 => (hω.words_compose_last hA h1 h2).2) h1 h2 h3
  by_cases hz : k = 0
  · subst hz
    have : natPos ω.period (span A) 0 = 0 := by simp [natPos]
    rw [this]
    exact ⟨fun _ => by rw [Xw_zero, Xw_zero], fun _ => by rw [Yw_zero, Yw_zero]⟩
  by_cases hn : k = (span (ω.compose A) : ℤ)
  · subst hn
    have hnat : natPos ω.period (span A) (span (ω.compose A) : ℤ) = (span ω.E : ℤ) := by
      unfold natPos
      simp only [show ¬ ((span (ω.compose A) : ℤ) ≤ 0) by omega, ↓reduceIte]
      have h1 : ((span A : ℤ) - 1) ≤ ((span (ω.compose A) : ℤ) - 1) / ω.period := by
        rw [Int.le_ediv_iff_mul_le hf0]; nlinarith
      rw [min_eq_right h1]
      nlinarith
    rw [hnat]
    exact ⟨fun _ => by rw [Xw_span hspC1, Xw_span hspE1], fun _ => by
      rw [Yw_span hspC1, Yw_span hspE1]⟩
  have hk1 : 1 ≤ k := by omega
  have hk2 : k ≤ (span (ω.compose A) : ℤ) - 1 := by omega
  constructor
  · intro hS
    obtain ⟨h1, h2, h3⟩ := genB k hk1 hk2 hS
    rw [Xw_of_mem hk1 (by omega), Xw_of_mem h2 (by omega), h1]
  · intro hS
    obtain ⟨h1, h2, h3⟩ := genA k hk1 hk2 hS
    rw [Yw_of_mem hk1 (by omega), Yw_of_mem h2 (by omega), h1]

end MarkedInner

end SkewGluing
