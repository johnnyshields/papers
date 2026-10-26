/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/OrdinaryDrift.lean`. -/
import GluingCore.Coding
import GluingCore.CommonFactorGraph
import GluingCore.OrdinaryDrift.Words

/-!
# Two ordinary roots: the drift lemma

Formalizes `shields-2026-skew-factor-gluing.tex`, «Two ordinary roots» (`eq:gluing-gcd-data`,
`lem:gluing-ordinary-drift`, `eq:gluing-pinch-equations`, `eq:gluing-pinches`).

The arithmetic of the proof is in `GluingCore.OrdinaryDrift.Words`, on abstract bit words.  This
file reads two ordinary proper legal charts of one parent `F` as such words: the words
`ordFold_wA F`, `ordFold_wB F` (`lem:gluing-coding`, via `wordA`, `wordB`), the caps
`eq:gluing-caps`, the exceptional residues `eq:gluing-holes`, the private singletons of
`lem:gluing-local`, and the generic bits of `lem:gluing-periods` (ii).

* `OrdinaryRoot`, `Chart.IsProperLegal.ordinaryRoot`: one ordinary chart with a nonempty mark, read
  on the parent words;
* `OrdinaryPair`: two such charts of one parent, of nondividing periods; `GcdData` is the setting
  `eq:gluing-gcd-data`;
* `ordFold_exists_generic_word`: the generic bits `A⁰_j`, `B⁰_j` of `lem:gluing-periods` (ii);
* `OrdinaryPair.ordinary_drift` (`lem:gluing-ordinary-drift`), with
  `OrdinaryPair.pinch_equations` (`eq:gluing-pinch-equations`) and the pinches
  `eq:gluing-pinches`.

The drift lemma is stated for nonempty marks; the paper's standing assumption for the fold is that
the supplied widths are at least two (`lem:gluing-small` treats widths zero and one).

Sorry-free.
-/

namespace GluingCore

open PeriodWords


/-- The northwest word of a diagram, indexed by `ℕ`. -/
def ordFold_wA (F : Diagram) (k : ℕ) : ℤ := wordA F k

/-- The southeast word of a diagram, indexed by `ℕ`. -/
def ordFold_wB (F : Diagram) (k : ℕ) : ℤ := wordB F k

/-- The height word of the bit words of a connected skew diagram is its diagonal heights. -/
theorem ordFold_heightWord_wA_wB {D : Diagram} (h : IsConnectedSkew D) :
    ∀ n : ℕ, n < span D → heightWord (ordFold_wA D) (ordFold_wB D) n = height D (minContent D + n)
        := by
  intro n
  have h' := isConnectedSkew_iff_diagonal.mp h
  have hspan := span_eq_of_isConnectedSkew h
  have hc0 := minContent_mem h'.1
  have sing : diagLo D (minContent D) = diagHi D (minContent D) :=
    h'.2.2.2.2 _ hc0 (Or.inl (fun hm => by have := minContent_le hm; omega))
  induction n with
  | zero => intro _; simp [heightWord, height, sing]
  | succ n ih =>
    intro hn
    rw [heightWord_succ, ih (by omega)]
    have e1 : minContent D + ((n + 1 : ℕ) : ℤ) - 1 = minContent D + n := by push_cast; ring
    simp only [height, ordFold_wA, ordFold_wB, wordA, wordB, bitA, bitB, e1]
    push_cast
    ring_nf

theorem ordFold_wordData_wA_wB {F : Diagram} (h : IsConnectedSkew F) :
    OrdinaryDrift.WordData (ordFold_wA F) (ordFold_wB F) (span F) := by
  have := isBitData_of_isConnectedSkew h
  obtain ⟨-, hb, hp, hl⟩ := this
  exact ⟨hb, hp, hl⟩


/-- A slice of `X` at the content `c` is a translate of a singleton slice of `Y`: `X` has a
singleton diagonal there. -/
theorem ordFold_diag_singleton_of_slice {X Y : Diagram} {v : ℤ × ℤ} {c : ℤ} (hX : c ∈ contents X)
    (hslice : ∀ x : ℤ × ℤ, content x = c → (x ∈ X ↔ x - v ∈ Y))
    (hY : diagLo Y (c - content v) = diagHi Y (c - content v)) :
    diagLo X c = diagHi X c := by
  have key : ∀ i, (i, i + c) ∈ X → i - v.1 = diagLo Y (c - content v) := by
    intro i hi
    have hy := (hslice (i, i + c) (by simp [content])).mp hi
    have e : (i, i + c) - v = (i - v.1, (i - v.1) + (c - content v)) := by
      ext <;> simp [content]
      ring
    rw [e] at hy
    have h1 := diagLo_le (k := c - content v) hy (by ring)
    have h2 := le_diagHi (k := c - content v) hy (by ring)
    omega
  have h1 := key _ (diagLo_mem hX)
  have h2 := key _ (diagHi_mem hX)
  omega

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem IsLegalNonempty.contents_compose (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    {c : ℤ} : c ∈ contents (ω.compose D) ↔
      minContent ω.E + minContent D * ω.period ≤ c ∧
        c ≤ minContent ω.E + maxContent D * ω.period + ω.period + ω.widthZ - 1 := by
  have hP := h.1.isConnectedSkew_compose hD
  rw [(isConnectedSkew_iff_diagonal.mp hP).mem_contents_iff, h.1.minContent_compose hD,
    h.1.maxContent_compose hD]
  rfl

/-- The private singletons of a composite, on its diagonals: `H_w`, `H_{q-1}`, `H_{N-q}` and
`H_{N-1-w}` are all `1`, i.e. the first and last row coincide. -/
theorem IsLegalNonempty.parent_singleton_diagonals (h : ω.IsLegalNonempty)
    (hD : IsConnectedSkew D) :
    (diagLo (ω.compose D) (minContent ω.E + minContent D * ω.period + ω.widthZ) =
      diagHi (ω.compose D) (minContent ω.E + minContent D * ω.period + ω.widthZ)) ∧
    (diagLo (ω.compose D) (minContent ω.E + minContent D * ω.period + (ω.period - 1)) =
      diagHi (ω.compose D) (minContent ω.E + minContent D * ω.period + (ω.period - 1))) ∧
    (diagLo (ω.compose D) (minContent ω.E + maxContent D * ω.period + ω.widthZ) =
      diagHi (ω.compose D) (minContent ω.E + maxContent D * ω.period + ω.widthZ)) ∧
    (diagLo (ω.compose D) (minContent ω.E + maxContent D * ω.period + (ω.period - 1)) =
      diagHi (ω.compose D) (minContent ω.E + maxContent D * ω.period + (ω.period - 1))) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hwz : ω.widthZ = (ω.width : ℤ) := rfl
  have hDne := hD.2.1
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hDne)
  have hmq : minContent D * ω.period ≤ maxContent D * ω.period :=
    mul_le_mul_of_nonneg_right hmM (by omega)
  have s1 := h.lo_w_eq_hi_w
  have s2 := h.lo_pred_period_eq_hi
  have hcoF : content (ω.origin D (sw D)) = minContent D * ω.period := by
    rw [content_origin, content_sw hDne]
  have hcoL : content (ω.origin D (ne D)) = maxContent D * ω.period := by
    rw [content_origin, content_ne hDne]
  have hEc : ∀ a : ℤ, 0 ≤ a → a ≤ ω.period + ω.widthZ - 1 → minContent ω.E + a ∈ contents ω.E :=
    fun a h1 h2 => by
      rw [h.contents_E, Finset.mem_Icc]; constructor <;> omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ordFold_diag_singleton_of_slice (v := ω.origin D (sw D))
      ((h.contents_compose hD).mpr ⟨by omega, by omega⟩)
    · intro x hx
      exact h.1.mem_compose_first hD (by omega)
    · rw [hcoF]
      have e : minContent ω.E + minContent D * ω.period + ω.widthZ - minContent D * ω.period =
          minContent ω.E + ω.widthZ := by ring
      rw [e]; exact s1
  · apply ordFold_diag_singleton_of_slice (v := ω.origin D (sw D))
      ((h.contents_compose hD).mpr ⟨by omega, by omega⟩)
    · intro x hx
      exact h.1.mem_compose_first hD (by omega)
    · rw [hcoF]
      have e : minContent ω.E + minContent D * ω.period + (ω.period - 1) -
          minContent D * ω.period = minContent ω.E + (ω.period - 1) := by ring
      rw [e]; exact s2
  · apply ordFold_diag_singleton_of_slice (v := ω.origin D (ne D))
      ((h.contents_compose hD).mpr ⟨by omega, by omega⟩)
    · intro x hx
      exact h.1.mem_compose_last hD (by omega)
    · rw [hcoL]
      have e : minContent ω.E + maxContent D * ω.period + ω.widthZ - maxContent D * ω.period =
          minContent ω.E + ω.widthZ := by ring
      rw [e]; exact s1
  · apply ordFold_diag_singleton_of_slice (v := ω.origin D (ne D))
      ((h.contents_compose hD).mpr ⟨by omega, by omega⟩)
    · intro x hx
      exact h.1.mem_compose_last hD (by omega)
    · rw [hcoL]
      have e : minContent ω.E + maxContent D * ω.period + (ω.period - 1) -
          maxContent D * ω.period = minContent ω.E + (ω.period - 1) := by ring
      rw [e]; exact s2


end MarkedInner

/-- The exceptional residue of the northwest word `A` of an ordinary mark, from
`eq:gluing-holes`: `t` in case (a), `s` in case (b). -/
def ordHoleA (x : AttachCase) (s t : ℤ) : ℤ :=
  match x with
  | .b => s
  | _ => t

/-- The exceptional residue of the southeast word `B` of an ordinary mark, from
`eq:gluing-holes`: `s` in case (a), `t` in case (b). -/
def ordHoleB (x : AttachCase) (s t : ℤ) : ℤ :=
  match x with
  | .b => t
  | _ => s

theorem ordFold_holesA_ordinary {x : AttachCase} (hx : ¬ x.IsMixed) (s t : ℤ) :
    holesA x s t = {ordHoleA x s t} := by
  cases x <;> simp_all [AttachCase.IsMixed, holesA, ordHoleA]

theorem ordFold_holesB_ordinary {x : AttachCase} (hx : ¬ x.IsMixed) (s t : ℤ) :
    holesB x s t = {ordHoleB x s t} := by
  cases x <;> simp_all [AttachCase.IsMixed, holesB, ordHoleB]


namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem IsLegalNonempty.span_compose_nat (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) :
    span (ω.compose D) = span D * ω.period.toNat + ω.width := by
  have h1 := span_compose hD h.1
  have hq := h.1.period_pos
  have : (ω.period.toNat : ℤ) = ω.period := Int.toNat_of_nonneg hq.le
  zify
  rw [this]
  exact h1

/-- Heights of the parent words at the private singletons (`lem:gluing-local` (1), (3)). -/
theorem IsLegalNonempty.parent_heights (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hD2 : 2 ≤ span D) :
    heightWord (ordFold_wA (ω.compose D)) (ordFold_wB (ω.compose D)) ω.width = 1 ∧
    heightWord (ordFold_wA (ω.compose D)) (ordFold_wB (ω.compose D)) (ω.period.toNat - 1) = 1 ∧
    heightWord (ordFold_wA (ω.compose D)) (ordFold_wB (ω.compose D)) (span (ω.compose D) -
        ω.period.toNat) = 1 ∧
    heightWord (ordFold_wA (ω.compose D)) (ordFold_wB (ω.compose D)) (span (ω.compose D) - 1 -
        ω.width) = 1 := by
  have hP := h.1.isConnectedSkew_compose hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hwz : ω.widthZ = (ω.width : ℤ) := rfl
  have hqn : (ω.period.toNat : ℤ) = ω.period := Int.toNat_of_nonneg (by omega)
  have hN := h.span_compose_nat hD
  have hsD := span_eq_of_isConnectedSkew hD
  have hmin := h.1.minContent_compose hD
  obtain ⟨s1, s2, s3, s4⟩ := h.parent_singleton_diagonals hD
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hlt : span (ω.compose D) - 1 - ω.width < span (ω.compose D) := by omega
  have hq1 : ω.period.toNat - 1 < span (ω.compose D) := by
    have : 1 ≤ ω.period.toNat := by omega
    have : 2 ≤ span D := hD2
    have := Nat.mul_le_mul_right ω.period.toNat hD2
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ordFold_heightWord_wA_wB hP _ (by
      have : 2 ≤ span D := hD2
      have := Nat.mul_le_mul_right ω.period.toNat hD2
      omega)]
    unfold height
    rw [hmin]
    have e : minContent ω.E + minContent D * ω.period + (ω.width : ℤ) =
        minContent ω.E + minContent D * ω.period + ω.widthZ := by rw [hwz]
    rw [e, s1]; ring
  · rw [ordFold_heightWord_wA_wB hP _ hq1]
    unfold height
    rw [hmin]
    have e : minContent ω.E + minContent D * ω.period + (((ω.period.toNat - 1 : ℕ)) : ℤ) =
        minContent ω.E + minContent D * ω.period + (ω.period - 1) := by
      have : 1 ≤ ω.period.toNat := by omega
      push_cast [Nat.cast_sub this]; rw [hqn]
    rw [e, s2]; ring
  · rw [ordFold_heightWord_wA_wB hP _ (by
      have : 2 ≤ span D := hD2
      have := Nat.mul_le_mul_right ω.period.toNat hD2
      omega)]
    unfold height
    rw [hmin]
    have e : minContent ω.E + minContent D * ω.period +
        (((span (ω.compose D) - ω.period.toNat : ℕ)) : ℤ) =
        minContent ω.E + maxContent D * ω.period + ω.widthZ := by
      have h1 : ω.period.toNat ≤ span (ω.compose D) := by
        have := Nat.mul_le_mul_right ω.period.toNat hD2
        omega
      push_cast [Nat.cast_sub h1]
      rw [hN]; push_cast; rw [hqn, hwz]
      have : (span D : ℤ) = maxContent D - minContent D + 1 := hsD
      rw [this]; ring
    rw [e, s3]; ring
  · rw [ordFold_heightWord_wA_wB hP _ hlt]
    unfold height
    rw [hmin]
    have h1 : ω.width + 1 ≤ span (ω.compose D) := by
      have := Nat.mul_le_mul_right ω.period.toNat hD2
      omega
    have hX1 : 1 ≤ span D * ω.period.toNat := by
      have := Nat.mul_le_mul_right ω.period.toNat hD2
      omega
    have e1 : span (ω.compose D) - 1 - ω.width = span D * ω.period.toNat - 1 := by
      rw [hN]; omega
    have e : minContent ω.E + minContent D * ω.period +
        (((span (ω.compose D) - 1 - ω.width : ℕ)) : ℤ) =
        minContent ω.E + maxContent D * ω.period + (ω.period - 1) := by
      rw [e1]
      push_cast [Nat.cast_sub hX1]
      rw [hqn]
      have : (span D : ℤ) = maxContent D - minContent D + 1 := hsD
      rw [this]; ring
    rw [e, s4]; ring


theorem IsLegalNonempty.rootWords (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hD2 : 2 ≤ span D) (hord : ¬ ω.case.IsMixed) {s t : ℤ} (hph : ω.IsPhases s t) :
    OrdinaryDrift.RootWords (ordFold_wA (ω.compose D)) (ordFold_wB (ω.compose D)) (span (ω.compose
        D))
      ω.period.toNat ω.width (ordHoleA ω.case s t).toNat (ordHoleB ω.case s t).toNat := by
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hq := h.width_lt_period
  have hwz : ω.widthZ = (ω.width : ℤ) := rfl
  have hqn : (ω.period.toNat : ℤ) = ω.period := Int.toNat_of_nonneg (by omega)
  have hN := h.span_compose_nat hD
  have hwN : ω.width ≤ span (ω.compose D) := by
    have := Nat.mul_le_mul_right ω.period.toNat hD2
    omega
  have hcast : ∀ x : ℕ, (((span (ω.compose D) - ω.width + x : ℕ)) : ℤ) =
      (span (ω.compose D) : ℤ) - ω.widthZ + x := by
    intro x; push_cast [Nat.cast_sub hwN]; rw [hwz]
  obtain ⟨hh1, hh2, hh3, hh4⟩ := h.parent_heights hD hD2
  have hsn : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg (by omega)
  have htn : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg (by omega)
  have hrep : ∃ r, 2 ≤ r ∧ span (ω.compose D) = r * ω.period.toNat + ω.width :=
    ⟨span D, hD2, hN⟩
  have hwq : ω.width < ω.period.toNat := by omega
  have hmix : ω.case = .a ∨ ω.case = .b := by
    unfold AttachCase.IsMixed at hord
    cases hc : ω.case <;> simp_all
  rcases hmix with hc | hc
  · have cp := h.caps_a hD hc hph
    simp only [ordHoleA, ordHoleB, hc]
    refine ⟨hwq, hrep, by omega, by omega, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_,
      fun h1 => ?_, hh1, hh2, hh4, hh3⟩
    · have := cp.1 (by omega)
      unfold ordFold_wA; rwa [htn]
    · have := cp.2.1
      unfold ordFold_wB; rwa [hsn]
    · have := cp.2.2.1
      unfold ordFold_wA; rw [hcast, htn]; exact this
    · have := cp.2.2.2 (by omega)
      unfold ordFold_wB; rw [hcast, hsn]; exact this
  · have cp := h.caps_b hD hc hph
    simp only [ordHoleA, ordHoleB, hc]
    refine ⟨hwq, hrep, by omega, by omega, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_,
      fun h1 => ?_, hh1, hh2, hh4, hh3⟩
    · have := cp.2.1
      unfold ordFold_wA; rwa [hsn]
    · have := cp.1 (by omega)
      unfold ordFold_wB; rwa [htn]
    · have := cp.2.2.2 (by omega)
      unfold ordFold_wA; rw [hcast, hsn]; exact this
    · have := cp.2.2.1
      unfold ordFold_wB; rw [hcast, htn]; exact this


end MarkedInner

theorem ordHoleA_nonneg {ω : MarkedInner} {s t : ℤ} (hph : ω.IsPhases s t)
    : 0 ≤ ordHoleA ω.case s t := by
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  unfold ordHoleA
  cases ω.case <;> simp <;> omega

theorem ordHoleB_nonneg {ω : MarkedInner} {s t : ℤ} (hph : ω.IsPhases s t)
    : 0 ≤ ordHoleB ω.case s t := by
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  unfold ordHoleB
  cases ω.case <;> simp <;> omega

theorem ordFold_periodExcept_congr {L p : ℕ} {S : Finset ℤ} {f g : ℤ → ℤ}
    (h : ∀ x ∈ Finset.Icc (1 : ℤ) L, f x = g x) (hf : PeriodWords.PeriodExcept L p S f) :
    PeriodWords.PeriodExcept L p S g := by
  intro x hx hS
  rw [Finset.mem_Icc] at hx
  have h1 := h x (Finset.mem_Icc.mpr ⟨hx.1, by omega⟩)
  have h2 := h (x + p) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  rw [← h1, ← h2]
  exact hf x (Finset.mem_Icc.mpr hx) hS

/-- One ordinary root read on the boundary words of the parent `F`: `(ordFold_wA F, ordFold_wB F)`
are the bit
words of a connected skew diagram, they carry the facts `RootWords` of a root of period `q` and
width `w` with exceptional residues `ha`, `hb`, and they have period `q` except at `ha` (word `A`)
and at `hb` (word `B`), as in `eq:gluing-holes`. -/
structure OrdinaryRoot (F : Diagram) (q w ha hb : ℕ) : Prop where
  words : OrdinaryDrift.WordData (ordFold_wA F) (ordFold_wB F) (span F)
  root : OrdinaryDrift.RootWords (ordFold_wA F) (ordFold_wB F) (span F) q w ha hb
  periodA : PeriodWords.PeriodExcept (span F - 1) q {(ha : ℤ)} (wordA F)
  periodB : PeriodWords.PeriodExcept (span F - 1) q {(hb : ℤ)} (wordB F)

/-- An ordinary proper legal chart with a nonempty mark is an `OrdinaryRoot` of its parent, for the
middle phases `s, t`. -/
theorem Chart.IsProperLegal.ordinaryRoot {χ : Chart} {F : Diagram} (h : χ.IsProperLegal)
    (hF : χ.IsChartOf F) (hord : ¬ χ.ω.case.IsMixed) (hW : χ.ω.W.Nonempty) :
    ∃ s t : ℤ, χ.ω.IsPhases s t ∧
      OrdinaryRoot F χ.ω.period.toNat χ.ω.width (ordHoleA χ.ω.case s t).toNat
        (ordHoleB χ.ω.case s t).toNat := by
  obtain ⟨t0, rfl⟩ := hF
  have hl : χ.ω.IsLegalNonempty := ⟨h.2.2.2, hW⟩
  have hD := h.1
  have hD2 := two_le_span_of_two_le_card h.1 h.2.1
  have hP := h.2.2.2.isConnectedSkew_compose hD
  obtain ⟨s, t, hph⟩ : ∃ s t, χ.ω.IsPhases s t := hl.exists_phases
  refine ⟨s, t, hph, ?_⟩
  change OrdinaryRoot (translate t0 (χ.ω.compose χ.D)) _ _ _ _
  have hspan : span (translate t0 (χ.ω.compose χ.D)) = span (χ.ω.compose χ.D) :=
    span_translate _
  have hagree : ∀ x : ℕ, 1 ≤ x → x < span (χ.ω.compose χ.D) →
      ordFold_wA (translate t0 (χ.ω.compose χ.D)) x = ordFold_wA (χ.ω.compose χ.D) x ∧
        ordFold_wB (translate t0 (χ.ω.compose χ.D)) x = ordFold_wB (χ.ω.compose χ.D) x := fun x h1
            h2 =>
    ⟨wordA_translate hP t0 (by omega) (by omega), wordB_translate hP t0 (by omega)
        (by omega)⟩
  have hagreeZ : ∀ x ∈ Finset.Icc (1 : ℤ) (((span (χ.ω.compose χ.D) - 1 : ℕ)) : ℤ),
      (wordA (χ.ω.compose χ.D) x = wordA (translate t0 (χ.ω.compose χ.D)) x ∧
        wordB (χ.ω.compose χ.D) x = wordB (translate t0 (χ.ω.compose χ.D)) x) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    exact ⟨(wordA_translate hP t0 hx.1 (by omega)).symm,
      (wordB_translate hP t0 hx.1 (by omega)).symm⟩
  obtain ⟨pa, pb⟩ := hl.gluing_coding_periodic hD hph
  rw [ordFold_holesA_ordinary hord] at pa
  rw [ordFold_holesB_ordinary hord] at pb
  have hA0 := ordHoleA_nonneg hph
  have hB0 := ordHoleB_nonneg hph
  have hspan' : span (translate t0 (χ.ω.compose χ.D)) - 1 = span (χ.ω.compose χ.D) - 1 := by
    rw [hspan]
  refine ⟨ordFold_wordData_wA_wB (isConnectedSkew_translate t0 hP), ?_, ?_, ?_⟩
  · rw [hspan]
    exact (hl.rootWords hD hD2 hord hph).congr (fun x h1 h2 =>
      ⟨(hagree x h1 h2).1.symm, (hagree x h1 h2).2.symm⟩)
  · rw [hspan']
    refine ordFold_periodExcept_congr (fun x hx => (hagreeZ x hx).1) ?_
    rwa [Int.toNat_of_nonneg hA0]
  · rw [hspan']
    refine ordFold_periodExcept_congr (fun x hx => (hagreeZ x hx).2) ?_
    rwa [Int.toNat_of_nonneg hB0]



theorem ordFold_sh_iff {p Q h₁ h₂ : ℕ} {x : ℕ} :
    IsSimultaneousHole p Q {(h₁ : ℤ)} {(h₂ : ℤ)} (x : ℤ) ↔ (x % p = h₁ ∧ x % Q = h₂) := by
  unfold IsSimultaneousHole
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨e1, e2⟩
    exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
  · rintro ⟨e1, e2⟩
    exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩

/-- **The generic bits of `lem:gluing-periods` (ii)**, for a word with one exceptional residue in
each of two nondividing periods: there is a word `W⁰` on the residues modulo `g = gcd p Q` that the
word follows at every position that is not a simultaneous hole. -/
theorem ordFold_exists_generic_word {W : ℤ → ℤ} {N p Q w u h₁ h₂ r m : ℕ} (hp : 0 < p) (hQ : 0 < Q)
    (hr : 2 ≤ r) (hm : 2 ≤ m) (hw : w < p) (hu : u < Q) (hNp : N = r * p + w)
    (hNQ : N = m * Q + u) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) (hh₁ : h₁ ≤ w) (hh₂ : h₂ ≤ u)
    (hfp : PeriodExcept (N - 1) p {(h₁ : ℤ)} W) (hfQ : PeriodExcept (N - 1) Q {(h₂ : ℤ)} W) :
    ∃ W0 : ℕ → ℤ, (∀ j, j < Nat.gcd p Q → ∃ x : ℕ, 1 ≤ x ∧ x < N ∧ W0 j = W x) ∧
      ∀ x : ℕ, 1 ≤ x → x < N → ¬ (x % p = h₁ ∧ x % Q = h₂) → W x = W0 (x % Nat.gcd p Q) := by
  set g := Nat.gcd p Q with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hp
  have hgp : g ∣ p := Nat.gcd_dvd_left p Q
  have hgQ : g ∣ Q := Nat.gcd_dvd_right p Q
  have hpg : g < p := by
    rcases (Nat.le_of_dvd hp hgp).lt_or_eq with h | h
    · exact h
    · exfalso; apply hpQ; rw [← h]; exact hgQ
  have hgg : 2 * g ≤ p := by
    obtain ⟨k, hk⟩ := hgp
    have : 2 ≤ k := by
      by_contra hk2
      have : k ≤ 1 := by omega
      interval_cases k <;> omega
    nlinarith
  have hN2 : 2 * p ≤ N := by
    have := Nat.mul_le_mul_right p hr; omega
  have hLN : N - 1 + 1 = N := by omega
  have hnotboth : ∀ y : ℕ, ¬ (y % p = h₁ ∧ y % Q = h₂) ∨
      ¬ ((y + g) % p = h₁ ∧ (y + g) % Q = h₂) := by
    intro y
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hcon
    have hmod : y ≡ y + g [MOD p] := by unfold Nat.ModEq; rw [a1, b1]
    have d1 : p ∣ g := by
      have := (Nat.modEq_iff_dvd' (Nat.le_add_right y g)).mp hmod
      simpa using this
    exact absurd (Nat.le_of_dvd hg0 d1) (by omega)
  let rep : ℕ → ℕ := fun j => if (j + g) % p = h₁ ∧ (j + g) % Q = h₂ then j + 2 * g else j + g
  have hrep_range : ∀ j, j < g → 1 ≤ rep j ∧ rep j < N := by
    intro j hj
    unfold rep
    split_ifs <;> constructor <;> omega
  have hrep_nsh : ∀ j, ¬ ((rep j) % p = h₁ ∧ (rep j) % Q = h₂) := by
    intro j
    unfold rep
    split_ifs with hs
    · have := hnotboth (j + g)
      rw [show j + g + g = j + 2 * g by ring] at this
      rcases this with h | h
      · exact absurd hs h
      · exact h
    · exact hs
  have hrep_mod : ∀ j, j < g → rep j % g = j := by
    intro j hj
    unfold rep
    split_ifs
    · rw [show j + 2 * g = j + g * 2 by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  refine ⟨fun j => W (rep j),
    fun j hj => ⟨rep j, (hrep_range j hj).1, (hrep_range j hj).2, rfl⟩, ?_⟩
  intro x hx1 hx2 hxs
  have hj : x % g < g := Nat.mod_lt _ hg0
  have hrr := hrep_range (x % g) hj
  have hjoined := periods_two_holes (p := p) (Q := Q) (N := N) (r := r) (m := m) (w := w)
    (u := u) (h₁ := (h₁ : ℤ)) (h₂ := (h₂ : ℤ)) (L := N - 1) hp hQ hr hm hw hu hNp hNQ hpQ hQp
    ⟨by positivity, by exact_mod_cast hh₁⟩ ⟨by positivity, by exact_mod_cast hh₂⟩ (by omega)
    (x := (x : ℤ)) (y := ((rep (x % g) : ℕ) : ℤ))
    (Finset.mem_Icc.mpr ⟨by exact_mod_cast hx1,
      by push_cast [Nat.cast_sub (show 1 ≤ N by omega)]; omega⟩)
    (Finset.mem_Icc.mpr ⟨by exact_mod_cast hrr.1,
      by push_cast [Nat.cast_sub (show 1 ≤ N by omega)]; omega⟩)
    (by
      have h1 : (x : ℤ) ≡ ((rep (x % g) : ℕ) : ℤ) [ZMOD (g : ℤ)] := by
        rw [Int.natCast_modEq_iff]
        unfold Nat.ModEq
        rw [hrep_mod _ hj]
      exact (Int.modEq_iff_dvd.mp h1))
    (fun hh => hxs (ordFold_sh_iff.mp hh))
    (fun hh => hrep_nsh _ (ordFold_sh_iff.mp hh))
  exact hjoined.eq_of_periodExcept hfp hfQ



/-- Two `OrdinaryRoot`s of one parent, of periods `a g`, `c g` with `a, c ≥ 2` coprime and
widths `b g + w_g`, `d g + w_g`, give the `GcdPair` of `GluingCore.OrdinaryDrift.Words`: the
generic words `A⁰`, `B⁰` are those of `lem:gluing-periods` (ii). -/
theorem ordFold_gcdPair_of_roots {F : Diagram} {p Q w₁ w₂ g a b c d wg ha₁ hb₁ ha₂ hb₂ : ℕ}
    (R₁ : OrdinaryRoot F p w₁ ha₁ hb₁) (R₂ : OrdinaryRoot F Q w₂ ha₂ hb₂)
    (hg : g = Nat.gcd p Q) (hp : p = a * g) (hQ : Q = c * g) (hcop : Nat.Coprime a c)
    (ha2 : 2 ≤ a) (hc2 : 2 ≤ c) (hwg : wg < g) (hw₁ : w₁ = b * g + wg) (hw₂ : w₂ = d * g + wg)
    (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) :
    ∃ A0 B0 : ℕ → ℤ, OrdinaryDrift.GcdPair (ordFold_wA F) (ordFold_wB F) A0 B0 (span F) g a b c d wg
      ha₁ hb₁ ha₂ hb₂ := by
  obtain ⟨r₁, hr₁, hN₁⟩ := R₁.root.rep
  obtain ⟨r₂, hr₂, hN₂⟩ := R₂.root.rep
  have hp0 : 0 < p := by have := R₁.root.hwq; omega
  have hQ0 : 0 < Q := by have := R₂.root.hwq; omega
  have hg0 : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_left _ hp0
  have hgg : Nat.gcd p Q = g := hg.symm
  have wq₁ := R₁.root.hwq
  have wq₂ := R₂.root.hwq
  obtain ⟨A0, hA0r, hA0g⟩ := ordFold_exists_generic_word (W := wordA F) hp0 hQ0 hr₁ hr₂ wq₁ wq₂ hN₁
      hN₂
    hpQ hQp R₁.root.ha_le R₂.root.ha_le R₁.periodA R₂.periodA
  obtain ⟨B0, hB0r, hB0g⟩ := ordFold_exists_generic_word (W := wordB F) hp0 hQ0 hr₁ hr₂ wq₁ wq₂ hN₁
      hN₂
    hpQ hQp R₁.root.hb_le R₂.root.hb_le R₁.periodB R₂.periodB
  rw [hgg] at hA0r hA0g hB0r hB0g
  subst hp hQ hw₁ hw₂
  refine ⟨A0, B0, ?_⟩
  exact ⟨R₁.words, hg0, ha2, hc2, hcop, hwg, R₁.root, R₂.root,
    fun j hj => by
      obtain ⟨x, hx1, hx2, hx⟩ := hA0r j hj
      have := (R₁.words.bits x hx1 hx2).1
      rw [hx]; exact this,
    fun j hj => by
      obtain ⟨x, hx1, hx2, hx⟩ := hB0r j hj
      have := (R₁.words.bits x hx1 hx2).2
      rw [hx]; exact this,
    fun x hx1 hx2 hS => hA0g x hx1 hx2 hS, fun x hx1 hx2 hS => hB0g x hx1 hx2 hS⟩


/-! ### Two ordinary roots of nondividing periods -/

/-- Two ordinary proper legal roots of one parent `F`, with nonempty marks and nondividing periods:
the hypotheses of `lem:gluing-ordinary-drift` and `prop:gluing-ordinary-fold`.  (The paper treats
widths zero and one by `lem:gluing-small`; nonempty marks are what the coding lemma reads.) -/
structure OrdinaryPair (F : Diagram) (χ₁ χ₂ : Chart) : Prop where
  proper₁ : χ₁.IsProperLegal
  proper₂ : χ₂.IsProperLegal
  chart₁ : χ₁.IsChartOf F
  chart₂ : χ₂.IsChartOf F
  ordinary₁ : ¬ χ₁.ω.case.IsMixed
  ordinary₂ : ¬ χ₂.ω.case.IsMixed
  nonempty₁ : χ₁.ω.W.Nonempty
  nonempty₂ : χ₂.ω.W.Nonempty
  nondiv₁ : ¬ χ₁.ω.period.toNat ∣ χ₂.ω.period.toNat
  nondiv₂ : ¬ χ₂.ω.period.toNat ∣ χ₁.ω.period.toNat

/-- The setting `eq:gluing-gcd-data`: periods `p = a g`, `Q = c g` with `gcd (a, c) = 1`,
`a, c ≥ 2`; span `N = g M + w_g` with `0 ≤ w_g < g`; widths `w = b g + w_g` and `u = d g + w_g`. -/
structure GcdData (F : Diagram) (χ₁ χ₂ : Chart) (g a b c d M wg : ℕ) : Prop where
  g_eq : g = Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat
  period₁ : χ₁.ω.period.toNat = a * g
  period₂ : χ₂.ω.period.toNat = c * g
  coprime : Nat.Coprime a c
  a_ge : 2 ≤ a
  c_ge : 2 ≤ c
  span_eq : span F = g * M + wg
  wg_lt : wg < g
  width₁ : χ₁.ω.width = b * g + wg
  width₂ : χ₂.ω.width = d * g + wg

theorem ordFold_mul_add_mod_of_dvd {g p r w : ℕ} (hg : g ∣ p) : (r * p + w) % g = w % g := by
  obtain ⟨k, rfl⟩ := hg
  rw [show r * (g * k) = g * (r * k) by ring, Nat.mul_add_mod]

theorem OrdinaryPair.exists_gcdData {F : Diagram} {χ₁ χ₂ : Chart} (h : OrdinaryPair F χ₁ χ₂) :
    ∃ g a b c d M wg, GcdData F χ₁ χ₂ g a b c d M wg := by
  obtain ⟨s₁, t₁, hph₁, R₁⟩ := h.proper₁.ordinaryRoot h.chart₁ h.ordinary₁ h.nonempty₁
  obtain ⟨s₂, t₂, hph₂, R₂⟩ := h.proper₂.ordinaryRoot h.chart₂ h.ordinary₂ h.nonempty₂
  obtain ⟨r₁, hr₁, hN₁⟩ := R₁.root.rep
  have hp0 : 0 < χ₁.ω.period.toNat := by have := R₁.root.hwq; omega
  have hQ0 : 0 < χ₂.ω.period.toNat := by have := R₂.root.hwq; omega
  set p := χ₁.ω.period.toNat with hp
  set Q := χ₂.ω.period.toNat with hQ
  set g := Nat.gcd p Q with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hp0
  have hgp : g ∣ p := Nat.gcd_dvd_left p Q
  have hgQ : g ∣ Q := Nat.gcd_dvd_right p Q
  refine ⟨g, p / g, χ₁.ω.width / g, Q / g, χ₂.ω.width / g, span F / g, span F % g,
    ⟨hg, (Nat.div_mul_cancel hgp).symm, (Nat.div_mul_cancel hgQ).symm,
      Nat.coprime_div_gcd_div_gcd hg0, ?_, ?_, (Nat.div_add_mod _ _).symm, Nat.mod_lt _ hg0,
      ?_, ?_⟩⟩
  · by_contra hlt
    have h1 : p / g = 1 := by
      have : 0 < p / g := Nat.div_pos (Nat.le_of_dvd hp0 hgp) hg0
      omega
    apply h.nondiv₁
    have : p = g := by
      have := Nat.div_mul_cancel hgp
      rw [h1] at this; omega
    change p ∣ Q
    rw [this]; exact hgQ
  · by_contra hlt
    have h1 : Q / g = 1 := by
      have : 0 < Q / g := Nat.div_pos (Nat.le_of_dvd hQ0 hgQ) hg0
      omega
    apply h.nondiv₂
    have : Q = g := by
      have := Nat.div_mul_cancel hgQ
      rw [h1] at this; omega
    change Q ∣ p
    rw [this]; exact hgp
  · have hw : span F % g = χ₁.ω.width % g := by
      rw [hN₁]; exact ordFold_mul_add_mod_of_dvd hgp
    rw [hw]; exact (Nat.div_add_mod' _ _).symm
  · obtain ⟨r₂, -, hN₂⟩ := R₂.root.rep
    have hw : span F % g = χ₂.ω.width % g := by
      rw [hN₂]; exact ordFold_mul_add_mod_of_dvd hgQ
    rw [hw]; exact (Nat.div_add_mod' _ _).symm


theorem ordFold_genSum_incr_period (A0 B0 : ℕ → ℤ) {g : ℕ} :
    OrdinaryDrift.genSum (OrdinaryDrift.incr A0 B0 g) g = ∑ j ∈ Finset.range g, (A0 j - B0 j) := by
  rw [OrdinaryDrift.genSum_period_eq_sum (by simp [OrdinaryDrift.incr])]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  simp [OrdinaryDrift.incr, Nat.mod_eq_of_lt hj]

theorem ordFold_genSum_incr_lt (A0 B0 : ℕ → ℤ) {g n : ℕ} (hn : n < g) :
    OrdinaryDrift.genSum (OrdinaryDrift.incr A0 B0 g) n =
      ∑ i ∈ Finset.range n, (A0 (i + 1) - B0 (i + 1)) := by
  unfold OrdinaryDrift.genSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp [OrdinaryDrift.incr, Nat.mod_eq_of_lt (show i + 1 < g by omega)]

/-- The conclusion of `lem:gluing-ordinary-drift`, for the parent `F`, in the setting
`eq:gluing-gcd-data` (`p = a g`, `Q = c g`, `w_g`), with generic bits `A⁰`, `B⁰` on the residues
modulo `g` and `C_j = A⁰_j - B⁰_j`:

* the words follow the generic bits at every position that is not a simultaneous hole of the two
  roots (`lem:gluing-periods` (ii)); the exceptional residues of the two roots are
  `ha₁, hb₁` (for the word `A`, `B` of the first root) and `ha₂, hb₂`;
* `Δ = ∑_{j<g} C_j = 0`, the initial budget `ε = C_0` is a bit, `P_{w_g} = -ε`, and the terminal
  budget `-C_{w_g}` is a bit;
* every initial deviation from the generic words occurs within the first `w_g` steps and every
  terminal deviation within the last `w_g` steps (`initial_window`, `terminal_window`): the words
  are generic on the positions `x` with `w_g < x < max (p, Q)` and on those with
  `N - max (p, Q) < y < N - w_g`, whether or not they are simultaneous holes (the simultaneous holes
  beyond these windows are the free slots of the outer, `generic_A`, `generic_B`);
* the pinches `eq:gluing-pinches`: `H_{w_g} = H_{g-1} = H_{N-g} = H_{N-w_g-1} = 1`. -/
structure DriftConclusion (F : Diagram) (g a c wg ha₁ hb₁ ha₂ hb₂ : ℕ) (A0 B0 : ℕ → ℤ) : Prop where
  bit_A : ∀ j, j < g → A0 j = 0 ∨ A0 j = 1
  bit_B : ∀ j, j < g → B0 j = 0 ∨ B0 j = 1
  generic_A : ∀ x, 1 ≤ x → x < span F → ¬ (x % (a * g) = ha₁ ∧ x % (c * g) = ha₂) →
    ordFold_wA F x = A0 (x % g)
  generic_B : ∀ x, 1 ≤ x → x < span F → ¬ (x % (a * g) = hb₁ ∧ x % (c * g) = hb₂) →
    ordFold_wB F x = B0 (x % g)
  delta_zero : ∑ j ∈ Finset.range g, (A0 j - B0 j) = 0
  initial_budget : A0 0 - B0 0 = 0 ∨ A0 0 - B0 0 = 1
  initial_sum : ∑ i ∈ Finset.range wg, (A0 (i + 1) - B0 (i + 1)) = -(A0 0 - B0 0)
  terminal_budget : B0 wg - A0 wg = 0 ∨ B0 wg - A0 wg = 1
  initial_window : ∀ x, wg < x → x < max (a * g) (c * g) → x < span F →
    ordFold_wA F x = A0 (x % g) ∧ ordFold_wB F x = B0 (x % g)
  terminal_window : ∀ y, span F < y + max (a * g) (c * g) → y + wg < span F →
    ordFold_wA F y = A0 (y % g) ∧ ordFold_wB F y = B0 (y % g)
  pinch_initial : height F (minContent F + wg) = 1
  pinch_initial' : height F (minContent F + ((g - 1 : ℕ) : ℤ)) = 1
  pinch_terminal : height F (minContent F + ((span F - g : ℕ) : ℤ)) = 1
  pinch_terminal' : height F (minContent F + ((span F - 1 - wg : ℕ) : ℤ)) = 1

theorem OrdinaryPair.gcdPair {F : Diagram} {χ₁ χ₂ : Chart} (h : OrdinaryPair F χ₁ χ₂)
    {g a b c d M wg : ℕ} (hd : GcdData F χ₁ χ₂ g a b c d M wg) :
    ∃ (s₁ t₁ s₂ t₂ : ℤ) (A0 B0 : ℕ → ℤ), χ₁.ω.IsPhases s₁ t₁ ∧ χ₂.ω.IsPhases s₂ t₂ ∧
      OrdinaryDrift.GcdPair (ordFold_wA F) (ordFold_wB F) A0 B0 (span F) g a b c d wg
        (ordHoleA χ₁.ω.case s₁ t₁).toNat (ordHoleB χ₁.ω.case s₁ t₁).toNat
        (ordHoleA χ₂.ω.case s₂ t₂).toNat (ordHoleB χ₂.ω.case s₂ t₂).toNat := by
  obtain ⟨s₁, t₁, hph₁, R₁⟩ := h.proper₁.ordinaryRoot h.chart₁ h.ordinary₁ h.nonempty₁
  obtain ⟨s₂, t₂, hph₂, R₂⟩ := h.proper₂.ordinaryRoot h.chart₂ h.ordinary₂ h.nonempty₂
  obtain ⟨A0, B0, hG⟩ := ordFold_gcdPair_of_roots R₁ R₂ hd.g_eq hd.period₁ hd.period₂ hd.coprime
      hd.a_ge
    hd.c_ge hd.wg_lt hd.width₁ hd.width₂ h.nondiv₁ h.nondiv₂
  exact ⟨s₁, t₁, s₂, t₂, A0, B0, hph₁, hph₂, hG⟩

/-- **`lem:gluing-ordinary-drift`.**  Two ordinary proper legal roots of nondividing periods of one
parent `F`, in the setting `eq:gluing-gcd-data`, have generic bits `A⁰_j`, `B⁰_j` on the residues
modulo `g`, and satisfy `DriftConclusion`: `Δ = 0`, the initial and terminal deviations lie within
`w_g` steps of the ends, and the four pinches `eq:gluing-pinches` hold.  Here `s₁ t₁`, `s₂ t₂` are
the middle phases of the two marks. -/
theorem OrdinaryPair.ordinary_drift {F : Diagram} {χ₁ χ₂ : Chart} (h : OrdinaryPair F χ₁ χ₂)
    {g a b c d M wg : ℕ} (hd : GcdData F χ₁ χ₂ g a b c d M wg) :
    ∃ (s₁ t₁ s₂ t₂ : ℤ) (A0 B0 : ℕ → ℤ), χ₁.ω.IsPhases s₁ t₁ ∧ χ₂.ω.IsPhases s₂ t₂ ∧
      DriftConclusion F g a c wg (ordHoleA χ₁.ω.case s₁ t₁).toNat (ordHoleB χ₁.ω.case s₁ t₁).toNat
        (ordHoleA χ₂.ω.case s₂ t₂).toNat (ordHoleB χ₂.ω.case s₂ t₂).toNat A0 B0 := by
  obtain ⟨s₁, t₁, s₂, t₂, A0, B0, hph₁, hph₂, hG⟩ := h.gcdPair hd
  refine ⟨s₁, t₁, s₂, t₂, A0, B0, hph₁, hph₂, ?_⟩
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hG.drift_full
  have hg := hG.g_pos
  have hFc : IsConnectedSkew F := by
    obtain ⟨t0, rfl⟩ := h.chart₁
    exact isConnectedSkew_translate t0 (h.proper₁.2.2.2.isConnectedSkew_compose h.proper₁.1)
  have hN2 := hG.root₁.two_q_le
  have hag : g ≤ a * g := Nat.le_mul_of_pos_left g (by have := hG.a_ge; omega)
  have hwg := hG.wg_lt
  have hH := ordFold_heightWord_wA_wB hFc
  exact ⟨hG.A0_bit, hG.B0_bit, hG.genA, hG.genB, by rw [← ordFold_genSum_incr_period A0 B0]; exact
      d1,
    d2, by rw [← ordFold_genSum_incr_lt A0 B0 hwg]; exact d3, d4, d5, d6,
    by rw [← hH _ (by omega)]; exact d7, by rw [← hH _ (by omega)]; exact d8,
    by rw [← hH _ (by omega)]; exact d9, by rw [← hH _ (by omega)]; exact d10⟩


/-- **`eq:gluing-pinch-equations`.**  For each of the two roots, with `Δ = ∑_{j<g} C_j`,
`ε = C_0`, `P_{w_g} = ∑_{j=1}^{w_g} C_j` and `δ` the sum of the initial deviations of the root
(`1 - A⁰_{ha}` at the northwest cap and `B⁰_{hb}` at the southeast cap, for the exceptional
residues `ha`, `hb` of the root):
`b Δ + P_{w_g} + δ = 0`, `a Δ - ε + δ = 0` and `0 ≤ δ ≤ 2` (and `d, c` for the second root). -/
theorem OrdinaryPair.pinch_equations {F : Diagram} {χ₁ χ₂ : Chart} (h : OrdinaryPair F χ₁ χ₂)
    {g a b c d M wg : ℕ} (hd : GcdData F χ₁ χ₂ g a b c d M wg) :
    ∃ (s₁ t₁ s₂ t₂ : ℤ) (A0 B0 : ℕ → ℤ), χ₁.ω.IsPhases s₁ t₁ ∧ χ₂.ω.IsPhases s₂ t₂ ∧
      let ha₁ := (ordHoleA χ₁.ω.case s₁ t₁).toNat
      let hb₁ := (ordHoleB χ₁.ω.case s₁ t₁).toNat
      let ha₂ := (ordHoleA χ₂.ω.case s₂ t₂).toNat
      let hb₂ := (ordHoleB χ₂.ω.case s₂ t₂).toNat
      let Δ := ∑ j ∈ Finset.range g, (A0 j - B0 j)
      let ε := A0 0 - B0 0
      let P := ∑ i ∈ Finset.range wg, (A0 (i + 1) - B0 (i + 1))
      let δ₁ := OrdinaryDrift.devA A0 g ha₁ + OrdinaryDrift.devB B0 g hb₁
      let δ₂ := OrdinaryDrift.devA A0 g ha₂ + OrdinaryDrift.devB B0 g hb₂
      (b * Δ + P + δ₁ = 0 ∧ a * Δ - ε + δ₁ = 0 ∧ 0 ≤ δ₁ ∧ δ₁ ≤ 2) ∧
      (d * Δ + P + δ₂ = 0 ∧ c * Δ - ε + δ₂ = 0 ∧ 0 ≤ δ₂ ∧ δ₂ ≤ 2) := by
  obtain ⟨s₁, t₁, s₂, t₂, A0, B0, hph₁, hph₂, hG⟩ := h.gcdPair hd
  refine ⟨s₁, t₁, s₂, t₂, A0, B0, hph₁, hph₂, ?_⟩
  have hg := hG.g_pos
  have hwg := hG.wg_lt
  obtain ⟨⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3, f4⟩⟩ := hG.pinch_equations
  simp only
  rw [← ordFold_genSum_incr_period A0 B0, ← ordFold_genSum_incr_lt A0 B0 hwg]
  exact ⟨⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3, f4⟩⟩

/-! ### Checked example

`(14) = (3) ∘_ω (4 + 2) = (2) ∘_ω' (6 + 2)`, both row marks of case (a), of periods `4` and `6`,
widths `2`: gcd `g = 2` and `w_g = 0`.  Both generic words are zero, and the heights are all one,
so the pinches hold. -/

/-- The row `(6)` with the mark of period four, width two. -/
def ordFold_rowInnerPeriodFour : MarkedInner where
  E := skewOf [6] []
  W := {(0, 0), (0, 1)}
  v := (0, 4)
  case := .a

/-- The row `(8)` with the mark of period six, width two. -/
def ordFold_rowInnerPeriodSix : MarkedInner where
  E := skewOf [8] []
  W := {(0, 0), (0, 1)}
  v := (0, 6)
  case := .a

example : ordFold_rowInnerPeriodFour.IsLegal := by decide +kernel
example : ordFold_rowInnerPeriodSix.IsLegal := by decide +kernel

/-- Two ordinary roots of the row `(14)`, of periods `4` and `6` (so `g = 2`). -/
theorem ordFold_row_ordinaryPair : OrdinaryPair (skewOf [14] []) ⟨skewOf [3] [],
    ordFold_rowInnerPeriodFour⟩
    ⟨skewOf [2] [], ordFold_rowInnerPeriodSix⟩ := by
  refine ⟨?_, ?_, ⟨0, ?_⟩, ⟨0, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Chart.IsProperLegal; decide +kernel
  · unfold Chart.IsProperLegal; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- The setting `eq:gluing-gcd-data` for the two roots of the row `(14)`: `g = 2`, `w_g = 0`. -/
theorem ordFold_row_gcdData : GcdData (skewOf [14] []) ⟨skewOf [3] [], ordFold_rowInnerPeriodFour⟩
    ⟨skewOf [2] [], ordFold_rowInnerPeriodSix⟩ 2 2 1 3 1 7 0 := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩ <;>
    decide +kernel

end GluingCore
