import SkewGluing.OrdinaryFold.Fold
import SkewGluing.OrdinaryFold.Antitranspose
import SkewGluing.OrdinaryFold.Empty
import SkewGluing.OrdinaryDrift

/-!
# `prop:gluing-ordinary-fold`: two ordinary roots fold to a period-`g` root

Formalizes `shields-2026-skew-gluing.tex`, «Two ordinary roots» (`prop:gluing-ordinary-fold`,
with `eq:gluing-ordinary-slot`, `eq:gluing-original-ordinary-mark`).

**Statement** (`OrdinaryPair.exists_gcd_root`).  Let `F` have two proper legal ordinary charts with
nonempty marks, of periods `p`, `Q` that do not divide one another, in the setting
`eq:gluing-gcd-data` (`GcdData`), with `g = gcd (p, Q) > 1`.  Then `F` has a proper legal chart of
period `g`: a chart `χ` with `χ.IsProperLegal`, `χ.IsChartOf F` and `χ.period = g`.

The proof runs the paper's three cases.  The roots are first normalized so that the first chart has
case (a) (`OrdinaryPair.at`, antitransposition of the whole pair).  Then:

* `w_g = 0`: the root has the empty mark (`SkewGluing.OrdinaryFold.Empty`);
* `w_g ≥ 1`: the boundary words of `F` are in the slot form `SlotWords`
  (`SkewGluing.OrdinaryFold.Fold`), for the words themselves (the folded mark has case (a)) or for
  their antitransposes (case (b)), and `SlotWords.exists_root` builds the legal mark and the outer.
  The remainder `w_g = 1` is the singleton-mark case, the same construction with a one-cell mark.

**Differs from the paper's route.**  The paper treats the remainder one by the singleton coding of
`lem:gluing-small` and the remainder zero by `lem:gluing-aligned`; here one construction covers
every remainder `w_g ≥ 1` (the inner `G` read from the generic words, with the caps imposed at the
slots), and the empty root is read directly from the parent words.

The "every fork at this diagram glues" consequence of `lem:gluing-aligned` is not part of the
statement; this theorem is the constructive content that the assembly combines with
`prop:gluing-divisible`.

The widths are assumed at least one (nonempty marks); the paper treats widths zero and one by
`lem:gluing-small`.

Sorry-free.
-/

namespace SkewGluing

open OrdinaryFold OrdinaryDrift

namespace Chart

/-- The antitransposed chart: the outer is unchanged, the marked inner is antitransposed. -/
def «at» (χ : Chart) : Chart := ⟨χ.D, χ.ω.anti⟩

theorem at_period (χ : Chart) : χ.at.period = χ.period := MarkedInner.period_anti χ.ω

theorem at_parent {χ : Chart} (h : χ.IsProperLegal) (hord : ¬ χ.ω.case.IsMixed) :
    χ.at.parent = antitranspose χ.parent :=
  (MarkedInner.antitranspose_compose hord (h.1.2.1)).symm

theorem IsProperLegal.at {χ : Chart} (h : χ.IsProperLegal) (hW : χ.ω.W.Nonempty) :
    χ.at.IsProperLegal := by
  obtain ⟨hD, hc, hE, hω⟩ := h
  refine ⟨hD, hc, ?_, MarkedInner.isLegal_anti hω hW⟩
  change 2 ≤ (antitranspose χ.ω.E).card
  rw [card_antitranspose]
  exact hE

theorem IsChartOf.at {χ : Chart} {F : Diagram} (h : χ.IsProperLegal) (hord : ¬ χ.ω.case.IsMixed)
    (hF : χ.IsChartOf F) : χ.at.IsChartOf (antitranspose F) := by
  obtain ⟨t, rfl⟩ := hF
  refine ⟨atVec t, ?_⟩
  rw [at_parent h hord, ← antitranspose_translate]


/-- **The heights of the first band of an ordinary chart of case (a)**
(`eq:gluing-original-ordinary-mark`):
on the contents `z < w` of the parent, the height is the height of the lower copy plus one from the
residue `s` on, hence at least `1 + [s ≤ z]`. -/
theorem IsProperLegal.markHeights {χ : Chart} {F : Diagram} (h : χ.IsProperLegal)
    (hF : χ.IsChartOf F) (hca : χ.ω.case = .a) (hW : χ.ω.W.Nonempty) {s t : ℤ}
    (hph : χ.ω.IsPhases s t) (z : ℕ) (hz : z < χ.ω.width) :
    1 + (if s.toNat ≤ z then 1 else 0) ≤ heightWord (ordFold_wA F) (ordFold_wB F) z := by
  obtain ⟨t0, rfl⟩ := hF
  have hl : χ.ω.IsLegalNonempty := ⟨h.2.2.2, hW⟩
  have hD := h.1
  have hP := h.2.2.2.isConnectedSkew_compose hD
  have hD2 := two_le_span_of_two_le_card h.1 h.2.1
  have hspan := hl.span_compose_nat hD
  have hq := hl.width_lt_period
  have hw := hl.width_pos
  have hqn : (χ.ω.period.toNat : ℤ) = χ.ω.period := Int.toNat_of_nonneg (by omega)
  have hwz : χ.ω.widthZ = (χ.ω.width : ℤ) := rfl
  have hzs : z < span (χ.ω.compose χ.D) := by
    have := Nat.mul_le_mul_right χ.ω.period.toNat hD2
    omega
  change 1 + (if s.toNat ≤ z then 1 else 0) ≤
    heightWord (ordFold_wA (translate t0 (χ.ω.compose χ.D))) (ordFold_wB (translate t0 (χ.ω.compose
        χ.D))) z
  have hcongr : heightWord (ordFold_wA (translate t0 (χ.ω.compose χ.D)))
      (ordFold_wB (translate t0 (χ.ω.compose χ.D))) z =
      heightWord (ordFold_wA (χ.ω.compose χ.D)) (ordFold_wB (χ.ω.compose χ.D)) z :=
    heightWord_congr fun x hx1 hx2 => ⟨wordA_translate hP t0 (by omega) (by omega),
      wordB_translate hP t0 (by omega) (by omega)⟩
  rw [hcongr, ordFold_heightWord_wA_wB hP z hzs]
  obtain ⟨s1, s2, ht1, ht2, -, -⟩ := id hph
  have hmin := hl.minContent_compose' hD
  have hmM : minContent χ.D ≤ maxContent χ.D := minContent_le (maxContent_mem hD.2.1)
  have hE := (hl.ordinary_endpoints_a hD hca hph (J := minContent χ.D) (z := (z : ℤ))
    (by omega)).2.2.1 (by omega) rfl
  have hends := MarkedInner.D_ends hD
  obtain ⟨hlo, hhi⟩ := hE
  obtain ⟨r, hr⟩ := hl.exists_W (a := (z : ℤ)) (by omega) (by omega)
  have hmemW : minContent χ.ω.E + (z : ℤ) ∈ contents χ.ω.W := by
    have := content_mem_contents hr
    rwa [MarkedInner.content_cell] at this
  have hWle := diagLo_le_diagHi hmemW
  unfold height
  rw [hmin]
  have e : minContent χ.ω.E + minContent χ.D * χ.ω.period + (z : ℤ) =
      minContent χ.ω.E + (minContent χ.D * χ.ω.period + (z : ℤ)) := by ring
  have hzcast : ((z : ℕ) : ℤ) = (z : ℤ) := rfl
  rw [e, hlo, hhi]
  have hsz : (s.toNat ≤ z) ↔ s ≤ (z : ℤ) := by omega
  by_cases hsz' : s ≤ (z : ℤ)
  · simp only [show s.toNat ≤ z by omega, show ¬ ((z : ℤ) < s) by omega, ite_true, ite_false]
    omega
  · simp only [show ¬ (s.toNat ≤ z) by omega, show (z : ℤ) < s by omega, ite_true, ite_false]
    omega


/-- A legal chart with an empty mark is the empty mark on its inner, in the horizontal reading. -/
theorem IsProperLegal.eq_emptyMarkH {χ : Chart} (h : χ.IsProperLegal) (hW : χ.ω.W = ∅) :
    χ.ω = emptyMarkH χ.ω.E := by
  have hwf := h.2.2.2.1
  have hemp : χ.ω.IsEmptyMark := by
    rcases hwf.2 with h1 | h1
    · exact h1
    · exact absurd hW h1.1.ne_empty
  obtain ⟨h1, h2, h3⟩ := hemp
  cases hω : χ.ω
  simp only [hω] at h1 h2 h3 ⊢
  simp [emptyMarkH, h1, h2, h3]

/-- **Antitransposing a root back.**  A proper legal ordinary root of `AT(F)`, with a nonempty mark
or the empty mark, gives a proper legal root of `F` of the same period. -/
theorem exists_root_of_at {F : Diagram} {χ' : Chart} (h : χ'.IsProperLegal)
    (hF' : χ'.IsChartOf (antitranspose F)) (hord : ¬ χ'.ω.case.IsMixed)
    (hW : χ'.ω.W.Nonempty ∨ χ'.ω.W = ∅) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period = χ'.period ∧
      χ.ω.width = χ'.ω.width := by
  rcases hW with hW | hW
  · refine ⟨χ'.at, h.at hW, ?_, χ'.at_period, MarkedInner.width_anti χ'.ω⟩
    have := IsChartOf.at h hord hF'
    rwa [antitranspose_antitranspose] at this
  · have hω := h.eq_emptyMarkH hW
    obtain ⟨hD, hc, hE, hleg⟩ := h
    have hEcs : IsConnectedSkew χ'.ω.E := hleg.1.1
    have hEcs' := isConnectedSkew_antitranspose hEcs
    refine ⟨⟨antitranspose χ'.D, emptyMarkH (antitranspose χ'.ω.E)⟩,
      ⟨isConnectedSkew_antitranspose hD, ?_, ?_, emptyMarkH_isLegal hEcs'⟩, ?_, ?_, ?_⟩
    · change 2 ≤ (antitranspose χ'.D).card
      rw [card_antitranspose]; exact hc
    · change 2 ≤ (antitranspose χ'.ω.E).card
      rw [card_antitranspose]; exact hE
    · obtain ⟨t, ht⟩ := hF'
      refine ⟨atVec t, ?_⟩
      have hDne := hD.2.1
      have e1 : (emptyMarkH (antitranspose χ'.ω.E)).compose (antitranspose χ'.D) =
          antitranspose (χ'.ω.compose χ'.D) := by
        rw [compose_emptyMarks_antitranspose (antitranspose_nonempty_iff.mpr hDne),
          antitranspose_antitranspose]
        have hat : emptyMarkV (antitranspose χ'.ω.E) = χ'.ω.anti := by
          have hsw := sw_antitranspose hEcs
          have hne := ne_antitranspose hEcs
          have hv : vV (antitranspose χ'.ω.E) = atVec χ'.ω.v := by
            have hv0 : χ'.ω.v = vH χ'.ω.E := by rw [hω]; rfl
            unfold vV
            rw [hsw, hne, hv0]
            unfold vH
            ext <;> simp [atVec] <;> ring
          have hW0 : antitranspose χ'.ω.W = ∅ := by rw [hW]; rfl
          have hc0 : χ'.ω.case = .a := by rw [hω]; rfl
          simp only [emptyMarkV, MarkedInner.anti, hv, hW0, hc0, AttachCase.anti]
        rw [hat]
        exact (MarkedInner.antitranspose_compose hord hDne).symm
      change F = translate (atVec t) ((emptyMarkH (antitranspose χ'.ω.E)).compose
        (antitranspose χ'.D))
      rw [e1]
      have h2 := congrArg antitranspose ht
      rw [antitranspose_antitranspose] at h2
      rw [h2]
      exact antitranspose_translate t χ'.parent
    · change (emptyMarkH (antitranspose χ'.ω.E)).period = χ'.ω.period
      rw [emptyMarkH_period hEcs', span_antitranspose]
      have : χ'.ω.period = (emptyMarkH χ'.ω.E).period := by rw [← hω]
      rw [this, emptyMarkH_period hEcs]
    · change (emptyMarkH (antitranspose χ'.ω.E)).width = χ'.ω.width
      have h1 : (emptyMarkH (antitranspose χ'.ω.E)).width = 0 := by
        simp [MarkedInner.width, emptyMarkH, span, contents]
      have h2 : χ'.ω.width = 0 := by
        simp [MarkedInner.width, hW, span, contents]
      rw [h1, h2]

end Chart


theorem Chart.IsProperLegal.isConnectedSkew_parent_of {χ : Chart} {F : Diagram} (h :
    χ.IsProperLegal)
    (hF : χ.IsChartOf F) : IsConnectedSkew F := by
  obtain ⟨t, rfl⟩ := hF
  exact isConnectedSkew_translate t (h.2.2.2.isConnectedSkew_compose h.1)

/-- **`prop:gluing-ordinary-fold`, first chart of case (a).**  The constructive content, with the
case split on the remainder `w_g` and on the case of the folded mark; the root is ordinary, with a
nonempty mark or the empty mark. -/
theorem OrdinaryPair.exists_root_case_a {F : Diagram} {χ₁ χ₂ : Chart} (h : OrdinaryPair F χ₁ χ₂)
    (hca : χ₁.ω.case = .a) {g a b c d M wg : ℕ} (hd : GcdData F χ₁ χ₂ g a b c d M wg)
    (hg2 : 2 ≤ g) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period = g ∧ ¬ χ.ω.case.IsMixed ∧
      (χ.ω.W.Nonempty ∨ χ.ω.W = ∅) ∧ χ.ω.width = wg := by
  obtain ⟨s₁, t₁, s₂, t₂, A0, B0, hph₁, hph₂, hG⟩ := h.gcdPair hd
  have e1 : ordHoleA χ₁.ω.case s₁ t₁ = t₁ := by simp [ordHoleA, hca]
  have e2 : ordHoleB χ₁.ω.case s₁ t₁ = s₁ := by simp [ordHoleB, hca]
  rw [e1, e2] at hG
  have hF := h.proper₁.isConnectedSkew_parent_of h.chart₁
  have hw := hd.width₁
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph₁
  have hwz : χ₁.ω.widthZ = (χ₁.ω.width : ℤ) := rfl
  have hha : t₁.toNat < b * g + wg := by omega
  have hhb1 : 1 ≤ s₁.toNat := by omega
  have hMpos : ∀ z, z < b * g + wg →
      1 + (if s₁.toNat ≤ z then 1 else 0) ≤ heightWord (ordFold_wA F) (ordFold_wB F) z := by
    intro z hz
    exact h.proper₁.markHeights h.chart₁ hca h.nonempty₁ hph₁ z (by omega)
  have hspan : (span F) = span F := rfl
  by_cases hwg0 : wg = 0
  · have hEW := hG.emptyWords hwg0 hg2 hha hhb1
    obtain ⟨χ, hχ, hχF, hper, hW⟩ := EmptyWords.exists_root hEW hF rfl
      (fun k _ _ => rfl) (fun k _ _ => rfl)
    refine ⟨χ, hχ, hχF, hper, ?_, Or.inr hW, ?_⟩
    · have := hχ.eq_emptyMarkH hW
      rw [this]
      simp [emptyMarkH, AttachCase.IsMixed]
    · simp [MarkedInner.width, hW, span, contents, hwg0]
  · have hwg1 : 1 ≤ wg := by omega
    by_cases hnew : A0 (t₁.toNat % g) = 1 ∨ t₁.toNat % g < s₁.toNat % g
    · have hSW := hG.slotWords_a hwg1 hha hhb1 hMpos hnew
      obtain ⟨χ, hχ, hχF, hper, hcase, hW, hwid⟩ := SlotWords.exists_root hSW hF rfl
        (fun k _ _ => rfl) (fun k _ _ => rfl)
      refine ⟨χ, hχ, hχF, hper, ?_, Or.inl hW, hwid⟩
      simp [hcase, AttachCase.IsMixed]
    · have hSW := hG.slotWords_b hwg1 hha hhb1 hMpos hnew
      have hF' := isConnectedSkew_antitranspose hF
      obtain ⟨χ', hχ', hχF', hper, hcase, hW, hwid⟩ := SlotWords.exists_root hSW hF' (by
        rw [span_antitranspose])
        (fun k hk1 hk2 => by
          rw [ordFold_wordA_antitranspose hF (by exact_mod_cast hk1) (by exact_mod_cast hk2)]
          rfl)
        (fun k hk1 hk2 => by
          rw [ordFold_wordB_antitranspose hF (by exact_mod_cast hk1) (by exact_mod_cast hk2)]
          rfl)
      have hord : ¬ χ'.ω.case.IsMixed := by simp [hcase, AttachCase.IsMixed]
      refine ⟨χ'.at, hχ'.at hW, ?_, ?_, ?_, Or.inl (antitranspose_nonempty_iff.mpr hW), ?_⟩
      · have := Chart.IsChartOf.at hχ' hord hχF'
        rwa [antitranspose_antitranspose] at this
      · rw [Chart.at_period]; exact hper
      · change ¬ χ'.ω.case.anti.IsMixed
        simp [hcase, AttachCase.IsMixed, AttachCase.anti]
      · change χ'.ω.anti.width = wg
        rw [MarkedInner.width_anti]; exact hwid

/-- The antitransposed pair of ordinary roots of the antitransposed parent. -/
theorem OrdinaryPair.at {F : Diagram} {χ₁ χ₂ : Chart} (h : OrdinaryPair F χ₁ χ₂) :
    OrdinaryPair (antitranspose F) χ₁.at χ₂.at := by
  have hmix : ∀ χ : Chart, ¬ χ.ω.case.IsMixed → ¬ χ.at.ω.case.IsMixed := by
    intro χ hχ
    change ¬ χ.ω.case.anti.IsMixed
    unfold AttachCase.IsMixed at hχ ⊢
    cases hh : χ.ω.case <;> simp_all [AttachCase.anti]
  exact ⟨h.proper₁.at h.nonempty₁, h.proper₂.at h.nonempty₂,
    Chart.IsChartOf.at h.proper₁ h.ordinary₁ h.chart₁,
    Chart.IsChartOf.at h.proper₂ h.ordinary₂ h.chart₂, hmix _ h.ordinary₁, hmix _ h.ordinary₂,
    antitranspose_nonempty_iff.mpr h.nonempty₁, antitranspose_nonempty_iff.mpr h.nonempty₂,
    by change ¬ (MarkedInner.period χ₁.ω.anti).toNat ∣ (MarkedInner.period χ₂.ω.anti).toNat
       rw [MarkedInner.period_anti, MarkedInner.period_anti]; exact h.nondiv₁,
    by change ¬ (MarkedInner.period χ₂.ω.anti).toNat ∣ (MarkedInner.period χ₁.ω.anti).toNat
       rw [MarkedInner.period_anti, MarkedInner.period_anti]; exact h.nondiv₂⟩

theorem GcdData.at {F : Diagram} {χ₁ χ₂ : Chart} {g a b c d M wg : ℕ}
    (hd : GcdData F χ₁ χ₂ g a b c d M wg) : GcdData (antitranspose F) χ₁.at χ₂.at g a b c d M wg :=
        by
  refine ⟨?_, ?_, ?_, hd.coprime, hd.a_ge, hd.c_ge, ?_, hd.wg_lt, ?_, ?_⟩
  · change g = Nat.gcd (MarkedInner.period χ₁.ω.anti).toNat (MarkedInner.period χ₂.ω.anti).toNat
    rw [MarkedInner.period_anti, MarkedInner.period_anti]; exact hd.g_eq
  · change (MarkedInner.period χ₁.ω.anti).toNat = a * g
    rw [MarkedInner.period_anti]; exact hd.period₁
  · change (MarkedInner.period χ₂.ω.anti).toNat = c * g
    rw [MarkedInner.period_anti]; exact hd.period₂
  · rw [span_antitranspose]; exact hd.span_eq
  · change (MarkedInner.width χ₁.ω.anti) = b * g + wg
    rw [MarkedInner.width_anti]; exact hd.width₁
  · change (MarkedInner.width χ₂.ω.anti) = d * g + wg
    rw [MarkedInner.width_anti]; exact hd.width₂

/-- **`prop:gluing-ordinary-fold`.**  Two ordinary proper legal roots of nondividing periods with
nonempty marks, whose gcd `g` exceeds one, have a proper legal root of period `g`.  The setting is
`eq:gluing-gcd-data` (`GcdData`).  The root has the empty mark when the remainder `w_g` is zero, the
singleton mark when `w_g = 1`, and the folded mark of the paper otherwise. -/
theorem OrdinaryPair.exists_gcd_root {F : Diagram} {χ₁ χ₂ : Chart} (h : OrdinaryPair F χ₁ χ₂)
    {g a b c d M wg : ℕ} (hd : GcdData F χ₁ χ₂ g a b c d M wg) (hg : 1 < g) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period = g ∧ χ.ω.width = wg := by
  by_cases hca : χ₁.ω.case = .a
  · obtain ⟨χ, h1, h2, h3, -, -, h6⟩ := h.exists_root_case_a hca hd hg
    exact ⟨χ, h1, h2, h3, h6⟩
  · have hcb : χ₁.ω.case = .b := by
      have := h.ordinary₁
      unfold AttachCase.IsMixed at this
      cases hh : χ₁.ω.case <;> simp_all
    have hca' : χ₁.at.ω.case = .a := by
      change χ₁.ω.case.anti = .a
      rw [hcb]; rfl
    obtain ⟨χ', h1, h2, h3, h4, h5, h6⟩ := h.at.exists_root_case_a hca' hd.at hg
    obtain ⟨χ, k1, k2, k3, k4⟩ := Chart.exists_root_of_at h1 h2 h4 h5
    exact ⟨χ, k1, k2, by rw [k3]; exact h3, by rw [k4]; exact h6⟩

/-- **The remainder `w_g = 0`**: the root has the empty mark. -/
theorem OrdinaryPair.exists_gcd_root_empty {F : Diagram} {χ₁ χ₂ : Chart}
    (h : OrdinaryPair F χ₁ χ₂) {g a b c d M : ℕ} (hd : GcdData F χ₁ χ₂ g a b c d M 0)
    (hg : 1 < g) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period = g ∧ χ.ω.W = ∅ := by
  obtain ⟨χ, h1, h2, h3, h4⟩ := h.exists_gcd_root hd hg
  refine ⟨χ, h1, h2, h3, ?_⟩
  have : span χ.ω.W = 0 := h4
  unfold span contents at this
  rw [Finset.card_eq_zero, Finset.image_eq_empty] at this
  exact this

/-- **The remainder `w_g = 1`**: the root has a one-cell (singleton) mark. -/
theorem OrdinaryPair.exists_gcd_root_singleton {F : Diagram} {χ₁ χ₂ : Chart}
    (h : OrdinaryPair F χ₁ χ₂) {g a b c d M : ℕ} (hd : GcdData F χ₁ χ₂ g a b c d M 1)
    (hg : 1 < g) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period = g ∧ χ.ω.W.card = 1 := by
  obtain ⟨χ, h1, h2, h3, h4⟩ := h.exists_gcd_root hd hg
  refine ⟨χ, h1, h2, h3, ?_⟩
  have hwid : span χ.ω.W = 1 := h4
  have hWne : χ.ω.W.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    simp [span, contents, hcon] at hwid
  have hnon : χ.ω.IsNonemptyMark := by
    rcases h1.2.2.2.1.2 with hemp | hnon
    · exact absurd hemp.1 hWne.ne_empty
    · exact hnon
  have hWcs := hnon.2.1
  have hsp := span_eq_of_isConnectedSkew hWcs
  rw [hwid] at hsp
  rw [Finset.card_eq_one]
  have hsw := sw_mem hWne
  refine ⟨sw χ.ω.W, ?_⟩
  ext x
  rw [Finset.mem_singleton]
  constructor
  · intro hx
    have c1 := minContent_le (content_mem_contents hx)
    have c2 := le_maxContent (content_mem_contents hx)
    exact MarkedInner.eq_sw_of_content hWcs hx (by omega)
  · rintro rfl
    exact hsw

/-! ### Checked examples -/

/-- The row `(14)` has the ordinary roots of periods `4` and `6`, hence a proper legal root of
period `g = 2` with the empty mark. -/
example : ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf (skewOf [14] []) ∧ χ.period = 2 ∧
    χ.ω.W = ∅ :=
  ordFold_row_ordinaryPair.exists_gcd_root_empty ordFold_row_gcdData (by norm_num)

/-- The row `(5)` with the singleton mark of period four. -/
def ordFold_rowFiveMark : MarkedInner where
  E := skewOf [5] []
  W := {(0, 0)}
  v := (0, 4)
  case := .a

/-- The row `(7)` with the singleton mark of period six. -/
def ordFold_rowSevenMark : MarkedInner where
  E := skewOf [7] []
  W := {(0, 0)}
  v := (0, 6)
  case := .a

example : ordFold_rowFiveMark.IsLegal := by decide +kernel
example : ordFold_rowSevenMark.IsLegal := by decide +kernel

/-- Two ordinary roots of the row `(13)`, of periods `4` and `6` and width one. -/
theorem ordFold_row13_ordinaryPair : OrdinaryPair (skewOf [13] [])
    ⟨skewOf [3] [], ordFold_rowFiveMark⟩ ⟨skewOf [2] [], ordFold_rowSevenMark⟩ := by
  refine ⟨?_, ?_, ⟨0, ?_⟩, ⟨0, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Chart.IsProperLegal; decide +kernel
  · unfold Chart.IsProperLegal; decide +kernel
  · decide +kernel
  · decide +kernel
  all_goals decide +kernel

/-- The setting `eq:gluing-gcd-data` for the two roots of the row `(13)`: `g = 2`, `w_g = 1`. -/
theorem ordFold_row13_gcdData : GcdData (skewOf [13] [])
    ⟨skewOf [3] [], ordFold_rowFiveMark⟩ ⟨skewOf [2] [], ordFold_rowSevenMark⟩ 2 2 0 3 0 6 1 := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by norm_num, ?_, by norm_num, ?_, ?_⟩ <;>
    decide +kernel

/-- The row `(13)` has the ordinary roots of periods `4` and `6` with singleton marks (`w_g = 1`),
hence a proper legal root of period `g = 2` with a one-cell mark. -/
example : ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf (skewOf [13] []) ∧ χ.period = 2 ∧
    χ.ω.W.card = 1 :=
  ordFold_row13_ordinaryPair.exists_gcd_root_singleton ordFold_row13_gcdData (by norm_num)

/-- The row `(8)` with the two-cell mark of period six. -/
def ordFold_rowEightMark : MarkedInner where
  E := skewOf [8] []
  W := {(0, 0), (0, 1)}
  v := (0, 6)
  case := .a

/-- The row `(11)` with the two-cell mark of period nine. -/
def ordFold_rowElevenMark : MarkedInner where
  E := skewOf [11] []
  W := {(0, 0), (0, 1)}
  v := (0, 9)
  case := .a

example : ordFold_rowEightMark.IsLegal := by decide +kernel
example : ordFold_rowElevenMark.IsLegal := by decide +kernel

/-- Two ordinary roots of the row `(20)`, of periods `6` and `9` and width two. -/
theorem ordFold_row20_ordinaryPair : OrdinaryPair (skewOf [20] [])
    ⟨skewOf [3] [], ordFold_rowEightMark⟩ ⟨skewOf [2] [], ordFold_rowElevenMark⟩ := by
  refine ⟨?_, ?_, ⟨0, ?_⟩, ⟨0, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Chart.IsProperLegal; decide +kernel
  · unfold Chart.IsProperLegal; decide +kernel
  · decide +kernel
  · decide +kernel
  all_goals decide +kernel

/-- The setting `eq:gluing-gcd-data` for the two roots of the row `(20)`: `g = 3`, `w_g = 2`. -/
theorem ordFold_row20_gcdData : GcdData (skewOf [20] [])
    ⟨skewOf [3] [], ordFold_rowEightMark⟩ ⟨skewOf [2] [], ordFold_rowElevenMark⟩ 3 2 0 3 0 6 2 := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by norm_num, ?_, by norm_num, ?_, ?_⟩ <;>
    decide +kernel

/-- The row `(20)` has the ordinary roots of periods `6` and `9` with two-cell marks
(`w_g = 2`), hence a proper legal root of period `g = 3` and width two: the folded mark. -/
example : ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf (skewOf [20] []) ∧ χ.period = 3 ∧
    χ.ω.width = 2 :=
  ordFold_row20_ordinaryPair.exists_gcd_root ordFold_row20_gcdData (by norm_num)

end SkewGluing
