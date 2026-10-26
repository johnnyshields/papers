import SkewGluing.MixedPairs
import SkewGluing.MixedFold.Root

/-!
# The mixed fold

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`).

`gluing_mixed_fold` is the statement of `prop:gluing-mixed-fold`: two same-case mixed proper roots
of nondividing periods with `gcd p Q = g > 1` give a proper legal period-`g` root of the same case,
whose width is the remainder `N_F mod g`, which is positive (`TwoRoots.mixed_pairs_remainder_zero`);
at remainder one its marked copy is a single cell, and at `g = 2` its inner is the three-cell hook
(`MarkedInner.IsLegalNonempty.eq_hook`; case (c) by rotation).

The construction of the period-`g` root of two case-(d) roots, `mixFold_exists_root_d`, is built in
`SkewGluing.MixedFold.*`: the word analysis (generic bits, zero drift, concentration of the phases,
the pinches: `eq:gluing-mixed-phases`, `eq:gluing-mixed-heights`,
`eq:gluing-original-mixed-mark`), the inner and its legal mark, the outer
(`eq:gluing-mixed-inverse`) and the identity with the parent.  The worked example at the end
(`g = 2`, remainder one) is checked by `decide`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner}

/-- A legal case-(d) mark of width one and period two lives on the three-cell hook: its inner is a
translate of `(2, 1)`, its displacement is `(-1, 1)` and its marked copy is the single cell at the
southwest end. -/
theorem IsLegalNonempty.eq_hook (h : ω.IsLegalNonempty) (hcd : ω.case = .d) (hw : ω.width = 1)
    (hq : ω.period = 2) :
    ∃ x : ℤ × ℤ, ω.W = {x} ∧ ω.v = (-1, 1) ∧
      ω.E = SkewGluing.translate (x.1 - 1, x.2) (skewOf [2, 1] []) := by
  have hn := h.nonemptyMark
  obtain ⟨hWne, hWc, hWE, hUE, hsw, hneU, -⟩ := hn
  have hE := h.isConnectedSkew_E
  have hEne : ω.E.Nonempty := hE.2.1
  -- the marked copy is one cell
  have hcard : ω.W.card = 1 := by
    have h1 : ω.W.card ≤ 1 := by
      by_contra hcon
      have := two_le_span_of_two_le_card hWc (by omega)
      unfold MarkedInner.width at hw
      omega
    have := hWne.card_pos
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  have hsx : sw ω.E = x := by
    have := hsw; rw [hx] at this; simpa using this
  have hup : ω.upper = {x + ω.v} := by
    unfold upper; rw [hx]; simp [SkewGluing.translate]
  have hnx : ne ω.E = x + ω.v := by
    have := hneU; rw [hup] at this; simpa using this
  obtain ⟨⟨y, hy, hyc, hyW⟩, -⟩ := h.attach.2.2.2 hcd
  obtain ⟨-, ⟨z, hz, hzc, hzU⟩⟩ := h.attach.2.2.2 hcd
  rw [hx] at hyW
  rw [hup] at hzU
  have hyW' : (y.1 + 1, y.2) = x := by simpa using hyW
  have hzU' : (z.1, z.2 + 1) = x + ω.v := by simpa using hzU
  have hyE : y ∈ ω.E := (Finset.mem_sdiff.mp hy).1
  have hzE : z ∈ ω.E := (Finset.mem_sdiff.mp hz).1
  have hq1 : ω.lo (ω.period - 1) = ω.hi (ω.period - 1) := h.lo_pred_period_eq_hi
  have hspan := h.span_eq
  have hsp3 : (span ω.E : ℤ) = 3 := by
    have : (ω.width : ℤ) = 1 := by exact_mod_cast hw
    unfold widthZ at *; omega
  have hmc : minContent ω.E = content x := by
    rw [← hsx, content_sw hEne]
  -- the contents of `y` and `z`
  have hcy : content y = content x + 1 := by
    obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
    simp only [content, Prod.mk.injEq] at hyW' ⊢; omega
  have hcz : content z = content x + 1 := by
    have e := congrArg content hzU'
    have : content (x + ω.v) = content x + content ω.v := content_add _ _
    have hcv : content ω.v = 2 := hq
    simp only [content] at e this hcv ⊢
    omega
  have hyz : y = z := by
    have hs : diagLo ω.E (minContent ω.E + 1) = diagHi ω.E (minContent ω.E + 1) := by
      have := hq1; rw [hq] at this
      unfold lo hi at this
      simpa using this
    exact eq_of_singleton_diag hs hyE hzE (by rw [hcy, hmc]) (by rw [hcz, hmc])
  subst hyz
  have hv1 : ω.v = (-1, 1) := by
    have e1 := congrArg Prod.fst hzU'
    have e2 := congrArg Prod.snd hzU'
    have f1 := congrArg Prod.fst hyW'
    have f2 := congrArg Prod.snd hyW'
    simp only [Prod.fst_add, Prod.snd_add] at e1 e2 f1 f2
    ext <;> simp <;> omega
  refine ⟨x, hx, hv1, ?_⟩
  -- the three cells of `E`
  have hcont : ∀ e ∈ ω.E, content e = content x ∨ content e = content x + 1 ∨
      content e = content x + 2 := by
    intro e he
    have h1 := minContent_le (content_mem_contents he)
    have h2 := le_maxContent (content_mem_contents he)
    have : maxContent ω.E = minContent ω.E + 2 := by
      have := span_eq_of_isConnectedSkew hE; omega
    omega
  have hxne : x + ω.v = ne ω.E := hnx.symm
  have hs1 : diagLo ω.E (minContent ω.E + 1) = diagHi ω.E (minContent ω.E + 1) := by
    have := hq1; rw [hq] at this; unfold lo hi at this; simpa using this
  have hEeq : ω.E = {x, y, x + ω.v} := by
    ext e
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro he
      rcases hcont e he with h0 | h0 | h0
      · left
        rw [← hsx]; exact eq_sw_of_content hE he (by rw [h0, hmc])
      · right; left
        exact eq_of_singleton_diag hs1 he hyE (by rw [h0, hmc]) (by rw [hcy, hmc])
      · right; right
        rw [hxne]; exact eq_ne_of_content hE he (by
          have := span_eq_of_isConnectedSkew hE; omega)
    · rintro (rfl | rfl | rfl)
      · rw [← hsx]; exact sw_mem hEne
      · exact hyE
      · rw [hxne]; exact ne_mem hEne
  rw [hEeq, hv1]
  have hk : skewOf [2, 1] [] = {(0, 0), (0, 1), (1, 0)} := by decide
  rw [hk]
  have hy1 : y = (x.1 - 1, x.2) := by
    obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
    simp only [Prod.mk.injEq] at hyW' ⊢; omega
  rw [hy1]
  obtain ⟨a, b⟩ := x
  ext e
  simp only [SkewGluing.translate, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨(1, 0), by simp, by ext <;> simp⟩
    · exact ⟨(0, 0), by simp, by ext <;> simp⟩
    · exact ⟨(0, 1), by simp, by ext <;> simp <;> omega⟩
  · rintro ⟨z, hz, rfl⟩
    rcases hz with rfl | rfl | rfl
    · right; left; ext <;> simp
    · right; right; ext <;> simp <;> omega
    · left; ext <;> simp

end MarkedInner

/-! ### Facts about a root of period `g` -/

theorem Chart.IsProperLegal.width_eq_span_mod {F : Diagram} {χ : Chart} (h : χ.IsProperLegal)
    (hF : χ.IsChartOf F) : χ.ω.width = span F % χ.ω.period.toNat := by
  obtain ⟨v, hv⟩ := hF
  have hq := h.2.2.2.period_pos
  have h1 := h.2.2.2.width_eq_span_emod h.1
  have hs : span F = span (χ.ω.compose χ.D) := by rw [hv, span_translate]; rfl
  rw [hs]
  have hqz : ((χ.ω.period.toNat : ℕ) : ℤ) = χ.ω.period := Int.toNat_of_nonneg (by omega)
  rw [← hqz] at h1
  exact_mod_cast h1

theorem Chart.IsProperLegal.exists_singleton_of_width_eq_one {χ : Chart} (h : χ.IsProperLegal)
    (hw : χ.ω.width = 1) : ∃ x : ℤ × ℤ, χ.ω.W = {x} := by
  have hWne : χ.ω.W.Nonempty := by
    by_contra hcon
    have := MarkedInner.width_eq_zero_of_eq_empty (Finset.not_nonempty_iff_eq_empty.mp hcon)
    omega
  have hmark := (show χ.ω.IsLegalNonempty from ⟨h.2.2.2, hWne⟩).nonemptyMark
  have hWc := hmark.2.1
  have h1 : χ.ω.W.card ≤ 1 := by
    by_contra hcon
    have := two_le_span_of_two_le_card hWc (by omega)
    unfold MarkedInner.width at hw
    omega
  exact Finset.card_eq_one.mp (le_antisymm h1 hWne.card_pos)

/-- The boundary coding, the private heights and the first interface relation of a proper legal
case-(d) chart `χ` of `F`, on the words of `F`, for some middle phases. -/
theorem mixFold_chart_data {F : Diagram} {χ : Chart} (h : χ.IsProperLegal) (hF : χ.IsChartOf F)
    (hd : χ.ω.case = .d) :
    ∃ s t : ℤ, MixFoldCoding (wordA F) (wordB F) (span F) χ.ω.period.toNat χ.ω.width .d s t ∧
      MixFoldExtra (wordA F) (wordB F) (span F) χ.ω.period.toNat χ.ω.width s t ∧
      0 < χ.ω.width := by
  have hw := TwoRoots.width_pos_of_mixed h (Or.inr hd)
  have hW : χ.ω.W.Nonempty := by
    by_contra hcon
    have := MarkedInner.width_eq_zero_of_eq_empty (Finset.not_nonempty_iff_eq_empty.mp hcon)
    omega
  have hl : χ.ω.IsLegalNonempty := ⟨h.2.2.2, hW⟩
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := id hph
  have hcod := (h.mixFoldCoding_of_chartOf hF).2 s t hW hph
  rw [hd] at hcod
  have hP : IsConnectedSkew χ.parent := h.2.2.2.isConnectedSkew_compose h.1
  obtain ⟨v, hv⟩ := hF
  have hspan : span F = span χ.parent := by rw [hv, span_translate]
  have hD2 : 2 ≤ span χ.D := two_le_span_of_two_le_card h.1 h.2.1
  have hx := hl.mixFold_extra h.1 hD2 hd hph
  have hwq := hcod.w_lt
  have hN := hcod.two_q_add_w_le
  have hx' : MixFoldExtra (wordA χ.parent) (wordB χ.parent) (span F) χ.ω.period.toNat χ.ω.width
      s t := by
    rw [hspan]; exact hx
  refine ⟨s, t, hcod, ?_, hw⟩
  refine hx'.of_agree hcod.q_pos hs1 hs2 ht1 ht2 (fun k h1 h2 => ?_) (fun k h1 h2 => ?_)
    (by omega)
  · rw [hv]
    exact (wordA_translate hP v h1 (by omega)).symm
  · rw [hv]
    exact (wordB_translate hP v h1 (by omega)).symm

/-- **The construction of the period-`g` root of two case-(d) roots** (the construction paragraph
of the proof of `prop:gluing-mixed-fold`).

The proof is on the bit words of the parent: the word data `MixFoldFold` of the folded root is
derived from the two codings (`MixFoldPair.fold_facts`: non-collision of the phases
(`lem:gluing-collision`), generic bits (`lem:gluing-periods` (ii)), zero drift, concentration of
the phases, `eq:gluing-mixed-phases`, the pinches and the block relation); the inner `G` and its
mark are built from those words, with legality I–IV read off the diagonal data
(`MixFoldDiag.legal`); the outer is `eq:gluing-mixed-inverse` and the composite is compared with `F`
on bit words (`MixFoldFold.exists_chart`).

**Differs from the paper's route.**  The paper marks the retained copies by deleting cells of `G`;
here the copy is the full intersection `W₋ = G ∩ (G - v)` of `lem:gluing-local` (1), and the
legality conditions are checked on its diagonal rows. -/
theorem mixFold_exists_root_d {F : Diagram} {χ₁ χ₂ : Chart} (T : TwoRoots F χ₁ χ₂)
    (_hg : 1 < Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) (h₁ : χ₁.ω.case = .d)
    (h₂ : χ₂.ω.case = .d) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧
      χ.ω.period.toNat = Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ∧ χ.ω.case = .d := by
  have hrem : 0 < span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat := by
    by_contra hcon
    exact (TwoRoots.mixed_pairs_remainder_zero T (by omega)).1 (Or.inr h₁)
  have hFc : IsConnectedSkew F := by
    obtain ⟨v, hv⟩ := T.chart₁
    rw [hv]
    exact isConnectedSkew_translate v (T.proper₁.2.2.2.isConnectedSkew_compose T.proper₁.1)
  obtain ⟨s₁, t₁, c₁, x₁, hw₁⟩ := mixFold_chart_data T.proper₁ T.chart₁ h₁
  obtain ⟨s₂, t₂, c₂, x₂, hw₂⟩ := mixFold_chart_data T.proper₂ T.chart₂ h₂
  have P : MixFoldPair (wordA F) (wordB F) (span F) χ₁.ω.period.toNat χ₂.ω.period.toNat
      χ₁.ω.width χ₂.ω.width s₁ t₁ s₂ t₂ :=
    ⟨c₁, c₂, x₁, x₂, MixFoldWordsOK.of_isConnectedSkew hFc, hw₁, hw₂, T.not_dvd₁, T.not_dvd₂,
      hrem⟩
  obtain ⟨M, v, α, β, hfold⟩ := P.fold_facts
  obtain ⟨χ, hχ, hF', hper, hcase, -⟩ := hfold.exists_chart hFc
  exact ⟨χ, hχ, hF', hper, hcase⟩

/-- **`prop:gluing-mixed-fold`.**  Two same-case mixed proper roots `χ₁`, `χ₂` of one parent `F`, of
nondividing periods `p`, `Q` with `g = gcd p Q > 1`, have a proper legal period-`g` root `χ` of the
same case.  Its width is the remainder `w_g = N_F mod g`, which is positive; at remainder one its
marked copy is a single cell, and at `g = 2` its inner is the three-cell hook `(2, 1)` (for case
(d); the rotated hook for case (c)). -/
theorem gluing_mixed_fold {F : Diagram} {χ₁ χ₂ : Chart} (T : TwoRoots F χ₁ χ₂)
    (hg : 1 < Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) (hsame : χ₁.ω.case = χ₂.ω.case)
    (hmix : χ₁.ω.case.IsMixed) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧
      χ.ω.period.toNat = Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ∧
      χ.ω.case = χ₁.ω.case ∧
      0 < span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ∧
      χ.ω.width = span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ∧
      (span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat = 1 → ∃ x : ℤ × ℤ, χ.ω.W = {x}) ∧
      (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat = 2 →
        (χ₁.ω.case = .d → ∃ v : ℤ × ℤ, χ.ω.E = translate v (skewOf [2, 1] [])) ∧
        (χ₁.ω.case = .c → ∃ v : ℤ × ℤ, χ.ω.E = translate v (rotate (skewOf [2, 1] [])))) := by
  have hrem : 0 < span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat := by
    by_contra hcon
    exact (TwoRoots.mixed_pairs_remainder_zero T (by omega)).1 hmix
  -- the root, for case (d), and for case (c) by rotation
  have key : ∀ {F : Diagram} {χ₁ χ₂ : Chart}, TwoRoots F χ₁ χ₂ →
      1 < Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat → χ₁.ω.case = .d → χ₂.ω.case = .d →
      0 < span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat →
      ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧
        χ.ω.period.toNat = Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ∧ χ.ω.case = .d ∧
        0 < span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ∧
        χ.ω.width = span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat ∧
        (span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat = 1 → ∃ x : ℤ × ℤ, χ.ω.W = {x}) ∧
        (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat = 2 →
          ∃ v : ℤ × ℤ, χ.ω.E = translate v (skewOf [2, 1] [])) := by
    intro F χ₁ χ₂ T hg h₁ h₂ hrem
    obtain ⟨χ, hχ, hF, hper, hcase⟩ := mixFold_exists_root_d T hg h₁ h₂
    have hwid := hχ.width_eq_span_mod hF
    rw [hper] at hwid
    refine ⟨χ, hχ, hF, hper, hcase, hrem, hwid, fun h1 => ?_, fun h2 => ?_⟩
    · exact hχ.exists_singleton_of_width_eq_one (by rw [hwid]; exact h1)
    · have hw1 : χ.ω.width = 1 := by
        have hlt : span F % Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat < 2 := by
          rw [h2]; exact Nat.mod_lt _ (by norm_num)
        omega
      have hWne : χ.ω.W.Nonempty := by
        by_contra hcon
        have := MarkedInner.width_eq_zero_of_eq_empty (Finset.not_nonempty_iff_eq_empty.mp hcon)
        omega
      obtain ⟨x, -, -, hE⟩ := (show χ.ω.IsLegalNonempty from ⟨hχ.2.2.2, hWne⟩).eq_hook hcase hw1
        (by
          have hq := hχ.2.2.2.period_pos
          have : (χ.ω.period.toNat : ℤ) = χ.ω.period := Int.toNat_of_nonneg (by omega)
          rw [hper, h2] at this
          exact_mod_cast this.symm)
      exact ⟨_, hE⟩
  rcases hmix with hc | hd
  · -- case (c): rotate both charts, fold, and rotate back
    have hc2 : χ₂.ω.case = .c := hsame ▸ hc
    have T' := T.rotate
    have hg' : 1 < Nat.gcd χ₁.rotate.ω.period.toNat χ₂.rotate.ω.period.toNat := by
      rw [TwoRoots.rotate_period, TwoRoots.rotate_period]; exact hg
    have hrem' : 0 < span (rotate F) %
        Nat.gcd χ₁.rotate.ω.period.toNat χ₂.rotate.ω.period.toNat := by
      rw [TwoRoots.span_rotate_eq, TwoRoots.rotate_period, TwoRoots.rotate_period]; exact hrem
    obtain ⟨χ, hχ, hF, hper, hcase, -, hwid, hsing, hhook⟩ :=
      key T' hg' (TwoRoots.rotate_case_d hc) (TwoRoots.rotate_case_d hc2) hrem'
    rw [TwoRoots.rotate_period, TwoRoots.rotate_period] at hper hwid hsing hhook
    rw [TwoRoots.span_rotate_eq] at hwid hsing
    refine ⟨χ.rotate, hχ.rotate, ?_, ?_, ?_, hrem, ?_, ?_, ?_⟩
    · have := TwoRoots.chart_rotate hχ hF
      rwa [rotate_rotate] at this
    · rw [TwoRoots.rotate_period]; exact hper
    · change χ.ω.case.rotate = _; rw [hcase, hc]; rfl
    · rw [show χ.rotate.ω.width = χ.ω.width from MarkedInner.width_rotate _]; exact hwid
    · intro h1
      obtain ⟨x, hx⟩ := hsing h1
      refine ⟨-(x + χ.ω.v), ?_⟩
      change rotate χ.ω.upper = _
      rw [MarkedInner.upper, hx]
      simp [translate, rotate]
    · intro h2
      refine ⟨fun hd' => absurd (hd'.symm.trans hc) (by decide), fun _ => ?_⟩
      obtain ⟨v, hv⟩ := hhook h2
      refine ⟨-v, ?_⟩
      change rotate χ.ω.E = _
      rw [hv, rotate_translate_eq]
  · have hd2 : χ₂.ω.case = .d := hsame ▸ hd
    obtain ⟨χ, hχ, hF, hper, hcase, -, hwid, hsing, hhook⟩ := key T hg hd hd2 hrem
    refine ⟨χ, hχ, hF, hper, by rw [hcase, hd], hrem, hwid, hsing, fun h2 => ⟨fun _ => hhook h2,
      fun hc => absurd (hd.symm.trans hc) (by decide)⟩⟩

/-! ### Checked examples

The parent `F = (3) ∘_{ω₄} E₄ = (2) ∘_{ω₆} E₆` of span `15` has two case-(d) roots, of periods
`4` and `6` (`g = 2`, remainder one); it is also `(7) ∘_ω (2, 1)` for the singleton hook mark. -/

section Examples

/-- A case-(d) mark of period four and width three. -/
def mixedInnerFour : MarkedInner where
  E := {(0, 2), (0, 3), (1, 1), (1, 2), (2, 0), (2, 1), (3, 0)}
  W := {(2, 0), (2, 1), (3, 0)}
  v := (-2, 2)
  case := .d

/-- A case-(d) mark of period six and width three. -/
def mixedInnerSix : MarkedInner where
  E := {(0, 3), (0, 4), (1, 2), (1, 3), (2, 1), (2, 2), (3, 0), (3, 1), (4, 0)}
  W := {(3, 0), (3, 1), (4, 0)}
  v := (-3, 3)
  case := .d

example : mixedInnerFour.IsLegal ∧ mixedInnerSix.IsLegal := by decide +kernel

/-- The two roots of the parent `F`. -/
def mixedRootFour : Chart := ⟨skewOf [3] [], mixedInnerFour⟩

def mixedRootSix : Chart := ⟨skewOf [2] [], mixedInnerSix⟩

example : mixedRootFour.parent = translate (-1, 0) mixedRootSix.parent := by
  decide +kernel

example : span mixedRootFour.parent = 15 := by decide +kernel

/-- The two roots form a `TwoRoots` pair: proper, legal, nondividing periods. -/
theorem mixedRoots_twoRoots : TwoRoots mixedRootFour.parent mixedRootFour mixedRootSix := by
  refine ⟨?_, ?_, ⟨0, by simp [translate_zero]⟩, ⟨(-1, 0), ?_⟩, by decide, by decide⟩
  · unfold Chart.IsProperLegal
    decide +kernel
  · unfold Chart.IsProperLegal
    decide +kernel
  · have : mixedRootFour.parent = translate (-1, 0) mixedRootSix.parent := by decide +kernel
    exact this

/-- `lem:gluing-incompatible` on the example: the two mixed roots have equal cases. -/
example : mixedRootFour.ω.case = mixedRootSix.ω.case :=
  TwoRoots.gluing_incompatible mixedRoots_twoRoots (Or.inl (Or.inr rfl))

/-- The fixed boundary `B` of the parent `F` has period `gcd 4 6 = 2`. -/
example : PeriodWords.PeriodExcept (span mixedRootFour.parent - 1) 2 ∅
    (wordB mixedRootFour.parent) := by
  have := TwoRoots.fixed_boundary_d mixedRoots_twoRoots rfl (fun h => by cases h)
  have e : Nat.gcd mixedRootFour.ω.period.toNat mixedRootSix.ω.period.toNat = 2 := by
    decide +kernel
  rwa [e] at this

/-- `lem:gluing-collision` on the example (`g = 2`, `N_F = 15`, `w_g = 1`): both words are
`2`-periodic, so the middle phases of the period-four root are not both even. -/
example : ∀ s t : ℤ, mixedInnerFour.IsPhases s t → ¬ (s % 2 = 0 ∧ t % 2 = 0) := by
  intro s t hph
  have hspan : span mixedRootFour.parent = 15 := by decide +kernel
  have hB : PeriodWords.PeriodExcept (span mixedRootFour.parent - 1) 2 ∅
      (wordB mixedRootFour.parent) := by rw [hspan]; decide +kernel
  have hA : PeriodWords.PeriodExcept (span mixedRootFour.parent - 1) 2 {0}
      (wordA mixedRootFour.parent) := by rw [hspan]; decide +kernel
  have := gluing_collision (R := 0) (g := 2) (χ := mixedRootFour) (F := mixedRootFour.parent)
    (mixedRoots_twoRoots.proper₁) ⟨0, by simp [translate_zero]⟩ rfl (by norm_num)
    (by decide +kernel) (by rw [hspan]; decide) hB hA hph
  exact this

/-- The fold: the period-two root `(7) ∘_ω (2, 1)` with the singleton hook mark has the same
parent, up to translation. -/
example : translate (2, 0) (MarkedInner.compose (skewOf [7] []) hookInner) =
    mixedRootFour.parent := by
  decide +kernel

end Examples

end SkewGluing
