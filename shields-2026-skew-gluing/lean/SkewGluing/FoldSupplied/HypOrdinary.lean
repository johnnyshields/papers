import SkewGluing.FoldSupplied.Ordinary
import SkewGluing.OrdinaryFold
import SkewGluing.Lines.FirstWindow
import SkewGluing.FoldSupplied.HypAnti

/-!
# `prop:gluing-ordinary-fold`: the class hypotheses of the fold from the two roots

Formalizes `shields-2026-skew-gluing.tex`, «Two ordinary roots» (`prop:gluing-ordinary-fold`,
`lem:gluing-periods` (ii)): two ordinary proper roots of nondividing periods `p`, `Q` with
`g = gcd (p, Q) > 1` make the boundary words of the parent follow generic bits modulo `g` off the
simultaneous holes.  Restricted to the first `p`-window, which is the window of the supplied inner
`E` of the first chart, this makes every residue class modulo `g` of the completed native lists
of `E`, other than those of the contacts, full or empty:

* `FoldSupplied.fullOrEmptyOff_of_residues`: the residue-class bookkeeping;
* `FoldSupplied.fullOrEmptyOff_col`, `FoldSupplied.fullOrEmptyOff_row`: the two native lists, from
  the generic bits of the parent; at residue zero the value is read at the actual step `p`;
* `FoldSupplied.ordinary_fold_of_roots_a`: the ordinary fold of the supplied inner of a first chart
  of case (a), lifted to the parent, with no hypothesis beyond the two roots;
* `FoldSupplied.ordinary_fold_of_roots`: the same for either ordinary case, the case (b) being the
  antitransposed comparison transported back (`FoldSupplied.ordinary_transport`).

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open OrdinaryDrift OrdinaryFold SmallOverlap MarkedInner

/-- A set whose members in the window `[1, p)` follow a function of the residue modulo `g`, off the
residue of `ex`, and whose zero member follows it when the residue of `ex` is nonzero, meets every
other residue class modulo `g` in all of it or none of it. -/
theorem fullOrEmptyOff_of_residues {S : Finset ℕ} {g p ex : ℕ} (hg : 0 < g) (hgr : g ∣ p)
    (V : ℕ → ℤ)
    (hS : ∀ k, 1 ≤ k → k < p → k % g ≠ ex % g → (k ∈ S ↔ V (k % g) = 1))
    (h0 : ex % g ≠ 0 → (0 ∈ S ↔ V 0 = 1)) : FullOrEmptyOff S g p ex := by
  intro ρ hρ hne
  have key : ∀ j, j < p / g → (j * g + ρ ∈ S ↔ V ρ = 1) := by
    intro j hj
    obtain ⟨R, hR⟩ := hgr
    have hjR : j < R := by
      rw [hR, Nat.mul_div_cancel_left _ hg] at hj
      exact hj
    have hjp : j * g + ρ < p := by
      rw [hR]
      have : (j + 1) * g ≤ R * g := Nat.mul_le_mul_right g hjR
      nlinarith
    have hmod : (j * g + ρ) % g = ρ := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hρ]
    by_cases h00 : j = 0 ∧ ρ = 0
    · obtain ⟨rfl, rfl⟩ := h00
      simpa using h0 (fun h => hne h.symm)
    · have h1 : 1 ≤ j * g + ρ := by
        by_contra hcon
        apply h00
        have e1 : j * g = 0 := by omega
        have e2 : ρ = 0 := by omega
        refine ⟨?_, e2⟩
        rcases Nat.mul_eq_zero.mp e1 with h | h
        · exact h
        · omega
      have := hS (j * g + ρ) h1 hjp (by rw [hmod]; exact hne)
      rwa [hmod] at this
  by_cases hV : V ρ = 1
  · exact Or.inl fun j hj => (key j hj).mpr hV
  · exact Or.inr fun j hj hm => hV ((key j hj).mp hm)

variable {ω : MarkedInner} {D : Diagram}

theorem wordA_E_eq_compose (hl : ω.IsLegalNonempty) (hD : IsConnectedSkew D) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k < ω.period.toNat) : wordA ω.E (k : ℤ) = wordA (ω.compose D) (k : ℤ) := by
  have hc := hl.1.period_toNat_cast
  exact (hl.1.wordA_compose_first hD (by exact_mod_cast hk1) (by omega)).symm

theorem wordB_E_eq_compose (hl : ω.IsLegalNonempty) (hD : IsConnectedSkew D) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k < ω.period.toNat) : wordB ω.E (k : ℤ) = wordB (ω.compose D) (k : ℤ) := by
  have hc := hl.1.period_toNat_cast
  exact (hl.1.wordB_compose_first hD (by exact_mod_cast hk1) (by omega)).symm

theorem period_le_span_compose (hl : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hD2 : 2 ≤ span D) : ω.period.toNat < span (ω.compose D) := by
  rw [hl.span_compose_nat hD]
  have := Nat.mul_le_mul_right ω.period.toNat hD2
  have := hl.width_pos
  have := hl.1.period_toNat_cast
  have := hl.1.period_pos
  have : ω.width ≥ 0 := Nat.zero_le _
  omega

/-- At the actual step `p`, the northwest word of the parent of a case-(a) mark takes the value one
when the contact `t` is positive. -/
theorem wordA_compose_period (hl : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hD2 : 2 ≤ span D)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t) (ht0 : t ≠ 0) :
    wordA (ω.compose D) (ω.period.toNat : ℤ) = 1 := by
  have hc := hl.1.period_toNat_cast
  have hsp := span_eq_of_isConnectedSkew hD
  have hq := hl.1.period_pos
  have h := hl.wordA_generic hD hca hph (J := minContent D + 1) (a := 0) le_rfl hq
    (Or.inl ⟨by omega, by omega⟩) (fun _ => le_rfl) (Ne.symm ht0)
  have e : (minContent D + 1 - minContent D) * ω.period + 0 = (ω.period.toNat : ℤ) := by
    rw [hc]; ring
  rw [e] at h
  simpa using h

/-- At the actual step `p`, the southeast word of the parent of a case-(a) mark is zero. -/
theorem wordB_compose_period (hl : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hD2 : 2 ≤ span D)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t) :
    wordB (ω.compose D) (ω.period.toNat : ℤ) = 0 := by
  have hc := hl.1.period_toNat_cast
  have hsp := span_eq_of_isConnectedSkew hD
  have hq := hl.1.period_pos
  have hs1 := hph.1
  have h := hl.wordB_generic hD hca hph (J := minContent D + 1) (a := 0) le_rfl hq
    (Or.inl ⟨by omega, by omega⟩) (fun _ => le_rfl) (by omega)
  have e : (minContent D + 1 - minContent D) * ω.period + 0 = (ω.period.toNat : ℤ) := by
    rw [hc]; ring
  rw [e] at h
  simpa using h

/-- **The completed native column list is full or empty off the class of `t`**, when the parent's
northwest word follows generic bits modulo `g` away from the first contact. -/
theorem fullOrEmptyOff_col (hl : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hD2 : 2 ≤ span D)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t) {g : ℕ} (hg : 0 < g)
    (hgr : g ∣ ω.period.toNat) {A0 : ℕ → ℤ}
    (hgen : ∀ x : ℕ, 1 ≤ x → x < span (ω.compose D) → x % ω.period.toNat ≠ t.toNat →
      wordA (ω.compose D) x = A0 (x % g)) :
    FullOrEmptyOff (nativeColSet ω.E ω.period.toNat) g ω.period.toNat t.toNat := by
  have hspan := period_le_span_compose hl hD hD2
  have hp0 : 0 < ω.period.toNat := by
    have := hl.1.period_toNat_cast; have := hl.1.period_pos; omega
  refine fullOrEmptyOff_of_residues hg hgr A0 ?_ ?_
  · intro k hk1 hk2 hne
    have hkt : k % ω.period.toNat ≠ t.toNat := by
      rw [Nat.mod_eq_of_lt hk2]
      intro h; apply hne; rw [h]
    have hw := hgen k hk1 (by omega) hkt
    have hE := wordA_E_eq_compose hl hD hk1 hk2
    have hk0 : k ≠ 0 := by omega
    unfold nativeColSet
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range, hk0, false_or]
    constructor
    · rintro ⟨-, -, h⟩
      rw [← hw]; exact_mod_cast hE ▸ h
    · intro h
      refine ⟨hk2, hk1, ?_⟩
      rw [hE]; exact_mod_cast hw ▸ h
  · intro hne
    have ht0 : t.toNat ≠ 0 := by
      intro h; apply hne; rw [h]; simp
    have ht0' : t ≠ 0 := by omega
    have h1 := wordA_compose_period hl hD hD2 hca hph ht0'
    have h2 := hgen ω.period.toNat (by omega) (by omega) (by
      rw [Nat.mod_self]; exact fun h => ht0 h.symm)
    have h3 : ω.period.toNat % g = 0 := Nat.mod_eq_zero_of_dvd hgr
    rw [h3] at h2
    have : A0 0 = 1 := by rw [← h2]; exact_mod_cast h1
    simp [nativeColSet, this]

/-- **The completed native row list is full or empty off the class of `s`**, when the parent's
southeast word follows generic bits modulo `g` away from the first contact. -/
theorem fullOrEmptyOff_row (hl : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hD2 : 2 ≤ span D)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t) {g : ℕ} (hg : 0 < g)
    (hgr : g ∣ ω.period.toNat) {B0 : ℕ → ℤ}
    (hgen : ∀ x : ℕ, 1 ≤ x → x < span (ω.compose D) → x % ω.period.toNat ≠ s.toNat →
      wordB (ω.compose D) x = B0 (x % g)) :
    FullOrEmptyOff (nativeRowSet ω.E ω.period.toNat s.toNat) g ω.period.toNat s.toNat := by
  have hspan := period_le_span_compose hl hD hD2
  have hp0 : 0 < ω.period.toNat := by
    have := hl.1.period_toNat_cast; have := hl.1.period_pos; omega
  have hs1 := hph.1
  refine fullOrEmptyOff_of_residues hg hgr B0 ?_ ?_
  · intro k hk1 hk2 hne
    have hkt : k % ω.period.toNat ≠ s.toNat := by
      rw [Nat.mod_eq_of_lt hk2]
      intro h; apply hne; rw [h]
    have hks : k ≠ s.toNat := fun h => hkt (by rw [Nat.mod_eq_of_lt hk2]; exact h)
    have hw := hgen k hk1 (by omega) hkt
    have hE := wordB_E_eq_compose hl hD hk1 hk2
    unfold nativeRowSet
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range, hks, false_or]
    constructor
    · rintro ⟨-, -, h⟩
      rw [← hw]; exact_mod_cast hE ▸ h
    · intro h
      refine ⟨hk2, hk1, ?_⟩
      rw [hE]; exact_mod_cast hw ▸ h
  · intro hne
    have h1 := wordB_compose_period hl hD hD2 hca hph
    have h2 := hgen ω.period.toNat (by omega) (by omega) (by
      rw [Nat.mod_self]; omega)
    have h3 : ω.period.toNat % g = 0 := Nat.mod_eq_zero_of_dvd hgr
    rw [h3] at h2
    have h4 : B0 0 = 0 := by rw [← h2]; exact_mod_cast h1
    have hs0 : (0 : ℕ) ≠ s.toNat := by omega
    simp [nativeRowSet, h4, hs0]

/-- **`prop:gluing-ordinary-fold`, supplied-inner form, first chart of case (a).**  Two ordinary
proper legal roots `χ₁`,
`χ₂` of one diagram `F`, with nonempty marks and nondividing periods, whose gcd `g` exceeds one,
with the mark of `χ₁` of case (a) (the other case is reached by antitransposing the whole
comparison, as in the paper).  Then `F` has a proper legal chart of period `g` whose marked inner
is the ordinary fold of the supplied inner `χ₁.ω.E` (up to translation) and whose outer is the
composite of a legal mark on the outer of that fold with `γ (χ₁.D)`, `γ ∈ {id, AT}`.  The only
hypotheses are the two roots: the class hypotheses of `ordinary_fold` are derived from the second
root through the generic bits of `lem:gluing-periods` (ii). -/
theorem ordinary_fold_of_roots_a {F : Diagram} {χ₁ χ₂ : Chart} (h : OrdinaryPair F χ₁ χ₂)
    (hca : χ₁.ω.case = .a)
    (hg2 : 2 ≤ Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) :
    ∃ (χ' ψ : Chart) (μ : MarkedInner) (γ : Diagram → Diagram) (u : ℤ × ℤ),
      ψ.IsProperLegal ∧ ψ.IsChartOf χ₁.ω.E ∧
        ψ.period = (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat : ℤ) ∧
      χ'.IsProperLegal ∧ χ'.IsChartOf F ∧ χ'.ω = ψ.ω.translate u ∧
        χ'.period = (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat : ℤ) ∧
      μ.IsLegal ∧ μ.E = ψ.D ∧ (γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)) ∧
      χ'.D = μ.compose (γ χ₁.D) := by
  obtain ⟨g, a, b, c, d, M, wg, hd⟩ := h.exists_gcdData
  have hgg : g = Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat := hd.g_eq
  rw [← hgg] at hg2 ⊢
  obtain ⟨s₁, t₁, s₂, t₂, A0, B0, hph₁, hph₂, hG⟩ := h.gcdPair hd
  have e1 : ordHoleA χ₁.ω.case s₁ t₁ = t₁ := by simp [ordHoleA, hca]
  have e2 : ordHoleB χ₁.ω.case s₁ t₁ = s₁ := by simp [ordHoleB, hca]
  rw [e1, e2] at hG
  have hl : χ₁.ω.IsLegalNonempty := ⟨h.proper₁.2.2.2, h.nonempty₁⟩
  have hD := h.proper₁.1
  have hD2 := two_le_span_of_two_le_card hD h.proper₁.2.1
  have hg0 : 0 < g := hG.g_pos
  have hgr : g ∣ χ₁.ω.period.toNat := by rw [hd.period₁]; exact Dvd.intro_left a rfl
  have hglt : g < χ₁.ω.period.toNat := by
    rw [hd.period₁]; have := hd.a_ge; nlinarith
  have hP : IsConnectedSkew χ₁.parent := h.proper₁.2.2.2.isConnectedSkew_compose hD
  obtain ⟨t0, ht0⟩ := h.chart₁
  have hspF : span F = span χ₁.parent := by rw [ht0]; exact span_translate _
  have hper : a * g = χ₁.ω.period.toNat := hd.period₁.symm
  have hC := fullOrEmptyOff_col hl hD hD2 hca hph₁ hg0 hgr (A0 := A0) (fun x hx1 hx2 hx3 => by
    have hx2' : x < span F := by rw [hspF]; exact hx2
    have := hG.genA x hx1 hx2' (by
      intro hh; apply hx3; rw [← hper]; exact hh.1)
    have e : wordA F (x : ℤ) = wordA χ₁.parent (x : ℤ) := by
      rw [ht0]; exact wordA_translate hP t0 (by exact_mod_cast hx1) (by exact_mod_cast hx2)
    exact e ▸ this)
  have hB := fullOrEmptyOff_row hl hD hD2 hca hph₁ hg0 hgr (B0 := B0) (fun x hx1 hx2 hx3 => by
    have hx2' : x < span F := by rw [hspF]; exact hx2
    have := hG.genB x hx1 hx2' (by
      intro hh; apply hx3; rw [← hper]; exact hh.1)
    have e : wordB F (x : ℤ) = wordB χ₁.parent (x : ℤ) := by
      rw [ht0]; exact wordB_translate hP t0 (by exact_mod_cast hx1) (by exact_mod_cast hx2)
    exact e ▸ this)
  obtain ⟨χ', ψ, μ, γ, u, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ :=
    ordinary_fold_lift h.proper₁ ⟨t0, ht0⟩ hca h.nonempty₁ hph₁ hg2 hgr hglt hB hC
  exact ⟨χ', ψ, μ, γ, u, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩

/-- **`prop:gluing-ordinary-fold`, supplied-inner form.**  Two ordinary proper legal roots `χ₁`,
`χ₂` of one diagram `F`, with nonempty marks and nondividing periods, whose gcd `g` exceeds one.
Then `F` has a proper legal chart of period `g` whose marked inner is the ordinary fold of the
supplied inner `χ₁.ω.E` (up to translation) and whose outer is the composite of a legal mark on the
outer of that fold with `γ (χ₁.D)`, `γ ∈ {id, AT}`, `γ = AT` only for an empty mark.  The only
hypotheses are the two roots.  A first chart of case (b) is handled by antitransposing the whole
comparison, applying the case (a) construction, and transporting the result back. -/
theorem ordinary_fold_of_roots {F : Diagram} {χ₁ χ₂ : Chart} (h : OrdinaryPair F χ₁ χ₂)
    (hg2 : 2 ≤ Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat) :
    ∃ (χ' ψ : Chart) (μ : MarkedInner) (γ : Diagram → Diagram) (u : ℤ × ℤ),
      ψ.IsProperLegal ∧ ψ.IsChartOf χ₁.ω.E ∧
        ψ.period = (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat : ℤ) ∧
      χ'.IsProperLegal ∧ χ'.IsChartOf F ∧ χ'.ω = ψ.ω.translate u ∧
        χ'.period = (Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat : ℤ) ∧
      μ.IsLegal ∧ μ.E = ψ.D ∧ (γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)) ∧
      χ'.D = μ.compose (γ χ₁.D) := by
  have hcase : χ₁.ω.case = .a ∨ χ₁.ω.case = .b := by
    have := h.ordinary₁
    unfold AttachCase.IsMixed at this
    cases hh : χ₁.ω.case <;> simp_all
  rcases hcase with hca | hcb
  · exact ordinary_fold_of_roots_a h hca hg2
  · have hca' : χ₁.at.ω.case = .a := by
      change χ₁.ω.case.anti = .a
      rw [hcb]; rfl
    have e1 : χ₁.at.ω.period = χ₁.ω.period := MarkedInner.period_anti χ₁.ω
    have e2 : χ₂.at.ω.period = χ₂.ω.period := MarkedInner.period_anti χ₂.ω
    have hgcd : Nat.gcd χ₁.at.ω.period.toNat χ₂.at.ω.period.toNat =
        Nat.gcd χ₁.ω.period.toNat χ₂.ω.period.toNat := by rw [e1, e2]
    obtain ⟨χ'', ψ, μ, γ, u, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ :=
      ordinary_fold_of_roots_a h.at hca' (by rw [hgcd]; exact hg2)
    rw [hgcd] at k3 k7
    obtain ⟨χ', ψ', μ', γ', u', l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ :=
      ordinary_transport (E := χ₁.ω.E) (F := F) (X := χ₁.D) h.proper₁.1 k1 k2 k4 k5 k6 k8 k9 k10
        k11
    exact ⟨χ', ψ', μ', γ', u', l1, l2, l3.trans k3, l4, l5, l6, l7.trans k7, l8, l9, l10, l11⟩

end FoldSupplied
end SkewGluing
