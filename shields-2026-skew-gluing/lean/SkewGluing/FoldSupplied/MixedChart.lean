import SkewGluing.FoldSupplied.MixedFold
import SkewGluing.FoldSupplied.Lift
import SkewGluing.FoldSupplied.Areas

/-!
# `ge:mixed-fold` and its lift to the original parent

Formalizes `shields-2026-skew-gluing.tex`, «The mixed residue fold in every width range»
(`ge:mixed-fold`) and «Pairs involving mixed charts» (`prop:gluing-mixed-fold`).

For an actual case-(d) marked inner `J = ω.E` with a legal nonempty mark of period `r`, width
`0 < v < r` and phases `t < s ≤ v`, the complete native row list is
`mixRowSet J r = {k ∈ [1, r) : B_k = 1} = X_J ∩ [0, r)` and the square native column list is
`mixColSet J r t = (Y_J ∩ [0, r)) \ {t}`.

`FoldSupplied.mixed_fold`: if `g ∣ r`, `2 ≤ g < r`, every residue class of the row list modulo `g`
is full or empty, and every class of the column list outside the residues of `t` and `s` is full or
empty, then `J` has a proper legal chart of period `g`, of case (d), with width `v mod g`, where
`0 < v mod g < g`.  No inequality between `v` and `g` is assumed.

`FoldSupplied.mixed_fold_lift` applies the fold to the supplied inner of a proper chart of `F` and
lifts it to `F` by aligned composition (`FoldSupplied.exists_lifted_chart`).

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open MarkedInner

/-- The complete native row list `X_J ∩ [0, r)` of an inner of case (d). -/
def mixRowSet (E : Diagram) (r : ℕ) : Finset ℕ :=
  (Finset.range r).filter fun k => 1 ≤ k ∧ wordB E k = 1

/-- The square native column list `(Y_J ∩ [0, r)) \ {t}` of an inner of case (d). -/
def mixColSet (E : Diagram) (r t : ℕ) : Finset ℕ := (nativeColSet E r).erase t

/-- Every residue class of `S ∩ [0, r)` modulo `g` is full or empty. -/
def FullOrEmptyAll (S : Finset ℕ) (g r : ℕ) : Prop :=
  ∀ ρ, ρ < g → (∀ j, j < r / g → j * g + ρ ∈ S) ∨ (∀ j, j < r / g → j * g + ρ ∉ S)

/-- Every residue class of `S ∩ [0, r)` modulo `g`, except those of `e₁` and `e₂`, is full or
empty. -/
def FullOrEmptyOff2 (S : Finset ℕ) (g r e₁ e₂ : ℕ) : Prop :=
  ∀ ρ, ρ < g → ρ ≠ e₁ % g → ρ ≠ e₂ % g →
    (∀ j, j < r / g → j * g + ρ ∈ S) ∨ (∀ j, j < r / g → j * g + ρ ∉ S)

theorem eq_of_fullOrEmpty {f : ℕ → ℤ} {S : Finset ℕ} {g r : ℕ} (hg : 0 < g) (hgr : g ∣ r)
    (hf : ∀ k, k < r → f k = if k ∈ S then 1 else 0) {x y : ℕ} (hx : x < r) (hy : y < r)
    (hxy : x % g = y % g)
    (h : (∀ j, j < r / g → j * g + x % g ∈ S) ∨ (∀ j, j < r / g → j * g + x % g ∉ S)) :
    f x = f y := by
  have hxj : x / g < r / g := by
    rw [Nat.div_lt_iff_lt_mul hg, Nat.div_mul_cancel hgr]; exact hx
  have hyj : y / g < r / g := by
    rw [Nat.div_lt_iff_lt_mul hg, Nat.div_mul_cancel hgr]; exact hy
  have ex' := Nat.div_add_mod' x g
  have ey' := Nat.div_add_mod' y g
  rw [hf x hx, hf y hy]
  rcases h with h1 | h1
  · have a1 := h1 (x / g) hxj
    have a2 := h1 (y / g) hyj
    rw [ex'] at a1
    rw [hxy, ey'] at a2
    simp [a1, a2]
  · have a1 := h1 (x / g) hxj
    have a2 := h1 (y / g) hyj
    rw [ex'] at a1
    rw [hxy, ey'] at a2
    simp [a1, a2]

variable {ω : MarkedInner}

theorem MixWords.mnB_eq_mem {r v s t : ℕ} (h : MixWords (wordA ω.E) (wordB ω.E) r v s t) {k : ℕ}
    (hk : k < r) : mnB (wordB ω.E) k = if k ∈ mixRowSet ω.E r then 1 else 0 := by
  unfold mnB mixRowSet
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hbit := (h.bits k (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0) (by
      have := h.v_pos
      have : (k : ℤ) + 1 ≤ ((r + v : ℕ) : ℤ) := by omega
      omega)).2
    have h1 : 1 ≤ k := by omega
    rcases hbit with hz | hz
    · simp [hk0, hz, h1]
    · simp [hk0, hz, h1, hk]

theorem MixWords.mnA_eq_mem {r v s t : ℕ} (h : MixWords (wordA ω.E) (wordB ω.E) r v s t) {k : ℕ}
    (hk : k < r) (ht : k ≠ t) :
    mnA (wordA ω.E) k = if k ∈ mixColSet ω.E r t then 1 else 0 := by
  unfold mnA mixColSet nativeColSet
  by_cases hk0 : k = 0
  · subst hk0
    simp [ht]
  · have hbit := (h.bits k (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0) (by
      have := h.v_pos
      have : (k : ℤ) + 1 ≤ ((r + v : ℕ) : ℤ) := by omega
      omega)).1
    have h1 : 1 ≤ k := by omega
    rcases hbit with hz | hz
    · simp [hk0, hz, h1, ht]
    · simp [hk0, hz, h1, hk, ht]

/-- **`ge:mixed-fold`**, as a context of word facts. -/
theorem IsLegalNonempty.mixCtx (hl : ω.IsLegalNonempty) (hcd : ω.case = .d) {s t : ℤ}
    (hph : ω.IsPhases s t) {g : ℕ} (hg2 : 2 ≤ g) (hgr : g ∣ ω.period.toNat)
    (hglt : g < ω.period.toNat)
    (hB : FullOrEmptyAll (mixRowSet ω.E ω.period.toNat) g ω.period.toNat)
    (hC : FullOrEmptyOff2 (mixColSet ω.E ω.period.toNat t.toNat) g ω.period.toNat t.toNat
      s.toNat) :
    MixCtx (wordA ω.E) (wordB ω.E) ω.period.toNat ω.width s.toNat t.toNat g := by
  have hw := IsLegalNonempty.mixWords hl hcd hph
  have hg : 0 < g := by omega
  have hlt := hl.phases_lt (Or.inr hcd) hph
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hq := hl.width_lt_period
  have hwp := hl.width_pos
  refine ⟨hw, hg2, hgr, hglt, ?_, ?_⟩
  · intro x y hx hy hxy
    have hmod : x % g < g := Nat.mod_lt _ hg
    refine eq_of_fullOrEmpty (S := mixRowSet ω.E ω.period.toNat) hg hgr (fun k hk => hw.mnB_eq_mem hk)
      hx hy hxy (hB _ hmod)
  · intro x y hx hy hxy hxt hxs
    have hmod : x % g < g := Nat.mod_lt _ hg
    have hxne : x ≠ t.toNat := fun e => hxt (by rw [e])
    have hyne : y ≠ t.toNat := fun e => hxt (by rw [hxy, e])
    have := eq_of_fullOrEmpty (f := fun k => if k = t.toNat then 0 else mnA (wordA ω.E) k)
      (S := mixColSet ω.E ω.period.toNat t.toNat) hg hgr (fun k hk => by
        by_cases hkt : k = t.toNat
        · simp [hkt, mixColSet]
        · simp only [hkt, if_false]
          exact hw.mnA_eq_mem hk hkt) hx hy hxy (hC _ hmod hxt hxs)
    simpa [hxne, hyne] using this

/-- **`ge:mixed-fold`.**  Let `ω` be a legal case-(d) mark of period `r`, width `0 < v < r` and
phases `t < s ≤ v`, with `g ∣ r` and `1 < g < r`.  If every residue class of the row list is full
or empty, and every class of the column list outside the residues of `t` and `s` is full or empty,
then the inner `ω.E` has a proper legal chart of period `g`, of case (d) and of width
`v mod g`, which satisfies `0 < v mod g < g`.  Both factors have strictly fewer cells than `ω.E`.
No inequality between `v` and `g` is required. -/
theorem mixed_fold {ω : MarkedInner} (hω : ω.IsLegal) (hW : ω.W.Nonempty) (hcd : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) {g : ℕ} (hg2 : 2 ≤ g) (hgr : g ∣ ω.period.toNat)
    (hglt : g < ω.period.toNat)
    (hB : FullOrEmptyAll (mixRowSet ω.E ω.period.toNat) g ω.period.toNat)
    (hC : FullOrEmptyOff2 (mixColSet ω.E ω.period.toNat t.toNat) g ω.period.toNat t.toNat
      s.toNat) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf ω.E ∧ χ.period = g ∧ χ.ω.case = .d ∧
      χ.ω.width = ω.width % g ∧ 0 < ω.width % g ∧ ω.width % g < g ∧
      χ.ω.E.card < ω.E.card ∧ χ.D.card < ω.E.card := by
  have hl : ω.IsLegalNonempty := ⟨hω, hW⟩
  have ctx := IsLegalNonempty.mixCtx hl hcd hph hg2 hgr hglt hB hC
  have hq := hl.width_lt_period
  have hwp := hl.width_pos
  have hspan : span ω.E = ω.period.toNat + ω.width := by
    have h1 := hl.span_eq
    have h2 : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg (by omega)
    have : (span ω.E : ℤ) = ((ω.period.toNat + ω.width : ℕ) : ℤ) := by
      rw [h1]; push_cast; rw [h2]; rfl
    exact_mod_cast this
  have hfd := ctx.foldData hspan
  obtain ⟨χ, hχ, hχF, hper, hcase, hwid⟩ := hfd.exists_chart hl.isConnectedSkew_E
  have hpos : 0 < ω.width % g := ctx.a_pos
  refine ⟨χ, hχ, hχF, ?_, hcase, hwid, hpos, Nat.mod_lt _ (by omega),
    hχ.inner_card_lt_of_chartOf hχF, hχ.outer_card_lt_of_chartOf hχF⟩
  unfold Chart.period
  have : ((χ.ω.period.toNat : ℕ) : ℤ) = χ.ω.period := Int.toNat_of_nonneg (by
    have := hχ.2.2.2.period_pos; omega)
  rw [← this, hper]

/-- **The mixed fold applied to the supplied inner and lifted to the parent**
(`prop:gluing-mixed-fold`).  Let `χ` be a proper legal chart of `F` with a nonempty case-(d) mark
whose inner satisfies the hypotheses of `mixed_fold`.  Then `F` has a proper legal chart of period
`g` whose marked inner is the fold of `χ.ω.E` (up to translation) and whose outer is the composite
of a legal mark on the outer of that fold with `γ(χ.D)`, `γ ∈ {id, AT}`. -/
theorem mixed_fold_lift {F : Diagram} {χ : Chart} (hχ : χ.IsProperLegal) (hF : χ.IsChartOf F)
    (hcd : χ.ω.case = .d) (hW : χ.ω.W.Nonempty) {s t : ℤ} (hph : χ.ω.IsPhases s t) {g : ℕ}
    (hg2 : 2 ≤ g) (hgr : g ∣ χ.ω.period.toNat) (hglt : g < χ.ω.period.toNat)
    (hB : FullOrEmptyAll (mixRowSet χ.ω.E χ.ω.period.toNat) g χ.ω.period.toNat)
    (hC : FullOrEmptyOff2 (mixColSet χ.ω.E χ.ω.period.toNat t.toNat) g χ.ω.period.toNat
      t.toNat s.toNat) :
    ∃ (χ' ψ : Chart) (μ : MarkedInner) (γ : Diagram → Diagram) (u : ℤ × ℤ),
      ψ.IsProperLegal ∧ ψ.IsChartOf χ.ω.E ∧ ψ.period = g ∧ ψ.ω.case = .d ∧
      ψ.ω.width = χ.ω.width % g ∧
      χ'.IsProperLegal ∧ χ'.IsChartOf F ∧ χ'.ω = ψ.ω.translate u ∧ χ'.period = g ∧
      μ.IsLegal ∧ μ.E = ψ.D ∧ (γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)) ∧
      χ'.D = μ.compose (γ χ.D) := by
  obtain ⟨ψ, hψ, hψE, hψper, hψcase, hψw, -, -, -, -⟩ :=
    mixed_fold hχ.2.2.2 hW hcd hph hg2 hgr hglt hB hC
  have hper : ((χ.ω.period.toNat : ℕ) : ℤ) = χ.ω.period := Int.toNat_of_nonneg (by
    have hl : χ.ω.IsLegalNonempty := ⟨hχ.2.2.2, hW⟩
    have := hl.width_lt_period; have := hl.width_pos; omega)
  have hdvd : ψ.period ∣ χ.period := by
    rw [hψper]
    have h := Int.natCast_dvd_natCast.mpr hgr
    rw [hper] at h
    exact h
  obtain ⟨χ', μ, γ, u, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_lifted_chart hχ hψ hF hψE hdvd
  exact ⟨χ', ψ, μ, γ, u, hψ, hψE, hψper, hψcase, hψw, h1, h2, h3, by rw [h4]; exact hψper,
    h5, h6, h7, h8⟩

end FoldSupplied
end SkewGluing
