import SkewGluing.FoldSupplied.OrdinaryChart

/-!
# `ge:ordinary-fold` and its lift to the original parent

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`) and «Two ordinary roots» (`prop:gluing-ordinary-fold`).

For an actual ordinary marked inner `J = ω.E` with a legal nonempty case-(a) mark of period `r`,
width `v < r` and contacts `1 ≤ s ≤ v`, `0 ≤ t < v`, the completed native lists are

* `nativeRowSet J r s = {k ∈ [1, r) : B_k = 1} ∪ {s}`, which equals `X_J ∩ [0, r) ∪ {s}`, and
* `nativeColSet J r = {0} ∪ {k ∈ [1, r) : A_k = 1}`, which equals `Y_J ∩ [0, r)`.

`FoldSupplied.ordinary_fold`: if `g ∣ r`, `2 ≤ g < r`, every residue class modulo `g` of the row
list other than that of `s` is full or empty, and likewise the column list off that of `t`, then
`J` has a proper legal chart of period `g`; its mark is the horizontal empty mark when `g ∣ v`, and
otherwise has width `v mod g`, type (a) when `v < g` or the projected contacts satisfy
`t mod g ≤ s mod g`, and type (b) otherwise.

`FoldSupplied.ordinary_fold_lift` applies the fold to the supplied inner of a proper chart of `F`
and lifts it to `F` by aligned composition (`FoldSupplied.exists_lifted_chart`).

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open OrdinaryDrift OrdinaryFold SmallOverlap MarkedInner

/-- The completed native row list `X_J ∩ [0, r) ∪ {s}` of an inner. -/
def nativeRowSet (E : Diagram) (r s : ℕ) : Finset ℕ :=
  insert s ((Finset.range r).filter fun k => 1 ≤ k ∧ wordB E k = 1)

/-- The completed native column list `Y_J ∩ [0, r)` of an inner. -/
def nativeColSet (E : Diagram) (r : ℕ) : Finset ℕ :=
  insert 0 ((Finset.range r).filter fun k => 1 ≤ k ∧ wordA E k = 1)

/-- Every residue class of `S ∩ [0, r)` modulo `g`, except the class of `ex`, is full or empty. -/
def FullOrEmptyOff (S : Finset ℕ) (g r ex : ℕ) : Prop :=
  ∀ ρ, ρ < g → ρ ≠ ex % g →
    (∀ j, j < r / g → j * g + ρ ∈ S) ∨ (∀ j, j < r / g → j * g + ρ ∉ S)

variable {A B : ℕ → ℤ} {r v s t g ex : ℕ}

theorem classConst_of_fullOrEmpty {f : ℕ → ℤ} {S : Finset ℕ} (hf : ∀ k, k < r → f k = if k ∈ S then 1 else 0)
    (hgr : g ∣ r) (hg : 0 < g) (h : FullOrEmptyOff S g r ex) : ClassConst f g r ex := by
  intro x y hx hy hxy hne
  have hρ : x % g < g := Nat.mod_lt _ hg
  have hxj : x / g < r / g := by
    rw [Nat.div_lt_iff_lt_mul hg, Nat.div_mul_cancel hgr]; exact hx
  have hyj : y / g < r / g := by
    rw [Nat.div_lt_iff_lt_mul hg, Nat.div_mul_cancel hgr]; exact hy
  have ex' := Nat.div_add_mod' x g
  have ey' := Nat.div_add_mod' y g
  rw [hf x hx, hf y hy]
  rcases h (x % g) hρ hne with h1 | h1
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

theorem OrdWords.natC_eq_mem {ω : MarkedInner} (h : OrdWords (fun k : ℕ => wordA ω.E k)
    (fun k : ℕ => wordB ω.E k) r v s t) {k : ℕ} (hk : k < r) :
    natC (fun k : ℕ => wordA ω.E k) k = if k ∈ nativeColSet ω.E r then 1 else 0 := by
  have hb := h.words.bits
  unfold natC nativeColSet
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hbit : wordA ω.E (k : ℤ) = 0 ∨ wordA ω.E (k : ℤ) = 1 :=
      (hb k (by omega) (by have := h.v_pos; omega)).1
    have h1 : 1 ≤ k := by omega
    rcases hbit with hz | hz
    · simp [hk0, hz, h1]
    · simp [hk0, hz, h1, hk]

theorem OrdWords.natB_eq_mem {ω : MarkedInner} (h : OrdWords (fun k : ℕ => wordA ω.E k)
    (fun k : ℕ => wordB ω.E k) r v s t) {k : ℕ} (hk : k < r) :
    natB (fun k : ℕ => wordB ω.E k) s k = if k ∈ nativeRowSet ω.E r s then 1 else 0 := by
  have hb := h.words.bits
  have hs1 := h.s_pos
  have hs0 : s ≠ 0 := by omega
  unfold natB nativeRowSet
  by_cases hk0 : k = 0
  · subst hk0
    have : (0 : ℕ) ≠ s := by omega
    simp [this]
  · by_cases hks : k = s
    · simp [hks, hs0]
    · have hbit : wordB ω.E (k : ℤ) = 0 ∨ wordB ω.E (k : ℤ) = 1 :=
        (hb k (by omega) (by have := h.v_pos; omega)).2
      have h1 : 1 ≤ k := by omega
      rcases hbit with hz | hz
      · simp [hk0, hks, hz, h1]
      · simp [hk0, hks, hz, h1, hk]

/-- **`ge:ordinary-fold`.** -/
theorem ordinary_fold {ω : MarkedInner} (hω : ω.IsLegal) (hW : ω.W.Nonempty)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t) {g : ℕ} (hg2 : 2 ≤ g)
    (hgr : g ∣ ω.period.toNat) (hglt : g < ω.period.toNat)
    (hB : FullOrEmptyOff (nativeRowSet ω.E ω.period.toNat s.toNat) g ω.period.toNat s.toNat)
    (hC : FullOrEmptyOff (nativeColSet ω.E ω.period.toNat) g ω.period.toNat t.toNat) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf ω.E ∧ χ.period = g ∧
      (ω.width % g = 0 → χ.ω = emptyMarkH χ.ω.E ∧ χ.ω.W = ∅) ∧
      (0 < ω.width % g → χ.ω.W.Nonempty ∧ χ.ω.width = ω.width % g ∧
        ((ω.width < g ∨ t.toNat % g ≤ s.toNat % g) → χ.ω.case = .a) ∧
        (g ≤ ω.width → s.toNat % g < t.toNat % g → χ.ω.case = .b)) := by
  have hl : ω.IsLegalNonempty := ⟨hω, hW⟩
  have hw := SkewGluing.FoldSupplied.IsLegalNonempty.ordWords hl hca hph
  have hg : 0 < g := by omega
  have hCc : ClassConst (natC (fun k : ℕ => wordA ω.E k)) g ω.period.toNat t.toNat :=
    classConst_of_fullOrEmpty (fun k hk => hw.natC_eq_mem hk) hgr hg hC
  have hBc : ClassConst (natB (fun k : ℕ => wordB ω.E k) s.toNat) g ω.period.toNat s.toNat :=
    classConst_of_fullOrEmpty (fun k hk => hw.natB_eq_mem hk) hgr hg hB
  have ctx : OrdCtx (fun k : ℕ => wordA ω.E k) (fun k : ℕ => wordB ω.E k) ω.period.toNat ω.width
      s.toNat t.toNat g := ⟨hw, hg2, hgr, hglt, hCc, hBc⟩
  have hspan : span ω.E = ω.period.toNat + ω.width := by
    have h1 := hl.span_eq
    have h2 : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg (by
      have := hl.width_lt_period; have := hl.width_pos; omega)
    have : (span ω.E : ℤ) = ((ω.period.toNat + ω.width : ℕ) : ℤ) := by
      rw [h1]; push_cast; rw [h2]; rfl
    exact_mod_cast this
  obtain ⟨χ, hχ, hχF, hper, hemp, hpos⟩ := ctx.exists_chart hl.isConnectedSkew_E hspan
    (fun k _ _ => rfl) (fun k _ _ => rfl)
  refine ⟨χ, hχ, hχF, hper, fun h => ?_, hpos⟩
  have hW0 := hemp h
  exact ⟨hχ.eq_emptyMarkH hW0, hW0⟩


/-- **The ordinary fold applied to the supplied inner and lifted to the parent**
(`prop:gluing-ordinary-fold`).  Let `χ` be a proper legal chart of `F` with a nonempty case-(a)
mark whose inner satisfies the hypotheses of `ordinary_fold`.  Then `F` has a proper legal chart
of period `g` whose marked inner is the fold of `χ.ω.E` (up to translation) and whose outer is the
composite of a legal mark on the outer of that fold with `γ(χ.D)`, `γ ∈ {id, AT}`. -/
theorem ordinary_fold_lift {F : Diagram} {χ : Chart} (hχ : χ.IsProperLegal) (hF : χ.IsChartOf F)
    (hca : χ.ω.case = .a) (hW : χ.ω.W.Nonempty) {s t : ℤ} (hph : χ.ω.IsPhases s t) {g : ℕ}
    (hg2 : 2 ≤ g) (hgr : g ∣ χ.ω.period.toNat) (hglt : g < χ.ω.period.toNat)
    (hB : FullOrEmptyOff (nativeRowSet χ.ω.E χ.ω.period.toNat s.toNat) g χ.ω.period.toNat s.toNat)
    (hC : FullOrEmptyOff (nativeColSet χ.ω.E χ.ω.period.toNat) g χ.ω.period.toNat t.toNat) :
    ∃ (χ' ψ : Chart) (μ : MarkedInner) (γ : Diagram → Diagram) (u : ℤ × ℤ),
      ψ.IsProperLegal ∧ ψ.IsChartOf χ.ω.E ∧ ψ.period = g ∧
      χ'.IsProperLegal ∧ χ'.IsChartOf F ∧ χ'.ω = ψ.ω.translate u ∧ χ'.period = g ∧
      μ.IsLegal ∧ μ.E = ψ.D ∧ (γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)) ∧
      χ'.D = μ.compose (γ χ.D) := by
  obtain ⟨ψ, hψ, hψE, hψper, -, -⟩ := ordinary_fold hχ.2.2.2 hW hca hph hg2 hgr hglt hB hC
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
  exact ⟨χ', ψ, μ, γ, u, hψ, hψE, hψper, h1, h2, h3, by rw [h4]; exact hψper, h5, h6, h7, h8⟩

end FoldSupplied
end SkewGluing
