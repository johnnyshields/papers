/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperBinders

/-!
# The lower cluster's chart, on the caller's own principal pair

`EndpointPackage.exists_lower_cluster_enumeration_of_two_le_rho` produces the
retained enumeration, but it produces its **own** `ψ` — it calls
`exists_principal_pair_cluster_indices_of_two_le_rho` internally, and that
theorem's conclusion is an existential.  So a caller that has already called the
principal-pair theorem, and holds the retained-set fields and the slopes on *its*
`ψ`, cannot combine the two: nothing identifies the two charts, and a composition
that pairs them builds green while the residue asymptotics — stated at
`clusterAlpha x₁ ρ (idx₀ i)` — end up describing a different point than
`hgmem₀` places in the retained set.

That is the "which index" failure with the index question moved one level out, to
*which cluster*.  This module removes it by isolating the part of the enumeration
that has nothing to do with `ψ` at all: given only the two principal positions
`j_p`, `j_c` the caller already holds, it returns the chart on `Fin (ρ - 2)` and
the four facts the binders need.  Everything analytic stays with the caller, so
there is exactly one `ψ` in play.

`idx₀ i = (chart i + ρ - j_p) \bmod ρ` never takes the values `0` or `1` — those
are the manuscript's labels for the principal pair, since `α_1 = \overline{α_0}`
— so the retained labels are `2, …, ρ-1` and `n_0 = ρ - 2`.  At `ρ = 2` the chart
is empty, which is the manuscript's "the cluster is the principal pair alone".

## Main statements

* `shift_mod_of_lt` — the shift `(j + ρ - j_p) \bmod ρ`, resolved.
* `exists_lower_chart` — the chart and its four facts, from `j_p` and `j_c` alone.
* `lower_cluster_enumeration_of_chart` — the three binders, as the
  `EndpointUpperBinders.ClusterEnumeration` both endpoint blocks return.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:lower-cluster-expansion`.

## Tags

lower endpoint, cluster enumeration, retained cluster, weighted dominance
-/

namespace ForgacsTran

/-- The shift `(j + ρ - j_p) \bmod ρ`, resolved into its two cases.  A public
copy of the arithmetic `exists_lower_cluster_enumeration_of_two_le_rho` keeps
private, which is what makes the chart statable away from that proof. -/
theorem shift_mod_of_lt {ρ j jp : ℕ} (hj : j < ρ) (hjp : jp < ρ) :
    (j + ρ - jp) % ρ = if jp ≤ j then j - jp else j + ρ - jp := by
  by_cases h : jp ≤ j
  · rw [if_pos h, show j + ρ - jp = (j - jp) + ρ by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- **The retained chart, from the principal pair alone.**  `range ρ` with the two
principal positions erased has `ρ - 2` elements; enumerating it gives an injective
`chart` avoiding both, and the manuscript's label `(chart i + ρ - j_p) \bmod ρ`
avoids `0` and `1`.

No `ψ`, no cluster, no analysis: the caller keeps all of it, and therefore keeps
one cluster rather than two. -/
theorem exists_lower_chart {ρ : ℕ} (hρ : 2 ≤ ρ) {jp jc : ℕ} (hjp : jp < ρ)
    (hjc : jc < ρ) (hjcshift : jc = (1 + jp) % ρ) :
    ∃ chart : Fin (ρ - 2) → ℕ, Function.Injective chart
      ∧ (∀ i, chart i < ρ) ∧ (∀ i, chart i ≠ jp) ∧ (∀ i, chart i ≠ jc)
      ∧ (∀ i, (chart i + ρ - jp) % ρ ≠ 0 ∧ (chart i + ρ - jp) % ρ ≠ 1) := by
  classical
  have hjpc : jp ≠ jc := by
    rw [hjcshift]
    rcases lt_or_ge (1 + jp) ρ with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [show 1 + jp = ρ by omega, Nat.mod_self]; omega
  set J : Finset ℕ := ((Finset.range ρ).erase jp).erase jc with hJdef
  have hjpm : jp ∈ Finset.range ρ := Finset.mem_range.2 hjp
  have hjcm : jc ∈ (Finset.range ρ).erase jp :=
    Finset.mem_erase.2 ⟨Ne.symm hjpc, Finset.mem_range.2 hjc⟩
  have hJ : J.card = ρ - 2 := by
    rw [hJdef, Finset.card_erase_of_mem hjcm, Finset.card_erase_of_mem hjpm,
      Finset.card_range]
    omega
  set chart : Fin (ρ - 2) → ℕ := fun i => ((J.orderIsoOfFin hJ i : J) : ℕ) with hchart
  have hmemJ : ∀ i, chart i ∈ J := fun i => (J.orderIsoOfFin hJ i).2
  have hlt : ∀ i, chart i < ρ := fun i =>
    Finset.mem_range.1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hmemJ i)))
  have hnejp : ∀ i, chart i ≠ jp := fun i =>
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (hmemJ i))
  have hnejc : ∀ i, chart i ≠ jc := fun i => Finset.ne_of_mem_erase (hmemJ i)
  have hinj : Function.Injective chart := fun i j hij =>
    (J.orderIsoOfFin hJ).injective (Subtype.ext hij)
  have hjcval : (jp + 1 < ρ ∧ jc = jp + 1) ∨ (jp + 1 = ρ ∧ jc = 0) := by
    rcases lt_or_ge (1 + jp) ρ with h | h
    · exact Or.inl ⟨by omega, by rw [hjcshift, Nat.mod_eq_of_lt h]; omega⟩
    · exact Or.inr ⟨by omega, by rw [hjcshift, show 1 + jp = ρ by omega, Nat.mod_self]⟩
  refine ⟨chart, hinj, hlt, hnejp, hnejc, fun i => ?_⟩
  have hci := hlt i
  have hp := hnejp i
  have hq := hnejc i
  rw [shift_mod_of_lt hci hjp]
  rcases hjcval with ⟨hltρ, hv⟩ | ⟨heρ, hv⟩ <;> split_ifs with h <;>
    exact ⟨by omega, by omega⟩

/-! ### The enumeration's analytic half, parameterized on the caller's chart

`exists_lower_cluster_enumeration_of_two_le_rho` proves `hginj₀`, `hgmem₀` and
`hgcard₀`, and that content is real — `exists_lower_chart` above supplies only the
arithmetic.  What makes it uncomposable is the packaging: it opens its own `∃ ψ`.

So the same demotion is applied to it.  Everything here is stated at a `ψ`, a
principal pair and a chart the **caller** holds, so a caller that has called
`exists_principal_pair_cluster_indices_of_two_le_rho` once and `exists_lower_chart`
once has exactly one cluster in play and can still reach all three binders.

Stated at `ftTauArc` rather than `ftTauLower`, because that is the radius a
two-endpoint composition must use; the caller supplies `hp` and `hq` through
`ftPrincipal_ftTauArc_eq_lower` and `conj_ftPrincipal_ftTauArc_eq_lower`. -/

/-- **`hginj₀`, `hgmem₀` and `hgcard₀` at one angle**, from the caller's own
cluster.  The chart names the point, the principal pair names the two erased
positions, and the count says the `ρ` chart images are distinct — nothing else
enters, and no cluster is constructed here.

The three are `ClusterEnumeration` at this cluster, which is the same shape
`EndpointLowerBlock.exists_lower_endpoint_block` goes on to return: what this
theorem supplies is exactly the enumeration half of the block, on a `ψ` the caller
owns rather than one this proof opens. -/
theorem lower_cluster_enumeration_of_chart {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {ψ : ℂ → ℂ} {jp jc : ℕ} (hjp : jp < ρ) (hjc : jc < ρ) (hjpc : jp ≠ jc)
    {chart : Fin (ρ - 2) → ℕ} (hchartinj : Function.Injective chart)
    (hchartlt : ∀ i, chart i < ρ) (hnejp : ∀ i, chart i ≠ jp) (hnejc : ∀ i, chart i ≠ jc)
    {δ : ℝ} (hcardS : (ftClusterSet a c r (n - 1) ρ ψ δ).card = ρ)
    (hp : ftPrincipal (ftTauArc a r (n - 1) x₁) δ
      = ψ (clusterDir ρ jp * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)))
    (hq : ((ftTauArc a r (n - 1) x₁ δ : ℝ) : ℂ)
        * Complex.exp (-((δ : ℝ) : ℂ) * Complex.I)
      = ψ (clusterDir ρ jc * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))) :
    ClusterEnumeration (ftClusterSet a c r (n - 1) ρ ψ δ)
      (ftPrincipal (ftTauArc a r (n - 1) x₁) δ)
      (((ftTauArc a r (n - 1) x₁ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * Complex.I))
      (fun i : Fin (ρ - 2) =>
        ψ (clusterDir ρ (chart i) * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))) := by
  classical
  have hInjOn : Set.InjOn
      (fun j => ψ (clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)))
      (Finset.range ρ) := by
    refine Finset.injOn_of_card_image_eq ?_
    change (ftClusterSet a c r (n - 1) ρ ψ δ).card = (Finset.range ρ).card
    rw [hcardS, Finset.card_range]
  have hmemS : ∀ j : ℕ, j < ρ →
      ψ (clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
        ∈ ftClusterSet a c r (n - 1) ρ ψ δ :=
    fun j hj => mem_ftClusterSet.2 ⟨j, Finset.mem_range.2 hj, rfl⟩
  have hchartne : ∀ i j : ℕ, i < ρ → j < ρ → i ≠ j →
      ψ (clusterDir ρ i * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
        ≠ ψ (clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) := by
    intro i j hi hj hij hEq
    exact hij (hInjOn (Finset.mem_coe.2 (Finset.mem_range.2 hi))
      (Finset.mem_coe.2 (Finset.mem_range.2 hj)) hEq)
  refine ⟨fun i j hij => hchartinj (hInjOn
    (Finset.mem_coe.2 (Finset.mem_range.2 (hchartlt i)))
    (Finset.mem_coe.2 (Finset.mem_range.2 (hchartlt j))) hij), fun i => ?_, ?_⟩
  · refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hmemS _ (hchartlt i)⟩⟩
    · rw [hq]; exact hchartne _ _ (hchartlt i) hjc (hnejc i)
    · rw [hp]; exact hchartne _ _ (hchartlt i) hjp (hnejp i)
  · have hpS : ftPrincipal (ftTauArc a r (n - 1) x₁) δ
        ∈ ftClusterSet a c r (n - 1) ρ ψ δ := by rw [hp]; exact hmemS _ hjp
    have hqS : (((ftTauArc a r (n - 1) x₁ δ : ℝ) : ℂ)
        * Complex.exp (-((δ : ℝ) : ℂ) * Complex.I))
        ∈ (ftClusterSet a c r (n - 1) ρ ψ δ).erase
          (ftPrincipal (ftTauArc a r (n - 1) x₁) δ) := by
      refine Finset.mem_erase.2 ⟨?_, by rw [hq]; exact hmemS _ hjc⟩
      rw [hq, hp]
      exact hchartne _ _ hjc hjp (Ne.symm hjpc)
    rw [Finset.card_erase_of_mem hqS, Finset.card_erase_of_mem hpS, hcardS]
    omega

end ForgacsTran
