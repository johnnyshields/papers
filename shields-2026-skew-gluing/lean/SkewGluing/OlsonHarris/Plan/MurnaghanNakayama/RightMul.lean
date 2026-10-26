import SkewGluing.OlsonHarris.Plan.MurnaghanNakayama.Shift
import SkewGluing.OlsonHarris.Plan.MurnaghanNakayama.LeftDeriv

/-!
# The multiplication form of the Murnaghan–Nakayama rule on Ferrers shapes

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.1.3 (`OlsonHarris2024HopfApplications`), Thm. 5.1.13
for one power sum.

`ribbonAdditions μ m` is the set of Young diagrams `λ ⊇ μ` with `λ / μ` a ribbon of `m` cells; it
is finite, and `sum_update_rows_eq` sorts the determinants of `Shift` by `RowMove`:
`Σ_k det (h_{a_i + m δ_{ik} + j}) = Σ_{λ} (-1)^{ht(λ/μ)} s_λ` in `N` rows.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace MN

open MvPolynomial

namespace RowMove

variable {mu nu : YoungDiagram} {j i1 m : ℕ}

theorem rowLen_le (h : RowMove mu nu j i1 m) (hm : 0 < m) (i : ℕ) :
    nu.rowLen i ≤ mu.rowLen 0 + m := by
  have htop := h.top
  have hjn : ((j - i1 : ℕ) : ℤ) = (j : ℤ) - i1 := by have := h.i1_le; omega
  rw [hjn] at htop
  have a1 := mu.rowLen_anti 0 j (by omega)
  have a2 := mu.rowLen_anti 0 i (by omega)
  have a3 := mu.rowLen_anti 0 (i - 1) (by omega)
  by_cases h1 : i < i1 ∨ j < i
  · rw [h.outside i h1]; omega
  · by_cases h2 : i = i1
    · subst h2; omega
    · have := h.inner i (by omega) (by omega)
      omega

theorem j_lt (h : RowMove mu nu j i1 m) (hm : 0 < m) : j < mu.colLen 0 + m := by
  have hi1 : i1 ≤ mu.colLen 0 := by
    by_cases h0 : i1 = 0
    · omega
    · have a1 := h.outside (i1 - 1) (Or.inl (by omega))
      have a2 := nu.rowLen_anti (i1 - 1) i1 (by omega)
      have a3 := h.row_lt hm (le_refl i1) h.i1_le
      have a4 : (i1 - 1, 0) ∈ mu := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [YoungDiagram.mem_iff_lt_colLen] at a4
      omega
  have hrows : numRows (skewDiagram nu mu) ≤ (skewDiagram nu mu).card :=
    Finset.card_image_le
  rw [h.numRows_eq hm, h.card_eq hm] at hrows
  omega

end RowMove

/-- The Young diagrams `λ ⊇ μ` such that `λ / μ` is a ribbon with `m` cells. -/
def ribbonAdditions (mu : YoungDiagram) (m : ℕ) : Set YoungDiagram :=
  {lam | mu ≤ lam ∧ IsRibbon (skewDiagram lam mu) ∧ (skewDiagram lam mu).card = m}

theorem ribbonAdditions_finite (mu : YoungDiagram) {m : ℕ} (hm : 0 < m) :
    (ribbonAdditions mu m).Finite := by
  refine Set.Finite.of_injOn (f := fun lam : YoungDiagram => lam.cells)
    (t := ((Finset.range (mu.colLen 0 + m) ×ˢ Finset.range (mu.rowLen 0 + m)).powerset :
      Set (Finset (ℕ × ℕ)))) ?_ ?_ (Finset.finite_toSet _)
  · intro lam hlam
    obtain ⟨hl, hrib, hcard⟩ := hlam
    obtain ⟨j, i1, hRM⟩ := RowMove.of_isRibbon hl hrib
    rw [hcard] at hRM
    have hj := hRM.j_lt hm
    rw [Finset.mem_coe, Finset.mem_powerset]
    rintro ⟨i, x⟩ hp
    have hp' : (i, x) ∈ lam := hp
    rw [YoungDiagram.mem_iff_lt_rowLen] at hp'
    have h1 := hRM.rowLen_le hm i
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    refine ⟨?_, by omega⟩
    by_contra hcon
    have h2 := hRM.outside i (Or.inr (by omega))
    have h3 : mu.rowLen i = 0 := by
      by_contra h4
      have : (i, 0) ∈ mu := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h4)
      rw [YoungDiagram.mem_iff_lt_colLen] at this
      omega
    omega
  · intro a _ b _ hab
    exact YoungDiagram.ext hab

/-- **Sorting the raised rows.**  In `N ≥ ℓ(μ) + m` rows, the sum over the raised β-numbers
of `μ` is the signed sum over the ribbon additions. -/
theorem sum_update_rows_eq {mu : YoungDiagram} {m : ℕ} (hm : 0 < m) {N : ℕ}
    (hN : mu.colLen 0 + m ≤ N) (T : Finset YoungDiagram)
    (hT : ∀ lam, lam ∈ T ↔ lam ∈ ribbonAdditions mu m) :
    ∑ k : Fin N, jtDet (Function.update (fun i : Fin N => (mu.rowLen i : ℤ) - i) k
        ((mu.rowLen k : ℤ) - k + m)) (fun j : Fin N => -(j : ℤ)) =
      ∑ lam ∈ T, (ribbonSign (skewDiagram lam mu) : Lambda) *
        jtDet (fun i : Fin N => (lam.rowLen i : ℤ) - i) (fun j : Fin N => -(j : ℤ)) := by
  classical
  have hMmu : ∀ i, N ≤ i → mu.rowLen i = 0 := fun i hi =>
    rowLen_eq_zero_of_colLen_le mu i (by omega)
  set a : Fin N → ℤ := fun i => (mu.rowLen i : ℤ) - i with ha
  set b0 : Fin N → ℤ := fun j => -(j : ℤ) with hb0
  have hmain : ∀ (j : ℕ) (hj : j < N) (nu : YoungDiagram) (i1 : ℕ), RowMove mu nu j i1 m →
      jtDet (Function.update a ⟨j, hj⟩ (a ⟨j, hj⟩ + m)) b0 =
        (ribbonSign (skewDiagram nu mu) : Lambda) *
          jtDet (fun i : Fin N => (nu.rowLen i : ℤ) - i) b0 := by
    intro j hj nu i1 hRM
    have h1 := jtDet_rows_update_eq hj hRM b0
    unfold ribbonSign ribbonHeight
    rw [hRM.numRows_eq hm]
    simp only [Nat.add_sub_cancel, Int.cast_pow, Int.cast_neg, Int.cast_one]
    exact h1
  have hex : ∀ k : Fin N, jtDet (Function.update a k (a k + m)) b0 ≠ 0 →
      ∃ nu i1, RowMove mu nu k.val i1 m ∧ nu ∈ ribbonAdditions mu m := by
    intro k hne
    have hinj : ∀ k', k' < N → k' ≠ k.val →
        (mu.rowLen k' : ℤ) - k' ≠ mu.rowLen k - k + m := by
      intro k' hk' hkk heq
      apply hne
      refine jtDet_rows_eq_zero_of_eq _ b0 (p := ⟨k', hk'⟩) (q := k)
        (fun h => hkk (by simpa using congrArg Fin.val h)) ?_
      rw [Function.update_of_ne (fun h => hkk (by simpa using congrArg Fin.val h)),
        Function.update_self]
      simpa [ha] using heq
    obtain ⟨nu, i1, hRM⟩ := exists_rowMove_of_injective hMmu k.isLt hm hinj
    exact ⟨nu, i1, hRM, hRM.le hm, hRM.isRibbon hm, hRM.card_eq hm⟩
  refine Finset.sum_bij_ne_zero (fun k _ hne => (hex k hne).choose) ?_ ?_ ?_ ?_
  · intro k _ hne
    exact (hT _).mpr (hex k hne).choose_spec.choose_spec.2
  · intro k1 _ h1 k2 _ h2 heq
    obtain ⟨i1, hRM1, -⟩ := (hex k1 h1).choose_spec
    obtain ⟨i2, hRM2, -⟩ := (hex k2 h2).choose_spec
    rw [← heq] at hRM2
    exact Fin.ext (hRM1.unique_j hm hRM2)
  · intro lam hlam hg
    obtain ⟨hl, hrib, hcard⟩ := (hT lam).mp hlam
    obtain ⟨j, i1, hRM⟩ := RowMove.of_isRibbon hl hrib
    rw [hcard] at hRM
    have hjN : j < N := lt_of_lt_of_le (hRM.j_lt hm) hN
    have hfg := hmain j hjN lam i1 hRM
    have hne : jtDet (Function.update a ⟨j, hjN⟩ (a ⟨j, hjN⟩ + m)) b0 ≠ 0 := by
      rw [hfg]; exact hg
    refine ⟨⟨j, hjN⟩, Finset.mem_univ _, hne, ?_⟩
    obtain ⟨i1', hRM', -⟩ := (hex ⟨j, hjN⟩ hne).choose_spec
    exact (hRM.unique_nu hm hRM').symm
  · intro k _ hne
    obtain ⟨i1, hRM, -⟩ := (hex k hne).choose_spec
    exact hmain k.val k.isLt _ i1 hRM

end MN

end Plan

end SkewGluing
