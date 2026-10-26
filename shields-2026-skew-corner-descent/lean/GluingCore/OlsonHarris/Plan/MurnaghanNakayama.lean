-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/MurnaghanNakayama.lean
import GluingCore.OlsonHarris.Plan.Defs
import GluingCore.OlsonHarris.Plan.MurnaghanNakayama.PowerSumSpan
import GluingCore.OlsonHarris.Plan.MurnaghanNakayama.Derivation
import GluingCore.OlsonHarris.Plan.MurnaghanNakayama.Ferrers

/-!
# The Murnaghan–Nakayama rule for one power sum

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.1.3 (`OlsonHarris2024HopfApplications`), Cor. 5.1.15
with Thm. 5.1.14, in the three forms the rest of the decomposition consumes.  The adjoint of
multiplication by `p_m` is the derivation `pDeriv m` of `Λ = ℚ[h₁, h₂, …]`.

* `pDeriv_cellSchur_left`, `pDeriv_cellSchur_right`: the derivation form for every skew diagram,
  `p_m^⊥ s_X = Σ_Y (-1)^{ht Y} s_{X \ Y}` over the ribbons `Y` of size `m` removable on the left,
  respectively on the right (`⟨p_m, s_Y⟩ = (-1)^{ht Y}` for a ribbon `Y` of size `m`, zero for
  other shapes, together with the coproduct formula);
* `pPoly_mul_cellSchur_ferrers`: the multiplication form (Murnaghan–Nakayama rule I for one power
  sum) on Ferrers shapes;
* `exists_pProd_expansion`: the `p_ν` span `Λ` over `ℚ`.

None of these uses the Hall inner product.  **Differs from the paper's route.**  The thesis reads
the derivation form off the coproduct and `⟨p_m, s_Y⟩`; here the Jacobi–Trudi determinant
`det (h_{λ_i - i - (μ_j - j)})` of a skew shape of Young diagrams is differentiated column by
column (`∂_m h_k = h_{k-m}`): a column index raised by `m` is either a repeated column or, after
sorting by a cycle, the determinant of the shape with a ribbon of `m` cells removed on the left,
with the sign of the cycle, and the nonzero terms are in bijection with the ribbons
(`RowMove`).  A general skew diagram is a translate of such a shape, and the right form follows
by rotation.  The multiplication form is proved in `N` variables: with `H = (h_{a_i + j})`
and the matrix `C` with `H C = (x_l^{a_i + N - 1})` one gets
`p_m det H = Σ_k det (H with the row `a_k` raised by `m`)`, and the same sorting gives the
ribbons; evaluations in all large `N` determine an element of `Λ`.  The spanning statement is
Newton's identity.

The proofs are in the modules under `MurnaghanNakayama/`: `Derivation` (left and right
derivation forms, from `LeftDeriv`, `Young`, `RowMoveDet`, `Raise`, `RowMove`, `RibbonCells`,
`Determinant`, `Beta`), `Ferrers` (the multiplication form, from `RightMul`, `Shift`) and
`PowerSumSpan`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

/-- **Murnaghan–Nakayama, derivation form, left.**  For a skew diagram `X` and `m > 0`,
`∂_m s_X = Σ_{Y ∈ leftRibbons X m} (-1)^{ht Y} s_{X \ Y}`.  True also for disconnected `X`. -/
theorem pDeriv_cellSchur_left {X : Diagram} (hX : IsSkew X) {m : ℕ} (hm : 0 < m) :
    pDeriv m (cellSchur X) = ribbonSumLeft cellSchur X m :=
  MN.pDeriv_cellSchur_left_of_isSkew hX hm

open scoped Classical in
/-- A diagram with fewer than `n` diagonals has no ribbon of size `n`, since a ribbon of size
`n` occupies `n` diagonals. -/
theorem leftRibbons_eq_empty_of_span_lt {X : Diagram} {n : ℕ} (h : span X < n) :
    leftRibbons X n = ∅ := by
  ext Y
  rw [mem_leftRibbons]
  simp only [Finset.notMem_empty, iff_false]
  rintro ⟨hY, hcard, hrib, -⟩
  have h1 : span Y ≤ span X := by
    apply Finset.card_le_card
    exact Finset.image_subset_image hY
  have := hrib.2
  omega

/-- A derivation kills a finite product if it kills each factor. -/
theorem pDeriv_prod_eq_zero {ι : Type*} (D : Derivation ℚ Lambda Lambda) (s : Finset ι)
    (f : ι → Lambda) (h : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, h a (Finset.mem_insert_self _ _),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
    simp

open scoped Classical in
/-- **A diagram with fewer than `n` diagonals is killed by `p_n^⊥`** (Murnaghan–Nakayama:
`pDeriv_cellSchur_left` on each connected component, which has no ribbon of size `n`). -/
theorem pDeriv_cellSchur_eq_zero_of_span_lt {Z : Diagram} {n : ℕ} (h : span Z < n) :
    pDeriv n (cellSchur Z) = 0 := by
  have hn : 0 < n := by omega
  unfold cellSchur
  refine pDeriv_prod_eq_zero _ _ _ fun C hC => ?_
  by_cases hconn : IsConnectedSkew C
  · rw [connectedSchur_of_isConnectedSkew hconn, ← cellSchur_of_isConnectedSkew hconn,
      pDeriv_cellSchur_left hconn.1 hn]
    have hsp : span C ≤ span Z :=
      Finset.card_le_card (Finset.image_subset_image (component_subset hC))
    rw [ribbonSumLeft, leftRibbons_eq_empty_of_span_lt (by omega)]
    simp
  · unfold connectedSchur
    simp only [hconn, ↓reduceIte]
    exact Derivation.map_one_eq_zero _

/-- **Murnaghan–Nakayama, derivation form, right.**  As `pDeriv_cellSchur_left` with the ribbons
removable on the right (it follows from the left form by rotation). -/
theorem pDeriv_cellSchur_right {X : Diagram} (hX : IsSkew X) {m : ℕ} (hm : 0 < m) :
    pDeriv m (cellSchur X) = ribbonSumRight cellSchur X m :=
  MN.pDeriv_cellSchur_right_of_isSkew hX hm

open scoped Classical in
/-- **Murnaghan–Nakayama rule I for one power sum, on Ferrers shapes.**
`p_m · s_μ = Σ_λ (-1)^{ht(λ/μ)} s_λ`, the sum over the partitions `λ ⊇ μ` such that `λ / μ` is a
ribbon with `m` cells.  (A finite sum; `finsum` records that the sum has finite support. -/
theorem pPoly_mul_cellSchur_ferrers (mu : YoungDiagram) {m : ℕ} (hm : 0 < m) :
    pPoly m * cellSchur (skewDiagram mu ⊥) =
      ∑ᶠ lam : YoungDiagram,
        if mu ≤ lam ∧ IsRibbon (skewDiagram lam mu) ∧ (skewDiagram lam mu).card = m then
          (ribbonSign (skewDiagram lam mu) : Lambda) * cellSchur (skewDiagram lam ⊥)
        else 0 :=
  MN.pPoly_mul_cellSchur_ferrers_eq mu hm

/-- **The power sums span `Λ`.**  Every element of `Λ` is a rational combination of products
`p_ν` of power sums with positive parts (Newton's identity expresses each `h_n` through the
`p_i`). -/
theorem exists_pProd_expansion (f : Lambda) :
    ∃ l : List (ℚ × List ℕ), (∀ p ∈ l, ∀ m ∈ p.2, 0 < m) ∧
      f = (l.map fun p => p.1 • pProd p.2).sum :=
  MN.exists_pProd_expansion_aux (MN.mem_pProdSpan f)

end Plan

end GluingCore
