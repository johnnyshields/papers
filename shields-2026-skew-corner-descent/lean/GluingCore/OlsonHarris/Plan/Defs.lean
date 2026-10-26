-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/Defs.lean
import GluingCore.CellSchur
import GluingCore.Composition
import GluingCore.OlsonHarris.Cited

/-!
# Definitions for the decomposition of the Olson-Harris composition theorem

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the vocabulary in which the proof of Olson-Harris, Thm. 5.3.9
(`OlsonHarris2024HopfApplications`, Chapter 5), is split into independent statements.

* **Ribbons.**  `IsRibbon`, `ribbonHeight`, `leftRibbons X m` (ribbons of size `m` that are
  downsets of `X`: *removable on the left*, `X ≥ Y` in the thesis) and `rightRibbons X m`
  (ribbons that are upsets of `X`: removable on the right).
* **The shape space** `ShapeSpace = (Diagram →₀ ℚ)` (a basis element `shape X` for each cell set,
  translates identified only through `shapeKernelSpan`) with the ribbon-removal operators
  `leftOp m`, `rightOp m`, the words `leftWord ν`, `rightWord ν`, the Schur map `shapeSchur` and
  the span `shapeKernelSpan` of the relations `f ⇀ h - h ↼ f` (Thm. 5.2.2).
* **Symmetric functions.**  `pPoly m` (the power sum `p_m` in the `h`-variables, Newton
  recursion), `pProd ν`, and the derivation `pDeriv m = p_m^⊥` of `Λ = ℚ[h₁, h₂, …]` with
  `∂_m h_n = h_{n-m}`.
* **Key ribbons.**  `nwBorder E` (the northwest border), `keyRibbon ω` (the top key ribbon
  `K↑(E)` of a mark) and `liftRibbon ω X A` (the copies of `K↑(E)` at the cells of `A`, which
  is `A ∘ K↑(E)` for a ribbon `A` of `X`).
* **Modified composition.**  `hatMiddleFin`, `hatMarkFin` (the shapes `\overline O`,
  `\overline W` of the thesis), `hatFactor ω = s_W s_{\overline W} s_{\overline O}`,
  `modComp ω X` (the Schur function of `[X] □_W E`, thesis (5.13), extended multiplicatively over
  the edge components of `X`), and its corner variant `modCompC` with the sign `(-1)^{ξ}` of
  thesis (5.14).
* **The compatibility predicates** `EdgeCompat ω` and `CornerCompat ω`, which say that `modComp`
  intertwines `p_{mq}^⊥` with ribbon removal (thesis Lemma 5.4.7 and Thm. 5.4.9; Lemmas 5.5.12
  and 5.5.13 and the proof of Thm. 5.5.14).

Everything here is a definition or a checked example.

Sorry-free.
-/

namespace GluingCore

namespace Plan

open MvPolynomial

/-! ### Ribbons and their removal -/

/-- A ribbon: a connected skew diagram with no two cells on one diagonal, i.e. one cell per
occupied diagonal (`|Y| = N_Y`). -/
def IsRibbon (Y : Diagram) : Prop := IsConnectedSkew Y ∧ Y.card = span Y

instance (Y : Diagram) : Decidable (IsRibbon Y) := by unfold IsRibbon; infer_instance

/-- The height of a ribbon: its number of rows minus one. -/
def ribbonHeight (Y : Diagram) : ℕ := numRows Y - 1

/-- The sign `(-1)^{ht Y}` of a ribbon. -/
def ribbonSign (Y : Diagram) : ℤ := (-1) ^ ribbonHeight Y

/-- `Y` is a downset of `X` for the northwest order: `Y ≤ X` in the thesis, so `X \ Y` is
*removable on the left*. -/
def IsDownsetIn (X Y : Diagram) : Prop :=
  Y ⊆ X ∧ ∀ x ∈ X, ∀ y ∈ Y, x.1 ≤ y.1 → x.2 ≤ y.2 → x ∈ Y

/-- `Y` is an upset of `X` for the northwest order: `X \ Y ≤ X`, so `Y` is *removable on the
right*. -/
def IsUpsetIn (X Y : Diagram) : Prop :=
  Y ⊆ X ∧ ∀ x ∈ X, ∀ y ∈ Y, y.1 ≤ x.1 → y.2 ≤ x.2 → x ∈ Y

instance (X Y : Diagram) : Decidable (IsDownsetIn X Y) := by unfold IsDownsetIn; infer_instance
instance (X Y : Diagram) : Decidable (IsUpsetIn X Y) := by unfold IsUpsetIn; infer_instance

/-- The ribbons of size `m` removable on the left from `X`: the ribbons that are downsets. -/
def leftRibbons (X : Diagram) (m : ℕ) : Finset Diagram :=
  X.powerset.filter fun Y => Y.card = m ∧ IsRibbon Y ∧ IsDownsetIn X Y

/-- The ribbons of size `m` removable on the right from `X`: the ribbons that are upsets. -/
def rightRibbons (X : Diagram) (m : ℕ) : Finset Diagram :=
  X.powerset.filter fun Y => Y.card = m ∧ IsRibbon Y ∧ IsUpsetIn X Y

theorem mem_leftRibbons {X Y : Diagram} {m : ℕ} :
    Y ∈ leftRibbons X m ↔ Y ⊆ X ∧ Y.card = m ∧ IsRibbon Y ∧ IsDownsetIn X Y := by
  unfold leftRibbons
  rw [Finset.mem_filter, Finset.mem_powerset]

theorem mem_rightRibbons {X Y : Diagram} {m : ℕ} :
    Y ∈ rightRibbons X m ↔ Y ⊆ X ∧ Y.card = m ∧ IsRibbon Y ∧ IsUpsetIn X Y := by
  unfold rightRibbons
  rw [Finset.mem_filter, Finset.mem_powerset]

/-- The signed ribbon-removal sum `Σ_{Y ∈ leftRibbons X m} (-1)^{ht Y} F (X \ Y)`. -/
noncomputable def ribbonSumLeft (F : Diagram → Lambda) (X : Diagram) (m : ℕ) : Lambda :=
  ∑ Y ∈ leftRibbons X m, (ribbonSign Y : Lambda) * F (X \ Y)

/-- The signed ribbon-removal sum `Σ_{Y ∈ rightRibbons X m} (-1)^{ht Y} F (X \ Y)`. -/
noncomputable def ribbonSumRight (F : Diagram → Lambda) (X : Diagram) (m : ℕ) : Lambda :=
  ∑ Y ∈ rightRibbons X m, (ribbonSign Y : Lambda) * F (X \ Y)

section RibbonExamples

/-- The hook `(2, 1)` has two ribbons of size `2` removable on the left: the first row and the
first column. -/
example : (leftRibbons (skewOf [2, 1] []) 2).card = 2 := by decide

/-- No ribbon of size `2` of the hook is an upset: an upset meeting the origin is everything. -/
example : (rightRibbons (skewOf [2, 1] []) 2).card = 0 := by decide

/-- Size one: the hook has one box removable on the left and two on the right. -/
example : (leftRibbons (skewOf [2, 1] []) 1).card = 1 := by decide
example : (rightRibbons (skewOf [2, 1] []) 1).card = 2 := by decide

/-- The whole hook is a ribbon of size three and height one, removable on the left. -/
example : leftRibbons (skewOf [2, 1] []) 3 = {skewOf [2, 1] []} := by decide
example : ribbonHeight (skewOf [2, 1] []) = 1 := by decide

end RibbonExamples

/-! ### The shape space and the two actions -/

/-- The free `ℚ`-space on cell diagrams.  The thesis's shape Hopf algebra is the quotient by
the span of the differences of translates; here the translations are part of
`shapeKernelSpan`. -/
abbrev ShapeSpace : Type := Diagram →₀ ℚ

/-- The basis element of a diagram. -/
noncomputable def shape (X : Diagram) : ShapeSpace := Finsupp.single X 1

/-- `h ↦ h ↼ p_m`: remove a ribbon of size `m` from the left, with sign `(-1)^{ht}`
(Murnaghan–Nakayama for one power sum, thesis Cor. 5.1.15). -/
noncomputable def leftOp (m : ℕ) : ShapeSpace →ₗ[ℚ] ShapeSpace :=
  Finsupp.linearCombination ℚ fun X =>
    ∑ Y ∈ leftRibbons X m, ((ribbonSign Y : ℚ)) • shape (X \ Y)

/-- `h ↦ p_m ⇀ h`: remove a ribbon of size `m` from the right, with sign `(-1)^{ht}`. -/
noncomputable def rightOp (m : ℕ) : ShapeSpace →ₗ[ℚ] ShapeSpace :=
  Finsupp.linearCombination ℚ fun X =>
    ∑ Y ∈ rightRibbons X m, ((ribbonSign Y : ℚ)) • shape (X \ Y)

/-- The action of `p_ν = p_{ν₁} p_{ν₂} ⋯` on the right: `ν₁` is removed first. -/
noncomputable def leftWord : List ℕ → ShapeSpace →ₗ[ℚ] ShapeSpace
  | [] => LinearMap.id
  | m :: ν => (leftWord ν).comp (leftOp m)

/-- The action of `p_ν = p_{ν₁} p_{ν₂} ⋯` on the left: `ν₁` is removed last. -/
noncomputable def rightWord : List ℕ → ShapeSpace →ₗ[ℚ] ShapeSpace
  | [] => LinearMap.id
  | m :: ν => (rightOp m).comp (rightWord ν)

/-- The skew Schur function of a formal combination of diagrams (`schur : S → Sym`). -/
noncomputable def shapeSchur : ShapeSpace →ₗ[ℚ] Lambda :=
  Finsupp.linearCombination ℚ cellSchur

/-- The relations of the shape space: translates are identified, and `p_ν ⇀ h = h ↼ p_ν`
(thesis Thm. 5.2.2: these span the kernel of `schur`).  Words have positive parts and the
generating diagrams are skew. -/
noncomputable def shapeKernelSpan : Submodule ℚ ShapeSpace :=
  Submodule.span ℚ
    ({h | ∃ (X : Diagram) (v : ℤ × ℤ), IsSkew X ∧ h = shape X - shape (translate v X)} ∪
     {h | ∃ (ν : List ℕ) (Z : Diagram), (∀ m ∈ ν, 0 < m) ∧ IsSkew Z ∧
        h = rightWord ν (shape Z) - leftWord ν (shape Z)})

/-- A formal combination supported on skew diagrams. -/
def IsSkewSupported (h : ShapeSpace) : Prop := ∀ X ∈ h.support, IsSkew X

/-! ### Symmetric functions in the `h`-variables -/

/-- The power sum `p_m ∈ Λ = ℚ[h₁, h₂, …]`, by Newton's recursion
`m h_m = Σ_{i=1}^{m} p_i h_{m-i}`; `p_0 = 0`. -/
noncomputable def pPoly : ℕ → Lambda
  | 0 => 0
  | n + 1 => ((n + 1 : ℕ) : Lambda) * hPos (n + 1) -
      ∑ i : Fin n, pPoly (i + 1) * hPos (n - i)
termination_by n => n
decreasing_by
  have := i.isLt
  omega

/-- The product `p_ν = p_{ν₁} p_{ν₂} ⋯`. -/
noncomputable def pProd (ν : List ℕ) : Lambda := (ν.map pPoly).prod

/-- The derivation `p_m^⊥ = m ∂/∂p_m` of `Λ`: the derivation with `∂_m h_n = h_{n-m}`
(`h₀ = 1`, `h_{j} = 0` for `j < 0`).  It is the adjoint of multiplication by `p_m`. -/
noncomputable def pDeriv (m : ℕ) : Derivation ℚ Lambda Lambda :=
  MvPolynomial.mkDerivation ℚ fun k : ℕ+ => hh ((k : ℤ) - m)

/-- The composite `∂_{ν₁}` first, then `∂_{ν₂}`, and so on. -/
noncomputable def pDerivWord : List ℕ → Lambda →ₗ[ℚ] Lambda
  | [] => LinearMap.id
  | m :: ν => (pDerivWord ν).comp (pDeriv m).toLinearMap

theorem pDeriv_X (m : ℕ) (k : ℕ+) : pDeriv m (X k) = hh ((k : ℤ) - m) := by
  unfold pDeriv
  exact MvPolynomial.mkDerivation_X ℚ _ k

/-- `p_1 = h₁` and `p_2 = 2 h₂ - h₁²`. -/
example : pPoly 1 = X 1 := by
  change pPoly (0 + 1) = X 1
  rw [pPoly]
  simp [hPos]

example : pPoly 2 = 2 * X 2 - X 1 ^ 2 := by
  change pPoly (1 + 1) = _
  rw [pPoly]
  simp only [Fin.sum_univ_one]
  change _ - pPoly (0 + 1) * hPos (1 - 0) = _
  rw [pPoly]
  simp [hPos]
  ring

/-- `∂_1 h₃ = h₂`. -/
example : pDeriv 1 (X 3) = X 2 := by
  rw [pDeriv_X]
  simpa using hh_pnat 2

/-! ### The modified composition -/

/-- The union `𝐄 = ⋃_k (E + k v)` of the periodic copies, restricted to the copies
`-2 ≤ k ≤ 2`, which are the only ones that meet the hatted mark of a legal mark. -/
def periodicWindow (ω : MarkedInner) : Diagram :=
  (Finset.Icc (-2 : ℤ) 2).biUnion fun k => translate (k • ω.v) ω.E

/-- The hatted middle `\overline O = {x ∈ O : x + e ∈ O}` of thesis §5.3.1. -/
def hatMiddleFin (ω : MarkedInner) : Diagram :=
  ω.middle.filter fun x => x + eCell ∈ ω.middle

/-- The hatted mark `\overline W = {x ∈ 𝐄 : x + e ∈ W₋} ∪ {x ∈ W₋ : x + e ∈ 𝐄}` of thesis
§5.3.1, for the copy `W₋` of the mark (`MarkedInner.hatMark`, with the periodic copies
`-2 ≤ k ≤ 2`). -/
def hatMarkFin (ω : MarkedInner) : Diagram :=
  (ω.W.image fun y => y - eCell).filter (fun x => x + eCell ∈ ω.W ∧ x ∈ periodicWindow ω) ∪
    ω.W.filter fun x => x + eCell ∈ periodicWindow ω

/-- The factor `s_W · s_{\overline W} · s_{\overline O}` of thesis Lemmas 5.4.7 and 5.5.12
(without the sign `(-1)^{h(E)}`, which is carried by `edgeSign`). -/
noncomputable def hatFactor (ω : MarkedInner) : Lambda :=
  cellSchur ω.W * cellSchur (hatMarkFin ω) * cellSchur (hatMiddleFin ω)

/-- The modified composition (thesis (5.13)) of a connected diagram `C`, as a Schur function:
`s_W^{|C| - row C} s_{\overline W}^{|C| - col C} s_{\overline O}^{|C| - dia C} s_{C ∘_ω E}`. -/
noncomputable def componentT (ω : MarkedInner) (C : Diagram) : Lambda :=
  cellSchur ω.W ^ (C.card - numRows C) * cellSchur (hatMarkFin ω) ^ (C.card - numCols C) *
    cellSchur (hatMiddleFin ω) ^ (C.card - span C) * cellSchur (ω.compose C)

/-- The modified composition of a skew diagram, multiplicative over its edge components
(thesis: `(D ⊔ D') ∘_W E = (D ∘_W E) ⊔ (D' ∘_W E)`, and rows, columns and diagonals add). -/
noncomputable def modComp (ω : MarkedInner) (X : Diagram) : Lambda :=
  ∏ C ∈ edgeComponents X, componentT ω C

/-- The number `ξ(C)` of northbound boxes of a connected diagram `C` for a mark of case (c):
the boxes with a box to the north on the same northwest ribbon, i.e. the boxes at which the
mixed composition carries a supplemental copy. -/
def northbound (ω : MarkedInner) (C : Diagram) : ℕ := (C.filter (ω.SameRibbon C)).card

/-- The corner variant of `componentT` (thesis (5.14)): the sign `(-1)^{ξ(C)}` is included. -/
noncomputable def componentTc (ω : MarkedInner) (C : Diagram) : Lambda :=
  (-1 : Lambda) ^ northbound ω C * componentT ω C

/-- The corner modified composition of a skew diagram. -/
noncomputable def modCompC (ω : MarkedInner) (X : Diagram) : Lambda :=
  ∏ C ∈ edgeComponents X, componentTc ω C

/-- The sign in thesis Lemma 5.4.7 (case (a)) and Thm. 5.4.9 (case (b)), for the `m`-th power:
`(-1)^{m h(E)}` with `h(E) = |v₁|` in case (a), and `(-1)^{m - 1} (-1)^{m (h(E))}` with
`h(E) = |v₁| - 1 (mod 2)` in case (b) (the twist `ω(p_m) = (-1)^{m-1} p_m` of Thm. 5.4.9). -/
def edgeSign (ω : MarkedInner) (m : ℕ) : ℤ :=
  match ω.case with
  | .b => -((-1) ^ (m * ω.v.1.natAbs))
  | _ => (-1) ^ (m * ω.v.1.natAbs)

/-- The two edge equations at a diagram `X` and a size `m` (thesis Lemma 5.4.7 for case (a),
Thm. 5.4.9 for case (b), in the form obtained by applying `schur`): the modified composition
intertwines `p_{mq}^⊥` with signed ribbon removal on the left, and with signed ribbon removal on
the right, up to the factor `± (s_W s_{\overline W} s_{\overline O})^m`. -/
def EdgeEq (ω : MarkedInner) (X : Diagram) (m : ℕ) : Prop :=
  pDeriv (m * ω.period.toNat) (modComp ω X) =
      (edgeSign ω m : Lambda) * hatFactor ω ^ m * ribbonSumLeft (modComp ω) X m ∧
    pDeriv (m * ω.period.toNat) (modComp ω X) =
      (edgeSign ω m : Lambda) * hatFactor ω ^ m * ribbonSumRight (modComp ω) X m

/-- The corner equations at `X` and `m` (thesis Lemmas 5.5.12 and 5.5.13 and the proof of
Thm. 5.5.14, in the form obtained by applying `schur`): the corner modified composition is
killed by `p_{mq}^⊥`, and signed ribbon removal on the left and on the right agree on it. -/
def CornerEq (ω : MarkedInner) (X : Diagram) (m : ℕ) : Prop :=
  pDeriv (m * ω.period.toNat) (modCompC ω X) = 0 ∧
    ribbonSumRight (modCompC ω) X m = ribbonSumLeft (modCompC ω) X m

/-- The edge equations hold at every skew diagram and every `m > 0`. -/
def EdgeCompat (ω : MarkedInner) : Prop :=
  ∀ X : Diagram, IsSkew X → ∀ m : ℕ, 0 < m → EdgeEq ω X m

/-- The corner equations hold at every skew diagram and every `m > 0`. -/
def CornerCompat (ω : MarkedInner) : Prop :=
  ∀ X : Diagram, IsSkew X → ∀ m : ℕ, 0 < m → CornerEq ω X m

/-! ### Checks of the hat shapes on the worked marks -/

/-- On the chart-figure mark, `\overline W` is the single cell `(-1, -1)` and `\overline O` is
empty. -/
example : hatMarkFin chartFigureInner = {(-1, -1)} := by decide +kernel
example : hatMiddleFin chartFigureInner = ∅ := by decide +kernel

/-- On `gaugeInnerA`, `\overline W = {(1, -1), (1, 0)}` and `\overline O = ∅`. -/
example : hatMarkFin gaugeInnerA = {(1, -1), (1, 0)} := by decide +kernel
example : hatMiddleFin gaugeInnerA = ∅ := by decide +kernel

/-- The northwest border of a diagram: the cells with no cell of the diagram to the northwest on
their diagonal. -/
def nwBorder (E : Diagram) : Diagram := E.filter fun z => z - eCell ∉ E

/-- The top key ribbon `K↑(E)` of a mark (thesis §5.3.3): the cells of the northwest border of `E`
on the `q` contents ending at the greatest content of the middle. -/
def keyRibbon (ω : MarkedInner) : Diagram :=
  (nwBorder ω.E).filter fun z =>
    maxContent ω.middle - ω.period < content z ∧ content z ≤ maxContent ω.middle

/-- The copies of the top key ribbon at the cells of `A`: `A ∘ K↑(E)`. -/
def liftRibbon (ω : MarkedInner) (X A : Diagram) : Diagram :=
  A.biUnion fun b => translate (ω.origin X b) (keyRibbon ω)

end Plan

end GluingCore
