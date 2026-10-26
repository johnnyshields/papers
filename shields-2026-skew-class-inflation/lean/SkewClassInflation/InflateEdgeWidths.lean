/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateConnected
import SkewClassInflation.InflateBridge
import SkewGluing.OrdinaryFold.Mark
import SkewGluing.MarkLocality

/-!
# The two edge widths of `lem:inflate-chart`

Formalizes the second and third assertions of `lem:inflate-chart` in
`shields-2026-skew-class-inflation.tex`, the alternatives at width zero and at width `q - 1`.

* **Width zero.**  For a connected inner `V` of span `q ≥ 2` with `A_V(1) = B_V(q - 1) = 0`, the
  inflation `I(V)` carries the singleton end mark `(a)` at `sw(V)` and `ne(V) + (0, 1)` with the
  original displacement `v_H`, a legal ordinary mark of period `q` and width one (`SlotGeom` with
  `w = 1`, `σ = 1`, `τ = 0`), and its marked composition with every nonempty outer is the cell
  inflation of the empty-mark composition (`singletonMark_compose`).
* **Width `q - 1`.**  The atom `𝒜(W)` of a mark `W` of span `w`, the one-middle-cell inner of case
  `(a)`, is a legal mark of period `w + 1` and width `w` (`atomMark_isLegal`), and
  `I(C ∘_W 𝒜(W)) = I(C) ∘_∅ I(W)` (`atomMark_compose_inflate`).

The inner is read in the position with least content zero, the normalization of `SlotGeom`.
Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing

/-! ### Diagonal data of a connected diagram -/

/-- A connected skew diagram with least content zero is described by its diagonal intervals. -/
theorem diagSet_shape_of_connected {E : Diagram} (hE : IsConnectedSkew E) (h0 : minContent E = 0) :
    DiagSet E 0 (maxContent E) (diagLo E) (diagHi E) ∧
      DiagShape 0 (maxContent E) (diagLo E) (diagHi E) := by
  have hs := isConnectedSkew_iff_diagonal.mp hE
  have hne : E.Nonempty := hs.1
  have hce := hs.contents_eq
  have hle : minContent E ≤ maxContent E := minContent_le (maxContent_mem hne)
  have hc : ∀ k : ℤ, k ∈ contents E ↔ 0 ≤ k ∧ k ≤ maxContent E := by
    intro k
    rw [hce, Finset.mem_Icc, h0]
  refine ⟨fun i k => ?_, ?_⟩
  · rw [hs.mem_iff, hc, and_assoc]
  · refine ⟨by omega, fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_, ?_, ?_⟩
    · exact diagLo_le_diagHi ((hc k).mpr ⟨h1, h2⟩)
    · have := (hs.2.2.2.1 k ((hc k).mpr ⟨by omega, h2⟩) ((hc (k - 1)).mpr ⟨by omega, by omega⟩)).1
      simpa [bitA] using this
    · have := (hs.2.2.2.1 k ((hc k).mpr ⟨by omega, h2⟩) ((hc (k - 1)).mpr ⟨by omega, by omega⟩)).2
      simpa [bitB] using this
    · exact hs.2.2.2.2 0 ((hc 0).mpr ⟨le_rfl, by omega⟩)
        (Or.inl (fun h => by have := (hc (0 - 1)).mp h; omega))
    · exact hs.2.2.2.2 (maxContent E) ((hc _).mpr ⟨by omega, le_rfl⟩)
        (Or.inr (fun h => by have := (hc (maxContent E + 1)).mp h; omega))

theorem contents_inflateCells {D : Diagram} (hD : IsConnectedSkew D) :
    contents (inflateCells D) = Finset.Icc (minContent D) (maxContent D + 1) := by
  have hd := (inflateCells_diagonals hD).2
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hne := hs.1
  have hce := hs.contents_eq
  have hle : minContent D ≤ maxContent D := minContent_le (maxContent_mem hne)
  have hLH : ∀ k ∈ contents D, diagLo D k ≤ diagHi D k := fun k hk => diagLo_le_diagHi hk
  ext k
  rw [mem_contents_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi⟩
    have := (hd i k).mp (by simpa using hi)
    exact ⟨this.1, this.2.1⟩
  · rintro ⟨h1, h2⟩
    have hk1 : min k (maxContent D) ∈ contents D := by
      rw [hce, Finset.mem_Icc]; constructor <;> omega
    have hk2 : max (k - 1) (minContent D) ∈ contents D := by
      rw [hce, Finset.mem_Icc]; constructor <;> omega
    refine ⟨diagLo D (min k (maxContent D)), ?_⟩
    have := (hd (diagLo D (min k (maxContent D))) k).mpr ⟨h1, h2, le_rfl, ?_⟩
    · simpa using this
    · have e1 := hLH _ hk1
      have e2 := hLH _ hk2
      have hs' := hs
      by_cases hk : k ≤ maxContent D
      · rw [min_eq_left hk]
        by_cases hk' : minContent D < k
        · rw [max_eq_left (by omega)]
          have := hs.diagLo_anti (a := k - 1) (b := k) ((hce ▸ Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
            (hce ▸ Finset.mem_Icc.mpr ⟨by omega, hk⟩) (by omega)
          have h3 := hs.diagHi_anti (a := k - 1) (b := k) ((hce ▸ Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
            (hce ▸ Finset.mem_Icc.mpr ⟨by omega, hk⟩) (by omega)
          have e3 := hLH k (by rw [hce, Finset.mem_Icc]; omega)
          omega
        · have : k = minContent D := by omega
          subst this
          rw [max_eq_right (by omega)]
          exact hLH _ (by rw [hce, Finset.mem_Icc]; omega)
      · rw [min_eq_right (by omega), show maxContent D = k - 1 by omega, max_eq_left (by omega)]
        have : k - 1 = maxContent D := by omega
        rw [this]
        exact hLH _ (by rw [hce, Finset.mem_Icc]; omega)


/-! ### Diagonals of the cell inflation -/

theorem diagLo_inflateCells {E : Diagram} (hE : IsConnectedSkew E) {k : ℤ}
    (h1 : minContent E ≤ k) (h2 : k ≤ maxContent E + 1) :
    diagLo (inflateCells E) k = diagLo E (min k (maxContent E)) := by
  have hd := (inflateCells_diagonals hE).2
  have hk : k ∈ contents (inflateCells E) := by
    rw [contents_inflateCells hE, Finset.mem_Icc]; exact ⟨h1, h2⟩
  obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
  have hi' := (hd i k).mp hi
  have hne : diagLo E (min k (maxContent E)) ≤ diagHi E (max (k - 1) (minContent E)) :=
    hi'.2.2.1.trans hi'.2.2.2
  apply diagLo_eq_of ((hd _ k).mpr ⟨h1, h2, le_rfl, hne⟩)
  intro j hj
  exact ((hd j k).mp hj).2.2.1

theorem diagHi_inflateCells {E : Diagram} (hE : IsConnectedSkew E) {k : ℤ}
    (h1 : minContent E ≤ k) (h2 : k ≤ maxContent E + 1) :
    diagHi (inflateCells E) k = diagHi E (max (k - 1) (minContent E)) := by
  have hd := (inflateCells_diagonals hE).2
  have hk : k ∈ contents (inflateCells E) := by
    rw [contents_inflateCells hE, Finset.mem_Icc]; exact ⟨h1, h2⟩
  obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
  have hi' := (hd i k).mp hi
  have hne : diagLo E (min k (maxContent E)) ≤ diagHi E (max (k - 1) (minContent E)) :=
    hi'.2.2.1.trans hi'.2.2.2
  apply diagHi_eq_of ((hd _ k).mpr ⟨h1, h2, hne, le_rfl⟩)
  intro j hj
  exact ((hd j k).mp hj).2.2.2

theorem minContent_inflateCells {E : Diagram} (hE : IsConnectedSkew E) :
    minContent (inflateCells E) = minContent E := by
  have hle : minContent E ≤ maxContent E :=
    minContent_le (maxContent_mem (isConnectedSkew_iff_diagonal.mp hE).1)
  apply minContent_eq_of
  · rw [contents_inflateCells hE, Finset.mem_Icc]; omega
  · intro k hk
    rw [contents_inflateCells hE, Finset.mem_Icc] at hk
    exact hk.1

theorem maxContent_inflateCells {E : Diagram} (hE : IsConnectedSkew E) :
    maxContent (inflateCells E) = maxContent E + 1 := by
  have hle : minContent E ≤ maxContent E :=
    minContent_le (maxContent_mem (isConnectedSkew_iff_diagonal.mp hE).1)
  apply maxContent_eq_of
  · rw [contents_inflateCells hE, Finset.mem_Icc]; omega
  · intro k hk
    rw [contents_inflateCells hE, Finset.mem_Icc] at hk
    exact hk.2

/-! ### Width zero: the singleton end mark -/

theorem compose_eq_of_ordinary {ω ω' : MarkedInner} (hE : ω.E = ω'.E) (hv : ω.v = ω'.v)
    (hc : ω.case = ω'.case) (ho : ¬ ω.case.IsMixed) {D : Diagram} (hD : D.Nonempty) :
    ω.compose D = ω'.compose D := by
  have ho' : ¬ ω'.case.IsMixed := hc ▸ ho
  ext x
  rw [MarkedInner.compose_of_ordinary hD ho, MarkedInner.compose_of_ordinary hD ho']
  have : ∀ d, ω.origin D d = ω'.origin D d := by
    intro d
    unfold MarkedInner.origin
    rw [hc, hv]
  simp only [this, hE]

/-- The slot data of the inflated width-zero inner: period `q = N_V`, width one, phases
`σ = 1`, `τ = 0`, from `A_V(1) = 0` and `B_V(q - 1) = 0`. -/
theorem singleton_slotGeom {E : Diagram} (hE : IsConnectedSkew E) (h0 : minContent E = 0)
    (hq : 1 ≤ maxContent E) (hA : diagLo E 0 = diagLo E 1)
    (hB : diagHi E (maxContent E - 1) = diagHi E (maxContent E)) :
    DiagSet (inflateCells E) 0 (maxContent E + 1 + 1 - 1) (diagLo (inflateCells E))
        (diagHi (inflateCells E)) ∧
      SlotGeom (maxContent E + 1) 1 0 1 (diagLo E (maxContent E) - diagLo E 0)
        (diagLo (inflateCells E)) (diagHi (inflateCells E)) := by
  have hI := isConnectedSkew_inflateCells hE
  have hmin := minContent_inflateCells hE
  have hmax := maxContent_inflateCells hE
  rw [h0] at hmin
  obtain ⟨hS, hSh⟩ := diagSet_shape_of_connected hI hmin
  rw [hmax] at hS hSh
  obtain ⟨hS0, hSh0⟩ := diagSet_shape_of_connected hE h0
  have e0 := hSh0.endLo
  have e1 := hSh0.endHi
  have hne := hSh0.ne
  set c := maxContent E with hc
  have L : ∀ k, 0 ≤ k → k ≤ c + 1 → diagLo (inflateCells E) k = diagLo E (min k c) :=
    fun k h1 h2 => diagLo_inflateCells hE (by omega) h2
  have H : ∀ k, 0 ≤ k → k ≤ c + 1 → diagHi (inflateCells E) k = diagHi E (max (k - 1) 0) :=
    fun k h1 h2 => by rw [diagHi_inflateCells hE (by omega) h2, h0]
  refine ⟨by simpa using hS, ?_⟩
  have sh : DiagShape 0 (c + 1 + 1 - 1) (diagLo (inflateCells E)) (diagHi (inflateCells E)) := by
    simpa using hSh
  have L0 := L 0 le_rfl (by omega)
  have L1 := L 1 (by omega) (by omega)
  have Lc := L c (by omega) (by omega)
  have Lc1 := L (c + 1) (by omega) le_rfl
  have H0 := H 0 le_rfl (by omega)
  have H1 := H 1 (by omega) (by omega)
  have Hc := H c (by omega) (by omega)
  have Hc1 := H (c + 1) (by omega) le_rfl
  simp only [min_eq_left (show (0 : ℤ) ≤ c by omega), min_eq_left (show (1 : ℤ) ≤ c by omega),
    min_self, min_eq_right (show c ≤ c + 1 by omega), zero_sub, add_sub_cancel_right, sub_self,
    max_eq_right (show (-1 : ℤ) ≤ 0 by omega), max_self,
    max_eq_left (show (0 : ℤ) ≤ c by omega)] at L0 L1 Lc Lc1 H0 H1 Hc Hc1
  have hmx : max (c - 1) 0 = c - 1 := max_eq_left (by omega)
  have e1' := hB
  refine ⟨le_rfl, by omega, le_rfl, le_rfl, le_rfl, by omega, sh, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro r h1 h2; omega
  · intro r h1 h2
    have : r = 0 := by omega
    subst this
    rw [show (c + 1 + 0) = c + 1 by ring, Lc1, L0]
    omega
  · intro r h1 h2
    have : r = 0 := by omega
    subst this
    rw [show (c + 1 + 0) = c + 1 by ring, Hc1, H0]
    omega
  · intro r h1 h2; omega
  · rw [L1, H1]; omega
  · rw [show (c + 1 - 1) = c by ring, Lc, Hc]
    simp only [hmx]
    omega
  · intro r h1 h2
    have : r = 0 := by omega
    subst this
    rw [L0, H0]
    simp only [show ¬ (1 ≤ (0 : ℤ)) by omega, ite_false]
    have := hne 0 le_rfl (by omega)
    omega
  · intro h; omega
  · rw [show (1 - 1 : ℤ) = 0 by ring, L0, H1]
    omega
  · rw [show (c + 1 + 0 - 1 : ℤ) = c by ring, show (c + 1 + 0 : ℤ) = c + 1 by ring, Lc, Hc1]
    omega

/-- **Width zero** (`lem:inflate-chart`, second assertion), legality.  With
`A_V(1) = B_V(q - 1) = 0` the inflated inner `I(V)` carries a legal ordinary singleton mark of
period `q = N_V` and width one with the original displacement `v_H`. -/
theorem singleton_mark_isLegal {E : Diagram} (hE : IsConnectedSkew E) (h0 : minContent E = 0)
    (hq : 1 ≤ maxContent E) (hA : diagLo E 0 = diagLo E 1)
    (hB : diagHi E (maxContent E - 1) = diagHi E (maxContent E)) :
    (SlotGeom.mark (inflateCells E) (maxContent E + 1) 1 1
      (diagLo E (maxContent E) - diagLo E 0) (diagHi (inflateCells E))).IsLegal := by
  obtain ⟨hS, hs⟩ := singleton_slotGeom hE h0 hq hA hB
  exact SlotGeom.mark_isLegal hS hs

/-- The singleton mark has the displacement `v_H(V)`, the period `N_V`, and is of case `(a)`. -/
theorem singleton_mark_data {E : Diagram} (hE : IsConnectedSkew E) (h0 : minContent E = 0) :
    (SlotGeom.mark (inflateCells E) (maxContent E + 1) 1 1
        (diagLo E (maxContent E) - diagLo E 0) (diagHi (inflateCells E))).E = inflateCells E ∧
      (SlotGeom.mark (inflateCells E) (maxContent E + 1) 1 1
        (diagLo E (maxContent E) - diagLo E 0) (diagHi (inflateCells E))).v = vH E ∧
      (SlotGeom.mark (inflateCells E) (maxContent E + 1) 1 1
        (diagLo E (maxContent E) - diagLo E 0) (diagHi (inflateCells E))).case = .a := by
  refine ⟨rfl, ?_, rfl⟩
  have hne := (isConnectedSkew_iff_diagonal.mp hE).1
  change SlotGeom.disp _ _ = vH E
  unfold SlotGeom.disp vH ne sw
  rw [h0]
  ext <;> simp <;> ring

/-- **Width zero** (`lem:inflate-chart`, second assertion), the cell identity.  The marked
composition of the singleton inner with any nonempty outer is the cell inflation of the
empty-mark composition `D ∘_∅ V`. -/
theorem singleton_mark_compose {E : Diagram} (hE : IsConnectedSkew E) (h0 : minContent E = 0)
    {D : Diagram} (hD : D.Nonempty) :
    (SlotGeom.mark (inflateCells E) (maxContent E + 1) 1 1
        (diagLo E (maxContent E) - diagLo E 0) (diagHi (inflateCells E))).compose D =
      inflateCells ((emptyMarkH E).compose D) := by
  obtain ⟨h1, h2, h3⟩ := singleton_mark_data hE h0
  rw [← compose_inflateMarked (emptyMarkH E) D hD]
  exact compose_eq_of_ordinary h1 (by rw [h2]; rfl) (by rw [h3]; rfl)
    (by rw [h3]; simp [AttachCase.IsMixed]) hD

/-- **`lem:inflate-chart`, second assertion.**  Let `T = D ∘_∅ V` be the composite of a connected
outer that is not a row with a legal empty mark on `V`, with `V` in the position of least content
zero and period `q ≥ 2`, and suppose `T` is a translate of the cell diagram of `P` with
`I(T)` zero-free.  Then the inner `I(V)` with its singleton end mark `(a)` and displacement `v_H`
is a legal ordinary mark of period `q` and width one, with `I(T)`-composite
`D ∘ I(V) = I(D ∘_∅ V)` as cells. -/
theorem width_zero_chart {ω : MarkedInner} {D : Diagram} (h : ω.IsLegalEmpty)
    (hD : IsConnectedSkew D) (hrow : ¬ IsRowDiagram D) (hq2 : 2 ≤ ω.period)
    (h0 : minContent ω.E = 0) {n : ℕ} {P : Profile n} {v : ℤ × ℤ}
    (hT : ω.compose D = translate v (profileCells P)) (hz : (Profile.inflate 1 P).ZeroFree) :
    (SlotGeom.mark (inflateCells ω.E) (maxContent ω.E + 1) 1 1
        (diagLo ω.E (maxContent ω.E) - diagLo ω.E 0) (diagHi (inflateCells ω.E))).IsLegal ∧
      (SlotGeom.mark (inflateCells ω.E) (maxContent ω.E + 1) 1 1
        (diagLo ω.E (maxContent ω.E) - diagLo ω.E 0) (diagHi (inflateCells ω.E))).period =
          ω.period ∧
      (SlotGeom.mark (inflateCells ω.E) (maxContent ω.E + 1) 1 1
        (diagLo ω.E (maxContent ω.E) - diagLo ω.E 0) (diagHi (inflateCells ω.E))).compose D =
        inflateCells (ω.compose D) := by
  obtain ⟨hA1, hB1⟩ := Width0.inner_constraints_of_zeroFree h hD hrow hq2 hT hz
  have hE := h.1.1.1
  have hsp := h.span_eq
  rw [span_eq_of_isConnectedSkew hE, h0] at hsp
  have hper : maxContent ω.E + 1 = ω.period := by omega
  have hA : diagLo ω.E 0 = diagLo ω.E 1 := by
    unfold SkewGluing.wordA bitA at hA1
    rw [h0] at hA1
    simp only [zero_add, sub_self] at hA1
    omega
  have hB : diagHi ω.E (maxContent ω.E - 1) = diagHi ω.E (maxContent ω.E) := by
    unfold SkewGluing.wordB bitB at hB1
    rw [h0] at hB1
    have e : 0 + (ω.period - 1) = maxContent ω.E := by omega
    simp only [zero_add] at hB1
    rw [show ω.period - 1 = maxContent ω.E by omega] at hB1
    omega
  have hq1 : 1 ≤ maxContent ω.E := by omega
  refine ⟨singleton_mark_isLegal hE h0 hq1 hA hB, ?_, ?_⟩
  · change content (SlotGeom.disp _ _) = _
    rw [SlotGeom.content_disp, hper]
  · have hem : ω = emptyMarkH ω.E := by
      obtain ⟨hW, hv, hc⟩ := h.isEmptyMark
      cases ω
      simp only [emptyMarkH] at *
      simp_all
    rw [singleton_mark_compose hE h0 (hD.2.1)]
    rw [hem]
    rfl

/-! ### Width `q - 1`: the one-middle-cell atom -/

/-- The displacement of the atom `𝒜(W)`: `ne(W) - sw(W) + (0, 2)`. -/
def atomDisp (W : Diagram) : ℤ × ℤ := ne W - sw W + (0, 2)

/-- The inner diagram of the atom: `W`, the single joining middle cell east of `ne(W)`, and the
translate of `W` by the atom displacement. -/
def atomInner (W : Diagram) : Diagram :=
  W ∪ {ne W + (0, 1)} ∪ translate (atomDisp W) W

/-- The atom `𝒜(W)` as a marked inner: lower copy `W`, displacement `atomDisp W`, case `(a)`. -/
def atomMark (W : Diagram) : MarkedInner where
  E := atomInner W
  W := W
  v := atomDisp W
  case := .a

theorem content_atomDisp {W : Diagram} (hW : IsConnectedSkew W) :
    content (atomDisp W) = span W + 1 := by
  have hne := (isConnectedSkew_iff_diagonal.mp hW).1
  have := span_eq_of_isConnectedSkew hW
  unfold atomDisp
  rw [content_add, MarkedInner.content_sub, content_ne hne, content_sw hne]
  simp only [content]
  omega

theorem sw_inflateCells {W : Diagram} (hW : IsConnectedSkew W) :
    sw (inflateCells W) = sw W := by
  have hle : minContent W ≤ maxContent W :=
    minContent_le (maxContent_mem (isConnectedSkew_iff_diagonal.mp hW).1)
  unfold sw
  rw [minContent_inflateCells hW, diagLo_inflateCells hW le_rfl (by omega),
    min_eq_left hle]

theorem ne_inflateCells {W : Diagram} (hW : IsConnectedSkew W) :
    ne (inflateCells W) = ne W + (0, 1) := by
  have hle : minContent W ≤ maxContent W :=
    minContent_le (maxContent_mem (isConnectedSkew_iff_diagonal.mp hW).1)
  unfold ne
  rw [maxContent_inflateCells hW, diagLo_inflateCells hW (by omega) le_rfl,
    min_eq_right (by omega)]
  ext <;> simp <;> ring

/-- The empty-overlap displacement of `I(W)` is the atom displacement. -/
theorem vH_inflateCells {W : Diagram} (hW : IsConnectedSkew W) :
    vH (inflateCells W) = atomDisp W := by
  unfold vH atomDisp
  rw [ne_inflateCells hW, sw_inflateCells hW]
  ext <;> simp <;> ring

theorem mem_inflateCells_singleton {m x : ℤ × ℤ} :
    x ∈ inflateCells ({m} : Diagram) ↔ x = m ∨ x = m + (0, 1) := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := m
  rw [mem_inflateCells]
  simp only [Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, add_zero]
  omega

theorem atom_middle_mem {W : Diagram} (hW : IsConnectedSkew W) :
    ne W + (0, 1) ∈ inflateCells W ∧
      ne W + (0, 1) + (0, 1) ∈ SkewGluing.translate (atomDisp W) (inflateCells W) := by
  have hne := (isConnectedSkew_iff_diagonal.mp hW).1
  constructor
  · rw [mem_inflateCells]
    right
    simpa using ne_mem hne
  · rw [SkewGluing.mem_translate, mem_inflateCells]
    left
    have : ne W + (0, 1) + (0, 1) - atomDisp W = sw W := by
      unfold atomDisp
      ext <;> simp <;> ring
    rw [this]
    exact sw_mem hne

/-- Inflation of the atom's inner: the middle cell and its east neighbor are absorbed by the two
inflated copies. -/
theorem inflateCells_atomInner {W : Diagram} (hW : IsConnectedSkew W) :
    inflateCells (atomInner W) =
      inflateCells W ∪ SkewGluing.translate (atomDisp W) (inflateCells W) := by
  obtain ⟨h1, h2⟩ := atom_middle_mem hW
  unfold atomInner
  rw [inflateCells_union, inflateCells_union, inflateCells_translate]
  ext x
  simp only [Finset.mem_union, mem_inflateCells_singleton]
  constructor
  · rintro ((h | h | h) | h)
    · exact Or.inl h
    · exact Or.inl (h ▸ h1)
    · exact Or.inr (h ▸ h2)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

/-! ### Legality of the atom -/

/-- The first rows of the diagonals of the atom's inner in terms of the first rows `L` of `W`,
greatest content `c`: the diagonals of `W`, the joining cell, then the translate of `W`. -/
def atomLoF (c : ℤ) (L : ℤ → ℤ) (k : ℤ) : ℤ :=
  if k ≤ c then L k else if k = c + 1 then L c else L (k - (c + 2)) + (L c - L 0)

/-- The last rows of the diagonals of the atom's inner, from the first rows `L` and the last
rows `H` of `W`. -/
def atomHiF (c : ℤ) (L H : ℤ → ℤ) (k : ℤ) : ℤ :=
  if k ≤ c then H k else if k = c + 1 then L c else H (k - (c + 2)) + (L c - L 0)

/-- The first rows of the diagonals of the atom's inner. -/
def atomLo (W : Diagram) : ℤ → ℤ := atomLoF (maxContent W) (diagLo W)

/-- The last rows of the diagonals of the atom's inner. -/
def atomHi (W : Diagram) : ℤ → ℤ := atomHiF (maxContent W) (diagLo W) (diagHi W)

theorem atomDisp_eq {W : Diagram} (hW : IsConnectedSkew W) (h0 : minContent W = 0) :
    atomDisp W = (diagLo W (maxContent W) - diagLo W 0,
      diagLo W (maxContent W) - diagLo W 0 + (maxContent W + 2)) := by
  unfold atomDisp ne sw
  rw [h0]
  ext <;> simp <;> ring

theorem diagSet_atomInner {W : Diagram} (hW : IsConnectedSkew W) (h0 : minContent W = 0) :
    DiagSet (atomInner W) 0 (maxContent W + 2 + maxContent W) (atomLo W) (atomHi W) := by
  obtain ⟨hS, hSh⟩ := diagSet_shape_of_connected hW h0
  have hle : 0 ≤ maxContent W := h0 ▸ minContent_le (maxContent_mem
    (isConnectedSkew_iff_diagonal.mp hW).1)
  have hne : ne W = (diagLo W (maxContent W), diagLo W (maxContent W) + maxContent W) := rfl
  intro i k
  unfold atomInner
  simp only [Finset.mem_union, Finset.mem_singleton, SkewGluing.mem_translate]
  have e1 : (i, i + k) - atomDisp W = (i - (diagLo W (maxContent W) - diagLo W 0),
      (i - (diagLo W (maxContent W) - diagLo W 0)) + (k - (maxContent W + 2))) := by
    rw [atomDisp_eq hW h0]; ext <;> simp <;> ring
  rw [e1, hS, hS, hne]
  simp only [Prod.mk_add_mk, add_zero, Prod.mk.injEq]
  unfold atomLo atomHi atomLoF atomHiF
  have l0 := diagLo_le_diagHi (D := W) (k := 0) (by
    rw [(isConnectedSkew_iff_diagonal.mp hW).contents_eq, Finset.mem_Icc]; omega)
  have lc := diagLo_le_diagHi (D := W) (k := maxContent W) (by
    rw [(isConnectedSkew_iff_diagonal.mp hW).contents_eq, Finset.mem_Icc]; omega)
  have e0 := hSh.endLo
  have ec := hSh.endHi
  clear hS hSh
  generalize maxContent W = c at *
  by_cases hk1 : k ≤ c
  · have hk2 : ¬ k = c + 1 := by omega
    simp only [hk1, hk2, ↓reduceIte, true_and, and_true]
    constructor
    · rintro ((h | h) | h) <;> omega
    · intro h; left; left; omega
  · by_cases hk2 : k = c + 1
    · subst hk2
      simp only [hk1, ↓reduceIte, true_and, and_true]
      constructor
      · rintro ((h | h) | h)
        · exact absurd h.2.1 id
        · omega
        · omega
      · intro h; left; right; omega
    · simp only [hk1, hk2, ↓reduceIte, true_and, and_true]
      constructor
      · rintro ((h | h) | h)
        · exact absurd h.2.1 id
        · omega
        · omega
      · intro h; right; omega

theorem atom_shape (c : ℤ) (L H : ℤ → ℤ) (hc : 0 ≤ c) (sh : DiagShape 0 c L H) :
    DiagShape 0 (c + 2 + c) (atomLoF c L) (atomHiF c L H) := by
  have e0 := sh.endLo
  have ec := sh.endHi
  refine ⟨by omega, fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_, ?_, ?_⟩
  · unfold atomLoF atomHiF
    have l0 := sh.ne 0 le_rfl hc
    have lc := sh.ne c hc le_rfl
    by_cases a1 : k ≤ c
    · have := sh.ne k h1 a1
      simp only [a1, ↓reduceIte]; omega
    · by_cases a2 : k = c + 1
      · simp only [a1, a2, ↓reduceIte]; omega
      · have := sh.ne (k - (c + 2)) (by omega) (by omega)
        simp only [a1, a2, ↓reduceIte]; omega
  · unfold atomLoF
    have l0 := sh.ne 0 le_rfl hc
    by_cases a1 : k ≤ c
    · have := sh.stepLo k h1 a1
      have a3 : k - 1 ≤ c := by omega
      simp only [a1, a3, ↓reduceIte]; omega
    · by_cases a2 : k = c + 1
      · subst a2
        simp only [a1, show c + 1 - 1 = c by ring, le_refl, ↓reduceIte]
        omega
      · by_cases a4 : k = c + 2
        · subst a4
          simp only [a1, a2, show c + 2 - 1 = c + 1 by ring, show ¬ (c + 1 ≤ c) by omega,
            ↓reduceIte, show c + 2 - (c + 2) = 0 by ring]
          omega
        · have := sh.stepLo (k - (c + 2)) (by omega) (by omega)
          simp only [a1, a2, show ¬ (k - 1 ≤ c) by omega, show ¬ (k - 1 = c + 1) by omega,
            ↓reduceIte]
          have e : k - 1 - (c + 2) = k - (c + 2) - 1 := by ring
          rw [e]
          omega
  · unfold atomHiF
    by_cases a1 : k ≤ c
    · have := sh.stepHi k h1 a1
      have a3 : k - 1 ≤ c := by omega
      simp only [a1, a3, ↓reduceIte]; omega
    · by_cases a2 : k = c + 1
      · subst a2
        simp only [a1, show c + 1 - 1 = c by ring, le_refl, ↓reduceIte]
        omega
      · by_cases a4 : k = c + 2
        · subst a4
          simp only [a1, a2, show c + 2 - 1 = c + 1 by ring, show ¬ (c + 1 ≤ c) by omega,
            ↓reduceIte, show c + 2 - (c + 2) = 0 by ring]
          omega
        · have := sh.stepHi (k - (c + 2)) (by omega) (by omega)
          simp only [a1, a2, show ¬ (k - 1 ≤ c) by omega, show ¬ (k - 1 = c + 1) by omega,
            ↓reduceIte]
          have e : k - 1 - (c + 2) = k - (c + 2) - 1 := by ring
          rw [e]
          omega
  · unfold atomLoF atomHiF
    simp only [show (0 : ℤ) ≤ c from hc, ↓reduceIte]
    exact e0
  · unfold atomLoF atomHiF
    have a1 : ¬ (c + 2 + c ≤ c) := by omega
    have a2 : ¬ (c + 2 + c = c + 1) := by omega
    simp only [a1, a2, ↓reduceIte, show c + 2 + c - (c + 2) = c by ring]
    omega

theorem atom_slotGeom (c : ℤ) (L H : ℤ → ℤ) (hc : 0 ≤ c) (sh : DiagShape 0 c L H) :
    SlotGeom (c + 2) (c + 1) 0 (c + 1) (L c - L 0) (atomLoF c L) (atomHiF c L H) := by
  have e0 := sh.endLo
  have ec := sh.endHi
  have hsh := atom_shape c L H hc sh
  have key : ∀ r, 0 ≤ r → r ≤ c → atomLoF c L (c + 2 + r) = L r + (L c - L 0) ∧
      atomHiF c L H (c + 2 + r) = H r + (L c - L 0) ∧ atomLoF c L r = L r ∧
      atomHiF c L H r = H r := by
    intro r h1 h2
    unfold atomLoF atomHiF
    simp only [show ¬ (c + 2 + r ≤ c) by omega, show ¬ (c + 2 + r = c + 1) by omega, h2,
      ↓reduceIte, show c + 2 + r - (c + 2) = r by ring, and_self]
  have mid : atomLoF c L (c + 1) = L c ∧ atomHiF c L H (c + 1) = L c := by
    unfold atomLoF atomHiF
    simp only [show ¬ (c + 1 ≤ c) by omega, ↓reduceIte, and_self]
  have top : atomHiF c L H (c + 2) = H 0 + (L c - L 0) := by
    have := (key 0 le_rfl hc).2.1
    simpa using this
  refine ⟨by omega, by omega, by omega, by omega, le_rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simpa [show c + 2 + (c + 1) - 1 = c + 2 + c by ring] using hsh
  · intro r h1 h2; omega
  · intro r h1 h2
    rw [(key r h1 (by omega)).1, (key r h1 (by omega)).2.2.1]
  · intro r h1 h2
    rw [(key r h1 (by omega)).2.1, (key r h1 (by omega)).2.2.2]
  · intro r h1 h2; omega
  · rw [mid.1, mid.2]
  · rw [show c + 2 - 1 = c + 1 by ring, mid.1, mid.2]
  · intro r h1 h2
    have := sh.ne r h1 (by omega)
    rw [(key r h1 (by omega)).2.2.1, (key r h1 (by omega)).2.2.2]
    simp only [show ¬ (c + 1 ≤ r) by omega, ↓reduceIte]
    omega
  · intro h; omega
  · rw [show c + 1 - 1 = c by ring, (key c hc le_rfl).2.2.1, mid.2]
  · have := sh.ne 0 le_rfl hc
    rw [show c + 2 + 0 - 1 = c + 1 by ring, mid.1, show c + 2 + 0 = c + 2 by ring, top]
    omega

theorem lowerCopy_atomInner {W : Diagram} (hW : IsConnectedSkew W) (h0 : minContent W = 0) :
    SlotGeom.lowerCopy (atomInner W) (maxContent W + 1) (maxContent W + 1) (atomHi W) = W := by
  obtain ⟨hS, hSh⟩ := diagSet_shape_of_connected hW h0
  have hG := diagSet_atomInner hW h0
  have hle : 0 ≤ maxContent W := h0 ▸ minContent_le (maxContent_mem
    (isConnectedSkew_iff_diagonal.mp hW).1)
  ext ⟨i, j⟩
  have e : (i, j) = (i, i + (j - i)) := by ext <;> simp
  unfold SlotGeom.lowerCopy
  rw [Finset.mem_filter, e, hG, hS]
  simp only [content, add_sub_cancel_left]
  unfold atomLo atomHi atomLoF atomHiF
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    simp only [show j - i ≤ maxContent W by omega, ↓reduceIte] at h3 h4 h6
    exact ⟨h1, by omega, h3, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, by omega, ?_, ?_⟩, by omega, ?_⟩
    · simp only [h2, ↓reduceIte]; exact h3
    · simp only [h2, ↓reduceIte]; exact h4
    · simp only [h2, ↓reduceIte, show ¬ (maxContent W + 1 ≤ j - i) by omega]; omega

/-- **The atom is a legal mark** (`lem:inflate-chart`, third assertion).  For a connected `W`
with least content zero, the one-middle-cell atom `𝒜(W)` of case `(a)`, period `N_W + 1` and
width `N_W` is a legal marked inner. -/
theorem atomMark_isLegal {W : Diagram} (hW : IsConnectedSkew W) (h0 : minContent W = 0) :
    (atomMark W).IsLegal := by
  obtain ⟨hS, hSh⟩ := diagSet_shape_of_connected hW h0
  have hle : 0 ≤ maxContent W := h0 ▸ minContent_le (maxContent_mem
    (isConnectedSkew_iff_diagonal.mp hW).1)
  have hsg := atom_slotGeom (maxContent W) (diagLo W) (diagHi W) hle hSh
  have hG := diagSet_atomInner hW h0
  have hG' : DiagSet (atomInner W) 0 (maxContent W + 2 + (maxContent W + 1) - 1) (atomLo W)
      (atomHi W) := by
    rw [show maxContent W + 2 + (maxContent W + 1) - 1 = maxContent W + 2 + maxContent W by ring]
    exact hG
  have hm := SlotGeom.mark_isLegal hG' hsg
  have heq : atomMark W = SlotGeom.mark (atomInner W) (maxContent W + 2) (maxContent W + 1)
      (maxContent W + 1) (diagLo W (maxContent W) - diagLo W 0) (atomHi W) := by
    unfold atomMark SlotGeom.mark
    rw [lowerCopy_atomInner hW h0, atomDisp_eq hW h0]
    unfold SlotGeom.disp
    congr 2 <;> ring
  rw [heq]
  exact hm

/-- **Width `q - 1`** (`lem:inflate-chart`, third assertion), the cell identity:
`I(C ∘_W 𝒜(W)) = I(C) ∘_∅ I(W)`, for every nonempty outer `C`. -/
theorem atom_compose_inflate {W : Diagram} (hW : IsConnectedSkew W) {C : Diagram}
    (hC : C.Nonempty) :
    inflateCells ((atomMark W).compose C) =
      (emptyMarkH (inflateCells W)).compose (inflateCells C) := by
  have hIC : (inflateCells C).Nonempty := by
    obtain ⟨d, hd⟩ := hC
    exact ⟨d, mem_inflateCells.mpr (Or.inl hd)⟩
  have hna : ¬ (inflateMarked (atomMark W)).case.IsMixed := by
    simp [inflateMarked, atomMark, AttachCase.IsMixed]
  have hnb : ¬ (emptyMarkH (inflateCells W)).case.IsMixed := by
    simp [emptyMarkH, AttachCase.IsMixed]
  rw [← compose_inflateMarked (atomMark W) C hC]
  have hv : vH (inflateCells W) = atomDisp W := vH_inflateCells hW
  have hoa : ∀ d, (inflateMarked (atomMark W)).origin C d =
      content d • atomDisp W + d.1 • eCell := fun d => rfl
  have hob : ∀ d, (emptyMarkH (inflateCells W)).origin (inflateCells C) d =
      content d • atomDisp W + d.1 • eCell := by
    intro d
    change content d • vH (inflateCells W) + d.1 • eCell = _
    rw [hv]
  have hE : (inflateMarked (atomMark W)).E = inflateCells W ∪
      SkewGluing.translate (atomDisp W) (inflateCells W) := inflateCells_atomInner hW
  ext x
  rw [MarkedInner.compose_of_ordinary hC hna, MarkedInner.compose_of_ordinary hIC hnb]
  simp only [hoa, hob, hE, SkewGluing.mem_translate, Finset.mem_union]
  constructor
  · rintro ⟨d, hd, hx⟩
    rcases hx with hx | hx
    · exact ⟨d, mem_inflateCells.mpr (Or.inl hd), hx⟩
    · have hd1 : ((d + (0, 1)).1, (d + (0, 1)).2 - 1) = d := by ext <;> simp
      refine ⟨d + (0, 1), mem_inflateCells.mpr (Or.inr (hd1 ▸ hd)), ?_⟩
      have e : content (d + (0, 1)) • atomDisp W + (d + (0, 1)).1 • eCell =
          content d • atomDisp W + d.1 • eCell + atomDisp W := by
        have : content (d + (0, 1)) = content d + 1 := by simp [content]; ring
        rw [this, add_smul, one_smul]
        simp only [Prod.fst_add]
        abel
      rw [e, show x - (content d • atomDisp W + d.1 • eCell + atomDisp W) =
        x - (content d • atomDisp W + d.1 • eCell) - atomDisp W by abel]
      exact hx
  · rintro ⟨d', hd', hx⟩
    rcases mem_inflateCells.mp hd' with h | h
    · exact ⟨d', h, Or.inl hx⟩
    · refine ⟨(d'.1, d'.2 - 1), h, Or.inr ?_⟩
      have e : content d' • atomDisp W + d'.1 • eCell =
          content (d'.1, d'.2 - 1) • atomDisp W + (d'.1, d'.2 - 1).1 • eCell + atomDisp W := by
        have : content d' = content (d'.1, d'.2 - 1) + 1 := by simp [content]; ring
        rw [this, add_smul, one_smul]
        abel
      rw [e] at hx
      rw [show x - (content (d'.1, d'.2 - 1) • atomDisp W + (d'.1, d'.2 - 1).1 • eCell) -
        atomDisp W = x - (content (d'.1, d'.2 - 1) • atomDisp W +
          (d'.1, d'.2 - 1).1 • eCell + atomDisp W) by abel]
      exact hx

/-- The right-hand side of the atom identity is a legal empty-mark inner of period `N_W + 1`. -/
theorem atom_empty_mark_isLegal {W : Diagram} (hW : IsConnectedSkew W) :
    (emptyMarkH (inflateCells W)).IsLegal ∧
      (emptyMarkH (inflateCells W)).period = content (atomDisp W) ∧
      (emptyMarkH (inflateCells W)).period = (span W : ℤ) + 1 := by
  have hI := isConnectedSkew_inflateCells hW
  refine ⟨emptyMarkH_isLegal hI, ?_, ?_⟩
  · change content (vH (inflateCells W)) = _
    rw [vH_inflateCells hW]
  · change content (vH (inflateCells W)) = _
    rw [vH_inflateCells hW, content_atomDisp hW]

end SkewClassInflation
