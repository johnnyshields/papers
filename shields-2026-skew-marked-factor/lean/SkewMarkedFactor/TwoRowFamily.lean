/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.Gluing.RowInner
import SkewMarkedFactor.OrdinaryAction

/-!
# The marked two-row family

Actual cells, end marks, and Hypotheses I–IV for `eq:two-row-mark` in
«Explicit formulas and examples» (`sec:examples`) of
`shields-2026-skew-marked-factor.tex`.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan Gluing.MarkedInner

/-- The only restrictions are the displayed standing bounds. -/
structure TwoRowParameters where
  /-- Length of the upper row of the inner diagram. -/
  x : ℕ
  /-- Length of the lower row of the inner diagram. -/
  y : ℕ
  /-- The overlap of the two inner rows minus one. -/
  d : ℕ
  /-- Length of the southwest row mark. -/
  w : ℕ
  x_bound : d + w + 1 ≤ x
  y_bound : d + w + 1 ≤ y

/-- The profile has two rows and overlap minus one `d`. -/
def twoRowProfile (x y d : ℕ) (hx : d < x) (hy : d < y) : Profile 1 where
  r := ![x, y]
  g := ![d]
  r_pos := by intro i; fin_cases i <;> simp <;> omega
  g_lt_castSucc := by intro i; fin_cases i; simpa using hx
  g_lt_succ := by intro i; fin_cases i; simpa using hy

theorem twoRow_zeta (x y d : ℕ) (hx : d < x) (hy : d < y) :
    (twoRowProfile x y d hx hy).zeta = ![(y : ℤ) - d, 0] := by
  funext i
  fin_cases i <;> simp [Profile.zeta, twoRowProfile]

theorem twoRow_xi (x y d : ℕ) (hx : d < x) (hy : d < y) :
    (twoRowProfile x y d hx hy).xi = ![(y : ℤ) - d + x, y] := by
  funext i
  fin_cases i <;> simp [Profile.xi, Profile.zeta, twoRowProfile]

/-- The profile is translated down one column, so the lower row begins at zero. -/
def twoRows (x y d : ℕ) (hx : d < x) (hy : d < y) : Diagram :=
  translate (0, -1) (twoRowProfile x y d hx hy).cells

/-- Interval reading, valid also when the overlap minus one is zero. -/
theorem mem_twoRows {x y d : ℕ} {hx : d < x} {hy : d < y} {a b : ℤ} :
    (a, b) ∈ twoRows x y d hx hy ↔
      (a = 0 ∧ (y : ℤ) - d - 1 ≤ b ∧ b < (x : ℤ) + y - d - 1) ∨
      (a = 1 ∧ 0 ≤ b ∧ b < y) := by
  rw [twoRows, mem_translate]
  simp only [Prod.mk_sub_mk, sub_zero, sub_neg_eq_add]
  rw [Profile.mem_cells]
  constructor
  · rintro ⟨i, hi, hlo, hhi⟩
    fin_cases i <;> simp [twoRow_zeta, twoRow_xi] at hi hlo hhi
    · left; omega
    · right; omega
  · rintro (⟨ha, hlo, hhi⟩ | ⟨ha, hlo, hhi⟩)
    · refine ⟨0, ?_, ?_, ?_⟩ <;> simp [twoRow_zeta, twoRow_xi] <;> omega
    · refine ⟨1, ?_, ?_, ?_⟩ <;> simp [twoRow_zeta, twoRow_xi] <;> omega

theorem twoRows_connected (x y d : ℕ) (hx : d < x) (hy : d < y) :
    IsConnectedSkew (twoRows x y d hx hy) :=
  isConnectedSkew_translate _ (Profile.isConnectedSkew_cells _)

theorem twoRows_minContent (x y d : ℕ) (hx : d < x) (hy : d < y) :
    minContent (twoRows x y d hx hy) = -1 := by
  apply minContent_eq_of
  · exact content_mem_contents (mem_twoRows.mpr (Or.inr ⟨rfl, by omega, by omega⟩) :
      (1, 0) ∈ twoRows x y d hx hy)
  · intro k hk
    obtain ⟨a, ha⟩ := mem_contents_iff.mp hk
    rw [mem_twoRows] at ha
    rcases ha with h | h <;> omega

theorem twoRows_maxContent (x y d : ℕ) (hx : d < x) (hy : d < y) :
    maxContent (twoRows x y d hx hy) = (x : ℤ) + y - d - 2 := by
  apply maxContent_eq_of
  · have hc : (0, (x : ℤ) + y - d - 2) ∈ twoRows x y d hx hy :=
      mem_twoRows.mpr (Or.inl ⟨rfl, by omega, by omega⟩)
    simpa [content] using content_mem_contents hc
  · intro k hk
    obtain ⟨a, ha⟩ := mem_contents_iff.mp hk
    rw [mem_twoRows] at ha
    rcases ha with h | h <;> omega

theorem twoRows_sw (x y d : ℕ) (hx : d < x) (hy : d < y) :
    sw (twoRows x y d hx hy) = (1, 0) := by
  have hz : (1, 0) ∈ twoRows x y d hx hy :=
    mem_twoRows.mpr (Or.inr ⟨rfl, by omega, by omega⟩)
  exact (eq_sw_of_content (twoRows_connected x y d hx hy) hz
    (by simp [content, twoRows_minContent])).symm

theorem twoRows_ne (x y d : ℕ) (hx : d < x) (hy : d < y) :
    ne (twoRows x y d hx hy) = (0, (x : ℤ) + y - d - 2) := by
  have hz : (0, (x : ℤ) + y - d - 2) ∈ twoRows x y d hx hy :=
    mem_twoRows.mpr (Or.inl ⟨rfl, by omega, by omega⟩)
  exact (eq_ne_of_content (twoRows_connected x y d hx hy) hz
    (by simp [content, twoRows_maxContent])).symm

namespace TwoRowParameters
variable (s : TwoRowParameters)

theorem d_lt_x : s.d < s.x := by have := s.x_bound; omega
theorem d_lt_y : s.d < s.y := by have := s.y_bound; omega
theorem d_lt_x_sub_w : s.d < s.x - s.w := by have := s.x_bound; omega
theorem d_lt_y_sub_w : s.d < s.y - s.w := by have := s.y_bound; omega

/-- The positive supplied period, including both zero boundaries. -/
def period : ℕ := s.x + s.y - s.d - s.w

theorem period_cast : (s.period : ℤ) = (s.x : ℤ) + s.y - s.d - s.w := by
  have := s.x_bound
  have := s.y_bound
  simp only [period]
  omega

theorem width_lt_period : s.w < s.period := by
  have := s.x_bound
  have := s.y_bound
  simp only [period]
  omega

end TwoRowParameters

/-- Actual two-row cells from the prescribed profile. -/
def twoRowInner (s : TwoRowParameters) : Diagram :=
  twoRows s.x s.y s.d s.d_lt_x s.d_lt_y

/-- The prescribed lower row, with the displayed ordinary displacement. -/
def twoRowMark (s : TwoRowParameters) : MarkedInner where
  E := twoRowInner s
  W := translate (1, 0) (rowCells 0 s.w)
  v := (-1, (s.period : ℤ) - 1)
  case := .a

section Family
variable (s : TwoRowParameters)

theorem twoRowInner_mem {a b : ℤ} : (a, b) ∈ twoRowInner s ↔
    (a = 0 ∧ (s.y : ℤ) - s.d - 1 ≤ b ∧ b < (s.x : ℤ) + s.y - s.d - 1) ∨
    (a = 1 ∧ 0 ≤ b ∧ b < s.y) := mem_twoRows

theorem twoRowMark_mem {a b : ℤ} : (a, b) ∈ (twoRowMark s).W ↔
    a = 1 ∧ 0 ≤ b ∧ b < s.w := by
  simp only [twoRowMark, mem_translate, Prod.mk_sub_mk, sub_zero, mem_rowCells]
  omega

theorem twoRowMark_upper_mem {a b : ℤ} : (a, b) ∈ (twoRowMark s).upper ↔
    a = 0 ∧ (s.period : ℤ) - 1 ≤ b ∧ b < (s.x : ℤ) + s.y - s.d - 1 := by
  rw [MarkedInner.upper, mem_translate]
  simp only [twoRowMark, Prod.mk_sub_mk, sub_neg_eq_add]
  rw [mem_translate, mem_rowCells]
  simp only [Prod.mk_sub_mk, sub_zero]
  have := s.period_cast
  omega

theorem twoRowMark_middle_mem {a b : ℤ} : (a, b) ∈ (twoRowMark s).middle ↔
    (a = 0 ∧ (s.y : ℤ) - s.d - 1 ≤ b ∧ b < (s.period : ℤ) - 1) ∨
    (a = 1 ∧ (s.w : ℤ) ≤ b ∧ b < s.y) := by
  simp only [MarkedInner.middle, Finset.mem_sdiff, Finset.mem_union]
  change ((a, b) ∈ twoRowInner s ∧
    ¬ ((a, b) ∈ (twoRowMark s).W ∨ (a, b) ∈ (twoRowMark s).upper)) ↔ _
  rw [twoRowInner_mem, twoRowMark_mem, twoRowMark_upper_mem]
  have := s.x_bound
  have := s.y_bound
  have := s.period_cast
  omega

theorem twoRowInner_connected : IsConnectedSkew (twoRowInner s) :=
  twoRows_connected _ _ _ _ _

theorem twoRowMark_middle : (twoRowMark s).middle =
    translate (0, s.w) (twoRows (s.x - s.w) (s.y - s.w) s.d
      s.d_lt_x_sub_w s.d_lt_y_sub_w) := by
  ext ⟨a, b⟩
  rw [twoRowMark_middle_mem, mem_translate]
  simp only [Prod.mk_sub_mk, sub_zero]
  rw [mem_twoRows]
  have := s.x_bound
  have := s.y_bound
  have := s.period_cast
  omega

theorem twoRowMark_removalsConnected : (twoRowMark s).RemovalsConnected := by
  constructor
  · have he : (twoRowMark s).E \ (twoRowMark s).W =
        translate (0, s.w) (twoRows s.x (s.y - s.w) s.d s.d_lt_x s.d_lt_y_sub_w) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_sdiff]
      change ((a, b) ∈ twoRowInner s ∧ ¬ (a, b) ∈ (twoRowMark s).W) ↔ _
      rw [twoRowInner_mem, twoRowMark_mem, mem_translate]
      simp only [Prod.mk_sub_mk, sub_zero]
      rw [mem_twoRows]
      have := s.y_bound
      omega
    rw [he]
    exact isConnectedSkew_translate _ (twoRows_connected _ _ _ _ _)
  · have he : (twoRowMark s).E \ (twoRowMark s).upper =
        twoRows (s.x - s.w) s.y s.d s.d_lt_x_sub_w s.d_lt_y := by
      ext ⟨a, b⟩
      simp only [Finset.mem_sdiff]
      change ((a, b) ∈ twoRowInner s ∧ ¬ (a, b) ∈ (twoRowMark s).upper) ↔ _
      rw [twoRowInner_mem, twoRowMark_upper_mem, mem_twoRows]
      have := s.x_bound
      have := s.y_bound
      have := s.period_cast
      omega
    rw [he]
    exact twoRows_connected _ _ _ _ _

theorem twoRowMark_middle_min : minContent (twoRowMark s).middle = (s.w : ℤ) - 1 := by
  rw [twoRowMark_middle, minContent_translate
    (twoRows_connected _ _ _ _ _).2.1, twoRows_minContent]
  simp only [content]
  omega

theorem twoRowMark_middle_max : maxContent (twoRowMark s).middle = (s.period : ℤ) - 2 := by
  rw [twoRowMark_middle, maxContent_translate
    (twoRows_connected _ _ _ _ _).2.1, twoRows_maxContent]
  have := s.x_bound
  have := s.y_bound
  have := s.period_cast
  simp only [content]
  omega

theorem twoRowMark_empty (hw : s.w = 0) : twoRowMark s = emptyMarkH (twoRowInner s) := by
  have hv : vH (twoRowInner s) = (-1, (s.period : ℤ) - 1) := by
    unfold vH twoRowInner
    rw [twoRows_ne, twoRows_sw]
    have := s.period_cast
    apply Prod.ext
    · simp
    · simp only [Prod.snd_sub, Prod.snd_add]
      omega
  have hW : (twoRowMark s).W = ∅ := by
    ext ⟨a, b⟩
    rw [twoRowMark_mem]
    simp [hw]
  change MarkedInner.mk (twoRowInner s) (translate (1, 0) (rowCells 0 s.w))
    (-1, (s.period : ℤ) - 1) .a =
      MarkedInner.mk (twoRowInner s) ∅ (vH (twoRowInner s)) .a
  congr 1
  exact hv.symm

theorem twoRowMark_isWellFormed : (twoRowMark s).IsWellFormed := by
  refine ⟨twoRowInner_connected s, ?_⟩
  by_cases hw : s.w = 0
  · rw [twoRowMark_empty s hw]
    exact (emptyMarkH_isLegal (twoRowInner_connected s)).1.2
  · right
    have hwpos : 0 < s.w := Nat.pos_of_ne_zero hw
    have hx := s.x_bound
    have hy := s.y_bound
    have hp := s.period_cast
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨(1, 0), (twoRowMark_mem s).mpr ⟨rfl, by omega, by omega⟩⟩
    · exact isConnectedSkew_translate _ (isConnectedSkew_rowCells (by omega))
    · intro ⟨a, b⟩ hb
      rw [twoRowMark_mem] at hb
      exact (twoRowInner_mem s).mpr (Or.inr ⟨hb.1, hb.2.1, by omega⟩)
    · intro ⟨a, b⟩ hb
      rw [twoRowMark_upper_mem] at hb
      exact (twoRowInner_mem s).mpr (Or.inl ⟨hb.1, by omega, hb.2.2⟩)
    · change sw (twoRows _ _ _ _ _) ∈ _
      rw [twoRows_sw, twoRowMark_mem]
      exact ⟨rfl, by omega, by omega⟩
    · change ne (twoRows _ _ _ _ _) ∈ _
      rw [twoRows_ne, twoRowMark_upper_mem]
      exact ⟨rfl, by omega, by omega⟩
    · refine ⟨fun _ => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · refine ⟨(1, s.w), ?_, ?_, ?_⟩
        · exact (twoRowMark_middle_mem s).mpr (Or.inr ⟨rfl, by omega, by omega⟩)
        · rw [twoRowMark_middle_min]; rfl
        · rw [twoRowMark_mem]; exact ⟨rfl, by omega, by omega⟩
      · refine ⟨(0, (s.period : ℤ) - 2), ?_, ?_, ?_⟩
        · exact (twoRowMark_middle_mem s).mpr (Or.inl ⟨rfl, by omega, by omega⟩)
        · rw [twoRowMark_middle_max]; simp [content]
        · rw [twoRowMark_upper_mem]; exact ⟨rfl, by omega, by omega⟩
      all_goals intro h; cases h

theorem twoRowMark_isMaximal : (twoRowMark s).IsMaximal := by
  intro W' hW' hlt _ hc z hz
  exfalso
  have hsub : W' ⊆ twoRowInner s := Finset.mem_powerset.mp hW'
  have hsame : W' ⊆ (twoRowMark s).W := by
    intro ⟨a, b⟩ hb
    have he := (twoRowInner_mem s).mp (hsub hb)
    have hk := content_mem_contents hb
    rw [hc] at hk
    obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
    rw [twoRowMark_mem] at hi
    have hy := s.y_bound
    simp only [content] at *
    rw [twoRowMark_mem]
    omega
  exact (not_subset_of_ssubset hlt) hsame

theorem twoRowMark_width : (twoRowMark s).width = s.w := by
  simp [MarkedInner.width, twoRowMark, span_translate, span_rowCells]

theorem twoRowMark_period : (twoRowMark s).period = s.period := by
  simp [MarkedInner.period, twoRowMark, content]

theorem twoRowMark_isNarrow : (twoRowMark s).IsNarrow := by
  rw [MarkedInner.IsNarrow, twoRowMark_width, twoRowMark_period]
  exact ⟨by positivity, by exact_mod_cast s.width_lt_period⟩

/-- No periodic copy contains the predecessor or successor of a lower marked cell. -/
theorem twoRowMark_mark_neighbors {a b : ℤ} (h : (a, b) ∈ (twoRowMark s).W) :
    (a - 1, b - 1) ∉ (twoRowMark s).periodicUnion ∧
      (a + 1, b + 1) ∉ (twoRowMark s).periodicUnion := by
  rw [twoRowMark_mem] at h
  obtain ⟨rfl, hb0, hbw⟩ := h
  have hx := s.x_bound
  have hy := s.y_bound
  have hp := s.period_cast
  constructor <;> rintro ⟨k, hk⟩ <;>
    simp only [twoRowMark, Prod.smul_mk, smul_eq_mul, mul_neg_one,
      Prod.mk_sub_mk] at hk <;>
    rw [twoRowInner_mem] at hk
  · rcases hk with hk | hk
    · have hk0 : k = 0 := by omega
      subst k
      simp only [zero_mul] at hk
      omega
    · have hk1 : k = 1 := by omega
      subst k
      simp only [one_mul] at hk
      omega
  · rcases hk with hk | hk
    · have hk0 : k = -2 := by omega
      subst k
      norm_num at hk
      omega
    · have hk1 : k = -1 := by omega
      subst k
      simp only [neg_one_mul] at hk
      omega

theorem twoRowMark_hatMark_empty (m : ℤ) :
    (twoRowMark s).hatMark (translate (m • (twoRowMark s).v) (twoRowMark s).W) = ∅ := by
  apply le_antisymm ?_ (Set.empty_subset _)
  intro z hz
  have shift : ∀ t ∈ (twoRowMark s).periodicUnion,
      t - m • (twoRowMark s).v ∈ (twoRowMark s).periodicUnion := by
    intro t ht
    obtain ⟨k, hk⟩ := ht
    refine ⟨k - m, ?_⟩
    convert hk using 1
    simp [sub_smul]
  have hn : ∀ t ∈ (twoRowMark s).W,
      t - eCell ∉ (twoRowMark s).periodicUnion ∧
        t + eCell ∉ (twoRowMark s).periodicUnion := by
    intro ⟨a, b⟩ ht
    simpa [eCell] using twoRowMark_mark_neighbors s ht
  rcases hz with ⟨hz, hw⟩ | ⟨hw, hz⟩
  · have hw' := mem_translate.mp hw
    have hz' := shift z hz
    apply (hn _ hw').1
    convert hz' using 1
    abel
  · have hw' := mem_translate.mp hw
    have hz' := shift (z + eCell) hz
    apply (hn _ hw').2
    convert hz' using 1
    abel

theorem twoRowMark_noHatAdjacency : (twoRowMark s).NoHatAdjacency := by
  intro k m z hz t ht
  rw [twoRowMark_hatMark_empty] at ht
  exact False.elim ht

/-- A producer for old geometric legality, with no certificate assumptions. -/
theorem twoRowMark_legal : (twoRowMark s).IsLegal :=
  ⟨twoRowMark_isWellFormed s, twoRowMark_isMaximal s, twoRowMark_isNarrow s,
    twoRowMark_removalsConnected s, twoRowMark_noHatAdjacency s⟩

theorem twoRowMark_hatMiddle : hatMiddleFin (twoRowMark s) =
    translate (0, (s.y : ℤ) - s.d - 1) (rowCells 0 s.d) := by
  ext ⟨a, b⟩
  simp only [hatMiddleFin, Finset.mem_filter]
  rw [twoRowMark_middle_mem]
  have he : (a, b) + eCell = (a + 1, b + 1) := rfl
  rw [he, twoRowMark_middle_mem, mem_translate]
  simp only [Prod.mk_sub_mk, sub_zero, mem_rowCells]
  have := s.x_bound
  have := s.y_bound
  have := s.period_cast
  omega

theorem twoRowMark_hatMarkFin : hatMarkFin (twoRowMark s) = ∅ := by
  apply le_antisymm ?_ (Finset.empty_subset _)
  intro z hz
  have hw : ∀ t ∈ periodicWindow (twoRowMark s), t ∈ (twoRowMark s).periodicUnion := by
    intro t ht
    obtain ⟨k, hk, ht⟩ := Finset.mem_biUnion.mp ht
    exact ⟨k, mem_translate.mp ht⟩
  have hh : z ∈ (twoRowMark s).hatMark (twoRowMark s).W := by
    rw [hatMarkFin, Finset.mem_union] at hz
    rcases hz with hz | hz
    · have h := Finset.mem_filter.mp hz
      exact Or.inl ⟨hw z h.2.2, h.2.1⟩
    · have h := Finset.mem_filter.mp hz
      exact Or.inr ⟨h.1, hw (z + eCell) h.2⟩
  have he := twoRowMark_hatMark_empty s 0
  simp only [zero_smul, Gluing.translate_zero] at he
  rw [he] at hh
  simp at hh

theorem twoRowInner_card : (twoRowInner s).card = s.x + s.y := by
  unfold twoRowInner twoRows
  unfold Gluing.translate
  rw [Finset.card_image_of_injective _ (add_left_injective _), Profile.card_cells]
  simp [twoRowProfile, Fin.sum_univ_two]

theorem twoRowMark_ordinary : (twoRowMark s).IsOrdinary := by
  simp [MarkedInner.IsOrdinary, twoRowMark, AttachCase.IsMixed]

theorem twoRowChart_proper {D : Diagram} (hD : IsConnectedSkew D) (ha : 2 ≤ D.card) :
    (⟨D, twoRowMark s⟩ : Chart).IsProperOrdinary := by
  refine ⟨⟨hD, ha, ?_, (twoRowMark_legal s).readoutLegal⟩, twoRowMark_ordinary s⟩
  change 2 ≤ (twoRowInner s).card
  rw [twoRowInner_card]
  have := s.x_bound
  have := s.y_bound
  omega

end Family
end SkewMarkedFactor
