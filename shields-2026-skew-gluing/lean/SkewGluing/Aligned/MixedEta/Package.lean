import SkewGluing.Aligned.Statement
import SkewGluing.Aligned.Lattice
import SkewGluing.Local
import SkewGluing.Aligned.MixedEta.Base

/-!
# The lower mark of an aligned pair: legality from diagonal data

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-walk-signs`), the legality checks for the lower mark
`Z = V ∩ (V - z)` of case (d).

`DPackage V a b θ` collects the diagonal data of `V` that the paper reads off the upper mark:
the periodic southeast boundary (`θ`), the walk signs of `eq:gluing-walk-signs` for the
northwest offsets, the singleton diagonals `b` and `a - 1`, and the attachment bits.  From it
`DPackage.legal` proves that `(V, V ∩ (V - z), z)` is a legal mark of case (d): conditions I–IV,
connected complements, and the attachments.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

namespace MixedEta

/-- **The diagonal data of a case-(d) lower mark.**  `V` is connected skew with the contents
`[m, m + a + b - 1]` (`m` its least content), `1 ≤ b < a`.  Its southeast boundary is
`a`-periodic with row shift `θ` on the first `b` diagonals (`K1`); the northwest offsets
`g_j = ℓ_{j+a} - θ - ℓ_j` are `-1, 0` or `1` (`K2`), the positive ones forming a final segment
and the negative ones an initial segment (`K3`); the diagonals `m + b` and `m + a - 1` are
singletons (`K4`); and when there is no lower (upper) tail the two singleton diagonals
`m + b - 1`, `m + b` (respectively `m + a - 1`, `m + a`) are joined vertically (horizontally)
(`K5`). -/
structure DPackage (V : Diagram) (a b θ : ℤ) : Prop where
  conn : IsConnectedSkew V
  hmax : maxContent V = minContent V + a + b - 1
  hb : 1 ≤ b
  hba : b < a
  k1 : ∀ j, minContent V ≤ j → j ≤ minContent V + b - 1 →
    diagHi V (j + a) = diagHi V j + θ
  k2 : ∀ j, minContent V ≤ j → j ≤ minContent V + b - 1 →
    -1 ≤ diagLo V (j + a) - θ - diagLo V j ∧ diagLo V (j + a) - θ - diagLo V j ≤ 1
  k3lo : ∀ j j', minContent V ≤ j → j < j' → j' ≤ minContent V + b - 1 →
    0 < diagLo V (j + a) - θ - diagLo V j → 0 < diagLo V (j' + a) - θ - diagLo V j'
  k3up : ∀ j j', minContent V ≤ j → j < j' → j' ≤ minContent V + b - 1 →
    diagLo V (j' + a) - θ - diagLo V j' < 0 → diagLo V (j + a) - θ - diagLo V j < 0
  k4lo : diagLo V (minContent V + b) = diagHi V (minContent V + b)
  k4up : diagLo V (minContent V + a - 1) = diagHi V (minContent V + a - 1)
  k5lo : (∀ j, minContent V ≤ j → j ≤ minContent V + b - 1 →
      diagLo V (j + a) - θ - diagLo V j ≤ 0) →
    diagHi V (minContent V + b - 1) - diagHi V (minContent V + b) = 1
  k5up : (∀ j, minContent V ≤ j → j ≤ minContent V + b - 1 →
      0 ≤ diagLo V (j + a) - θ - diagLo V j) →
    diagHi V (minContent V + a - 1) - diagHi V (minContent V + a) = 0

namespace DPackage

variable {V : Diagram} {a b θ : ℤ}

theorem shape (h : DPackage V a b θ) : HasDiagonalShape V :=
  isConnectedSkew_iff_diagonal.mp h.conn

theorem mem_V (h : DPackage V a b θ) {i j : ℤ} :
    (i, i + j) ∈ V ↔ minContent V ≤ j ∧ j ≤ minContent V + a + b - 1 ∧ diagLo V j ≤ i ∧
      i ≤ diagHi V j := by
  have := h.shape.mem_iff (k := j) (i := i)
  rw [this, h.shape.mem_contents_iff, h.hmax]
  have : minContent V + a + b - 1 = minContent V + a + b - 1 := rfl
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, by omega, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, by omega⟩, h3, h4⟩

/-- The nonempty diagonals of `V` have `ℓ_j ≤ h_j`. -/
theorem lo_le_hi (h : DPackage V a b θ) {j : ℤ} (h1 : minContent V ≤ j)
    (h2 : j ≤ minContent V + a + b - 1) : diagLo V j ≤ diagHi V j := by
  apply diagLo_le_diagHi
  rw [h.shape.mem_contents_iff, h.hmax]
  exact ⟨h1, by omega⟩

theorem bits (h : DPackage V a b θ) {j : ℤ} (h1 : minContent V + 1 ≤ j)
    (h2 : j ≤ minContent V + a + b - 1) :
    (diagLo V (j - 1) - diagLo V j = 0 ∨ diagLo V (j - 1) - diagLo V j = 1) ∧
    (diagHi V (j - 1) - diagHi V j = 0 ∨ diagHi V (j - 1) - diagHi V j = 1) := by
  have := D_bits h.conn (J := j) h1 (by rw [h.hmax]; omega)
  exact this

theorem first_single (h : DPackage V a b θ) : diagLo V (minContent V) = diagHi V (minContent V) :=
  (D_ends h.conn).1

theorem last_single (h : DPackage V a b θ) :
    diagLo V (minContent V + a + b - 1) = diagHi V (minContent V + a + b - 1) := by
  have := (D_ends h.conn).2
  rw [h.hmax] at this
  exact this


/-- The row displacement `θ` and the content shift `a` of the lower mark. -/
def zOf (a θ : ℤ) : ℤ × ℤ := (θ, θ + a)

theorem mem_Z (h : DPackage V a b θ) {i j : ℤ} :
    (i, i + j) ∈ (lowerMark V (zOf a θ) .d).W ↔ minContent V ≤ j ∧ j ≤ minContent V + b - 1 ∧
      max (diagLo V j) (diagLo V (j + a) - θ) ≤ i ∧ i ≤ diagHi V j := by
  have hba := h.hba
  have hb := h.hb
  change (i, i + j) ∈ V.filter (fun y => y + zOf a θ ∈ V) ↔ _
  rw [Finset.mem_filter]
  have e : ((i, i + j) : ℤ × ℤ) + zOf a θ = (i + θ, i + θ + (j + a)) := by
    unfold zOf; ext <;> simp; ring
  rw [e, h.mem_V, h.mem_V]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩
    have hk := h.k1 j h1 (by omega)
    refine ⟨h1, by omega, ?_, h4⟩
    rw [max_le_iff]; exact ⟨h3, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    rw [max_le_iff] at h3
    have hk := h.k1 j h1 h2
    refine ⟨⟨h1, by omega, h3.1, h4⟩, by omega, by omega, by omega, by omega⟩

theorem mem_upper (h : DPackage V a b θ) {i j : ℤ} :
    (i, i + j) ∈ (lowerMark V (zOf a θ) .d).upper ↔
      minContent V + a ≤ j ∧ j ≤ minContent V + a + b - 1 ∧
        max (diagLo V (j - a) + θ) (diagLo V j) ≤ i ∧ i ≤ diagHi V j := by
  have hba := h.hba
  have hb := h.hb
  unfold upper
  rw [mem_translate]
  have e : ((i, i + j) : ℤ × ℤ) - (lowerMark V (zOf a θ) .d).v = (i - θ, i - θ + (j - a)) := by
    change ((i, i + j) : ℤ × ℤ) - zOf a θ = _
    unfold zOf; ext <;> simp; ring
  rw [e, mem_Z h]
  have hj : j - a + a = j := by ring
  rw [hj]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hk := h.k1 (j - a) h1 h2
    rw [hj] at hk
    refine ⟨by omega, by omega, ?_, by omega⟩
    rw [max_le_iff] at h3 ⊢; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hk := h.k1 (j - a) (by omega) (by omega)
    rw [hj] at hk
    rw [max_le_iff] at h3
    refine ⟨by omega, by omega, ?_, by omega⟩
    rw [max_le_iff]; exact ⟨by omega, by omega⟩


theorem Z_connected (h : DPackage V a b θ) : IsConnectedSkew (lowerMark V (zOf a θ) .d).W := by
  have hba := h.hba
  have hb := h.hb
  refine isConnectedSkew_of_rows _ (minContent V) (minContent V + b - 1)
    (fun j => max (diagLo V j) (diagLo V (j + a) - θ)) (fun j => diagHi V j)
    (by omega) (fun i j => mem_Z h) ?_ ?_ ?_ ?_ ?_
  · intro j h1 h2
    have := h.lo_le_hi h1 (by omega : j ≤ minContent V + a + b - 1)
    have := h.lo_le_hi (j := j + a) (by omega) (by omega)
    have := h.k1 j h1 h2
    simp only [max_le_iff]; omega
  · intro j h1 h2
    have b1 := h.bits (j := j) (by omega) (by omega)
    have b2 := h.bits (j := j + a) (by omega) (by omega)
    have e : j + a - 1 = j - 1 + a := by ring
    rw [e] at b2
    omega
  · intro j h1 h2
    have b1 := h.bits (j := j) (by omega) (by omega)
    omega
  · have := h.first_single
    have := h.lo_le_hi (j := minContent V) (le_refl _) (by omega)
    have := h.lo_le_hi (j := minContent V + a) (by omega) (by omega)
    have := h.k1 (minContent V) (le_refl _) (by omega)
    omega
  · have := h.last_single
    have := h.k1 (minContent V + b - 1) (by omega) (le_refl _)
    have e : minContent V + b - 1 + a = minContent V + a + b - 1 := by ring
    rw [e] at this ⊢
    have := h.lo_le_hi (j := minContent V + b - 1) (by omega) (by omega)
    omega


theorem LZ_le_hi (h : DPackage V a b θ) {j : ℤ} (h1 : minContent V ≤ j)
    (h2 : j ≤ minContent V + b - 1) : max (diagLo V j) (diagLo V (j + a) - θ) ≤ diagHi V j := by
  have hba := h.hba
  have := h.lo_le_hi h1 (by omega : j ≤ minContent V + a + b - 1)
  have := h.lo_le_hi (j := j + a) (by omega) (by omega)
  have := h.k1 j h1 h2
  simp only [max_le_iff]; omega

theorem contents_Z (h : DPackage V a b θ) :
    contents (lowerMark V (zOf a θ) .d).W = Finset.Icc (minContent V) (minContent V + b - 1) := by
  ext k
  rw [Finset.mem_Icc, mem_contents_iff]
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_Z h] at hi
    exact ⟨hi.1, hi.2.1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨diagHi V k, (mem_Z h).mpr ⟨h1, h2, h.LZ_le_hi h1 h2, le_refl _⟩⟩

theorem width_eq (h : DPackage V a b θ) : ((lowerMark V (zOf a θ) .d).width : ℤ) = b := by
  have hb := h.hb
  unfold width span
  rw [contents_Z h, Int.card_Icc]
  omega

theorem period_eq (_h : DPackage V a b θ) : (lowerMark V (zOf a θ) .d).period = a := by
  change content (zOf a θ) = a
  unfold zOf content; simp

theorem narrow (h : DPackage V a b θ) : (lowerMark V (zOf a θ) .d).IsNarrow := by
  unfold IsNarrow
  rw [width_eq h, period_eq h]
  exact ⟨by have := h.hb; omega, h.hba⟩

theorem W_subset (_h : DPackage V a b θ) : (lowerMark V (zOf a θ) .d).W ⊆ V := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem upper_subset (_h : DPackage V a b θ) : (lowerMark V (zOf a θ) .d).upper ⊆ V := by
  intro x hx
  unfold upper at hx
  rw [mem_translate] at hx
  have := (Finset.mem_filter.mp hx).2
  have e : x - (lowerMark V (zOf a θ) .d).v + zOf a θ = x := by
    change x - zOf a θ + zOf a θ = x
    abel
  rw [e] at this
  exact this

theorem sw_mem_Z (h : DPackage V a b θ) : sw V ∈ (lowerMark V (zOf a θ) .d).W := by
  have hb := h.hb
  have hba := h.hba
  have hs := h.first_single
  have := h.LZ_le_hi (j := minContent V) (le_refl _) (by omega)
  unfold sw
  have e : (diagLo V (minContent V), diagLo V (minContent V) + minContent V) =
      (diagLo V (minContent V), diagLo V (minContent V) + minContent V) := rfl
  rw [mem_Z h]
  have := h.lo_le_hi (j := minContent V) (le_refl _) (by omega)
  have h3 := h.lo_le_hi (j := minContent V + a) (by omega) (by omega)
  have h4 := h.k1 (minContent V) (le_refl _) (by omega)
  refine ⟨le_refl _, by omega, ?_, by omega⟩
  rw [max_le_iff]; omega

theorem ne_mem_upper (h : DPackage V a b θ) : ne V ∈ (lowerMark V (zOf a θ) .d).upper := by
  have hb := h.hb
  have hba := h.hba
  have hl := h.last_single
  have hM := h.hmax
  unfold ne
  rw [hM, mem_upper h]
  have h4 := h.k1 (minContent V + b - 1) (by omega) (le_refl _)
  have e : minContent V + b - 1 + a = minContent V + a + b - 1 := by ring
  rw [e] at h4
  have h5 := h.lo_le_hi (j := minContent V + b - 1) (by omega) (by omega)
  have h6 := h.lo_le_hi (j := minContent V + a + b - 1) (by omega) (by omega)
  have e2 : minContent V + a + b - 1 - a = minContent V + b - 1 := by ring
  rw [e2]
  refine ⟨by omega, le_refl _, ?_, by omega⟩
  rw [max_le_iff]; omega


theorem top_mem_Z (h : DPackage V a b θ) :
    (diagHi V (minContent V + b - 1), diagHi V (minContent V + b - 1) + (minContent V + b - 1)) ∈
      (lowerMark V (zOf a θ) .d).W :=
  (mem_Z h).mpr ⟨by have := h.hb; omega, le_refl _,
    h.LZ_le_hi (by have := h.hb; omega) (le_refl _), le_refl _⟩

theorem maximal (h : DPackage V a b θ) : (lowerMark V (zOf a θ) .d).IsMaximal := by
  have hb := h.hb
  have hba := h.hba
  intro W' hW'V hZW' _ hcont x hx hsub
  have hW'V' : W' ⊆ V := Finset.mem_powerset.mp hW'V
  have hsub' : SkewGluing.translate (ne V - x) W' ⊆ V := hsub
  set y0 : ℤ × ℤ := (diagHi V (minContent V + b - 1),
    diagHi V (minContent V + b - 1) + (minContent V + b - 1)) with hy0def
  have hy0 : y0 ∈ (lowerMark V (zOf a θ) .d).W := top_mem_Z h
  have hy0W' : y0 ∈ W' := hZW'.1 hy0
  have hxV : x ∈ V := hW'V' hx
  have hxc : content x ∈ contents W' := content_mem_contents hx
  rw [hcont, contents_Z h, Finset.mem_Icc] at hxc
  set t := ne V - x with ht
  have hy0t : y0 + t ∈ V := by
    apply hsub'
    rw [mem_translate]
    simpa using hy0W'
  have hMc : content (ne V) = maxContent V := content_ne h.conn.2.1
  have htc : content t = maxContent V - content x := by
    rw [ht]; unfold content at hMc ⊢
    simp only [Prod.snd_sub, Prod.fst_sub]; omega
  have hle : content y0 + content t ≤ maxContent V := by
    have := le_maxContent (content_mem_contents hy0t)
    rwa [content_add] at this
  have hc0 : content y0 = minContent V + b - 1 := by
    rw [hy0def]; unfold content; simp
  have hcx : content x = minContent V + b - 1 := by omega
  have hta : content t = a := by rw [htc, h.hmax]; omega
  have hrow := (h.mem_V (i := y0.1 + t.1) (j := maxContent V)).mp (by
    have e : y0 + t = (y0.1 + t.1, y0.1 + t.1 + maxContent V) := by
      ext
      · simp
      · simp only [Prod.snd_add]
        unfold content at hta hc0
        rw [h.hmax] at *
        rw [hy0def]
        simp only
        omega
    rw [← e]; exact hy0t)
  have hl := h.last_single
  have hk := h.k1 (minContent V + b - 1) (by omega) (le_refl _)
  have e : minContent V + b - 1 + a = minContent V + a + b - 1 := by ring
  rw [e, ← h.hmax] at hk
  rw [← h.hmax] at hl
  have hy01 : y0.1 = diagHi V (minContent V + b - 1) := by rw [hy0def]
  have ht1 : t.1 = θ := by omega
  have htz : t = zOf a θ := by
    unfold zOf
    ext
    · exact ht1
    · unfold content at hta; omega
  apply hZW'.2
  intro w hw
  have hwV : w ∈ V := hW'V' hw
  have hwt : w + t ∈ V := by
    apply hsub'
    rw [mem_translate]; simpa using hw
  rw [htz] at hwt
  exact Finset.mem_filter.mpr ⟨hwV, hwt⟩


/-- The northwest offset `g_j = ℓ_{j+a} - θ - ℓ_j`. -/
def gOf (V : Diagram) (a θ j : ℤ) : ℤ := diagLo V (j + a) - θ - diagLo V j

theorem exists_lower_threshold (h : DPackage V a b θ) :
    ∃ j0, minContent V ≤ j0 ∧ j0 ≤ minContent V + b ∧
      ∀ j, minContent V ≤ j → j ≤ minContent V + b - 1 → (0 < gOf V a θ j ↔ j0 ≤ j) := by
  classical
  by_cases hex : ∃ j, minContent V ≤ j ∧ j ≤ minContent V + b - 1 ∧ 0 < gOf V a θ j
  · obtain ⟨j0, ⟨h1, h2, h3⟩, hmin⟩ := Int.exists_least_of_bdd
      (P := fun j => minContent V ≤ j ∧ j ≤ minContent V + b - 1 ∧ 0 < gOf V a θ j)
      ⟨minContent V, fun j hj => hj.1⟩ hex
    refine ⟨j0, h1, by omega, fun j hj1 hj2 => ⟨fun hg => ?_, fun hj => ?_⟩⟩
    · exact hmin j ⟨hj1, hj2, hg⟩
    · rcases eq_or_lt_of_le hj with e | hlt
      · rw [← e]; exact h3
      · exact h.k3lo j0 j h1 hlt hj2 h3
  · refine ⟨minContent V + b, by have := h.hb; omega, le_refl _,
      fun j hj1 hj2 => ⟨fun hg => ?_, fun hj => ?_⟩⟩
    · exact absurd ⟨j, hj1, hj2, hg⟩ hex
    · omega

theorem exists_upper_threshold (h : DPackage V a b θ) :
    ∃ j1, minContent V - 1 ≤ j1 ∧ j1 ≤ minContent V + b - 1 ∧
      ∀ j, minContent V ≤ j → j ≤ minContent V + b - 1 → (gOf V a θ j < 0 ↔ j ≤ j1) := by
  classical
  by_cases hex : ∃ j, minContent V ≤ j ∧ j ≤ minContent V + b - 1 ∧ gOf V a θ j < 0
  · obtain ⟨j1, ⟨h1, h2, h3⟩, hmax⟩ := Int.exists_greatest_of_bdd
      (P := fun j => minContent V ≤ j ∧ j ≤ minContent V + b - 1 ∧ gOf V a θ j < 0)
      ⟨minContent V + b - 1, fun j hj => hj.2.1⟩ hex
    refine ⟨j1, by omega, h2, fun j hj1 hj2 => ⟨fun hg => ?_, fun hj => ?_⟩⟩
    · exact hmax j ⟨hj1, hj2, hg⟩
    · rcases eq_or_lt_of_le hj with e | hlt
      · rw [e]; exact h3
      · exact h.k3up j j1 hj1 hlt h2 h3
  · refine ⟨minContent V - 1, le_refl _, by have := h.hb; omega,
      fun j hj1 hj2 => ⟨fun hg => ?_, fun hj => ?_⟩⟩
    · exact absurd ⟨j, hj1, hj2, hg⟩ hex
    · omega


theorem g_last_nonneg (h : DPackage V a b θ) : 0 ≤ gOf V a θ (minContent V + b - 1) := by
  have hb := h.hb
  have hl := h.last_single
  have hk := h.k1 (minContent V + b - 1) (by omega) (le_refl _)
  have e : minContent V + b - 1 + a = minContent V + a + b - 1 := by ring
  rw [e] at hk
  have := h.lo_le_hi (j := minContent V + b - 1) (by omega) (by have := h.hba; omega)
  unfold gOf
  rw [e]
  omega

theorem g_first_nonpos (h : DPackage V a b θ) : gOf V a θ (minContent V) ≤ 0 := by
  have hb := h.hb
  have hba := h.hba
  have hs := h.first_single
  have hk := h.k1 (minContent V) (le_refl _) (by omega)
  have := h.lo_le_hi (j := minContent V + a) (by omega) (by omega)
  unfold gOf
  omega

theorem ite_pos' {c : Prop} [Decidable c] {α : Type*} (h : c) (x y : α) :
    (if c then x else y) = x := by simp [h]

theorem ite_neg' {c : Prop} [Decidable c] {α : Type*} (h : ¬ c) (x y : α) :
    (if c then x else y) = y := by simp [h]

theorem lower_complement_connected (h : DPackage V a b θ) :
    IsConnectedSkew ((lowerMark V (zOf a θ) .d).E \ (lowerMark V (zOf a θ) .d).W) := by
  have hb := h.hb
  have hba := h.hba
  obtain ⟨j0, hj0a, hj0b, hthr⟩ := exists_lower_threshold h
  have hk4 := h.k4lo
  have hlast := h.last_single
  have hg1 := g_last_nonneg h
  have hhM := h.hmax
  have hLZ : ∀ j, minContent V ≤ j → j ≤ minContent V + b - 1 → j0 ≤ j →
      max (diagLo V j) (diagLo V (j + a) - θ) = diagLo V j + gOf V a θ j ∧
      0 < gOf V a θ j ∧ gOf V a θ j = 1 := by
    intro j h1 h2 h3
    have hg := (hthr j h1 h2).mpr h3
    have hk := h.k2 j h1 h2
    unfold gOf at *
    refine ⟨?_, hg, by omega⟩
    rw [max_def]; split_ifs <;> omega
  refine isConnectedSkew_of_rows _ j0 (minContent V + a + b - 1)
    (fun j => diagLo V j)
    (fun j => if j ≤ minContent V + b - 1 then
      max (diagLo V j) (diagLo V (j + a) - θ) - 1 else diagHi V j)
    (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j
    change (i, i + j) ∈ V \ (lowerMark V (zOf a θ) .d).W ↔ _
    rw [Finset.mem_sdiff, h.mem_V, mem_Z h]
    by_cases hj : j ≤ minContent V + b - 1
    · rw [ite_pos' hj]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        have h6 : ¬ (max (diagLo V j) (diagLo V (j + a) - θ) ≤ i) :=
          fun hh => h5 ⟨h1, hj, hh, h4⟩
        rw [not_le] at h6
        have hgp : 0 < gOf V a θ j := by
          unfold gOf; rw [lt_max_iff] at h6; omega
        have := (hthr j h1 hj).mp hgp
        exact ⟨this, h2, h3, by omega⟩
      · rintro ⟨h1, h2, h3, h4⟩
        have := hLZ j (by omega) hj h1
        have hbv := h.LZ_le_hi (by omega) hj
        refine ⟨⟨by omega, h2, h3, by omega⟩, ?_⟩
        rintro ⟨-, -, h5, -⟩
        omega
    · rw [ite_neg' hj]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨by omega, h2, h3, h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨⟨by omega, h2, h3, h4⟩, ?_⟩
        rintro ⟨-, h6, -⟩
        omega
  · intro j h1 h2
    by_cases hj : j ≤ minContent V + b - 1
    · rw [ite_pos' hj]
      have := hLZ j (by omega) hj h1
      omega
    · rw [ite_neg' hj]
      exact h.lo_le_hi (by omega) h2
  · intro j h1 h2
    have := h.bits (j := j) (by omega) h2
    omega
  · intro j h1 h2
    by_cases hj : j ≤ minContent V + b - 1
    · have hj' : j - 1 ≤ minContent V + b - 1 := by omega
      rw [ite_pos' hj, ite_pos' hj']
      have b1 := h.bits (j := j) (by omega) (by omega)
      have b2 := h.bits (j := j + a) (by omega) (by omega)
      have e : j + a - 1 = j - 1 + a := by ring
      rw [e] at b2
      omega
    · rw [ite_neg' hj]
      by_cases hj' : j - 1 ≤ minContent V + b - 1
      · rw [ite_pos' hj']
        have hjb : j = minContent V + b := by omega
        have hlz := hLZ (j - 1) (by omega) hj' (by omega)
        have hb1 := h.bits (j := j) (by omega) (by omega)
        subst hjb
        omega
      · rw [ite_neg' hj']
        exact (h.bits (j := j) (by omega) h2).2
  · by_cases hj : j0 ≤ minContent V + b - 1
    · have hl := hLZ j0 hj0a hj (le_refl _)
      change diagLo V j0 = if j0 ≤ minContent V + b - 1 then _ else _
      rw [ite_pos' hj]
      omega
    · have : j0 = minContent V + b := by omega
      subst this
      change diagLo V (minContent V + b) = if minContent V + b ≤ minContent V + b - 1 then _ else _
      rw [ite_neg' (by omega)]
      exact hk4
  · rw [ite_neg' (by omega)]
    exact hlast


theorem upper_complement_connected (h : DPackage V a b θ) :
    IsConnectedSkew ((lowerMark V (zOf a θ) .d).E \ (lowerMark V (zOf a θ) .d).upper) := by
  have hb := h.hb
  have hba := h.hba
  obtain ⟨j1, hj1a, hj1b, hthr⟩ := exists_upper_threshold h
  have hk4 := h.k4up
  have hfirst := h.first_single
  have hhM := h.hmax
  have hg0 := g_first_nonpos h
  -- the upper tails: `g_{j-a} = -1`
  have hLU : ∀ j, minContent V + a ≤ j → j ≤ j1 + a →
      max (diagLo V (j - a) + θ) (diagLo V j) = diagLo V j + 1 ∧
      diagLo V (j - a) + θ = diagLo V j + 1 := by
    intro j h1 h2
    have hg := (hthr (j - a) (by omega) (by omega)).mpr (by omega)
    have hk := h.k2 (j - a) (by omega) (by omega)
    unfold gOf at hg hk
    rw [show j - a + a = j by ring] at hg hk
    constructor
    · rw [max_def]; split_ifs <;> omega
    · omega
  refine isConnectedSkew_of_rows _ (minContent V) (j1 + a)
    (fun j => diagLo V j)
    (fun j => if j ≤ minContent V + a - 1 then diagHi V j else
      max (diagLo V (j - a) + θ) (diagLo V j) - 1)
    (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j
    change (i, i + j) ∈ V \ (lowerMark V (zOf a θ) .d).upper ↔ _
    rw [Finset.mem_sdiff, h.mem_V, mem_upper h]
    by_cases hj : j ≤ minContent V + a - 1
    · rw [ite_pos' hj]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨h1, by omega, h3, h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨⟨h1, by omega, h3, h4⟩, ?_⟩
        rintro ⟨h5, -⟩
        omega
    · rw [ite_neg' hj]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        have h6 : ¬ (max (diagLo V (j - a) + θ) (diagLo V j) ≤ i) :=
          fun hh => h5 ⟨by omega, h2, hh, h4⟩
        rw [not_le] at h6
        have hgp : gOf V a θ (j - a) < 0 := by
          unfold gOf; rw [show j - a + a = j by ring]; rw [lt_max_iff] at h6; omega
        have := (hthr (j - a) (by omega) (by omega)).mp hgp
        exact ⟨h1, by omega, h3, by omega⟩
      · rintro ⟨h1, h2, h3, h4⟩
        have := hLU j (by omega) h2
        refine ⟨⟨h1, by omega, h3, ?_⟩, ?_⟩
        · have := h.lo_le_hi (j := j) h1 (by omega)
          omega
        · rintro ⟨-, -, h5, -⟩
          omega
  · intro j h1 h2
    by_cases hj : j ≤ minContent V + a - 1
    · rw [ite_pos' hj]
      exact h.lo_le_hi h1 (by omega)
    · rw [ite_neg' hj]
      have := hLU j (by omega) h2
      omega
  · intro j h1 h2
    have := h.bits (j := j) (by omega) (by omega)
    omega
  · intro j h1 h2
    by_cases hj : j ≤ minContent V + a - 1
    · have hj' : j - 1 ≤ minContent V + a - 1 := by omega
      rw [ite_pos' hj, ite_pos' hj']
      exact (h.bits (j := j) (by omega) (by omega)).2
    · rw [ite_neg' hj]
      have hlu := hLU j (by omega) h2
      by_cases hj' : j - 1 ≤ minContent V + a - 1
      · rw [ite_pos' hj']
        have hjb : j = minContent V + a := by omega
        have hb1 := h.bits (j := j) (by omega) (by omega)
        subst hjb
        omega
      · rw [ite_neg' hj']
        have hlu' := hLU (j - 1) (by omega) (by omega)
        have hb1 := h.bits (j := j) (by omega) (by omega)
        omega
  · rw [ite_pos' (by omega)]
    exact hfirst
  · by_cases hj : j1 + a ≤ minContent V + a - 1
    · rw [ite_pos' hj]
      have : j1 + a = minContent V + a - 1 := by omega
      rw [this]; exact hk4
    · rw [ite_neg' hj]
      have := hLU (j1 + a) (by omega) (le_refl _)
      omega


theorem mem_middle (h : DPackage V a b θ) {i j : ℤ} :
    (i, i + j) ∈ (lowerMark V (zOf a θ) .d).middle ↔
      (minContent V ≤ j ∧ j ≤ minContent V + a + b - 1 ∧ diagLo V j ≤ i ∧ i ≤ diagHi V j) ∧
      ¬ (minContent V ≤ j ∧ j ≤ minContent V + b - 1 ∧
        max (diagLo V j) (diagLo V (j + a) - θ) ≤ i ∧ i ≤ diagHi V j) ∧
      ¬ (minContent V + a ≤ j ∧ j ≤ minContent V + a + b - 1 ∧
        max (diagLo V (j - a) + θ) (diagLo V j) ≤ i ∧ i ≤ diagHi V j) := by
  unfold middle
  change (i, i + j) ∈ V \ ((lowerMark V (zOf a θ) .d).W ∪ (lowerMark V (zOf a θ) .d).upper) ↔ _
  rw [Finset.mem_sdiff, Finset.mem_union, h.mem_V, mem_Z h, mem_upper h]
  simp only [not_or]

theorem middle_two_cells (h : DPackage V a b θ) {i j : ℤ}
    (h1 : (i, i + j) ∈ (lowerMark V (zOf a θ) .d).middle)
    (h2 : (i + 1, i + 1 + j) ∈ (lowerMark V (zOf a θ) .d).middle) :
    minContent V + b + 1 ≤ j ∧ j ≤ minContent V + a - 2 := by
  have hb := h.hb
  have hba := h.hba
  rw [mem_middle h] at h1 h2
  obtain ⟨⟨a1, a2, a3, a4⟩, a5, a6⟩ := h1
  obtain ⟨⟨b1, b2, b3, b4⟩, b5, b6⟩ := h2
  by_cases hj1 : j ≤ minContent V + b - 1
  · exfalso
    have hk := h.k2 j a1 hj1
    have : ¬ (max (diagLo V j) (diagLo V (j + a) - θ) ≤ i + 1) := fun hh => b5 ⟨b1, hj1, hh, b4⟩
    rw [not_le, lt_max_iff] at this
    omega
  · by_cases hj2 : j = minContent V + b
    · exfalso
      have := h.k4lo
      rw [← hj2] at this
      omega
    · by_cases hj3 : j = minContent V + a - 1
      · exfalso
        have := h.k4up
        rw [← hj3] at this
        omega
      · by_cases hj4 : minContent V + a ≤ j
        · exfalso
          have hk := h.k2 (j - a) (by omega) (by omega)
          rw [show j - a + a = j by ring] at hk
          have : ¬ (max (diagLo V (j - a) + θ) (diagLo V j) ≤ i + 1) :=
            fun hh => b6 ⟨hj4, b2, hh, b4⟩
          rw [not_le, lt_max_iff] at this
          omega
        · omega


theorem lowerV (h : DPackage V a b θ) : (lowerMark V (zOf a θ) .d).LowerV := by
  have hb := h.hb
  have hba := h.hba
  obtain ⟨j0, hj0a, hj0b, hthr⟩ := exists_lower_threshold h
  have hg0 := g_first_nonpos h
  have hjm : minContent V + 1 ≤ j0 := by
    by_contra hcon
    have : j0 = minContent V := by omega
    have := (hthr (minContent V) (le_refl _) (by omega)).mpr (by omega)
    omega
  -- the first cell of the diagonal `j0` lies in the middle
  have hbit := h.bits (j := j0) hjm (by omega)
  have hx0 : (diagLo V j0, diagLo V j0 + j0) ∈ (lowerMark V (zOf a θ) .d).middle := by
    rw [mem_middle h]
    have hl := h.lo_le_hi (j := j0) (by omega) (by omega)
    refine ⟨⟨by omega, by omega, le_refl _, hl⟩, ?_, ?_⟩
    · rintro ⟨h1, h2, h3, h4⟩
      have := (hthr j0 h1 h2).mpr (le_refl _)
      unfold gOf at this
      rw [max_le_iff] at h3
      omega
    · rintro ⟨h1, -⟩
      omega
  have hmin : minContent (lowerMark V (zOf a θ) .d).middle = j0 := by
    apply minContent_eq_of (k := j0)
    · rw [mem_contents_iff]
      exact ⟨_, hx0⟩
    · intro k hk
      rw [mem_contents_iff] at hk
      obtain ⟨i, hi⟩ := hk
      rw [mem_middle h] at hi
      obtain ⟨⟨a1, a2, a3, a4⟩, a5, -⟩ := hi
      by_contra hlt
      rw [not_le] at hlt
      have hr : k ≤ minContent V + b - 1 := by omega
      have : ¬ (max (diagLo V k) (diagLo V (k + a) - θ) ≤ i) := fun hh => a5 ⟨a1, hr, hh, a4⟩
      rw [not_le, lt_max_iff] at this
      have hgp : 0 < gOf V a θ k := by unfold gOf; omega
      have := (hthr k a1 hr).mp hgp
      omega
  refine ⟨_, hx0, ?_, ?_⟩
  · rw [hmin]; unfold content; simp
  · -- the southern neighbour lies in `W₋`
    have e : ((diagLo V j0 + 1, diagLo V j0 + j0) : ℤ × ℤ) =
        (diagLo V j0 + 1, diagLo V j0 + 1 + (j0 - 1)) := by ext <;> simp
    change (diagLo V j0 + 1, diagLo V j0 + j0) ∈ (lowerMark V (zOf a θ) .d).W
    rw [e, mem_Z h]
    have hgn := hthr (j0 - 1) (by omega) (by omega)
    have hgn' : gOf V a θ (j0 - 1) ≤ 0 := by
      by_contra hcon
      have := hgn.mp (by omega)
      omega
    unfold gOf at hgn'
    have e2 : j0 - 1 + a = j0 + a - 1 := by ring
    rw [e2] at hgn'
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [max_le_iff, e2]; omega
    · by_cases hj : j0 ≤ minContent V + b - 1
      · have hl := h.LZ_le_hi (j := j0) (by omega) hj
        have hg := (hthr j0 (by omega) hj).mpr (le_refl _)
        have hk := h.k2 j0 (by omega) hj
        unfold gOf at hg hk
        rw [max_def] at hl
        have hbit2 := h.bits (j := j0) hjm (by omega)
        split_ifs at hl <;> omega
      · have hjb : j0 = minContent V + b := by omega
        have hno : ∀ j, minContent V ≤ j → j ≤ minContent V + b - 1 →
            diagLo V (j + a) - θ - diagLo V j ≤ 0 := by
          intro j h1 h2
          by_contra hcon
          have := (hthr j h1 h2).mp (by unfold gOf; omega)
          omega
        have h5 := h.k5lo hno
        have h4 := h.k4lo
        rw [← hjb] at h5 h4
        omega


theorem upperH (h : DPackage V a b θ) : (lowerMark V (zOf a θ) .d).UpperH := by
  have hb := h.hb
  have hba := h.hba
  obtain ⟨j1, hj1a, hj1b, hthr⟩ := exists_upper_threshold h
  have hgl := g_last_nonneg h
  have hj1c : j1 ≤ minContent V + b - 2 := by
    by_contra hcon
    have : j1 = minContent V + b - 1 := by omega
    have := (hthr (minContent V + b - 1) (by omega) (le_refl _)).mpr (by omega)
    omega
  -- facts on the upper tails
  have hLU : ∀ j, minContent V + a ≤ j → j ≤ j1 + a →
      max (diagLo V (j - a) + θ) (diagLo V j) = diagLo V j + 1 ∧
      diagLo V (j - a) + θ = diagLo V j + 1 := by
    intro j h1 h2
    have hg := (hthr (j - a) (by omega) (by omega)).mpr (by omega)
    have hk := h.k2 (j - a) (by omega) (by omega)
    unfold gOf at hg hk
    rw [show j - a + a = j by ring] at hg hk
    constructor
    · rw [max_def]; split_ifs <;> omega
    · omega
  set jt := j1 + a with hjt
  have hlt := h.lo_le_hi (j := jt) (by omega) (by omega)
  have hx1 : (diagLo V jt, diagLo V jt + jt) ∈ (lowerMark V (zOf a θ) .d).middle := by
    rw [mem_middle h]
    refine ⟨⟨by omega, by omega, le_refl _, hlt⟩, ?_, ?_⟩
    · rintro ⟨-, h2, -⟩
      omega
    · rintro ⟨h1, h2, h3, h4⟩
      have := hLU jt h1 (le_refl _)
      omega
  have hmax : maxContent (lowerMark V (zOf a θ) .d).middle = jt := by
    apply maxContent_eq_of (k := jt)
    · rw [mem_contents_iff]
      exact ⟨_, hx1⟩
    · intro k hk
      rw [mem_contents_iff] at hk
      obtain ⟨i, hi⟩ := hk
      rw [mem_middle h] at hi
      obtain ⟨⟨a1, a2, a3, a4⟩, -, a6⟩ := hi
      by_contra hlt'
      rw [not_le] at hlt'
      have hr : minContent V + a ≤ k := by omega
      have : ¬ (max (diagLo V (k - a) + θ) (diagLo V k) ≤ i) := fun hh => a6 ⟨hr, a2, hh, a4⟩
      rw [not_le, lt_max_iff] at this
      have hgp : gOf V a θ (k - a) < 0 := by
        unfold gOf; rw [show k - a + a = k by ring]; omega
      have := (hthr (k - a) (by omega) (by omega)).mp hgp
      omega
  refine ⟨_, hx1, ?_, ?_⟩
  · rw [hmax]; unfold content; simp
  · have e : ((diagLo V jt, diagLo V jt + jt + 1) : ℤ × ℤ) =
        (diagLo V jt, diagLo V jt + (jt + 1)) := by ext <;> simp; ring
    change (diagLo V jt, diagLo V jt + jt + 1) ∈ (lowerMark V (zOf a θ) .d).upper
    rw [e, mem_upper h]
    have hgn := hthr (jt + 1 - a) (by omega) (by omega)
    have hgn' : 0 ≤ gOf V a θ (jt + 1 - a) := by
      by_contra hcon
      have := hgn.mp (by omega)
      omega
    unfold gOf at hgn'
    rw [show jt + 1 - a + a = jt + 1 by ring] at hgn'
    have hb1 := h.bits (j := jt + 1) (by omega) (by omega)
    rw [show jt + 1 - 1 = jt by ring] at hb1
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [max_le_iff]
      constructor
      · omega
      · omega
    · by_cases hj : minContent V ≤ j1
      · have hl := hLU jt (by omega) (le_refl _)
        have hk := h.k1 j1 hj (by omega)
        have e5 : j1 + a = jt := rfl
        rw [e5] at hk
        have := h.lo_le_hi (j := j1) hj (by omega)
        rw [show jt - a = j1 by omega] at hl
        omega
      · have hj1 : j1 = minContent V - 1 := by omega
        have hk4 := h.k4up
        have hno : ∀ j, minContent V ≤ j → j ≤ minContent V + b - 1 →
            0 ≤ diagLo V (j + a) - θ - diagLo V j := by
          intro j h1 h2
          by_contra hcon
          have := (hthr j h1 h2).mp (by unfold gOf; omega)
          omega
        have h5 := h.k5up hno
        have e6 : jt = minContent V + a - 1 := by omega
        have e8 : jt + 1 = minContent V + a := by omega
        rw [e8]
        rw [e6] at hlt ⊢
        omega


theorem W_content (h : DPackage V a b θ) {y : ℤ × ℤ} (hy : y ∈ (lowerMark V (zOf a θ) .d).W) :
    minContent V ≤ content y ∧ content y ≤ minContent V + b - 1 := by
  have := content_mem_contents hy
  rw [contents_Z h, Finset.mem_Icc] at this
  exact this

theorem hatWindowClear (h : DPackage V a b θ) : (lowerMark V (zOf a θ) .d).HatWindowClear := by
  have hb := h.hb
  have hba := h.hba
  intro k hk x hx y hy hadj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rw [Finset.mem_filter] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hv : (lowerMark V (zOf a θ) .d).v = zOf a θ := rfl
  rw [mem_translate, hv] at hx1 hx2
  -- the content of `y`
  have hyc : minContent V ≤ content y ∧ content y ≤ minContent V + b - 1 := by
    unfold hatMarkWindow at hy
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hy
    rcases hy with ⟨-, hy2⟩ | ⟨hy1, -⟩
    · have := W_content h hy2
      rw [content_eCell_add] at this
      exact this
    · exact W_content h hy1
  -- the cell `x₀ = x - k z` and its diagonal successor
  set x0 : ℤ × ℤ := x - k • zOf a θ with hx0
  have e1 : x0 = (x0.1, x0.1 + content x0) := by ext <;> simp [content]
  have e2 : x0 + eCell = (x0.1 + 1, x0.1 + 1 + content x0) := by
    ext
    · simp [eCell]
    · simp [eCell, content]; ring
  have hx2' : x0 + eCell ∈ (lowerMark V (zOf a θ) .d).middle := by
    have : x + eCell - k • zOf a θ = x0 + eCell := by rw [hx0]; abel
    rw [← this]; exact hx2
  rw [e1] at hx1
  rw [e2] at hx2'
  have hj := middle_two_cells h hx1 hx2'
  have hca := content_adj hadj
  have hcx : content x = content x0 + k * a := by
    have : x = x0 + k • zOf a θ := by rw [hx0]; abel
    rw [this, content_add, content_smul]
    have : content (zOf a θ) = a := by unfold zOf content; simp
    rw [this]
  rcases hk with hk | hk
  · rw [hk] at hcx
    omega
  · rw [hk] at hcx
    omega

theorem legal (h : DPackage V a b θ) : (lowerMark V (zOf a θ) .d).IsLegal := by
  have hwf : (lowerMark V (zOf a θ) .d).IsWellFormed := by
    refine ⟨h.conn, Or.inr ?_⟩
    refine ⟨⟨_, top_mem_Z h⟩, Z_connected h, W_subset h, upper_subset h, sw_mem_Z h,
      ne_mem_upper h, ?_⟩
    refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_, fun _ => ⟨lowerV h, upperH h⟩⟩
    all_goals exact absurd (show AttachCase.d = _ from hc) (by decide)
  have hn := narrow h
  exact ⟨hwf, maximal h, hn, ⟨lower_complement_connected h, upper_complement_connected h⟩,
    (noHatAdjacency_iff_window hwf hn).mpr (hatWindowClear h)⟩


theorem diagLo_Z (h : DPackage V a b θ) {j : ℤ} (h1 : minContent V ≤ j)
    (h2 : j ≤ minContent V + b - 1) :
    diagLo (lowerMark V (zOf a θ) .d).W j = max (diagLo V j) (diagLo V (j + a) - θ) := by
  apply diagLo_eq_of (l := max (diagLo V j) (diagLo V (j + a) - θ))
  · exact (mem_Z h).mpr ⟨h1, h2, le_rfl, h.LZ_le_hi h1 h2⟩
  · intro i hi
    exact ((mem_Z h).mp hi).2.2.1

theorem diagHi_Z (h : DPackage V a b θ) {j : ℤ} (h1 : minContent V ≤ j)
    (h2 : j ≤ minContent V + b - 1) : diagHi (lowerMark V (zOf a θ) .d).W j = diagHi V j := by
  apply diagHi_eq_of (l := diagHi V j)
  · exact (mem_Z h).mpr ⟨h1, h2, h.LZ_le_hi h1 h2, le_rfl⟩
  · intro i hi
    exact ((mem_Z h).mp hi).2.2.2

theorem minContent_Z (h : DPackage V a b θ) :
    minContent (lowerMark V (zOf a θ) .d).W = minContent V := by
  have hb := h.hb
  apply minContent_eq_of (k := minContent V)
  · rw [contents_Z h, Finset.mem_Icc]; omega
  · intro k hk
    rw [contents_Z h, Finset.mem_Icc] at hk
    exact hk.1

theorem maxContent_Z (h : DPackage V a b θ) :
    maxContent (lowerMark V (zOf a θ) .d).W = minContent V + b - 1 := by
  have hb := h.hb
  apply maxContent_eq_of (k := minContent V + b - 1)
  · rw [contents_Z h, Finset.mem_Icc]; omega
  · intro k hk
    rw [contents_Z h, Finset.mem_Icc] at hk
    exact hk.2

end DPackage

end MixedEta

end MarkedInner

end SkewGluing
