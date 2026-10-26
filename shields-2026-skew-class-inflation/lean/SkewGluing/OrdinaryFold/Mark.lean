-- TODO-COPIED: skew-factor-gluing/lean/SkewGluing/OrdinaryFold/Mark.lean
import SkewGluing.OrdinaryFold.Interval
import SkewGluing.Local

/-!
# A legal ordinary mark from slot data

Formalizes `shields-2026-skew-factor-gluing.tex`, «Two ordinary roots»
(`prop:gluing-ordinary-fold`),
the paragraph that defines the marks on the inner `G` of the fold: on the lower marked residues
`r ≥ σ` the southeast cell of the diagonal is removed, on the upper relative residues `r < τ` the
northwest cell (`eq:gluing-ordinary-slot`), and the legality conditions I–IV are verified.

The inner is given by the endpoint functions `lo`, `hi` of its diagonals (`DiagSet`).  The data
`SlotGeom` are the diagonal identities that the paper reads off the generic boundary words: the
lower and upper copies are congruent (`elo`, `ehi`), the private diagonals `w` and `q - 1` are
singletons, the retained lower copy has positive heights, and the two attachments are horizontal.

* `SlotGeom.mark_isLegal`: the mark `SlotGeom.mark` is legal (I–IV), of case (a) with copies
  `lowerCopy` and `disp q v₁`;
* `SlotGeom.mark_period`, `mark_width`, `mark_phases`: its period `q`, width `w` and middle phases
  `(s, t) = (σ, τ)`;
* `noHatAdjacency_of_thin`: the sufficient condition for IV used (thin middle, private singletons).

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

/-- The diagonal data of an inner `G` with a case-(a) mark of period `q` and width `w`, with lower
tail residues `[σ, w - 1]` and upper tail residues `[0, τ - 1]`, and displacement `v = (v₁, v₁ +
q)`.
`G` has the rows `[lo k, hi k]` on the contents `0 ≤ k ≤ q + w - 1`. -/
structure SlotGeom (q w τ σ v₁ : ℤ) (lo hi : ℤ → ℤ) : Prop where
  w_pos : 1 ≤ w
  w_lt : w < q
  σ_pos : 1 ≤ σ
  σ_le : σ ≤ w
  τ_nonneg : 0 ≤ τ
  τ_lt : τ < w
  shape : DiagShape 0 (q + w - 1) lo hi
  /-- The lower copy is congruent to the upper copy: first rows. -/
  elo_lt : ∀ r, 0 ≤ r → r < τ → lo (q + r) + 1 = lo r + v₁
  elo_ge : ∀ r, τ ≤ r → r < w → lo (q + r) = lo r + v₁
  /-- The lower copy is congruent to the upper copy: last rows. -/
  ehi_lt : ∀ r, 0 ≤ r → r < σ → hi (q + r) = hi r + v₁
  ehi_ge : ∀ r, σ ≤ r → r < w → hi (q + r) = hi r - 1 + v₁
  sing_w : lo w = hi w
  sing_q : lo (q - 1) = hi (q - 1)
  /-- The retained lower copy has positive heights. -/
  pos : ∀ r, 0 ≤ r → r < w → lo r + (if σ ≤ r then 1 else 0) ≤ hi r
  /-- The southeast tail cell on the residue `σ` is attached to the lower copy horizontally. -/
  capB : σ < w → hi (σ - 1) = hi σ
  /-- The lower attachment is horizontal. -/
  lowerH : lo (σ - 1) ≤ hi σ
  /-- The upper attachment is horizontal. -/
  upperH : lo (q + τ - 1) ≤ hi (q + τ)

namespace SlotGeom

variable {q w τ σ v₁ : ℤ} {lo hi : ℤ → ℤ}

/-- The lower copy `W₋`: on the contents `r < w` the cells of `G` except the southeast cell
on the residues `r ≥ σ`. -/
def lowerCopy (G : Diagram) (w σ : ℤ) (hi : ℤ → ℤ) : Diagram :=
  G.filter fun x => content x ≤ w - 1 ∧ x.1 ≤ hi (content x) - if σ ≤ content x then 1 else 0

/-- The displacement `v = (v₁, v₁ + q)`. -/
def disp (q v₁ : ℤ) : ℤ × ℤ := (v₁, v₁ + q)

theorem content_disp (q v₁ : ℤ) : content (disp q v₁) = q := by simp [disp, content]

variable {G : Diagram}

/-- The last rows of the retained lower copy. -/
def hiW (σ : ℤ) (hi : ℤ → ℤ) (k : ℤ) : ℤ := hi k - if σ ≤ k then 1 else 0

theorem diagSet_lowerCopy (hG : DiagSet G 0 (q + w - 1) lo hi) (_hw : 1 ≤ w) (hwq : w < q) :
    DiagSet (lowerCopy G w σ hi) 0 (w - 1) lo (hiW σ hi) := by
  intro i k
  unfold lowerCopy hiW
  have hc : content (i, i + k) = k := by simp [content]
  rw [Finset.mem_filter, hG]
  simp only [hc]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    exact ⟨h1, by omega, h3, h6⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, by omega, h3, ?_⟩, by omega, h4⟩
    split_ifs at h4 <;> omega

theorem diagSet_upper (hG : DiagSet G 0 (q + w - 1) lo hi) (hw : 1 ≤ w) (hwq : w < q)
    (hs : SlotGeom q w τ σ v₁ lo hi) :
    DiagSet (translate (disp q v₁) (lowerCopy G w σ hi)) q (q + w - 1)
      (fun k => lo k + if k - q < τ then 1 else 0) hi := by
  intro i k
  rw [mem_translate]
  have e : (i, i + k) - disp q v₁ = (i - v₁, (i - v₁) + (k - q)) := by
    ext <;> simp [disp]
    ring
  rw [e, diagSet_lowerCopy hG hw hwq]
  unfold hiW
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by omega, by omega, ?_, ?_⟩
    · by_cases ht : k - q < τ
      · have := hs.elo_lt (k - q) (by omega) ht
        simp only [ht, ite_true]
        have e2 : q + (k - q) = k := by ring
        rw [e2] at this
        omega
      · have := hs.elo_ge (k - q) (by omega) (by omega)
        simp only [ht, ite_false]
        have e2 : q + (k - q) = k := by ring
        rw [e2] at this
        omega
    · by_cases ht : σ ≤ k - q
      · have := hs.ehi_ge (k - q) ht (by omega)
        have e2 : q + (k - q) = k := by ring
        rw [e2] at this
        simp only [ht, ite_true] at h4
        omega
      · have := hs.ehi_lt (k - q) (by omega) (by omega)
        have e2 : q + (k - q) = k := by ring
        rw [e2] at this
        simp only [ht, ite_false] at h4
        omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by omega, by omega, ?_, ?_⟩
    · by_cases ht : k - q < τ
      · have := hs.elo_lt (k - q) (by omega) ht
        simp only [ht, ite_true] at h3
        have e2 : q + (k - q) = k := by ring
        rw [e2] at this
        omega
      · have := hs.elo_ge (k - q) (by omega) (by omega)
        simp only [ht, ite_false] at h3
        have e2 : q + (k - q) = k := by ring
        rw [e2] at this
        omega
    · by_cases ht : σ ≤ k - q
      · have := hs.ehi_ge (k - q) ht (by omega)
        have e2 : q + (k - q) = k := by ring
        rw [e2] at this
        simp only [ht, ite_true]
        omega
      · have := hs.ehi_lt (k - q) (by omega) (by omega)
        have e2 : q + (k - q) = k := by ring
        rw [e2] at this
        simp only [ht, ite_false]
        omega


/-- The first rows of the middle `O`. -/
def loO (w : ℤ) (lo hi : ℤ → ℤ) (k : ℤ) : ℤ := if k < w then hi k else lo k

/-- The last rows of the middle `O`. -/
def hiO (q : ℤ) (lo hi : ℤ → ℤ) (k : ℤ) : ℤ := if q ≤ k then lo k else hi k

theorem diagSet_middle (hG : DiagSet G 0 (q + w - 1) lo hi) (hs : SlotGeom q w τ σ v₁ lo hi) :
    DiagSet (G \ (lowerCopy G w σ hi ∪ translate (disp q v₁) (lowerCopy G w σ hi))) σ (q + τ - 1)
      (loO w lo hi) (hiO q lo hi) := by
  have hw := hs.w_pos
  have hwq := hs.w_lt
  intro i k
  rw [Finset.mem_sdiff, Finset.mem_union, hG, diagSet_lowerCopy hG hw hwq i k,
    diagSet_upper hG hw hwq hs i k]
  unfold hiW loO hiO
  beta_reduce
  have hne := hs.shape.ne
  have hσ := hs.σ_pos
  have hσw := hs.σ_le
  have hτ0 := hs.τ_nonneg
  have hτw := hs.τ_lt
  by_cases h0 : 0 ≤ k
  · by_cases h1 : k ≤ q + w - 1
    · have hk := hne k h0 h1
      split_ifs <;> omega
    · omega
  · omega

/-- The first rows of `G ∖ W₋`. -/
def loA (w : ℤ) (lo hi : ℤ → ℤ) (k : ℤ) : ℤ := if k < w then hi k else lo k

theorem diagSet_sdiff_lower (hG : DiagSet G 0 (q + w - 1) lo hi) (hs : SlotGeom q w τ σ v₁ lo hi) :
    DiagSet (G \ lowerCopy G w σ hi) σ (q + w - 1) (loA w lo hi) hi := by
  have hw := hs.w_pos
  have hwq := hs.w_lt
  intro i k
  rw [Finset.mem_sdiff, hG, diagSet_lowerCopy hG hw hwq i k]
  unfold hiW loA
  have hne := hs.shape.ne
  have hσ := hs.σ_pos
  have hσw := hs.σ_le
  by_cases h0 : 0 ≤ k
  · by_cases h1 : k ≤ q + w - 1
    · have hk := hne k h0 h1
      split_ifs <;> omega
    · omega
  · omega

/-- The last rows of `G ∖ W₊`. -/
def hiB (q : ℤ) (lo hi : ℤ → ℤ) (k : ℤ) : ℤ := if q ≤ k then lo k else hi k

theorem diagSet_sdiff_upper (hG : DiagSet G 0 (q + w - 1) lo hi) (hs : SlotGeom q w τ σ v₁ lo hi) :
    DiagSet (G \ translate (disp q v₁) (lowerCopy G w σ hi)) 0 (q + τ - 1) lo (hiB q lo hi) := by
  have hw := hs.w_pos
  have hwq := hs.w_lt
  intro i k
  rw [Finset.mem_sdiff, hG, diagSet_upper hG hw hwq hs i k]
  unfold hiB
  beta_reduce
  have hne := hs.shape.ne
  have hσ := hs.σ_pos
  have hτ0 := hs.τ_nonneg
  have hτw := hs.τ_lt
  by_cases h0 : 0 ≤ k
  · by_cases h1 : k ≤ q + w - 1
    · have hk := hne k h0 h1
      split_ifs <;> omega
    · omega
  · omega


theorem shape_lowerCopy (hs : SlotGeom q w τ σ v₁ lo hi) :
    DiagShape 0 (w - 1) lo (hiW σ hi) := by
  have hw := hs.w_pos
  have hwq := hs.w_lt
  have hσ := hs.σ_pos
  have hσw := hs.σ_le
  have hτ0 := hs.τ_nonneg
  have hτw := hs.τ_lt
  have sh := hs.shape
  refine ⟨by omega, fun k h0 h1 => ?_, fun k h0 h1 => ?_, fun k h0 h1 => ?_, ?_, ?_⟩
  · have := hs.pos k h0 (by omega)
    unfold hiW
    split_ifs at this ⊢ <;> omega
  · exact sh.stepLo k h0 (by omega)
  · have := sh.stepHi k h0 (by omega)
    unfold hiW
    by_cases hk : k = σ
    · have := hs.capB (by omega)
      subst hk
      simp only [le_refl, ite_true, show ¬ (k ≤ k - 1) by omega, ite_false]
      omega
    · split_ifs <;> omega
  · have := sh.endLo
    unfold hiW
    simp only [show ¬ (σ ≤ 0) by omega, ite_false]
    omega
  · have h1 := sh.endHi
    have h2 := hs.elo_ge (w - 1) (by omega) (by omega)
    unfold hiW
    by_cases hk : σ ≤ w - 1
    · have h3 := hs.ehi_ge (w - 1) hk (by omega)
      simp only [hk, ite_true]
      have e : q + (w - 1) = q + w - 1 := by ring
      rw [e] at h2 h3
      omega
    · have h3 := hs.ehi_lt (w - 1) (by omega) (by omega)
      simp only [hk, ite_false]
      have e : q + (w - 1) = q + w - 1 := by ring
      rw [e] at h2 h3
      omega

theorem shape_middle (hs : SlotGeom q w τ σ v₁ lo hi) :
    DiagShape σ (q + τ - 1) (loO w lo hi) (hiO q lo hi) := by
  have hw := hs.w_pos
  have hwq := hs.w_lt
  have hσ := hs.σ_pos
  have hσw := hs.σ_le
  have hτ0 := hs.τ_nonneg
  have hτw := hs.τ_lt
  have sh := hs.shape
  have s1 := hs.sing_w
  have s2 := hs.sing_q
  unfold loO hiO
  refine ⟨by omega, fun k h0 h1 => ?_, fun k h0 h1 => ?_, fun k h0 h1 => ?_, ?_, ?_⟩
  · have := sh.ne k (by omega) (by omega)
    split_ifs <;> omega
  · have b1 := sh.stepLo k (by omega) (by omega)
    have b2 := sh.stepHi k (by omega) (by omega)
    by_cases hk1 : k - 1 < w <;> by_cases hk2 : k < w
    · simp only [hk1, hk2, ite_true]; omega
    · have : k = w := by omega
      subst this
      simp only [hk1, hk2, ite_true, ite_false]; omega
    · omega
    · simp only [hk1, hk2, ite_false]; omega
  · have b1 := sh.stepLo k (by omega) (by omega)
    have b2 := sh.stepHi k (by omega) (by omega)
    by_cases hk1 : q ≤ k - 1 <;> by_cases hk2 : q ≤ k
    · simp only [hk1, hk2, ite_true]; omega
    · omega
    · have : k = q := by omega
      subst this
      simp only [hk1, hk2, ite_true, ite_false]; omega
    · simp only [hk1, hk2, ite_false]; omega
  · by_cases h : σ < w
    · simp only [h, ite_true, show ¬ (q ≤ σ) by omega, ite_false]
    · have : σ = w := by omega
      subst this
      simp only [lt_irrefl, ite_false, show ¬ (q ≤ σ) by omega]
      omega
  · by_cases h : τ = 0
    · subst h
      simp only [add_zero, show ¬ (q - 1 < w) by omega, ite_false, show ¬ (q ≤ q - 1) by omega]
      omega
    · simp only [show ¬ (q + τ - 1 < w) by omega, ite_false, show q ≤ q + τ - 1 by omega,
        ite_true]

theorem shape_sdiff_lower (hs : SlotGeom q w τ σ v₁ lo hi) :
    DiagShape σ (q + w - 1) (loA w lo hi) hi := by
  have hw := hs.w_pos
  have hwq := hs.w_lt
  have hσ := hs.σ_pos
  have hσw := hs.σ_le
  have sh := hs.shape
  have s1 := hs.sing_w
  unfold loA
  refine ⟨by omega, fun k h0 h1 => ?_, fun k h0 h1 => ?_, fun k h0 h1 => ?_, ?_, ?_⟩
  · have := sh.ne k (by omega) (by omega)
    split_ifs <;> omega
  · have b1 := sh.stepLo k (by omega) (by omega)
    have b2 := sh.stepHi k (by omega) (by omega)
    by_cases hk1 : k - 1 < w <;> by_cases hk2 : k < w
    · simp only [hk1, hk2, ite_true]; omega
    · have : k = w := by omega
      subst this
      simp only [hk1, hk2, ite_true, ite_false]; omega
    · omega
    · simp only [hk1, hk2, ite_false]; omega
  · exact sh.stepHi k (by omega) h1
  · by_cases h : σ < w
    · simp only [h, ite_true]
    · have : σ = w := by omega
      subst this
      simp only [lt_irrefl, ite_false]
      omega
  · have := sh.endHi
    simp only [show ¬ (q + w - 1 < w) by omega, ite_false]
    omega

theorem shape_sdiff_upper (hs : SlotGeom q w τ σ v₁ lo hi) :
    DiagShape 0 (q + τ - 1) lo (hiB q lo hi) := by
  have hw := hs.w_pos
  have hwq := hs.w_lt
  have hτ0 := hs.τ_nonneg
  have hτw := hs.τ_lt
  have sh := hs.shape
  have s2 := hs.sing_q
  unfold hiB
  refine ⟨by omega, fun k h0 h1 => ?_, fun k h0 h1 => ?_, fun k h0 h1 => ?_, ?_, ?_⟩
  · have := sh.ne k (by omega) (by omega)
    split_ifs <;> omega
  · exact sh.stepLo k h0 (by omega)
  · have b1 := sh.stepLo k (by omega) (by omega)
    have b2 := sh.stepHi k (by omega) (by omega)
    by_cases hk1 : q ≤ k - 1 <;> by_cases hk2 : q ≤ k
    · simp only [hk1, hk2, ite_true]; omega
    · omega
    · have : k = q := by omega
      subst this
      simp only [hk1, hk2, ite_true, ite_false]; omega
    · simp only [hk1, hk2, ite_false]; omega
  · have := sh.endLo
    simp only [show ¬ (q ≤ 0) by omega, ite_false]
    exact this
  · by_cases h : τ = 0
    · subst h
      simp only [add_zero, show ¬ (q ≤ q - 1) by omega, ite_false]
      omega
    · simp only [show q ≤ q + τ - 1 by omega, ite_true]


end SlotGeom

/-- **A sufficient condition for IV.**  If the middle has at most one cell on each content
`≤ c₀ + w` and each content `≥ c₀ + q - 1`, where `c₀` is the least content of `E`, then no hatted
middle cell is adjacent to a hatted mark cell: a hatted middle cell lies on a content of the
middle with two cells, hence in `[c₀ + w + 1, c₀ + q - 2]` modulo `q`, while hatted mark cells lie
in `[c₀, c₀ + w - 1]` modulo `q`, at distance at least two. -/
theorem noHatAdjacency_of_thin {ω : MarkedInner} (hE : IsConnectedSkew ω.E)
    (hn : ω.IsNonemptyMark) (hII : ω.IsNarrow)
    (thin : ∀ x ∈ ω.middle, ∀ y ∈ ω.middle, content x = content y →
      (content x ≤ minContent ω.E + ω.width ∨ minContent ω.E + ω.period - 1 ≤ content x) →
        x = y) :
    ω.NoHatAdjacency := by
  have hb := hn.content_bounds hE
  obtain ⟨hw0, hwq⟩ := hII
  intro k m x hx y hy hadj
  obtain ⟨hx1, hx2⟩ := hx
  have hx1' := mem_translate_smul.mp hx1
  have hx2' := mem_translate_smul.mp hx2
  have hxe : x + eCell - k • ω.v = (x - k • ω.v) + eCell := by abel
  rw [hxe] at hx2'
  have hc1 : content (x - k • ω.v + eCell) = content (x - k • ω.v) := content_eCell_add _
  have hne : x - k • ω.v ≠ x - k • ω.v + eCell := by
    intro h
    have := congrArg Prod.fst h
    simp [eCell] at this
  have hcx : content x = content (x - k • ω.v) + k * ω.period := by
    rw [content_sub, content_smul]
    have : content ω.v = ω.period := rfl
    rw [this]; ring
  have hmid : minContent ω.E + ω.width < content (x - k • ω.v) ∧
      content (x - k • ω.v) < minContent ω.E + ω.period - 1 := by
    by_contra hcon
    apply hne
    apply thin _ hx1' _ hx2' hc1.symm
    omega
  have hyW : ∃ z : ℤ × ℤ, z - m • ω.v ∈ ω.W ∧ content z = content y := by
    rcases hy with ⟨-, hy2⟩ | ⟨hy1, -⟩
    · exact ⟨y + eCell, mem_translate_smul.mp hy2, content_eCell_add y⟩
    · exact ⟨y, mem_translate_smul.mp hy1, rfl⟩
  obtain ⟨z, hz, hzc⟩ := hyW
  have hzb := hb.1 _ hz
  rw [content_sub, content_smul] at hzb
  have hper : content ω.v = ω.period := rfl
  rw [hper] at hzb
  have hq : 0 < ω.period := by omega
  have hadj' := content_adj hadj
  rw [hcx, ← hzc] at hadj'
  -- `n q + e = ±1` with `2 ≤ e ≤ q - 2` is impossible
  set n := k - m with hn'
  have key : ∀ e : ℤ, 2 ≤ e → e ≤ ω.period - 2 → n * ω.period + e ≠ 1 ∧ n * ω.period + e ≠ -1 := by
    intro e h1 h2
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · have : n * ω.period ≤ -ω.period := by nlinarith
      omega
    · rw [hn0]; omega
    · have : n * ω.period ≥ ω.period := by nlinarith
      omega
  have hk : k * ω.period - m * ω.period = n * ω.period := by rw [hn']; ring
  rcases hadj' with h | h
  · have := key (content (x - k • ω.v) - (content z - m * ω.period))
      (by omega) (by omega)
    omega
  · have := key (content (x - k • ω.v) - (content z - m * ω.period))
      (by omega) (by omega)
    omega

namespace SlotGeom

variable {q w τ σ v₁ : ℤ} {lo hi : ℤ → ℤ} {G : Diagram}

/-- The marked inner built from the slot data. -/
def mark (G : Diagram) (q w σ v₁ : ℤ) (hi : ℤ → ℤ) : MarkedInner where
  E := G
  W := lowerCopy G w σ hi
  v := disp q v₁
  case := .a

theorem mark_upper : (mark G q w σ v₁ hi).upper = translate (disp q v₁) (lowerCopy G w σ hi) :=
  rfl

theorem mark_middle : (mark G q w σ v₁ hi).middle =
    G \ (lowerCopy G w σ hi ∪ translate (disp q v₁) (lowerCopy G w σ hi)) := rfl

/-- **The mark of the fold is legal** (`prop:gluing-ordinary-fold`, the legality conditions I–IV
of the marks on `G`).  The mark `mark G q w σ v₁ hi` is a legal ordinary mark of case (a) with
nonempty copies, of period `q` and width `w`, and its middle phases are `(s, t) = (σ, τ)`. -/
theorem mark_isLegal (hG : DiagSet G 0 (q + w - 1) lo hi) (hs : SlotGeom q w τ σ v₁ lo hi) :
    (mark G q w σ v₁ hi).IsLegal := by
  have hw := hs.w_pos
  have hwq := hs.w_lt
  have hσ := hs.σ_pos
  have hσw := hs.σ_le
  have hτ0 := hs.τ_nonneg
  have hτw := hs.τ_lt
  have sh := hs.shape
  have hW := diagSet_lowerCopy hG hw hwq (σ := σ)
  have hshW := shape_lowerCopy hs
  have hT := diagSet_upper hG hw hwq hs
  have hO := diagSet_middle hG hs
  have hshO := shape_middle hs
  have hA := diagSet_sdiff_lower hG hs
  have hshA := shape_sdiff_lower hs
  have hB := diagSet_sdiff_upper hG hs
  have hshB := shape_sdiff_upper hs
  have hGcs := hG.isConnectedSkew sh
  have hWcs := hW.isConnectedSkew hshW
  have hWne := hW.nonempty hshW
  have hswG := hG.sw_eq sh
  have hneG := hG.ne_eq sh
  have hmin := hG.minContent_eq sh
  have hcsd : content (disp q v₁) = q := content_disp q v₁
  -- W is contained in G, and so is its translate
  have hWG : lowerCopy G w σ hi ⊆ G := Finset.filter_subset _ _
  have hTG : translate (disp q v₁) (lowerCopy G w σ hi) ⊆ G := by
    intro x hx
    obtain ⟨i, j⟩ := x
    have e : i + (j - i) = j := by ring
    have h2 := (hT i (j - i)).mp (by rw [e]; exact hx)
    have h3 : lo (j - i) ≤ i := by
      obtain ⟨-, -, h2c, -⟩ := h2
      beta_reduce at h2c
      split_ifs at h2c <;> omega
    have h4 := (hG i (j - i)).mpr ⟨by omega, by omega, h3, h2.2.2.2⟩
    rwa [e] at h4
  have hwf : (mark G q w σ v₁ hi).IsWellFormed := by
    refine ⟨hGcs, Or.inr ?_⟩
    refine ⟨hWne, hWcs, hWG, hTG, ?_, ?_, ?_⟩
    · -- sw G ∈ W
      change sw G ∈ lowerCopy G w σ hi
      rw [hswG]
      have := (hW (lo 0) 0).mpr ⟨le_refl _, by omega, le_refl _, by
        have := hshW.ne 0 (le_refl _) (by omega)
        exact this⟩
      simpa using this
    · -- ne G ∈ upper
      change ne G ∈ translate (disp q v₁) (lowerCopy G w σ hi)
      rw [hneG]
      have hnl : ¬ (q + w - 1 - q < τ) := by omega
      have hend := sh.endHi
      have h3 : (fun k => lo k + if k - q < τ then 1 else 0) (q + w - 1) ≤ lo (q + w - 1) := by
        beta_reduce
        simp only [hnl, ite_false]
        omega
      have := (hT (lo (q + w - 1)) (q + w - 1)).mpr ⟨by omega, le_refl _, h3, by omega⟩
      simpa using this
    · -- attachments
      have hmid := mark_middle (G := G) (q := q) (w := w) (σ := σ) (v₁ := v₁) (hi := hi)
      refine ⟨fun _ => ⟨?_, ?_⟩, fun h => by simp [mark] at h, fun h => by simp [mark] at h,
        fun h => by simp [mark] at h⟩
      · -- lower horizontal
        change ∃ x ∈ (mark G q w σ v₁ hi).middle, content x = minContent (mark G q w σ v₁
            hi).middle ∧
          (x.1, x.2 - 1) ∈ (mark G q w σ v₁ hi).W
        rw [mark_middle]
        have hmc := hO.minContent_eq hshO
        have hne' := hshO.ne σ (le_refl _) (by omega)
        have hloσ : loO w lo hi σ = hi σ := by
          unfold loO
          by_cases h : σ < w
          · simp [h]
          · have : σ = w := by omega
            subst this
            simp only [lt_irrefl, ite_false]
            exact hs.sing_w
        refine ⟨(loO w lo hi σ, loO w lo hi σ + σ), (hO _ _).mpr ⟨le_refl _, by omega, le_refl _,
          hne'⟩, ?_, ?_⟩
        · rw [hmc]; simp [content]
        · change (loO w lo hi σ, loO w lo hi σ + σ - 1) ∈ lowerCopy G w σ hi
          have e : loO w lo hi σ + σ - 1 = loO w lo hi σ + (σ - 1) := by ring
          rw [e, hW]
          have b := sh.stepHi σ (by omega) (by omega)
          unfold hiW
          simp only [show ¬ (σ ≤ σ - 1) by omega, ite_false]
          refine ⟨by omega, by omega, ?_, ?_⟩
          · rw [hloσ]; exact hs.lowerH
          · rw [hloσ]; omega
      · -- upper horizontal
        change ∃ x ∈ (mark G q w σ v₁ hi).middle, content x = maxContent (mark G q w σ v₁
            hi).middle ∧
          (x.1, x.2 + 1) ∈ (mark G q w σ v₁ hi).upper
        rw [mark_middle, mark_upper]
        have hmc := hO.maxContent_eq hshO
        have hne' := hshO.ne (q + τ - 1) (by omega) le_rfl
        have hhi1 : hiO q lo hi (q + τ - 1) = lo (q + τ - 1) := by
          unfold hiO
          by_cases h : τ = 0
          · subst h
            simp only [add_zero, show ¬ (q ≤ q - 1) by omega, ite_false]
            exact hs.sing_q.symm
          · simp only [show q ≤ q + τ - 1 by omega, ite_true]
        have hlo1 : loO w lo hi (q + τ - 1) = lo (q + τ - 1) := by
          unfold loO
          simp only [show ¬ (q + τ - 1 < w) by omega, ite_false]
        refine ⟨(hiO q lo hi (q + τ - 1), hiO q lo hi (q + τ - 1) + (q + τ - 1)),
          (hO _ _).mpr ⟨by omega, le_rfl, hne', le_rfl⟩, ?_, ?_⟩
        · rw [hmc]; simp [content]
        · have e : hiO q lo hi (q + τ - 1) + (q + τ - 1) + 1 =
              hiO q lo hi (q + τ - 1) + (q + τ) := by ring
          change (hiO q lo hi (q + τ - 1), hiO q lo hi (q + τ - 1) + (q + τ - 1) + 1) ∈
            translate (disp q v₁) (lowerCopy G w σ hi)
          rw [e, hT]
          have b := sh.stepLo (q + τ) (by omega) (by omega)
          have : ¬ (q + τ - q < τ) := by omega
          simp only [this, ite_false]
          refine ⟨by omega, by omega, ?_, ?_⟩
          · rw [hhi1]; omega
          · rw [hhi1]; exact hs.upperH
  have hnarrow : (mark G q w σ v₁ hi).IsNarrow := by
    have hsp := hW.span_eq hshW
    refine ⟨by positivity, ?_⟩
    change ((span (lowerCopy G w σ hi) : ℕ) : ℤ) < content (disp q v₁)
    rw [hcsd]
    omega
  refine ⟨hwf, ?_, hnarrow, ⟨?_, ?_⟩, ?_⟩
  · -- I: maximality
    have hnon := hwf.2.resolve_left (by
      intro h
      have : (lowerCopy G w σ hi).Nonempty := hWne
      have h1 := h.1
      change lowerCopy G w σ hi = ∅ at h1
      rw [h1] at this
      exact absurd this (by simp))
    apply IsMaximalAtDisplacement.isMaximal hGcs hnon
    intro W' hW' hlt hsk hc hsub
    have hsubW : W' ⊆ lowerCopy G w σ hi := by
      intro y hy
      obtain ⟨i, j⟩ := y
      have hyE : (i, j) ∈ G := Finset.mem_powerset.mp hW' hy
      have hc' : contents W' = contents (lowerCopy G w σ hi) := hc
      have hkc : j - i ∈ contents (lowerCopy G w σ hi) := by
        rw [← hc']; exact content_mem_contents hy
      rw [hW.contents_eq hshW, Finset.mem_Icc] at hkc
      have e : i + (j - i) = j := by ring
      have hyv : (i, j) + disp q v₁ ∈ translate (disp q v₁) W' :=
        Finset.mem_image_of_mem _ hy
      have hyv' : (i, j) + disp q v₁ ∈ G := hsub hyv
      have e2 : (i, j) + disp q v₁ = (i + v₁, (i + v₁) + (j - i + q)) := by
        ext <;> simp [disp]
        ring
      rw [e2, hG] at hyv'
      have e3 : j - i + q = q + (j - i) := by ring
      rw [e3] at hyv'
      have hyE' := (hG i (j - i)).mp (by rw [e]; exact hyE)
      have := hs.ehi_lt
      have := hs.ehi_ge
      have key : i ≤ hiW σ hi (j - i) := by
        unfold hiW
        by_cases h : σ ≤ j - i
        · have := hs.ehi_ge (j - i) h (by omega)
          simp only [h, ite_true]
          omega
        · have := hs.ehi_lt (j - i) (by omega) (by omega)
          simp only [h, ite_false]
          omega
      have := (hW i (j - i)).mpr ⟨hkc.1, hkc.2, hyE'.2.2.1, key⟩
      rw [e] at this
      exact this
    exact hlt.2 hsubW
  · exact hA.isConnectedSkew hshA
  · exact hB.isConnectedSkew hshB
  · -- IV
    have hnon := hwf.2.resolve_left (by
      intro h
      have : (lowerCopy G w σ hi).Nonempty := hWne
      have h1 := h.1
      change lowerCopy G w σ hi = ∅ at h1
      rw [h1] at this
      exact absurd this (by simp))
    apply noHatAdjacency_of_thin hGcs hnon hnarrow
    intro x hx y hy hxy hrange
    rw [mark_middle] at hx hy
    have hspan := hW.span_eq hshW
    change (span (lowerCopy G w σ hi) : ℤ) = w - 1 - 0 + 1 at hspan
    have hmid : (mark G q w σ v₁ hi).width = (span (lowerCopy G w σ hi)) := rfl
    obtain ⟨i, j⟩ := x
    obtain ⟨i', j'⟩ := y
    have hx' := (hO i (j - i)).mp (by
      have e : i + (j - i) = j := by ring
      rw [e]; exact hx)
    have hy' := (hO i' (j' - i')).mp (by
      have e : i' + (j' - i') = j' := by ring
      rw [e]; exact hy)
    change j - i = j' - i' at hxy
    have hmc : minContent G = 0 := hmin
    have hcw : ((mark G q w σ v₁ hi).width : ℤ) = w := by omega
    have hcq : (mark G q w σ v₁ hi).period = q := by
      change content (disp q v₁) = q
      exact hcsd
    change j - i ≤ minContent G + ((mark G q w σ v₁ hi).width : ℤ) ∨
      minContent G + (mark G q w σ v₁ hi).period - 1 ≤ j - i at hrange
    rw [hcw, hcq, hmc] at hrange
    have hrow : loO w lo hi (j - i) = hiO q lo hi (j - i) := by
      have hs1 := hs.sing_w
      have hs2 := hs.sing_q
      unfold loO hiO
      rcases hrange with h | h
      · by_cases h1 : j - i < w
        · simp only [h1, ite_true, show ¬ (q ≤ j - i) by omega, ite_false]
        · have : j - i = w := by omega
          rw [this]
          simp only [lt_irrefl, ite_false, show ¬ (q ≤ w) by omega]
          exact hs1
      · by_cases h1 : q ≤ j - i
        · simp only [show ¬ (j - i < w) by omega, ite_false, h1, ite_true]
        · have : j - i = q - 1 := by omega
          rw [this]
          simp only [show ¬ (q - 1 < w) by omega, ite_false, show ¬ (q ≤ q - 1) by omega]
          exact hs2
    rw [← hxy] at hy'
    have hii : i = i' := by omega
    have hjj : j = j' := by omega
    rw [hii, hjj]

theorem mark_width (hG : DiagSet G 0 (q + w - 1) lo hi) (hs : SlotGeom q w τ σ v₁ lo hi) :
    ((mark G q w σ v₁ hi).width : ℤ) = w := by
  have hsp := (diagSet_lowerCopy hG hs.w_pos hs.w_lt (σ := σ)).span_eq (shape_lowerCopy hs)
  change ((span (lowerCopy G w σ hi) : ℕ) : ℤ) = w
  omega

theorem mark_period : (mark G q w σ v₁ hi).period = q := content_disp q v₁

theorem mark_nonempty (hG : DiagSet G 0 (q + w - 1) lo hi) (hs : SlotGeom q w τ σ v₁ lo hi) :
    (mark G q w σ v₁ hi).W.Nonempty :=
  (diagSet_lowerCopy hG hs.w_pos hs.w_lt (σ := σ)).nonempty (shape_lowerCopy hs)

/-- The first rows of `E` read by the mark. -/
theorem mark_lo (hG : DiagSet G 0 (q + w - 1) lo hi) (hs : SlotGeom q w τ σ v₁ lo hi) {a : ℤ}
    (h0 : 0 ≤ a) (h1 : a ≤ q + w - 1) : (mark G q w σ v₁ hi).lo a = lo a := by
  unfold MarkedInner.lo
  change diagLo G (minContent G + a) = lo a
  rw [hG.minContent_eq hs.shape, zero_add]
  exact hG.diagLo_eq hs.shape h0 h1

theorem mark_hi (hG : DiagSet G 0 (q + w - 1) lo hi) (hs : SlotGeom q w τ σ v₁ lo hi) {a : ℤ}
    (h0 : 0 ≤ a) (h1 : a ≤ q + w - 1) : (mark G q w σ v₁ hi).hi a = hi a := by
  unfold MarkedInner.hi
  change diagHi G (minContent G + a) = hi a
  rw [hG.minContent_eq hs.shape, zero_add]
  exact hG.diagHi_eq hs.shape h0 h1

theorem mark_rowShift : (mark G q w σ v₁ hi).rowShift = v₁ := rfl

/-- The middle phases of the mark are `(s, t) = (σ, τ)`. -/
theorem mark_phases (hG : DiagSet G 0 (q + w - 1) lo hi) (hs : SlotGeom q w τ σ v₁ lo hi) :
    (mark G q w σ v₁ hi).IsPhases σ τ := by
  have hw := hs.w_pos
  have hwq := hs.w_lt
  have hwz : (mark G q w σ v₁ hi).widthZ = w := mark_width hG hs
  have hper := mark_period (G := G) (q := q) (w := w) (σ := σ) (v₁ := v₁) (hi := hi)
  have hσw := hs.σ_le
  have hτw := hs.τ_lt
  refine ⟨hs.σ_pos, by omega, hs.τ_nonneg, by omega, ?_, ?_⟩
  · intro a h0 h1
    rw [hwz] at h1
    have e1 := mark_lo hG hs (a := a + q) (by omega) (by omega)
    have e2 := mark_lo hG hs (a := a) (by omega) (by omega)
    have e3 := mark_hi hG hs (a := a + q) (by omega) (by omega)
    have e4 := mark_hi hG hs (a := a) (by omega) (by omega)
    unfold MarkedInner.TailLower MarkedInner.dLo MarkedInner.dHi
    rw [hper, e1, e2, e3, e4, mark_rowShift]
    have ec : a + q = q + a := by ring
    rw [ec]
    by_cases hτ : a < τ
    · have := hs.elo_lt a h0 hτ
      by_cases hσ : σ ≤ a
      · have := hs.ehi_ge a hσ (by omega)
        omega
      · have := hs.ehi_lt a h0 (by omega)
        omega
    · have := hs.elo_ge a (by omega) (by omega)
      by_cases hσ : σ ≤ a
      · have := hs.ehi_ge a hσ (by omega)
        omega
      · have := hs.ehi_lt a h0 (by omega)
        omega
  · intro a h0 h1
    rw [hwz] at h1
    have e1 := mark_lo hG hs (a := a + q) (by omega) (by omega)
    have e2 := mark_lo hG hs (a := a) (by omega) (by omega)
    have e3 := mark_hi hG hs (a := a + q) (by omega) (by omega)
    have e4 := mark_hi hG hs (a := a) (by omega) (by omega)
    unfold MarkedInner.TailUpper MarkedInner.dLo MarkedInner.dHi
    rw [hper, e1, e2, e3, e4, mark_rowShift]
    have ec : a + q = q + a := by ring
    rw [ec]
    by_cases hτ : a < τ
    · have := hs.elo_lt a h0 hτ
      by_cases hσ : σ ≤ a
      · have := hs.ehi_ge a hσ (by omega)
        omega
      · have := hs.ehi_lt a h0 (by omega)
        omega
    · have := hs.elo_ge a (by omega) (by omega)
      by_cases hσ : σ ≤ a
      · have := hs.ehi_ge a hσ (by omega)
        omega
      · have := hs.ehi_lt a h0 (by omega)
        omega

end SlotGeom

end SkewGluing
