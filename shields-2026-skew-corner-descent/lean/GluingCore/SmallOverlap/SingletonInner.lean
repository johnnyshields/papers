/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/SmallOverlap/SingletonInner.lean`. -/
import GluingCore.SmallOverlap.FirstBlock

/-!
# The singleton inner and its legal mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the singleton construction: the inner is read from bit words, its
two end copies are the extreme cells, and the marks are maximal and separated, their complements
are connected skew, and their marked hats are empty.

* `SingletonInnerData g a b`: bit data `a, b` of span `g + 1` whose second and last-but-one
  diagonals are singletons (`a 1 = b 1`, `heightWord a b (g - 1) = 1`).
* `singletonMark E cs`: the marked inner `(E, {sw E}, ne E - sw E, cs)`.
* `singletonMark_isLegal`: for `E = fromBits (g + 1) a b`, it is legal when the end bits
  `a 1`, `a g` are the ones of the attachment case (`CaseBits`).

Sorry-free.
-/

namespace GluingCore

open MarkedInner

/-- The marked inner whose two copies are the extreme cells of `E`. -/
def singletonMark (E : Diagram) (cs : AttachCase) : MarkedInner where
  E := E
  W := {sw E}
  v := ne E - sw E
  case := cs

namespace SmallOverlap

/-- The end bits of the inner in an attachment case: `l` is `0` for a horizontal and `1` for a
vertical lower attachment, `u` is `0` for a horizontal and `1` for a vertical upper attachment. -/
def CaseBits (cs : AttachCase) (l u : ℤ) : Prop :=
  match cs with
  | .a => l = 0 ∧ u = 0
  | .b => l = 1 ∧ u = 1
  | .c => l = 0 ∧ u = 1
  | .d => l = 1 ∧ u = 0

/-- Bit data of span `g + 1` whose diagonals `1` and `g - 1` are singletons. -/
structure SingletonInnerData (g : ℕ) (a b : ℕ → ℤ) : Prop where
  bits : IsBitData (g + 1) a b
  two_le : 2 ≤ g
  first : a 1 = b 1
  pen : heightWord a b (g - 1) = 1

variable {g : ℕ} {a b : ℕ → ℤ}

theorem SingletonInnerData.last (h : SingletonInnerData g a b) : a g = b g := by
  have h1 := h.bits.2.2.2
  have e : g + 1 - 1 = g - 1 + 1 := by have := h.two_le; omega
  rw [e, heightWord_succ, h.pen] at h1
  have e2 : g - 1 + 1 = g := by have := h.two_le; omega
  rw [e2] at h1
  omega

theorem SingletonInnerData.bit01 (h : SingletonInnerData g a b) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ g) : (a k = 0 ∨ a k = 1) ∧ (b k = 0 ∨ b k = 1) :=
  h.bits.2.1 k hk1 (by omega)

theorem SingletonInnerData.bitsLo_pen (h : SingletonInnerData g a b) :
    bitsLo a (g - 1) = bitsLo b (g - 1) := by
  have := bitsLo_add_heightWord a b (g - 1)
  rw [h.pen] at this
  omega

theorem SingletonInnerData.bitsLo_g (h : SingletonInnerData g a b) :
    bitsLo a g = bitsLo a (g - 1) - a g ∧ bitsLo b g = bitsLo b (g - 1) - b g := by
  have e : g = g - 1 + 1 := by have := h.two_le; omega
  constructor
  · conv_lhs => rw [e, bitsLo_succ]
    rw [← e]
  · conv_lhs => rw [e, bitsLo_succ]
    rw [← e]

theorem SingletonInnerData.bitsLo_g_eq (h : SingletonInnerData g a b) :
    bitsLo a g = bitsLo b g := by
  have := h.bitsLo_g
  have := h.bitsLo_pen
  have := h.last
  omega

theorem bitsLo_one (a : ℕ → ℤ) : bitsLo a 1 = - a 1 := by
  simp [bitsLo]

theorem SingletonInnerData.mem_diag0 (_h : SingletonInnerData g a b) {i j : ℤ}
    (hm : (i, j) ∈ fromBits (g + 1) a b) (hc : j - i = 0) : i = 0 := by
  obtain ⟨k, hk, hj, h1, h2⟩ := mem_fromBits'.mp hm
  have : k = 0 := by omega
  subst this
  simp [bitsLo] at h1 h2
  omega

theorem SingletonInnerData.mem_diagg (h : SingletonInnerData g a b) {i j : ℤ}
    (hm : (i, j) ∈ fromBits (g + 1) a b) (hc : j - i = g) : i = bitsLo a g := by
  obtain ⟨k, hk, hj, h1, h2⟩ := mem_fromBits'.mp hm
  have : k = g := by omega
  subst this
  have := h.bitsLo_g_eq
  omega

theorem SingletonInnerData.content_range (_h : SingletonInnerData g a b) {i j : ℤ}
    (hm : (i, j) ∈ fromBits (g + 1) a b) : 0 ≤ j - i ∧ j - i ≤ g := by
  obtain ⟨k, hk, hj, -, -⟩ := mem_fromBits'.mp hm
  omega

theorem SingletonInnerData.sw_eq (h : SingletonInnerData g a b) :
    sw (fromBits (g + 1) a b) = (0, 0) := sw_fromBits h.bits

theorem SingletonInnerData.ne_eq (h : SingletonInnerData g a b) :
    ne (fromBits (g + 1) a b) = (bitsLo a g, bitsLo a g + g) := by
  have hmax : maxContent (fromBits (g + 1) a b) = (g : ℤ) := by
    rw [maxContent_fromBits h.bits]; push_cast; ring
  have := diagLo_fromBits h.bits (n := g) (by omega)
  simp only [ne, hmax, this]

theorem SingletonInnerData.zero_mem (h : SingletonInnerData g a b) :
    ((0 : ℤ), (0 : ℤ)) ∈ fromBits (g + 1) a b := by
  have := sw_mem (D := fromBits (g + 1) a b) (isConnectedSkew_fromBits h.bits).2.1
  rwa [h.sw_eq] at this

theorem SingletonInnerData.ne_mem (h : SingletonInnerData g a b) :
    (bitsLo a g, bitsLo a g + g) ∈ fromBits (g + 1) a b := by
  have := GluingCore.ne_mem (D := fromBits (g + 1) a b) (isConnectedSkew_fromBits h.bits).2.1
  rwa [h.ne_eq] at this

theorem minContent_ge_of_forall {D : Diagram} (hne : D.Nonempty) {c : ℤ}
    (hc : ∀ x ∈ D, c ≤ content x) : c ≤ minContent D := by
  obtain ⟨x, hx, hxc⟩ := Finset.mem_image.mp (minContent_mem hne)
  rw [← hxc]; exact hc x hx

theorem maxContent_le_of_forall {D : Diagram} (hne : D.Nonempty) {c : ℤ}
    (hc : ∀ x ∈ D, content x ≤ c) : maxContent D ≤ c := by
  obtain ⟨x, hx, hxc⟩ := Finset.mem_image.mp (maxContent_mem hne)
  rw [← hxc]; exact hc x hx

theorem bitsLo_shift (a : ℕ → ℤ) (k : ℕ) :
    bitsLo (fun m => a (m + 1)) k = bitsLo a (k + 1) + a 1 := by
  induction k with
  | zero => simp [bitsLo]
  | succ k ih =>
    rw [bitsLo_succ, ih, bitsLo_succ a (k + 1)]
    ring

theorem heightWord_shift (a b : ℕ → ℤ) (h1 : a 1 = b 1) (k : ℕ) :
    heightWord (fun m => a (m + 1)) (fun m => b (m + 1)) k = heightWord a b (k + 1) := by
  induction k with
  | zero => simp [heightWord, h1]
  | succ k ih =>
    rw [heightWord_succ, ih, heightWord_succ a b (k + 1)]

theorem SingletonInnerData.shift (hh : SingletonInnerData g a b) :
    IsBitData g (fun m => a (m + 1)) (fun m => b (m + 1)) := by
  obtain ⟨hpos, hbits, hh', hl⟩ := hh.bits
  have hg := hh.two_le
  refine ⟨by omega, fun k hk1 hk2 => hbits (k + 1) (by omega) (by omega), fun k hk => ?_, ?_⟩
  · rw [heightWord_shift a b hh.first]
    exact hh' (k + 1) (by omega)
  · rw [heightWord_shift a b hh.first]
    have e : g - 1 + 1 = g := by omega
    rw [e]
    have e2 : g + 1 - 1 = g := by omega
    rw [e2] at hl
    exact hl

theorem SingletonInnerData.init (hh : SingletonInnerData g a b) : IsBitData g a b := by
  obtain ⟨hpos, hbits, hh', hl⟩ := hh.bits
  have hg := hh.two_le
  exact ⟨by omega, fun k hk1 hk2 => hbits k hk1 (by omega), fun k hk => hh' k (by omega), hh.pen⟩

/-! ### The legal singleton mark -/

section Legal

variable (h : SingletonInnerData g a b)
include h

omit h in
theorem SingletonInnerData.singletonMark_E (cs : AttachCase) :
    (singletonMark (fromBits (g + 1) a b) cs).E = fromBits (g + 1) a b := rfl

theorem SingletonInnerData.singletonMark_W (cs : AttachCase) :
    (singletonMark (fromBits (g + 1) a b) cs).W = {((0 : ℤ), (0 : ℤ))} := by
  simp only [singletonMark, h.sw_eq]

theorem SingletonInnerData.singletonMark_v (cs : AttachCase) :
    (singletonMark (fromBits (g + 1) a b) cs).v = (bitsLo a g, bitsLo a g + g) := by
  simp only [singletonMark, h.sw_eq, h.ne_eq]; ext <;> simp

theorem SingletonInnerData.singletonMark_upper (cs : AttachCase) :
    (singletonMark (fromBits (g + 1) a b) cs).upper = {(bitsLo a g, bitsLo a g + g)} := by
  simp only [MarkedInner.upper, h.singletonMark_W cs, h.singletonMark_v cs, translate,
    Finset.image_singleton]
  ext; simp

theorem SingletonInnerData.singletonMark_width (cs : AttachCase) :
    (singletonMark (fromBits (g + 1) a b) cs).width = 1 := by
  simp only [MarkedInner.width, h.singletonMark_W cs, span, contents, Finset.image_singleton,
    Finset.card_singleton]

theorem SingletonInnerData.singletonMark_period (cs : AttachCase) :
    (singletonMark (fromBits (g + 1) a b) cs).period = g := by
  simp only [MarkedInner.period, h.singletonMark_v cs, content]; ring

theorem SingletonInnerData.singletonMark_middle (cs : AttachCase) {x : ℤ × ℤ} :
    x ∈ (singletonMark (fromBits (g + 1) a b) cs).middle ↔
      x ∈ fromBits (g + 1) a b ∧ x ≠ (0, 0) ∧ x ≠ (bitsLo a g, bitsLo a g + g) := by
  simp only [MarkedInner.middle, Finset.mem_sdiff, Finset.mem_union, h.singletonMark_W cs,
    h.singletonMark_upper cs, Finset.mem_singleton, not_or]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

theorem SingletonInnerData.lowerH (cs : AttachCase) (hl : a 1 = 0) :
    (singletonMark (fromBits (g + 1) a b) cs).LowerH := by
  have hg := h.two_le
  have hx : ((0 : ℤ), (1 : ℤ)) ∈ (singletonMark (fromBits (g + 1) a b) cs).middle := by
    rw [h.singletonMark_middle cs]
    have := h.first
    refine ⟨?_, by simp, ?_⟩
    · rw [mem_fromBits']
      refine ⟨1, by omega, by simp, ?_, ?_⟩ <;> rw [bitsLo_one] <;> omega
    · intro hh
      simp only [Prod.mk.injEq] at hh
      omega
  refine ⟨(0, 1), hx, ?_, ?_⟩
  · apply le_antisymm
    · refine minContent_ge_of_forall ⟨_, hx⟩ fun y hy => ?_
      rw [h.singletonMark_middle cs] at hy
      obtain ⟨hy1, hy2, -⟩ := hy
      obtain ⟨y1, y2⟩ := y
      have hr := h.content_range hy1
      simp only [content] at hr ⊢
      by_contra hcon
      have : y2 - y1 = 0 := by omega
      have := h.mem_diag0 hy1 this
      apply hy2
      ext <;> simp <;> omega
    · exact minContent_le (content_mem_contents hx)
  · rw [singletonMark_W h]; simp

theorem SingletonInnerData.lowerV (cs : AttachCase) (hl : a 1 = 1) :
    (singletonMark (fromBits (g + 1) a b) cs).LowerV := by
  have hg := h.two_le
  have hx : ((-1 : ℤ), (0 : ℤ)) ∈ (singletonMark (fromBits (g + 1) a b) cs).middle := by
    rw [h.singletonMark_middle cs]
    have := h.first
    refine ⟨?_, by simp, ?_⟩
    · rw [mem_fromBits']
      refine ⟨1, by omega, by simp, ?_, ?_⟩ <;> rw [bitsLo_one] <;> omega
    · intro hh
      simp only [Prod.mk.injEq] at hh
      omega
  refine ⟨(-1, 0), hx, ?_, ?_⟩
  · apply le_antisymm
    · refine minContent_ge_of_forall ⟨_, hx⟩ fun y hy => ?_
      rw [h.singletonMark_middle cs] at hy
      obtain ⟨hy1, hy2, -⟩ := hy
      obtain ⟨y1, y2⟩ := y
      have hr := h.content_range hy1
      simp only [content] at hr ⊢
      by_contra hcon
      have : y2 - y1 = 0 := by omega
      have := h.mem_diag0 hy1 this
      apply hy2
      ext <;> simp <;> omega
    · exact minContent_le (content_mem_contents hx)
  · rw [singletonMark_W h]; simp

theorem SingletonInnerData.upperH (cs : AttachCase) (hu : a g = 0) :
    (singletonMark (fromBits (g + 1) a b) cs).UpperH := by
  have hg := h.two_le
  have hbg := h.bitsLo_g
  have hpen := h.bitsLo_pen
  have hx : (bitsLo a g, bitsLo a g + (g - 1 : ℤ)) ∈
      (singletonMark (fromBits (g + 1) a b) cs).middle := by
    rw [h.singletonMark_middle cs]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_fromBits']
      refine ⟨g - 1, by omega, by push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring, ?_, ?_⟩ <;>
        omega
    · intro hh
      simp only [Prod.mk.injEq] at hh
      omega
    · intro hh
      simp only [Prod.mk.injEq] at hh
      omega
  refine ⟨_, hx, ?_, ?_⟩
  · apply le_antisymm
    · exact le_maxContent (content_mem_contents hx)
    · refine maxContent_le_of_forall ⟨_, hx⟩ fun y hy => ?_
      rw [h.singletonMark_middle cs] at hy
      obtain ⟨hy1, hy2, hy3⟩ := hy
      obtain ⟨y1, y2⟩ := y
      have hr := h.content_range hy1
      simp only [content] at hr ⊢
      by_contra hcon
      have : y2 - y1 = g := by omega
      have := h.mem_diagg hy1 this
      apply hy3
      ext <;> simp <;> omega
  · rw [singletonMark_upper h]
    simp only [Finset.mem_singleton, Prod.mk.injEq, true_and]
    ring

theorem SingletonInnerData.upperV (cs : AttachCase) (hu : a g = 1) :
    (singletonMark (fromBits (g + 1) a b) cs).UpperV := by
  have hg := h.two_le
  have hbg := h.bitsLo_g
  have hpen := h.bitsLo_pen
  have hx : (bitsLo a g + 1, bitsLo a g + g) ∈
      (singletonMark (fromBits (g + 1) a b) cs).middle := by
    rw [h.singletonMark_middle cs]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_fromBits']
      refine ⟨g - 1, by omega, by push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring, ?_, ?_⟩ <;>
        omega
    · intro hh
      simp only [Prod.mk.injEq] at hh
      omega
    · intro hh
      simp only [Prod.mk.injEq] at hh
      omega
  refine ⟨_, hx, ?_, ?_⟩
  · apply le_antisymm
    · exact le_maxContent (content_mem_contents hx)
    · refine maxContent_le_of_forall ⟨_, hx⟩ fun y hy => ?_
      rw [h.singletonMark_middle cs] at hy
      obtain ⟨hy1, hy2, hy3⟩ := hy
      obtain ⟨y1, y2⟩ := y
      have hr := h.content_range hy1
      simp only [content] at hr ⊢
      by_contra hcon
      have : y2 - y1 = g := by omega
      have := h.mem_diagg hy1 this
      apply hy3
      ext <;> simp <;> omega
  · rw [singletonMark_upper h]
    simp

theorem SingletonInnerData.attach (cs : AttachCase) (hc : CaseBits cs (a 1) (a g)) :
    (singletonMark (fromBits (g + 1) a b) cs).AttachmentMatches := by
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · have h1' : cs = .a := h1
    subst h1'
    exact ⟨h.lowerH _ hc.1, h.upperH _ hc.2⟩
  · have h1' : cs = .b := h1
    subst h1'
    exact ⟨h.lowerV _ hc.1, h.upperV _ hc.2⟩
  · have h1' : cs = .c := h1
    subst h1'
    exact ⟨h.lowerH _ hc.1, h.upperV _ hc.2⟩
  · have h1' : cs = .d := h1
    subst h1'
    exact ⟨h.lowerV _ hc.1, h.upperH _ hc.2⟩

theorem SingletonInnerData.isNonemptyMark (cs : AttachCase) (hc : CaseBits cs (a 1) (a g)) :
    (singletonMark (fromBits (g + 1) a b) cs).IsNonemptyMark := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.attach cs hc⟩
  · rw [singletonMark_W h]; exact ⟨_, Finset.mem_singleton_self _⟩
  · rw [singletonMark_W h]; exact isConnectedSkew_singleton _
  · rw [singletonMark_W h, singletonMark_E]
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]; exact h.zero_mem
  · rw [singletonMark_upper h, singletonMark_E]
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]; exact h.ne_mem
  · change sw (fromBits (g + 1) a b) ∈ {sw (fromBits (g + 1) a b)}
    exact Finset.mem_singleton_self _
  · rw [singletonMark_upper h, singletonMark_E, h.ne_eq]
    exact Finset.mem_singleton_self _

theorem SingletonInnerData.isWellFormed (cs : AttachCase) (hc : CaseBits cs (a 1) (a g)) :
    (singletonMark (fromBits (g + 1) a b) cs).IsWellFormed :=
  ⟨isConnectedSkew_fromBits h.bits, Or.inr (h.isNonemptyMark cs hc)⟩

theorem SingletonInnerData.isMaximal (cs : AttachCase) :
    (singletonMark (fromBits (g + 1) a b) cs).IsMaximal := by
  intro W' hW' hlt hsk hcont x hx
  exfalso
  rw [Finset.mem_powerset] at hW'
  apply hlt.2
  intro y hy
  rw [singletonMark_W h] at hcont ⊢
  have hc : content y ∈ contents W' := content_mem_contents hy
  rw [hcont] at hc
  simp only [contents, Finset.image_singleton, Finset.mem_singleton] at hc
  have hyE := hW' hy
  obtain ⟨y1, y2⟩ := y
  simp only [content] at hc
  have := h.mem_diag0 hyE (by omega)
  rw [Finset.mem_singleton]
  ext <;> simp <;> omega

theorem SingletonInnerData.isNarrow (cs : AttachCase) :
    (singletonMark (fromBits (g + 1) a b) cs).IsNarrow := by
  unfold MarkedInner.IsNarrow
  rw [h.singletonMark_width cs, h.singletonMark_period cs]
  have := h.two_le
  constructor <;> omega

theorem SingletonInnerData.sdiff_sw :
    fromBits (g + 1) a b \ {((0 : ℤ), (0 : ℤ))} =
      translate ((-a 1 : ℤ), (-a 1 : ℤ) + 1)
        (fromBits g (fun m => a (m + 1)) (fun m => b (m + 1))) := by
  have hg := h.two_le
  ext ⟨i, j⟩
  rw [Finset.mem_sdiff, Finset.mem_singleton, mem_translate, mem_fromBits', mem_fromBits']
  constructor
  · rintro ⟨⟨k0, hk0, hj, h1, h2⟩, hne⟩
    have hk0' : k0 ≠ 0 := by
      rintro rfl
      apply hne
      have := h.mem_diag0 (mem_fromBits'.mpr ⟨0, hk0, hj, h1, h2⟩) (by simp at hj; omega)
      simp at hj
      ext <;> simp <;> omega
    obtain ⟨k, rfl⟩ : ∃ k, k0 = k + 1 := ⟨k0 - 1, by omega⟩
    refine ⟨k, by omega, by
      push_cast at hj ⊢; simp only [Prod.fst_sub, Prod.snd_sub]; omega, ?_, ?_⟩
    · rw [bitsLo_shift]; simp only [Prod.fst_sub]; omega
    · rw [bitsLo_shift]; simp only [Prod.fst_sub]; have := h.first; omega
  · rintro ⟨k, hk, hj, h1, h2⟩
    simp only [Prod.fst_sub, Prod.snd_sub] at hj h1 h2
    rw [bitsLo_shift] at h1 h2
    refine ⟨⟨k + 1, by omega, by push_cast; omega, by omega, by have := h.first; omega⟩, ?_⟩
    intro hh
    simp only [Prod.mk.injEq] at hh
    omega

theorem SingletonInnerData.sdiff_ne :
    fromBits (g + 1) a b \ {(bitsLo a g, bitsLo a g + g)} = fromBits g a b := by
  have hg := h.two_le
  ext ⟨i, j⟩
  rw [Finset.mem_sdiff, Finset.mem_singleton, mem_fromBits', mem_fromBits']
  constructor
  · rintro ⟨⟨k0, hk0, hj, h1, h2⟩, hne⟩
    have hk0' : k0 ≠ g := by
      intro hkg
      apply hne
      have := h.mem_diagg (mem_fromBits'.mpr ⟨k0, hk0, hj, h1, h2⟩) (by omega)
      ext <;> simp <;> omega
    exact ⟨k0, by omega, hj, h1, h2⟩
  · rintro ⟨k, hk, hj, h1, h2⟩
    refine ⟨⟨k, by omega, hj, h1, h2⟩, ?_⟩
    intro hh
    simp only [Prod.mk.injEq] at hh
    omega

theorem SingletonInnerData.removals (cs : AttachCase) :
    (singletonMark (fromBits (g + 1) a b) cs).RemovalsConnected := by
  constructor
  · change IsConnectedSkew (fromBits (g + 1) a b \ (singletonMark (fromBits (g + 1) a b) cs).W)
    rw [singletonMark_W h, SingletonInnerData.sdiff_sw h]
    exact isConnectedSkew_translate _ (isConnectedSkew_fromBits (SingletonInnerData.shift h))
  · change IsConnectedSkew (fromBits (g + 1) a b \
      (singletonMark (fromBits (g + 1) a b) cs).upper)
    rw [singletonMark_upper h, SingletonInnerData.sdiff_ne h]
    exact isConnectedSkew_fromBits (SingletonInnerData.init h)

/-- A cell of the periodic union on the content `m g` is the copy `m v` of the extreme cell. -/
theorem SingletonInnerData.periodic_content (cs : AttachCase) {z : ℤ × ℤ} {m : ℤ}
    (hz : z ∈ (singletonMark (fromBits (g + 1) a b) cs).periodicUnion)
    (hc : content z = m * g) : z = m • (bitsLo a g, bitsLo a g + g) := by
  have hg := h.two_le
  obtain ⟨k, hk⟩ := hz
  rw [singletonMark_v h] at hk
  obtain ⟨z1, z2⟩ := z
  simp only [singletonMark_E, Prod.smul_mk, smul_eq_mul, Prod.mk_sub_mk] at hk
  have hr := h.content_range hk
  simp only [content] at hc hr
  have hd : 0 ≤ (m - k) * g ∧ (m - k) * g ≤ g := by
    constructor <;> nlinarith
  have hmk : m - k = 0 ∨ m - k = 1 := by
    by_contra hcon
    rcases lt_or_gt_of_ne (show m - k ≠ 0 by omega) with hlt | hgt
    · nlinarith
    · have : 2 ≤ m - k := by omega
      nlinarith
  rcases hmk with h0 | h1
  · have hm : m = k := by omega
    subst hm
    have := h.mem_diag0 hk (by nlinarith)
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> nlinarith
  · have hm : m = k + 1 := by omega
    subst hm
    have := h.mem_diagg hk (by nlinarith)
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> nlinarith

theorem SingletonInnerData.noHatAdjacency (cs : AttachCase) :
    (singletonMark (fromBits (g + 1) a b) cs).NoHatAdjacency := by
  intro k m x hx y hy
  exfalso
  have hy' : y ∈ (singletonMark (fromBits (g + 1) a b) cs).hatMark
      (translate (m • (singletonMark (fromBits (g + 1) a b) cs).v)
        (singletonMark (fromBits (g + 1) a b) cs).W) := hy
  have hg := h.two_le
  rw [singletonMark_W h, singletonMark_v h] at hy'
  have hW : translate (m • (bitsLo a g, bitsLo a g + (g : ℤ))) ({((0 : ℤ), (0 : ℤ))} : Diagram) =
      {m • (bitsLo a g, bitsLo a g + (g : ℤ))} := by
    simp [translate]
  rw [hW] at hy'
  have hcm : ∀ z : ℤ × ℤ, content (z + eCell) = content z := content_eCell_add
  have hcv : content (m • (bitsLo a g, bitsLo a g + (g : ℤ))) = m * g := by
    simp [content]; ring
  have hee : ∀ z : ℤ × ℤ, z + eCell ≠ z := by
    intro z hz
    have := congrArg Prod.fst hz
    simp [eCell] at this
  unfold MarkedInner.hatMark at hy'
  rcases hy' with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
  · have hy2' : y + eCell = m • (bitsLo a g, bitsLo a g + (g : ℤ)) := by
      simpa using hy2
    have hyc : content y = m * g := by rw [← hcm, hy2', hcv]
    have := h.periodic_content cs hy1 hyc
    apply hee y
    rw [hy2', this]
  · have hy1' : y = m • (bitsLo a g, bitsLo a g + (g : ℤ)) := by simpa using hy1
    have hyc : content (y + eCell) = m * g := by rw [hcm, hy1', hcv]
    have := h.periodic_content cs hy2 hyc
    apply hee y
    rw [this, hy1']

/-- **The singleton mark is legal.**  For bit data `a, b` of span `g + 1` with singleton second
and last-but-one diagonals, the marked inner `(E, {sw E}, ne E - sw E, cs)` on
`E = fromBits (g + 1) a b` is legal as soon as the end bits `a 1`, `a g` are those of the
attachment case `cs`. -/
theorem SingletonInnerData.isLegal (cs : AttachCase) (hc : CaseBits cs (a 1) (a g)) :
    (singletonMark (fromBits (g + 1) a b) cs).IsLegal :=
  ⟨h.isWellFormed cs hc, h.isMaximal cs, h.isNarrow cs, h.removals cs, h.noHatAdjacency cs⟩

end Legal

end SmallOverlap
end GluingCore
