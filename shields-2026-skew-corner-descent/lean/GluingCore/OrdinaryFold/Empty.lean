/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/OrdinaryFold/Empty.lean`. -/
import GluingCore.OrdinaryFold.Realize
import GluingCore.OrdinaryDrift

/-!
# The fold at remainder zero: the empty root

Formalizes `shields-2026-skew-factor-gluing.tex`, «Two ordinary roots» (`prop:gluing-ordinary-fold`,
the case `w_g = 0`): the parent is an empty composition of the inner `G` formed by its first `g`
diagonals with a connected outer read at the multiples of `g`.

`EmptyWords` is the form of the boundary words of a diagram of span `N = M g`: generic except at
the multiples of `g`.  `EmptyWords.exists_root` builds the legal empty mark on `G`, the outer
`A^D_j = A_{jg}`, `B^D_j = B_{jg}`, and proves `F = D ∘_ω G` by comparing boundary words.

**Differs from the paper's route.**  The paper obtains the empty root by writing the supplied inner
as an empty composition and appending the outer with `lem:gluing-aligned`; here the parent words
are read directly.

Sorry-free.
-/

namespace GluingCore
namespace OrdinaryFold

open OrdinaryDrift

variable {A B A0 B0 : ℕ → ℤ} {N g M : ℕ}

theorem emptyMarkH_period {E : Diagram} (hE : IsConnectedSkew E) :
    (emptyMarkH E).period = (span E : ℤ) := by
  have hne := hE.2.1
  change content (vH E) = (span E : ℤ)
  unfold vH
  rw [content_add, MarkedInner.content_sub, content_ne hne, content_sw hne,
    span_eq_of_isConnectedSkew hE]
  simp [content]

/-- The form of the boundary words `(A, B)` of a diagram of span `N = M g` with generic bits `A⁰`,
`B⁰`: generic off the multiples of `g`, the generic bits at the residue zero agree, and the
singleton diagonals `g - 1`, `N - g`. -/
structure EmptyWords (A B A0 B0 : ℕ → ℤ) (N g M : ℕ) : Prop where
  N_eq : N = M * g
  M_ge : 2 ≤ M
  g_ge : 2 ≤ g
  words : WordData A B N
  genA : ∀ x, 1 ≤ x → x < N → x % g ≠ 0 → A x = A0 (x % g)
  genB : ∀ x, 1 ≤ x → x < N → x % g ≠ 0 → B x = B0 (x % g)
  delta : ∑ j ∈ Finset.range g, A0 j = ∑ j ∈ Finset.range g, B0 j
  rho : A0 0 = B0 0
  pinch_g : heightWord A B (g - 1) = 1
  pinch_Ng : heightWord A B (N - g) = 1

namespace EmptyWords

theorem height_outer (h : EmptyWords A B A0 B0 N g M) :
    ∀ j, j + 1 ≤ M → heightWord (outerWord A g 0) (outerWord B g 0) j =
      heightWord A B (j * g) := by
  have hN := h.N_eq
  have hM := h.M_ge
  have hg := h.g_ge
  intro j
  induction j with
  | zero =>
    intro _
    simp [heightWord]
  | succ j ih =>
    intro hj
    rw [heightWord_succ, ih (by omega)]
    have hx0 : (j * g) % g = 0 := Nat.mul_mod_left j g
    have hlt : j * g + g < N := by
      have : (j + 1) * g ≤ (M - 1) * g := Nat.mul_le_mul_right g (by omega)
      have h2 : (M - 1) * g + g = M * g := by
        have : M = (M - 1) + 1 := by omega
        conv_rhs => rw [this]
        ring
      nlinarith
    have := height_window_gen (A := A) (B := B) (A0 := A0) (B0 := B0) (N := N) (g := g)
      (wg := 0) (τ := 0) (σ := 0) (x0 := j * g) (by omega) (by omega) le_rfl le_rfl
      h.genA h.genB h.delta h.rho hx0 hlt
    have e1 : (j + 1) * g = j * g + g := by ring
    rw [e1, this]
    simp only [outerWord, Nat.add_zero, Nat.sub_zero]
    have e2 : (j + 1) * g = j * g + g := e1
    rw [e2]

theorem isBitData_outer (h : EmptyWords A B A0 B0 N g M) :
    IsBitData M (outerWord A g 0) (outerWord B g 0) := by
  have hN := h.N_eq
  have hM := h.M_ge
  have hg := h.g_ge
  have hlt : ∀ j, j + 1 ≤ M → j * g < N := by
    intro j hj
    have : (j + 1) * g ≤ M * g := Nat.mul_le_mul_right g hj
    nlinarith
  refine ⟨by omega, fun j hj1 hj2 => ?_, fun j hj => ?_, ?_⟩
  · have hjg : g ≤ j * g := Nat.le_mul_of_pos_left g (by omega)
    have := hlt j hj2
    constructor
    · exact (h.words.bits (j * g + 0) (by omega) (by omega)).1
    · exact (h.words.bits (j * g + 0) (by omega) (by omega)).2
  · rw [h.height_outer j (by omega)]
    exact h.words.pos _ (hlt j (by omega))
  · rw [h.height_outer (M - 1) (by omega)]
    have e : (M - 1) * g = N - g := by
      have : M = (M - 1) + 1 := by omega
      rw [hN]
      conv_rhs => rw [this]
      rw [add_mul, one_mul]
      omega
    rw [e]
    exact h.pinch_Ng

theorem isBitData_inner (h : EmptyWords A B A0 B0 N g M) : IsBitData g A B := by
  have hN := h.N_eq
  have hM := h.M_ge
  have hg := h.g_ge
  have hMg : g ≤ M * g := Nat.le_mul_of_pos_left g (by omega)
  refine ⟨by omega, fun k hk1 hk2 => h.words.bits k hk1 (by omega),
    fun k hk => h.words.pos k (by omega), ?_⟩
  exact h.pinch_g


/-- **The empty root** (`prop:gluing-ordinary-fold`, `w_g = 0`).  A connected skew diagram whose
boundary words are in the form `EmptyWords` is an empty composition `D ∘_ω G` of a connected outer
with a legal empty mark on the inner `G` formed by its first `g` diagonals. -/
theorem exists_root (h : EmptyWords A B A0 B0 N g M) {F : Diagram} (hF : IsConnectedSkew F)
    (hspF : span F = N) (hFA : ∀ k : ℕ, 1 ≤ k → k < N → wordA F k = A k)
    (hFB : ∀ k : ℕ, 1 ≤ k → k < N → wordB F k = B k) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period = g ∧ χ.ω.W = ∅ := by
  have hN := h.N_eq
  have hM2 := h.M_ge
  have hg2 := h.g_ge
  have hbdG := h.isBitData_inner
  set G := fromBits g A B with hGd
  have hGcs : IsConnectedSkew G := isConnectedSkew_fromBits hbdG
  have hspG : span G = g := span_fromBits hbdG
  set ω := emptyMarkH G with hω
  have hleg : ω.IsLegal := emptyMarkH_isLegal hGcs
  have hlegE : ω.IsLegalEmpty := ⟨hleg, rfl⟩
  have hper : ω.period = (g : ℤ) := by rw [hω, emptyMarkH_period hGcs, hspG]
  have hDbd := h.isBitData_outer
  set D := fromBits M (outerWord A g 0) (outerWord B g 0) with hDd
  have hDcs : IsConnectedSkew D := isConnectedSkew_fromBits hDbd
  have hm0 : minContent D = 0 := minContent_fromBits hDbd
  have hspD : span D = M := span_fromBits hDbd
  have hspan : (span (ω.compose D) : ℤ) = N := by
    rw [MarkedInner.span_compose hDcs hleg, hspD, hper, hN]
    have : ω.width = 0 := by
      simp [MarkedInner.width, hω, emptyMarkH, span, contents]
    rw [this]; push_cast; ring
  have hcsF' : IsConnectedSkew (ω.compose D) := hleg.isConnectedSkew_compose hDcs
  have hspN : span (ω.compose D) = N := by exact_mod_cast hspan
  have hmaxD : maxContent D = (M : ℤ) - 1 := maxContent_fromBits hDbd
  have hc := hlegE.classRows hDcs
  have hmin := hlegE.minContent_compose' hDcs
  have hw0 : ω.widthZ = 0 := hlegE.width_zero
  have hmE : minContent ω.E = 0 := minContent_fromBits hbdG
  have hlo : ∀ a : ℕ, a < g → ω.lo a = bitsLo A a := by
    intro a ha
    unfold MarkedInner.lo
    change diagLo G (minContent G + a) = bitsLo A a
    rw [minContent_fromBits hbdG, zero_add]
    exact diagLo_fromBits hbdG ha
  have hhi : ∀ a : ℕ, a < g → ω.hi a = bitsLo B a := by
    intro a ha
    unfold MarkedInner.hi
    change diagHi G (minContent G + a) = bitsLo B a
    rw [minContent_fromBits hbdG, zero_add]
    exact diagHi_fromBits hbdG ha
  have key : ∀ k : ℕ, 1 ≤ k → k < N → ∃ J a : ℕ, k = J * g + a ∧ a < g ∧ J ≤ M - 1 := by
    intro k hk1 hk2
    refine ⟨k / g, k % g, (Nat.div_add_mod' k g).symm, Nat.mod_lt _ (by omega), ?_⟩
    have : k / g < M := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    omega
  have hAk : ∀ k : ℕ, 1 ≤ k → k < N → wordA (ω.compose D) k = A k := by
    intro k hk1 hk2
    obtain ⟨J, a, hk, hag, hJ⟩ := key k hk1 hk2
    subst hk
    have hmod : (J * g + a) % g = a := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hag]
    have hpos : ((J : ℤ) - minContent D) * ω.period + a = ((J * g + a : ℕ) : ℤ) := by
      rw [hm0, hper]; push_cast; ring
    by_cases ha0 : a = 0
    · subst ha0
      have hJ1 : 1 ≤ J := by
        rcases Nat.eq_zero_or_pos J with h0 | h0
        · subst h0; simp at hk1
        · exact h0
      have hj := (hlegE.joining hDcs (j := J) (by exact_mod_cast hJ1)
        (by rw [hspD]; exact_mod_cast (by omega : J < M))).1
      have e : ((J : ℤ)) * ω.period = ((J * g + 0 : ℕ) : ℤ) := by rw [hper]; push_cast; ring
      rw [e] at hj
      rw [hj]
      unfold wordA
      rw [hm0]
      have := bitA_fromBits hDbd hJ1 (by omega : J < M)
      rw [hm0, zero_add] at this
      simp only [zero_add] at this ⊢
      rw [this]
      rfl
    · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a := by
        rw [hm0, hmaxD]
        left
        refine ⟨by omega, by omega⟩
      have h1 := hc.wordA_class hmin (a := a) (J := J) (by omega) (by rw [hper]; omega) hv
        (fun h0 => absurd h0 (by omega))
      rw [hpos] at h1
      rw [h1]
      unfold classBitLo
      simp only [show (a : ℤ) ≠ 0 by omega, ite_false]
      have hao := hlo (a - 1) (by omega)
      have hbo := hlo a hag
      have e1 : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ a)]; ring
      rw [e1, hao, hbo]
      have e2 := bitsLo_succ A (a - 1)
      have e3 : a - 1 + 1 = a := by omega
      rw [e3] at e2
      have g1 := h.genA a (by omega) (by
        have : g ≤ M * g := Nat.le_mul_of_pos_left g (by omega)
        omega) (by rw [Nat.mod_eq_of_lt hag]; omega)
      have g2 := h.genA (J * g + a) hk1 hk2 (by rw [hmod]; omega)
      rw [hmod] at g2
      rw [Nat.mod_eq_of_lt hag] at g1
      linarith
  have hBk : ∀ k : ℕ, 1 ≤ k → k < N → wordB (ω.compose D) k = B k := by
    intro k hk1 hk2
    obtain ⟨J, a, hk, hag, hJ⟩ := key k hk1 hk2
    subst hk
    have hmod : (J * g + a) % g = a := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hag]
    have hpos : ((J : ℤ) - minContent D) * ω.period + a = ((J * g + a : ℕ) : ℤ) := by
      rw [hm0, hper]; push_cast; ring
    by_cases ha0 : a = 0
    · subst ha0
      have hJ1 : 1 ≤ J := by
        rcases Nat.eq_zero_or_pos J with h0 | h0
        · subst h0; simp at hk1
        · exact h0
      have hj := (hlegE.joining hDcs (j := J) (by exact_mod_cast hJ1)
        (by rw [hspD]; exact_mod_cast (by omega : J < M))).2
      have e : ((J : ℤ)) * ω.period = ((J * g + 0 : ℕ) : ℤ) := by rw [hper]; push_cast; ring
      rw [e] at hj
      rw [hj]
      unfold wordB
      rw [hm0]
      have := bitB_fromBits hDbd hJ1 (by omega : J < M)
      rw [hm0, zero_add] at this
      simp only [zero_add] at this ⊢
      rw [this]
      rfl
    · have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a := by
        rw [hm0, hmaxD]
        left
        refine ⟨by omega, by omega⟩
      have h1 := hc.wordB_class hmin (a := a) (J := J) (by omega) (by rw [hper]; omega) hv
        (fun h0 => absurd h0 (by omega))
      rw [hpos] at h1
      rw [h1]
      unfold classBitHi
      simp only [show (a : ℤ) ≠ 0 by omega, ite_false]
      have hao := hhi (a - 1) (by omega)
      have hbo := hhi a hag
      have e1 : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ a)]; ring
      rw [e1, hao, hbo]
      have e2 := bitsLo_succ B (a - 1)
      have e3 : a - 1 + 1 = a := by omega
      rw [e3] at e2
      have g1 := h.genB a (by omega) (by
        have : g ≤ M * g := Nat.le_mul_of_pos_left g (by omega)
        omega) (by rw [Nat.mod_eq_of_lt hag]; omega)
      have g2 := h.genB (J * g + a) hk1 hk2 (by rw [hmod]; omega)
      rw [hmod] at g2
      rw [Nat.mod_eq_of_lt hag] at g1
      linarith
  obtain ⟨t, ht⟩ := eq_translate_of_bits hcsF' hF (by rw [hspN, hspF])
    (fun k hk1 hk2 => by
      have e1 := hAk k hk1 (by omega)
      have e2 := hFA k hk1 (by omega)
      unfold wordA at e1 e2
      rw [e1, e2])
    (fun k hk1 hk2 => by
      have e1 := hBk k hk1 (by omega)
      have e2 := hFB k hk1 (by omega)
      unfold wordB at e1 e2
      rw [e1, e2])
  refine ⟨⟨D, ω⟩, ⟨hDcs, ?_, ?_, hleg⟩, ⟨t, ht⟩, ?_, rfl⟩
  · change 2 ≤ D.card
    have h1 : span D ≤ D.card := Finset.card_image_le
    omega
  · change 2 ≤ G.card
    have h1 : span G ≤ G.card := Finset.card_image_le
    omega
  · have : ω.period = (g : ℤ) := hper
    exact this

end EmptyWords

end OrdinaryFold
end GluingCore
