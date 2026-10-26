import SkewGluing.FoldSupplied.JWords

/-!
# The ordinary residue fold at width a multiple of `g`: the empty target

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`, the case `a = 0`).

From the facts `OrdWords` about the boundary words of an ordinary inner of period `r` and width
`v` with `g ∣ r`, `g ∣ v`, `g < r`, and the residue classes of the native lists constant off the
classes of the contacts, the words are in the form `EmptyWords`
(`SkewGluing.OrdinaryFold.Empty`) of a diagram of span `r + v`, which is an empty composition.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open OrdinaryDrift OrdinaryFold SmallOverlap

/-- The completed native column word `Y`: the value one at the returned position zero. -/
def natC (A : ℕ → ℤ) (k : ℕ) : ℤ := if k = 0 then 1 else A k

/-- The completed native row word `X`: the value zero at position zero and the contact `s`
inserted. -/
def natB (B : ℕ → ℤ) (s k : ℕ) : ℤ := if k = 0 then 0 else if k = s then 1 else B k

/-- The residue classes of `f` on `[0, r)` modulo `g` are constant, except the class of `ex`. -/
def ClassConst (f : ℕ → ℤ) (g r ex : ℕ) : Prop :=
  ∀ x y, x < r → y < r → x % g = y % g → x % g ≠ ex % g → f x = f y

theorem sum_abs_le {c : ℕ → ℤ} (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 1) (n : ℕ) :
    -(n : ℤ) ≤ ∑ i ∈ Finset.range n, c i ∧ ∑ i ∈ Finset.range n, c i ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := hc n
    push_cast
    constructor <;> linarith [ih.1, ih.2]

variable {A B : ℕ → ℤ} {r v s t g : ℕ}

/-- The generic bits at a position, when the exceptional residues are zero (width a multiple of
`g`): both words repeat the bits of the first block. -/
theorem OrdWords.generic_empty (h : OrdWords A B r v s t) (hg : 0 < g) (hgr : g ∣ r)
    (ht0 : t % g = 0) (hs0 : s % g = 0)
    (hC : ClassConst (natC A) g r t) (hB : ClassConst (natB B s) g r s) {x : ℕ}
    (hx1 : 1 ≤ x) (hxN : x < r + v) (hxg : x % g ≠ 0) :
    A x = A (x % g) ∧ B x = B (x % g) := by
  have hrg : r % g = 0 := Nat.mod_eq_zero_of_dvd hgr
  have hgr' : g ≤ r := Nat.le_of_dvd (by have := h.v_lt; have := h.v_pos; omega) hgr
  have hmodlt : x % g < g := Nat.mod_lt _ hg
  have key : ∀ y, 1 ≤ y → y < r → y % g ≠ 0 → A y = A (y % g) ∧ B y = B (y % g) := by
    intro y hy1 hyr hyg
    have hmod : y % g % g = y % g := Nat.mod_mod _ _
    have hyl : y % g < r := lt_of_lt_of_le (Nat.mod_lt _ hg) hgr'
    have e1 := hC y (y % g) hyr hyl hmod.symm (by rw [ht0]; exact hyg)
    have e2 := hB y (y % g) hyr hyl hmod.symm (by rw [hs0]; exact hyg)
    have hy0 : y % g ≠ 0 := hyg
    have hyne : y ≠ 0 := by omega
    unfold natC at e1
    unfold natB at e2
    simp only [hy0, hyne, if_false] at e1 e2
    refine ⟨e1, ?_⟩
    have hsy : y ≠ s := fun hh => hyg (by rw [hh]; exact hs0)
    have hsy' : y % g ≠ s := fun hh => hyg (by
      rw [← Nat.mod_mod y g, hh]; exact hs0)
    simp only [hsy, hsy', if_false] at e2
    exact e2
  by_cases hxr : x < r
  · exact key x hx1 hxr hxg
  · have hb1 : 1 ≤ x - r := by
      by_contra hcon
      have : x = r := by omega
      apply hxg; rw [this]; exact hrg
    have hbv : x - r < v := by omega
    have hbg : (x - r) % g ≠ 0 := by
      intro hh
      apply hxg
      have : x = r + (x - r) := by omega
      rw [this, Nat.add_mod, hrg, hh]; simp
    have hbr : x - r < r := by have := h.v_lt; omega
    have hbt : x - r ≠ t := fun hh => hbg (by rw [hh]; exact ht0)
    have hbs : x - r ≠ s := fun hh => hbg (by rw [hh]; exact hs0)
    have c1 := h.copyA (x - r) hb1 hbv
    have c2 := h.copyB (x - r) hb1 hbv
    simp only [hbt, hbs, if_false, sub_zero, add_zero] at c1 c2
    have e : r + (x - r) = x := by omega
    rw [e] at c1 c2
    have hk := key (x - r) hb1 hbr hbg
    have hmx : (x - r) % g = x % g := by
      have : x = r + (x - r) := by omega
      conv_rhs => rw [this, Nat.add_mod, hrg]
      simp
    rw [hmx] at hk
    exact ⟨c1.trans hk.1, c2.trans hk.2⟩


/-- **The words at width a multiple of `g`** (`ge:ordinary-fold`, `a = 0`).  The exceptional classes
of an ordinary inner of period `r` and width `v`, with `g ∣ r`, `g ∣ v`, `g < r`, are the residue
zero; the generic bits are those of the first block, their charge vanishes, and the words are in
the form `EmptyWords`. -/
theorem OrdWords.emptyWords (h : OrdWords A B r v s t) (hg2 : 2 ≤ g) (hgr : g ∣ r)
    (hgv : g ∣ v) (hglt : g < r) (hC : ClassConst (natC A) g r t)
    (hB : ClassConst (natB B s) g r s) :
    EmptyWords A B (fun ρ => if ρ = 0 then 0 else A ρ) (fun ρ => if ρ = 0 then 0 else B ρ)
      (r + v) g ((r + v) / g) := by
  have hg : 0 < g := by omega
  obtain ⟨R, hR⟩ := hgr
  obtain ⟨d, hd⟩ := hgv
  have hv1 := h.v_pos
  have hvr := h.v_lt
  have hR2 : 2 ≤ R := by
    by_contra hcon
    have : g * R ≤ g * 1 := Nat.mul_le_mul_left g (by omega)
    omega
  have hd1 : 1 ≤ d := by
    by_contra hcon
    have : d = 0 := by omega
    subst this; omega
  have hrg : r % g = 0 := Nat.mod_eq_zero_of_dvd ⟨R, hR⟩
  have hvg : v % g = 0 := Nat.mod_eq_zero_of_dvd ⟨d, hd⟩
  have hNM : r + v = g * (R + d) := by rw [hR, hd]; ring
  have hMdiv : (r + v) / g = R + d := by rw [hNM]; exact Nat.mul_div_cancel_left _ hg
  -- the exceptional residues are zero
  have ht0 : t % g = 0 := by
    by_contra hcon
    have e := hC v 0 hvr (by omega) (by rw [hvg]; simp) (by rw [hvg]; omega)
    unfold natC at e
    have hv0 : v ≠ 0 := by omega
    simp only [hv0, if_false, if_true] at e
    have := h.A_v
    omega
  have hs0 : s % g = 0 := by
    by_contra hcon
    have e := hB v 0 hvr (by omega) (by rw [hvg]; simp) (by rw [hvg]; omega)
    unfold natB at e
    have hv0 : v ≠ 0 := by omega
    simp only [hv0, if_false, if_true] at e
    have := h.B_v
    have hs := h.s_le
    by_cases hsv : v = s
    · simp only [hsv, if_true] at e; omega
    · simp only [hsv, if_false] at e
      have : s < v := by omega
      simp only [this, if_true] at *
      omega
  have gen : ∀ x, 1 ≤ x → x < r + v → x % g ≠ 0 → A x = A (x % g) ∧ B x = B (x % g) :=
    fun x hx1 hxN hxg => h.generic_empty hg ⟨R, hR⟩ ht0 hs0 hC hB hx1 hxN hxg
  -- block structure
  set κ : ℤ := ∑ m ∈ Finset.range (g - 1), (A (m + 1) - B (m + 1)) with hκ
  have hblock : ∀ j, j + 1 ≤ R + d →
      heightWord A B (j * g + (g - 1)) = heightWord A B (j * g) + κ := by
    intro j hj
    rw [SmallOverlap.heightWord_add]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    have hpos : j * g + m + 1 < r + v := by
      have h1 : (j + 1) * g ≤ (R + d) * g := Nat.mul_le_mul_right g hj
      have h2 : (j + 1) * g = j * g + g := by ring
      have h3 : r + v = (R + d) * g := by rw [hNM]; ring
      omega
    have hmod : (j * g + m + 1) % g = m + 1 := by
      have : j * g + m + 1 = (m + 1) + g * j := by ring
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hne : (j * g + m + 1) % g ≠ 0 := by rw [hmod]; omega
    have g1 := gen (j * g + m + 1) (by omega) hpos hne
    rw [hmod] at g1
    rw [g1.1, g1.2]
  set c : ℕ → ℤ := fun i => if 1 ≤ i * g ∧ i * g < r + v then A (i * g) - B (i * g) else 0 with hc
  have hcb : ∀ i, -1 ≤ c i ∧ c i ≤ 1 := by
    intro i
    simp only [hc]
    split_ifs with hh
    · have := h.words.bits (i * g) hh.1 hh.2
      omega
    · omega
  have hstep : ∀ j, j + 1 ≤ R + d - 1 + 0 → j + 1 < R + d →
      heightWord A B ((j + 1) * g) = heightWord A B (j * g) + κ + c (j + 1) := by
    intro j _ hj
    have e : (j + 1) * g = (j * g + (g - 1)) + 1 := by
      have : 1 ≤ g := hg
      ring_nf
      omega
    rw [e, heightWord_succ, hblock j (by omega)]
    have hpos : (j + 1) * g < r + v := by
      have : (j + 1) * g < (R + d) * g := Nat.mul_lt_mul_of_pos_right hj hg
      nlinarith
    have h1 : 1 ≤ (j + 1) * g := by nlinarith
    simp only [hc, h1, hpos, and_self, if_true]
    rw [← e]
  have hform : ∀ j, j < R + d →
      heightWord A B (j * g) = 1 + j * κ + ∑ i ∈ Finset.range j, c (i + 1) := by
    intro j
    induction j with
    | zero => intro _; simp [heightWord]
    | succ j ih =>
      intro hj
      rw [hstep j (by omega) hj, ih (by omega), Finset.sum_range_succ]
      push_cast
      ring
  -- the charge vanishes
  obtain ⟨R', hR'⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  have hr1 : r - 1 = R' * g + (g - 1) := by
    have : r = R' * g + g := by rw [hR, hR']; ring
    omega
  have hκ0 : κ = 0 := by
    have h1 := hform R' (by omega)
    have h2 := hblock R' (by omega)
    rw [← hr1] at h2
    rw [h.sing_r] at h2
    rw [h1] at h2
    have hb := sum_abs_le (c := fun i => c (i + 1)) (fun i => hcb (i + 1)) R'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hk1 : κ ≤ -1 := by omega
      have : ((R' : ℤ) + 1) * κ ≤ ((R' : ℤ) + 1) * (-1) :=
        mul_le_mul_of_nonneg_left hk1 (by positivity)
      linarith [hb.1, hb.2]
    · have hk1 : 1 ≤ κ := by omega
      have : ((R' : ℤ) + 1) * 1 ≤ ((R' : ℤ) + 1) * κ :=
        mul_le_mul_of_nonneg_left hk1 (by positivity)
      linarith [hb.1, hb.2]
  have hM2 : 2 ≤ (r + v) / g := by rw [hMdiv]; omega
  have hlastblk := hblock (R + d - 1) (by omega)
  have hNe : (R + d - 1) * g + (g - 1) = r + v - 1 := by
    have e : r + v = (R + d - 1) * g + g := by
      obtain ⟨M', hM'⟩ : ∃ M', R + d = M' + 1 := ⟨R + d - 1, by omega⟩
      have h1 : R + d - 1 = M' := by omega
      rw [h1, hNM, hM']; ring
    omega
  have hNeq : r + v = (r + v) / g * g := by rw [hMdiv, hNM]; ring
  refine ⟨hNeq, hM2, hg2, h.words, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro x hx1 hxN hxg
    have := (gen x hx1 hxN hxg).1
    simp only [hxg, ite_false]
    exact this
  · intro x hx1 hxN hxg
    have := (gen x hx1 hxN hxg).2
    simp only [hxg, ite_false]
    exact this
  · -- delta
    have e1 : ∑ j ∈ Finset.range g, (if j = 0 then (0 : ℤ) else A j) =
        ∑ m ∈ Finset.range (g - 1), A (m + 1) := by
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      rw [Finset.sum_range_succ']
      simp
    have e2 : ∑ j ∈ Finset.range g, (if j = 0 then (0 : ℤ) else B j) =
        ∑ m ∈ Finset.range (g - 1), B (m + 1) := by
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      rw [Finset.sum_range_succ']
      simp
    rw [e1, e2]
    have : ∑ m ∈ Finset.range (g - 1), (A (m + 1) - B (m + 1)) = 0 := hκ0
    rw [Finset.sum_sub_distrib] at this
    linarith
  · have := hblock 0 (by omega)
    simp only [zero_mul, zero_add] at this
    have h0 : heightWord A B 0 = 1 := by simp [heightWord]
    rw [this, h0, hκ0]; ring
  · have e : r + v - g = (R + d - 1) * g := by
      have := hNe
      have : 1 ≤ g := hg
      omega
    have h1 := hlastblk
    rw [hNe, h.words.last, hκ0] at h1
    rw [e]
    linarith

end FoldSupplied
end SkewGluing
