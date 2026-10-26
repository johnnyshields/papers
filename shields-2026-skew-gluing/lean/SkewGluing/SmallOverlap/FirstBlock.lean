import SkewGluing.SmallOverlap.Singleton

/-!
# The first block of a composite

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (3), the
first window, read on the boundary words of `lem:gluing-coding`).

For a legal mark `ω` and a connected outer `D`, the boundary words `wordA`, `wordB` of `D ∘_ω E`
at the positions `1, …, q - 1` are the bits of `E` at the same positions
(`wordA_compose_first`, `wordB_compose_first`).

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

theorem diagRows_filter_content_le (X : Diagram) (b c : ℤ) (hc : c ≤ b) :
    diagRows (X.filter fun x => content x ≤ b) c = diagRows X c := by
  ext i
  rw [mem_diagRows, mem_diagRows, Finset.mem_filter]
  simp only [content, and_iff_left_iff_imp]
  intro _; omega

theorem diagLo_filter_content_le (X : Diagram) (b c : ℤ) (hc : c ≤ b) :
    diagLo (X.filter fun x => content x ≤ b) c = diagLo X c := by
  unfold diagLo; rw [diagRows_filter_content_le X b c hc]

theorem diagHi_filter_content_le (X : Diagram) (b c : ℤ) (hc : c ≤ b) :
    diagHi (X.filter fun x => content x ≤ b) c = diagHi X c := by
  unfold diagHi; rw [diagRows_filter_content_le X b c hc]

theorem mem_contents_filter_content_le {X : Diagram} {b c : ℤ} (hc : c ≤ b) (hX : c ∈ contents X) :
    c ∈ contents (X.filter fun x => content x ≤ b) := by
  rw [mem_contents_iff] at hX ⊢
  obtain ⟨i, hi⟩ := hX
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, by simp only [content]; omega⟩⟩

/-- **`lem:gluing-local` (3), first window, on the words.**  For `1 ≤ k ≤ q - 1` the bits of the
composite at the position `k` are the bits of `E` there. -/
theorem wordAB_compose_first {ω : MarkedInner} {D : Diagram} (hω : ω.IsLegal)
    (hD : IsConnectedSkew D) {k : ℤ} (h1 : 1 ≤ k) (h2 : k ≤ ω.period - 1) :
    wordA (ω.compose D) k = bitA ω.E (minContent ω.E + k) ∧
    wordB (ω.compose D) k = bitB ω.E (minContent ω.E + k) := by
  have hq := hω.period_pos
  have hmin := hω.minContent_compose hD
  have hwin := hω.compose_first_window hD
  have hEc : IsConnectedSkew ω.E := hω.1.1
  have hEs := isConnectedSkew_iff_diagonal.mp hEc
  have hsp := hω.1.span_eq
  have hw : (ω.width : ℤ) < ω.period := hω.2.2.1.2
  set t := ω.origin D (sw D) with ht
  have hct : content t = minContent D * ω.period := by
    rw [ht, content_origin, content_sw hD.2.1]
  set bnd := minContent ω.E + minContent D * ω.period + ω.period - 1 with hbnd
  set X := ω.E.filter (fun y => content y ≤ minContent ω.E + ω.period - 1) with hX
  have hcont : ∀ j : ℤ, 0 ≤ j → j ≤ ω.period - 1 → minContent ω.E + j ∈ contents X := by
    intro j hj0 hj1
    apply mem_contents_filter_content_le (by omega)
    rw [hEs.mem_contents_iff]
    have := span_eq_of_isConnectedSkew hEc
    have h0 : (0 : ℤ) ≤ ω.width := by positivity
    constructor <;> omega
  have hLo : ∀ j : ℤ, 0 ≤ j → j ≤ ω.period - 1 →
      diagLo (ω.compose D) (minContent ω.E + minContent D * ω.period + j) =
        diagLo ω.E (minContent ω.E + j) + t.1 := by
    intro j hj0 hj1
    have e1 : diagLo (ω.compose D) (minContent ω.E + minContent D * ω.period + j) =
        diagLo ((ω.compose D).filter fun x => content x ≤ bnd)
          (minContent ω.E + minContent D * ω.period + j) :=
      (diagLo_filter_content_le _ _ _ (by omega)).symm
    rw [e1, hwin]
    have := diagLo_translate t (minContent ω.E + j) (hcont j hj0 hj1)
    rw [hct] at this
    have e2 : minContent ω.E + minContent D * ω.period + j =
        minContent ω.E + j + minContent D * ω.period := by ring
    rw [e2, this, diagLo_filter_content_le _ _ _ (by omega)]
  have hHi : ∀ j : ℤ, 0 ≤ j → j ≤ ω.period - 1 →
      diagHi (ω.compose D) (minContent ω.E + minContent D * ω.period + j) =
        diagHi ω.E (minContent ω.E + j) + t.1 := by
    intro j hj0 hj1
    have e1 : diagHi (ω.compose D) (minContent ω.E + minContent D * ω.period + j) =
        diagHi ((ω.compose D).filter fun x => content x ≤ bnd)
          (minContent ω.E + minContent D * ω.period + j) :=
      (diagHi_filter_content_le _ _ _ (by omega)).symm
    rw [e1, hwin]
    have := diagHi_translate t (minContent ω.E + j) (hcont j hj0 hj1)
    rw [hct] at this
    have e2 : minContent ω.E + minContent D * ω.period + j =
        minContent ω.E + j + minContent D * ω.period := by ring
    rw [e2, this, diagHi_filter_content_le _ _ _ (by omega)]
  have e3 : ∀ j : ℤ, minContent (ω.compose D) + j =
      minContent ω.E + minContent D * ω.period + j := fun j => by rw [hmin]
  have e4 : minContent (ω.compose D) + k - 1 =
      minContent ω.E + minContent D * ω.period + (k - 1) := by rw [hmin]; ring
  have e5 : minContent ω.E + k - 1 = minContent ω.E + (k - 1) := by ring
  refine ⟨?_, ?_⟩
  · unfold wordA bitA
    rw [e4, e3, hLo (k - 1) (by omega) (by omega), hLo k (by omega) (by omega), e5]
    ring
  · unfold wordB bitB
    rw [e4, e3, hHi (k - 1) (by omega) (by omega), hHi k (by omega) (by omega), e5]
    ring

end SmallOverlap
end SkewGluing
