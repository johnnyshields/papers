/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/MixedFold/Extra.lean`. -/
import GluingCore.MixedPairs

/-!
# Private heights and the first interface relation of a case-(d) chart

Formalizes `shields-2026-skew-factor-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`), the inputs read from `eq:gluing-mixed-profile` and
`eq:gluing-interface`.

For a legal case-(d) mark of width `w`, period `q` and a connected outer of span at least two, the
parent has height one on the private diagonals `w` and `N - q` (`mixFold_extra_single`) and the
height increment from `w` to `q + w` is `A_{q+t} + A_{q+s} - 1` (`mixFold_extra_inter`); these are
packaged as `MixFoldExtra` for the words of any parent that has the chart.

Sorry-free.
-/

namespace GluingCore

/-- The private heights and the first interface relation of a case-(d) chart, on the bit words of
the parent (`N = r q + w` with `r ≥ 2`). -/
structure MixFoldExtra (A B : ℤ → ℤ) (N q w : ℕ) (s t : ℤ) : Prop where
  single_w : mixFold_ht A B w = 1
  single_Nq : mixFold_ht A B (N - q) = 1
  inter : 2 * q + w ≤ N →
    mixFold_ht A B (q + w) = mixFold_ht A B w + (A ((q : ℤ) + t) + A ((q : ℤ) + s) - 1)

theorem MixFoldExtra.of_agree {A B A' B' : ℤ → ℤ} {N q w : ℕ} {s t : ℤ}
    (h : MixFoldExtra A B N q w s t) (hq : 0 < q) (hs : 1 ≤ s) (hs' : s ≤ w)
    (ht : 0 ≤ t) (ht' : t < w)
    (hA : ∀ k : ℤ, 1 ≤ k → k ≤ (N : ℤ) - 1 → A k = A' k)
    (hB : ∀ k : ℤ, 1 ≤ k → k ≤ (N : ℤ) - 1 → B k = B' k) (hN : q + w ≤ N) :
    MixFoldExtra A' B' N q w s t := by
  have hc : ∀ n : ℕ, n ≤ N - 1 → mixFold_ht A B n = mixFold_ht A' B' n := fun n hn =>
    mixFold_ht_congr (fun k hk1 hk2 => ⟨hA k hk1 (by omega), hB k hk1 (by omega)⟩)
  refine ⟨?_, ?_, fun h2 => ?_⟩
  · rw [← hc w (by omega)]; exact h.single_w
  · rw [← hc (N - q) (by omega)]; exact h.single_Nq
  · have := h.inter h2
    rw [hc (q + w) (by omega), hc w (by omega)] at this
    rw [this, hA ((q : ℤ) + t) (by omega) (by omega), hA ((q : ℤ) + s) (by omega) (by omega)]

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem IsLegalNonempty.mixFold_extra (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hr : 2 ≤ span D) (hcd : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t) :
    MixFoldExtra (wordA (ω.compose D)) (wordB (ω.compose D)) (span (ω.compose D))
      ω.period.toNat ω.width s t := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hlt := h.phases_lt (Or.inr hcd) hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hsp := span_eq_of_isConnectedSkew hD
  have hmin := h.minContent_compose' hD
  have hN := h.span_compose_eq hD
  have hqz : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg (by omega)
  have hwz : (ω.width : ℤ) = ω.widthZ := rfl
  have hFc := h.1.isConnectedSkew_compose hD
  have hdD := D_ends hD
  have hsingle : height ω.E (minContent ω.E + ω.widthZ) = 1 := by
    have := h.lo_w_eq_hi_w
    unfold height; unfold lo hi at this; omega
  -- heights of the composite on private residue `w`, at the first and last class
  have hH : ∀ J : ℤ, minContent D ≤ J → J ≤ maxContent D →
      height (ω.compose D) (minContent (ω.compose D) + ((J - minContent D) * ω.period + ω.widthZ))
        = profM D J := by
    intro J h1 h2
    have e : minContent (ω.compose D) + ((J - minContent D) * ω.period + ω.widthZ) =
        minContent ω.E + (J * ω.period + ω.widthZ) := by rw [hmin]; ring
    rw [e]
    have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J ω.widthZ := Or.inl ⟨h1, h2⟩
    have := (h.mixed_profile hD hcd hph hlt (a := ω.widthZ) (by omega) (by omega) hv).2.1
      (le_refl _)
    rw [this, hsingle]; ring
  have hMend : ∀ J, J = minContent D ∨ J = maxContent D → profM D J = 1 := by
    intro J hJ
    unfold profM
    rcases hJ with rfl | rfl
    · simp only [hmM, le_refl, and_self, ite_true]; rw [hdD.1]; ring
    · simp only [hmM, le_refl, and_self, ite_true]; rw [hdD.2]; ring
  have hpos : (ω.period.toNat : ℤ) = ω.period := hqz
  have hn1 : ((ω.period.toNat * 0 + ω.width : ℕ) : ℤ) = ω.widthZ := by simp [hwz]
  refine ⟨?_, ?_, fun h2 => ?_⟩
  · have := hH (minContent D) (le_refl _) hmM
    rw [mixFold_ht_eq_height hFc (n := ω.width) (by
        have := mul_le_mul_of_nonneg_right (show 1 ≤ maxContent D - minContent D + 1 by omega)
          (show 0 ≤ ω.period by omega)
        omega)]
    have e : (minContent (ω.compose D) + ((ω.width : ℕ) : ℤ)) =
        minContent (ω.compose D) + ((minContent D - minContent D) * ω.period + ω.widthZ) := by
      simp [hwz]
    rw [e, this]; exact hMend _ (Or.inl rfl)
  · have hr1 : 1 ≤ maxContent D - minContent D := by omega
    have hn : ω.period.toNat ≤ span (ω.compose D) := by
      have := mul_le_mul_of_nonneg_right (show 1 ≤ maxContent D - minContent D + 1 by omega)
        (show 0 ≤ ω.period by omega)
      omega
    have hn' : span (ω.compose D) - ω.period.toNat < span (ω.compose D) := by
      have : 0 < ω.period.toNat := by omega
      omega
    rw [mixFold_ht_eq_height hFc hn']
    have e : minContent (ω.compose D) + ((span (ω.compose D) - ω.period.toNat : ℕ) : ℤ) =
        minContent (ω.compose D) +
          ((maxContent D - minContent D) * ω.period + ω.widthZ) := by
      have : ((span (ω.compose D) - ω.period.toNat : ℕ) : ℤ) =
          (span (ω.compose D) : ℤ) - ω.period := by omega
      rw [this, hN]; ring
    rw [e, hH (maxContent D) hmM (le_refl _)]
    exact hMend _ (Or.inr rfl)
  · -- the first interface relation
    have hr2 : 2 ≤ maxContent D - minContent D + 1 := by omega
    have hn1 : ω.period.toNat + ω.width < span (ω.compose D) := by
      have := mul_le_mul_of_nonneg_right hr2 (show 0 ≤ ω.period by omega)
      omega
    have hn0 : ω.width < span (ω.compose D) := by omega
    rw [mixFold_ht_eq_height hFc hn1, mixFold_ht_eq_height hFc hn0]
    have e1 : minContent (ω.compose D) + ((ω.period.toNat + ω.width : ℕ) : ℤ) =
        minContent (ω.compose D) + (((minContent D + 1) - minContent D) * ω.period + ω.widthZ) := by
      push_cast; rw [hqz, hwz]; ring
    have e0 : minContent (ω.compose D) + ((ω.width : ℕ) : ℤ) =
        minContent (ω.compose D) + ((minContent D - minContent D) * ω.period + ω.widthZ) := by
      rw [hwz]; ring
    rw [e1, e0, hH (minContent D + 1) (by omega) (by omega), hH (minContent D) (le_refl _) hmM]
    have hi := h.interface_d hD hcd hph (j := 1) (le_refl _) (by omega)
    have hA : wordA (ω.compose D) (((ω.period.toNat : ℕ) : ℤ) + t) = wordA D 1 := by
      rw [hqz, ← one_mul ω.period]; exact hi.1
    have hB : wordA (ω.compose D) (((ω.period.toNat : ℕ) : ℤ) + s) = 1 - wordB D 1 := by
      rw [hqz, ← one_mul ω.period]; exact hi.2
    rw [hA, hB]
    have hb := D_bits hD (J := minContent D + 1) (by omega) (by omega)
    unfold profM wordA wordB bitA bitB
    have e2 : minContent D + 1 - 1 = minContent D := by ring
    have e3 : minContent D + (1 : ℤ) - 1 = minContent D := by ring
    simp only [hmM, show minContent D + 1 ≤ maxContent D by omega, le_refl, and_self, ite_true,
      show minContent D ≤ minContent D + 1 by omega, e2]
    ring

end MarkedInner

end GluingCore
