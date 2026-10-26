import SkewGluing.Aligned.OrdinaryEdge

/-!
# The lower copy `V ∩ (V - z)`

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, ordinary case, `b > 0`).

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

/-- The lower copy `Z = V ∩ (V - z)` of the lower mark on `V` with displacement `z`. -/
def lowerCopy (V : Diagram) (z : ℤ × ℤ) : Diagram := V.filter fun x => x + z ∈ V

/-- The candidate lower mark on `V`: lower copy `V ∩ (V - z)`, displacement `z`. -/
def muOf (V : Diagram) (z : ℤ × ℤ) (cs : AttachCase) : MarkedInner :=
  ⟨V, lowerCopy V z, z, cs⟩

/-- The northwest offset `ℓ_{J + α} - ℓ_J - θ` of `V - z` against `V` on the diagonal `J`
(`z = (θ, θ + α)`). -/
def gapLo (V : Diagram) (z : ℤ × ℤ) (J : ℤ) : ℤ := diagLo V (J + content z) - diagLo V J - z.1

/-- The southeast offset `h_{J + α} - h_J - θ`. -/
def gapHi (V : Diagram) (z : ℤ × ℤ) (J : ℤ) : ℤ := diagHi V (J + content z) - diagHi V J - z.1

theorem mem_lowerCopy {V : Diagram} {z x : ℤ × ℤ} : x ∈ lowerCopy V z ↔ x ∈ V ∧ x + z ∈ V := by
  simp [lowerCopy]

theorem lowerCopy_row {V : Diagram} {z : ℤ × ℤ} (hV : IsConnectedSkew V) {i J : ℤ} :
    (i, i + J) ∈ lowerCopy V z ↔
      (minContent V ≤ J ∧ J ≤ maxContent V ∧ diagLo V J ≤ i ∧ i ≤ diagHi V J) ∧
      (minContent V ≤ J + content z ∧ J + content z ≤ maxContent V ∧
        diagLo V (J + content z) ≤ i + z.1 ∧ i + z.1 ≤ diagHi V (J + content z)) := by
  rw [mem_lowerCopy, mem_D hV]
  have e : (i, i + J) + z = (i + z.1, (i + z.1) + (J + content z)) := by
    ext
    · simp
    · simp only [Prod.snd_add, content]; ring
  rw [e, mem_D hV]

/-- The hypotheses on a connected skew diagram `V` and a displacement `z` that are read off the
legality of a mark `η` on `V ∘_ω E` (the diagonals of `V` sampled at the private residue `w`):
the lower copy `Z` is nonempty on `b = N_V - α` diagonals, the tails of the middle are thin and
form an interval of the marked diagonals, and the two junction diagonals are singletons. -/
structure GlueData (V : Diagram) (z : ℤ × ℤ) : Prop where
  conn : IsConnectedSkew V
  alpha_lt : content z < (span V : ℤ)
  sep : (span V : ℤ) < 2 * content z
  nonempty : ∀ J, minContent V ≤ J → J ≤ maxContent V - content z →
    max (diagLo V J) (diagLo V (J + content z) - z.1) ≤
      min (diagHi V J) (diagHi V (J + content z) - z.1)
  thin_lo : ∀ J, minContent V ≤ J → J ≤ maxContent V - content z →
    gapLo V z J ≤ 1 ∧ -1 ≤ gapHi V z J ∧ ¬ (0 < gapLo V z J ∧ gapHi V z J < 0)
  thin_up : ∀ J, minContent V ≤ J → J ≤ maxContent V - content z →
    -1 ≤ gapLo V z J ∧ gapHi V z J ≤ 1 ∧ ¬ (gapLo V z J < 0 ∧ 0 < gapHi V z J)
  mono_lo : ∀ J J', minContent V ≤ J → J ≤ J' → J' ≤ maxContent V - content z →
    (0 < gapLo V z J ∨ gapHi V z J < 0) → (0 < gapLo V z J' ∨ gapHi V z J' < 0)
  mono_up : ∀ J J', minContent V ≤ J → J ≤ J' → J' ≤ maxContent V - content z →
    (gapLo V z J' < 0 ∨ 0 < gapHi V z J') → (gapLo V z J < 0 ∨ 0 < gapHi V z J)
  noncross_RL : ∀ J, minContent V ≤ J → J + 1 ≤ maxContent V - content z →
    gapHi V z J < 0 → gapLo V z (J + 1) ≤ 0
  noncross_LR : ∀ J, minContent V ≤ J → J + 1 ≤ maxContent V - content z →
    0 < gapLo V z J → 0 ≤ gapHi V z (J + 1)
  sing_b : diagLo V (maxContent V - content z + 1) = diagHi V (maxContent V - content z + 1)
  sing_a : diagLo V (minContent V + content z - 1) = diagHi V (minContent V + content z - 1)

namespace GlueData

variable {V : Diagram} {z : ℤ × ℤ}

theorem span_eq (G : GlueData V z) : (span V : ℤ) = maxContent V - minContent V + 1 :=
  span_eq_of_isConnectedSkew G.conn

theorem alpha_pos (G : GlueData V z) : 0 < content z := by
  have := G.sep
  have := G.span_eq
  have := minContent_le (maxContent_mem G.conn.2.1)
  omega

theorem le_max (G : GlueData V z) : minContent V ≤ maxContent V - content z := by
  have := G.alpha_lt
  have := G.span_eq
  omega

/-- The lower copy is a connected skew diagram. -/
theorem isConnectedSkew_lowerCopy (G : GlueData V z) : IsConnectedSkew (lowerCopy V z) := by
  have hV := G.conn
  have hα := G.alpha_pos
  have hle := G.le_max
  have hends := D_ends hV
  have hsh := isConnectedSkew_iff_diagonal.mp hV
  refine isConnectedSkew_of_rows _ (minContent V) (maxContent V - content z)
    (fun J => max (diagLo V J) (diagLo V (J + content z) - z.1))
    (fun J => min (diagHi V J) (diagHi V (J + content z) - z.1)) hle (fun i J => ?_)
    ?nonempty ?stepLo ?stepHi ?first ?last
  case nonempty => exact fun J h1 h2 => G.nonempty J h1 h2
  case first =>
    have := G.nonempty (minContent V) le_rfl G.le_max
    change max _ _ = min _ _
    omega
  case last =>
    have := G.nonempty (maxContent V - content z) G.le_max le_rfl
    change max _ _ = min _ _
    simp only [sub_add_cancel] at this ⊢
    omega
  · rw [lowerCopy_row hV]
    simp only [max_le_iff, le_min_iff]
    omega
  all_goals
    intro J h1 h2
    have b1 := D_bits hV (J := J) (by omega) (by omega)
    have b2 := D_bits hV (J := J + content z) (by omega) (by omega)
    have e : J - 1 + content z = J + content z - 1 := by ring
    rw [e]
    omega

/-- The first diagonal of the lower middle tail. -/
theorem exists_first_tail (G : GlueData V z) : ∃ J0, minContent V ≤ J0 ∧
    J0 ≤ maxContent V - content z + 1 ∧
    (∀ J, minContent V ≤ J → J < J0 → ¬ (0 < gapLo V z J ∨ gapHi V z J < 0)) ∧
    (∀ J, J0 ≤ J → J ≤ maxContent V - content z → (0 < gapLo V z J ∨ gapHi V z J < 0)) := by
  have hle := G.le_max
  by_cases hex : ∃ J, minContent V ≤ J ∧ J ≤ maxContent V - content z ∧
      (0 < gapLo V z J ∨ gapHi V z J < 0)
  · obtain ⟨J0, ⟨h1, h2, h3⟩, hmin⟩ := Int.exists_least_of_bdd
      (P := fun J => minContent V ≤ J ∧ J ≤ maxContent V - content z ∧
        (0 < gapLo V z J ∨ gapHi V z J < 0)) ⟨minContent V, fun J hJ => hJ.1⟩ hex
    refine ⟨J0, h1, by omega, fun J hJ1 hJ2 ht => ?_, fun J hJ1 hJ2 => ?_⟩
    · have := hmin J ⟨hJ1, by omega, ht⟩
      omega
    · exact G.mono_lo J0 J h1 hJ1 hJ2 h3
  · refine ⟨maxContent V - content z + 1, by omega, le_rfl, fun J hJ1 hJ2 ht => hex ⟨J, hJ1,
      by omega, ht⟩, fun J hJ1 hJ2 => by omega⟩

/-- The lower complement `V \ Z` is a connected skew diagram. -/
theorem isConnectedSkew_sdiff_lower (G : GlueData V z) : IsConnectedSkew (V \ lowerCopy V z) := by
  have hV := G.conn
  have hα := G.alpha_pos
  have hle := G.le_max
  have hsp := G.span_eq
  have hends := D_ends hV
  have hsh := isConnectedSkew_iff_diagonal.mp hV
  obtain ⟨J0, hJ0a, hJ0b, hno, hyes⟩ := G.exists_first_tail
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  have hlh : ∀ J, minContent V ≤ J → J ≤ maxContent V → diagLo V J ≤ diagHi V J := fun J h1 h2 =>
    diagLo_le_diagHi (hsh.mem_contents_iff.mpr ⟨h1, h2⟩)
  set bb := maxContent V - content z + 1 with hbb
  refine isConnectedSkew_of_rows _ J0 (maxContent V)
    (fun J => if bb ≤ J then diagLo V J else if 0 < gapLo V z J then diagLo V J
      else diagHi V J)
    (fun J => if bb ≤ J then diagHi V J else if 0 < gapLo V z J then diagLo V J
      else diagHi V J) (by omega) (fun i J => ?_) ?_ ?stepLo ?stepHi ?first ?last
  · rw [Finset.mem_sdiff, mem_D hV, lowerCopy_row hV]
    by_cases hJ : bb ≤ J
    · simp only [hJ, ite_true]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨by omega, h1.2.1, h1.2.2.1, h1.2.2.2⟩
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨⟨by omega, h2, h3, h4⟩, fun h => by omega⟩
    · simp only [hJ, ite_false]
      by_cases hJ1 : J0 ≤ J
      · have htl := hyes J hJ1 (by omega)
        by_cases hJ2 : minContent V ≤ J
        · have t1 := G.thin_lo J hJ2 (by omega)
          have e1 := hlh J hJ2 (by omega)
          unfold gapLo gapHi at htl t1
          by_cases hg : 0 < gapLo V z J
          · simp only [hg, ite_true]
            unfold gapLo at hg
            constructor
            · rintro ⟨h1, h2⟩
              have h3 : ¬ (diagLo V (J + content z) ≤ i + z.1 ∧
                  i + z.1 ≤ diagHi V (J + content z)) :=
                fun h => h2 ⟨h1, ⟨by omega, by omega, h.1, h.2⟩⟩ |>.elim
              omega
            · rintro ⟨h1, h2, h3, h4⟩
              refine ⟨⟨by omega, by omega, by omega, by omega⟩, fun h => ?_⟩
              omega
          · simp only [hg, ite_false]
            unfold gapLo at hg
            constructor
            · rintro ⟨h1, h2⟩
              omega
            · rintro ⟨h1, h2, h3, h4⟩
              refine ⟨⟨by omega, by omega, by omega, by omega⟩, fun h => ?_⟩
              omega
        · exact ⟨fun h => by omega, fun h => by omega⟩
      · have hJ2 : ¬ (J0 ≤ J) := hJ1
        constructor
        · rintro ⟨h1, h2⟩
          exfalso
          by_cases hJ3 : minContent V ≤ J
          · have hnt := hno J hJ3 (by omega)
            unfold gapLo gapHi at hnt
            exact h2 ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, by omega, by omega,
              by omega⟩
          · omega
        · rintro ⟨h1, _⟩; omega
  · intro J h1 h2
    by_cases hJ : bb ≤ J
    · simp only [hJ, ite_true]; exact hlh J (by omega) h2
    · simp only [hJ, ite_false]
      split_ifs <;> omega
  case first =>
    by_cases hJ : bb ≤ J0
    · have : J0 = bb := by omega
      simp only [hJ, ite_true]
      have sb := G.sing_b
      rw [← hbb] at sb
      rw [this]; exact sb
    · simp only [hJ, ite_false]
  case last =>
    have : bb ≤ maxContent V := by omega
    simp only [this, ite_true]
    exact hends.2
  all_goals
    intro J h1 h2
    have bJ := D_bits hV (J := J) (by omega) h2
    have hJ1 : minContent V ≤ J - 1 := by omega
    by_cases hJ : bb ≤ J - 1
    · have hJ' : bb ≤ J := by omega
      simp only [hJ, hJ', ite_true]
      omega
    · by_cases hJb : bb ≤ J
      · have hJe : J = bb := by omega
        have htl := hyes (J - 1) (by omega) (by omega)
        have sb := G.sing_b
        simp only [hJ, hJb, ite_true, ite_false]
        rw [← hbb] at sb
        subst hJe
        unfold gapLo gapHi at htl
        split_ifs <;> omega
      · simp only [hJ, hJb, ite_false]
        have htl1 := hyes (J - 1) (by omega) (by omega)
        have htl2 := hyes J (by omega) (by omega)
        have n1 := G.noncross_RL (J - 1) hJ1 (by omega)
        have n2 := G.noncross_LR (J - 1) hJ1 (by omega)
        have e : J - 1 + 1 = J := by ring
        rw [e] at n1 n2
        have t1 := G.thin_lo (J - 1) hJ1 (by omega)
        have t2 := G.thin_lo J (by omega) (by omega)
        simp only [gapLo, gapHi] at htl1 htl2 n1 n2 t1 t2 ⊢
        split_ifs <;> omega

end GlueData

end MarkedInner

end SkewGluing
