import SkewGluing.Antitranspose
import SkewGluing.Local
import SkewGluing.Coding

/-!
# Boundary words of an antitransposed diagram

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`eq:gluing-gauge`, and "antitransposition changes the bit pair to `(1 - B, 1 - A)`, giving case
(b)"), in the form used by `prop:gluing-ordinary-fold` ("antitranspose the pair if necessary").

`ordFold_diagLo_antitranspose` and `ordFold_diagHi_antitranspose` give the extreme rows of the
diagonals of `AT(F)`, and `ordFold_wordA_antitranspose`, `ordFold_wordB_antitranspose` the boundary
words: `A_k(AT F) = 1 - B_k(F)`, `B_k(AT F) = 1 - A_k(F)`.  The antitransposed marked inner is
`MarkedInner.anti` of `SkewGluing.Antitranspose`.

**Differs from the paper's route.**  The paper obtains the case-(b) statements from case (a) by
the identity `eq:gluing-gauge`; here the antitransposition of the whole marked inner is used.

Sorry-free.
-/

namespace SkewGluing

theorem ordFold_diagLo_antitranspose {D : Diagram} {c : ℤ} (hc : c ∈ contents D) :
    diagLo (antitranspose D) c = -(diagHi D c) - c := by
  apply diagLo_eq_of
  · rw [mem_antitranspose']
    have := diagHi_mem hc
    convert this using 2 <;> simp [atVec, add_comm]
  · intro i hi
    rw [mem_antitranspose'] at hi
    have := le_diagHi (D := D) (k := c) hi (by simp)
    simp at this
    omega

theorem ordFold_diagHi_antitranspose {D : Diagram} {c : ℤ} (hc : c ∈ contents D) :
    diagHi (antitranspose D) c = -(diagLo D c) - c := by
  apply diagHi_eq_of
  · rw [mem_antitranspose']
    have := diagLo_mem hc
    convert this using 2 <;> simp [atVec, add_comm]
  · intro i hi
    rw [mem_antitranspose'] at hi
    have := diagLo_le (D := D) (k := c) hi (by simp)
    simp at this
    omega

theorem ordFold_wordA_antitranspose {F : Diagram} (hF : IsConnectedSkew F) {k : ℤ} (hk1 : 1 ≤ k)
    (hk2 : k < (span F : ℤ)) : wordA (antitranspose F) k = 1 - wordB F k := by
  have hsp := span_eq_of_isConnectedSkew hF
  have hc : ∀ {j : ℤ}, j ∈ contents F ↔ minContent F ≤ j ∧ j ≤ maxContent F :=
    fun {j} => (isConnectedSkew_iff_diagonal.mp hF).mem_contents_iff (k := j)
  unfold wordA wordB bitA bitB
  rw [minContent_antitranspose]
  rw [ordFold_diagLo_antitranspose (hc.mpr ⟨by omega, by omega⟩ : minContent F + k - 1 ∈ contents
      F),
    ordFold_diagLo_antitranspose (hc.mpr ⟨by omega, by omega⟩ : minContent F + k ∈ contents F)]
  ring

theorem ordFold_wordB_antitranspose {F : Diagram} (hF : IsConnectedSkew F) {k : ℤ} (hk1 : 1 ≤ k)
    (hk2 : k < (span F : ℤ)) : wordB (antitranspose F) k = 1 - wordA F k := by
  have hsp := span_eq_of_isConnectedSkew hF
  have hc : ∀ {j : ℤ}, j ∈ contents F ↔ minContent F ≤ j ∧ j ≤ maxContent F :=
    fun {j} => (isConnectedSkew_iff_diagonal.mp hF).mem_contents_iff (k := j)
  unfold wordA wordB bitA bitB
  rw [minContent_antitranspose]
  rw [ordFold_diagHi_antitranspose (hc.mpr ⟨by omega, by omega⟩ : minContent F + k - 1 ∈ contents
      F),
    ordFold_diagHi_antitranspose (hc.mpr ⟨by omega, by omega⟩ : minContent F + k ∈ contents F)]
  ring

end SkewGluing
