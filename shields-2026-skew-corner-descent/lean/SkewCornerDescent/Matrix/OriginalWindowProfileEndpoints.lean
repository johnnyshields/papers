/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowBounds
import SkewCornerDescent.Matrix.OriginalWindowExteriorContainment
import SkewGluing.ProfileStatistics

/-!
# Actual exterior endpoint producers for complete window profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Literal complete
parent-cell windows determine the true endpoint beta indices. All whole target blocks,
including empty pivots, lie in the transported window. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- A full literal profile window contains every target whole block, not only selected ones. -/
theorem originalLiteralWindow_full_profile_blocks {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo hi : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi) (a : OriginalBlocks Q) :
    originalBlockInWindow Q (lo + content v) (hi + content v) a := by
  have hb := (originalLiteralWindow_profile_bounds P Q lo hi v hwindow hlo hhi).1
  have hl := hb _ (Q.row_left_mem_cells (Fin.last m))
  have hh := hb _ (Q.row_right_mem_cells 0)
  simp only [content, add_sub_cancel_right, Q.zeta_last] at hl
  simp only [content, Fin.val_zero, Nat.cast_zero, add_zero, sub_zero] at hh
  exact originalBlockInWindow_mono Q 0 (Q.xi 0) (lo + content v) (hi + content v) a
    (originalBlockInWindow_full_profile Q a)
    (by dsimp only [content]; omega) (by dsimp only [content]; omega)

/-- The top source parent cell survives every nonempty upper-content end window. -/
theorem originalLiteralWindow_upper_top {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0)) :
    Q.xi 0 = P.xi 0 + content v := by
  have hmax : maxContent (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0) =
      P.xi 0 - 1 := by
    apply maxContent_eq_of
    · have hc : content (0, P.xi 0 - 1) = P.xi 0 - 1 := by simp only [content, sub_zero]
      have hp : (0, P.xi 0 - 1) ∈ P.cells := by
        simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using P.row_right_mem_cells 0
      rw [← hc]
      apply content_mem_contents
      exact Finset.mem_filter.mpr ⟨hp, by rw [hc]; omega⟩
    · intro k hk
      obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
      have hb := P.content_bounds_cells (Finset.mem_filter.mp hi).1
      simp only [content, add_sub_cancel_left] at hb
      omega
  have hne : (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0).Nonempty := by
    have hn := Q.isConnectedSkew_cells.2.1
    rw [hwindow] at hn
    obtain ⟨x, hx⟩ := hn
    exact ⟨x - v, mem_translate.mp hx⟩
  have he := congrArg maxContent hwindow
  rw [Q.maxContent_cells, maxContent_translate hne, hmax] at he
  omega

/-- The bottom source parent cell survives every nonempty lower-content end window. -/
theorem originalLiteralWindow_lower_shift {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi)) :
    content v = 0 := by
  have hmin : minContent (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi) = 0 := by
    apply minContent_eq_of
    · have hp := P.row_left_mem_cells (Fin.last n)
      have hc : content ((n : ℤ), P.zeta (Fin.last n) + n) = 0 := by
        simp only [content, P.zeta_last, zero_add, sub_self]
      have hp' : ((n : ℤ), P.zeta (Fin.last n) + n) ∈ P.cells := hp
      have hf : ((n : ℤ), P.zeta (Fin.last n) + n) ∈
          P.cells.filter (fun x => 0 ≤ content x ∧ content x < hi) :=
        Finset.mem_filter.mpr ⟨hp', by rw [hc]; omega⟩
      have h := content_mem_contents hf
      rwa [hc] at h
    · intro k hk
      obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
      have hb := (Finset.mem_filter.mp hi).2.1
      simpa only [content, add_sub_cancel_left] using hb
  have hne : (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi).Nonempty := by
    have hn := Q.isConnectedSkew_cells.2.1
    rw [hwindow] at hn
    obtain ⟨x, hx⟩ := hn
    exact ⟨x - v, mem_translate.mp hx⟩
  have he := congrArg minContent hwindow
  rw [Q.minContent_cells, minContent_translate hne, hmin, zero_add] at he
  exact he.symm

/-- A complete lower end window supplies the exact row offset and row-count bound.
The bottom parent cell survives; no profile-row embedding is assumed. -/
theorem originalLiteralWindow_lower_row_offset {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi)) :
    m ≤ n ∧ v.1 = (m : ℤ) - (n : ℤ) := by
  have rows {d : ℕ} (T : Profile d) (x : ℤ × ℤ) (hx : x ∈ T.cells) :
      0 ≤ x.1 ∧ x.1 ≤ (d : ℤ) := by
    obtain ⟨i, he, _⟩ := Profile.mem_cells.mp hx
    have hi := i.isLt
    change (i.val : ℤ) = x.1 at he
    omega
  have hQlast : ((m : ℤ), (m : ℤ)) ∈ Q.cells := by
    simpa only [Q.zeta_last, Fin.val_last, zero_add] using Q.row_left_mem_cells (Fin.last m)
  have hQfirst : (0, Q.zeta 0) ∈ Q.cells := by
    simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using Q.row_left_mem_cells 0
  have hlastP : ((m : ℤ), (m : ℤ)) - v ∈ P.cells := by
    rw [hwindow, mem_translate, Finset.mem_filter] at hQlast
    exact hQlast.1
  have hfirstP : (0, Q.zeta 0) - v ∈ P.cells := by
    rw [hwindow, mem_translate, Finset.mem_filter] at hQfirst
    exact hQfirst.1
  have hPlast : ((n : ℤ), (n : ℤ)) ∈
      P.cells.filter (fun x => 0 ≤ content x ∧ content x < hi) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simpa only [P.zeta_last, Fin.val_last, zero_add] using P.row_left_mem_cells (Fin.last n)
    · simpa only [content, sub_self] using And.intro (le_refl (0 : ℤ)) hhi
  have hlastQ : ((n : ℤ), (n : ℤ)) + v ∈ Q.cells := by
    rw [hwindow]
    apply mem_translate.mpr
    simpa only [add_sub_cancel_right] using hPlast
  have hbP := rows P _ hlastP
  have htP := rows P _ hfirstP
  have hbQ := rows Q _ hlastQ
  simp only [Prod.fst_sub, Prod.fst_add] at hbP htP hbQ
  constructor <;> omega

/-- The complete lower end window supplies every literal row fiber with its actual
suffix index. Endpoint clipping is retained, including ordinary boundary pivots. -/
theorem originalLiteralWindow_lower_row_fibers {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi)) :
    ∃ h : m ≤ n, ∀ j : Fin (m + 1), ∀ k : ℤ,
      (Q.zeta j ≤ k ∧ k < Q.xi j) ↔
        (P.zeta ⟨n - m + j.val, by have := j.isLt; omega⟩ ≤ k ∧
          k < P.xi ⟨n - m + j.val, by have := j.isLt; omega⟩ ∧ 0 ≤ k ∧ k < hi) := by
  obtain ⟨hn, hv⟩ := originalLiteralWindow_lower_row_offset P Q hi v hhi hwindow
  have hc := originalLiteralWindow_lower_shift P Q hi v hhi hwindow
  have hv2 : v.2 = v.1 := by dsimp only [content] at hc; omega
  refine ⟨hn, ?_⟩
  intro j k
  let i : Fin (n + 1) := ⟨n - m + j.val, by have := j.isLt; omega⟩
  have hrow : (j : ℤ) - v.1 = (i : ℤ) := by dsimp only [i]; omega
  have hp : ((j : ℤ), k + j) - v = ((i : ℤ), k + i) := by
    ext <;> dsimp only [Prod.fst_sub, Prod.snd_sub] <;> omega
  have hmem : (Q.zeta j ≤ k ∧ k < Q.xi j) ↔ ((j : ℤ), k + j) ∈ Q.cells := by
    rw [Profile.mem_cells_fin]
    omega
  rw [hmem, hwindow, mem_translate, hp, Finset.mem_filter, Profile.mem_cells_fin]
  change (P.zeta i + i ≤ k + i ∧ k + i < P.xi i + i) ∧
    (0 ≤ content ((i : ℤ), k + i) ∧ content ((i : ℤ), k + i) < hi) ↔
      (P.zeta i ≤ k ∧ k < P.xi i ∧ 0 ≤ k ∧ k < hi)
  dsimp only [content]
  omega

/-- Every starting beta endpoint of a complete lower end window is the unchanged
literal parent suffix endpoint; no endpoint correspondence is an input. -/
theorem originalLiteralWindow_lower_zeta {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi)) :
    ∃ h : m ≤ n, ∀ j : Fin (m + 1),
      Q.zeta j = P.zeta ⟨n - m + j.val, by have := j.isLt; omega⟩ := by
  obtain ⟨hn, hf⟩ := originalLiteralWindow_lower_row_fibers P Q hi v hhi hwindow
  refine ⟨hn, ?_⟩
  intro j
  let i : Fin (n + 1) := ⟨n - m + j.val, by have := j.isLt; omega⟩
  have hqpos : Q.zeta j < Q.xi j := by
    have hr := Q.xi_sub_zeta j
    have hp := Q.r_pos j
    omega
  have hp0 : P.zeta i < P.xi i := by
    have hr := P.xi_sub_zeta i
    have hp := P.r_pos i
    omega
  have hleft := (hf j (Q.zeta j)).mp ⟨le_refl _, hqpos⟩
  change P.zeta i ≤ Q.zeta j ∧ Q.zeta j < P.xi i ∧
    0 ≤ Q.zeta j ∧ Q.zeta j < hi at hleft
  have hright := (hf j (P.zeta i)).mpr
    ⟨le_refl _, hp0, P.zeta_nonneg i, hleft.1.trans_lt hleft.2.2.2⟩
  change Q.zeta j = P.zeta i
  exact le_antisymm hright.1 hleft.1

/-- The complete lower end window supplies every ending beta endpoint with its exact
content clipping. No row endpoint or clipping formula is carried as a hypothesis. -/
theorem originalLiteralWindow_lower_xi {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi)) :
    ∃ h : m ≤ n, ∀ j : Fin (m + 1),
      Q.xi j = min (P.xi ⟨n - m + j.val, by have := j.isLt; omega⟩) hi := by
  obtain ⟨hn, hf⟩ := originalLiteralWindow_lower_row_fibers P Q hi v hhi hwindow
  refine ⟨hn, ?_⟩
  intro j
  let i : Fin (n + 1) := ⟨n - m + j.val, by have := j.isLt; omega⟩
  have hqpos : Q.zeta j < Q.xi j := by
    have hr := Q.xi_sub_zeta j
    have hp := Q.r_pos j
    omega
  have hleft := (hf j (Q.zeta j)).mp ⟨le_refl _, hqpos⟩
  change P.zeta i ≤ Q.zeta j ∧ Q.zeta j < P.xi i ∧
    0 ≤ Q.zeta j ∧ Q.zeta j < hi at hleft
  have hb := (hf j (Q.xi j - 1)).mp ⟨by omega, by omega⟩
  change P.zeta i ≤ Q.xi j - 1 ∧ Q.xi j - 1 < P.xi i ∧
    0 ≤ Q.xi j - 1 ∧ Q.xi j - 1 < hi at hb
  have hu : Q.xi j ≤ min (P.xi i) hi := le_min (by omega) (by omega)
  have hmξ := min_le_left (P.xi i) hi
  have hmh := min_le_right (P.xi i) hi
  have hlow : Q.zeta j < min (P.xi i) hi := lt_min hleft.2.1 hleft.2.2.2
  have hp0 := P.zeta_nonneg i
  have hl := (hf j (min (P.xi i) hi - 1)).mpr (by
    change P.zeta i ≤ min (P.xi i) hi - 1 ∧
      min (P.xi i) hi - 1 < P.xi i ∧
      0 ≤ min (P.xi i) hi - 1 ∧ min (P.xi i) hi - 1 < hi
    omega)
  change Q.xi j = min (P.xi i) hi
  exact le_antisymm hu (by have := hl.2; omega)

/-- The complete lower window's interior ending endpoints are unclipped by strict
beta ordering alone. The clipped top row remains in the border. -/
theorem originalLiteralWindow_lower_core_xi {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi)) :
    ∃ h : m ≤ n, ∀ j : Fin m,
      Q.xi j.succ = P.xi ⟨n - m + j.val + 1, by have := j.isLt; omega⟩ := by
  obtain ⟨hn, hx⟩ := originalLiteralWindow_lower_xi P Q hi v hhi hwindow
  refine ⟨hn, ?_⟩
  intro j
  have htop := hx 0
  have hbound := min_le_right
    (P.xi ⟨n - m + (0 : Fin (m + 1)).val, by omega⟩) hi
  rw [← htop] at hbound
  have hstrict : Q.xi j.succ < Q.xi 0 := Q.xi_strictAnti (by
    change 0 < j.val + 1
    omega)
  have he := hx j.succ
  change Q.xi j.succ =
    min (P.xi ⟨n - m + j.val + 1, by have := j.isLt; omega⟩) hi at he
  simp only [min_def] at he
  split_ifs at he <;> omega

/-- The complete upper end window begins on the parent's first row and occupies
an actual row prefix. No row embedding or translation coordinate is assumed. -/
theorem originalLiteralWindow_upper_row_offset {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0)) :
    m ≤ n ∧ v.1 = 0 := by
  have rows {d : ℕ} (T : Profile d) (x : ℤ × ℤ) (hx : x ∈ T.cells) :
      0 ≤ x.1 ∧ x.1 ≤ (d : ℤ) := by
    obtain ⟨i, he, _⟩ := Profile.mem_cells.mp hx
    have hi := i.isLt
    change (i.val : ℤ) = x.1 at he
    omega
  have hfirstQ : (0, Q.zeta 0) ∈ Q.cells := by
    simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using Q.row_left_mem_cells 0
  have hlastQ : ((m : ℤ), (m : ℤ)) ∈ Q.cells := by
    simpa only [Q.zeta_last, Fin.val_last, zero_add] using Q.row_left_mem_cells (Fin.last m)
  have hfirstP : (0, Q.zeta 0) - v ∈ P.cells := by
    rw [hwindow, mem_translate, Finset.mem_filter] at hfirstQ
    exact hfirstQ.1
  have hlastP : ((m : ℤ), (m : ℤ)) - v ∈ P.cells := by
    rw [hwindow, mem_translate, Finset.mem_filter] at hlastQ
    exact hlastQ.1
  have htop : (0, P.xi 0 - 1) ∈
      P.cells.filter (fun x => lo ≤ content x ∧ content x < P.xi 0) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using P.row_right_mem_cells 0
    · simp only [content, sub_zero]
      omega
  have htopQ : (0, P.xi 0 - 1) + v ∈ Q.cells := by
    rw [hwindow]
    apply mem_translate.mpr
    simpa only [add_sub_cancel_right] using htop
  have hb0 := rows P _ hfirstP
  have hbn := rows P _ hlastP
  have ht0 := rows Q _ htopQ
  simp only [Prod.fst_sub, Prod.fst_add, zero_sub, zero_add] at hb0 hbn ht0
  constructor <;> omega

/-- Every upper-window row fiber is the literal parent prefix fiber, with the
actual content shift and lower clipping. -/
theorem originalLiteralWindow_upper_row_fibers {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0)) :
    ∃ h : m ≤ n, ∀ j : Fin (m + 1), ∀ k : ℤ,
      (Q.zeta j ≤ k + content v ∧ k + content v < Q.xi j) ↔
        (P.zeta ⟨j.val, by have := j.isLt; omega⟩ ≤ k ∧
          k < P.xi ⟨j.val, by have := j.isLt; omega⟩ ∧ lo ≤ k) := by
  obtain ⟨hn, hv⟩ := originalLiteralWindow_upper_row_offset P Q lo v hlo hwindow
  refine ⟨hn, ?_⟩
  intro j k
  let i : Fin (n + 1) := ⟨j.val, by have := j.isLt; omega⟩
  have hp : ((j : ℤ), k + content v + j) - v = ((i : ℤ), k + i) := by
    ext <;> dsimp only [Prod.fst_sub, Prod.snd_sub, content, i] <;> omega
  have hmem : (Q.zeta j ≤ k + content v ∧ k + content v < Q.xi j) ↔
      ((j : ℤ), k + content v + j) ∈ Q.cells := by
    rw [Profile.mem_cells_fin]
    omega
  rw [hmem, hwindow, mem_translate, hp, Finset.mem_filter, Profile.mem_cells_fin]
  have hb : P.xi i ≤ P.xi 0 := by
    apply P.xi_strictAnti.antitone
    exact Fin.zero_le i
  change (P.zeta i + i ≤ k + i ∧ k + i < P.xi i + i) ∧
    (lo ≤ content ((i : ℤ), k + i) ∧ content ((i : ℤ), k + i) < P.xi 0) ↔
      (P.zeta i ≤ k ∧ k < P.xi i ∧ lo ≤ k)
  dsimp only [content]
  omega

/-- The complete upper end window supplies its clipped starting endpoints and
unchanged ending endpoints, with the actual translation's content shift. -/
theorem originalLiteralWindow_upper_endpoints {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0)) :
    ∃ h : m ≤ n, ∀ j : Fin (m + 1),
      Q.zeta j = max (P.zeta ⟨j.val, by have := j.isLt; omega⟩) lo + content v ∧
      Q.xi j = P.xi ⟨j.val, by have := j.isLt; omega⟩ + content v := by
  obtain ⟨hn, hf⟩ := originalLiteralWindow_upper_row_fibers P Q lo v hlo hwindow
  refine ⟨hn, ?_⟩
  intro j
  let i : Fin (n + 1) := ⟨j.val, by have := j.isLt; omega⟩
  have hqpos : Q.zeta j < Q.xi j := by
    have hr := Q.xi_sub_zeta j
    have hp := Q.r_pos j
    omega
  have hleft := (hf j (Q.zeta j - content v)).mp ⟨by omega, by omega⟩
  change P.zeta i ≤ Q.zeta j - content v ∧
    Q.zeta j - content v < P.xi i ∧ lo ≤ Q.zeta j - content v at hleft
  have hbound : max (P.zeta i) lo < P.xi i :=
    (max_le hleft.1 hleft.2.2).trans_lt hleft.2.1
  have hstart := (hf j (max (P.zeta i) lo)).mpr
    ⟨le_max_left _ _, hbound, le_max_right _ _⟩
  have hright := (hf j (Q.xi j - content v - 1)).mp ⟨by omega, by omega⟩
  change P.zeta i ≤ Q.xi j - content v - 1 ∧
    Q.xi j - content v - 1 < P.xi i ∧ lo ≤ Q.xi j - content v - 1 at hright
  have hfinish := (hf j (P.xi i - 1)).mpr (by
    change P.zeta i ≤ P.xi i - 1 ∧ P.xi i - 1 < P.xi i ∧ lo ≤ P.xi i - 1
    have := le_max_left (P.zeta i) lo
    have := le_max_right (P.zeta i) lo
    omega)
  change Q.zeta j = max (P.zeta i) lo + content v ∧ Q.xi j = P.xi i + content v
  constructor
  · have := max_le hleft.1 hleft.2.2
    have := hstart.1
    omega
  · have := hfinish.2
    have := hright.2.1
    omega

/-- The complete upper window's interior starting endpoints are unclipped by
strict beta ordering alone. The clipped last row remains in the border. -/
theorem originalLiteralWindow_upper_core_zeta {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0)) :
    ∃ h : m ≤ n, ∀ j : Fin m,
      Q.zeta j.castSucc = P.zeta ⟨j.val, by have := j.isLt; omega⟩ + content v := by
  obtain ⟨hn, he⟩ := originalLiteralWindow_upper_endpoints P Q lo v hlo hwindow
  refine ⟨hn, ?_⟩
  intro j
  have hlast := (he (Fin.last m)).1
  have hbound := le_max_right (P.zeta ⟨m, by omega⟩) lo
  have hstrict : Q.zeta (Fin.last m) < Q.zeta j.castSucc := Q.zeta_strictAnti (by
    change j.val < m
    exact j.isLt)
  have hz := (he j.castSucc).1
  change Q.zeta j.castSucc =
    max (P.zeta ⟨j.val, by have := j.isLt; omega⟩) lo + content v at hz
  simp only [max_def] at hz
  split_ifs at hz <;> omega

/-- Rows omitted from a complete lower end window start at or beyond its content
cut. This is produced from literal cell equality, not from a supplied block shape. -/
theorem originalLiteralWindow_lower_prefix_bound {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi)) :
    ∀ i : Fin (n + 1), i.val < n - m → hi ≤ P.zeta i := by
  obtain ⟨hn, hv⟩ := originalLiteralWindow_lower_row_offset P Q hi v hhi hwindow
  intro i hirow
  by_contra hnot
  have hz : P.zeta i < hi := by omega
  have hx := P.row_left_mem_cells i
  have hc : content ((i : ℤ), P.zeta i + i) = P.zeta i := by dsimp [content]; omega
  have hfilter : ((i : ℤ), P.zeta i + i) ∈
      P.cells.filter (fun x => 0 ≤ content x ∧ content x < hi) := by
    exact Finset.mem_filter.mpr ⟨hx, by rw [hc]; exact ⟨P.zeta_nonneg i, hz⟩⟩
  have hQ : ((i : ℤ), P.zeta i + i) + v ∈ Q.cells := by
    rw [hwindow]
    apply mem_translate.mpr
    simpa only [add_sub_cancel_right] using hfilter
  obtain ⟨j, hrow, _⟩ := Profile.mem_cells.mp hQ
  change (j.val : ℤ) = (i.val : ℤ) + v.1 at hrow
  omega

/-- Rows omitted from a complete upper end window end at or below its content cut. -/
theorem originalLiteralWindow_upper_suffix_bound {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0)) :
    ∀ i : Fin (n + 1), m < i.val → P.xi i ≤ lo := by
  obtain ⟨hn, hv⟩ := originalLiteralWindow_upper_row_offset P Q lo v hlo hwindow
  intro i hirow
  by_contra hnot
  have hz : lo < P.xi i := by omega
  have hx : ((i : ℤ), P.xi i - 1 + i) ∈ P.cells := by
    convert P.row_right_mem_cells i using 1
    congr 1
    omega
  have hc : content ((i : ℤ), P.xi i - 1 + i) = P.xi i - 1 := by dsimp [content]; omega
  have hbound : P.xi i ≤ P.xi 0 := P.xi_strictAnti.antitone (Fin.zero_le i)
  have hfilter : ((i : ℤ), P.xi i - 1 + i) ∈
      P.cells.filter (fun x => lo ≤ content x ∧ content x < P.xi 0) := by
    exact Finset.mem_filter.mpr ⟨hx, by rw [hc]; constructor <;> omega⟩
  have hQ : ((i : ℤ), P.xi i - 1 + i) + v ∈ Q.cells := by
    rw [hwindow]
    apply mem_translate.mpr
    simpa only [add_sub_cancel_right] using hfilter
  obtain ⟨j, hrow, _⟩ := Profile.mem_cells.mp hQ
  have hj := j.isLt
  change (j.val : ℤ) = (i.val : ℤ) + v.1 at hrow
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
