import SkewGluing.FoldSupplied.Lift
import SkewGluing.OrdinaryFold
import SkewGluing.AntitransposeMixed
import SkewGluing.Lines.Mates

/-!
# Transport of a fold back along antitransposition

Formalizes `shields-2026-skew-gluing.tex`, «Two ordinary roots» (`prop:gluing-ordinary-fold`,
"physically antitranspose the whole comparison", "undo the initial physical antitranspose"):
if the comparison `AT(F)` of the antitransposed charts has a lifted fold chart over a supplied
inner `AT(E)`, then `F` has one over `E` with the same outer `X`.

* `FoldSupplied.emptyAt`: the chart with the outer antitransposed and the empty mark read
  horizontally, which is how an antitransposed empty-marked chart is presented again as a legal one
  (`eq:gluing-gauge`);
* `FoldSupplied.ordinary_transport`: the transport.  With a nonempty copy the chart and its fold
  are antitransposed with the same outer and the same gauge; with an empty copy the outer is
  antitransposed, which moves the gauge `γ` to `AT ∘ γ`, and the descended mark is replaced by its
  antitransposition (a nonempty mark) or by the horizontal empty mark (an empty one).

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open MarkedInner

theorem anti_translate' (u : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translate u).anti = ω.anti.translate (atVec u) := by
  unfold MarkedInner.anti MarkedInner.translate
  simp [antitranspose_translate]

/-- Antitransposing a legal chart (any attachment case) antitransposes what it presents. -/
theorem at_chartOf {χ : Chart} {G : Diagram} (h : χ.IsProperLegal) (hG : χ.IsChartOf G) :
    χ.at.IsChartOf (antitranspose G) := by
  obtain ⟨t, rfl⟩ := hG
  refine ⟨atVec t, ?_⟩
  have e : χ.at.parent = antitranspose χ.parent :=
    (MarkedInner.antitranspose_compose_of_isLegal h.2.2.2 h.1).symm
  rw [e, ← antitranspose_translate]

/-- The chart with the outer antitransposed and the empty mark on the antitransposed inner. -/
def emptyAt (χ : Chart) : Chart := ⟨antitranspose χ.D, emptyMarkH (antitranspose χ.ω.E)⟩

theorem emptyAt_spec {χ : Chart} {G : Diagram} (h : χ.IsProperLegal) (hW : χ.ω.W = ∅)
    (hG : χ.IsChartOf (antitranspose G)) :
    (emptyAt χ).IsProperLegal ∧ (emptyAt χ).IsChartOf G ∧ (emptyAt χ).period = χ.period := by
  have hω := h.eq_emptyMarkH hW
  obtain ⟨hD, hc, hE, hleg⟩ := h
  have hEcs : IsConnectedSkew χ.ω.E := hleg.1.1
  have hEcs' := isConnectedSkew_antitranspose hEcs
  have hDne := hD.2.1
  have hat0 : (emptyMarkH χ.ω.E).anti = χ.ω.anti := by rw [← hω]
  have hat : emptyMarkV (antitranspose χ.ω.E) = χ.ω.anti := (emptyMarkH_anti hEcs).symm.trans hat0
  refine ⟨⟨isConnectedSkew_antitranspose hD, ?_, ?_, emptyMarkH_isLegal hEcs'⟩, ?_, ?_⟩
  · change 2 ≤ (antitranspose χ.D).card
    rw [card_antitranspose]; exact hc
  · change 2 ≤ (antitranspose χ.ω.E).card
    rw [card_antitranspose]; exact hE
  · obtain ⟨t, ht⟩ := hG
    refine ⟨atVec t, ?_⟩
    have e1 : (emptyMarkH (antitranspose χ.ω.E)).compose (antitranspose χ.D) =
        antitranspose χ.parent := by
      rw [compose_emptyMarks_antitranspose (antitranspose_nonempty_iff.mpr hDne),
        antitranspose_antitranspose, hat]
      exact (MarkedInner.antitranspose_compose_of_isLegal hleg hD).symm
    have h2 := congrArg antitranspose ht
    rw [antitranspose_antitranspose, antitranspose_translate] at h2
    change G = translate (atVec t) ((emptyMarkH (antitranspose χ.ω.E)).compose
      (antitranspose χ.D))
    rw [e1]
    exact h2
  · change (emptyMarkH (antitranspose χ.ω.E)).period = χ.ω.period
    rw [OrdinaryFold.emptyMarkH_period hEcs', span_antitranspose]
    have : χ.ω.period = (emptyMarkH χ.ω.E).period := by rw [← hω]
    rw [this, OrdinaryFold.emptyMarkH_period hEcs]

theorem vH_antitranspose {E : Diagram} (hE : IsConnectedSkew E) :
    vH (antitranspose E) = atVec (vH E) + eCell := by
  have hv : atVec (vH E) = vV (antitranspose E) := by
    unfold vH vV
    rw [sw_antitranspose hE, ne_antitranspose hE]
    ext <;> simp [atVec] <;> ring
  rw [vH_eq_vV_add_eCell, hv]

theorem ordinary_transport {E F X : Diagram} {χ'' ψ : Chart} {μ : MarkedInner}
    {γ : Diagram → Diagram} {u : ℤ × ℤ} (hX : IsConnectedSkew X)
    (hψ : ψ.IsProperLegal) (hψE : ψ.IsChartOf (antitranspose E))
    (hχ : χ''.IsProperLegal) (hχF : χ''.IsChartOf (antitranspose F))
    (hω : χ''.ω = ψ.ω.translate u) (hμ : μ.IsLegal) (hμE : μ.E = ψ.D)
    (hγ : γ = id ∨ (γ = antitranspose ∧ μ.W = ∅)) (hD : χ''.D = μ.compose (γ X)) :
    ∃ (χ' ψ' : Chart) (μ' : MarkedInner) (γ' : Diagram → Diagram) (u' : ℤ × ℤ),
      ψ'.IsProperLegal ∧ ψ'.IsChartOf E ∧ ψ'.period = ψ.period ∧
      χ'.IsProperLegal ∧ χ'.IsChartOf F ∧ χ'.ω = ψ'.ω.translate u' ∧ χ'.period = χ''.period ∧
      μ'.IsLegal ∧ μ'.E = ψ'.D ∧ (γ' = id ∨ (γ' = antitranspose ∧ μ'.W = ∅)) ∧
      χ'.D = μ'.compose (γ' X) := by
  have hγX : IsConnectedSkew (γ X) := by
    rcases hγ with h | ⟨h, -⟩
    · rw [h]; exact hX
    · rw [h]; exact isConnectedSkew_antitranspose hX
  have hWtr : χ''.ω.W = SkewGluing.translate u ψ.ω.W := by rw [hω]; rfl
  by_cases hWψ : ψ.ω.W.Nonempty
  · have hWχ : χ''.ω.W.Nonempty := by rw [hWtr]; exact hWψ.image _
    refine ⟨χ''.at, ψ.at, μ, γ, atVec u, hψ.at hWψ, ?_, Chart.at_period ψ, hχ.at hWχ, ?_, ?_,
      Chart.at_period χ'', hμ, hμE, hγ, hD⟩
    · have := at_chartOf hψ hψE
      rwa [antitranspose_antitranspose] at this
    · have := at_chartOf hχ hχF
      rwa [antitranspose_antitranspose] at this
    · change χ''.ω.anti = ψ.ω.anti.translate (atVec u)
      rw [hω, anti_translate']
  · have hWψ' : ψ.ω.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hWψ
    have hWχ : χ''.ω.W = ∅ := by rw [hWtr, hWψ']; simp [SkewGluing.translate]
    obtain ⟨p1, p2, p3⟩ := emptyAt_spec hψ hWψ' hψE
    obtain ⟨q1, q2, q3⟩ := emptyAt_spec hχ hWχ hχF
    have hmk1 : ψ.ω = emptyMarkH ψ.ω.E := hψ.eq_emptyMarkH hWψ'
    have hmk2 : χ''.ω = emptyMarkH χ''.ω.E := hχ.eq_emptyMarkH hWχ
    have hEq : χ''.ω.E = SkewGluing.translate u ψ.ω.E := by rw [hω]; rfl
    have hvv : χ''.ω.v = ψ.ω.v := by rw [hω]; rfl
    have hv : vH χ''.ω.E = vH ψ.ω.E :=
      (congrArg MarkedInner.v hmk2).symm.trans (hvv.trans (congrArg MarkedInner.v hmk1))
    have hEψ : IsConnectedSkew ψ.ω.E := hψ.2.2.2.1.1
    have hEχ : IsConnectedSkew χ''.ω.E := hχ.2.2.2.1.1
    have hv' : vH (antitranspose χ''.ω.E) = vH (antitranspose ψ.ω.E) := by
      rw [vH_antitranspose hEχ, vH_antitranspose hEψ, hv]
    have hω' : (emptyAt χ'').ω = (emptyAt ψ).ω.translate (atVec u) := by
      change emptyMarkH (antitranspose χ''.ω.E) =
        (emptyMarkH (antitranspose ψ.ω.E)).translate (atVec u)
      unfold emptyMarkH MarkedInner.translate
      simp only [hv']
      have e : antitranspose χ''.ω.E = SkewGluing.translate (atVec u) (antitranspose ψ.ω.E) := by
        rw [hEq, antitranspose_translate]
      rw [e]
      simp [SkewGluing.translate]
    have hμEc : IsConnectedSkew μ.E := hμ.1.1
    by_cases hμW : μ.W = ∅
    · have hemp : μ.IsEmptyMark := by
        rcases hμ.1.2 with h1 | h1
        · exact h1
        · exact absurd hμW h1.1.ne_empty
      have hμeq : μ = emptyMarkH μ.E := MarkedInner.eq_emptyMarkH hemp
      have h1 : (emptyMarkH μ.E).anti = μ.anti := by rw [← hμeq]
      have hanti : μ.anti = emptyMarkV (antitranspose μ.E) :=
        h1.symm.trans (emptyMarkH_anti hμEc)
      have hAT : antitranspose χ''.D =
          (emptyMarkH (antitranspose μ.E)).compose (antitranspose (γ X)) := by
        rw [hD, MarkedInner.antitranspose_compose_of_isLegal hμ hγX, hanti]
        have := compose_emptyMarks_antitranspose
          (antitranspose_nonempty_iff.mpr hγX.2.1) (antitranspose μ.E)
        rw [antitranspose_antitranspose] at this
        exact this.symm
      refine ⟨emptyAt χ'', emptyAt ψ, emptyMarkH (antitranspose μ.E), antitranspose ∘ γ,
        atVec u, p1, p2, p3, q1, q2, hω', q3, emptyMarkH_isLegal
          (isConnectedSkew_antitranspose hμEc), ?_, ?_, hAT⟩
      · change antitranspose μ.E = antitranspose ψ.D
        rw [hμE]
      · rcases hγ with h | ⟨h, -⟩
        · right
          refine ⟨?_, rfl⟩
          rw [h]; rfl
        · left
          rw [h]; funext Y; exact antitranspose_antitranspose
    · have hγid : γ = id := by
        rcases hγ with h | ⟨-, h⟩
        · exact h
        · exact absurd h hμW
      have hμWn : μ.W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hμW
      refine ⟨emptyAt χ'', emptyAt ψ, μ.anti, id, atVec u, p1, p2, p3, q1, q2, hω', q3,
        isLegal_anti hμ hμWn, ?_, Or.inl rfl, ?_⟩
      · change antitranspose μ.E = antitranspose ψ.D
        rw [hμE]
      · change antitranspose χ''.D = μ.anti.compose X
        rw [hD, MarkedInner.antitranspose_compose_of_isLegal hμ hγX, hγid]
        rfl

end FoldSupplied
end SkewGluing
