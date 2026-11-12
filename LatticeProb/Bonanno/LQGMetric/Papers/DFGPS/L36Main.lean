/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36Main at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36LowerR
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
`DFGPS.Lem3_6` (T:1628–1650) = lower bound (proved, `lem3_6_lower`, from DG Thm 1.5 (1.5b) second
half) ∧ upper bound; the upper bound reduces to `𝕣 = 1` (`lem3_6_upper_of_one`). The remaining
open statement `Lem3_6UpperOne` is the upper half of (eqn-lfpp-dist-show), T:1645: w.p. → 1,
`D̃^δ_h(∂_L 𝕊, ∂_R 𝕊; 𝕊) ≤ δ^{−ξQ−ζ} e^{ξ h_1(0)}` (here `h_1(0) = 0` a.s.). See
`handoff/P2-DFC1.md` for why it does not follow from the DG Props as stated (paths must reach
the sides of `𝕊` inside `𝕊`; DG Thm 1.5 controls only fixed compact `K ⊂ U` without rate).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L36

open Blueprint

/-- Upper half of DFGPS Lemma 3.6 at `𝕣 = 1` (T:1645, `eqn-lfpp-dist-show`, upper inequality). -/
def Lem3_6UpperOne : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ ζ ∈ Ioo (0 : ℝ) 1,
    ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ graphLFPP (xiGamma γ) δ (fun x => circleAvg (h ω) δ x)
        (leftVerts δ 1) (rightVerts δ 1) (rS 1) ≤
          δ ^ (-xiGamma γ * Q γ - ζ) * Real.exp (xiGamma γ * circleAvg (h ω) 1 0)} ≤
        ENNReal.ofReal η

/-- **DFGPS Lemma 3.6** from DG Thm 1.5 (1.5b, second half) and the upper half at `𝕣 = 1`. -/
theorem lem3_6_of_upperOne (hKU : DGThm1_5KU) (hU : Lem3_6UpperOne) : DFGPS.Lem3_6 := by
  intro γ hγ0 hγ2 Ω _ P _ h hh ζ hζ η hη
  obtain ⟨δ₁, hδ₁, H1⟩ := lem3_6_lower hKU hγ0 hγ2 P h hh hζ.1 (η := η/2) (by positivity)
  obtain ⟨δ₂, hδ₂, H2⟩ := hU γ hγ0 hγ2 P h hh ζ hζ (η/2) (by positivity)
  have H2' := lem3_6_upper_of_one P h hh H2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ 𝕣 h𝕣 => ?_⟩
  have hδa : δ ∈ Ioo (0:ℝ) δ₁ := ⟨hδ.1, lt_of_lt_of_le hδ.2 (min_le_left _ _)⟩
  have hδb : δ ∈ Ioo (0:ℝ) δ₂ := ⟨hδ.1, lt_of_lt_of_le hδ.2 (min_le_right _ _)⟩
  refine (measure_mono fun ω hω => ?_).trans ((measure_union_le _ _).trans
    ((add_le_add (H1 δ hδa 𝕣 h𝕣) (H2' δ hδb 𝕣 h𝕣)).trans_eq ?_))
  · simp only [mem_setOf_eq, not_and_or] at hω
    exact hω
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end LQGMetric.DFGPS.L36
