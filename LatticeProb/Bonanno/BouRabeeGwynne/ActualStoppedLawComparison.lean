/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ActualStoppedLawComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteStoppedLawComparison
import LatticeProb.Bonanno.BouRabeeGwynne.WalkReconstructionLaw
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedEndpoint
import LatticeProb.Bonanno.BouRabeeGwynne.JointExcursionPasting

/-! Compare the actual stopped walk and Brownian laws through their finite
reconstructions. All support statements are derived from the exact original
process marginals of the full-excursion coupling. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal NNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem levyProkhorov_actual_stopped_laws_le (N : FiniteConductanceNetwork V)
    (hd : 1 ≤ d) (pos : V → Euc d) (hinj : Function.Injective pos)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (W : J → Set (Euc d)) (hW : ∀ j, IsOpen (W j))
    (hWb : ∀ j, Bornology.IsBounded (W j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ i, Measurable (select i))
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (v : V) (z : Euc d) (n : ℕ) (P : TimePartition n)
    {U : Set (Euc d)} (hU : IsOpen U) {a R S ε mesh δ η : ℝ}
    (hε : 0 < ε) (hmesh : 0 ≤ mesh) (hbuffer : ε + mesh < δ)
    (hnone : ∀ i x, select i x = none → x ∉ Metric.thickening δ U)
    (hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnear : dist (pos v) z ≤ a) (hpoint : R + a + S ≤ ε)
    (hsteps : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ k,
      dist (pos (ω k)) (pos (ω (k + 1))) ≤ mesh)
    (hwrange : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω i).2 ∈
        curveOscillationLe R)
    (hbrange : ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion W z initial (brownianSelectorForWalk select) i ω).2 ∈
        curveOscillationLe S)
    {b c o : ℝ≥0∞}
    (hfailure : N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
      {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ≤ b)
    (htail : μ {ω | (brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) n ω).1 = false} ≤ c)
    (hosc : μ {ω | P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k => (brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω).2)) ∈
      unitCurveExitOscillationBad (innerDomain U ε) (Metric.thickening δ U) η} ≤ o)
    (rWalk rMiddle rBrownian : ℝ≥0) (hrWalk : 0 < rWalk) (hrBrownian : 0 < rBrownian)
    (hwalkBudget : b + c ≤ (rWalk : ℝ≥0∞))
    (hbrownianBudget : c ≤ (rBrownian : ℝ≥0∞))
    (hmiddleBudget : b + c + o ≤ (rMiddle : ℝ≥0∞))
    (hsmall : ENNReal.ofReal (ε + η) < (rMiddle : ℝ≥0∞)) :
    levyProkhorovEDist
      ((N.trajectoryLaw A hA v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
      (stoppedBrownianLaw U z μ) ≤ (rWalk + rMiddle + rBrownian : ℝ≥0) := by
  let ρ := N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
  let Γ := fun ω k => brownianSkeletonExcursion W z initial
    (brownianSelectorForWalk select) k ω
  have hΓ : Measurable Γ := Measurable.of_eval fun k =>
    measurable_brownianSkeletonExcursion W hW z initial (fun i => hs (i - 1)) k
  have hmarg := N.walkBrownianJointLaw_marginals pos hinj B hB W hW μ select hs m E hE hdE
    hd hμ hWb hBA hA haccess initial v z
  have hwlaw : ρ.fst = (N.trajectoryLaw A hA v).map
      (actualWalkExcursionSequence pos B initial select) := hmarg.1
  have hblaw : ρ.snd = μ.map Γ := hmarg.2
  have hδ : 0 < δ := lt_of_lt_of_le hε (le_trans (le_add_of_nonneg_right hmesh) hbuffer.le)
  have hnoneU : ∀ i x, select i x = none → x ∉ U := by
    intro i x hx hxin
    exact hnone i x hx (Metric.self_subset_thickening hδ U hxin)
  have hnoneBrownian : ∀ i x, brownianSelectorForWalk select i x = none →
      x ∉ Metric.thickening δ U := fun i x hx => hnone (i - 1) x hx
  have hwalk : ∀ᵐ e ∂ρ.fst, (e n).1 = false ∨ e ∈ canonicalWalkStoppingSupport U mesh P := by
    rw [hwlaw]
    exact N.trajectoryLaw_map_ae_canonicalWalkStoppingSupport pos B hBA hA haccess
      initial select U hU.measurableSet hnoneU v n mesh hsteps P
  have hendpoint : ∀ᵐ γ ∂ρ.snd, (γ n).1 = true →
      P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (γ k).2)) 1 ∉
        Metric.thickening δ U := by
    rw [hblaw]
    exact standardBrownianLaw_skeleton_ae_stopped_endPoint_outside hd hμ W hW hWb z initial
      (brownianSelectorForWalk select) (fun i => hs (i - 1))
      Metric.isOpen_thickening.measurableSet hnoneBrownian n P
  have hclose : ∀ᵐ p ∂ρ,
      (∀ i ≤ n, (p.1 i, p.2 i) ∈ goodExcursionPair pos (E i) a) → ∀ t,
      dist (pastedWalkCurve P p.1 t)
        (P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (p.2 k).2)) t) ≤ ε := by
    filter_upwards [N.walkBrownianJointLaw_ae_pasted_dist_le hd pos hinj B hB W hW hWb μ hμ
      select hs m E hE hdE hBA hA haccess initial v z P hdiam hnear hwrange hbrange]
      with p hp
    intro hgood t
    exact (hp hgood t).trans hpoint
  have htailρ : ρ.snd (sequenceActive n) ≤ c := by
    rw [hblaw, Measure.map_apply hΓ (measurableSet_sequenceActive n)]
    exact htail
  let G := fun γ : ℕ → Bool × C(unitInterval, Euc d) =>
    P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (γ k).2))
  have hG : Measurable G := P.measurable_concatenate.comp
    ((ExcursionTrajectory.measurable_prefixChain n d).comp
      (Measurable.of_eval fun k => (measurable_pi_apply k).snd))
  have hObad : MeasurableSet {γ | G γ ∈
      unitCurveExitOscillationBad (innerDomain U ε) (Metric.thickening δ U) η} :=
    (measurableSet_unitCurveExitOscillationBad (isOpen_innerDomain U ε)
      Metric.isOpen_thickening η).preimage hG
  have hoscρ : ρ.snd {γ | G γ ∈
      unitCurveExitOscillationBad (innerDomain U ε) (Metric.thickening δ U) η} ≤ o := by
    rw [hblaw, Measure.map_apply hΓ hObad]
    exact hosc
  have hmiddle : levyProkhorovEDist
      (ρ.fst.map (reconstructedVertexStoppedCurve U n))
      (ρ.snd.map (reconstructedBrownianStoppedCurve U P)) ≤ (rMiddle : ℝ≥0∞) :=
    levyProkhorov_reconstructed_stopped_laws_le pos m E a P hU ρ hε hmesh hbuffer
      rMiddle hsmall hwalk hendpoint hclose hfailure htailρ hoscρ hmiddleBudget
  have hwalkTail : N.trajectoryLaw A hA v
      {ω | (actualWalkExcursionSequence pos B initial select ω n).1 = false} ≤
        (rWalk : ℝ≥0∞) := by
    apply (N.trajectoryLaw_walkActive_le_brownianActive_add_failure hd pos hinj B hB W hW hWb
      μ hμ select hs m E hE hdE hBA hA haccess initial v z a n).trans
    exact (add_le_add htail hfailure).trans (by simpa only [add_comm] using hwalkBudget)
  have hleft : levyProkhorovEDist
      ((N.trajectoryLaw A hA v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
      (ρ.fst.map (reconstructedVertexStoppedCurve U n)) ≤ (rWalk : ℝ≥0∞) := by
    rw [hwlaw]
    exact N.trajectoryLaw_reconstructedStopped_le pos B hBA hA haccess initial select U
      hU.measurableSet hnoneU v n rWalk hrWalk hwalkTail
  have hrightReverse : levyProkhorovEDist (stoppedBrownianLaw U z μ)
      (ρ.snd.map (reconstructedBrownianStoppedCurve U P)) ≤ (rBrownian : ℝ≥0∞) := by
    rw [hblaw]
    apply levyProkhorov_stoppedBrownian_reconstruction_le hd hμ W hW hWb z initial
      (brownianSelectorForWalk select) (fun i => hs (i - 1)) hU
      (fun i x hx => hnoneU (i - 1) x hx) n P rBrownian hrBrownian
    simpa only [brownianSkeletonExcursion_flag] using htail.trans hbrownianBudget
  have hright : levyProkhorovEDist
      (ρ.snd.map (reconstructedBrownianStoppedCurve U P)) (stoppedBrownianLaw U z μ) ≤
      (rBrownian : ℝ≥0∞) := by
    rw [levyProkhorovEDist_comm]
    exact hrightReverse
  have htriangle := (levyProkhorovEDist_triangle
    ((N.trajectoryLaw A hA v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
    (ρ.fst.map (reconstructedVertexStoppedCurve U n)) (stoppedBrownianLaw U z μ)).trans
      (add_le_add hleft ((levyProkhorovEDist_triangle
        (ρ.fst.map (reconstructedVertexStoppedCurve U n))
        (ρ.snd.map (reconstructedBrownianStoppedCurve U P)) (stoppedBrownianLaw U z μ)).trans
          (add_le_add hmiddle hright)))
  simpa only [ENNReal.coe_add, add_assoc] using htriangle

end BouRabeeGwynne.FiniteConductanceNetwork
