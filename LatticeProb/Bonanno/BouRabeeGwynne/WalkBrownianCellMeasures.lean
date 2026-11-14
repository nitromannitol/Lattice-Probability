/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkBrownianCellMeasures at commit fdb5cad; local import paths and Lean compatibility settings are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianCoupling

set_option linter.style.haveILetI false

/-! Exact cell masses of genuine whole excursions. The finite graph support
restriction does not change the actual walk exit probabilities. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal

namespace BouRabeeGwynne

variable {d : ℕ}

lemma activeEndpointCell_map_false {S : Type*} [MeasurableSpace S]
    (endpoint : S → Euc d) (he : Measurable endpoint) (ν : Measure S)
    {E : Set (Euc d)} (hE : MeasurableSet E) :
    (ν.map (fun e => (false, e))) (activeEndpointCell endpoint E) = (ν.map endpoint) E := by
  have hm : Measurable (fun e : S => (false, e)) := measurable_const.prodMk measurable_id
  rw [Measure.map_apply hm
      (measurableSet_activeEndpointCell endpoint he hE), Measure.map_apply he hE]
  congr 1
  ext e
  simp only [activeEndpointCell, mem_preimage, mem_ofPred_eq, true_and]

lemma brownian_activeEndpointCell_mass {U : Set (Euc d)} (hU : IsOpen U)
    (μ : Measure (BrownianPath d)) [IsFiniteMeasure μ] (z : Euc d)
    {E : Set (Euc d)} (hE : MeasurableSet E) :
    ((brownianExcursionKernel hU μ z).map (fun c => (false, c)))
        (activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) E) =
      ((stoppedBrownianLaw U z μ).map CurveSpace.endPoint) E := by
  rw [activeEndpointCell_map_false _ (ContinuousMap.measurable_eval 1) _ hE,
    ← brownianExcursionKernel_project hU μ z,
    Measure.map_map CurveSpace.continuous_endPoint.measurable
      CurveSpace.continuous_project.measurable]
  rfl

lemma brownian_activeEndpointCells_cover {U : Set (Euc d)} (hd : 1 ≤ d)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    {z : Euc d} (hz : z ∈ U) {ι : Type*} [Countable ι]
    (E : ι → Set (Euc d)) (hE : ∀ i, MeasurableSet (E i))
    (hcover : closure U ⊆ ⋃ i, E i) :
    ((brownianExcursionKernel hU μ z).map (fun c => (false, c)))
      (⋃ i, activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E i)) = 1 := by
  haveI : IsProbabilityMeasure
      ((brownianExcursionKernel hU μ z).map (fun c => (false, c))) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_const.prodMk measurable_id).aemeasurable).mpr inferInstance
  apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion fun i =>
    measurableSet_activeEndpointCell _ (ContinuousMap.measurable_eval 1) (hE i))).mp
  apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable
    (MeasurableSet.iUnion fun i =>
      measurableSet_activeEndpointCell _ (ContinuousMap.measurable_eval 1) (hE i))).mpr
  filter_upwards [brownianExcursionKernel_ae_mem_closure hd hU hUb μ hμ hz] with c hc
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (hc 1))
  exact Set.mem_iUnion.mpr ⟨i, rfl, hi⟩

namespace FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  (N : FiniteConductanceNetwork V)

lemma walkEndpointCell_mass (pos : V → Euc d) (B : Set V)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (v : V)
    {E : Set (Euc d)} (hE : MeasurableSet E) :
    ((N.clockedWalkExcursionKernel pos B hB v).map (fun e => (false, e)))
        (walkEndpointCell pos E) = ((N.discreteHarmonicMeasure B hB v).map pos) E := by
  change ((N.clockedWalkExcursionKernel pos B hB v).map (fun e => (false, e)))
    (activeEndpointCell ClockedWalkExcursion.endPoint (E ∩ Set.range pos)) = _
  rw [activeEndpointCell_map_false _ ClockedWalkExcursion.measurable_endPoint _
      (hE.inter (Set.finite_range pos).measurableSet),
    N.clockedWalkExcursionKernel_endPoint,
    Measure.map_apply (measurable_of_finite pos) (hE.inter (Set.finite_range pos).measurableSet),
    Measure.map_apply (measurable_of_finite pos) hE]
  congr 1
  ext w
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  exact and_iff_left ⟨w, rfl⟩

/-- The actual full-excursion coupling has small bad mass whenever the actual
spatial exit measures have small cell errors. The Brownian support is derived
from its genuine stopped path, including the exit endpoint. -/
theorem finite_walkBrownian_excursion_bad_le (hd : 1 ≤ d)
    (pos : V → Euc d) (B : Set V) (hB : ∀ v ∈ B, 0 < N.totalConductance v)
    (v : V) {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    {z : Euc d} (hz : z ∈ U) {m : ℕ} (E : Fin m → Set (Euc d))
    (hE : ∀ i, MeasurableSet (E i)) (hdE : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : closure U ⊆ ⋃ i, E i) {b : ℝ} (hb : 0 ≤ b)
    (herror : ∀ i, |(((N.discreteHarmonicMeasure B hB v).map pos) (E i)).toReal -
      (((stoppedBrownianLaw U z μ).map CurveSpace.endPoint) (E i)).toReal| ≤ b / (m + 1))
    (Bad : Set ((Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d))))
    (hBad : ∀ i, Disjoint Bad (walkEndpointCell pos (E i) ×ˢ
      activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E i))) :
    finitePartitionCoupling
      ((N.clockedWalkExcursionKernel pos B hB v).map (fun e => (false, e)))
      ((brownianExcursionKernel hU μ z).map (fun c => (false, c)))
      (fun i => walkEndpointCell pos (E i))
      (fun i => activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E i)) Bad ≤
        ENNReal.ofReal b := by
  haveI : IsProbabilityMeasure
      ((N.clockedWalkExcursionKernel pos B hB v).map (fun e => (false, e))) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_const.prodMk measurable_id).aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure
      ((brownianExcursionKernel hU μ z).map (fun c => (false, c))) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_const.prodMk measurable_id).aemeasurable).mpr inferInstance
  have herr : ∀ i : Fin m,
      |(((N.clockedWalkExcursionKernel pos B hB v).map (fun e => (false, e)))
          (walkEndpointCell pos (E i))).toReal -
        (((brownianExcursionKernel hU μ z).map (fun c => (false, c)))
          (activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E i))).toReal| ≤
            b / (m + 1) := by
    intro i
    rw [N.walkEndpointCell_mass pos B hB v (hE i),
      brownian_activeEndpointCell_mass hU μ z (hE i)]
    exact herror i
  apply (finitePartitionCoupling_bad_le_of_cell_error _ _
    (fun i => measurableSet_walkEndpointCell pos (hE i))
    (fun i => measurableSet_activeEndpointCell _ (ContinuousMap.measurable_eval 1) (hE i))
    (pairwiseDisjoint_walkEndpointCell pos hdE)
    (pairwiseDisjoint_activeEndpointCell _ hdE)
    (brownian_activeEndpointCells_cover hd hU hUb μ hμ hz E hE hcover)
    (div_nonneg hb (by positivity)) herr Bad hBad).trans
      (ENNReal.ofReal_le_ofReal ?_)
  simp only [Fintype.card_fin]
  change (m : ℝ) * (b / (m + 1)) ≤ b
  have hm : (0 : ℝ) < m + 1 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hm).mpr
  nlinarith

end FiniteConductanceNetwork
end BouRabeeGwynne
