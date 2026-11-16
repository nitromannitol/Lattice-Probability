import LatticeProb.Topology.DiskMobiusAction
import LatticeProb.Prob.VaryingFiniteMeasureAction

/-! # Möbius actions on continuously varying disk decorations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace LatticeProb

/-- The pushforward of a continuously varying finite measure by a continuously varying
    disk Möbius map is weakly continuous. -/
theorem continuous_varyingFiniteMeasure_map_diskMobiusAction
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    {μ : Z → FiniteMeasure ClosedUnitDisk} {p : Z → DiskMobiusParameters}
    (hμ : Continuous μ) (hp : Continuous p) :
    Continuous (fun z => (μ z).map (fun x => diskMobiusAction (x, p z))) := by
  apply continuous_varyingFiniteMeasure_map_family hμ
    (F := fun q : ClosedUnitDisk × Z => diskMobiusAction (q.1, p q.2))
  exact continuous_diskMobiusAction.comp (continuous_fst.prodMk (hp.comp continuous_snd))

/-- Applying continuously varying disk Möbius maps to continuously varying parametrized
    curves is continuous for the compact-open topology. -/
theorem continuous_varyingCurve_diskMobiusAction
    {Z T : Type*} [TopologicalSpace Z] [TopologicalSpace T] [LocallyCompactSpace T]
    {η : Z → C(T, ClosedUnitDisk)} {p : Z → DiskMobiusParameters}
    (hη : Continuous η) (hp : Continuous p) :
    Continuous (fun z => (⟨fun t => diskMobiusAction (η z t, p z),
      continuous_diskMobiusAction.comp ((η z).continuous.prodMk continuous_const)⟩ :
      C(T, ClosedUnitDisk))) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_diskMobiusAction.comp
    ((continuous_eval.comp ((hη.comp continuous_fst).prodMk continuous_snd)).prodMk
      (hp.comp continuous_fst))

/-- A disk Möbius transformation acts continuously on a varying measure, parametrized curve,
    and finite collection of marked points. -/
theorem continuous_varyingDecorated_diskMobiusAction
    {Z T ι : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [TopologicalSpace T] [LocallyCompactSpace T] [Fintype ι]
    {μ : Z → FiniteMeasure ClosedUnitDisk} {η : Z → C(T, ClosedUnitDisk)}
    {m : Z → ι → ClosedUnitDisk} {p : Z → DiskMobiusParameters}
    (hμ : Continuous μ) (hη : Continuous η) (hm : Continuous m) (hp : Continuous p) :
    Continuous (fun z => ((μ z).map (fun x => diskMobiusAction (x, p z)),
      (⟨fun t => diskMobiusAction (η z t, p z),
        continuous_diskMobiusAction.comp ((η z).continuous.prodMk continuous_const)⟩ :
        C(T, ClosedUnitDisk)),
      fun i => diskMobiusAction (m z i, p z))) := by
  refine (continuous_varyingFiniteMeasure_map_diskMobiusAction hμ hp).prodMk ?_
  refine (continuous_varyingCurve_diskMobiusAction hη hp).prodMk ?_
  apply continuous_pi
  intro i
  exact continuous_diskMobiusAction.comp
    (((continuous_apply i).comp hm).prodMk hp)

end LatticeProb
