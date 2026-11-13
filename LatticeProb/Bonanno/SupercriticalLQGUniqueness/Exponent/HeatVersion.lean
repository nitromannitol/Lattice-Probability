/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.HeatVersion at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.NV1Evidence
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgPairing
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylField
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldGrad
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinCmp
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffCV
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8Couple
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinSetup
import LatticeProb.Bonanno.LQGMetric.Field.MarkovFinal
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Inc3
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffPos
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenCountable




 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.HeatVersion

open LQGMetric (DistC)

 

theorem lfppCrossingLength_eq_rectLen (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    lfppCrossingLength ξ φ =
      LQGMetric.DDDF.rectLen ξ φ (LQGMetric.DDDF.rectAB 1 1) := by
  rw [lfppCrossingLength_eq_old]
  have hs : LQGMetric.Blueprint.closedUnitSquare =
      (LQGMetric.DDDF.rectAB 1 1).toSet := by
    ext z
    simp [LQGMetric.Blueprint.closedUnitSquare, LQGMetric.DDDF.MarkedRect.toSet,
      LQGMetric.DDDF.rectAB, Complex.mem_reProdIm, and_assoc]
  have hl : LQGMetric.leftSide = (LQGMetric.DDDF.rectAB 1 1).side₁ := by
    ext z
    simp [LQGMetric.leftSide, LQGMetric.DDDF.MarkedRect.side₁,
      LQGMetric.DDDF.rectAB, Complex.mem_reProdIm]
  have hr : LQGMetric.rightSide = (LQGMetric.DDDF.rectAB 1 1).side₂ := by
    ext z
    simp [LQGMetric.rightSide, LQGMetric.DDDF.MarkedRect.side₂,
      LQGMetric.DDDF.rectAB, Complex.mem_reProdIm]
  rw [hs, hl, hr]
  rfl

 

theorem lfppCrossingLength_le_exp_of_abs_sub_le
    (ξ M : ℝ) (φ ψ : C(ℂ, ℝ))
    (h : ∀ z ∈ unitSquare, |φ z - ψ z| ≤ M) :
    lfppCrossingLength ξ φ ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppCrossingLength ξ ψ := by
  rw [lfppCrossingLength_eq_rectLen, lfppCrossingLength_eq_rectLen]
  change LQGMetric.DDDF.crossLenIn ξ φ (LQGMetric.DDDF.rectAB 1 1).toSet
      (LQGMetric.DDDF.rectAB 1 1).side₁ (LQGMetric.DDDF.rectAB 1 1).side₂ ≤
    ENNReal.ofReal (Real.exp (|ξ| * M)) *
      LQGMetric.DDDF.crossLenIn ξ ψ (LQGMetric.DDDF.rectAB 1 1).toSet
        (LQGMetric.DDDF.rectAB 1 1).side₁ (LQGMetric.DDDF.rectAB 1 1).side₂
  apply LQGMetric.DDDF.crossLenIn_le_of_abs_sub_le
  intro z hz
  exact h z (by simpa [unitSquare, LQGMetric.DDDF.MarkedRect.toSet,
    LQGMetric.DDDF.rectAB, Complex.mem_reProdIm, and_assoc] using hz)

 
theorem ae_eq_continuous_heat_versions
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (ε : ℝ) (hε : 0 < ε)
    (X Y : Ω → C(ℂ, ℝ))
    (hX : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X ω z)))
    (hY : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (Y ω z))) :
    ∀ᵐ ω ∂P, X ω = Y ω := by
  have heq : ∀ z : ℂ, (fun ω => X ω z) =ᵐ[P] (fun ω => Y ω z) := by
    intro z
    filter_upwards [hX z, hY z] with ω hx hy
    exact tendsto_nhds_unique hx hy
  filter_upwards [LQGMetric.DDDF.ae_eq_of_continuous_modification
    (Y₁ := fun z ω => X ω z) (Y₂ := fun z ω => Y ω z)
    (fun ω => (X ω).continuous) (fun ω => (Y ω).continuous) heq] with ω hω
  exact ContinuousMap.ext (hω ·)

 

theorem ae_eq_crossing_of_heat_versions
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (ξ ε : ℝ) (hε : 0 < ε)
    (X Y : Ω → C(ℂ, ℝ))
    (hX : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X ω z)))
    (hY : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (Y ω z))) :
    (fun ω => lfppCrossingLength ξ (X ω)) =ᵐ[P]
      (fun ω => lfppCrossingLength ξ (Y ω)) := by
  filter_upwards [ae_eq_continuous_heat_versions ε hε X Y hX hY] with ω hω
  rw [hω]

 

private def heatCrossingChain (ξ ε : ℝ) (g : DistC) : ℝ≥0∞ :=
  ⨅ (a : LQGMetric.LFPP.sideRat 0) (b : LQGMetric.LFPP.sideRat 1),
    ⨅ (N : ℕ) (q : Fin N → ↥(LQGMetric.LFPP.gaussRat ∩
      LQGMetric.Blueprint.closedUnitSquare)),
      LQGMetric.LFPP.chainCost ξ (LQGMetric.heatMollify ε g) a b N q

private theorem measurable_heatCrossingChain (ξ ε : ℝ) :
    Measurable (heatCrossingChain ξ ε) := by
  have := (LQGMetric.LFPP.sideRat_countable 0).to_subtype
  have := (LQGMetric.LFPP.sideRat_countable 1).to_subtype
  exact Measurable.iInf fun a => Measurable.iInf fun b =>
    LQGMetric.LFPP.measurable_iInf_chainCost ξ ε
      (LQGMetric.LFPP.gaussRat_countable.mono Set.inter_subset_left) a b

 

theorem ae_crossing_eq_heatCrossingChain
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (ξ ε : ℝ) (hε : 0 < ε)
    (X : Ω → C(ℂ, ℝ))
    (hX : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X ω z))) :
    (fun ω => lfppCrossingLength ξ (X ω)) =ᵐ[P]
      (fun ω => heatCrossingChain ξ ε (h ω)) := by
  obtain ⟨H, hHeq, hHlim⟩ := exists_heatVersion hh ε hε
  filter_upwards [ae_eq_crossing_of_heat_versions ξ ε hε X H hX hHlim, hHeq]
    with ω hXH hHω
  rw [hXH]
  have hfun : LQGMetric.heatMollify ε (h ω) = ⇑(H ω) :=
    funext fun z => (hHω z).symm
  have hc : Continuous (LQGMetric.heatMollify ε (h ω)) := by
    rw [hfun]
    exact (H ω).continuous
  have hH : H ω = ⟨LQGMetric.heatMollify ε (h ω), hc⟩ :=
    ContinuousMap.ext fun z => hHω z
  rw [hH, lfppCrossingLength_eq_chain]
  rfl

 

theorem map_crossing_eq_of_normalizedGFF
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (hh' : IsNormalizedWholePlaneGFF h' P')
    (ξ ε : ℝ) (hε : 0 < ε) (X : Ω → C(ℂ, ℝ)) (X' : Ω' → C(ℂ, ℝ))
    (hX : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X ω z)))
    (hX' : ∀ z : ℂ, ∀ᵐ ω ∂P',
      Tendsto (fun n : ℕ => h' ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X' ω z))) :
    P.map (fun ω => lfppCrossingLength ξ (X ω)) =
      P'.map (fun ω => lfppCrossingLength ξ (X' ω)) := by
  calc
    P.map (fun ω => lfppCrossingLength ξ (X ω)) =
        P.map (fun ω => heatCrossingChain ξ ε (h ω)) :=
      Measure.map_congr (ae_crossing_eq_heatCrossingChain hh ξ ε hε X hX)
    _ = (P.map h).map (heatCrossingChain ξ ε) := by
      exact (Measure.map_map (measurable_heatCrossingChain ξ ε) hh.1.measurable).symm
    _ = (P'.map h').map (heatCrossingChain ξ ε) := by
      rw [LQGMetric.CircleAvg.map_eq_of_isNormalizedWPGFF
        (isNormalizedWholePlaneGFF_iff_old.mp hh)
        (isNormalizedWholePlaneGFF_iff_old.mp hh')]
    _ = P'.map (fun ω => heatCrossingChain ξ ε (h' ω)) := by
      exact Measure.map_map (measurable_heatCrossingChain ξ ε) hh'.1.measurable
    _ = P'.map (fun ω => lfppCrossingLength ξ (X' ω)) :=
      (Measure.map_congr (ae_crossing_eq_heatCrossingChain hh' ξ ε hε X' hX')).symm

 

theorem isMedian_crossing_iff_of_normalizedGFF
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (hh' : IsNormalizedWholePlaneGFF h' P')
    (ξ ε : ℝ) (hε : 0 < ε) (X : Ω → C(ℂ, ℝ)) (X' : Ω' → C(ℂ, ℝ))
    (hX : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X ω z)))
    (hX' : ∀ z : ℂ, ∀ᵐ ω ∂P',
      Tendsto (fun n : ℕ => h' ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X' ω z))) (m : ℝ≥0∞) :
    IsMedian P (fun ω => lfppCrossingLength ξ (X ω)) m ↔
      IsMedian P' (fun ω => lfppCrossingLength ξ (X' ω)) m := by
  let L : Ω → ℝ≥0∞ := fun ω => lfppCrossingLength ξ (X ω)
  let L' : Ω' → ℝ≥0∞ := fun ω => lfppCrossingLength ξ (X' ω)
  have hm : AEMeasurable L P :=
    ((measurable_heatCrossingChain ξ ε).comp hh.1.measurable).aemeasurable.congr
      (ae_crossing_eq_heatCrossingChain hh ξ ε hε X hX).symm
  have hm' : AEMeasurable L' P' :=
    ((measurable_heatCrossingChain ξ ε).comp hh'.1.measurable).aemeasurable.congr
      (ae_crossing_eq_heatCrossingChain hh' ξ ε hε X' hX').symm
  have hlaw := map_crossing_eq_of_normalizedGFF hh hh' ξ ε hε X X' hX hX'
  have hle : P {ω | L ω ≤ m} = P' {ω | L' ω ≤ m} := by
    have hmap := congrArg (fun μ : Measure ℝ≥0∞ => μ (Set.Iic m)) hlaw
    change (P.map L) (Set.Iic m) = (P'.map L') (Set.Iic m) at hmap
    rw [Measure.map_apply_of_aemeasurable hm measurableSet_Iic,
      Measure.map_apply_of_aemeasurable hm' measurableSet_Iic] at hmap
    exact hmap
  have hge : P {ω | m ≤ L ω} = P' {ω | m ≤ L' ω} := by
    have hmap := congrArg (fun μ : Measure ℝ≥0∞ => μ (Set.Ici m)) hlaw
    change (P.map L) (Set.Ici m) = (P'.map L') (Set.Ici m) at hmap
    rw [Measure.map_apply_of_aemeasurable hm measurableSet_Ici,
      Measure.map_apply_of_aemeasurable hm' measurableSet_Ici] at hmap
    exact hmap
  constructor
  · rintro ⟨_, h₁, h₂⟩
    exact ⟨hm', hle ▸ h₁, hge ▸ h₂⟩
  · rintro ⟨_, h₁, h₂⟩
    exact ⟨hm, hle.symm ▸ h₁, hge.symm ▸ h₂⟩

 

end SupercriticalLQGUniqueness.Exponent.HeatVersion
