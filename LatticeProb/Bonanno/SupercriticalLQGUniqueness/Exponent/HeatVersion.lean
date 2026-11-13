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

 
theorem lfppCrossingLength_lt_exp_of_abs_sub_le
    (ξ M : ℝ) (φ ψ : C(ℂ, ℝ)) (a : ℝ≥0∞)
    (h : ∀ z ∈ unitSquare, |φ z - ψ z| ≤ M)
    (hlt : lfppCrossingLength ξ φ < a) :
    lfppCrossingLength ξ ψ <
      ENNReal.ofReal (Real.exp (|ξ| * M)) * a := by
  have hs : ∀ z ∈ unitSquare, |ψ z - φ z| ≤ M := by
    intro z hz
    simpa only [abs_sub_comm] using h z hz
  have hcost := lfppCrossingLength_le_exp_of_abs_sub_le ξ M ψ φ hs
  have hmul : ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppCrossingLength ξ φ <
      ENNReal.ofReal (Real.exp (|ξ| * M)) * a := by
    simpa only [mul_comm] using
      (ENNReal.mul_lt_mul_left
        (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
        ENNReal.ofReal_ne_top hlt)
  exact hcost.trans_lt hmul

 

theorem rectLen_lt_exp_of_abs_sub_le
    (ξ M : ℝ) (f g : ℂ → ℝ) (a : ℝ≥0∞)
    (h : ∀ z ∈ LQGMetric.Blueprint.closedUnitSquare, |f z - g z| ≤ M)
    (hlt : LQGMetric.DDDF.rectLen ξ f (LQGMetric.DDDF.rectAB 1 1) < a) :
    LQGMetric.DDDF.rectLen ξ g (LQGMetric.DDDF.rectAB 1 1) <
      ENNReal.ofReal (Real.exp (|ξ| * M)) * a := by
  have hcost : LQGMetric.DDDF.rectLen ξ g (LQGMetric.DDDF.rectAB 1 1) ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) *
        LQGMetric.DDDF.rectLen ξ f (LQGMetric.DDDF.rectAB 1 1) := by
    change LQGMetric.DDDF.crossLenIn ξ g (LQGMetric.DDDF.rectAB 1 1).toSet
        (LQGMetric.DDDF.rectAB 1 1).side₁ (LQGMetric.DDDF.rectAB 1 1).side₂ ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) *
        LQGMetric.DDDF.crossLenIn ξ f (LQGMetric.DDDF.rectAB 1 1).toSet
          (LQGMetric.DDDF.rectAB 1 1).side₁ (LQGMetric.DDDF.rectAB 1 1).side₂
    apply LQGMetric.DDDF.crossLenIn_le_of_abs_sub_le
    intro z hz
    have hzS : z ∈ LQGMetric.Blueprint.closedUnitSquare := by
      simpa [LQGMetric.Blueprint.closedUnitSquare, LQGMetric.DDDF.MarkedRect.toSet,
        LQGMetric.DDDF.rectAB, Complex.mem_reProdIm, and_assoc] using hz
    simpa only [abs_sub_comm] using h z hzS
  have hmul : ENNReal.ofReal (Real.exp (|ξ| * M)) *
      LQGMetric.DDDF.rectLen ξ f (LQGMetric.DDDF.rectAB 1 1) <
      ENNReal.ofReal (Real.exp (|ξ| * M)) * a := by
    simpa only [mul_comm] using
      (ENNReal.mul_lt_mul_left
        (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
        ENNReal.ofReal_ne_top hlt)
  exact hcost.trans_lt hmul

theorem rectLen_le_exp_of_abs_sub_le
    (ξ M : ℝ) (f g : ℂ → ℝ) (a : ℝ≥0∞)
    (h : ∀ z ∈ LQGMetric.Blueprint.closedUnitSquare, |f z - g z| ≤ M)
    (hle : LQGMetric.DDDF.rectLen ξ f (LQGMetric.DDDF.rectAB 1 1) ≤ a) :
    LQGMetric.DDDF.rectLen ξ g (LQGMetric.DDDF.rectAB 1 1) ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) * a := by
  have hcost : LQGMetric.DDDF.rectLen ξ g (LQGMetric.DDDF.rectAB 1 1) ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) *
        LQGMetric.DDDF.rectLen ξ f (LQGMetric.DDDF.rectAB 1 1) := by
    change LQGMetric.DDDF.crossLenIn ξ g (LQGMetric.DDDF.rectAB 1 1).toSet
        (LQGMetric.DDDF.rectAB 1 1).side₁ (LQGMetric.DDDF.rectAB 1 1).side₂ ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) *
        LQGMetric.DDDF.crossLenIn ξ f (LQGMetric.DDDF.rectAB 1 1).toSet
          (LQGMetric.DDDF.rectAB 1 1).side₁ (LQGMetric.DDDF.rectAB 1 1).side₂
    apply LQGMetric.DDDF.crossLenIn_le_of_abs_sub_le
    intro z hz
    have hzS : z ∈ LQGMetric.Blueprint.closedUnitSquare := by
      simpa [LQGMetric.Blueprint.closedUnitSquare, LQGMetric.DDDF.MarkedRect.toSet,
        LQGMetric.DDDF.rectAB, Complex.mem_reProdIm, and_assoc] using hz
    simpa only [abs_sub_comm] using h z hzS
  exact hcost.trans (mul_le_mul_of_nonneg_left hle zero_le)

 

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

 
theorem isMedian_congr_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {L L' : Ω → ℝ≥0∞} (h : L =ᵐ[P] L') (m : ℝ≥0∞) :
    IsMedian P L m ↔ IsMedian P L' m := by
  have aux : ∀ {A B : Ω → ℝ≥0∞}, A =ᵐ[P] B → IsMedian P A m → IsMedian P B m := by
    intro A B hab
    rintro ⟨hm, hleft, hright⟩
    refine ⟨(aemeasurable_congr hab).mp hm, ?_, ?_⟩
    · have he : {ω | A ω ≤ m} =ᵐ[P] {ω | B ω ≤ m} :=
        hab.mono fun ω hω => by simp only [Set.mem_ofPred_eq, hω]
      simpa only [measure_congr he] using hleft
    · have he : {ω | m ≤ A ω} =ᵐ[P] {ω | m ≤ B ω} :=
        hab.mono fun ω hω => by simp only [Set.mem_ofPred_eq, hω]
      simpa only [measure_congr he] using hright
  exact ⟨aux h, aux h.symm⟩

 

theorem isMedian_heat_version_iff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (ξ ε : ℝ) (hε : 0 < ε) (X Y : Ω → C(ℂ, ℝ))
    (hX : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X ω z)))
    (hY : ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (Y ω z))) (m : ℝ≥0∞) :
    IsMedian P (fun ω => lfppCrossingLength ξ (X ω)) m ↔
      IsMedian P (fun ω => lfppCrossingLength ξ (Y ω)) m :=
  isMedian_congr_ae P (ae_eq_crossing_of_heat_versions ξ ε hε X Y hX hY) m

 


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

 

theorem log_median_bound_of_sandwich
    {u v lam a d K : ℝ} (hu : 0 < u) (hv : 0 < v) (_hlam : 0 < lam)
    (ha : 0 < a)
    (hlo : Real.exp (-d) * u ≤ a)
    (hhi : a ≤ Real.exp d * v)
    (hqu : Real.log lam - K ≤ Real.log u)
    (hqv : Real.log v ≤ Real.log lam + K) :
    |Real.log a - Real.log lam| ≤ d + K := by
  have hlower : -d + Real.log u ≤ Real.log a := by
    have h := Real.log_le_log (mul_pos (Real.exp_pos _) hu) hlo
    rw [Real.log_mul (Real.exp_pos _).ne' hu.ne', Real.log_exp] at h
    exact h
  have hupper : Real.log a ≤ d + Real.log v := by
    have h := Real.log_le_log ha hhi
    rw [Real.log_mul (Real.exp_pos _).ne' hv.ne', Real.log_exp] at h
    exact h
  apply abs_le.mpr
  constructor <;> linarith only [hlower, hupper, hqu, hqv]

 



theorem exists_markov_heat_comparison
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : LQGMetric.IsWholePlaneGFF h P) :
    ∃ (Xh : LQGMetric.BddOn (LQGMetric.HeatSq.sqOpens (-1) 3 : Set ℂ) → Ω → ℝ)
      (Y : ℝ → ℂ → Ω → ℝ) (M ε₁ : ℝ),
      LQGMetric.IsZBGFFProcessExt (LQGMetric.HeatSq.sqOpens (-1) 3) Xh P ∧
      (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
        LQGMetric.Blueprint.IsContVersion
          (fun x => Xh (LQGMetric.Blueprint.heatBdd (LQGMetric.HeatSq.sqOpens (-1) 3)
            (δ / 2) x)) (Y δ) P) ∧
      0 < ε₁ ∧
      (∀ ε, 0 < ε → ε < ε₁ →
        P {ω | ∃ z ∈ LQGMetric.Blueprint.closedUnitSquare,
          M < |LQGMetric.heatMollify ε (h ω) z - Y (ε ^ 2) z ω|} ≤
            ENNReal.ofReal (1 / 16)) := by
  have hVb : Bornology.IsBounded
      ((LQGMetric.HeatSq.sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ) :=
    LQGMetric.HeatSq.isBounded_sqOpen (-1) 3
  have hVd : Disjoint
      ((LQGMetric.HeatSq.sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ)
      (Metric.sphere (0 : ℂ) 4) := LQGMetric.DFGPS.disjoint_sqOpen_sphere
  obtain ⟨harm, zb, Xh, hsum, hharm, _, hX, hlink⟩ :=
    LQGMetric.DFGPS.markov_zb_coupling LQGMetric.MarkovFinal.lmLem2_1
      P h hh (by norm_num : (0 : ℝ) < 4) 0
      (LQGMetric.HeatSq.sqOpens (-1) 3) hVb hVd
  obtain ⟨Y, hY⟩ :=
    LQGMetric.DFGPS.exists_heat_contVersion_sq
      (by norm_num : (0 : ℝ) < 3) hX
  obtain ⟨M, ε₁, hε₁, hprob⟩ :=
    LQGMetric.DFGPS.gff_zb_field_prob hh hsum hharm hX hlink hY
      (1 / 16) (by norm_num)
  exact ⟨Xh, Y, M, ε₁, hX, hY, hε₁, hprob⟩

 



theorem exists_p29_fixed_threshold :
    ∃ x : ℝ, 0 < x ∧ ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
        (Xh : LQGMetric.BddOn
          (LQGMetric.HeatSq.sqOpens (-1) 3 : Set ℂ) → Ω → ℝ)
        (W : LQGMetric.WhiteNoise.WNSpace → Ω → ℝ) (Y : ℂ → Ω → ℝ),
        @IsProbabilityMeasure Ω mΩ P ∧
        @LQGMetric.IsZBGFFProcessExt Ω mΩ
          (LQGMetric.HeatSq.sqOpens (-1) 3) Xh P ∧
        @LQGMetric.WhiteNoise.IsWhiteNoise Ω mΩ P W ∧
        @LQGMetric.Blueprint.IsContVersion Ω mΩ
          (fun z => Xh (LQGMetric.Blueprint.heatBdd
            (LQGMetric.HeatSq.sqOpens (-1) 3) (t / 2) z)) Y P ∧
        P {ω | ENNReal.ofReal x ≤
          ⨆ z ∈ LQGMetric.HeatSq.sqOpen (-1 / 2) 2,
            ENNReal.ofReal
              |LQGMetric.DDDF.phiVer W P (Real.sqrt t) 1 z ω - Y z ω|} ≤
          ENNReal.ofReal (1 / 16) := by
  let U : Set ℂ := LQGMetric.HeatSq.sqOpen (-1 / 2) 2
  have hUc : closure U ⊆
      ((LQGMetric.HeatSq.sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ) := by
    intro z hz
    obtain ⟨h₁, h₂, h₃, h₄⟩ :=
      LQGMetric.DFGPS.closure_sqOpen_subset _ _ hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨C, c, hC, hc, hP29⟩ :=
    LQGMetric.DDDF.P29WN.dddfProp29Sq U
      (LQGMetric.HeatSq.isOpen_sqOpen _ _)
      (LQGMetric.HeatSq.isBounded_sqOpen _ _).isCompact_closure hUc
  obtain ⟨x, hx0, hxζ⟩ :=
    LQGMetric.DFGPS.exists_gauss_tail_le (C := C) hc
      (by norm_num : (0 : ℝ) < 1 / 16)
  refine ⟨x, hx0, fun t ht => ?_⟩
  obtain ⟨Ω, mΩ, P, Xh, W, Y, hP, hX, hW, hY, htail⟩ := hP29 t ht
  refine ⟨Ω, mΩ, P, Xh, W, Y, hP, hX, hW, hY, ?_⟩
  exact (htail x hx0.le).trans (ENNReal.ofReal_le_ofReal hxζ)

 

theorem map_rectLen_heat_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P']
    {Xh : LQGMetric.BddOn
      (LQGMetric.HeatSq.sqOpens (-1) 3 : Set ℂ) → Ω → ℝ}
    {Xh' : LQGMetric.BddOn
      (LQGMetric.HeatSq.sqOpens (-1) 3 : Set ℂ) → Ω' → ℝ}
    (hX : LQGMetric.IsZBGFFProcessExt (LQGMetric.HeatSq.sqOpens (-1) 3) Xh P)
    (hX' : LQGMetric.IsZBGFFProcessExt (LQGMetric.HeatSq.sqOpens (-1) 3) Xh' P')
    {s : ℝ} {Y : ℂ → Ω → ℝ} {Y' : ℂ → Ω' → ℝ}
    (hY : LQGMetric.Blueprint.IsContVersion
      (fun x => Xh (LQGMetric.Blueprint.heatBdd
        (LQGMetric.HeatSq.sqOpens (-1) 3) s x)) Y P)
    (hY' : LQGMetric.Blueprint.IsContVersion
      (fun x => Xh' (LQGMetric.Blueprint.heatBdd
        (LQGMetric.HeatSq.sqOpens (-1) 3) s x)) Y' P')
    (ξ : ℝ) :
    P.map (fun ω => LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
      (LQGMetric.DDDF.rectAB 1 1)) =
    P'.map (fun ω => LQGMetric.DDDF.rectLen ξ (fun z => Y' z ω)
      (LQGMetric.DDDF.rectAB 1 1)) := by
  let F : C(ℂ, ℝ) → ℝ≥0∞ := fun f =>
    LQGMetric.DDDF.rectLen ξ f (LQGMetric.DDDF.rectAB 1 1)
  have hF : Measurable F :=
    LQGMetric.DDDF.measurable_crossLenIn
      (LQGMetric.DDDF.rectAB 1 1).isCompact_toSet
      (fun f => f.continuous)
      (fun z => ContinuousMap.measurable_eval z)
  calc
    P.map (fun ω => LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
        (LQGMetric.DDDF.rectAB 1 1)) =
        (P.map (LQGMetric.DFGPS.pathC Y hY.1)).map F := by
      exact (Measure.map_map hF
        (LQGMetric.DFGPS.measurable_pathC hY.1 hY.2.1)).symm
    _ = (P'.map (LQGMetric.DFGPS.pathC Y' hY'.1)).map F := by
      rw [LQGMetric.DFGPS.map_pathC_heat_eq hX hX' hY hY']
    _ = P'.map (fun ω => LQGMetric.DDDF.rectLen ξ (fun z => Y' z ω)
        (LQGMetric.DDDF.rectAB 1 1)) :=
      Measure.map_map hF (LQGMetric.DFGPS.measurable_pathC hY'.1 hY'.2.1)

 

theorem cdf_lt_le_of_good_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : Ω → ℝ≥0∞) (E : Set Ω) (a b : ℝ≥0∞)
    (hgood : ∀ ω ∈ E, A ω < a → B ω < b) :
    P {ω | A ω < a} ≤ P {ω | B ω < b} + P Eᶜ := by
  calc
    P {ω | A ω < a} ≤ P ({ω | B ω < b} ∪ Eᶜ) := by
      apply measure_mono
      intro ω hω
      by_cases he : ω ∈ E
      · exact Or.inl (hgood ω he hω)
      · exact Or.inr he
    _ ≤ P {ω | B ω < b} + P Eᶜ := measure_union_le _ _

theorem cdf_le_le_of_good_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : Ω → ℝ≥0∞) (E : Set Ω) (a b : ℝ≥0∞)
    (hgood : ∀ ω ∈ E, A ω ≤ a → B ω ≤ b) :
    P {ω | A ω ≤ a} ≤ P {ω | B ω ≤ b} + P Eᶜ := by
  calc
    P {ω | A ω ≤ a} ≤ P ({ω | B ω ≤ b} ∪ Eᶜ) := by
      apply measure_mono
      intro ω hω
      by_cases he : ω ∈ E
      · exact Or.inl (hgood ω he hω)
      · exact Or.inr he
    _ ≤ P {ω | B ω ≤ b} + P Eᶜ := measure_union_le _ _

 

theorem markov_heat_cdf_lt_step
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (Y : ℂ → Ω → ℝ) (ξ ε M ζ : ℝ) (a : ℝ≥0∞)
    (hprob : P {ω | ∃ z ∈ LQGMetric.Blueprint.closedUnitSquare,
      M < |LQGMetric.heatMollify ε (h ω) z - Y z ω|} ≤ ENNReal.ofReal ζ) :
    P {ω | LQGMetric.DDDF.rectLen ξ (LQGMetric.heatMollify ε (h ω))
      (LQGMetric.DDDF.rectAB 1 1) < a} ≤
    P {ω | LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
      (LQGMetric.DDDF.rectAB 1 1) <
      ENNReal.ofReal (Real.exp (|ξ| * M)) * a} + ENNReal.ofReal ζ := by
  let E : Set Ω := {ω | ¬∃ z ∈ LQGMetric.Blueprint.closedUnitSquare,
    M < |LQGMetric.heatMollify ε (h ω) z - Y z ω|}
  have hEc : P Eᶜ ≤ ENNReal.ofReal ζ := by
    simpa only [E, Set.compl_ofPred, not_not] using hprob
  have hgood : ∀ ω ∈ E,
      LQGMetric.DDDF.rectLen ξ (LQGMetric.heatMollify ε (h ω))
        (LQGMetric.DDDF.rectAB 1 1) < a →
      LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
        (LQGMetric.DDDF.rectAB 1 1) <
        ENNReal.ofReal (Real.exp (|ξ| * M)) * a := by
    intro ω hω ha
    apply rectLen_lt_exp_of_abs_sub_le ξ M _ _ a ?_ ha
    intro z hz
    exact le_of_not_gt (fun hgt => hω ⟨z, hz, by simpa only [abs_sub_comm] using hgt⟩)
  exact (cdf_lt_le_of_good_event P _ _ E a
    (ENNReal.ofReal (Real.exp (|ξ| * M)) * a) hgood).trans
    (add_le_add_right hEc _)

 
theorem markov_heat_cdf_le_step
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (Y : ℂ → Ω → ℝ) (ξ ε M ζ : ℝ) (a : ℝ≥0∞)
    (hprob : P {ω | ∃ z ∈ LQGMetric.Blueprint.closedUnitSquare,
      M < |LQGMetric.heatMollify ε (h ω) z - Y z ω|} ≤ ENNReal.ofReal ζ) :
    P {ω | LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
      (LQGMetric.DDDF.rectAB 1 1) ≤ a} ≤
    P {ω | LQGMetric.DDDF.rectLen ξ (LQGMetric.heatMollify ε (h ω))
      (LQGMetric.DDDF.rectAB 1 1) ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) * a} + ENNReal.ofReal ζ := by
  let E : Set Ω := {ω | ¬∃ z ∈ LQGMetric.Blueprint.closedUnitSquare,
    M < |LQGMetric.heatMollify ε (h ω) z - Y z ω|}
  have hEc : P Eᶜ ≤ ENNReal.ofReal ζ := by
    simpa only [E, Set.compl_ofPred, not_not] using hprob
  have hgood : ∀ ω ∈ E,
      LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
        (LQGMetric.DDDF.rectAB 1 1) ≤ a →
      LQGMetric.DDDF.rectLen ξ (LQGMetric.heatMollify ε (h ω))
        (LQGMetric.DDDF.rectAB 1 1) ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) * a := by
    intro ω hω ha
    apply rectLen_le_exp_of_abs_sub_le ξ M _ _ a ?_ ha
    intro z hz
    exact le_of_not_gt (fun hgt => hω ⟨z, hz, by simpa only [abs_sub_comm] using hgt⟩)
  exact (cdf_le_le_of_good_event P _ _ E a
    (ENNReal.ofReal (Real.exp (|ξ| * M)) * a) hgood).trans
    (add_le_add_right hEc _)

 

theorem p29_zeroBoundary_cdf_lt_step
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P']
    {Xh : LQGMetric.BddOn
      (LQGMetric.HeatSq.sqOpens (-1) 3 : Set ℂ) → Ω → ℝ}
    {Xh' : LQGMetric.BddOn
      (LQGMetric.HeatSq.sqOpens (-1) 3 : Set ℂ) → Ω' → ℝ}
    (hX : LQGMetric.IsZBGFFProcessExt (LQGMetric.HeatSq.sqOpens (-1) 3) Xh P)
    (hX' : LQGMetric.IsZBGFFProcessExt (LQGMetric.HeatSq.sqOpens (-1) 3) Xh' P')
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 2))
    {Y : ℂ → Ω → ℝ} {Y' : ℂ → Ω' → ℝ}
    (hY : LQGMetric.Blueprint.IsContVersion
      (fun z => Xh (LQGMetric.Blueprint.heatBdd
        (LQGMetric.HeatSq.sqOpens (-1) 3) (t / 2) z)) Y P)
    (hY' : LQGMetric.Blueprint.IsContVersion
      (fun z => Xh' (LQGMetric.Blueprint.heatBdd
        (LQGMetric.HeatSq.sqOpens (-1) 3) (t / 2) z)) Y' P')
    (W : LQGMetric.WhiteNoise.WNSpace → Ω' → ℝ)
    (hW : LQGMetric.WhiteNoise.IsWhiteNoise P' W)
    (ξ x : ℝ) (hx : 0 < x)
    (htail : P' {ω | ENNReal.ofReal x ≤
      ⨆ z ∈ LQGMetric.HeatSq.sqOpen (-1 / 2) 2,
        ENNReal.ofReal
          |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω|} ≤
      ENNReal.ofReal (1 / 16)) (a : ℝ≥0∞) :
    P {ω | LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
      (LQGMetric.DDDF.rectAB 1 1) < a} ≤
    P' {ω | LQGMetric.DDDF.rectLen ξ
      (fun z => LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω)
      (LQGMetric.DDDF.rectAB 1 1) <
      ENNReal.ofReal (Real.exp (|ξ| * x)) * a} + ENNReal.ofReal (1 / 16) := by
  let Z : Ω' → ℝ≥0∞ := fun ω =>
    LQGMetric.DDDF.rectLen ξ
      (fun z => LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω)
      (LQGMetric.DDDF.rectAB 1 1)
  let Yc : Ω' → ℝ≥0∞ := fun ω =>
    LQGMetric.DDDF.rectLen ξ (fun z => Y' z ω) (LQGMetric.DDDF.rectAB 1 1)
  let E : Set Ω' := {ω | (⨆ z ∈ LQGMetric.HeatSq.sqOpen (-1 / 2) 2,
    ENNReal.ofReal |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω|) <
      ENNReal.ofReal x}
  have hEc : P' Eᶜ ≤ ENNReal.ofReal (1 / 16) := by
    simpa only [E, Set.compl_ofPred, not_lt] using htail
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
  have hsqrt_le : Real.sqrt t ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith [ht.2]
  have hφ := LQGMetric.DDDF.isPhiVersion_phiVer hW hsqrt hsqrt_le
  have hgood : ∀ ω ∈ E, Yc ω < a →
      Z ω < ENNReal.ofReal (Real.exp (|ξ| * x)) * a := by
    intro ω hω hωa
    let fY : C(ℂ, ℝ) := ⟨fun z => Y' z ω, hY'.1 ω⟩
    let fφ : C(ℂ, ℝ) :=
      ⟨fun z => LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω, hφ.cont ω⟩
    have hsq : ∀ z ∈ unitSquare, |fY z - fφ z| ≤ x := by
      intro z hz
      have hzU : z ∈ LQGMetric.HeatSq.sqOpen (-1 / 2) 2 := by
        rcases hz with ⟨h₁, h₂, h₃, h₄⟩
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      have hzsup : ENNReal.ofReal
          |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω| ≤
          ⨆ z ∈ LQGMetric.HeatSq.sqOpen (-1 / 2) 2,
            ENNReal.ofReal
              |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω| :=
        le_iSup₂ (f := fun z (_ : z ∈ LQGMetric.HeatSq.sqOpen (-1 / 2) 2) =>
          ENNReal.ofReal
            |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω|) z hzU
      have hreal : |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω| < x :=
        (ENNReal.ofReal_lt_ofReal_iff hx).1 (hzsup.trans_lt hω)
      simpa only [fY, fφ, ContinuousMap.coe_mk, abs_sub_comm] using hreal.le
    have hlt := lfppCrossingLength_lt_exp_of_abs_sub_le ξ x fY fφ a hsq
      (by simpa only [fY, Yc, lfppCrossingLength_eq_rectLen,
        ContinuousMap.coe_mk] using hωa)
    simpa only [fφ, Z, lfppCrossingLength_eq_rectLen,
      ContinuousMap.coe_mk] using hlt
  have hstep := cdf_lt_le_of_good_event P' Yc Z E a
    (ENNReal.ofReal (Real.exp (|ξ| * x)) * a) hgood
  have hlaw := map_rectLen_heat_eq hX hX' hY hY' ξ
  have hYm : Measurable (fun ω => LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
      (LQGMetric.DDDF.rectAB 1 1)) :=
    LQGMetric.DDDF.measurable_crossLenIn
      (LQGMetric.DDDF.rectAB 1 1).isCompact_toSet hY.1 hY.2.1
  have hY'm : Measurable Yc :=
    LQGMetric.DDDF.measurable_crossLenIn
      (LQGMetric.DDDF.rectAB 1 1).isCompact_toSet hY'.1 hY'.2.1
  have hCDF : P {ω | LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
      (LQGMetric.DDDF.rectAB 1 1) < a} = P' {ω | Yc ω < a} := by
    have he := congrArg (fun μ : Measure ℝ≥0∞ => μ (Set.Iio a)) hlaw
    rw [Measure.map_apply hYm measurableSet_Iio,
      Measure.map_apply hY'm measurableSet_Iio] at he
    exact he
  rw [hCDF]
  exact hstep.trans (add_le_add_right hEc _)

 

theorem p29_zeroBoundary_cdf_le_step
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P']
    {Xh : LQGMetric.BddOn
      (LQGMetric.HeatSq.sqOpens (-1) 3 : Set ℂ) → Ω → ℝ}
    {Xh' : LQGMetric.BddOn
      (LQGMetric.HeatSq.sqOpens (-1) 3 : Set ℂ) → Ω' → ℝ}
    (hX : LQGMetric.IsZBGFFProcessExt (LQGMetric.HeatSq.sqOpens (-1) 3) Xh P)
    (hX' : LQGMetric.IsZBGFFProcessExt (LQGMetric.HeatSq.sqOpens (-1) 3) Xh' P')
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 2))
    {Y : ℂ → Ω → ℝ} {Y' : ℂ → Ω' → ℝ}
    (hY : LQGMetric.Blueprint.IsContVersion
      (fun z => Xh (LQGMetric.Blueprint.heatBdd
        (LQGMetric.HeatSq.sqOpens (-1) 3) (t / 2) z)) Y P)
    (hY' : LQGMetric.Blueprint.IsContVersion
      (fun z => Xh' (LQGMetric.Blueprint.heatBdd
        (LQGMetric.HeatSq.sqOpens (-1) 3) (t / 2) z)) Y' P')
    (W : LQGMetric.WhiteNoise.WNSpace → Ω' → ℝ)
    (hW : LQGMetric.WhiteNoise.IsWhiteNoise P' W)
    (ξ x : ℝ) (hx : 0 < x)
    (htail : P' {ω | ENNReal.ofReal x ≤
      ⨆ z ∈ LQGMetric.HeatSq.sqOpen (-1 / 2) 2,
        ENNReal.ofReal
          |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω|} ≤
      ENNReal.ofReal (1 / 16)) (a : ℝ≥0∞) :
    P' {ω | LQGMetric.DDDF.rectLen ξ
      (fun z => LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω)
      (LQGMetric.DDDF.rectAB 1 1) ≤ a} ≤
    P {ω | LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
      (LQGMetric.DDDF.rectAB 1 1) ≤
      ENNReal.ofReal (Real.exp (|ξ| * x)) * a} + ENNReal.ofReal (1 / 16) := by
  let Z : Ω' → ℝ≥0∞ := fun ω =>
    LQGMetric.DDDF.rectLen ξ
      (fun z => LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω)
      (LQGMetric.DDDF.rectAB 1 1)
  let Yc : Ω' → ℝ≥0∞ := fun ω =>
    LQGMetric.DDDF.rectLen ξ (fun z => Y' z ω) (LQGMetric.DDDF.rectAB 1 1)
  let E : Set Ω' := {ω | (⨆ z ∈ LQGMetric.HeatSq.sqOpen (-1 / 2) 2,
    ENNReal.ofReal |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω|) <
      ENNReal.ofReal x}
  have hEc : P' Eᶜ ≤ ENNReal.ofReal (1 / 16) := by
    simpa only [E, Set.compl_ofPred, not_lt] using htail
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
  have hsqrt_le : Real.sqrt t ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith [ht.2]
  have hφ := LQGMetric.DDDF.isPhiVersion_phiVer hW hsqrt hsqrt_le
  have hgood : ∀ ω ∈ E, Z ω ≤ a →
      Yc ω ≤ ENNReal.ofReal (Real.exp (|ξ| * x)) * a := by
    intro ω hω hωa
    let fY : C(ℂ, ℝ) := ⟨fun z => Y' z ω, hY'.1 ω⟩
    let fφ : C(ℂ, ℝ) :=
      ⟨fun z => LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω, hφ.cont ω⟩
    have hsq : ∀ z ∈ unitSquare, |fY z - fφ z| ≤ x := by
      intro z hz
      have hzU : z ∈ LQGMetric.HeatSq.sqOpen (-1 / 2) 2 := by
        rcases hz with ⟨h₁, h₂, h₃, h₄⟩
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      have hzsup : ENNReal.ofReal
          |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω| ≤
          ⨆ z ∈ LQGMetric.HeatSq.sqOpen (-1 / 2) 2,
            ENNReal.ofReal
              |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω| :=
        le_iSup₂ (f := fun z (_ : z ∈ LQGMetric.HeatSq.sqOpen (-1 / 2) 2) =>
          ENNReal.ofReal
            |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω|) z hzU
      have hreal : |LQGMetric.DDDF.phiVer W P' (Real.sqrt t) 1 z ω - Y' z ω| < x :=
        (ENNReal.ofReal_lt_ofReal_iff hx).1 (hzsup.trans_lt hω)
      simpa only [fY, fφ, ContinuousMap.coe_mk, abs_sub_comm] using hreal.le
    have hcost := lfppCrossingLength_le_exp_of_abs_sub_le ξ x fY fφ hsq
    have hφle : lfppCrossingLength ξ fφ ≤ a := by
      simpa only [fφ, Z, lfppCrossingLength_eq_rectLen,
        ContinuousMap.coe_mk] using hωa
    have hYle := hcost.trans (mul_le_mul_of_nonneg_left hφle zero_le)
    simpa only [fY, Yc, lfppCrossingLength_eq_rectLen,
      ContinuousMap.coe_mk] using hYle
  have hstep := cdf_le_le_of_good_event P' Z Yc E a
    (ENNReal.ofReal (Real.exp (|ξ| * x)) * a) hgood
  have hlaw := map_rectLen_heat_eq hX hX' hY hY' ξ
  have hYm : Measurable (fun ω => LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
      (LQGMetric.DDDF.rectAB 1 1)) :=
    LQGMetric.DDDF.measurable_crossLenIn
      (LQGMetric.DDDF.rectAB 1 1).isCompact_toSet hY.1 hY.2.1
  have hY'm : Measurable Yc :=
    LQGMetric.DDDF.measurable_crossLenIn
      (LQGMetric.DDDF.rectAB 1 1).isCompact_toSet hY'.1 hY'.2.1
  have hCDF : P' {ω | Yc ω ≤ ENNReal.ofReal (Real.exp (|ξ| * x)) * a} =
      P {ω | LQGMetric.DDDF.rectLen ξ (fun z => Y z ω)
        (LQGMetric.DDDF.rectAB 1 1) ≤
          ENNReal.ofReal (Real.exp (|ξ| * x)) * a} := by
    have he := congrArg (fun μ : Measure ℝ≥0∞ => μ
      (Set.Iic (ENNReal.ofReal (Real.exp (|ξ| * x)) * a))) hlaw
    rw [Measure.map_apply hYm measurableSet_Iic,
      Measure.map_apply hY'm measurableSet_Iic] at he
    exact he.symm
  rw [← hCDF]
  exact hstep.trans (add_le_add_right hEc _)

 


theorem exists_heat_whiteNoise_cdf_bounds
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) (ξ : ℝ) :
    ∃ (M x ε₀ : ℝ), 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω')
        (W : LQGMetric.WhiteNoise.WNSpace → Ω' → ℝ),
        @IsProbabilityMeasure Ω' mΩ' P' ∧
        @LQGMetric.WhiteNoise.IsWhiteNoise Ω' mΩ' P' W ∧
        ∀ a : ℝ≥0∞,
          P {ω | LQGMetric.DDDF.rectLen ξ
            (LQGMetric.heatMollify ε (h ω))
            (LQGMetric.DDDF.rectAB 1 1) < a} ≤
          P' {ω | LQGMetric.DDDF.rectLen ξ
            (fun z => LQGMetric.DDDF.phiVer W P' (Real.sqrt (ε ^ 2)) 1 z ω)
            (LQGMetric.DDDF.rectAB 1 1) <
              ENNReal.ofReal (Real.exp (|ξ| * x)) *
                (ENNReal.ofReal (Real.exp (|ξ| * M)) * a)} +
            ENNReal.ofReal (1 / 8) ∧
          P' {ω | LQGMetric.DDDF.rectLen ξ
            (fun z => LQGMetric.DDDF.phiVer W P' (Real.sqrt (ε ^ 2)) 1 z ω)
            (LQGMetric.DDDF.rectAB 1 1) ≤ a} ≤
          P {ω | LQGMetric.DDDF.rectLen ξ
            (LQGMetric.heatMollify ε (h ω))
            (LQGMetric.DDDF.rectAB 1 1) ≤
              ENNReal.ofReal (Real.exp (|ξ| * M)) *
                (ENNReal.ofReal (Real.exp (|ξ| * x)) * a)} +
            ENNReal.ofReal (1 / 8) := by
  obtain ⟨Xh, Y, M, ε₁, hX, hY, hε₁, hprob⟩ :=
    exists_markov_heat_comparison P h hh.1
  obtain ⟨x, hx, hp29⟩ := exists_p29_fixed_threshold
  refine ⟨M, x, min ε₁ (1 / 2), lt_min hε₁ (by norm_num), fun ε hε hε₀ => ?_⟩
  have hε₁' : ε < ε₁ := hε₀.trans_le (min_le_left _ _)
  have hεhalf : ε < 1 / 2 := hε₀.trans_le (min_le_right _ _)
  have ht : ε ^ 2 ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
    constructor
    · positivity
    · nlinarith
  have ht1 : ε ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  obtain ⟨Ω', mΩ', P', Xh', W, Y', hP', hX', hW, hY', htail⟩ :=
    hp29 (ε ^ 2) ht
  letI : MeasurableSpace Ω' := mΩ'
  letI : IsProbabilityMeasure P' := hP'
  refine ⟨Ω', mΩ', P', W, hP', hW, fun a => ?_⟩
  let r₁ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * M))
  let r₂ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * x))
  have hfirst := markov_heat_cdf_lt_step P h (Y (ε ^ 2)) ξ ε M (1 / 16) a
    (hprob ε hε hε₁')
  have hsecond := p29_zeroBoundary_cdf_lt_step hX hX' ht (hY _ ht1) hY'
    W hW ξ x hx htail (r₁ * a)
  constructor
  · calc
      P {ω | LQGMetric.DDDF.rectLen ξ
          (LQGMetric.heatMollify ε (h ω))
          (LQGMetric.DDDF.rectAB 1 1) < a} ≤
        P {ω | LQGMetric.DDDF.rectLen ξ (fun z => Y (ε ^ 2) z ω)
          (LQGMetric.DDDF.rectAB 1 1) < r₁ * a} +
          ENNReal.ofReal (1 / 16) := hfirst
      _ ≤ (P' {ω | LQGMetric.DDDF.rectLen ξ
          (fun z => LQGMetric.DDDF.phiVer W P' (Real.sqrt (ε ^ 2)) 1 z ω)
          (LQGMetric.DDDF.rectAB 1 1) < r₂ * (r₁ * a)} +
          ENNReal.ofReal (1 / 16)) + ENNReal.ofReal (1 / 16) :=
        add_le_add hsecond le_rfl
      _ = P' {ω | LQGMetric.DDDF.rectLen ξ
          (fun z => LQGMetric.DDDF.phiVer W P' (Real.sqrt (ε ^ 2)) 1 z ω)
          (LQGMetric.DDDF.rectAB 1 1) < r₂ * (r₁ * a)} +
          ENNReal.ofReal (1 / 8) := by
        rw [add_assoc, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
  · have hsecond' := p29_zeroBoundary_cdf_le_step hX hX' ht (hY _ ht1) hY'
      W hW ξ x hx htail a
    have hfirst' := markov_heat_cdf_le_step P h (Y (ε ^ 2)) ξ ε M (1 / 16)
      (r₂ * a) (hprob ε hε hε₁')
    calc
      P' {ω | LQGMetric.DDDF.rectLen ξ
          (fun z => LQGMetric.DDDF.phiVer W P' (Real.sqrt (ε ^ 2)) 1 z ω)
          (LQGMetric.DDDF.rectAB 1 1) ≤ a} ≤
        P {ω | LQGMetric.DDDF.rectLen ξ (fun z => Y (ε ^ 2) z ω)
          (LQGMetric.DDDF.rectAB 1 1) ≤ r₂ * a} +
          ENNReal.ofReal (1 / 16) := hsecond'
      _ ≤ (P {ω | LQGMetric.DDDF.rectLen ξ
          (LQGMetric.heatMollify ε (h ω))
          (LQGMetric.DDDF.rectAB 1 1) ≤ r₁ * (r₂ * a)} +
          ENNReal.ofReal (1 / 16)) + ENNReal.ofReal (1 / 16) :=
        add_le_add hfirst' le_rfl
      _ = P {ω | LQGMetric.DDDF.rectLen ξ
          (LQGMetric.heatMollify ε (h ω))
          (LQGMetric.DDDF.rectAB 1 1) ≤ r₁ * (r₂ * a)} +
          ENNReal.ofReal (1 / 8) := by
        rw [add_assoc, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num


end SupercriticalLQGUniqueness.Exponent.HeatVersion
