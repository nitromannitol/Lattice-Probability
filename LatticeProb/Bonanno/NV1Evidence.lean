/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module NV1Evidence at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyUnif
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable
import LatticeProb.Bonanno.LQGMetric.Prob.Median

 





set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions

namespace SupercriticalLQGUniqueness

open LQGMetric (DistC IsWholePlaneGFF)

theorem isCircleAverage_old_of_exists {g : DistC} {r : Set.Ioi (0 : ℝ)} {z : ℂ}
    (h : ∃ a, IsCircleAverage g r z a) :
    IsCircleAverage g r z (LQGMetric.circleAvg g r z) := by
  obtain ⟨a, ha⟩ := h
  have heq : LQGMetric.circleAvg g r z = a := ha.limUnder_eq
  rw [heq]
  exact ha

theorem ae_isCircleAverage_old {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    ∀ᵐ ω ∂P, IsCircleAverage (h ω) r z (LQGMetric.circleAvg (h ω) r z) :=
  (LQGMetric.CircleAvg.ae_tendsto_mollAvg hh z r.2).mono
    (fun _ hω => isCircleAverage_old_of_exists hω)

theorem isNormalizedWholePlaneGFF_iff_old {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} :
    IsNormalizedWholePlaneGFF h P ↔ LQGMetric.IsNormalizedWPGFF h P := by
  constructor
  · rintro ⟨hh, h0⟩
    exact ⟨hh, h0.mono (fun _ hω => hω.limUnder_eq)⟩
  · rintro ⟨hh, h0⟩
    refine ⟨hh, ((ae_isCircleAverage_old hh ⟨1, Set.mem_Ioi.mpr one_pos⟩ 0).and h0).mono ?_⟩
    intro ω hω
    simpa only [IsCircleAverage, Subtype.coe_mk, hω.2] using hω.1

theorem exists_normalizedGFF :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P := by
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  exact ⟨Ω, mΩ, P, hP, h, isNormalizedWholePlaneGFF_iff_old.mpr hh⟩

 

theorem exists_heatVersion {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (ε : ℝ) (hε : 0 < ε) :
    ∃ X : Ω → C(ℂ, ℝ),
      (∀ᵐ ω ∂P, ∀ z : ℂ, X ω z = LQGMetric.heatMollify ε (h ω) z) ∧
      ∀ z : ℂ, ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => h ω
          (positiveHeatTrunc ⟨ε ^ 2 / 2,
            Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n)) atTop
          (𝓝 (X ω z)) := by
  classical
  let X : Ω → C(ℂ, ℝ) := fun ω =>
    if hc : Continuous (LQGMetric.heatMollify ε (h ω)) then
      ⟨LQGMetric.heatMollify ε (h ω), hc⟩ else 0
  refine ⟨X, ?_, ?_⟩
  · filter_upwards [hh.1.ae_tendstoLocallyUniformly_heatMollify ε hε.ne'] with ω hω z
    simp only [X, dif_pos hω.2, ContinuousMap.coe_mk]
  · intro z
    filter_upwards [hh.1.ae_tendstoLocallyUniformly_heatMollify ε hε.ne',
      hh.1.ae_tendsto_heatMollify ε hε.ne' z] with ω hcont hlim
    simpa only [positiveHeatTrunc, X, dif_pos hcont.2, ContinuousMap.coe_mk] using hlim

theorem lfppCrossingLength_eq_old (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    lfppCrossingLength ξ φ =
      ⨅ z ∈ LQGMetric.leftSide, ⨅ w ∈ LQGMetric.rightSide,
        LQGMetric.LFPP.lfppDOn ξ φ LQGMetric.Blueprint.closedUnitSquare z w := by
  apply le_antisymm
  · refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => le_iInf fun P => ?_
    have hpc : LQGMetric.IsPiecewiseC1Path P.1 (P.1 0) (P.1 1) :=
      ⟨rfl, rfl, P.2.1.continuousOn, P.2.1.piecewise⟩
    have hP : IsLeftRightCrossing P.1 :=
      ⟨hpc, P.2.1.source.symm ▸ hz, P.2.1.target.symm ▸ hw,
        fun t ht => P.2.2 t ht⟩
    exact iInf₂_le P.1 hP
  · refine le_iInf₂ fun P hP => ?_
    have hz : P 0 ∈ LQGMetric.leftSide := hP.2.1
    have hw : P 1 ∈ LQGMetric.rightSide := hP.2.2.1
    have hsq : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ LQGMetric.Blueprint.closedUnitSquare :=
      hP.2.2.2
    exact (iInf₂_le_of_le (P 0) hz (iInf₂_le_of_le (P 1) hw
      (iInf_le_of_le ⟨P, hP.1, hsq⟩ le_rfl)))

theorem lfppCrossingLength_eq_chain (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    lfppCrossingLength ξ φ =
      ⨅ (a : LQGMetric.LFPP.sideRat 0) (b : LQGMetric.LFPP.sideRat 1),
        ⨅ (N : ℕ)
          (q : Fin N → ↥(LQGMetric.LFPP.gaussRat ∩
            LQGMetric.Blueprint.closedUnitSquare)),
          LQGMetric.LFPP.chainCost ξ φ a b N q := by
  rw [lfppCrossingLength_eq_old,
    LQGMetric.LFPP.iInf_sides_eq φ.continuous LQGMetric.LFPP.convex_closedUnitSquare
      LQGMetric.LFPP.leftSide_subset_square LQGMetric.LFPP.rightSide_subset_square]
  refine iInf_congr fun a => iInf_congr fun b => ?_
  exact LQGMetric.LFPP.lfppDOn_eq_iInf_chain φ.continuous
    LQGMetric.LFPP.convex_closedUnitSquare inter_subset_right
    (fun x hx ρ hρ => LQGMetric.LFPP.gaussRat_square_dense hx hρ)
    (LQGMetric.LFPP.leftSide_subset_square (LQGMetric.LFPP.sideRat_subset 0 a.2))
    (LQGMetric.LFPP.rightSide_subset_square (LQGMetric.LFPP.sideRat_subset 1 b.2))

theorem lfppCrossingLength_lt_top (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    lfppCrossingLength ξ φ < ∞ := by
  let E : ℂ → ℝ := fun z => Real.exp (ξ * φ z)
  have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul φ.continuous)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hE.continuousOn
  have hB : ∀ z ∈ Metric.closedBall (0 : ℂ) ‖(1 : ℂ) - 0‖,
      Real.exp (ξ * φ z) ≤ |M| := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 := by simpa using hz
    exact (Real.le_norm_self _).trans ((hM z hz').trans (le_abs_self M))
  have h0 : (0 : ℂ) ∈ LQGMetric.leftSide := by simp [LQGMetric.leftSide]
  have h1 : (1 : ℂ) ∈ LQGMetric.rightSide := by simp [LQGMetric.rightSide]
  calc lfppCrossingLength ξ φ
      = ⨅ z ∈ LQGMetric.leftSide, ⨅ w ∈ LQGMetric.rightSide,
          LQGMetric.LFPP.lfppDOn ξ φ LQGMetric.Blueprint.closedUnitSquare z w :=
        lfppCrossingLength_eq_old ξ φ
    _ ≤ LQGMetric.LFPP.lfppDOn ξ φ LQGMetric.Blueprint.closedUnitSquare 0 1 :=
        iInf₂_le_of_le 0 h0 (iInf₂_le 1 h1)
    _ ≤ LQGMetric.LFPP.segCost ξ φ 0 1 :=
        LQGMetric.LFPP.lfppDOn_le_segCost
          LQGMetric.LFPP.convex_closedUnitSquare
          (LQGMetric.LFPP.leftSide_subset_square h0)
          (LQGMetric.LFPP.rightSide_subset_square h1)
    _ ≤ ENNReal.ofReal (|M| * ‖(1 : ℂ) - 0‖) := LQGMetric.LFPP.segCost_le hB
    _ < ∞ := ENNReal.ofReal_lt_top

theorem exists_median_of_ae_lt_top {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (L : Ω → ℝ≥0∞)
    (hL : AEMeasurable L P) (hfinite : ∀ᵐ ω ∂P, L ω < ∞) :
    ∃ m : ℝ≥0∞, IsMedian P L m := by
  let Y : Ω → ℝ := fun ω => (L ω).toReal
  have hY : AEMeasurable Y P := hL.ennreal_toReal
  letI : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY).2 inferInstance
  obtain ⟨q, hq⟩ := LQGMetric.exists_isMedian (μ := P.map Y)
  have hq0 : 0 ≤ q := by
    by_contra hn
    have hneg : q < 0 := lt_of_not_ge hn
    have hevent : {ω | Y ω ≤ q} = (∅ : Set Ω) := by
      ext ω
      have hnot : ¬ Y ω ≤ q :=
        not_le_of_gt (lt_of_lt_of_le hneg ENNReal.toReal_nonneg)
      simp only [mem_setOf_eq, mem_empty_iff_false, hnot, iff_self]
    have hmass := ((LQGMetric.isMedian_map_iff hY).1 hq).1
    rw [hevent, measure_empty] at hmass
    exact (not_le_of_gt LQGMetric.inv_two_pos') hmass
  have hlevel := (LQGMetric.isMedian_map_iff hY).1 hq
  have hlow : {ω | L ω ≤ ENNReal.ofReal q} =ᵐ[P] {ω | Y ω ≤ q} :=
    hfinite.mono fun ω hω => by
      change (L ω ≤ ENNReal.ofReal q) = (Y ω ≤ q)
      exact propext (ENNReal.le_ofReal_iff_toReal_le hω.ne hq0)
  have hupper : {ω | ENNReal.ofReal q ≤ L ω} =ᵐ[P] {ω | q ≤ Y ω} :=
    hfinite.mono fun ω hω => by
      change (ENNReal.ofReal q ≤ L ω) = (q ≤ Y ω)
      exact propext (ENNReal.ofReal_le_iff_le_toReal hω.ne)
  refine ⟨ENNReal.ofReal q, hL, ?_, ?_⟩
  · rw [measure_congr hlow]
    exact hlevel.1
  · rw [measure_congr hupper]
    exact hlevel.2

end SupercriticalLQGUniqueness
