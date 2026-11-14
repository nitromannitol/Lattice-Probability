/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundMeas at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLFPPMetricMeas
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundWitness
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4a

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

theorem laneC_um_aroundDist_lt (A E F : Set ℂ) (hA : IsOpen A) (c : ℝ≥0∞) :
    UMeasurableSet {D : ContMetric | D.aroundDist A E F < c} := by
  let R : Set (ContMetric × C(unitInterval, ℂ)) :=
    {p | range p.2 ⊆ A ∧ LQGMetric.Disconnects (range p.2) E F ∧
      p.1.len (fun t => p.2 (GM.pj t)) 0 1 < c}
  have hcar : MeasurableSet
      {p : ContMetric × C(unitInterval, ℂ) | range p.2 ⊆ A} := by
    have hopen : IsOpen {η : C(unitInterval, ℂ) | range η ⊆ A} := by
      simpa only [mapsTo_univ_iff, range_subset_iff] using
        ContinuousMap.isOpen_setOfPred_mapsTo (X := unitInterval) (Y := ℂ)
          isCompact_univ hA
    exact hopen.measurableSet.preimage measurable_snd
  have hsep : MeasurableSet
      {p : ContMetric × C(unitInterval, ℂ) |
        LQGMetric.Disconnects (range p.2) E F} := by
    have hc := (GM.isOpen_setOf_not_disconnects E F).measurableSet.compl
    have hc' : MeasurableSet {η : C(unitInterval, ℂ) |
        LQGMetric.Disconnects (range η) E F} := by
      convert hc using 1
      ext η
      simp
    exact hc'.preimage measurable_snd
  have hlen : MeasurableSet
      {p : ContMetric × C(unitInterval, ℂ) |
        p.1.len (fun t => p.2 (GM.pj t)) 0 1 < c} :=
    measurableSet_lt GM.lowerSemicontinuous_lenPath.measurable measurable_const
  have hR : MeasurableSet R := hcar.inter (hsep.inter hlen)
  have hproj : UMeasurableSet
      {D : ContMetric | ∃ η : C(unitInterval, ℂ), (D, η) ∈ R} :=
    UMeasurableSet.setOf_exists hR
  convert hproj using 1
  ext D
  constructor
  · intro h
    obtain ⟨a, b, P, hab, hcont, hcar', hsep', hlen'⟩ :=
      laneC_exists_around_witness_of_lt D A E F h
    obtain ⟨η, hη⟩ := (GM.exists_path_iff D
      (fun I l => I ⊆ A ∧ LQGMetric.Disconnects I E F ∧ l < c)).mp
        ⟨a, b, P, hab, hcont, hcar', hsep', hlen'⟩
    exact ⟨η, hη⟩
  · rintro ⟨η, hη⟩
    obtain ⟨a, b, P, hab, hcont, hcar', hsep', hlen'⟩ :=
      (GM.exists_path_iff D
        (fun I l => I ⊆ A ∧ LQGMetric.Disconnects I E F ∧ l < c)).mpr ⟨η, hη⟩
    have hle : D.aroundDist A E F ≤ D.len P a b := by
      unfold ContMetric.aroundDist
      exact iInf_le_of_le a (iInf_le_of_le b
        (iInf_le_of_le P (iInf_le_of_le hab
          (iInf_le_of_le hcont (iInf_le_of_le hcar'
            (iInf_le_of_le hsep' le_rfl))))))
    exact hle.trans_lt hlen'

theorem laneC_aemeasurable_aroundDist
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (D : Ω → ContMetric) (hD : Measurable D)
    (A E F : Set ℂ) (hA : IsOpen A) :
    AEMeasurable (fun ω => (D ω).aroundDist A E F) P := by
  have hm : @Measurable (NullMeasurableSpace Ω P) ℝ≥0∞ _ _
      (fun ω => (D ω).aroundDist A E F) := by
    apply measurable_of_Iio
    intro c
    have hpre : NullMeasurableSet
        ((fun ω => (D ω).aroundDist A E F) ⁻¹' Set.Iio c) P :=
      (laneC_um_aroundDist_lt A E F hA c).nullMeasurableSet_preimage
        hD.aemeasurable
    exact hpre
  exact (show NullMeasurable (fun ω => (D ω).aroundDist A E F) P from hm).aemeasurable

theorem laneC_sourceAround_isOpen (K m : ℕ) (b : ℤ × ℤ) :
    IsOpen (LaneCInputs.sourceAround K m b) := by
  unfold LaneCInputs.sourceAround
  exact (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const)

theorem laneC_aemeasurable_psi_aroundDist
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Qψ : PsiParams) (ξ : ℝ) (n K m : ℕ) (b : ℤ × ℤ) :
    AEMeasurable (fun ω =>
      (lfppContMetric ξ (fun z => psiMN Qψ W P 0 n z ω)
        ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
        (LaneCInputs.sourceAround K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b)) P := by
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let Y : ℂ → Ω → ℝ := psiMN Qψ W P 0 n
  have hYc : ∀ ω, Continuous fun z => Y z ω :=
    (isPsiVersion_psiMN hW (Nat.zero_le n)).cont
  have hYm : ∀ z, Measurable (Y z) :=
    (isPsiVersion_psiMN hW (Nat.zero_le n)).meas
  exact laneC_aemeasurable_aroundDist
    (fun ω => lfppContMetric ξ (fun z => Y z ω) (hYc ω))
    (laneC_measurable_lfppContMetric Y hYc hYm ξ)
    _ _ _ (laneC_sourceAround_isOpen K m b)

end SupercriticalLQGUniqueness.B2.DG20Conc
