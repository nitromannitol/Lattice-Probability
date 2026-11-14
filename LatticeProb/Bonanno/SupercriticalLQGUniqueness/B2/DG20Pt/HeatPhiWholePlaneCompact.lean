/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiWholePlaneCompact at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatWholePlaneZBVersion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiZeroBoundaryReal
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiGlueBound
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiPathComparison
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffPos

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DDDF.P29WN
  LQGMetric.DFGPS LQGMetric.WhiteNoise LQGMetric.HeatSq LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 





theorem dg20_whole_plane_heat_phi_compact_sup_tight_and_paths
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (K : Set ℂ) (_hK : IsCompact K) (hKsq : K ⊆ closedUnitSquare) :
    ∀ ζ : ℝ, 0 < ζ → ∃ M ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω')
          (W : WNSpace → Ω' → ℝ) (φ : Ω' → C(ℂ, ℝ))
          (R : Measure (Ω × C(ℂ, ℝ))),
          IsProbabilityMeasure Q ∧ IsWhiteNoise Q W ∧
          (∀ ω z, φ ω z = phiVer W Q ε 1 z ω) ∧
          IsProbabilityMeasure R ∧ R.map Prod.fst = P ∧ R.map Prod.snd = Q.map φ ∧
          R {p | ∃ z ∈ K, M < |heatMollify ε (h p.1) z - p.2 z|} ≤
            ENNReal.ofReal ζ ∧
          ∀ (ξ : ℝ) (γ : ℝ → ℂ),
            (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) →
            R {p | ¬ (
              lfppLen ξ (heatMollify ε (h p.1)) γ ≤
                ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppLen ξ (fun z => p.2 z) γ ∧
              lfppLen ξ (fun z => p.2 z) γ ≤
                ENNReal.ofReal (Real.exp (|ξ| * M)) *
                  lfppLen ξ (heatMollify ε (h p.1)) γ)} ≤ ENNReal.ofReal ζ := by
  let U : Set ℂ := sqOpen (-1 / 2) 2
  have hU : IsOpen U := isOpen_sqOpen _ _
  have hUc : IsCompact (closure U) := (isBounded_sqOpen _ _).isCompact_closure
  have hUsq : closure U ⊆
      ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ) := fun z hz => by
    obtain ⟨h1, h2, h3, h4⟩ := closure_sqOpen_subset _ _ hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hKU : K ⊆ U := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hKsq hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨Xh, Y, hX, hY, hwhole⟩ :=
    dg20_whole_plane_zero_boundary_heat_version P h hh
  obtain ⟨C, c, hC, hc, hP29⟩ :=
    dg20_zero_boundary_heat_phi_real_sup_tail U hU hUc hUsq
  intro ζ hζ
  obtain ⟨M₁, ε₁, hε₁, htail₁⟩ := hwhole (ζ / 2) (half_pos hζ)
  obtain ⟨M₂, hM₂, htail₂⟩ := exists_gauss_tail_le (C := C) hc (half_pos hζ)
  refine ⟨M₁ + M₂, min ε₁ (1 / 2), lt_min hε₁ (by norm_num), ?_⟩
  intro ε hε hε₀
  have hε₁' : ε < ε₁ := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hεhalf : ε < 1 / 2 := lt_of_lt_of_le hε₀ (min_le_right _ _)
  have hεsq : ε ^ 2 < 1 / 2 := by nlinarith
  obtain ⟨Ω', iΩ', Q, Xh', W, Y', hQ, hX', hW, hY', htail'⟩ :=
    hP29 ε hε hεsq
  letI : MeasurableSpace Ω' := iΩ'
  letI : IsProbabilityMeasure Q := hQ
  have hφ := isPhiVersion_phiVer hW hε (by linarith : ε ≤ 1)
  let φ : Ω' → C(ℂ, ℝ) := pathC (phiVer W Q ε 1) hφ.cont
  let R : Measure (Ω × C(ℂ, ℝ)) :=
    dg20GlueMeasure P Q
      (pathC (Y (ε ^ 2)) (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).1)
      (pathC Y' hY'.1) φ
      (measurable_pathC
        (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).1
        (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).2.1)
  have hlaw : P.map (pathC (Y (ε ^ 2))
      (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).1) =
      Q.map (pathC Y' hY'.1) :=
    map_pathC_heat_eq hX hX'
      (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩) hY'
  have hglue := dg20_heat_phi_glue_bound P Q K
    (fun z ω => heatMollify ε (h ω) z)
    (Y (ε ^ 2)) Y' (phiVer W Q ε 1)
    (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).1
    (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).2.1
    hY'.1 hY'.2.1 hφ.cont hφ.meas hlaw M₁ M₂
  have hA : P {ω | ∃ z ∈ K,
      M₁ < |heatMollify ε (h ω) z - Y (ε ^ 2) z ω|} ≤
      ENNReal.ofReal (ζ / 2) := by
    exact (measure_mono (by
      rintro ω ⟨z, hz, hb⟩
      exact ⟨z, hKsq hz, hb⟩)).trans (htail₁ ε hε hε₁')
  have hB : Q {ω | ∃ z ∈ K, M₂ < |Y' z ω - phiVer W Q ε 1 z ω|} ≤
      ENNReal.ofReal (ζ / 2) := by
    have hsub : {ω | ∃ z ∈ K, M₂ < |Y' z ω - phiVer W Q ε 1 z ω|} ⊆
        {ω | ENNReal.ofReal M₂ ≤ ⨆ z ∈ U,
          ENNReal.ofReal |phiVer W Q ε 1 z ω - Y' z ω|} := by
      rintro ω ⟨z, hz, hb⟩
      have hle : ENNReal.ofReal M₂ ≤
          ENNReal.ofReal |phiVer W Q ε 1 z ω - Y' z ω| := by
        rw [abs_sub_comm]
        exact ENNReal.ofReal_le_ofReal hb.le
      exact hle.trans (le_iSup_of_le z (le_iSup_of_le (hKU hz) le_rfl))
    exact (measure_mono hsub).trans
      ((htail' M₂ hM₂.le).trans (ENNReal.ofReal_le_ofReal htail₂))
  have hsup : R {p | ∃ z ∈ K,
      M₁ + M₂ < |heatMollify ε (h p.1) z - p.2 z|} ≤
      ENNReal.ofReal ζ := by
    calc
      _ ≤ P {ω | ∃ z ∈ K,
          M₁ < |heatMollify ε (h ω) z - Y (ε ^ 2) z ω|} +
          Q {ω | ∃ z ∈ K, M₂ < |Y' z ω - phiVer W Q ε 1 z ω|} := hglue
      _ ≤ ENNReal.ofReal (ζ / 2) + ENNReal.ofReal (ζ / 2) := add_le_add hA hB
      _ = ENNReal.ofReal ζ := by
        have hhalf0 : 0 ≤ ζ / 2 := (half_pos hζ).le
        rw [← ENNReal.ofReal_add hhalf0]
        congr 1
        ring
        all_goals positivity
  have hfst : R.map Prod.fst = P :=
    dg20GlueMeasure_fst P Q
      (pathC (Y (ε ^ 2)) (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).1)
      (pathC Y' hY'.1) φ
      (measurable_pathC
        (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).1
        (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).2.1)
  have hsnd : R.map Prod.snd = Q.map φ := by
    have hjoint := dg20GlueMeasure_joint P Q
      (pathC (Y (ε ^ 2)) (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).1)
      (pathC Y' hY'.1) φ
      (measurable_pathC
        (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).1
        (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).2.1)
      (measurable_pathC hY'.1 hY'.2.1)
      (measurable_pathC hφ.cont hφ.meas) hlaw
    have hj := congrArg (fun μ : Measure (C(ℂ, ℝ) × C(ℂ, ℝ)) =>
      μ.map Prod.snd) hjoint
    have hm₁ : Measurable (fun p : Ω × C(ℂ, ℝ) =>
        (pathC (Y (ε ^ 2))
          (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).1 p.1, p.2)) :=
      ((measurable_pathC
        (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).1
        (hY (ε ^ 2) ⟨sq_pos_of_pos hε, by linarith⟩).2.1).comp measurable_fst).prodMk
          measurable_snd
    have hm₂ : Measurable (fun ω : Ω' => (pathC Y' hY'.1 ω, φ ω)) :=
      (measurable_pathC hY'.1 hY'.2.1).prodMk
        (measurable_pathC hφ.cont hφ.meas)
    rw [Measure.map_map measurable_snd hm₁,
      Measure.map_map measurable_snd hm₂] at hj
    simpa only [R, Function.comp_def] using hj
  refine ⟨Ω', iΩ', Q, W, φ, R, hQ, hW,
    (fun ω z => rfl), inferInstance, hfst, hsnd, hsup, ?_⟩
  intro ξ γ hγ
  have hsub : {p : Ω × C(ℂ, ℝ) | ¬ (
      lfppLen ξ (heatMollify ε (h p.1)) γ ≤
        ENNReal.ofReal (Real.exp (|ξ| * (M₁ + M₂))) * lfppLen ξ (fun z => p.2 z) γ ∧
      lfppLen ξ (fun z => p.2 z) γ ≤
        ENNReal.ofReal (Real.exp (|ξ| * (M₁ + M₂))) *
          lfppLen ξ (heatMollify ε (h p.1)) γ)} ⊆
      {p : Ω × C(ℂ, ℝ) | ∃ z ∈ K,
        M₁ + M₂ < |heatMollify ε (h p.1) z - p.2 z|} := by
    intro p hbad
    by_contra hno
    exact hbad (dg20_heat_phi_lfppLen_compare_on_compact ξ
      (heatMollify ε (h p.1)) (fun z => p.2 z) K γ (M₁ + M₂) hγ
      (by intro z hz; exact le_of_not_gt (fun hgt => hno ⟨z, hz, hgt⟩)))
  exact (measure_mono hsub).trans hsup

end SupercriticalLQGUniqueness.B2.DG20Pt
