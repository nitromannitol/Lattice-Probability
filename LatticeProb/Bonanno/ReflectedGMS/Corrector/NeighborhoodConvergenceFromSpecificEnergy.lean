/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.NeighborhoodConvergenceFromSpecificEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedBallEnergyConvergence
import LatticeProb.Bonanno.ReflectedGMS.Corrector.DiscreteBallPoincare

/-!
# `hnbr` from `hspec`: neighbourhood convergence by the random-constant Poincaré argument

`HarmonicCoordinateAssembly.MarkedNeighborhoodConvergence` (`hnbr`) is the open input of the
harmonic-coordinate assembly asserting that, along the full sequence, the graph-neighbourhood
errors

`sup_{v ∈ B(H_0, radius+1)} min(1, |φ_m(v) − φ_m(H_0) − Φ(v)|)`

tend to zero in probability.  This module **derives** it from `hspec`
(`MarkedSpecificEnergyConvergence`), with the environment hypotheses of the main theorem, the
measurability input `hmeas`, and the every-stage covariance input of
`Corrector/MarkedBallEnergyConvergence`.

## The route

1. `MarkedBallEnergyConvergence.markedBallEnergyConvergence_of_specificEnergyConvergence` — the
   specific-energy density of `φ_m − Φ` is small **uniformly on the graph ball** in probability.
2. The additive constant: `normalizedPhi F D r m v = φ_m(v) − φ_m(r)` definitionally, so the
   field inside the neighbourhood error is `g = (φ_m − Φ) − φ_m(r)`.  Its specific-energy
   density is that of `φ_m − Φ` (`DiscreteBallPoincare.specificEnergyDensity_sub_const`), and it
   vanishes at the root because the marked limit does: `Φ(r)` is the diagonal value of a
   difference field once the base label is the root label
   (`HarmonicCoordinateAssembly.baseLabel_eq_of_rootAt`).
3. `DiscreteBallPoincare.iSup_min_one_norm_le_of_ball` with the **random constants**
   `a = κ⁻¹ = M` read off `MarkedBallEnergyGeometry.rootedGeom` (cell areas and inverse
   conductances in the ball): on `{rootedGeom ≤ M}` a ball energy below
   `ρ₀ = δ² / (2 M² (radius+1)²)` forces the neighbourhood error below `δ`
   (`markedGraphNeighborhoodError_lt`).
4. `P(error ≥ δ) ≤ P(rootedGeom > M) + P(ball energy ≥ ρ₀)`: the first term is small for large
   `M` (`MarkedBallEnergyGeometry.tendsto_measure_rootedGeom_gt`), the second tends to zero for
   each fixed `M` by step 1.

## Which branch carries the content

The `(rootAt …).elim 0` head of the error is **not** used to make anything vacuous: off the
boundary mask (almost surely, by mass transport) the root exists, and the whole Poincaré
argument runs on the `some r` branch.  The graph ball always contains the root, and the random
constants are finite at every environment, so no emptiness or infinity is exploited.

## The corollary

`harmonicCoordinateConclusions_of_eight_inputs` is the assembly's reduction with `hnbr`
discharged (on top of `hdens`, already discharged by
`MarkedDensityMeasurabilityProducer`) and with `hcov` replaced by its every-stage form.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.NeighborhoodConvergenceFromSpecificEnergy

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open MarkedBallEnergyGeometry MarkedBallEnergyConvergence

/-! ### The deterministic step -/

/-- The real inequality behind the energy threshold `ρ₀ = δ² / (2 M² (R+1)²)`. -/
theorem poincareConstant_lt (R M : ℕ) (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ) :
    (R : ℝ) * Real.sqrt (2 * (δ ^ 2 / (2 * (M : ℝ) ^ 2 * ((R : ℝ) + 1) ^ 2)) * (M : ℝ)
      / (1 / (M : ℝ))) < δ := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM0 : (M : ℝ) ≠ 0 := hM'.ne'
  have hR1 : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  have hR0 : (R : ℝ) + 1 ≠ 0 := hR1.ne'
  have hsq : 2 * (δ ^ 2 / (2 * (M : ℝ) ^ 2 * ((R : ℝ) + 1) ^ 2)) * (M : ℝ) / (1 / (M : ℝ))
      = (δ / ((R : ℝ) + 1)) ^ 2 := by
    field_simp
  rw [hsq, Real.sqrt_sq (div_nonneg hδ.le hR1.le), mul_div_assoc', div_lt_iff₀ hR1]
  nlinarith

theorem markedGraphNeighborhoodError_nonneg (ms : ℕ → ℕ) (radius m : ℕ)
    (ω : MarkedEnvironment) : 0 ≤ markedGraphNeighborhoodError ms radius m ω := by
  unfold markedGraphNeighborhoodError
  cases hr : rootAt (decode ω.1) 0 with
  | none => exact le_rfl
  | some r => exact Real.iSup_nonneg fun v => le_min zero_le_one (norm_nonneg _)

/-- The marked limit vanishes at the root: at the root label it is a diagonal value of the
marked difference field. -/
theorem markedPotential_root_eq_zero (ms : ℕ → ℕ) {ω : MarkedEnvironment} {r : Vertex ω.1.val}
    (hr : rootAt (decode ω.1) 0 = some r) : markedPotential ms ω r = 0 := by
  show markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) r.val) = 0
  rw [baseLabel_eq_of_rootAt hr]
  exact (isDifferenceField_markedDifferenceField ms ω).1 r

/-- **The pathwise Poincaré step.**  Where the geometric constant is at most `M` and the ball
energy of `φ_m − Φ` is below `ρ₀`, the neighbourhood error is below `δ` as soon as
`radius · √(2 ρ₀ M / M⁻¹) < δ`. -/
theorem markedGraphNeighborhoodError_lt (ms : ℕ → ℕ) (m R M : ℕ) (hM : 0 < M) {ρ₀ δ : ℝ}
    (hρ₀ : 0 ≤ ρ₀) (hconst : (R : ℝ) * Real.sqrt (2 * ρ₀ * (M : ℝ) / (1 / (M : ℝ))) < δ)
    (hδ : 0 < δ) {ω : MarkedEnvironment} (hgeom : rootedGeom R ω.1 ≤ M)
    (hball : markedBallEnergyError ms R m ω < ENNReal.ofReal ρ₀) :
    markedGraphNeighborhoodError ms R m ω < δ := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  unfold markedGraphNeighborhoodError
  cases hr : rootAt (decode ω.1) 0 with
  | none => exact hδ
  | some r =>
      show (⨆ v : (decode ω.1).graph.toSimpleGraph.ball r ((R + 1 : ℕ) : ℕ∞),
          min 1 ‖normalizedPhi (decode ω.1) ω.2 r m v.val - markedPotential ms ω v.val‖) < δ
      have hgr : normalizedPhi (decode ω.1) ω.2 r m r - markedPotential ms ω r = 0 := by
        rw [normalizedPhi_root, markedPotential_root_eq_zero ms hr, sub_zero]
      have hfun : (fun x : Vertex ω.1.val =>
            normalizedPhi (decode ω.1) ω.2 r m x - markedPotential ms ω x)
          = fun x : Vertex ω.1.val =>
            (phi (decode ω.1) ω.2 m x - markedPotential ms ω x) - phi (decode ω.1) ω.2 m r := by
        funext x
        simp only [normalizedPhi]
        abel
      have hρ : ∀ x ∈ (decode ω.1).graph.toSimpleGraph.ball r ((R + 1 : ℕ) : ℕ∞),
          RootDensities.specificEnergyDensity (decode ω.1)
            (fun x : Vertex ω.1.val =>
              normalizedPhi (decode ω.1) ω.2 r m x - markedPotential ms ω x) x
            ≤ ENNReal.ofReal ρ₀ := by
        intro x hx
        have hEq : RootDensities.specificEnergyDensity (decode ω.1)
              (fun x : Vertex ω.1.val =>
                normalizedPhi (decode ω.1) ω.2 r m x - markedPotential ms ω x) x
            = RootDensities.specificEnergyDensity (decode ω.1)
              (fun y : Vertex ω.1.val => phi (decode ω.1) ω.2 m y - markedPotential ms ω y) x :=
          (congrArg (fun g : Vertex ω.1.val → Plane =>
              RootDensities.specificEnergyDensity (decode ω.1) g x) hfun).trans
            (DiscreteBallPoincare.specificEnergyDensity_sub_const (decode ω.1)
              (fun y : Vertex ω.1.val => phi (decode ω.1) ω.2 m y - markedPotential ms ω y)
              (phi (decode ω.1) ω.2 m r) x)
        refine hEq.trans_le (le_trans ?_ hball.le)
        unfold markedBallEnergyError
        rw [hr]
        exact le_iSup (fun v : (decode ω.1).graph.toSimpleGraph.ball r ((R + 1 : ℕ) : ℕ∞) =>
          RootDensities.specificEnergyDensity (decode ω.1)
            (fun y : Vertex ω.1.val => phi (decode ω.1) ω.2 m y - markedPotential ms ω y) v.val)
          ⟨x, hx⟩
      have ha : ∀ x ∈ (decode ω.1).graph.toSimpleGraph.ball r ((R + 1 : ℕ) : ℕ∞),
          cellArea (decode ω.1) x ≤ (M : ℝ) := by
        intro x hx
        have h1 : volume ((decode ω.1).cell x : Set Plane) ≤ (M : ℝ≥0∞) :=
          (volume_cell_le_rootedGeom hr hx).trans hgeom
        unfold cellArea
        refine ENNReal.toReal_le_of_le_ofReal hMpos.le ?_
        rw [ENNReal.ofReal_natCast]
        exact h1
      have hc : ∀ x ∈ (decode ω.1).graph.toSimpleGraph.ball r ((R + 1 : ℕ) : ℕ∞),
          ∀ y ∈ (decode ω.1).graph.toSimpleGraph.ball r ((R + 1 : ℕ) : ℕ∞),
          (decode ω.1).graph.toSimpleGraph.Adj x y →
            1 / (M : ℝ) ≤ (decode ω.1).graph.c x y := by
        intro x hx y _ hadj
        have hpos : 0 < ω.1.val.2 x.val y.val := hadj
        have h1 : invConductance ω.1 x.val y.val ≤ (M : ℝ≥0∞) :=
          (invConductance_le_rootedGeom hr hx y.val).trans hgeom
        unfold invConductance at h1
        rw [if_pos hpos, ← ENNReal.ofReal_natCast] at h1
        have h2 : (ω.1.val.2 x.val y.val)⁻¹ ≤ (M : ℝ) :=
          (ENNReal.ofReal_le_ofReal_iff hMpos.le).1 h1
        rw [one_div]
        exact (inv_le_comm₀ hpos hMpos).1 h2
      have hκ : (0 : ℝ) < 1 / (M : ℝ) := by positivity
      have hmain := DiscreteBallPoincare.iSup_min_one_norm_le_of_ball (decode ω.1)
        (fun x : Vertex ω.1.val =>
          normalizedPhi (decode ω.1) ω.2 r m x - markedPotential ms ω x)
        r R hgr hρ₀ hκ hρ ha hc
      exact lt_of_le_of_lt hmain hconst

/-! ### The theorem -/

/-- **`hnbr` from `hspec`.**  The open input `MarkedNeighborhoodConvergence` of the
harmonic-coordinate assembly follows from `MarkedSpecificEnergyConvergence`, the environment
hypotheses `hν` and `hFE` of the main theorem, the measurability input `hmeas`, and the
every-stage covariance input `ApproximantGradientCovariantAtEveryStage`. -/
theorem markedNeighborhoodConvergence_of_specificEnergyConvergence (ν : Measure Env)
    [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariantAtEveryStage)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    MarkedNeighborhoodConvergence ν ms := by
  have hball :=
    markedBallEnergyConvergence_of_specificEnergyConvergence ν hν hFE ms hmeas hcov hspec
  intro R
  refine tendstoInMeasure_of_ne_top fun ε hε hεtop => ?_
  have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  have htail := tendsto_measure_rootedGeom_gt (ν.prod gridLaw) measurable_fst R
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 htail (η / 2) hη2)
  obtain ⟨M, hMpos, hM⟩ : ∃ M : ℕ, 0 < M ∧
      (ν.prod gridLaw) {ω : MarkedEnvironment | (M : ℝ≥0∞) < rootedGeom R ω.1} ≤ η / 2 :=
    ⟨max M₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right M₀ 1), hM₀ _ (le_max_left M₀ 1)⟩
  have hM' : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hR1 : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  obtain ⟨ρ₀, hρ₀, hconst⟩ : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      (R : ℝ) * Real.sqrt (2 * ρ₀ * (M : ℝ) / (1 / (M : ℝ))) < ε.toReal :=
    ⟨ε.toReal ^ 2 / (2 * (M : ℝ) ^ 2 * ((R : ℝ) + 1) ^ 2),
      div_pos (pow_pos hδ 2) (mul_pos (mul_pos two_pos (pow_pos hM' 2)) (pow_pos hR1 2)),
      poincareConstant_lt R M hMpos hδ⟩
  have hball' := hball R (ENNReal.ofReal ρ₀) (ENNReal.ofReal_pos.2 hρ₀)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hball' (η / 2) hη2] with m hm
  have hsubset : {ω : MarkedEnvironment | ε ≤ edist (markedGraphNeighborhoodError ms R m ω) 0}
      ⊆ {ω : MarkedEnvironment | (M : ℝ≥0∞) < rootedGeom R ω.1}
        ∪ {ω : MarkedEnvironment | ENNReal.ofReal ρ₀ ≤ markedBallEnergyError ms R m ω} := by
    intro ω hmem
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_le] at hnot
    have hlt := markedGraphNeighborhoodError_lt ms m R M hMpos hρ₀.le hconst hδ hnot.1 hnot.2
    have hnn := markedGraphNeighborhoodError_nonneg ms R m ω
    have hmem' : ε ≤ edist (markedGraphNeighborhoodError ms R m ω) 0 := hmem
    rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hmem'
    exact absurd ((ENNReal.le_ofReal_iff_toReal_le hεtop hnn).1 hmem') (not_le.2 hlt)
  calc (ν.prod gridLaw)
        {ω : MarkedEnvironment | ε ≤ edist (markedGraphNeighborhoodError ms R m ω) 0}
      ≤ (ν.prod gridLaw) ({ω : MarkedEnvironment | (M : ℝ≥0∞) < rootedGeom R ω.1}
          ∪ {ω : MarkedEnvironment | ENNReal.ofReal ρ₀ ≤ markedBallEnergyError ms R m ω}) :=
        measure_mono hsubset
    _ ≤ (ν.prod gridLaw) {ω : MarkedEnvironment | (M : ℝ≥0∞) < rootedGeom R ω.1}
        + (ν.prod gridLaw)
          {ω : MarkedEnvironment | ENNReal.ofReal ρ₀ ≤ markedBallEnergyError ms R m ω} :=
        measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hM hm
    _ = η := ENNReal.add_halves η

/-! ### The assembly reduction with `hnbr` discharged -/

/-- **The harmonic-coordinate reduction with `hnbr` discharged.**  Compared with
`MarkedDensityMeasurabilityProducer.harmonicCoordinateConclusions_of_nine_inputs`, the input
`hnbr` is gone and `hcov` is replaced by its every-stage form
`ApproximantGradientCovariantAtEveryStage` (which implies it, and which is implied by the hcov
packet's atomic input `BlockInterpolationSimilarityCovariant`).  The remaining **eight** inputs
are open; this is an implication, not a proof of the harmonic-coordinate theorem. -/
theorem harmonicCoordinateConclusions_of_eight_inputs (ν : Measure Env)
    [IsProbabilityMeasure ν] (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariantAtEveryStage)
    (hcopies : DifferenceFieldGridIndependent ν ms)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms)
    (hharm : MarkedHarmonicity ν ms) (hsub : MarkedCentroidSublinearity ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    HarmonicCoordinateConclusions ν :=
  MarkedDensityMeasurabilityProducer.harmonicCoordinateConclusions_of_nine_inputs ν hν hFE ms
    hms hmeas (approximantGradientCovariant_of_atEveryStage hcov ms) hcopies hconv hpatch hharm
    hsub (markedNeighborhoodConvergence_of_specificEnergyConvergence ν hν hFE.ne ms hmeas hcov
      hspec) hspec

end ReflectedGMS.NeighborhoodConvergenceFromSpecificEnergy
