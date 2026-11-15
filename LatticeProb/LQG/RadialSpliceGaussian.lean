import LatticeProb.LQG.RadialVersionBrownian

/-! # Gaussian law of a radial splice -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- The splice of independent continuous pre-Brownian paths is a centered
Gaussian process with the two-sided Brownian covariance. -/
theorem twoSided_preBrownian_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B C : Ω → C(ℝ≥0, ℝ)} (hB : IsPreBrownianReal (fun t ω => B ω t) P)
    (hC : IsPreBrownianReal (fun t ω => C ω t) P)
    (hBC : IndepFun (fun ω t => B ω t) (fun ω t => C ω t) P) :
    IsGaussianProcess (fun t ω => twoSided (B ω) (C ω) t) P ∧
      (∀ t, ∫ ω, twoSided (B ω) (C ω) t ∂P = 0) ∧
      ∀ s t, cov[fun ω => twoSided (B ω) (C ω) s,
        fun ω => twoSided (B ω) (C ω) t; P] = radCov s t := by
  let N : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun b => b - ContinuousMap.const _ (b 0)
  let B₀ : Ω → C(ℝ≥0, ℝ) := fun ω => N (B ω)
  let C₀ : Ω → C(ℝ≥0, ℝ) := fun ω => N (C ω)
  have hBeq : ∀ᵐ ω ∂P, B ω = B₀ ω := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    ext t
    simp [B₀, N, hω]
  have hCeq : ∀ᵐ ω ∂P, C ω = C₀ ω := by
    filter_upwards [hC.eval_zero_ae_eq_zero] with ω hω
    ext t
    simp [C₀, N, hω]
  have hB₀ : IsPreBrownianReal (fun t ω => B₀ ω t) P :=
    hB.congr fun t => hBeq.mono fun ω h => congrArg (fun b : C(ℝ≥0, ℝ) => b t) h
  have hC₀ : IsPreBrownianReal (fun t ω => C₀ ω t) P :=
    hC.congr fun t => hCeq.mono fun ω h => congrArg (fun b : C(ℝ≥0, ℝ) => b t) h
  have hi : IndepFun (fun ω t => B₀ ω t) (fun ω t => C₀ ω t) P :=
    hBC.congr (hBeq.mono fun ω h => congrArg (fun b : C(ℝ≥0, ℝ) => ⇑b) h)
      (hCeq.mono fun ω h => congrArg (fun b : C(ℝ≥0, ℝ) => ⇑b) h)
  have hbzero : ∀ ω, B₀ ω 0 = 0 := by intro ω; simp [B₀, N]
  have hczero : ∀ ω, C₀ ω 0 = 0 := by intro ω; simp [C₀, N]
  have hsplice : ∀ ω, twoSided (B₀ ω) (C₀ ω) = twoSided (B ω) (C ω) := by
    intro ω
    ext t
    simp only [twoSided_apply, B₀, C₀, N, ContinuousMap.sub_apply,
      ContinuousMap.const_apply]
    ring
  have hg : IsGaussianProcess (fun t ω => twoSided (B ω) (C ω) t) P := by
    simpa only [hsplice] using twoSided_isGaussianProcess hB₀.isGaussianProcess
      hC₀.isGaussianProcess hi
  refine ⟨hg, ?_, ?_⟩
  · intro t
    have heq : (fun ω => twoSided (B₀ ω) (C₀ ω) t) =
        fun ω => B₀ ω t.toNNReal + C₀ ω (-t).toNNReal := by
      funext ω
      simp [twoSided_apply, hbzero, hczero]
    rw [show (fun ω => twoSided (B ω) (C ω) t) =
      (fun ω => twoSided (B₀ ω) (C₀ ω) t) from funext fun ω => by rw [hsplice],
      heq, integral_add (hB₀.integrable_eval _) (hC₀.integrable_eval _),
      hB₀.integral_eval, hC₀.integral_eval, add_zero]
  · intro s t
    simpa only [hsplice] using twoSided_covariance hB₀ hC₀ hi hbzero hczero s t

/-- A splice of an independent Brownian path with the exterior half of a
centered radial version has the same continuous-path law as that version. -/
theorem IsWholePlaneGFF.map_twoSided_exterior_eq_radialVersion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {W : Ω → C(ℝ≥0, ℝ)} (hWm : Measurable W)
    (hW : IsPreBrownianReal (fun t ω => W ω t) P) (hXW : IndepFun X W P) :
    P.map (fun ω => twoSided (W ω)
      ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) =
      P.map (fun ω => R (X ω)) := by
  let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
    ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
  have hVm : Measurable V := ContinuousMap.measurable_iff_eval.2 fun t =>
    (ContinuousMap.measurable_eval (-(t : ℝ))).comp (hRm.comp hX.measurable)
  have hV : IsPreBrownianReal (fun t ω => V ω t) P :=
    IsWholePlaneGFF.radialVersion_exterior_isPreBrownianReal hX hR
  have hpath : IndepFun (fun ω t => W ω t) (fun ω t => V ω t) P := by
    have hco : Measurable (fun b : C(ℝ≥0, ℝ) => (fun t => b t)) :=
      measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval t
    have hrev : Measurable (fun x =>
        (⟨fun t => R x (-(t : ℝ)), (R x).continuous.comp (by fun_prop)⟩ : C(ℝ≥0, ℝ))) :=
      ContinuousMap.measurable_iff_eval.2 fun t =>
        (ContinuousMap.measurable_eval (-(t : ℝ))).comp hRm
    exact hXW.symm.comp hco (hco.comp hrev)
  obtain ⟨hg, hmean, hcov⟩ := twoSided_preBrownian_gaussian hW hV hpath
  obtain ⟨hrg, hrmean, hrcov⟩ := IsWholePlaneGFF.radialVersion_gaussian hX hR
  exact map_eq_of_radCov (measurable_twoSided.comp (hWm.prodMk hVm))
    (hRm.comp hX.measurable) hg hrg hmean hrmean hcov hrcov

end LatticeProb.LQG
