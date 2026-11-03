/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepMoment at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepRad
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepTight
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyVar

/-!
# GM Lemma 2.7: uniform second moments of increments of the harmonic part

Own argument (see `SpatialIndepTight`; replaces the translation-invariance step of GM l. 985–986,
`literature/src/1905.00383/uniqueness-final.tex`): for the radial test functions `ψ_y = radBump δ y`,
`ψ_y − ψ_z` is mean-zero, its log-covariance is bounded by a constant `radK δ ρ` for `|y − z| ≤ ρ`
(translation invariance `GFFInv.logCov_affine` and the crude bound `abs_logCov_le`), hence
`E[G(ψ_y − ψ_z)²] ≤ radK δ ρ` for the harmonic part `G` of a Markov decomposition, uniformly in
the configuration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric

namespace LQGMetric.GM

lemma integral_radBump {δ : ℝ} (hδ : 0 ≤ δ) (x : ℂ) :
    ∫ y, radBump δ hδ x y = ∫ y, radProf δ y := by
  simp only [radBump_apply]
  exact integral_sub_right_eq_self (fun y => radProf δ y) x

/-- `ψ_y − ψ_z` as a mean-zero test function -/
def radDiff {δ : ℝ} (hδ : 0 ≤ δ) (y z : ℂ) : TestC0 :=
  ⟨radBump δ hδ y - radBump δ hδ z, by
    have hc : ∀ x, Integrable (radBump δ hδ x : ℂ → ℝ) := fun x =>
      (radBump δ hδ x).continuous.integrable_of_hasCompactSupport (radBump δ hδ x).hasCompactSupport
    show ∫ x, ((radBump δ hδ y : ℂ → ℝ) x - (radBump δ hδ z : ℂ → ℝ) x) = 0
    rw [integral_sub (hc y) (hc z), integral_radBump, integral_radBump, sub_self]⟩

lemma radDiff_apply {δ : ℝ} (hδ : 0 ≤ δ) (y z x : ℂ) :
    (radDiff hδ y z).1 x = radProf δ (x - y) - radProf δ (x - z) := rfl

/-- the uniform constant -/
def radK (δ ρ : ℝ) : ℝ :=
  (2 * expNegInvGlue (δ ^ 2)) * (2 * expNegInvGlue (δ ^ 2)) * (Real.pi * (ρ + δ) ^ 2) *
    (2 * (ρ + δ) * (Real.pi * (ρ + δ) ^ 2) + logBallConst)

/-- **`logCov(ψ_y − ψ_z) ≤ radK δ ρ` for `|y − z| ≤ ρ`** -/
theorem logCov_radDiff_le {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ) {y z : ℂ} (hyz : ‖y - z‖ ≤ ρ) :
    logCov (radDiff hδ.le y z).1 (radDiff hδ.le y z).1 ≤ radK δ ρ := by
  set f : ℂ → ℝ := fun x => radProf δ (x - (y - z)) - radProf δ x with hf
  have hfc : Continuous f := ((contDiff_radProf δ).continuous.comp (continuous_id.sub
    continuous_const)).sub (contDiff_radProf δ).continuous
  have hsupp : ∀ x, ρ + δ < ‖x‖ → f x = 0 := by
    intro x hx
    have h1 : δ < ‖x - (y - z)‖ := by
      have := norm_sub_norm_le x (y - z); linarith
    simp [hf, radProf_eq_zero hδ.le h1.le, radProf_eq_zero hδ.le (by linarith : δ ≤ ‖x‖)]
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (ρ + δ)) fun x hx => hsupp x (by
      rw [mem_closedBall, dist_zero_right, not_le] at hx; exact hx))
  have hP : Integrable (radProf δ) :=
    (contDiff_radProf δ).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) δ) fun x hx =>
        radProf_eq_zero hδ.le (by rw [mem_closedBall, dist_zero_right, not_le] at hx; exact hx.le))
  have hf0 : ∫ x, f x = 0 := by
    rw [hf, integral_sub (hP.comp_sub_right (y - z)) hP,
      integral_sub_right_eq_self (fun x => radProf δ x) (y - z), sub_self]
  have hfun : (radDiff hδ.le y z).1 = fun x => f ((x - z) / (1 : ℝ)) := by
    funext x
    rw [radDiff_apply]
    simp only [Complex.ofReal_one, div_one, hf]
    congr 2; ring
  rw [hfun, GFFInv.logCov_affine f f hfi hf0 one_pos z, one_pow, one_mul]
  have hb : ∀ x, |f x| ≤ 2 * expNegInvGlue (δ ^ 2) := fun x => by
    have h1 := radProf_le δ (x - (y - z)); have h2 := radProf_le δ x
    have h3 := radProf_nonneg δ (x - (y - z)); have h4 := radProf_nonneg δ x
    rw [abs_le]; constructor <;> simp only [hf] <;> linarith
  exact (le_abs_self _).trans (abs_logCov_le (by linarith) hb hb hsupp hsupp)

/-- **`G(ψ_y − ψ_z) ∈ L²` and `E[G(ψ_y − ψ_z)²] ≤ radK δ ρ`** for the harmonic part `G` of a Markov decomposition
`h = G + h̊` on `V ⊇ B̄(z, ρ + δ)`, `|y − z| ≤ ρ` (uniform in everything else). -/
theorem integral_sq_radDiff_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h hz G : Ω → DistC} (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hzb : IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P)
    (hind : Indep (MeasurableSpace.comap hz inferInstance) (MeasurableSpace.comap G inferInstance) P)
    (hdec : ∀ᵐ ω ∂P, h ω = G ω + hz ω) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ) {y z : ℂ}
    (hyz : ‖y - z‖ ≤ ρ) (hB : closedBall z (ρ + δ) ⊆ V) :
    MemLp (fun ω => G ω (radDiff hδ.le y z).1) 2 P ∧
      ∫ ω, (G ω (radDiff hδ.le y z).1) ^ 2 ∂P ≤ radK δ ρ := by
  set φ := (radDiff hδ.le y z).1
  have hts : tsupport (φ : ℂ → ℝ) ⊆ V := by
    refine (closure_minimal (fun x hx => ?_) isClosed_closedBall).trans hB
    by_contra hx'
    rw [mem_closedBall, dist_eq_norm, not_le] at hx'
    apply hx
    show radProf δ (x - y) - radProf δ (x - z) = 0
    have h1 : δ < ‖x - y‖ := by
      have := norm_sub_norm_le (x - z) (y - z)
      rw [sub_sub_sub_cancel_right] at this; linarith
    rw [radProf_eq_zero hδ.le h1.le, radProf_eq_zero hδ.le (by linarith), sub_zero]
  let φV : TestOn V := ⟨φ, φ.contDiff, φ.hasCompactSupport, hts⟩
  have hφ : (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φV) = φ := by
    ext x; simp [TestFunction.monoCLM_apply, φV]
  refine ⟨?_, (integral_sq_harmonicPart_le hh hzb hind hdec (radDiff hδ.le y z) φV hφ).trans
    (logCov_radDiff_le hδ hρ hyz)⟩
  have hXL : MemLp (fun ω => h ω φ) 2 P := (hh.gaussian.hasGaussianLaw_eval _).memLp_two
  have hZL : MemLp (fun ω => hz ω φ) 2 P := by
    have e : (fun ω => hz ω φ) = fun ω => restrictTo V (hz ω) φV := by
      funext ω; rw [← hφ]; rfl
    rw [e]; exact (hzb.process.gaussian.hasGaussianLaw_eval φV).memLp_two
  refine (hXL.sub hZL).ae_eq ?_
  filter_upwards [hdec] with ω hω
  simp only [Pi.sub_apply, hω, add_apply]; ring

end LQGMetric.GM
