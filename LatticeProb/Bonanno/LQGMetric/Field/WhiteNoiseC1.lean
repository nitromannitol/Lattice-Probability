/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoiseC1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseC1Proc

/-!
# A `C¹` version of DDDF's white-noise field `φ_{a,b}` (task P2-DDDFFIELD, WP-21 `C¹` part)

DDDF (arXiv:1904.08021, `tightness.tex` l. 292) use an a.s. smooth version of
`φ_{a,b}(x) = √π ∫_{a²}^{b²} ∫ p_{t/2}(x − y) W(dy, dt)` and its gradient (l. 325–345,
Prop. 3). Here, for `0 < a ≤ b`:

* `exists_C1_modification_phi`: a modification `Y` of `φ_{a,b}` with `x ↦ Y x ω` of class `C¹`
  for **every** `ω`, whose gradient `(G 0, G 1)` (`∂₁`, `∂₂`) is continuous for every `ω`, is a
  modification of `√π W(∂_e k_x)` with the differentiated kernel
  `∂_e k_x(t, y) = 1_{[a²,b²]}(t) ∂_e p_{t/2}(x − y)` (`dqKernel_zero`), and is a centred
  Gaussian process (`cov_grad`: covariance `π ⟪∂_e k_x, ∂_{e'} k_{x'}⟫`).

Proof (own argument; DDDF state smoothness without proof): Kolmogorov–Čentsov for the
difference-quotient field `D_e(x, h)` in the three parameters `(x, h)` (`WhiteNoiseC1Proc`),
`φ(x + h e) − φ(x) = h D_e(x, h)` on a countable dense set and then everywhere by continuity,
and the deterministic `hasFDerivAt_of_diffQuot` (joint continuity of the difference quotients
in `(x, h)` gives the Fréchet derivative).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

/-- **Deterministic step**: if `y(x + h) − y(x) = h d₁(x, h)` and `y(x + h i) − y(x) = h d₂(x, h)`
with `d₁, d₂` jointly continuous, then `y` has Fréchet derivative `d₁(x,0) Re + d₂(x,0) Im`. -/
theorem hasFDerivAt_of_diffQuot {y : ℂ → ℝ} {d₁ d₂ : ℂ → ℝ → ℝ}
    (h₁c : Continuous fun p : ℂ × ℝ => d₁ p.1 p.2) (h₂c : Continuous fun p : ℂ × ℝ => d₂ p.1 p.2)
    (h₁ : ∀ (x : ℂ) (h : ℝ), y (x + h • (1 : ℂ)) - y x = h * d₁ x h)
    (h₂ : ∀ (x : ℂ) (h : ℝ), y (x + h • Complex.I) - y x = h * d₂ x h) (x : ℂ) :
    HasFDerivAt y (d₁ x 0 • Complex.reCLM + d₂ x 0 • Complex.imCLM) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have t1 : Tendsto (fun w : ℂ => d₁ x w.re) (𝓝 0) (𝓝 (d₁ x 0)) := by
    have := ((h₁c.comp ((continuous_const : Continuous fun _ : ℂ => x).prodMk
      Complex.continuous_re)).tendsto 0)
    simpa [Function.comp_def] using this
  have t2 : Tendsto (fun w : ℂ => d₂ (x + w.re • (1 : ℂ)) w.im) (𝓝 0) (𝓝 (d₂ x 0)) := by
    have hc2 : Continuous fun w : ℂ => (x + w.re • (1 : ℂ), w.im) := by fun_prop
    have := (h₂c.comp hc2).tendsto 0
    simpa [Function.comp_def] using this
  filter_upwards [t1.eventually (Metric.ball_mem_nhds _ (half_pos hc)),
    t2.eventually (Metric.ball_mem_nhds _ (half_pos hc))] with w hw1 hw2
  rw [Real.dist_eq] at hw1 hw2
  have hw : x + w = (x + w.re • (1 : ℂ)) + w.im • Complex.I := by
    simp only [Complex.real_smul, mul_one]
    rw [add_assoc, Complex.re_add_im]
  have e : y (x + w) - y x - (d₁ x 0 • Complex.reCLM + d₂ x 0 • Complex.imCLM) w =
      w.re * (d₁ x w.re - d₁ x 0) + w.im * (d₂ (x + w.re • (1 : ℂ)) w.im - d₂ x 0) := by
    rw [hw]
    have a1 := h₂ (x + w.re • (1 : ℂ)) w.im
    have a2 := h₁ x w.re
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
    linarith
  rw [e, Real.norm_eq_abs]
  have hre := Complex.abs_re_le_norm w
  have him := Complex.abs_im_le_norm w
  calc |w.re * (d₁ x w.re - d₁ x 0) + w.im * (d₂ (x + w.re • (1 : ℂ)) w.im - d₂ x 0)|
      ≤ |w.re| * |d₁ x w.re - d₁ x 0| + |w.im| * |d₂ (x + w.re • (1 : ℂ)) w.im - d₂ x 0| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ ‖w‖ * (c / 2) + ‖w‖ * (c / 2) := by gcongr
    _ = c * ‖w‖ := by ring

theorem contDiff_of_diffQuot {y : ℂ → ℝ} {d₁ d₂ : ℂ → ℝ → ℝ}
    (h₁c : Continuous fun p : ℂ × ℝ => d₁ p.1 p.2) (h₂c : Continuous fun p : ℂ × ℝ => d₂ p.1 p.2)
    (h₁ : ∀ (x : ℂ) (h : ℝ), y (x + h • (1 : ℂ)) - y x = h * d₁ x h)
    (h₂ : ∀ (x : ℂ) (h : ℝ), y (x + h • Complex.I) - y x = h * d₂ x h) :
    ContDiff ℝ 1 y ∧ ∀ x, fderiv ℝ y x = d₁ x 0 • Complex.reCLM + d₂ x 0 • Complex.imCLM := by
  have hD := hasFDerivAt_of_diffQuot h₁c h₂c h₁ h₂
  have hf : ∀ x, fderiv ℝ y x = d₁ x 0 • Complex.reCLM + d₂ x 0 • Complex.imCLM :=
    fun x => (hD x).fderiv
  refine ⟨contDiff_one_iff_fderiv.2 ⟨fun x => (hD x).differentiableAt, ?_⟩, hf⟩
  rw [show fderiv ℝ y = fun x => d₁ x 0 • Complex.reCLM + d₂ x 0 • Complex.imCLM from funext hf]
  exact ((h₁c.comp (continuous_id.prodMk continuous_const)).smul continuous_const).add
    ((h₂c.comp (continuous_id.prodMk continuous_const)).smul continuous_const)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- a.s., for all `(x, h)`: `Y(x + h e) − Y(x) = h D(x, h)` for continuous versions. -/
lemma ae_forall_diffQuot (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {e : ℂ}
    (he : ‖e‖ ≤ 1) {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hY : ∀ x, (fun ω => Y x ω) =ᵐ[P] phi W a b x) {D : ℂ → ℝ → Ω → ℝ}
    (hDc : ∀ ω, Continuous fun p : ℂ × ℝ => D p.1 p.2 ω)
    (hD : ∀ x h, (fun ω => D x h ω) =ᵐ[P] dphi W a b e x h) :
    ∀ᵐ ω ∂P, ∀ (x : ℂ) (h : ℝ), Y (x + h • e) ω - Y x ω = h * D x h ω := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (ℂ × ℝ)
  have := hSc.to_subtype
  have hS : ∀ᵐ ω ∂P, ∀ s : S, Y (s.1.1 + s.1.2 • e) ω - Y s.1.1 ω = s.1.2 * D s.1.1 s.1.2 ω := by
    refine ae_all_iff.mpr fun s => ?_
    filter_upwards [hY (s.1.1 + s.1.2 • e), hY s.1.1, hD s.1.1 s.1.2,
      phi_add_smul_sub_ae hW ha hab he s.1.1 s.1.2] with ω h1 h2 h3 h4
    rw [h1, h2, h3]; exact h4
  filter_upwards [hS] with ω hω
  intro x h
  have hc1 : Continuous fun p : ℂ × ℝ => Y (p.1 + p.2 • e) ω - Y p.1 ω :=
    ((hYc ω).comp (continuous_fst.add (continuous_snd.smul continuous_const))).sub
      ((hYc ω).comp continuous_fst)
  have hc2 : Continuous fun p : ℂ × ℝ => p.2 * D p.1 p.2 ω := continuous_snd.mul (hDc ω)
  exact congrFun (Continuous.ext_on hSd hc1 hc2 fun p hp => hω ⟨p, hp⟩) (x, h)

/-- The two coordinate directions `e₀ = 1`, `e₁ = i`. -/
def unitDir : Fin 2 → ℂ := ![1, Complex.I]

lemma norm_unitDir_le (j : Fin 2) : ‖unitDir j‖ ≤ 1 := by
  fin_cases j <;> simp [unitDir]

/-- **`C¹` version of `φ_{a,b}`** (DDDF l. 292, `C¹` part; WP-21). -/
theorem exists_C1_modification_phi (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ∃ (Y : ℂ → Ω → ℝ) (G : Fin 2 → ℂ → Ω → ℝ),
      (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W a b x) ∧ (∀ x, Measurable (Y x)) ∧
      (∀ ω, ContDiff ℝ 1 fun x => Y x ω) ∧
      (∀ ω x, fderiv ℝ (fun x => Y x ω) x = G 0 x ω • Complex.reCLM + G 1 x ω • Complex.imCLM) ∧
      (∀ j ω, Continuous fun x => G j x ω) ∧ (∀ j x, Measurable (G j x)) ∧
      (∀ j x, (fun ω => G j x ω) =ᵐ[P] dphi W a b (unitDir j) x 0) ∧
      ∀ j, IsGaussianProcess (G j) P := by
  obtain ⟨Y₀, hY₀c, hY₀m, hY₀⟩ := exists_continuous_modification_phi hW ha hab
  obtain ⟨D₁, hD₁c, hD₁m, hD₁⟩ :=
    exists_continuous_modification_dphi hW ha hab (norm_unitDir_le 0)
  obtain ⟨D₂, hD₂c, hD₂m, hD₂⟩ :=
    exists_continuous_modification_dphi hW ha hab (norm_unitDir_le 1)
  have r1 := ae_forall_diffQuot hW ha hab (norm_unitDir_le 0) hY₀c hY₀ hD₁c hD₁
  have r2 := ae_forall_diffQuot hW ha hab (norm_unitDir_le 1) hY₀c hY₀ hD₂c hD₂
  -- a measurable full-measure set on which both relations hold
  set B : Set Ω := {ω | ¬ ((∀ (x : ℂ) (h : ℝ), Y₀ (x + h • unitDir 0) ω - Y₀ x ω = h * D₁ x h ω) ∧
    ∀ (x : ℂ) (h : ℝ), Y₀ (x + h • unitDir 1) ω - Y₀ x ω = h * D₂ x h ω)} with hB
  set Gs : Set Ω := (toMeasurable P B)ᶜ with hGs
  have hGm : MeasurableSet Gs := (measurableSet_toMeasurable _ _).compl
  have hGae : ∀ᵐ ω ∂P, ω ∈ Gs := by
    rw [ae_iff]
    simp only [hGs, mem_compl_iff, not_not, Set.ofPred_mem_eq, measure_toMeasurable]
    exact ae_iff.mp (r1.and r2)
  have hGt : ∀ ω ∈ Gs, (∀ (x : ℂ) (h : ℝ), Y₀ (x + h • unitDir 0) ω - Y₀ x ω = h * D₁ x h ω) ∧
      ∀ (x : ℂ) (h : ℝ), Y₀ (x + h • unitDir 1) ω - Y₀ x ω = h * D₂ x h ω := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P B h)
  set Y : ℂ → Ω → ℝ := fun x ω => Gs.indicator (Y₀ x) ω with hY
  set E₁ : ℂ → ℝ → Ω → ℝ := fun x h ω => Gs.indicator (D₁ x h) ω with hE₁
  set E₂ : ℂ → ℝ → Ω → ℝ := fun x h ω => Gs.indicator (D₂ x h) ω with hE₂
  have hE₁c : ∀ ω, Continuous fun p : ℂ × ℝ => E₁ p.1 p.2 ω := fun ω => by
    by_cases hω : ω ∈ Gs
    · simp only [hE₁, indicator_of_mem hω]; exact hD₁c ω
    · simp only [hE₁, indicator_of_notMem hω]; exact continuous_const
  have hE₂c : ∀ ω, Continuous fun p : ℂ × ℝ => E₂ p.1 p.2 ω := fun ω => by
    by_cases hω : ω ∈ Gs
    · simp only [hE₂, indicator_of_mem hω]; exact hD₂c ω
    · simp only [hE₂, indicator_of_notMem hω]; exact continuous_const
  have hC : ∀ ω, ContDiff ℝ 1 (fun x => Y x ω) ∧ ∀ x, fderiv ℝ (fun x => Y x ω) x =
      E₁ x 0 ω • Complex.reCLM + E₂ x 0 ω • Complex.imCLM := by
    intro ω
    refine contDiff_of_diffQuot (y := fun x => Y x ω) (d₁ := fun x h => E₁ x h ω)
      (d₂ := fun x h => E₂ x h ω) (hE₁c ω) (hE₂c ω) (fun x h => ?_) (fun x h => ?_)
    · by_cases hω : ω ∈ Gs
      · simp only [hY, hE₁, indicator_of_mem hω]; exact (hGt ω hω).1 x h
      · simp [hY, hE₁, indicator_of_notMem hω]
    · by_cases hω : ω ∈ Gs
      · simp only [hY, hE₂, indicator_of_mem hω]; exact (hGt ω hω).2 x h
      · simp [hY, hE₂, indicator_of_notMem hω]
  set G : Fin 2 → ℂ → Ω → ℝ := ![fun x ω => E₁ x 0 ω, fun x ω => E₂ x 0 ω] with hG
  have hGae' : ∀ j x, (fun ω => G j x ω) =ᵐ[P] dphi W a b (unitDir j) x 0 := by
    intro j x
    fin_cases j
    · filter_upwards [hGae, hD₁ x 0] with ω h1 h2
      simp only [hG, hE₁, Fin.zero_eta, Matrix.cons_val_zero, indicator_of_mem h1]; exact h2
    · filter_upwards [hGae, hD₂ x 0] with ω h1 h2
      simp only [hG, hE₂, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        indicator_of_mem h1]
      exact h2
  refine ⟨Y, G, fun x => ?_, fun x => (hY₀m x).indicator hGm, fun ω => (hC ω).1,
    fun ω x => (hC ω).2 x, fun j ω => ?_, fun j x => ?_, hGae', fun j => ?_⟩
  · filter_upwards [hGae, hY₀ x] with ω h1 h2
    simp only [hY, indicator_of_mem h1]; exact h2
  · fin_cases j
    · exact (hE₁c ω).comp (continuous_id.prodMk continuous_const)
    · exact (hE₂c ω).comp (continuous_id.prodMk continuous_const)
  · fin_cases j
    · exact (hD₁m x 0).indicator hGm
    · exact (hD₂m x 0).indicator hGm
  · have h0 : IsGaussianProcess (fun x => dphi W a b (unitDir j) x 0) P := by
      have := (hW.isGaussianProcess_comp fun x => dqKernelL2 a b (unitDir j) x 0).smul
        (fun _ => Real.sqrt Real.pi)
      exact this
    exact h0.congr fun x => (hGae' j x).symm

end WhiteNoise
end LQGMetric
