/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.SegCombLaw at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Node `P1` (`Draft.SegCombLaw`): the law of finite families of segment averages of `h_ε`

Under `IsGFFCircleAverage h P` and for a fixed radius `ε > 0`, the random vector
`ω ↦ ((c i).avg (h ε · ω))_{i ∈ F}` has law `gaussVecLaw F (circCov ε)`.

## Strategy

* `segAvg φ a b` is the limit of the left Riemann sums `segRiemann φ a b N` for continuous `φ`
  (`tendsto_riemannSum`).  The Riemann sums of `h ε · ω` are finite linear combinations of values
  of the Gaussian process `z ↦ h ε z` (`InGSpan`), hence centered Gaussian.
* The covariance kernel `(z, w) ↦ gffCircleCov ε z ε w` is continuous
  (`continuous_gffCircleCov`).  This is proved *probabilistically*: variances of Gaussian
  variables converge under pointwise convergence (`tendsto_variance_of_hasGaussianLaw`, via
  characteristic functions), and the paths `z ↦ h ε z ω` are continuous.
* Hence the covariances of the Riemann sums (double Riemann sums of the kernel,
  `tendsto_riemannSum2`) converge to `circCov`.
* The characteristic function of every linear combination `∑ tᵢ Xᵢ` is the limit of Gaussian
  characteristic functions (dominated convergence), which identifies the law via
  `Measure.ext_of_charFun` and `charFun_multivariateGaussian`.  Positive semidefiniteness of
  `circCov` follows since it is a limit of covariance matrices.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical

namespace LQGDimension

namespace SegLaw

/-! ### Riemann sums on `[0,1]` -/

/-- Left Riemann sum `N⁻¹ ∑_{k<N} g (k/N)` of `g` over `[0,1]`. -/
def riemannSum (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, g ((k : ℝ) / N)

theorem one_div_natCast_lt {δ : ℝ} (hδ : 0 < δ) {N₀ N : ℕ} (hN₀ : 1 / δ < N₀) (hN : N₀ + 1 ≤ N) :
    1 / (N : ℝ) < δ := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have h1 : (N₀ : ℝ) < N := by exact_mod_cast (by omega : N₀ < N)
  exact (one_div_lt hNpos hδ).mpr (hN₀.trans h1)

/-- Quantitative Riemann-sum bound: if `g` oscillates by at most `η` on `[0,1]` at scale `1/N`,
the left Riemann sum is within `η` of the integral. -/
theorem abs_riemannSum_sub_integral_le {g : ℝ → ℝ} (hg : Continuous g) {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ 1 / N → |g x - g y| ≤ η) :
    |riemannSum g N - ∫ s in (0 : ℝ)..1, g s| ≤ η := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set a : ℕ → ℝ := fun k => (k : ℝ) / N with ha
  have hsplit : ∫ s in (0 : ℝ)..1, g s = ∑ k ∈ Finset.range N, ∫ s in a k..a (k + 1), g s := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hg.intervalIntegrable _ _)]
    simp [ha, hN'.ne']
  have hNne : (N : ℝ) ≠ 0 := hN'.ne'
  have hdiff : ∀ k : ℕ, a (k + 1) - a k = 1 / N := by
    intro k
    simp only [ha]
    push_cast
    ring
  have hconst : riemannSum g N = ∑ k ∈ Finset.range N, ∫ _ in a k..a (k + 1), g (a k) := by
    rw [riemannSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const, smul_eq_mul, hdiff]
    simp [ha, one_div]
  rw [hsplit, hconst, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range N, ((∫ _ in a k..a (k + 1), g (a k)) - ∫ s in a k..a (k + 1), g s)|
      ≤ ∑ k ∈ Finset.range N,
          |(∫ _ in a k..a (k + 1), g (a k)) - ∫ s in a k..a (k + 1), g s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, η * (1 / N) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : (k : ℝ) + 1 ≤ N := by
          have := Finset.mem_range.mp hk
          exact_mod_cast this
        have hab : a k ≤ a (k + 1) := by linarith [hdiff k, one_div_pos.mpr hN']
        have hk0 : 0 ≤ a k := by simp only [ha]; positivity
        have hk1 : a (k + 1) ≤ 1 := by
          simp only [ha]
          rw [div_le_one hN']
          push_cast
          linarith
        rw [← intervalIntegral.integral_sub intervalIntegrable_const (hg.intervalIntegrable _ _)]
        calc |∫ x in a k..a (k + 1), (g (a k) - g x)|
            = ‖∫ x in a k..a (k + 1), (g (a k) - g x)‖ := (Real.norm_eq_abs _).symm
          _ ≤ η * |a (k + 1) - a k| :=
              intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
          _ = η * (1 / N) := by rw [hdiff, abs_of_pos (one_div_pos.mpr hN')]
        rw [Set.uIoc_of_le hab] at hx
        rw [Real.norm_eq_abs]
        refine hη (a k) ⟨hk0, by linarith [hx.1, hx.2]⟩ x
          ⟨by linarith [hx.1], by linarith [hx.2]⟩ ?_
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]
        linarith [hx.2, hdiff k]
    _ = η := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

/-- **Riemann sums converge** for continuous integrands. -/
theorem tendsto_riemannSum {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (riemannSum g) atTop (𝓝 (∫ s in (0 : ℝ)..1, g s)) := by
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, hδ'⟩ := huc (η / 2) (half_pos hη)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / δ)
  refine ⟨N₀ + 1, fun N hN => ?_⟩
  have hNpos : 0 < N := by omega
  have hNδ := one_div_natCast_lt hδ hN₀ hN
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (abs_riemannSum_sub_integral_le hg hNpos fun x hx y hy hxy => ?_)
    (half_lt_self hη)
  have := hδ' x hx y hy (by rw [Real.dist_eq]; linarith)
  rw [Real.dist_eq] at this
  exact this.le

/-- Double left Riemann sum of `f` over `[0,1]²`. -/
def riemannSum2 (f : ℝ → ℝ → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * (N : ℝ)⁻¹ *
    ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, f ((k : ℝ) / N) ((l : ℝ) / N)

/-- **Double Riemann sums converge** to the iterated integral for jointly continuous integrands. -/
theorem tendsto_riemannSum2 {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) :
    Tendsto (riemannSum2 f) atTop (𝓝 (∫ s in (0 : ℝ)..1, ∫ s' in (0 : ℝ)..1, f s s')) := by
  set G : ℝ → ℝ := fun s => ∫ s' in (0 : ℝ)..1, f s s' with hG
  have hGc : Continuous G :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 1
  have huc := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, hδ'⟩ := huc (η / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / δ)
  refine ⟨N₀ + 1, fun N hN => ?_⟩
  have hNpos : 0 < N := by omega
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hNne : (N : ℝ) ≠ 0 := hN'.ne'
  have hNδ := one_div_natCast_lt hδ hN₀ hN
  have hrow : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1,
      |y - z| ≤ 1 / N → |f x y - f x z| ≤ η / 3 := by
    intro x hx y hy z hz hyz
    have := hδ' (x, y) ⟨hx, hy⟩ (x, z) ⟨hx, hz⟩ (by
      rw [Prod.dist_eq]
      simp only [dist_self, Real.dist_eq]
      exact max_lt hδ (by linarith))
    rw [Real.dist_eq] at this
    exact this.le
  have hcol : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1,
      |x - y| ≤ 1 / N → |f x z - f y z| ≤ η / 3 := by
    intro x hx y hy z hz hxy
    have := hδ' (x, z) ⟨hx, hz⟩ (y, z) ⟨hy, hz⟩ (by
      rw [Prod.dist_eq]
      simp only [dist_self, Real.dist_eq]
      exact max_lt (by linarith) hδ)
    rw [Real.dist_eq] at this
    exact this.le
  have hGmod : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ 1 / N →
      |G x - G y| ≤ η / 3 := by
    intro x hx y hy hxy
    simp only [hG]
    rw [← intervalIntegral.integral_sub ((hf.uncurry_left x).intervalIntegrable _ _)
      ((hf.uncurry_left y).intervalIntegrable _ _), ← Real.norm_eq_abs]
    calc ‖∫ s' in (0 : ℝ)..1, (f x s' - f y s')‖ ≤ η / 3 * |1 - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun z hz => ?_
      _ = η / 3 := by simp
    rw [Set.uIoc_of_le zero_le_one] at hz
    rw [Real.norm_eq_abs]
    exact hcol x hx y hy z ⟨hz.1.le, hz.2⟩ hxy
  have h1 := abs_riemannSum_sub_integral_le hGc hNpos hGmod
  have h2 : ∀ k ∈ Finset.range N,
      |riemannSum (f ((k : ℝ) / N)) N - G ((k : ℝ) / N)| ≤ η / 3 := by
    intro k hk
    have hk0 : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, by
        rw [div_le_one hN']
        exact_mod_cast (Finset.mem_range.mp hk).le⟩
    exact abs_riemannSum_sub_integral_le (hf.uncurry_left _) hNpos
      (fun y hy z hz hyz => hrow _ hk0 y hy z hz hyz)
  have hR2 : riemannSum2 f N =
      (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, riemannSum (f ((k : ℝ) / N)) N := by
    simp only [riemannSum2, riemannSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hRG : riemannSum G N = (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, G ((k : ℝ) / N) := rfl
  have hdecomp : riemannSum2 f N - ∫ s in (0 : ℝ)..1, G s =
      (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, (riemannSum (f ((k : ℝ) / N)) N - G ((k : ℝ) / N)) +
        (riemannSum G N - ∫ s in (0 : ℝ)..1, G s) := by
    rw [hR2, Finset.sum_sub_distrib, hRG]
    ring
  have h3 : |(N : ℝ)⁻¹ *
      ∑ k ∈ Finset.range N, (riemannSum (f ((k : ℝ) / N)) N - G ((k : ℝ) / N))| ≤ η / 3 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hN')]
    calc (N : ℝ)⁻¹ *
          |∑ k ∈ Finset.range N, (riemannSum (f ((k : ℝ) / N)) N - G ((k : ℝ) / N))|
        ≤ (N : ℝ)⁻¹ * ∑ _k ∈ Finset.range N, η / 3 := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h2)
      _ = η / 3 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  rw [Real.dist_eq]
  change |riemannSum2 f N - ∫ s in (0 : ℝ)..1, G s| < η
  rw [hdecomp]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ η / 3 + η / 3 := add_le_add h3 h1
    _ < η := by linarith

/-! ### Real Gaussian variables: characteristic functions and limits -/

section Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Characteristic function at `1` of a centered real Gaussian variable. -/
theorem integral_cexp_mul_I_of_hasGaussianLaw {Y : Ω → ℝ} (hY : HasGaussianLaw Y P)
    (h0 : ∫ ω, Y ω ∂P = 0) :
    ∫ ω, Complex.exp (Y ω * Complex.I) ∂P = ((Real.exp (-(Var[Y; P] / 2)) : ℝ) : ℂ) := by
  have h1 : charFun (P.map Y) 1 = ∫ ω, Complex.exp (Y ω * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map hY.aemeasurable]
    · simp
    · exact Continuous.aestronglyMeasurable (by fun_prop)
  rw [← h1, hY.map_eq_gaussianReal, charFun_gaussianReal, h0,
    Real.coe_toNNReal _ (variance_nonneg _ _), Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Dominated convergence for the characteristic function at `1` under pointwise convergence. -/
theorem tendsto_integral_cexp_mul_I {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    [IsProbabilityMeasure P] {Y : ι → Ω → ℝ} {Y₀ : Ω → ℝ}
    (hmeas : ∀ᶠ n in l, AEMeasurable (Y n) P)
    (hlim : ∀ ω, Tendsto (fun n => Y n ω) l (𝓝 (Y₀ ω))) :
    Tendsto (fun n => ∫ ω, Complex.exp (Y n ω * Complex.I) ∂P) l
      (𝓝 (∫ ω, Complex.exp (Y₀ ω * Complex.I) ∂P)) := by
  have hc : Continuous fun x : ℝ => Complex.exp (x * Complex.I) := by fun_prop
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
    (integrable_const 1) ?_
  · filter_upwards [hmeas] with n hn
    exact hc.comp_aestronglyMeasurable hn.aestronglyMeasurable
  · exact Eventually.of_forall fun n => Eventually.of_forall fun ω => by
      rw [Complex.norm_exp_ofReal_mul_I]
  · exact Eventually.of_forall fun ω => (hc.tendsto _).comp (hlim ω)

/-- **Variances of centered Gaussian variables converge under pointwise convergence** (when the
limit is itself centered Gaussian). -/
theorem tendsto_variance_of_hasGaussianLaw {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    [IsProbabilityMeasure P] {Y : ι → Ω → ℝ} {Y₀ : Ω → ℝ}
    (hY : ∀ᶠ n in l, HasGaussianLaw (Y n) P ∧ ∫ ω, Y n ω ∂P = 0)
    (hY₀ : HasGaussianLaw Y₀ P) (h0 : ∫ ω, Y₀ ω ∂P = 0)
    (hlim : ∀ ω, Tendsto (fun n => Y n ω) l (𝓝 (Y₀ ω))) :
    Tendsto (fun n => Var[Y n; P]) l (𝓝 Var[Y₀; P]) := by
  have h1 := tendsto_integral_cexp_mul_I (hY.mono fun n hn => hn.1.aemeasurable) hlim
  rw [integral_cexp_mul_I_of_hasGaussianLaw hY₀ h0] at h1
  have h2 : Tendsto (fun n => Real.exp (-(Var[Y n; P] / 2))) l
      (𝓝 (Real.exp (-(Var[Y₀; P] / 2)))) := by
    have h3 := (Complex.continuous_re.tendsto _).comp h1
    simp only [Complex.ofReal_re] at h3
    refine h3.congr' (hY.mono fun n hn => ?_)
    simp only [Function.comp_apply]
    rw [integral_cexp_mul_I_of_hasGaussianLaw hn.1 hn.2, Complex.ofReal_re]
  have h3 := h2.log (Real.exp_pos _).ne'
  simp only [Real.log_exp] at h3
  have h4 := h3.const_mul (-2)
  have e1 : (fun n => -2 * -(Var[Y n; P] / 2)) = fun n => Var[Y n; P] := by
    ext n
    ring
  have e2 : -2 * -(Var[Y₀; P] / 2) = Var[Y₀; P] := by ring
  rwa [e1, e2] at h4

/-- **Closure of centered Gaussian laws under pointwise limits**, at the level of the
characteristic function: if `Yₙ → Y₀` pointwise, `Yₙ` are centered Gaussian and
`Var Yₙ → v`, then `E exp(i Y₀) = exp(-v/2)`. -/
theorem integral_cexp_mul_I_of_tendsto [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {Y₀ : Ω → ℝ}
    {v : ℝ} (hY : ∀ n, HasGaussianLaw (Y n) P) (h0 : ∀ n, ∫ ω, Y n ω ∂P = 0)
    (hlim : ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Y₀ ω)))
    (hv : Tendsto (fun n => Var[Y n; P]) atTop (𝓝 v)) :
    ∫ ω, Complex.exp (Y₀ ω * Complex.I) ∂P = ((Real.exp (-(v / 2)) : ℝ) : ℂ) := by
  have h1 := tendsto_integral_cexp_mul_I (Eventually.of_forall fun n => (hY n).aemeasurable) hlim
  have h2 : Tendsto (fun n => ∫ ω, Complex.exp (Y n ω * Complex.I) ∂P) atTop
      (𝓝 ((Real.exp (-(v / 2)) : ℝ) : ℂ)) := by
    have e : ∀ n, ∫ ω, Complex.exp (Y n ω * Complex.I) ∂P =
        ((Real.exp (-(Var[Y n; P] / 2)) : ℝ) : ℂ) := fun n =>
      integral_cexp_mul_I_of_hasGaussianLaw (hY n) (h0 n)
    rw [tendsto_congr e]
    exact (Complex.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto _).comp (hv.div_const 2).neg)
  exact tendsto_nhds_unique h1 h2

end Gauss

/-! ### The linear span of a Gaussian process -/

section Span

variable {Ω : Type*} {T : Type*}

/-- `Y` is a finite linear combination of values of the process `X`. -/
def InGSpan (X : T → Ω → ℝ) (Y : Ω → ℝ) : Prop :=
  ∃ (I : Finset T) (β : T → ℝ), Y = fun ω => ∑ t ∈ I, β t * X t ω

variable {X : T → Ω → ℝ}

theorem InGSpan.eval (t : T) : InGSpan X (X t) :=
  ⟨{t}, fun _ => 1, by ext; simp⟩

theorem InGSpan.zero : InGSpan X (fun _ => 0) :=
  ⟨∅, fun _ => 0, by ext; simp⟩

theorem InGSpan.const_mul {Y : Ω → ℝ} (r : ℝ) (h : InGSpan X Y) :
    InGSpan X (fun ω => r * Y ω) := by
  obtain ⟨I, β, rfl⟩ := h
  exact ⟨I, fun t => r * β t, by ext ω; simp [Finset.mul_sum, mul_assoc]⟩

theorem InGSpan.add {Y Y' : Ω → ℝ} (h : InGSpan X Y) (h' : InGSpan X Y') :
    InGSpan X (fun ω => Y ω + Y' ω) := by
  obtain ⟨I, β, rfl⟩ := h
  obtain ⟨I', β', rfl⟩ := h'
  refine ⟨I ∪ I', fun t => (if t ∈ I then β t else 0) + (if t ∈ I' then β' t else 0), ?_⟩
  ext ω
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
    Finset.union_inter_cancel_right]

theorem InGSpan.finset_sum {κ : Type*} (s : Finset κ) {Y : κ → Ω → ℝ}
    (h : ∀ k ∈ s, InGSpan X (Y k)) : InGSpan X (fun ω => ∑ k ∈ s, Y k ω) := by
  induction s using Finset.induction_on with
  | empty => simpa using (InGSpan.zero (X := X))
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (h k (by simp)).add (ih fun j hj => h j (by simp [hj]))

theorem InGSpan.list_sum {κ : Type*} (l : List κ) {Y : κ → Ω → ℝ}
    (h : ∀ k ∈ l, InGSpan X (Y k)) : InGSpan X (fun ω => (l.map fun k => Y k ω).sum) := by
  induction l with
  | nil => simpa using (InGSpan.zero (X := X))
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h k (by simp)).add (ih fun j hj => h j (by simp [hj]))

theorem InGSpan.hasGaussianLaw [MeasurableSpace Ω] {P : Measure Ω}
    (hX : IsGaussianProcess X P) {Y : Ω → ℝ} (h : InGSpan X Y) : HasGaussianLaw Y P := by
  obtain ⟨I, β, rfl⟩ := h
  simpa [smul_eq_mul] using (hX.smul β).hasGaussianLaw_fun_sum (I := I)

theorem InGSpan.integral_eq_zero [MeasurableSpace Ω] {P : Measure Ω}
    (hX : IsGaussianProcess X P) (h0 : ∀ t, ∫ ω, X t ω ∂P = 0)
    {Y : Ω → ℝ} (h : InGSpan X Y) : ∫ ω, Y ω ∂P = 0 := by
  obtain ⟨I, β, rfl⟩ := h
  rw [integral_finsetSum]
  · simp [integral_const_mul, h0]
  · intro t _
    exact (hX.hasGaussianLaw_eval t).integrable.const_mul _

end Span

/-! ### The circle-average field at a fixed radius -/

section Field

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : ℝ → ℂ → Ω → ℝ}

theorem isGaussianProcess_slice (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε) :
    IsGaussianProcess (fun z : ℂ => h ε z) P :=
  hG.isGaussianProcess.comp_right (fun z : ℂ => ((⟨ε, hε⟩ : Ioi (0 : ℝ)), z))

theorem memLp_slice (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    MemLp (h ε z) 2 P :=
  ((isGaussianProcess_slice hG hε).hasGaussianLaw_eval z).memLp_two

theorem continuous_variance_of_inGSpan (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε)
    {Z : Type*} [TopologicalSpace Z] [FirstCountableTopology Z] {A : Z → Ω → ℝ}
    (hA : ∀ p, InGSpan (fun z : ℂ => h ε z) (A p)) (hcont : ∀ ω, Continuous fun p => A p ω) :
    Continuous fun p => Var[A p; P] := by
  have := hG.isProbabilityMeasure
  have hX := isGaussianProcess_slice hG hε
  have h0 : ∀ z, ∫ ω, h ε z ω ∂P = 0 := hG.integral_eq_zero ε hε
  refine continuous_iff_continuousAt.2 fun p => ?_
  exact tendsto_variance_of_hasGaussianLaw
    (Eventually.of_forall fun q => ⟨(hA q).hasGaussianLaw hX, (hA q).integral_eq_zero hX h0⟩)
    ((hA p).hasGaussianLaw hX) ((hA p).integral_eq_zero hX h0)
    fun ω => (hcont ω).continuousAt

/-- **Continuity of the circle-average covariance kernel** at a fixed radius `ε > 0`.  (Proved
from the hypotheses of `IsGFFCircleAverage`: sample continuity plus Gaussianity give
continuity of variances.) -/
theorem continuous_gffCircleCov (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun p : ℂ × ℂ => gffCircleCov ε p.1 ε p.2 := by
  have := hG.isProbabilityMeasure
  have hL := memLp_slice hG hε
  have key : ∀ p : ℂ × ℂ, gffCircleCov ε p.1 ε p.2 =
      (Var[fun ω => h ε p.1 ω + h ε p.2 ω; P] - Var[h ε p.1; P] - Var[h ε p.2; P]) / 2 := by
    intro p
    rw [variance_fun_add (hL p.1) (hL p.2), ← hG.covariance_eq ε hε ε hε]
    ring
  simp_rw [key]
  have hc : ∀ ω, Continuous fun z => h ε z ω := hG.continuous ε hε
  have c1 := continuous_variance_of_inGSpan hG hε
    (A := fun p : ℂ × ℂ => fun ω => h ε p.1 ω + h ε p.2 ω)
    (fun p => (InGSpan.eval p.1).add (InGSpan.eval p.2))
    fun ω => ((hc ω).comp continuous_fst).add ((hc ω).comp continuous_snd)
  have c2 := continuous_variance_of_inGSpan hG hε (A := fun p : ℂ × ℂ => h ε p.1)
    (fun p => InGSpan.eval p.1) fun ω => (hc ω).comp continuous_fst
  have c3 := continuous_variance_of_inGSpan hG hε (A := fun p : ℂ × ℂ => h ε p.2)
    (fun p => InGSpan.eval p.2) fun ω => (hc ω).comp continuous_snd
  exact ((c1.sub c2).sub c3).div_const 2

end Field

/-! ### Riemann approximations of segment averages -/

section Riemann

open Blueprint.Draft

/-- Left Riemann sum approximating `segAvg φ a b`. -/
def segRiemann (φ : ℂ → ℝ) (a b : ℂ) (N : ℕ) : ℝ :=
  riemannSum (fun s => φ (a + (s : ℂ) * (b - a))) N

/-- Riemann approximation of `SegComb.avg φ c`. -/
def combRiemann (φ : ℂ → ℝ) (c : SegComb) (N : ℕ) : ℝ :=
  (c.map fun p : ℝ × ℂ × ℂ => p.1 * segRiemann φ p.2.1 p.2.2 N).sum

theorem tendsto_segRiemann {φ : ℂ → ℝ} (hφ : Continuous φ) (a b : ℂ) :
    Tendsto (segRiemann φ a b) atTop (𝓝 (segAvg φ a b)) :=
  tendsto_riemannSum (by fun_prop)

theorem tendsto_combRiemann {φ : ℂ → ℝ} (hφ : Continuous φ) (c : SegComb) :
    Tendsto (combRiemann φ c) atTop (𝓝 (SegComb.avg φ c)) :=
  tendsto_list_sum c (f := fun (p : ℝ × ℂ × ℂ) N => p.1 * segRiemann φ p.2.1 p.2.2 N)
    (a := fun p : ℝ × ℂ × ℂ => p.1 * segAvg φ p.2.1 p.2.2)
    fun _ _ => (tendsto_segRiemann hφ _ _).const_mul _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : ℝ → ℂ → Ω → ℝ}

omit [MeasurableSpace Ω] in
theorem inGSpan_segRiemann (ε : ℝ) (a b : ℂ) (N : ℕ) :
    InGSpan (fun z : ℂ => h ε z) (fun ω => segRiemann (fun z => h ε z ω) a b N) :=
  (InGSpan.finset_sum (X := fun z : ℂ => h ε z) (Finset.range N)
    (Y := fun k => h ε (a + (((k : ℝ) / N : ℝ) : ℂ) * (b - a)))
    fun _ _ => InGSpan.eval _).const_mul ((N : ℝ)⁻¹)

omit [MeasurableSpace Ω] in
theorem inGSpan_combRiemann (ε : ℝ) (c : SegComb) (N : ℕ) :
    InGSpan (fun z : ℂ => h ε z) (fun ω => combRiemann (fun z => h ε z ω) c N) :=
  InGSpan.list_sum c
    (Y := fun (p : ℝ × ℂ × ℂ) ω => p.1 * segRiemann (fun z => h ε z ω) p.2.1 p.2.2 N)
    fun _ _ => (inGSpan_segRiemann ε _ _ N).const_mul _

theorem memLp_listComb [IsFiniteMeasure P] (c : SegComb) (f : ℝ × ℂ × ℂ → Ω → ℝ)
    (hf : ∀ p, MemLp (f p) 2 P) :
    MemLp (fun ω => (c.map fun p : ℝ × ℂ × ℂ => p.1 * f p ω).sum) 2 P := by
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((hf p).const_mul p.1).add ih

theorem covariance_listComb_right [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (c : SegComb) (g : ℝ × ℂ × ℂ → Ω → ℝ) (hg : ∀ p, MemLp (g p) 2 P) :
    cov[Y, fun ω => (c.map fun p : ℝ × ℂ × ℂ => p.1 * g p ω).sum; P] =
      (c.map fun p : ℝ × ℂ × ℂ => p.1 * cov[Y, g p; P]).sum := by
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    have := covariance_add_right hY ((hg p).const_mul p.1) (memLp_listComb c g hg)
    rw [covariance_const_mul_right] at this
    exact this

/-- Bilinearity of the covariance over segment combinations. -/
theorem covariance_listComb [IsProbabilityMeasure P] (c c' : SegComb) (f g : ℝ × ℂ × ℂ → Ω → ℝ)
    (hf : ∀ p, MemLp (f p) 2 P) (hg : ∀ p, MemLp (g p) 2 P) :
    cov[fun ω => (c.map fun p : ℝ × ℂ × ℂ => p.1 * f p ω).sum,
        fun ω => (c'.map fun p : ℝ × ℂ × ℂ => p.1 * g p ω).sum; P] =
      (c.map fun p : ℝ × ℂ × ℂ =>
        (c'.map fun p' : ℝ × ℂ × ℂ => p.1 * p'.1 * cov[f p, g p'; P]).sum).sum := by
  rw [covariance_comm, covariance_listComb_right (memLp_listComb c' g hg) c f hf]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  rw [covariance_comm, covariance_listComb_right (hf p) c' g hg, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun p' _ => ?_
  ring

theorem covariance_segRiemann (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε)
    (a b a' b' : ℂ) (N : ℕ) :
    cov[fun ω => segRiemann (fun z => h ε z ω) a b N,
        fun ω => segRiemann (fun z => h ε z ω) a' b' N; P] =
      riemannSum2 (fun s s' => gffCircleCov ε (a + (s : ℂ) * (b - a)) ε
        (a' + (s' : ℂ) * (b' - a'))) N := by
  have := hG.isProbabilityMeasure
  simp only [segRiemann, riemannSum, riemannSum2]
  rw [covariance_const_mul_left, covariance_const_mul_right,
    covariance_fun_sum_fun_sum' (fun k _ => memLp_slice hG hε _)
      (fun k _ => memLp_slice hG hε _)]
  simp_rw [hG.covariance_eq ε hε ε hε]
  ring

/-- The integrand `(s, s') ↦ gffCircleCov ε (a + s(b-a)) ε (a' + s'(b'-a'))` of `segCircCov`
is jointly continuous. -/
theorem continuous_segKernel (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε)
    (a b a' b' : ℂ) :
    Continuous (Function.uncurry fun s s' : ℝ =>
      gffCircleCov ε (a + (s : ℂ) * (b - a)) ε (a' + (s' : ℂ) * (b' - a'))) := by
  have hk : Continuous fun q : ℝ × ℝ => (a + (q.1 : ℂ) * (b - a), a' + (q.2 : ℂ) * (b' - a')) := by
    fun_prop
  refine ((continuous_gffCircleCov hG hε).comp hk).congr fun q => ?_
  obtain ⟨s, s'⟩ := q
  rfl

theorem tendsto_covariance_segRiemann (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε)
    (a b a' b' : ℂ) :
    Tendsto (fun N => cov[fun ω => segRiemann (fun z => h ε z ω) a b N,
        fun ω => segRiemann (fun z => h ε z ω) a' b' N; P]) atTop
      (𝓝 (segCircCov ε a b a' b')) := by
  rw [tendsto_congr (covariance_segRiemann hG hε a b a' b')]
  exact tendsto_riemannSum2 (continuous_segKernel hG hε a b a' b')

theorem covariance_combRiemann (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε)
    (c c' : SegComb) (N : ℕ) :
    cov[fun ω => combRiemann (fun z => h ε z ω) c N,
        fun ω => combRiemann (fun z => h ε z ω) c' N; P] =
      (c.map fun p : ℝ × ℂ × ℂ => (c'.map fun p' : ℝ × ℂ × ℂ => p.1 * p'.1 *
        cov[fun ω => segRiemann (fun z => h ε z ω) p.2.1 p.2.2 N,
          fun ω => segRiemann (fun z => h ε z ω) p'.2.1 p'.2.2 N; P]).sum).sum := by
  have := hG.isProbabilityMeasure
  have hL : ∀ p : ℝ × ℂ × ℂ,
      MemLp (fun ω => segRiemann (fun z => h ε z ω) p.2.1 p.2.2 N) 2 P := fun p =>
    ((inGSpan_segRiemann ε _ _ N).hasGaussianLaw (isGaussianProcess_slice hG hε)).memLp_two
  exact covariance_listComb c c'
    (fun (p : ℝ × ℂ × ℂ) ω => segRiemann (fun z => h ε z ω) p.2.1 p.2.2 N)
    (fun (p : ℝ × ℂ × ℂ) ω => segRiemann (fun z => h ε z ω) p.2.1 p.2.2 N) hL hL

/-- Covariances of the Riemann approximations of segment combinations converge to `circCov`. -/
theorem tendsto_covariance_combRiemann (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε)
    (c c' : SegComb) :
    Tendsto (fun N => cov[fun ω => combRiemann (fun z => h ε z ω) c N,
        fun ω => combRiemann (fun z => h ε z ω) c' N; P]) atTop
      (𝓝 (SegComb.circCov ε c c')) := by
  rw [tendsto_congr (covariance_combRiemann hG hε c c')]
  exact tendsto_list_sum c fun p _ => tendsto_list_sum c' fun p' _ =>
    (tendsto_covariance_segRiemann hG hε _ _ _ _).const_mul _

end Riemann

end SegLaw

open SegLaw Matrix in
/-- **Node `P1`.**  Finite families of segment averages of the circle-average field `h_ε` are
centered Gaussian vectors with covariance `circCov ε`. -/
theorem segCombLaw : Blueprint.Draft.SegCombLaw := by
  unfold Blueprint.Draft.SegCombLaw
  intro Ω _ P h hG ε hε ι F c
  have := hG.isProbabilityMeasure
  have hX := isGaussianProcess_slice hG hε
  have h0 : ∀ z, ∫ ω, h ε z ω ∂P = 0 := hG.integral_eq_zero ε hε
  set YN : ℕ → F → Ω → ℝ := fun N i ω => combRiemann (fun z => h ε z ω) (c i) N with hYN
  set Y : F → Ω → ℝ := fun i ω => Blueprint.Draft.SegComb.avg (fun z => h ε z ω) (c i) with hY
  have hspan : ∀ N i, InGSpan (fun z : ℂ => h ε z) (YN N i) := fun N i =>
    inGSpan_combRiemann ε (c i) N
  have hlim : ∀ i ω, Tendsto (fun N => YN N i ω) atTop (𝓝 (Y i ω)) := fun i ω =>
    tendsto_combRiemann (hG.continuous ε hε ω) (c i)
  have hcov : ∀ i j, Tendsto (fun N => cov[YN N i, YN N j; P]) atTop
      (𝓝 (Blueprint.Draft.SegComb.circCov ε (c i) (c j))) := fun i j =>
    tendsto_covariance_combRiemann hG hε (c i) (c j)
  have hmeasY : ∀ i, AEMeasurable (Y i) P := fun i =>
    aemeasurable_of_tendsto_metrizable_ae atTop
      (fun N => ((hspan N i).hasGaussianLaw hX).aemeasurable) (ae_of_all _ fun ω => hlim i ω)
  set M : Matrix F F ℝ := Matrix.of fun i j : F =>
    Blueprint.Draft.SegComb.circCov ε (c i) (c j) with hM
  have hsN : ∀ (t : F → ℝ) (N : ℕ),
      InGSpan (fun z : ℂ => h ε z) (fun ω => ∑ i, t i * YN N i ω) := fun t N =>
    InGSpan.finset_sum _ fun i _ => (hspan N i).const_mul (t i)
  have hvarN : ∀ (t : F → ℝ) (N : ℕ), Var[fun ω => ∑ i, t i * YN N i ω; P] =
      ∑ i, ∑ j, t i * t j * cov[YN N i, YN N j; P] := by
    intro t N
    have hL : ∀ i, MemLp (fun ω => t i * YN N i ω) 2 P := fun i =>
      (((hspan N i).hasGaussianLaw hX).memLp_two).const_mul _
    rw [← covariance_self ((hsN t N).hasGaussianLaw hX).aemeasurable,
      covariance_fun_sum_fun_sum hL hL]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hQ : ∀ t : F → ℝ, Tendsto (fun N => Var[fun ω => ∑ i, t i * YN N i ω; P]) atTop
      (𝓝 (t ⬝ᵥ M *ᵥ t)) := by
    intro t
    rw [tendsto_congr (hvarN t)]
    have : t ⬝ᵥ M *ᵥ t = ∑ i, ∑ j, t i * t j * M i j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => (hcov i j).const_mul _
  have hPSD : M.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · refine Matrix.IsHermitian.ext fun i j => ?_
      simp only [star_trivial, hM, Matrix.of_apply]
      exact tendsto_nhds_unique (hcov j i)
        ((hcov i j).congr fun N => covariance_comm _ _)
    · rw [star_trivial]
      exact ge_of_tendsto' (hQ x) fun N => variance_nonneg _ _
  have hchar : ∀ t : F → ℝ,
      ∫ ω, Complex.exp (((∑ i, t i * Y i ω : ℝ) : ℂ) * Complex.I) ∂P =
        ((Real.exp (-((t ⬝ᵥ M *ᵥ t) / 2)) : ℝ) : ℂ) := by
    intro t
    exact integral_cexp_mul_I_of_tendsto (Y := fun N ω => ∑ i, t i * YN N i ω)
      (fun N => (hsN t N).hasGaussianLaw hX) (fun N => (hsN t N).integral_eq_zero hX h0)
      (fun ω => tendsto_finsetSum _ fun i _ => (hlim i ω).const_mul _) (hQ t)
  have hmeasV : AEMeasurable (fun ω (i : F) => Y i ω) P := AEMeasurable.of_eval hmeasY
  have hZm : AEMeasurable (fun ω => WithLp.toLp 2 (fun i : F => Y i ω)) P :=
    (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable hmeasV
  have hZ : P.map (fun ω => WithLp.toLp 2 (fun i : F => Y i ω)) = multivariateGaussian 0 M := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_multivariateGaussian hPSD, charFun_apply, integral_map hZm]
    swap
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    have hinner : ∀ ω, (inner ℝ (WithLp.toLp 2 (fun i : F => Y i ω)) t : ℝ) =
        ∑ i, t.ofLp i * Y i ω := by
      intro ω
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct]
    simp_rw [hinner]
    rw [hchar t.ofLp, Complex.ofReal_exp, inner_zero_right]
    congr 1
    push_cast
    ring
  refine ⟨hmeasV, ?_⟩
  change P.map (fun ω (i : F) => Y i ω) = _
  have hof : (fun ω (i : F) => Y i ω) =
      WithLp.ofLp ∘ (fun ω => WithLp.toLp 2 (fun i : F => Y i ω)) := by
    funext ω i
    rfl
  rw [hof, ← AEMeasurable.map_map_of_aemeasurable
    (PiLp.continuous_ofLp 2 _).measurable.aemeasurable hZm, hZ]
  rfl

end LQGDimension
