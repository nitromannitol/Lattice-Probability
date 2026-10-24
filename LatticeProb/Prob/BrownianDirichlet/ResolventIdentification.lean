import LatticeProb.Prob.BrownianDirichlet.Representation
import LatticeProb.Prob.BrownianDirichlet.KilledResolvent
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Identification of the killed Brownian resolvent

Fubini identifies the pointwise Laplace integral of the killed kernel with the
strict-survival running payoff. Testing against L² functions identifies this integral
with the Bochner resolvent, so classical Dirichlet solutions lie in its generator graph.
-/

namespace LatticeProb

open MeasureTheory Set

noncomputable section

/-- Euclidean balls have finite restricted Lebesgue measure. -/
private instance finiteVolumeBall {d : ℕ} (c : Euc d) (R : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
  isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne

/-- Positive discount makes the bounded strict-survival integrand product integrable. -/
lemma integrable_discounted_survival {d : ℕ} {B : Set (Euc d)} (hB : IsOpen B)
    (σ : ℝ) {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {a : ℝ} (ha : 0 < a) {b : Euc d → ℝ} (hb : Measurable b)
    {C : ℝ} (hC : 0 ≤ C) (hbC : ∀ y, |b y| ≤ C) (x : Euc d) :
    Integrable (fun p : ℝ × BrownianPath d =>
      if ENNReal.ofReal p.1 < scaledExit B σ x p.2 then
        Real.exp (-a * p.1) * b (x + σ • p.2 p.1.toNNReal) else 0)
      ((volume.restrict (Ioi 0)).prod μ) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hk := (measurable_killed_integrand hB σ hb).comp
    (measurable_fst.real_toNNReal.prodMk
      ((measurable_const (a := x)).prodMk measurable_snd))
  have he : Measurable (fun p : ℝ × BrownianPath d => Real.exp (-a * p.1)) :=
    (measurable_const.mul measurable_fst).exp
  have hm : Measurable (fun p : ℝ × BrownianPath d =>
      if ENNReal.ofReal p.1 < scaledExit B σ x p.2 then
        Real.exp (-a * p.1) * b (x + σ • p.2 p.1.toNNReal) else 0) := by
    convert he.mul hk using 1
    funext p
    simp only [Pi.mul_apply, Function.comp_apply, ENNReal.ofNNReal_toNNReal,
      mul_ite, mul_zero]
  apply (((integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).mul_const C).comp_fst μ).mono'
    hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  split_ifs
  · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbC _) (Real.exp_pos _).le
  · simpa only [norm_zero] using mul_nonneg (Real.exp_pos (-a * p.1)).le hC

/-- The pointwise killed Laplace integral equals the expected strict-survival payoff. -/
theorem pointwise_laplace_killed_eq_J {d : ℕ} {B : Set (Euc d)} (hB : IsOpen B)
    (σ : ℝ) {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {a : ℝ} (ha : 0 < a) {b : Euc d → ℝ} (hb : Measurable b)
    {C : ℝ} (hC : 0 ≤ C) (hbC : ∀ y, |b y| ≤ C) (x : Euc d) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * killed B σ μ t.toNNReal b x) =
      ∫ ω, (∫ t in Ioi (0 : ℝ),
        if ENNReal.ofReal t < scaledExit B σ x ω then
          Real.exp (-a * t) * b (x + σ • ω t.toNNReal) else 0) ∂μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  rw [← integral_integral_swap (integrable_discounted_survival hB σ hμ ha hb hC hbC x)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [killed]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  simp only [ENNReal.ofNNReal_toNNReal, mul_ite, mul_zero]

/-- Integration against a finite measure preserves joint measurability of the killed kernel. -/
lemma measurable_killed_time_start {d : ℕ} {B : Set (Euc d)} (hB : IsOpen B)
    (σ : ℝ) {μ : Measure (BrownianPath d)} [SFinite μ]
    {b : Euc d → ℝ} (hb : Measurable b) :
    Measurable (fun p : ℝ × Euc d => killed B σ μ p.1.toNNReal b p.2) := by
  have hm := (measurable_killed_integrand hB σ hb).comp
    ((measurable_fst.fst.real_toNNReal).prodMk
      ((measurable_fst.snd).prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The pointwise killed Laplace integral is square integrable on a finite-volume domain. -/
lemma memLp_laplace_killed {d : ℕ} {B : Set (Euc d)}
    [IsFiniteMeasure (volume.restrict B)] (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {a : ℝ} (ha : 0 < a) {b : Euc d → ℝ} (hb : Measurable b)
    {C : ℝ} (hC : 0 ≤ C) (hbC : ∀ y, |b y| ≤ C) :
    MemLp (fun x => ∫ t in Ioi (0 : ℝ),
      Real.exp (-a * t) * killed B σ μ t.toNNReal b x) 2 (volume.restrict B) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hm : Measurable (fun p : ℝ × Euc d =>
      Real.exp (-a * p.1) * killed B σ μ p.1.toNNReal b p.2) :=
    (measurable_const.mul measurable_fst).exp.mul (measurable_killed_time_start hB σ hb)
  apply MemLp.of_bound hm.stronglyMeasurable.integral_prod_left.aestronglyMeasurable
    (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * C)
  apply Filter.Eventually.of_forall
  intro x
  apply norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).mul_const C)
  apply Filter.Eventually.of_forall
  intro t
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_killed_le σ t.toNNReal hC hbC x)
    (Real.exp_pos _).le

/-- The Bochner killed resolvent is the L² class of the pointwise Laplace integral. -/
theorem resolvent_killed_apply {d : ℕ} {B : Set (Euc d)}
    [IsFiniteMeasure (volume.restrict B)] (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {a : ℝ} (ha : 0 < a) {b : Euc d → ℝ} (hb : Measurable b)
    {C : ℝ} (hC : 0 ≤ C) (hbC : ∀ y, |b y| ≤ C)
    (hbLp : MemLp b 2 (volume.restrict B)) :
    ContractionSemigroup.resolvent (killedSemigroup hB σ hμ) a ha (hbLp.toLp b) =
      (memLp_laplace_killed hB σ hμ ha hb hC hbC).toLp
        (fun x => ∫ t in Ioi (0 : ℝ),
          Real.exp (-a * t) * killed B σ μ t.toNNReal b x) := by
  letI : IsProbabilityMeasure μ := hμ.1
  let ν := volume.restrict B
  let H : ℝ × Euc d → ℝ := fun p =>
    Real.exp (-a * p.1) * killed B σ μ p.1.toNNReal b p.2
  have hm : Measurable H :=
    (measurable_const.mul measurable_fst).exp.mul (measurable_killed_time_start hB σ hb)
  have hbound (t : ℝ) (x : Euc d) : ‖H (t, x)‖ ≤ Real.exp (-a * t) * C := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_killed_le σ t.toNNReal hC hbC x)
      (Real.exp_pos _).le
  apply ext_inner_left ℝ
  intro q
  have hq : Integrable q ν := (Lp.memLp q).integrable (by norm_num)
  have hi : Integrable (fun p : ℝ × Euc d => q p.2 * H p)
      ((volume.restrict (Ioi 0)).prod ν) := by
    apply (((integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).mul_const C).mul_prod
      hq.norm).mono'
      ((Lp.aestronglyMeasurable q).comp_snd.mul hm.aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro p
    change ‖q p.2 * H p‖ ≤ _
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbound p.1 p.2) (norm_nonneg _)
  rw [ContractionSemigroup.resolvent_apply]
  change inner ℝ q (∫ t in Ioi (0 : ℝ),
    Real.exp (-a * t) • killedLp hB σ hμ t.toNNReal (hbLp.toLp b)) = _
  rw [← integral_inner (integrable_discounted_killedLp hB σ hμ ha (hbLp.toLp b))]
  have ht (t : ℝ) :
      inner ℝ q (Real.exp (-a * t) • killedLp hB σ hμ t.toNNReal (hbLp.toLp b)) =
        ∫ x, q x * H (t, x) ∂ν := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul (Real.exp (-a * t))
      (killedLp hB σ hμ t.toNNReal (hbLp.toLp b)),
      (memLp_killed hB σ hμ t.toNNReal hb hC hbC).coeFn_toLp] with x hs hk
    rw [hs, killedLp_toLp hB σ hμ t.toNNReal hb hC hbC hbLp]
    dsimp only [Pi.smul_apply, smul_eq_mul]
    rw [hk]
    simp only [Real.inner_apply, H]
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ x, q x * H (t, x) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall ht
    _ = ∫ x, (∫ t in Ioi (0 : ℝ), q x * H (t, x)) ∂ν := integral_integral_swap hi
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(memLp_laplace_killed hB σ hμ ha hb hC hbC).coeFn_toLp] with x hx
      rw [hx, integral_const_mul]
      simp only [Real.inner_apply, H]

/-- Continuous closure data belong to L² of a bounded open finite-volume domain. -/
lemma memLp_restrict_of_continuousOn_closure {d : ℕ} {B : Set (Euc d)}
    [IsFiniteMeasure (volume.restrict B)] (hB : IsOpen B) (hbounded : Bornology.IsBounded B)
    {g : Euc d → ℝ} (hg : ContinuousOn g (closure B)) :
    MemLp g 2 (volume.restrict B) := by
  classical
  obtain ⟨C, hC⟩ := isBounded_image_closure hbounded hg
  have he : B.indicator g =ᵐ[volume.restrict B] g := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact indicator_of_mem hx g
  apply MemLp.of_bound
    ((measurable_indicator_of_continuousOn hB hg).aestronglyMeasurable.congr he) C
  filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
  exact (Real.norm_eq_abs _).trans_le (hC x (subset_closure hx))

/-- A classical solution on a Euclidean ball is the killed L² resolvent of its forcing. -/
theorem resolvent_killed_classical {d : ℕ} {c : Euc d} {R a₀ a : ℝ}
    [IsFiniteMeasure (volume.restrict (Metric.ball c R))]
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (hR : 0 < R) (ha₀ : 0 < a₀) (ha : 0 < a)
    {v g : Euc d → ℝ} (hv : ContDiffOn ℝ 2 v (Metric.ball c R))
    (hvc : ContinuousOn v (closure (Metric.ball c R)))
    (hzero : ∀ y ∈ frontier (Metric.ball c R), v y = 0)
    (hgc : ContinuousOn g (closure (Metric.ball c R)))
    (hpde : ∀ y ∈ Metric.ball c R, a * v y - a₀ * Laplacian.laplacian v y = g y)
    (hgLp : MemLp g 2 (volume.restrict (Metric.ball c R)))
    (hvLp : MemLp v 2 (volume.restrict (Metric.ball c R))) :
    ContractionSemigroup.resolvent
      (killedSemigroup Metric.isOpen_ball (Real.sqrt (2 * a₀)) hμ) a ha (hgLp.toLp g) =
        hvLp.toLp v := by
  classical
  let B := Metric.ball c R
  obtain ⟨M, hM⟩ := isBounded_image_closure Metric.isBounded_ball hgc
  have hb : Measurable (B.indicator g) :=
    measurable_indicator_of_continuousOn Metric.isOpen_ball hgc
  have hbound : ∀ y, |B.indicator g y| ≤ max M 0 := by
    intro y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy]
      exact (hM y (subset_closure hy)).trans (le_max_left _ _)
    · rw [indicator_of_notMem hy, abs_zero]
      exact le_max_right _ _
  have hbLp : MemLp (B.indicator g) 2 (volume.restrict B) :=
    MemLp.of_bound hb.aestronglyMeasurable (max M 0)
      (Filter.Eventually.of_forall fun y => (Real.norm_eq_abs _).trans_le (hbound y))
  have hquot : hgLp.toLp g = hbLp.toLp (B.indicator g) := by
    apply MemLp.toLp_congr
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact (indicator_of_mem hx g).symm
  rw [hquot, resolvent_killed_apply Metric.isOpen_ball (Real.sqrt (2 * a₀)) hμ ha hb
    (le_max_right M 0) hbound hbLp]
  apply Lp.ext
  filter_upwards [(memLp_laplace_killed Metric.isOpen_ball (Real.sqrt (2 * a₀)) hμ ha
    hb (le_max_right M 0) hbound).coeFn_toLp, hvLp.coeFn_toLp,
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hvx hxB
  rw [hx, hvx, pointwise_laplace_killed_eq_J Metric.isOpen_ball
    (Real.sqrt (2 * a₀)) hμ ha hb (le_max_right M 0) hbound]
  rw [brownian_dirichlet_representation_euc hμ hR ha₀ ha hv hvc hzero hgc hpde hxB]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  split_ifs with ht
  · rw [indicator_of_mem (mem_of_lt_scaledExit ht)]
  · rfl

/-- A classical Dirichlet solution belongs to the genuine killed generator graph. -/
theorem classical_mem_killed_generatorGraph {d : ℕ} {c : Euc d} {R a₀ a : ℝ}
    [IsFiniteMeasure (volume.restrict (Metric.ball c R))]
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (hR : 0 < R) (ha₀ : 0 < a₀) (ha : 0 < a)
    {v g : Euc d → ℝ} (hv : ContDiffOn ℝ 2 v (Metric.ball c R))
    (hvc : ContinuousOn v (closure (Metric.ball c R)))
    (hzero : ∀ y ∈ frontier (Metric.ball c R), v y = 0)
    (hgc : ContinuousOn g (closure (Metric.ball c R)))
    (hpde : ∀ y ∈ Metric.ball c R, a * v y - a₀ * Laplacian.laplacian v y = g y)
    (hgLp : MemLp g 2 (volume.restrict (Metric.ball c R)))
    (hvLp : MemLp v 2 (volume.restrict (Metric.ball c R))) :
    (hvLp.toLp v, a • hvLp.toLp v - hgLp.toLp g) ∈
      ContractionSemigroup.generatorGraph
        (killedSemigroup Metric.isOpen_ball (Real.sqrt (2 * a₀)) hμ) := by
  have he := resolvent_killed_classical hμ hR ha₀ ha hv hvc hzero hgc hpde hgLp hvLp
  have hg := ContractionSemigroup.resolvent_mem_generatorGraph
    (killedSemigroup Metric.isOpen_ball (Real.sqrt (2 * a₀)) hμ) ha (hgLp.toLp g)
  rw [he] at hg
  exact hg

/-- An actual one-dimensional Brownian law realizes a classical resolvent with center payoff one. -/
theorem exists_classical_killed_resolvent_payoff_one :
    ∃ (μ : Measure (BrownianPath 1)) (hμ : IsStandardBrownianLaw μ)
      (f v : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Euc 1) 1))),
      ContractionSemigroup.resolvent
        (killedSemigroup (B := Metric.ball (0 : Euc 1) 1) Metric.isOpen_ball
          (Real.sqrt (2 * 1)) hμ) 1 zero_lt_one f = v ∧
      (v, (1 : ℝ) • v - f) ∈ ContractionSemigroup.generatorGraph
        (killedSemigroup (B := Metric.ball (0 : Euc 1) 1) Metric.isOpen_ball
          (Real.sqrt (2 * 1)) hμ) ∧
      (∫ ω, (∫ t in Ioi (0 : ℝ),
        if ENNReal.ofReal t < scaledExit (Metric.ball (0 : Euc 1) 1)
            (Real.sqrt (2 * 1)) 0 ω then
          Real.exp (-1 * t) *
            (1 * (1 - ∑ i : Fin 1, (0 + Real.sqrt (2 * 1) • ω t.toNNReal) i ^ 2) +
              2 * (1 : ℝ) * 1) else 0) ∂μ) = 1 := by
  obtain ⟨μ, hμ, hpay⟩ := exists_brownian_quadratic_payoff_one
  obtain ⟨hv, hvc, hz, hpde⟩ := Elliptic.quadratic_euclidean_dirichlet (d := 1) 1 1
  have hg : ContinuousOn
      (fun x : Euc 1 => 1 * (1 - ∑ i : Fin 1, x i ^ 2) + 2 * (1 : ℝ) * 1)
      (closure (Metric.ball 0 1)) := by fun_prop
  have hgLp := memLp_restrict_of_continuousOn_closure Metric.isOpen_ball
    Metric.isBounded_ball hg
  have hvLp := memLp_restrict_of_continuousOn_closure Metric.isOpen_ball
    Metric.isBounded_ball hvc
  have hz' : ∀ y ∈ frontier (Metric.ball (0 : Euc 1) 1),
      1 - ∑ i : Fin 1, y i ^ 2 = 0 := by
    simpa only [frontier_ball _ one_ne_zero] using hz
  refine ⟨μ, hμ, hgLp.toLp _, hvLp.toLp _, ?_, ?_, hpay⟩
  · exact resolvent_killed_classical hμ zero_lt_one zero_lt_one zero_lt_one
      hv hvc hz' hg (by simpa only [Nat.cast_one] using hpde) hgLp hvLp
  · exact classical_mem_killed_generatorGraph hμ zero_lt_one zero_lt_one zero_lt_one
      hv hvc hz' hg (by simpa only [Nat.cast_one] using hpde) hgLp hvLp

end

end LatticeProb
