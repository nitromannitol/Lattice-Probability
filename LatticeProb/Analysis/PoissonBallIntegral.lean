import LatticeProb.Analysis.PoissonBallKernel

/-!
# The Poisson integral on the unit ball

For a function `f` continuous on the unit sphere of `ℝ ^ d`, the Poisson integral
`poissonIntegral f x = ⨍ ζ, P(x, ζ) f(ζ) dσ(ζ)` averages `f` against the Poisson kernel `P` of
`LatticeProb.Ishii.poissonKernel` over the surface measure `σ` of the unit sphere.

* `LatticeProb.Ishii.harmonicOnNhd_integral_mul`: an integral, over a compact parameter space with
  a finite measure, of kernels that are harmonic in `x` and jointly `C³` is harmonic;
* `LatticeProb.Ishii.harmonicOnNhd_poissonIntegral`: the Poisson integral is harmonic on the open
  unit ball (Axler–Bourdon–Ramey, *Harmonic Function Theory*, proof of 1.17);
* `LatticeProb.Ishii.integral_toSphere_comp_linearIsometryEquiv`: the surface measure of the unit
  sphere is invariant under linear isometries;
* `LatticeProb.Ishii.average_poissonKernel_eq_one`: for `d ≥ 1`, the Poisson kernel has average `1`
  over the sphere at every point of the open ball (Mörters–Peres, *Brownian Motion*,
  Theorem 3.43).

The harmonicity of the integral is obtained by differentiating twice under the integral sign; the
derivatives of the kernel are bounded on compact sets by continuity. Only directional second
derivatives are integrated. For the average of the kernel, `x ↦ ∫ P(x, ζ) dσ(ζ)` is harmonic and
depends only on `‖x‖`; the exit position of a Brownian motion from the ball of radius `‖x‖` about
`0` lies on the sphere of radius `‖x‖`, so the value at `x` equals the value at `0`, which is the
total mass of `σ`.
-/

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped RealInnerProductSpace Laplacian Pointwise

noncomputable section

namespace LatticeProb.Ishii

section ParametricHarmonic

variable {E V α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace α] [CompactSpace α]
  [MeasurableSpace α] [OpensMeasurableSpace α]

/-- `‖c • v‖ ≤ M C` from `‖c‖ ≤ M` and `‖v‖ ≤ C`. -/
theorem norm_smul_le_mul_of_le {Z : Type*} [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
    {c M C : ℝ} {v : Z} (hc : ‖c‖ ≤ M) (hv : ‖v‖ ≤ C) : ‖c • v‖ ≤ M * C := by
  rw [norm_smul]
  exact mul_le_mul hc hv (norm_nonneg _) ((norm_nonneg _).trans hc)

/-- A continuous function on an open set `W ⊆ X × V` is bounded on `S × ι(α)` for a compact `S`
with `S × ι(α) ⊆ W`. -/
theorem exists_norm_le_of_continuousOn {X V α Z : Type*} [TopologicalSpace X] [TopologicalSpace V]
    [TopologicalSpace α] [CompactSpace α] [SeminormedAddCommGroup Z] {W : Set (X × V)}
    {Φ : X × V → Z} (hΦ : ContinuousOn Φ W) {ι : α → V} (hι : Continuous ι) {S : Set X}
    (hS : IsCompact S) (hSW : ∀ y ∈ S, ∀ a, (y, ι a) ∈ W) :
    ∃ C, ∀ y ∈ S, ∀ a, ‖Φ (y, ι a)‖ ≤ C := by
  have hT : IsCompact ((fun q : X × α => (q.1, ι q.2)) '' (S ×ˢ univ)) :=
    (hS.prod isCompact_univ).image (continuous_fst.prodMk (hι.comp continuous_snd))
  have hTW : (fun q : X × α => (q.1, ι q.2)) '' (S ×ˢ univ) ⊆ W := by
    rintro _ ⟨⟨y, a⟩, ⟨hy, -⟩, rfl⟩
    exact hSW y hy a
  obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn (hΦ.mono hTW)
  exact ⟨C, fun y hy a => hC _ ⟨(y, a), ⟨hy, mem_univ a⟩, rfl⟩⟩

/-- The Laplacian through directional derivatives: if `fderiv f` is differentiable at `y`, then
`Δ f y = ∑ᵢ ∂ᵢ (∂ᵢ f) y` over the standard orthonormal basis. -/
theorem laplacian_eq_sum_fderiv_fderiv_apply {f : E → ℝ} {y : E}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) y) :
    Δ f y = ∑ i, fderiv ℝ (fun x => fderiv ℝ f x (stdOrthonormalBasis ℝ E i)) y
      (stdOrthonormalBasis ℝ E i) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_clm_apply hf (differentiableAt_const _)]
  simp

/-- An integral of harmonic kernels is harmonic: if `K : E × V → ℝ` is `C³` on an open set `W`,
`ι : α → V` is continuous on a compact space `α` with a finite measure `μ`, `(x, ι a) ∈ W` for
`x ∈ U`, and each `K (·, ι a)` is harmonic on the open set `U`, then for every continuous
`g : α → ℝ` the function `x ↦ ∫ K (x, ι a) g(a) dμ(a)` is harmonic on `U`. -/
theorem harmonicOnNhd_integral_mul {μ : Measure α} [IsFiniteMeasure μ] {K : E × V → ℝ}
    {W : Set (E × V)} (hW : IsOpen W) (hK : ContDiffOn ℝ 3 K W) {ι : α → V} (hι : Continuous ι)
    {U : Set E} (hU : IsOpen U) (hUW : ∀ x ∈ U, ∀ a, (x, ι a) ∈ W)
    (hharm : ∀ a, HarmonicOnNhd (fun x => K (x, ι a)) U) {g : α → ℝ} (hg : Continuous g) :
    HarmonicOnNhd (fun x => ∫ a, K (x, ι a) * g a ∂μ) U := by
  have hKat : ∀ q ∈ W, ContDiffAt ℝ 3 K q := fun q hq => hK.contDiffAt (hW.mem_nhds hq)
  have hsw : ∀ q : E × V, ContDiffAt ℝ 3 (fun p : (E × V) × E => (p.2, p.1.2)) (q, q.1) :=
    fun q => contDiffAt_snd.prodMk contDiffAt_fst.snd
  have hP1 : ∀ q ∈ W, ContDiffAt ℝ 2
      (fun q : E × V => fderiv ℝ (fun z => K (z, q.2)) q.1) q := by
    intro q hq
    have hu : ContDiffAt ℝ 3 (Function.uncurry fun (q : E × V) (z : E) => K (z, q.2)) (q, q.1) :=
      (hKat q hq).comp (q, q.1) (hsw q)
    exact hu.fderiv contDiffAt_fst (by norm_num)
  have hP2 : ∀ v : E, ∀ q ∈ W, ContinuousAt
      (fun q : E × V => fderiv ℝ (fun y => fderiv ℝ (fun z => K (z, q.2)) y v) q.1) q := by
    intro v q hq
    have hu : ContDiffAt ℝ 2 (Function.uncurry fun (q : E × V) (y : E) =>
        fderiv ℝ (fun z => K (z, q.2)) y v) (q, q.1) :=
      ((hP1 q hq).clm_apply (contDiffAt_const (c := v))).comp (q, q.1)
        ((hsw q).of_le (by norm_num))
    exact (hu.fderiv (m := 1) contDiffAt_fst (by norm_num)).continuousAt
  have hcont0 : ContinuousOn K W := hK.continuousOn
  have hcont1 : ContinuousOn (fun q : E × V => fderiv ℝ (fun z => K (z, q.2)) q.1) W :=
    fun q hq => (hP1 q hq).continuousAt.continuousWithinAt
  have hcont2 : ∀ v : E, ContinuousOn
      (fun q : E × V => fderiv ℝ (fun y => fderiv ℝ (fun z => K (z, q.2)) y v) q.1) W :=
    fun v q hq => (hP2 v q hq).continuousWithinAt
  obtain ⟨D1, hD1⟩ : ∃ D1 : E → α → E →L[ℝ] ℝ,
      ∀ x a, D1 x a = fderiv ℝ (fun z => K (z, ι a)) x := ⟨_, fun _ _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : E → α → E → E →L[ℝ] ℝ,
      ∀ x a v, S x a v = fderiv ℝ (fun z => fderiv ℝ (fun z' => K (z', ι a)) z v) x :=
    ⟨_, fun _ _ _ => rfl⟩
  have hk : ∀ x ∈ U, ∀ a, ContDiffAt ℝ 3 (fun z => K (z, ι a)) x := fun x hx a =>
    (hKat _ (hUW x hx a)).comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hk2 : ∀ x ∈ U, ∀ a, DifferentiableAt ℝ (fderiv ℝ (fun z => K (z, ι a))) x :=
    fun x hx a => ((hk x hx a).fderiv_right (m := 2) (by norm_num)).differentiableAt
      (by norm_num)
  have hdK : ∀ x ∈ U, ∀ a, HasFDerivAt (fun y => K (y, ι a)) (D1 x a) x := by
    intro x hx a
    rw [hD1]
    exact ((hk x hx a).differentiableAt (by norm_num)).hasFDerivAt
  have hdD1 : ∀ x ∈ U, ∀ a v, HasFDerivAt (fun y => D1 y a v) (S x a v) x := by
    intro x hx a v
    simp only [hD1, hS]
    exact ((hk2 x hx a).clm_apply (differentiableAt_const v)).hasFDerivAt
  have hcK : ∀ y ∈ U, Continuous fun a => K (y, ι a) := fun y hy =>
    hcont0.comp_continuous (continuous_const.prodMk hι) fun a => hUW y hy a
  have hcD1 : ∀ y ∈ U, Continuous fun a => D1 y a := fun y hy => by
    simp only [hD1]
    exact hcont1.comp_continuous (continuous_const.prodMk hι) fun a => hUW y hy a
  have hcS : ∀ y ∈ U, ∀ v, Continuous fun a => S y a v := fun y hy v => by
    simp only [hS]
    exact (hcont2 v).comp_continuous (continuous_const.prodMk hι) fun a => hUW y hy a
  have hxS : ∀ x ∈ U, ∀ a v, ContinuousAt (fun y => S y a v) x := fun x hx a v => by
    have hpc : ContinuousAt (fun y : E => (y, ι a)) x :=
      (continuous_id.prodMk continuous_const).continuousAt
    simp only [hS]
    exact ContinuousAt.comp (f := fun y : E => (y, ι a)) (hP2 v _ (hUW x hx a)) hpc
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have hgM : ∀ a, ‖g a‖ ≤ M := fun a => hM a (mem_univ a)
  have hbd : ∀ x ∈ U, ∀ v : E, ∃ ε > 0, closedBall x ε ⊆ U ∧ ∃ C0 C1 C2 : ℝ,
      ∀ y ∈ closedBall x ε, ∀ a, ‖K (y, ι a)‖ ≤ C0 ∧ ‖D1 y a‖ ≤ C1 ∧ ‖S y a v‖ ≤ C2 := by
    intro x hx v
    obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hsub : closedBall x (ε' / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hε')).trans hball
    have hSW : ∀ y ∈ closedBall x (ε' / 2), ∀ a, (y, ι a) ∈ W := fun y hy a =>
      hUW y (hsub hy) a
    obtain ⟨C0, hC0⟩ := exists_norm_le_of_continuousOn hcont0 hι (isCompact_closedBall x _) hSW
    obtain ⟨C1, hC1⟩ := exists_norm_le_of_continuousOn (Z := E →L[ℝ] ℝ) hcont1 hι
      (isCompact_closedBall x _) hSW
    obtain ⟨C2, hC2⟩ := exists_norm_le_of_continuousOn (Z := E →L[ℝ] ℝ) (hcont2 v) hι
      (isCompact_closedBall x _) hSW
    refine ⟨ε' / 2, half_pos hε', hsub, C0, C1, C2, fun y hy a => ⟨hC0 y hy a, ?_, ?_⟩⟩
    · rw [hD1]
      exact hC1 y hy a
    · rw [hS]
      exact hC2 y hy a
  have happ : ∀ (L : E →L[ℝ] ℝ) (C : ℝ) (v : E) (a : α), ‖L‖ ≤ C →
      ‖g a * L v‖ ≤ M * (C * ‖v‖) := fun L C v a hL => by
    rw [norm_mul]
    exact mul_le_mul (hgM a) ((L.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))) (norm_nonneg _)
      ((norm_nonneg _).trans (hgM a))
  have hG1 : ∀ x ∈ U, HasFDerivAt (fun y => ∫ a, K (y, ι a) * g a ∂μ)
      (∫ a, g a • D1 x a ∂μ) x := by
    intro x hx
    obtain ⟨ε, hε, hsub, C0, C1, C2, hC⟩ := hbd x hx 0
    have hU' : ∀ y ∈ ball x ε, y ∈ U := fun y hy => hsub (ball_subset_closedBall hy)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => M * C1)
      (F := fun y a => K (y, ι a) * g a) (F' := fun y a => g a • D1 y a)
      (ball_mem_nhds x hε) ?_ ?_ ((hg.smul (hcD1 x hx)).aestronglyMeasurable) ?_
      (integrable_const _) ?_
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact ((hcK y hy).mul hg).aestronglyMeasurable
    · refine Integrable.of_bound ((hcK x hx).mul hg).aestronglyMeasurable (C0 * M)
        (ae_of_all _ fun a => ?_)
      rw [norm_mul]
      exact mul_le_mul (hC x (mem_closedBall_self hε.le) a).1 (hgM a) (norm_nonneg _)
        ((norm_nonneg _).trans (hC x (mem_closedBall_self hε.le) a).1)
    · exact ae_of_all _ fun a y hy => norm_smul_le_mul_of_le (hgM a)
        (hC y (ball_subset_closedBall hy) a).2.1
    · exact ae_of_all _ fun a y hy => (hdK y (hU' y hy) a).mul_const (g a)
  have hfdv : ∀ x ∈ U, ∀ v, fderiv ℝ (fun y => ∫ a, K (y, ι a) * g a ∂μ) x v =
      ∫ a, g a * D1 x a v ∂μ := by
    intro x hx v
    obtain ⟨ε, hε, hsub, C0, C1, C2, hC⟩ := hbd x hx v
    have hI1 := Integrable.of_bound (μ := μ) (f := fun a => g a • D1 x a)
      (hg.smul (hcD1 x hx)).aestronglyMeasurable (M * C1)
      (ae_of_all _ fun a => norm_smul_le_mul_of_le (hgM a) (hC x (mem_closedBall_self hε.le) a).2.1)
    rw [(hG1 x hx).fderiv, ContinuousLinearMap.integral_apply hI1]
    simp only [smul_apply, smul_eq_mul]
  have hH : ∀ x ∈ U, ∀ v, HasFDerivAt (fun y => ∫ a, g a * D1 y a v ∂μ)
      (∫ a, g a • S x a v ∂μ) x := by
    intro x hx v
    obtain ⟨ε, hε, hsub, C0, C1, C2, hC⟩ := hbd x hx v
    have hU' : ∀ y ∈ ball x ε, y ∈ U := fun y hy => hsub (ball_subset_closedBall hy)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => M * C2)
      (F := fun y a => g a * D1 y a v) (F' := fun y a => g a • S y a v)
      (ball_mem_nhds x hε) ?_ ?_ ((hg.smul (hcS x hx v)).aestronglyMeasurable) ?_
      (integrable_const _) ?_
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact (hg.mul ((hcD1 y hy).clm_apply continuous_const)).aestronglyMeasurable
    · exact Integrable.of_bound
        (hg.mul ((hcD1 x hx).clm_apply continuous_const)).aestronglyMeasurable
        (M * (C1 * ‖v‖)) (ae_of_all _ fun a =>
          happ _ C1 v a (hC x (mem_closedBall_self hε.le) a).2.1)
    · exact ae_of_all _ fun a y hy => norm_smul_le_mul_of_le (hgM a)
        (hC y (ball_subset_closedBall hy) a).2.2
    · exact ae_of_all _ fun a y hy => (hdD1 y (hU' y hy) a v).const_mul (g a)
  have hIS : ∀ y ∈ U, ∀ v w, Integrable (fun a => g a * S y a v w) μ := by
    intro y hy v w
    obtain ⟨ε, hε, hsub, C0, C1, C2, hC⟩ := hbd y hy v
    exact Integrable.of_bound
      (hg.mul ((hcS y hy v).clm_apply continuous_const)).aestronglyMeasurable
      (M * (C2 * ‖w‖)) (ae_of_all _ fun a =>
        happ _ C2 w a (hC y (mem_closedBall_self hε.le) a).2.2)
  have hfdH : ∀ x ∈ U, ∀ v w, fderiv ℝ (fun y => ∫ a, g a * D1 y a v ∂μ) x w =
      ∫ a, g a * S x a v w ∂μ := by
    intro x hx v w
    obtain ⟨ε, hε, hsub, C0, C1, C2, hC⟩ := hbd x hx v
    have hI := Integrable.of_bound (μ := μ) (f := fun a => g a • S x a v)
      (hg.smul (hcS x hx v)).aestronglyMeasurable (M * C2)
      (ae_of_all _ fun a => norm_smul_le_mul_of_le (hgM a) (hC x (mem_closedBall_self hε.le) a).2.2)
    rw [(hH x hx v).fderiv, ContinuousLinearMap.integral_apply hI]
    simp only [smul_apply, smul_eq_mul]
  have hcS2 : ∀ x ∈ U, ∀ v w, ContinuousAt (fun y => ∫ a, g a * S y a v w ∂μ) x := by
    intro x hx v w
    obtain ⟨ε, hε, hsub, C0, C1, C2, hC⟩ := hbd x hx v
    refine continuousAt_of_dominated (bound := fun _ => M * (C2 * ‖w‖))
      (F := fun y a => g a * S y a v w) ?_ ?_ (integrable_const _)
      (ae_of_all _ fun a => continuousAt_const.mul ((hxS x hx a v).clm_apply continuousAt_const))
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact (hg.mul ((hcS y hy v).clm_apply continuous_const)).aestronglyMeasurable
    · filter_upwards [ball_mem_nhds x hε] with y hy
      exact ae_of_all _ fun a => happ _ C2 w a (hC y (ball_subset_closedBall hy) a).2.2
  have hGC : ContDiffOn ℝ 2 (fun x => ∫ a, K (x, ι a) * g a ∂μ) U := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_fderiv_apply hU.uniqueDiffOn]
    refine ⟨fun x hx => (hG1 x hx).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, fun v => ?_⟩
    refine ContDiffOn.congr ?_ fun x hx => by rw [fderivWithin_of_isOpen hU hx, hfdv x hx v]
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_apply hU.uniqueDiffOn]
    refine ⟨fun x hx => (hH x hx v).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, fun w => ?_⟩
    rw [contDiffOn_zero]
    exact ContinuousOn.congr (fun x hx => (hcS2 x hx v w).continuousWithinAt) fun x hx => by
      rw [fderivWithin_of_isOpen hU hx, hfdH x hx v w]
  intro x hx
  refine ⟨hGC.contDiffAt (hU.mem_nhds hx), ?_⟩
  filter_upwards [hU.mem_nhds hx] with y hy
  have hGd : DifferentiableAt ℝ (fderiv ℝ (fun x => ∫ a, K (x, ι a) * g a ∂μ)) y :=
    ((hGC.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hka : ∀ a, ∑ i, S y a (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) = 0 := by
    intro a
    have h0 := (hharm a y hy).2.self_of_nhds
    rw [laplacian_eq_sum_fderiv_fderiv_apply (hk2 y hy a)] at h0
    simpa only [hS, Pi.zero_apply] using h0
  have hterm : ∀ i, fderiv ℝ (fun x => fderiv ℝ (fun x => ∫ a, K (x, ι a) * g a ∂μ) x
      (stdOrthonormalBasis ℝ E i)) y (stdOrthonormalBasis ℝ E i) =
      ∫ a, g a * S y a (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) ∂μ := fun i => by
    have hfH : (fun x => fderiv ℝ (fun x => ∫ a, K (x, ι a) * g a ∂μ) x
        (stdOrthonormalBasis ℝ E i)) =ᶠ[𝓝 y]
        fun x => ∫ a, g a * D1 x a (stdOrthonormalBasis ℝ E i) ∂μ :=
      Filter.eventually_of_mem (hU.mem_nhds hy) fun z hz => hfdv z hz _
    rw [hfH.fderiv_eq, hfdH y hy]
  rw [Pi.zero_apply, laplacian_eq_sum_fderiv_fderiv_apply hGd,
    Finset.sum_congr rfl fun i _ => hterm i, ← integral_finsetSum _ fun i _ => hIS y hy _ _]
  simp only [← Finset.mul_sum, hka, mul_zero, integral_zero]

end ParametricHarmonic

variable {d : ℕ}

/-- The Poisson integral of `f` over the unit sphere, normalized:
`poissonIntegral f x = ⨍ ζ, P(x, ζ) f(ζ) dσ(ζ)`. -/
def poissonIntegral (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨍ ζ, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) * f ζ
    ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere)

/-- The Poisson kernel is `C³` (indeed smooth) off the diagonal, jointly in both variables. -/
theorem contDiffOn_poissonKernel :
    ContDiffOn ℝ 3 (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      poissonKernel p.1 p.2) {p | p.1 ≠ p.2} := by
  intro p hp
  have hne : p.1 - p.2 ≠ 0 := sub_ne_zero.2 hp
  refine ContDiffAt.contDiffWithinAt ?_
  exact (contDiff_const.sub (contDiff_fst.norm_sq (𝕜 := ℝ))).contDiffAt.div
    (((contDiff_fst.sub contDiff_snd).contDiffAt.norm ℝ hne).pow d)
    (pow_ne_zero d (norm_ne_zero_iff.2 hne))

/-- The integral of the Poisson kernel against a function continuous on the unit sphere is
harmonic on the open unit ball. -/
theorem harmonicOnNhd_integral_poissonKernel_mul (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ContinuousOn f (sphere 0 1)) :
    HarmonicOnNhd (fun x => ∫ ζ, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) * f ζ
      ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere)) (ball 0 1) := by
  have hW : IsOpen {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) | p.1 ≠ p.2} :=
    isOpen_ne_fun continuous_fst continuous_snd
  have hUW : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∀ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        (x, (ζ : EuclideanSpace ℝ (Fin d))) ∈ {p : EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin d) | p.1 ≠ p.2} := by
    intro x hx ζ hxζ
    rw [mem_ball_zero_iff] at hx
    have h1 : ‖(ζ : EuclideanSpace ℝ (Fin d))‖ = 1 := norm_eq_of_mem_sphere ζ
    exact hx.ne (by rw [show x = (ζ : EuclideanSpace ℝ (Fin d)) from hxζ, h1])
  have hharm : ∀ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      HarmonicOnNhd (fun x => poissonKernel x (ζ : EuclideanSpace ℝ (Fin d))) (ball 0 1) :=
    fun ζ => (harmonicOnNhd_poissonKernel (norm_eq_of_mem_sphere ζ)).mono fun x hx =>
      hUW x hx ζ
  exact harmonicOnNhd_integral_mul
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) hW contDiffOn_poissonKernel
    continuous_subtype_val isOpen_ball hUW hharm
    (hf.comp_continuous continuous_subtype_val fun ζ => ζ.2)

/-- The Poisson integral of a function continuous on the unit sphere is harmonic on the open unit
ball. -/
theorem harmonicOnNhd_poissonIntegral (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ContinuousOn f (sphere 0 1)) :
    HarmonicOnNhd (poissonIntegral f) (ball 0 1) := by
  have hPI : poissonIntegral f =
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.real univ)⁻¹ • fun x =>
        ∫ ζ, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d)) * f ζ
          ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) := by
    funext x
    rw [poissonIntegral, average_eq, Pi.smul_apply]
  rw [hPI]
  exact (harmonicOnNhd_integral_poissonKernel_mul f hf).const_smul

/-- The surface measure of the unit sphere is invariant under the linear isometries of `ℝ ^ d`. -/
theorem integral_toSphere_comp_linearIsometryEquiv
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (F : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, F (A ζ)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      ∫ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, F ζ
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  have hmem : ∀ (C : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
      (ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
      C ζ ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    fun C ζ => by rw [mem_sphere_zero_iff_norm, C.norm_map, norm_eq_of_mem_sphere ζ]
  let e : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ≃ᵐ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    { toFun := fun ζ => ⟨A ζ, hmem A ζ⟩
      invFun := fun ζ => ⟨A.symm ζ, hmem A.symm ζ⟩
      left_inv := fun ζ => Subtype.ext (A.symm_apply_apply ζ)
      right_inv := fun ζ => Subtype.ext (A.apply_symm_apply ζ)
      measurable_toFun :=
        ((A.continuous.comp continuous_subtype_val).subtype_mk _).measurable
      measurable_invFun :=
        ((A.symm.continuous.comp continuous_subtype_val).subtype_mk _).measurable }
  have he : MeasurePreserving e (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
    refine ⟨e.measurable, Measure.ext fun s hs => ?_⟩
    rw [Measure.map_apply e.measurable hs, Measure.toSphere_apply' _ (e.measurable hs),
      Measure.toSphere_apply' _ hs]
    congr 1
    have h1 : ((↑) '' (e ⁻¹' s) : Set (EuclideanSpace ℝ (Fin d))) =
        A ⁻¹' ((↑) '' s) := by
      ext x
      constructor
      · rintro ⟨ζ, hζ, rfl⟩
        exact ⟨e ζ, hζ, rfl⟩
      · rintro ⟨η, hη, hx⟩
        have hxs : x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
          rw [mem_sphere_zero_iff_norm, ← A.norm_map, ← hx]
          exact norm_eq_of_mem_sphere η
        refine ⟨⟨x, hxs⟩, ?_, rfl⟩
        have hex : e ⟨x, hxs⟩ = η := Subtype.ext hx.symm
        rw [mem_preimage, hex]
        exact hη
    have h2 : Ioo (0 : ℝ) 1 • (A ⁻¹' ((↑) '' s : Set (EuclideanSpace ℝ (Fin d)))) =
        A ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set (EuclideanSpace ℝ (Fin d)))) := by
      ext x
      simp only [Set.mem_smul, mem_preimage]
      constructor
      · rintro ⟨r, hr, y, hy, rfl⟩
        exact ⟨r, hr, A y, hy, (A.map_smul r y).symm⟩
      · rintro ⟨r, hr, y, hy, hxy⟩
        refine ⟨r, hr, A.symm y, by simpa using hy, A.injective ?_⟩
        rw [A.map_smul, A.apply_symm_apply, hxy]
    rw [h1, h2]
    exact (A.measurePreserving.measure_preimage_emb A.toHomeomorph.measurableEmbedding _)
  exact he.integral_comp' (fun ζ => F ζ)

/-- The Poisson kernel is invariant under a simultaneous linear isometry of both variables. -/
theorem poissonKernel_map (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x ζ : EuclideanSpace ℝ (Fin d)) : poissonKernel (A x) (A ζ) = poissonKernel x ζ := by
  rw [poissonKernel, poissonKernel, A.norm_map, ← map_sub, A.norm_map]

/-- The integral of `P(x, ·)` over the unit sphere depends only on `‖x‖`. -/
theorem integral_poissonKernel_eq_of_norm_eq {y z : EuclideanSpace ℝ (Fin d)} (h : ‖y‖ = ‖z‖) :
    ∫ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, poissonKernel y ζ
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      ∫ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, poissonKernel z ζ
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  set R := Submodule.reflection (ℝ ∙ (y - z))ᗮ with hRdef
  have hR : R y = z := Submodule.reflection_sub h
  rw [← hR, ← integral_toSphere_comp_linearIsometryEquiv R (fun w => poissonKernel (R y) w)]
  simp only [poissonKernel_map]

/-- In dimension `d ≥ 1`, the integral of `P(x, ·)` over the unit sphere is the same for every `x`
in the open unit ball: the integral is harmonic in `x` and depends only on `‖x‖`, so its value at
`x` is its value at the exit position of a Brownian motion from the ball of radius `‖x‖` about
`0`, whose expectation is the value at `0` (Mörters–Peres, *Brownian Motion*, proof of
Theorem 3.43). -/
theorem integral_poissonKernel_eq_integral_poissonKernel_zero (hd : 1 ≤ d)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ‖x‖ < 1) :
    ∫ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, poissonKernel x ζ
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      ∫ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, poissonKernel (0 : EuclideanSpace ℝ (Fin d)) ζ
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  have hJ : HarmonicOnNhd (fun y : EuclideanSpace ℝ (Fin d) =>
      ∫ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      poissonKernel y ζ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) (ball 0 1) := by
    have := harmonicOnNhd_integral_poissonKernel_mul
      (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) continuousOn_const
    simpa only [mul_one] using this
  rcases eq_or_ne x 0 with rfl | hx0
  · rfl
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx0
  obtain ⟨Ω, mΩ, P, B, hB, -, -⟩ := exists_isBrownianSpace_cont d 0
  have := hB.isProbabilityMeasure
  have hh : HarmonicNearClosure (fun y : EuclideanSpace ℝ (Fin d) =>
      ∫ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      poissonKernel y ζ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere)
      (ball 0 ‖x‖) :=
    harmonicNearClosure_iff.2
      (hJ.mono (closure_ball_subset_closedBall.trans (closedBall_subset_ball hx)))
  have key := integral_openExit_harmonicNearClosure hd hB isOpen_ball isBounded_ball hh
  have hae : (fun ω => ∫ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      poissonKernel (B (openExitTime B (ball 0 ‖x‖) ω).toNNReal ω) ζ
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) =ᵐ[P]
      fun _ => ∫ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, poissonKernel x ζ
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere :=
    (hB.ae_mem_sphere_openExitTime_ball hd hr).mono fun ω hω =>
      integral_poissonKernel_eq_of_norm_eq (mem_sphere_zero_iff_norm.1 hω)
  rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul] at key
  exact key

/-- In dimension `d ≥ 1`, the Poisson kernel has average `1` over the unit sphere at every point
of the open unit ball. -/
theorem average_poissonKernel_eq_one (hd : 1 ≤ d) {x : EuclideanSpace ℝ (Fin d)}
    (hx : ‖x‖ < 1) :
    ⨍ ζ, poissonKernel x (ζ : EuclideanSpace ℝ (Fin d))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) = 1 := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  have : NeZero (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere :=
    ⟨Measure.toSphere_ne_zero _⟩
  have h0 : ∀ ζ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      poissonKernel (0 : EuclideanSpace ℝ (Fin d)) ζ = 1 := fun ζ => by
    rw [poissonKernel, norm_zero, zero_sub, norm_neg, norm_eq_of_mem_sphere ζ]
    norm_num
  rw [average_eq, integral_poissonKernel_eq_integral_poissonKernel_zero hd hx]
  simp only [h0, integral_const, smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ measureReal_univ_pos.ne'

end LatticeProb.Ishii
