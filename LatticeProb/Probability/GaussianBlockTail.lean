import LatticeProb.Bonanno.LQGDimension.LFPP.OscillationAux

/-!
# Block tails of planar Gaussian processes with increments Lipschitz in `L²`

Let `X = (X_z)_{z ∈ ℂ}` be a centred real Gaussian process whose increments satisfy
`Var(X_z - X_w) ≤ A |z - w| / ε` for some constants `A, ε > 0`. Then the maximal increment of
`X` over the disc `B(g, 10 ε)` has a Gaussian tail whose constants depend only on `A`:
for `t ≥ √(A/2) c`,
`P(sup_{|u - g| < 10 ε} |X_u - X_g| > t) ≤ 2 exp(-2 (t / √(A/2) - c)² / (20 π²))`,
where `c = LQGDimension.Osc37.chainConst` is the Dudley chaining constant of the unit block.

The proof is the Kolmogorov–Dudley chaining bound for the expected maximum together with the
Gaussian concentration of the maximum (Borell–TIS), applied to a Gram representation of the
finite-dimensional laws. For circle averages of the Gaussian free field this is
`LQGDimension.Osc37.block_event_bound`; that argument uses only the multivariate normal law of
the finite-dimensional marginals and the increment bound, which is the setting here.

## Main results

* `map_toLp_eq_multivariateGaussian`, `hasLaw_gaussVecLaw_of_isGaussianProcess`: the
  finite-dimensional laws of a centred real Gaussian process are the multivariate normal laws
  with its covariance matrix.
* `measure_exists_abs_sub_gt_le_of_finset`: the block tail over a finite subset of the disc.
* `measure_exists_ball_abs_sub_gt_le`: the block tail over the open disc, for a process whose
  paths are almost surely continuous.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped RealInnerProductSpace

namespace GaussianBlockTail

open LQGDimension LQGDimension.Osc37 LQGDimension.Blueprint.Draft

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Finite-dimensional laws of a centred Gaussian process.** For a centred real Gaussian
process indexed by a finite type, the law of its vector in `EuclideanSpace ℝ T` is the
multivariate normal law with mean `0` and the covariance matrix of the process. -/
theorem map_toLp_eq_multivariateGaussian {T : Type*} [Fintype T] [DecidableEq T]
    {Y : T → Ω → ℝ} (hY : IsGaussianProcess Y P) (hc : ∀ i, ∫ ω, Y i ω ∂P = 0) :
    P.map (fun ω => WithLp.toLp 2 (fun i => Y i ω)) =
      multivariateGaussian 0 (Matrix.of fun i j => cov[Y i, Y j; P]) := by
  have := hY.isProbabilityMeasure
  have hYf : HasGaussianLaw (fun ω => (fun i => Y i ω)) P :=
    (hY.hasGaussianLaw Finset.univ).map_fun
      (ContinuousLinearMap.pi fun i : T =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : (Finset.univ : Finset T) => ℝ)
          ⟨i, Finset.mem_univ i⟩)
  have hYv : HasGaussianLaw (fun ω => WithLp.toLp 2 (fun i => Y i ω)) P := hYf.toLp_pi 2
  have hY2 : ∀ i, MemLp (Y i) 2 P := fun i => (hY.hasGaussianLaw_eval i).memLp_two
  have : IsGaussian (P.map fun ω => WithLp.toLp 2 (fun i => Y i ω)) := hYv.isGaussian_map
  have hmean : ∫ x, id x ∂(P.map fun ω => WithLp.toLp 2 (fun i => Y i ω)) = 0 := by
    rw [integral_map hYv.aemeasurable aestronglyMeasurable_id]
    refine PiLp.ext fun p => ?_
    have h := (EuclideanSpace.proj (𝕜 := ℝ) p).integral_comp_comm hYv.integrable
    have h2 : ∀ x : EuclideanSpace ℝ T, EuclideanSpace.proj (𝕜 := ℝ) p x = x.ofLp p :=
      fun x => rfl
    simp only [h2] at h
    show (∫ ω, WithLp.toLp 2 (fun i => Y i ω) ∂P).ofLp p = (0 : EuclideanSpace ℝ T).ofLp p
    rw [← h]
    simp [hc]
  set Cm : Matrix T T ℝ := Matrix.of fun i j => cov[Y i, Y j; P] with hCm_def
  have hcovB : ∀ x y : EuclideanSpace ℝ T,
      covarianceBilin (P.map fun ω => WithLp.toLp 2 (fun i => Y i ω)) x y =
        ∑ i, ∑ j, x.ofLp i * y.ofLp j * cov[Y i, Y j; P] :=
    fun x y => covarianceBilin_apply_pi hY2 x y
  have hCm : Cm.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j
      simp [hCm_def, covariance_comm]
    · have h := covarianceBilin_self_nonneg
        (μ := P.map fun ω => WithLp.toLp 2 (fun i => Y i ω)) (WithLp.toLp 2 x)
      rw [hcovB] at h
      refine h.trans_eq ?_
      simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum, hCm_def,
        Matrix.of_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hcov : covarianceBilin (P.map fun ω => WithLp.toLp 2 (fun i => Y i ω)) =
      covarianceBilin (multivariateGaussian 0 Cm) := by
    refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
    rw [hcovB, covarianceBilin_multivariateGaussian hCm]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, hCm_def, Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  exact IsGaussian.ext (by rw [hmean, integral_id_multivariateGaussian']) hcov

/-- **Finite-dimensional laws, `gaussVecLaw` form.** For a centred real Gaussian process `X`
and a finite set `F` of indices, the vector `(X_i)_{i ∈ F}` has the centred Gaussian law on
`F → ℝ` with covariance `cov[X_i, X_j]`. -/
theorem hasLaw_gaussVecLaw_of_isGaussianProcess {ι : Type*} {X : ι → Ω → ℝ}
    (hX : IsGaussianProcess X P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0) (F : Finset ι) :
    HasLaw (fun ω (i : F) => X i ω) (gaussVecLaw F fun i j => cov[X i, X j; P]) P := by
  classical
  have hXF : IsGaussianProcess (fun i : F => X i) P := hX.comp_right fun i : F => (i : ι)
  have hm : P.map (fun ω => WithLp.toLp 2 (fun i : F => X i ω)) =
      multivariateGaussian 0 (Matrix.of fun i j : F => cov[X i, X j; P]) :=
    map_toLp_eq_multivariateGaussian hXF fun i => hc i
  have hYv : AEMeasurable (fun ω => WithLp.toLp 2 (fun i : F => X i ω)) P :=
    (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable
      (AEMeasurable.of_eval fun i => hX.aemeasurable (i : ι))
  have hg : Measurable fun (x : EuclideanSpace ℝ F) (i : F) => x i :=
    (PiLp.continuous_ofLp 2 (fun _ : F => ℝ)).measurable
  refine ⟨AEMeasurable.of_eval fun i => hX.aemeasurable (i : ι), ?_⟩
  calc P.map (fun ω (i : F) => X i ω)
      = (P.map fun ω => WithLp.toLp 2 (fun i : F => X i ω)).map
          (fun (x : EuclideanSpace ℝ F) (i : F) => x i) :=
        (AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hYv).symm
    _ = gaussVecLaw F fun i j => cov[X i, X j; P] := by
        rw [hm, gaussVecLaw]

/-- **Block tail over a finite set.** Let `X` be a centred real Gaussian process on `ℂ` with
`Var(X_z - X_w) ≤ A |z - w| / ε`. For a finite set `F ∋ g` inside the disc `B(g, 10 ε)` and
`t ≥ √(A/2) c` (`c = chainConst`),
`P(∃ z ∈ F, |X_z - X_g| > t) ≤ 2 exp(-2 (t / √(A/2) - c)² / (20 π²))`. -/
theorem measure_exists_abs_sub_gt_le_of_finset {X : ℂ → Ω → ℝ} (hX : IsGaussianProcess X P)
    (hc : ∀ z, ∫ ω, X z ω ∂P = 0) {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε)
    (hinc : ∀ z w, Var[fun ω => X z ω - X w ω; P] ≤ A * ‖z - w‖ / ε)
    (F : Finset ℂ) {g : ℂ} (hgF : g ∈ F) (hF : ∀ z ∈ F, ‖z - g‖ < 10 * ε) {t : ℝ}
    (ht : √(A / 2) * chainConst ≤ t) :
    P {ω | ∃ z ∈ F, t < |X z ω - X g ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (t / √(A / 2) - chainConst) ^ 2 / (π ^ 2 * 20))) := by
  have := hX.isProbabilityMeasure
  set c : ℝ := √(A / 2) with hc_def
  have hcpos : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hm : ∀ z, MemLp (X z) 2 P := fun z => (hX.hasGaussianLaw_eval z).memLp_two
  have hlaw := hasLaw_gaussVecLaw_of_isGaussianProcess hX hc F
  obtain ⟨S, hSdef⟩ : ∃ S : Set (F → ℝ), S = {y | ∃ i : F, t < |y i - y ⟨g, hgF⟩|} :=
    ⟨_, rfl⟩
  have hS : MeasurableSet S := by
    rw [hSdef, Set.ofPred_exists]
    exact MeasurableSet.iUnion fun i => (isOpen_lt continuous_const
      (((continuous_apply i).sub (continuous_apply (⟨g, hgF⟩ : F))).abs)).measurableSet
  have h0 : (0 : F → ℝ) ∉ S := by
    rw [hSdef]
    rintro ⟨i, hi⟩
    simp only [Pi.zero_apply, sub_self, abs_zero] at hi
    have : 0 ≤ c * chainConst := mul_nonneg hcpos.le chainConst_nonneg
    linarith
  have hset : {ω | ∃ z ∈ F, t < |X z ω - X g ω|} = (fun ω (i : F) => X i ω) ⁻¹' S := by
    rw [hSdef]
    ext ω
    constructor
    · rintro ⟨z, hz, hlt⟩
      exact ⟨⟨z, hz⟩, hlt⟩
    · rintro ⟨⟨z, hz⟩, hlt⟩
      exact ⟨z, hz, hlt⟩
  rw [hset]
  refine measure_preimage_le_of_gram F _ hlaw hS h0 _ fun v hv => ?_
  have hinc' : ∀ i ∈ F, ∀ j ∈ F,
      ‖(fun z => c⁻¹ • v z) i - (fun z => c⁻¹ • v z) j‖ ^ 2 ≤ 2 * ‖i - j‖ / ε := by
    intro i hi j hj
    have hvv : ‖v i - v j‖ ^ 2 = Var[fun ω => X i ω - X j ω; P] := by
      rw [variance_fun_sub (hm i) (hm j), ← covariance_self (hX.aemeasurable i),
        ← covariance_self (hX.aemeasurable j), norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, hv i hi i hi, hv i hi j hj, hv j hj j hj]
    have hscale : ‖c⁻¹ • v i - c⁻¹ • v j‖ ^ 2 = c⁻¹ ^ 2 * ‖v i - v j‖ ^ 2 := by
      rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hc2 : c⁻¹ ^ 2 = 2 / A := by
      rw [inv_pow, hc_def, Real.sq_sqrt (by positivity)]
      field_simp
    show ‖c⁻¹ • v i - c⁻¹ • v j‖ ^ 2 ≤ 2 * ‖i - j‖ / ε
    rw [hscale, hvv, hc2]
    calc 2 / A * Var[fun ω => X i ω - X j ω; P] ≤ 2 / A * (A * ‖i - j‖ / ε) := by
          gcongr
          exact hinc i j
      _ = 2 * ‖i - j‖ / ε := by field_simp
  have ht' : chainConst ≤ t / c := by
    rw [le_div_iff₀ hcpos]
    linarith [mul_comm c chainConst]
  have hB := std_block_bound F (fun z => c⁻¹ • v z) hgF hε hF hinc' ht'
  rw [hSdef]
  refine le_trans (measure_mono fun x hx => ?_) hB
  obtain ⟨i, hi⟩ := hx
  have hi' : t < |⟪v i, x⟫ - ⟪v g, x⟫| := hi
  refine ⟨i, ?_⟩
  show t / c < |⟪c⁻¹ • v i, x⟫ - ⟪c⁻¹ • v g, x⟫|
  rw [real_inner_smul_left, real_inner_smul_left, ← mul_sub, abs_mul, abs_inv,
    abs_of_pos hcpos, div_eq_inv_mul]
  exact mul_lt_mul_of_pos_left hi' (inv_pos.2 hcpos)

/-- **Block tail over a disc.** Let `X` be a centred real Gaussian process on `ℂ` with almost
surely continuous paths and `Var(X_z - X_w) ≤ A |z - w| / ε`. For `t ≥ √(A/2) c`
(`c = chainConst`),
`P(∃ u, |u - g| < 10 ε ∧ |X_u - X_g| > t) ≤ 2 exp(-2 (t / √(A/2) - c)² / (20 π²))`. -/
theorem measure_exists_ball_abs_sub_gt_le {X : ℂ → Ω → ℝ} (hX : IsGaussianProcess X P)
    (hc : ∀ z, ∫ ω, X z ω ∂P = 0) (hcont : ∀ᵐ ω ∂P, Continuous fun z => X z ω) {A ε : ℝ}
    (hA : 0 < A) (hε : 0 < ε)
    (hinc : ∀ z w, Var[fun ω => X z ω - X w ω; P] ≤ A * ‖z - w‖ / ε) (g : ℂ) {t : ℝ}
    (ht : √(A / 2) * chainConst ≤ t) :
    P {ω | ∃ u : ℂ, ‖u - g‖ < 10 * ε ∧ t < |X u ω - X g ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (t / √(A / 2) - chainConst) ^ 2 / (π ^ 2 * 20))) := by
  classical
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ℂ
  let Fn : ℕ → Finset ℂ := fun n =>
    insert g (((Finset.range n).image u).filter fun z => ‖z - g‖ < 10 * ε)
  have hFn : ∀ n, ∀ z ∈ Fn n, ‖z - g‖ < 10 * ε := by
    intro n z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [sub_self, norm_zero]
      positivity
    · exact (Finset.mem_filter.1 hz).2
  have hmono : Monotone fun n => {ω | ∃ z ∈ Fn n, t < |X z ω - X g ω|} := by
    rintro m n hmn ω ⟨z, hz, hlt⟩
    refine ⟨z, ?_, hlt⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨?_, (Finset.mem_filter.1 hz).2⟩)
      obtain ⟨k, hk, hkz⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hz).1
      exact Finset.mem_image.2
        ⟨k, Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hk) hmn), hkz⟩
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | ∃ u' : ℂ, ‖u' - g‖ < 10 * ε ∧ t < |X u' ω - X g ω|} →
      ω ∈ ⋃ n, {ω | ∃ z ∈ Fn n, t < |X z ω - X g ω|} := by
    filter_upwards [hcont] with ω hcω
    rintro ⟨u₀, hu₀, hlt⟩
    have hO : IsOpen {z : ℂ | ‖z - g‖ < 10 * ε ∧ t < |X z ω - X g ω|} :=
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).inter
        (isOpen_lt continuous_const ((hcω.sub continuous_const).abs))
    obtain ⟨k, hk1, hk2⟩ := hu.exists_mem_open hO ⟨u₀, hu₀, hlt⟩
    refine mem_iUnion.2 ⟨k + 1, u k, ?_, hk2⟩
    exact Finset.mem_insert_of_mem (Finset.mem_filter.2
      ⟨Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_self k), rfl⟩, hk1⟩)
  calc P _ ≤ P (⋃ n, {ω | ∃ z ∈ Fn n, t < |X z ω - X g ω|}) := measure_mono_ae hsub
    _ = ⨆ n, P {ω | ∃ z ∈ Fn n, t < |X z ω - X g ω|} := hmono.measure_iUnion
    _ ≤ _ := iSup_le fun n =>
        measure_exists_abs_sub_gt_le_of_finset hX hc hA hε hinc (Fn n)
          (Finset.mem_insert_self _ _) (hFn n) ht

end GaussianBlockTail
