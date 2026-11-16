import LatticeProb.Analysis.Schauder.SineCoeff
import LatticeProb.Analysis.Schauder.SineDensity

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.TwoScale.SineSeries`.

# The sine series of a test function

The sine series `sineSeries a = Σ_k a_k φ_k` with coefficients `a`, and `sineSum f`, the sine series
with the sine coefficients of `f`. For a test function `f` of the open unit cube and `z` in the
cube, `Σ_k ⟨f, φ_k⟩ φ_k(z) = f(z)`, absolutely. The coefficients are summable by their rapid decay
(`summable_pow_mul_abs_sineCoeff`), so the series converges absolutely and uniformly to a continuous
function whose sine coefficients are those of `f` (`integral_sineSum_mul_sineMode`, from the
orthonormality of the sine modes). The remainder is therefore orthogonal to every sine mode, hence
(after multiplying by `Π_i sin(π z_i) > 0`) to the span of the sine monomials, which is dense by the
Stone–Weierstrass argument of `SineDensity`, so it vanishes.
-/

open MeasureTheory LatticeProb

noncomputable section

namespace LatticeProb.Analysis.Schauder

variable {d : ℕ}

/-- A product of one-variable summable nonnegative sequences is summable over `ℕ^d`. -/
theorem summable_prod_pi {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) :
    Summable fun k : Fin d → ℕ => ∏ i, g (k i) := by
  refine summable_of_sum_le (c := (∑' n, g n) ^ d)
    (fun k => Finset.prod_nonneg fun i _ => hg0 _) ?_
  intro u
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ k ∈ u, ∀ i, k i < M :=
    ⟨u.sup (fun k => Finset.univ.sup k) + 1, fun k hk i =>
      Nat.lt_succ_of_le ((Finset.le_sup (Finset.mem_univ i)).trans
        (Finset.le_sup (f := fun k : Fin d → ℕ => Finset.univ.sup k) hk))⟩
  calc ∑ k ∈ u, ∏ i, g (k i)
      ≤ ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range M), ∏ i, g (k i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ =>
          Finset.prod_nonneg fun i _ => hg0 _
        intro k hk
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (hM k hk i)
    _ = ∏ _i : Fin d, ∑ n ∈ Finset.range M, g n := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : Fin d, ∑' n, g n :=
        Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun n _ => hg0 n)
          fun _ _ => hg.sum_le_tsum _ fun n _ => hg0 n
    _ = (∑' n, g n) ^ d := by simp

/-- The inverse squared frequencies `((π (n + 1))²)⁻¹` of the one-variable sine modes are summable
over `ℕ`. -/
theorem summable_inv_sq_pi_mul_succ :
    Summable fun n : ℕ => ((Real.pi * ((n : ℝ) + 1)) ^ 2)⁻¹ := by
  have h1 : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
  refine (h1.mul_left (Real.pi ^ 2)⁻¹).congr fun n => ?_
  push_cast
  rw [mul_pow, mul_inv, one_div]

/-- The `d`-th power of the eigenvalue dominates the product of the squared frequencies. -/
theorem prod_sq_le_dirichletEigenvalue_pow (k : Fin d → ℕ) :
    ∏ i, (Real.pi * ((k i : ℝ) + 1)) ^ 2 ≤ dirichletEigenvalue k ^ d := by
  calc ∏ i, (Real.pi * ((k i : ℝ) + 1)) ^ 2 ≤ ∏ _i : Fin d, dirichletEigenvalue k :=
        Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ =>
          sineFreqSq_le_dirichletEigenvalue i k
    _ = dirichletEigenvalue k ^ d := by simp

/-- The inverse powers `(λ_k^d)⁻¹` of the eigenvalues are summable over `ℕ^d`. -/
theorem summable_inv_dirichletEigenvalue_pow :
    Summable fun k : Fin d → ℕ => ((dirichletEigenvalue k) ^ d)⁻¹ := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (summable_prod_pi (fun n => by positivity) summable_inv_sq_pi_mul_succ)
  · exact inv_nonneg.2 (pow_nonneg (dirichletEigenvalue_nonneg k) _)
  · rw [Finset.prod_inv_distrib]
    exact inv_anti₀ (Finset.prod_pos fun i _ => by positivity)
      (prod_sq_le_dirichletEigenvalue_pow k)

/-- Every polynomial moment of the sine coefficients is summable. -/
theorem summable_pow_mul_abs_sineCoeff (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (m : ℕ) :
    Summable fun k : Fin d → ℕ => dirichletEigenvalue k ^ m * |sineCoeff f k| := by
  obtain ⟨C, hC⟩ := exists_abs_sineCoeff_le hd f hf (m + d)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg
    (pow_nonneg (dirichletEigenvalue_pos hd k).le _) (abs_nonneg _)) (fun k => ?_)
    (summable_inv_dirichletEigenvalue_pow.mul_left |C|)
  have hpos := dirichletEigenvalue_pos hd k
  calc dirichletEigenvalue k ^ m * |sineCoeff f k|
      ≤ dirichletEigenvalue k ^ m * (|C| * ((dirichletEigenvalue k) ^ (m + d))⁻¹) := by
        refine mul_le_mul_of_nonneg_left ((hC k).trans ?_) (pow_nonneg hpos.le _)
        exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ = |C| * ((dirichletEigenvalue k) ^ d)⁻¹ := by
        rw [pow_add, mul_inv]
        field_simp

/-- The sine coefficients of a test function are absolutely summable. -/
theorem summable_abs_sineCoeff (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) : Summable fun k : Fin d → ℕ => |sineCoeff f k| := by
  simpa using summable_pow_mul_abs_sineCoeff hd f hf 0

/-- The integral of `cos (m π t)` over the unit interval for an integer frequency `m`. -/
theorem integral_cos_int_mul_pi (m : ℤ) :
    ∫ t in (0 : ℝ)..1, Real.cos ((m : ℝ) * Real.pi * t) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · have hc : (m : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by exact_mod_cast hm) Real.pi_ne_zero
    rw [ite_eq_right hm, intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hc, integral_cos]
    simp [Real.sin_int_mul_pi]

/-- The one-variable sine modes `√2 sin (π (a+1) t)` are orthonormal in `L²(0,1)`. -/
theorem integral_sineFactor_mul (a b : ℕ) :
    ∫ t in Set.Ioo (0 : ℝ) 1, (Real.sqrt 2 * Real.sin (Real.pi * ((a : ℝ) + 1) * t)) *
      (Real.sqrt 2 * Real.sin (Real.pi * ((b : ℝ) + 1) * t)) = if a = b then 1 else 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hfun : ∀ t : ℝ, (Real.sqrt 2 * Real.sin (Real.pi * ((a : ℝ) + 1) * t)) *
      (Real.sqrt 2 * Real.sin (Real.pi * ((b : ℝ) + 1) * t)) =
      Real.cos (((a : ℤ) - (b : ℤ) : ℤ) * Real.pi * t) -
        Real.cos (((a : ℤ) + (b : ℤ) + 2 : ℤ) * Real.pi * t) := fun t => by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have e1 : ((((a : ℤ) - (b : ℤ) : ℤ) : ℝ)) * Real.pi * t =
        Real.pi * ((a : ℝ) + 1) * t - Real.pi * ((b : ℝ) + 1) * t := by push_cast; ring
    have e2 : ((((a : ℤ) + (b : ℤ) + 2 : ℤ) : ℝ)) * Real.pi * t =
        Real.pi * ((a : ℝ) + 1) * t + Real.pi * ((b : ℝ) + 1) * t := by push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    calc _ = (Real.sqrt 2 * Real.sqrt 2) * (Real.sin (Real.pi * ((a : ℝ) + 1) * t) *
          Real.sin (Real.pi * ((b : ℝ) + 1) * t)) := by ring
      _ = _ := by rw [h2]; ring
  simp_rw [hfun]
  rw [intervalIntegral.integral_sub, integral_cos_int_mul_pi, integral_cos_int_mul_pi]
  · have h3 : ((a : ℤ) + (b : ℤ) + 2 : ℤ) ≠ 0 := by omega
    have h4 : (((a : ℤ) - (b : ℤ) : ℤ) = 0) ↔ a = b := by omega
    simp only [h3, h4, ↓reduceIte]
    simp
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- The integral over the unit cube of a product of one-variable functions. -/
theorem integral_unitCube_prod (g : Fin d → ℝ → ℝ) :
    ∫ z in unitCube d, ∏ i, g i (z i) = ∏ i, ∫ t in Set.Ioo (0 : ℝ) 1, g i t := by
  rw [← integral_indicator measurableSet_unitCube]
  have h1 : (unitCube d).indicator (fun z : Euc d => ∏ i, g i (z i)) =
      fun z => ∏ i, (Set.Ioo (0 : ℝ) 1).indicator (g i) (z i) := by
    funext z
    by_cases hz : z ∈ unitCube d
    · rw [Set.indicator_of_mem hz]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (show z i ∈ Set.Ioo (0 : ℝ) 1 from hz i) _).symm
    · rw [Set.indicator_of_notMem hz]
      obtain ⟨i, hi⟩ : ∃ i, z i ∉ Set.Ioo (0 : ℝ) 1 := by
        simpa [unitCube] using hz
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [h1]
  have h2 := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
    (g := fun y : Fin d → ℝ => ∏ i, (Set.Ioo (0 : ℝ) 1).indicator (g i) (y i))
  refine h2.trans ?_
  rw [volume_pi, integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (fun i => (Set.Ioo (0 : ℝ) 1).indicator (g i))]
  exact Finset.prod_congr rfl fun i _ => integral_indicator measurableSet_Ioo

/-- The open unit cube has finite volume. -/
theorem measure_unitCube_lt_top : volume (unitCube d) < ⊤ :=
  (isCompact_closedCube.measure_lt_top).trans_le' (measure_mono unitCube_subset_closedCube)

/-- The restriction of the volume to the open unit cube is a finite measure. -/
theorem isFiniteMeasure_restrict_unitCube : IsFiniteMeasure (volume.restrict (unitCube d)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_unitCube_lt_top⟩

/-- The sine modes are orthonormal in `L²(Q)`. -/
theorem integral_sineMode_mul (j k : Fin d → ℕ) :
    ∫ z in unitCube d, sineMode j z * sineMode k z = if j = k then 1 else 0 := by
  have h1 : ∀ z : Euc d, sineMode j z * sineMode k z = ∏ i,
      (Real.sqrt 2 * Real.sin (Real.pi * ((j i : ℝ) + 1) * z i)) *
        (Real.sqrt 2 * Real.sin (Real.pi * ((k i : ℝ) + 1) * z i)) := fun z => by
    unfold sineMode
    exact Finset.prod_mul_distrib.symm
  simp_rw [h1]
  rw [integral_unitCube_prod (fun i t =>
    (Real.sqrt 2 * Real.sin (Real.pi * ((j i : ℝ) + 1) * t)) *
      (Real.sqrt 2 * Real.sin (Real.pi * ((k i : ℝ) + 1) * t)))]
  simp_rw [integral_sineFactor_mul]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

/-- The sine series `Σ_k a_k φ_k` with coefficients `a`. -/
def sineSeries (a : (Fin d → ℕ) → ℝ) (z : Euc d) : ℝ := ∑' k, a k * sineMode k z

/-- The sine series `Σ_k ⟨f, φ_k⟩ φ_k` of a function `f`, as a function of the point. -/
def sineSum (f : Euc d → ℝ) (z : Euc d) : ℝ := ∑' k : Fin d → ℕ, sineCoeff f k * sineMode k z

/-- The sine series of a function `f` is the sine series with the sine coefficients of `f`. -/
theorem sineSum_eq_sineSeries (f : Euc d → ℝ) : sineSum f = sineSeries (sineCoeff f) := rfl

/-- The summands of the sine series of a test function are dominated by a summable series. -/
theorem norm_sineCoeff_mul_sineMode_le (f : Euc d → ℝ) (k : Fin d → ℕ) (z : Euc d) :
    ‖sineCoeff f k * sineMode k z‖ ≤ |sineCoeff f k| * Real.sqrt 2 ^ d := by
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_sineMode_le k z) (abs_nonneg _)

/-- The sine series of a test function converges absolutely at every point. -/
theorem summable_sineCoeff_mul_sineMode (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (z : Euc d) :
    Summable fun k : Fin d → ℕ => sineCoeff f k * sineMode k z :=
  Summable.of_norm_bounded ((summable_abs_sineCoeff hd f hf).mul_right (Real.sqrt 2 ^ d))
    fun k => norm_sineCoeff_mul_sineMode_le f k z

/-- The sine series of a test function is continuous. -/
theorem continuous_sineSum (hd : 1 ≤ d) (f : Euc d → ℝ) (hf : Sobolev.IsTestFn (unitCube d) f) :
    Continuous (sineSum f) :=
  continuous_tsum (fun k => continuous_const.mul (contDiff_sineMode k).continuous)
    ((summable_abs_sineCoeff hd f hf).mul_right (Real.sqrt 2 ^ d))
    fun k z => norm_sineCoeff_mul_sineMode_le f k z

/-- A sine mode is bounded on the open cube in norm by `(√2)^d`. -/
theorem norm_sineMode_le (k : Fin d → ℕ) (z : Euc d) : ‖sineMode k z‖ ≤ Real.sqrt 2 ^ d :=
  (Real.norm_eq_abs _).le.trans (abs_sineMode_le k z)

/-- **The sine coefficients of the sine series are the sine coefficients of `f`.** -/
theorem integral_sineSum_mul_sineMode (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (k : Fin d → ℕ) :
    ∫ z in unitCube d, sineSum f z * sineMode k z = sineCoeff f k := by
  have := isFiniteMeasure_restrict_unitCube (d := d)
  set F : (Fin d → ℕ) → Euc d → ℝ := fun j z => sineCoeff f j * sineMode j z * sineMode k z with hF
  have hint : ∀ j, Integrable (F j) (volume.restrict (unitCube d)) := fun j =>
    Integrable.of_bound
      ((continuous_const.mul (contDiff_sineMode j).continuous).mul
        (contDiff_sineMode k).continuous).aestronglyMeasurable
      (|sineCoeff f j| * Real.sqrt 2 ^ d * Real.sqrt 2 ^ d)
      (Filter.Eventually.of_forall fun z => by
        rw [hF, norm_mul]
        exact mul_le_mul (norm_sineCoeff_mul_sineMode_le f j z) (norm_sineMode_le k z)
          (norm_nonneg _) (by positivity))
  have hb : ∀ j z, ‖F j z‖ ≤ |sineCoeff f j| * Real.sqrt 2 ^ d * Real.sqrt 2 ^ d := fun j z => by
    rw [hF, norm_mul]
    exact mul_le_mul (norm_sineCoeff_mul_sineMode_le f j z) (norm_sineMode_le k z)
      (norm_nonneg _) (by positivity)
  have hsum : Summable fun j => ∫ z, ‖F j z‖ ∂(volume.restrict (unitCube d)) := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun z => norm_nonneg _)
      (fun j => ?_) ((summable_abs_sineCoeff hd f hf).mul_right
        (Real.sqrt 2 ^ d * Real.sqrt 2 ^ d * (volume (unitCube d)).toReal))
    calc ∫ z, ‖F j z‖ ∂(volume.restrict (unitCube d))
        ≤ ‖∫ z, ‖F j z‖ ∂(volume.restrict (unitCube d))‖ := Real.le_norm_self _
      _ ≤ (|sineCoeff f j| * Real.sqrt 2 ^ d * Real.sqrt 2 ^ d) *
          (volume.restrict (unitCube d)).real Set.univ :=
          norm_integral_le_of_norm_le_const
            (Filter.Eventually.of_forall fun z => by rw [norm_norm]; exact hb j z)
      _ = |sineCoeff f j| * (Real.sqrt 2 ^ d * Real.sqrt 2 ^ d * (volume (unitCube d)).toReal) := by
          rw [Measure.real, Measure.restrict_apply_univ]
          ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have h1 : ∀ j, ∫ z in unitCube d, F j z = if j = k then sineCoeff f k else 0 := fun j => by
    simp only [hF, mul_assoc]
    rw [integral_const_mul, integral_sineMode_mul]
    split_ifs with hjk
    · subst hjk
      simp
    · simp
  have h2 : ∫ z in unitCube d, ∑' j, F j z = ∫ z in unitCube d, sineSum f z * sineMode k z := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ∑' j, sineCoeff f j * sineMode j z * sineMode k z = sineSum f z * sineMode k z
    unfold sineSum
    rw [tsum_mul_right]
  simp_rw [h1] at h
  rw [← h2]
  exact ((hasSum_ite_eq k (sineCoeff f k)).unique h).symm

/-- A continuous function is integrable on the open cube. -/
theorem integrableOn_unitCube {g : Euc d → ℝ} (hg : Continuous g) :
    IntegrableOn g (unitCube d) :=
  (hg.continuousOn.integrableOn_compact isCompact_closedCube).mono_set unitCube_subset_closedCube

/-- A nonnegative continuous function with zero integral over the open cube vanishes on it. -/
theorem eq_zero_of_integral_eq_zero {h : Euc d → ℝ} (hc : Continuous h)
    (h0 : ∀ z ∈ unitCube d, 0 ≤ h z) (hI : ∫ z in unitCube d, h z = 0) :
    ∀ z ∈ unitCube d, h z = 0 := by
  intro z hz
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_unitCube).2 (Filter.Eventually.of_forall h0))
    (integrableOn_unitCube hc)).1 hI
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_unitCube] at hae
  by_contra hne
  have hopen : IsOpen {x : Euc d | x ∈ unitCube d ∧ h x ≠ 0} :=
    isOpen_unitCube.inter (isOpen_ne_fun hc continuous_const)
  have hpos := hopen.measure_pos volume ⟨z, hz, hne⟩
  rw [ae_iff] at hae
  refine hpos.ne' (measure_mono_null (fun x hx => ?_) hae)
  exact fun h' => hx.2 (h' hx.1)

/-- The remainder `f − Σ_k ⟨f, φ_k⟩ φ_k` of the sine series of `f`. -/
def sineRemainder (f : Euc d → ℝ) (z : Euc d) : ℝ := f z - sineSum f z

/-- The remainder of the sine series of a test function is continuous. -/
theorem continuous_sineRemainder (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) : Continuous (sineRemainder f) :=
  hf.1.continuous.sub (continuous_sineSum hd f hf)

/-- The remainder of the sine series is orthogonal to every sine mode. -/
theorem integral_sineRemainder_mul_sineMode (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (k : Fin d → ℕ) :
    ∫ z in unitCube d, sineRemainder f z * sineMode k z = 0 := by
  have hφ := (contDiff_sineMode (d := d) k).continuous
  unfold sineRemainder
  simp_rw [sub_mul]
  rw [integral_sub (f := fun z => f z * sineMode k z) (g := fun z => sineSum f z * sineMode k z)
    (integrableOn_unitCube (hf.1.continuous.mul hφ))
    (integrableOn_unitCube ((continuous_sineSum hd f hf).mul hφ)),
    integral_sineSum_mul_sineMode hd f hf k, sub_eq_zero]
  rfl

/-- A sine monomial with all frequencies nonzero is a constant multiple of a sine mode. -/
theorem exists_sineMonomial_eq_mul_sineMode (j : Fin d → ℤ) (hj : ∀ i, j i ≠ 0) :
    ∃ (c : ℝ) (k : Fin d → ℕ), ∀ z, sineMonomial j z = c * sineMode k z := by
  have hn : ∀ i, 1 ≤ (j i).natAbs := fun i => Int.natAbs_pos.2 (hj i)
  refine ⟨(∏ i, if 0 ≤ j i then (1 : ℝ) else -1) * ((Real.sqrt 2 ^ d)⁻¹),
    fun i => (j i).natAbs - 1, fun z => ?_⟩
  have hs : ∀ i, Real.sin (Real.pi * (j i : ℝ) * z i) =
      (if 0 ≤ j i then (1 : ℝ) else -1) *
        Real.sin (Real.pi * (((((j i).natAbs - 1 : ℕ)) : ℝ) + 1) * z i) := fun i => by
    have h1 : ((((j i).natAbs - 1 : ℕ)) : ℝ) + 1 = ((j i).natAbs : ℝ) := by
      rw [Nat.cast_sub (hn i)]
      ring
    rw [h1]
    by_cases h : 0 ≤ j i
    · have hz : (j i : ℤ) = ((j i).natAbs : ℤ) := by omega
      have : (j i : ℝ) = ((j i).natAbs : ℝ) := by
        rw [← Int.cast_natCast]
        exact congrArg Int.cast hz
      rw [ite_eq_left h, this, one_mul]
    · have hz : (j i : ℤ) = -((j i).natAbs : ℤ) := by omega
      have : (j i : ℝ) = -((j i).natAbs : ℝ) := by
        rw [← Int.cast_natCast, ← Int.cast_neg]
        exact congrArg Int.cast hz
      rw [ite_eq_right h, this, neg_one_mul, ← Real.sin_neg]
      congr 1
      ring
  have hm : sineMode (fun i => (j i).natAbs - 1) z = Real.sqrt 2 ^ d *
      ∏ i, Real.sin (Real.pi * (((((j i).natAbs - 1 : ℕ)) : ℝ) + 1) * z i) := by
    unfold sineMode
    rw [Finset.prod_mul_distrib]
    simp
  unfold sineMonomial
  simp_rw [hs]
  rw [Finset.prod_mul_distrib, hm]
  have : Real.sqrt 2 ^ d ≠ 0 := pow_ne_zero _ (by positivity)
  field_simp

/-- The remainder of the sine series is orthogonal to every sine monomial. -/
theorem integral_sineRemainder_mul_sineMonomial (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) (j : Fin d → ℤ) :
    ∫ z in unitCube d, sineRemainder f z * sineMonomial j z = 0 := by
  by_cases h0 : ∃ i, j i = 0
  · obtain ⟨i, hi⟩ := h0
    have : ∀ z, sineMonomial j z = 0 := fun z =>
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simp [this]
  · push Not at h0
    obtain ⟨c, k, hck⟩ := exists_sineMonomial_eq_mul_sineMode j h0
    have : ∀ z, sineRemainder f z * sineMonomial j z =
        c * (sineRemainder f z * sineMode k z) := fun z => by
      rw [hck z]
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_sineRemainder_mul_sineMode hd f hf k, mul_zero]

/-- The remainder of the sine series is orthogonal to the span of the sine monomials. -/
theorem integral_sineRemainder_mul_of_mem_sineSpan (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) {g : Euc d → ℝ} (hg : g ∈ sineSpan d) :
    ∫ z in unitCube d, sineRemainder f z * g z = 0 := by
  have hu := continuous_sineRemainder hd f hf
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact integral_sineRemainder_mul_sineMonomial hd f hf j
  | zero => simp
  | add x y hx hy ihx ihy =>
    have : ∀ z, sineRemainder f z * (x + y) z =
        sineRemainder f z * x z + sineRemainder f z * y z := fun z => by
      simp only [Pi.add_apply]
      ring
    simp_rw [this]
    rw [integral_add (f := fun z => sineRemainder f z * x z) (g := fun z => sineRemainder f z * y z)
      (integrableOn_unitCube (hu.mul (continuous_of_mem_sineSpan hx)))
      (integrableOn_unitCube (hu.mul (continuous_of_mem_sineSpan hy))), ihx, ihy, add_zero]
  | smul a x hx ihx =>
    have : ∀ z, sineRemainder f z * (a • x) z = a * (sineRemainder f z * x z) := fun z => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [this]
    rw [integral_const_mul, ihx, mul_zero]

/-- The weighted integral of the square of the remainder is bounded by every `ε` times a fixed
constant. -/
theorem abs_integral_sq_mul_cubeWeight_le (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) {ε : ℝ} (hε : 0 < ε) :
    |∫ z in unitCube d, sineRemainder f z ^ 2 * cubeWeight z| ≤
      ε * ∫ z in unitCube d, |sineRemainder f z| * cubeWeight z := by
  have := isFiniteMeasure_restrict_unitCube (d := d)
  have hu := continuous_sineRemainder hd f hf
  have hw : Continuous (cubeWeight : Euc d → ℝ) := continuous_sineMonomial _
  obtain ⟨g, hg, hgu⟩ := exists_sineSpan_approx (sineRemainder f) hu hε
  have hgc := continuous_of_mem_sineSpan hg
  have hI : ∫ z in unitCube d, sineRemainder f z ^ 2 * cubeWeight z =
      ∫ z in unitCube d, sineRemainder f z * (cubeWeight z * sineRemainder f z - g z) := by
    have h1 : ∫ z in unitCube d, sineRemainder f z * (cubeWeight z * sineRemainder f z - g z) =
        (∫ z in unitCube d, sineRemainder f z ^ 2 * cubeWeight z) -
          ∫ z in unitCube d, sineRemainder f z * g z := by
      rw [← integral_sub (f := fun z => sineRemainder f z ^ 2 * cubeWeight z)
        (g := fun z => sineRemainder f z * g z) (integrableOn_unitCube ((hu.pow 2).mul hw))
        (integrableOn_unitCube (hu.mul hgc))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only
      ring
    rw [h1, integral_sineRemainder_mul_of_mem_sineSpan hd f hf hg, sub_zero]
  rw [hI, ← Real.norm_eq_abs, ← integral_const_mul]
  refine (norm_integral_le_of_norm_le
    (integrableOn_unitCube ((hu.abs.mul hw).const_mul ε)) ?_).trans_eq ?_
  · refine (ae_restrict_iff' measurableSet_unitCube).2 (Filter.Eventually.of_forall fun z hz => ?_)
    have h := hgu z (unitCube_subset_closedCube hz)
    rw [Real.norm_eq_abs, abs_mul]
    calc |sineRemainder f z| * |cubeWeight z * sineRemainder f z - g z|
        ≤ |sineRemainder f z| * (ε * cubeWeight z) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = ε * (|sineRemainder f z| * cubeWeight z) := by ring
  · rfl

/-- The remainder of the sine series of a test function vanishes on the open cube. -/
theorem sineRemainder_eq_zero (hd : 1 ≤ d) (f : Euc d → ℝ)
    (hf : Sobolev.IsTestFn (unitCube d) f) : ∀ z ∈ unitCube d, sineRemainder f z = 0 := by
  have hu := continuous_sineRemainder hd f hf
  have hw : Continuous (cubeWeight : Euc d → ℝ) := continuous_sineMonomial _
  set I : ℝ := ∫ z in unitCube d, sineRemainder f z ^ 2 * cubeWeight z with hI
  set M : ℝ := ∫ z in unitCube d, |sineRemainder f z| * cubeWeight z with hM
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_unitCube fun z hz =>
    mul_nonneg (sq_nonneg _) (cubeWeight_pos hz).le
  have hM0 : 0 ≤ M := setIntegral_nonneg measurableSet_unitCube fun z hz =>
    mul_nonneg (abs_nonneg _) (cubeWeight_pos hz).le
  have hI1 : I = 0 := by
    by_contra hne
    have hpos : 0 < I := lt_of_le_of_ne hI0 (Ne.symm hne)
    have h := abs_integral_sq_mul_cubeWeight_le hd f hf (ε := I / (M + 1)) (by positivity)
    rw [← hI, ← hM, abs_of_nonneg hI0, div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h
    nlinarith
  intro z hz
  have h2 := eq_zero_of_integral_eq_zero (h := fun z => sineRemainder f z ^ 2 * cubeWeight z)
    ((hu.pow 2).mul hw) (fun z hz => mul_nonneg (sq_nonneg _) (cubeWeight_pos hz).le) hI1 z hz
  have hwz := cubeWeight_pos hz
  have : sineRemainder f z ^ 2 = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h hwz.ne'
  exact pow_eq_zero_iff two_ne_zero |>.1 this

/-- The sine series of a test function converges to it at every point of the open cube. -/
theorem sineSum_eq (hd : 1 ≤ d) (f : Euc d → ℝ) (hf : Sobolev.IsTestFn (unitCube d) f)
    (z : Euc d) (hz : z ∈ unitCube d) : sineSum f z = f z := by
  have := sineRemainder_eq_zero hd f hf z hz
  unfold sineRemainder at this
  linarith

/-- **The sine series of a test function converges to it**: for `f ∈ C_c^∞((0,1)^d)` and `z` in
the open cube,
`Σ_k ⟨f, φ_k⟩ φ_k(z) = f(z)`, the series being absolutely summable. Route: the odd `2`-periodic
extension of `f` in each coordinate is smooth on the torus `(ℝ/2ℤ)^d`; its Fourier coefficients
are `(i/2)^d`-multiples of the sine coefficients (odd symmetry), they are summable by
`exists_abs_sineCoeff_le`, so the Fourier series converges to the extension pointwise
(`hasSum_mFourier_series_apply_of_summable`, after rescaling the torus to `UnitAddTorus d`), and
pairing the modes `±(k+1)` turns the exponentials into the sine modes. -/
theorem hasSum_sineSeries (hd : 1 ≤ d) (f : Euc d → ℝ) (hf : Sobolev.IsTestFn (unitCube d) f)
    (z : Euc d) (hz : z ∈ unitCube d) :
    HasSum (fun k : Fin d → ℕ => sineCoeff f k * sineMode k z) (f z) := by
  have h := (summable_sineCoeff_mul_sineMode hd f hf z).hasSum
  have h1 : ∑' k : Fin d → ℕ, sineCoeff f k * sineMode k z = f z := sineSum_eq hd f hf z hz
  rwa [h1] at h

end LatticeProb.Analysis.Schauder

end
