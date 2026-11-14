import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2

/-!
# Whitening of the correlated Brownian pair at a deterministic time

Let `μ` be the law of the two-sided correlated Brownian pair `(L, R)` of the mating-of-trees
encoding (`IsCorrelatedBM2 γ μ`, paths in `Path2 = C(ℝ, ℝ × ℝ)`): `Var L_t = Var R_t = |t|` and
`Cov(L_t, R_t) = ρ |t|` with `ρ = lrCov γ 0 1 = -cos(πγ²/4)`. Put `U = L + R` and `V = L - R`.
Since `Var L = Var R`, the coordinates `U` and `V` are uncorrelated, with variances `2(1 + ρ)|t|`
and `2(1 - ρ)|t|`. For `γ ∈ (0, 2)` we have `πγ²/4 ∈ (0, π)`, so `ρ ∈ (-1, 1)` and both variances
are nondegenerate.

The whitening at time `q` recentres `U` and `V` at `q` and normalises them,
`whitenAt γ q ω u = ((U (q + u) - U q) / √(2(1 + ρ)), (V (q + u) - V q) / √(2(1 - ρ)))`.
Its image law is the law of a pair of independent two-sided standard Brownian motions, which is the
correlated pair with `γ = √2` (`lrCov √2 0 1 = -cos(π/2) = 0`).

## Main statements

* `LatticeProb.CorrelatedBM.whitenAt`, `LatticeProb.CorrelatedBM.continuous_whitenAt`.
* `LatticeProb.CorrelatedBM.lrCoord_zero_whitenAt`, `LatticeProb.CorrelatedBM.lrCoord_one_whitenAt`:
  the two coordinates of the whitened path.
* `LatticeProb.CorrelatedBM.isCorrelatedBM2_map_whitenAt`: for `γ ∈ (0, 2)`,
  `IsCorrelatedBM2 γ μ → IsCorrelatedBM2 (√2) (μ.map (whitenAt γ q))`.

Each coordinate of the image process is a linear combination of four coordinates of the original
Gaussian process, so the image is a centred Gaussian process. Its covariance follows from
`twoSidedMin x y = (|x| + |y| - |x - y|) / 2` and the shift identity
`twoSidedMin (q + u) (q + v) - twoSidedMin (q + u) q - twoSidedMin q (q + v) + twoSidedMin q q =
twoSidedMin u v`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- **Whitening of the correlated Brownian pair at time `q`.** With `U = L + R`, `V = L - R` and
`ρ = lrCov γ 0 1`, the path `u ↦ ((U (q + u) - U q) / √(2(1 + ρ)), (V (q + u) - V q) / √(2(1 - ρ)))`.
-/
def whitenAt (γ q : ℝ) : Path2 → Path2 := fun ω =>
  ⟨fun u =>
    (((ω (q + u)).1 + (ω (q + u)).2 - ((ω q).1 + (ω q).2)) / Real.sqrt (2 * (1 + lrCov γ 0 1)),
      ((ω (q + u)).1 - (ω (q + u)).2 - ((ω q).1 - (ω q).2)) / Real.sqrt (2 * (1 - lrCov γ 0 1))),
    by fun_prop⟩

/-- The whitening is continuous for the compact-open topology on `Path2`. -/
theorem continuous_whitenAt (γ q : ℝ) : Continuous (whitenAt γ q) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  show Continuous fun p : Path2 × ℝ =>
    ((((p.1 (q + p.2)).1 + (p.1 (q + p.2)).2 - ((p.1 q).1 + (p.1 q).2)) /
        Real.sqrt (2 * (1 + lrCov γ 0 1)),
      ((p.1 (q + p.2)).1 - (p.1 (q + p.2)).2 - ((p.1 q).1 - (p.1 q).2)) /
        Real.sqrt (2 * (1 - lrCov γ 0 1))) : ℝ × ℝ)
  fun_prop

/-- The first coordinate of the whitened path is the normalised sum coordinate `U = L + R`,
recentred at time `q`. -/
@[simp] theorem lrCoord_zero_whitenAt (γ q u : ℝ) (ω : Path2) :
    lrCoord 0 u (whitenAt γ q ω) =
      (lrCoord 0 (q + u) ω + lrCoord 1 (q + u) ω - (lrCoord 0 q ω + lrCoord 1 q ω)) /
        Real.sqrt (2 * (1 + lrCov γ 0 1)) :=
  rfl

/-- The second coordinate of the whitened path is the normalised difference coordinate
`V = L - R`, recentred at time `q`. -/
@[simp] theorem lrCoord_one_whitenAt (γ q u : ℝ) (ω : Path2) :
    lrCoord 1 u (whitenAt γ q ω) =
      (lrCoord 0 (q + u) ω - lrCoord 1 (q + u) ω - (lrCoord 0 q ω - lrCoord 1 q ω)) /
        Real.sqrt (2 * (1 - lrCov γ 0 1)) :=
  rfl

/-- The two-sided Brownian covariance kernel in terms of absolute values. -/
private lemma twoSidedMin_eq_abs' (x y : ℝ) : twoSidedMin x y = (|x| + |y| - |x - y|) / 2 := by
  unfold twoSidedMin
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [max_eq_left hx, max_eq_left hy, max_eq_right (neg_nonpos.2 hx),
      max_eq_right (neg_nonpos.2 hy), min_self, add_zero, abs_of_nonneg hx, abs_of_nonneg hy]
    rcases le_total x y with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]
      ring
  · rw [max_eq_left hx, max_eq_right hy, max_eq_right (neg_nonpos.2 hx),
      max_eq_left (neg_nonneg.2 hy), min_eq_right hx, min_eq_left (neg_nonneg.2 hy),
      abs_of_nonneg hx, abs_of_nonpos hy, abs_of_nonneg (by linarith : 0 ≤ x - y)]
    ring
  · rw [max_eq_right hx, max_eq_left hy, max_eq_left (neg_nonneg.2 hx),
      max_eq_right (neg_nonpos.2 hy), min_eq_left hy, min_eq_right (neg_nonneg.2 hx),
      abs_of_nonpos hx, abs_of_nonneg hy, abs_of_nonpos (by linarith : x - y ≤ 0)]
    ring
  · rw [max_eq_right hx, max_eq_right hy, max_eq_left (neg_nonneg.2 hx),
      max_eq_left (neg_nonneg.2 hy), min_self, zero_add, abs_of_nonpos hx, abs_of_nonpos hy]
    rcases le_total x y with h | h
    · rw [min_eq_right (neg_le_neg h), abs_of_nonpos (sub_nonpos.2 h)]
      ring
    · rw [min_eq_left (neg_le_neg h), abs_of_nonneg (sub_nonneg.2 h)]
      ring

/-- The covariance kernel of the increments after time `q` is the kernel itself. -/
private lemma twoSidedMin_shift (q u v : ℝ) :
    twoSidedMin (q + u) (q + v) - twoSidedMin (q + u) q - twoSidedMin q (q + v) +
      twoSidedMin q q = twoSidedMin u v := by
  simp only [twoSidedMin_eq_abs']
  rw [show q + u - (q + v) = u - v by ring, show q + u - q = u by ring,
    show q - (q + v) = -v by ring, sub_self, abs_zero, abs_neg]
  ring

/-- A process each of whose coordinates lies in the linear span of the coordinates of a real
Gaussian process is a Gaussian process. -/
private lemma isGaussianProcess_of_mem_span' {Ω T S : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : T → Ω → ℝ} (hX : IsGaussianProcess X P) {Y : S → Ω → ℝ}
    (h : ∀ s, Y s ∈ Submodule.span ℝ (Set.range X)) : IsGaussianProcess Y P := by
  refine hX.of_isGaussianProcess fun s => ?_
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (h s)
  refine ⟨c.support,
    ∑ i : c.support, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : c.support => ℝ) i,
    fun ω => ?_⟩
  rw [← hc]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FunLike.coe_sum,
    FunLike.coe_smul, ContinuousLinearMap.proj_apply, Finset.restrict]
  exact (Finset.sum_coe_sort c.support (fun i => c i * X i ω)).symm

/-- Centred finite combinations: the covariance of `c (X + s Y)` and `c' (X' + s' Y')`. -/
private lemma covariance_comb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y X' Y' : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX' : MemLp X' 2 P) (hY' : MemLp Y' 2 P) (c s c' s' : ℝ) :
    cov[fun ω => c * (X ω + s * Y ω), fun ω => c' * (X' ω + s' * Y' ω); P] =
      c * c' * (cov[X, X'; P] + s' * cov[X, Y'; P] + s * cov[Y, X'; P] +
        s * s' * cov[Y, Y'; P]) := by
  have h1 : (fun ω => X ω + s * Y ω) = X + fun ω => s * Y ω := rfl
  have h2 : (fun ω => X' ω + s' * Y' ω) = X' + fun ω => s' * Y' ω := rfl
  rw [covariance_const_mul_left, covariance_const_mul_right, h1, h2,
    covariance_add_left hX (hY.const_mul s) (hX'.add (hY'.const_mul s')),
    covariance_add_right hX hX' (hY'.const_mul s'),
    covariance_add_right (hY.const_mul s) hX' (hY'.const_mul s')]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

private lemma measurable_lrCoord' (i : Fin 2) (t : ℝ) :
    Measurable (fun ω : Path2 => lrCoord i t ω) := by
  unfold lrCoord
  split_ifs
  · exact measurable_fst.comp (ContinuousMap.measurable_eval t)
  · exact measurable_snd.comp (ContinuousMap.measurable_eval t)

/-- The increment `X (q + u) - X q` of the coordinate `i` after time `q`. -/
private def coordIncrement (i : Fin 2) (q u : ℝ) (ω : Path2) : ℝ :=
  lrCoord i (q + u) ω - lrCoord i q ω

/-- The normalising factors of the whitening. -/
private def whitenScale (γ : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then (Real.sqrt (2 * (1 + lrCov γ 0 1)))⁻¹ else (Real.sqrt (2 * (1 - lrCov γ 0 1)))⁻¹

/-- The sign of `R` in the sum (`i = 0`) and difference (`i = 1`) coordinates. -/
private def whitenSign (i : Fin 2) : ℝ := if i = 0 then 1 else -1

private lemma lrCoord_whitenAt_eq (γ q u : ℝ) (ω : Path2) (i : Fin 2) :
    lrCoord i u (whitenAt γ q ω) =
      whitenScale γ i * (coordIncrement 0 q u ω + whitenSign i * coordIncrement 1 q u ω) := by
  revert i
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · show _ = (Real.sqrt (2 * (1 + lrCov γ 0 1)))⁻¹ *
      (coordIncrement 0 q u ω + 1 * coordIncrement 1 q u ω)
    rw [lrCoord_zero_whitenAt]
    simp only [coordIncrement]
    ring
  · show _ = (Real.sqrt (2 * (1 - lrCov γ 0 1)))⁻¹ *
      (coordIncrement 0 q u ω + -1 * coordIncrement 1 q u ω)
    rw [lrCoord_one_whitenAt]
    simp only [coordIncrement]
    ring

/-- **Whitening a correlated Brownian pair gives two independent Brownian motions.** For
`γ ∈ (0, 2)` and a deterministic time `q`, the image of the law of the correlated pair under the
whitening at `q` is the correlated Brownian law with `γ = √2`, whose coordinates are uncorrelated
(`lrCov √2 0 1 = 0`). -/
theorem isCorrelatedBM2_map_whitenAt {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (q : ℝ)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    IsCorrelatedBM2 (Real.sqrt 2) (μ.map (whitenAt γ q)) := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hΦ : Measurable (whitenAt γ q) := (continuous_whitenAt γ q).measurable
  have hm : ∀ i t, Measurable (fun ω : Path2 => lrCoord i t ω) := measurable_lrCoord'
  have hL2 : ∀ i t, MemLp (lrCoord i t) 2 μ := fun i t =>
    (hμ.isGaussianProcess.hasGaussianLaw_eval (i, t)).memLp_two
  have hI2 : ∀ i u, MemLp (coordIncrement i q u) 2 μ := fun i u => (hL2 i (q + u)).sub (hL2 i q)
  -- the correlation `ρ = -cos(πγ²/4)` lies in `(-1, 1)`
  have hθ0 : 0 < Real.pi * γ ^ 2 / 4 := by
    have := mul_pos Real.pi_pos (pow_pos hγ0 2)
    linarith
  have hθπ : Real.pi * γ ^ 2 / 4 < Real.pi := by
    have hγ4 : γ ^ 2 < 4 := by nlinarith [mul_pos hγ0 (sub_pos.2 hγ2)]
    nlinarith [mul_pos Real.pi_pos (sub_pos.2 hγ4)]
  have hcos1 : Real.cos (Real.pi * γ ^ 2 / 4) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
    rwa [Real.cos_zero] at h
  have hcosm1 : -1 < Real.cos (Real.pi * γ ^ 2 / 4) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
    rwa [Real.cos_pi] at h
  have hρ : lrCov γ 0 1 = -Real.cos (Real.pi * γ ^ 2 / 4) := rfl
  have hx₀ : 0 < 2 * (1 + lrCov γ 0 1) := by rw [hρ]; linarith
  have hx₁ : 0 < 2 * (1 - lrCov γ 0 1) := by rw [hρ]; linarith
  have hkey : ∀ x : ℝ, 0 < x → (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ * x = 1 := fun x hx => by
    rw [← mul_inv, Real.mul_self_sqrt hx.le, inv_mul_cancel₀ hx.ne']
  have hcos : Real.cos (Real.pi * Real.sqrt 2 ^ 2 / 4) = 0 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), show Real.pi * 2 / 4 = Real.pi / 2 by ring,
      Real.cos_pi_div_two]
  have h00 : lrCov γ 0 0 = 1 := rfl
  have h11 : lrCov γ 1 1 = 1 := rfl
  have h10 : lrCov γ 1 0 = lrCov γ 0 1 := rfl
  have hscalar : ∀ i j : Fin 2, whitenScale γ i * whitenScale γ j *
      (1 + whitenSign j * lrCov γ 0 1 + whitenSign i * lrCov γ 0 1 + whitenSign i * whitenSign j) =
      lrCov (Real.sqrt 2) i j := by
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · show (Real.sqrt (2 * (1 + lrCov γ 0 1)))⁻¹ * (Real.sqrt (2 * (1 + lrCov γ 0 1)))⁻¹ *
          (1 + 1 * lrCov γ 0 1 + 1 * lrCov γ 0 1 + 1 * 1) = 1
      linear_combination hkey _ hx₀
    · show (Real.sqrt (2 * (1 + lrCov γ 0 1)))⁻¹ * (Real.sqrt (2 * (1 - lrCov γ 0 1)))⁻¹ *
          (1 + -1 * lrCov γ 0 1 + 1 * lrCov γ 0 1 + 1 * -1) =
          -Real.cos (Real.pi * Real.sqrt 2 ^ 2 / 4)
      rw [hcos]
      ring
    · show (Real.sqrt (2 * (1 - lrCov γ 0 1)))⁻¹ * (Real.sqrt (2 * (1 + lrCov γ 0 1)))⁻¹ *
          (1 + 1 * lrCov γ 0 1 + -1 * lrCov γ 0 1 + -1 * 1) =
          -Real.cos (Real.pi * Real.sqrt 2 ^ 2 / 4)
      rw [hcos]
      ring
    · show (Real.sqrt (2 * (1 - lrCov γ 0 1)))⁻¹ * (Real.sqrt (2 * (1 - lrCov γ 0 1)))⁻¹ *
          (1 + -1 * lrCov γ 0 1 + -1 * lrCov γ 0 1 + -1 * -1) = 1
      linear_combination hkey _ hx₁
  -- moments of the increments
  have hIint : ∀ i u, ∫ ω, coordIncrement i q u ω ∂μ = 0 := by
    intro i u
    simp only [coordIncrement]
    rw [integral_sub ((hL2 i _).integrable (by norm_num)) ((hL2 i q).integrable (by norm_num)),
      hμ.integral_eq_zero, hμ.integral_eq_zero, sub_self]
  have hcovI : ∀ i j u v, cov[coordIncrement i q u, coordIncrement j q v; μ] =
      lrCov γ i j * twoSidedMin u v := by
    intro i j u v
    show cov[fun ω => lrCoord i (q + u) ω - lrCoord i q ω,
      fun ω => lrCoord j (q + v) ω - lrCoord j q ω; μ] = _
    rw [covariance_fun_sub_fun_sub (hL2 i _) (hL2 i q) (hL2 j _) (hL2 j q),
      hμ.covariance_eq i j (q + u) (q + v), hμ.covariance_eq i j (q + u) q,
      hμ.covariance_eq i j q (q + v), hμ.covariance_eq i j q q, ← twoSidedMin_shift q u v]
    ring
  -- the whitened process is a Gaussian process under `μ`
  have hfun : ∀ p : Fin 2 × ℝ, (fun ω => lrCoord p.1 p.2 (whitenAt γ q ω)) =
      whitenScale γ p.1 • (coordIncrement 0 q p.2 + whitenSign p.1 • coordIncrement 1 q p.2) := by
    intro p
    funext ω
    simp only [lrCoord_whitenAt_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have hX : ∀ i t, lrCoord i t ∈
      Submodule.span ℝ (Set.range fun p : Fin 2 × ℝ => lrCoord p.1 p.2) :=
    fun i t => Submodule.subset_span (Set.mem_range_self (i, t))
  have hI : ∀ i u, coordIncrement i q u ∈
      Submodule.span ℝ (Set.range fun p : Fin 2 × ℝ => lrCoord p.1 p.2) := by
    intro i u
    have h := sub_mem (hX i (q + u)) (hX i q)
    exact h
  have hmem : ∀ p : Fin 2 × ℝ, (fun ω => lrCoord p.1 p.2 (whitenAt γ q ω)) ∈
      Submodule.span ℝ (Set.range fun p : Fin 2 × ℝ => lrCoord p.1 p.2) := by
    intro p
    rw [hfun p]
    exact SMulMemClass.smul_mem _ (add_mem (hI 0 p.2) (SMulMemClass.smul_mem _ (hI 1 p.2)))
  have hG : IsGaussianProcess
      (fun (p : Fin 2 × ℝ) (ω : Path2) => lrCoord p.1 p.2 (whitenAt γ q ω)) μ :=
    isGaussianProcess_of_mem_span' hμ.isGaussianProcess hmem
  have hgm : ∀ I : Finset (Fin 2 × ℝ),
      Measurable fun ω : Path2 => I.restrict (fun p : Fin 2 × ℝ => lrCoord p.1 p.2 ω) :=
    fun I => measurable_pi_iff.2 fun j => hm j.1.1 j.1.2
  refine
    { isProbabilityMeasure := (Measure.isProbabilityMeasure_map_iff hΦ.aemeasurable).2 ‹_›
      isGaussianProcess := ⟨fun I => ⟨(hgm I).aemeasurable, ?_⟩⟩
      integral_eq_zero := fun i t => ?_
      covariance_eq := fun i j s t => ?_ }
  · rw [Measure.map_map (hgm I) hΦ]
    exact (hG.hasGaussianLaw I).isGaussian_map
  · rw [integral_map hΦ.aemeasurable (hm i t).aestronglyMeasurable]
    simp only [lrCoord_whitenAt_eq]
    rw [integral_const_mul, integral_add ((hI2 0 t).integrable (by norm_num))
      (((hI2 1 t).integrable (by norm_num)).const_mul _), integral_const_mul, hIint, hIint]
    ring
  · rw [covariance_map_fun (hm i s).aestronglyMeasurable (hm j t).aestronglyMeasurable
      hΦ.aemeasurable]
    simp only [lrCoord_whitenAt_eq]
    rw [covariance_comb (hI2 0 s) (hI2 1 s) (hI2 0 t) (hI2 1 t)]
    simp only [hcovI]
    rw [h00, h11, h10, ← hscalar i j]
    ring

end LatticeProb.CorrelatedBM
