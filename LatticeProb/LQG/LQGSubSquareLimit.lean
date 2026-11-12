import Mathlib
import LatticeProb.Analysis.RiemannSquare
import LatticeProb.LQG.LQGSubSquareGaussian

/-!
# Riemann sums of the approximate Liouville density on two sub-squares

The grid `Fin 2 × Fin N × Fin N` of the two sub-squares `z_s + 2^{-k} [-1/8, 1/8]²` of the square
`[-1/8, 1/8]²`, with the points `2^{-k} pt_{ab} + z_s`, `pt_{ab} = (-1/8 + a/(4N)) + i (-1/8 + b/(4N))`,
carries the Riemann sums of the density `ε^{γ²/2} e^{γ h_ε(x)}` of the approximate Liouville measure.
For a function `h ε` continuous in the space variable these sums converge, as `N → ∞`, to the mass of
the sub-squares, and the weighted sums of the comparison vector converge to the products of the
lognormal weight and the mass of the unit square against an independent copy of the field.

* `tendsto_gridSum_lqgApprox`: the Riemann sums over `[-1/8, 1/8]²` of `δ^{γ²/2} e^{γ h_δ}`.
* `tendsto_gridSum_subSquareMass`: the sums over the two sub-squares converge to the masses of the
  sub-squares for the approximation at the scale `2^{-(k+m)}`.
* `tendsto_gridSum_subSquareComparison`: the corresponding limit for the comparison vector.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter Topology

namespace LatticeProb.LQG

open LatticeProb LQGDyadicScaling

/-- The grid point `(-1/8 + a/(4N)) + i (-1/8 + b/(4N))` of the square `[-1/8, 1/8]²`. -/
def sqGridPt (N a b : ℕ) : ℂ :=
  ⟨2 * (1 / 8 : ℝ) * ((a : ℝ) / N) + -(1 / 8 : ℝ), 2 * (1 / 8 : ℝ) * ((b : ℝ) / N) + -(1 / 8 : ℝ)⟩

theorem sqGridPt_mem_lqgSquare {N a b : ℕ} (ha : a < N) (hb : b < N) :
    sqGridPt N a b ∈ lqgSquare := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le a) ha)
  have h1 : (a : ℝ) / N ≤ 1 := (div_le_one hN).2 (by exact_mod_cast ha.le)
  have h2 : (b : ℝ) / N ≤ 1 := (div_le_one hN).2 (by exact_mod_cast hb.le)
  have h3 : 0 ≤ (a : ℝ) / N := by positivity
  have h4 : 0 ≤ (b : ℝ) / N := by positivity
  refine ⟨?_, ?_⟩ <;> simp only [sqGridPt, abs_le] <;> constructor <;> linarith

/-- **Riemann sums of the approximate density over the unit square.** If `z ↦ h δ z` is continuous
then the grid averages of `δ^{γ²/2} e^{γ h_δ}` over `[-1/8, 1/8]²` converge to the mass of the
square for `lqgApprox γ h δ`. -/
theorem tendsto_gridSum_lqgApprox (γ : ℝ) {δ : ℝ} (hδ : 0 < δ) (h : ℝ → ℂ → ℝ)
    (hc : Continuous (h δ)) :
    Tendsto (fun N : ℕ => ((2 * (1 / 8 : ℝ)) ^ 2 / (N : ℝ) ^ 2) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          δ ^ (γ ^ 2 / 2) * Real.exp (γ * h δ (sqGridPt N a b))) atTop
      (𝓝 (lqgApprox γ h δ lqgSquare).toReal) := by
  have hf : Continuous fun w : ℂ => δ ^ (γ ^ 2 / 2) * Real.exp (γ * h δ w) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))
  have hT : IsCompact lqgSquare := by
    have hcl : IsClosed lqgSquare := by
      have hre : Continuous fun w : ℂ => |w.re| := Complex.continuous_re.abs
      have him : Continuous fun w : ℂ => |w.im| := Complex.continuous_im.abs
      exact (isClosed_le hre continuous_const).inter (isClosed_le him continuous_const)
    exact (isCompact_closedBall (0 : ℂ) (1 / 4)).of_isClosed_subset hcl lqgSquare_subset_closedBall
  have hint : IntegrableOn (fun w : ℂ => δ ^ (γ ^ 2 / 2) * Real.exp (γ * h δ w)) lqgSquare :=
    hf.continuousOn.integrableOn_compact hT
  have hnn : ∀ w : ℂ, 0 ≤ δ ^ (γ ^ 2 / 2) * Real.exp (γ * h δ w) := fun w =>
    mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.exp_pos _).le
  have hval : (lqgApprox γ h δ lqgSquare).toReal =
      ∫ w in lqgSquare, δ ^ (γ ^ 2 / 2) * Real.exp (γ * h δ w) := by
    unfold lqgApprox
    rw [withDensity_apply _ measurableSet_lqgSquare,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_lqgSquare fun w _ => hnn w)]
  rw [hval]
  have key := tendsto_gridSum_centredSquare (c := 1 / 8) (by norm_num) hf
  simpa only [sqGridPt, lqgSquare] using key

/-- Sums over the grid `Fin 2 × Fin N × Fin N` as iterated sums over `range N`. -/
theorem sum_gridIdx (N : ℕ) (F : Fin 2 → ℕ → ℕ → ℝ) :
    ∑ i : Fin 2 × Fin N × Fin N, F i.1 i.2.1 i.2.2 =
      ∑ s : Fin 2, ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, F s a b := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type]
  calc ∑ a : Fin N, ∑ b : Fin N, F s a b
      = ∑ a : Fin N, ∑ b ∈ Finset.range N, F s a b :=
        Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun b => F s a b) N
    _ = _ := Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range N, F s a b) N

/-- `exp(γ x - γ² (-log ε) / 2) = ε^{γ²/2} e^{γ x}`. -/
theorem exp_sub_variance_div_two {ε : ℝ} (hε : 0 < ε) (γ x : ℝ) :
    Real.exp (γ * x - γ ^ 2 * (-Real.log ε) / 2) = ε ^ (γ ^ 2 / 2) * Real.exp (γ * x) := by
  rw [Real.rpow_def_of_pos hε, ← Real.exp_add]
  congr 1
  ring

/-- The scaling identity for the masses of the sub-squares. -/
theorem dyadicFactor_mul_lqgApprox_recentred {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℂ → ℝ) (k m : ℕ)
    (s : Fin 2) :
    dyadicFactor γ k (h (dyadicScale k) (lqgSquareCentre s)) *
        lqgApprox γ (fun t w => h (dyadicScale k * t) ((dyadicScale k : ℂ) * w + lqgSquareCentre s) -
          h (dyadicScale k) (lqgSquareCentre s)) (dyadicScale m) lqgSquare =
      lqgApprox γ h (dyadicScale (k + m)) (lqgSubSquare k s) := by
  have e : lqgApprox γ (fun t w => h (dyadicScale k * t) ((dyadicScale k : ℂ) * w + lqgSquareCentre s) -
      h (dyadicScale k) (lqgSquareCentre s)) (dyadicScale m) lqgSquare =
      lqgApproxMass γ (fun t w => h (dyadicScale k * t) ((dyadicScale k : ℂ) * w + lqgSquareCentre s) -
        h (dyadicScale k) (lqgSquareCentre s)) (lqgSquare.indicator 1) m := by
    unfold lqgApproxMass
    rw [lintegral_indicator_one measurableSet_lqgSquare]
  rw [e, ← lqgApproxMass_indicator_preimage_dyadic hγ h k m (lqgSquareCentre s)
    measurableSet_lqgSquare]
  unfold lqgApproxMass
  exact lintegral_indicator_one (measurableSet_lqgSubSquare k s)

/-- **Limit of the grid sums of the field vector.** For `h` with `z ↦ h (R δ) z` continuous, the sums
`∑_i p_N e^{γ h_{Rδ}(R pt_i + z_{s_i}) - Var/2}`, `p_N = R² (1/4)²/N²`, over the grid of the two
sub-squares converge to the masses of the sub-squares for the approximation at scale `2^{-(k+m)}`. -/
theorem tendsto_gridSum_subSquareMass {γ : ℝ} (hγ : γ ≠ 0) {k : ℕ} (m : ℕ) (h : ℝ → ℂ → ℝ)
    (hc : Continuous (h (dyadicScale k * dyadicScale m))) :
    Tendsto (fun N : ℕ => ∑ i : Fin 2 × Fin (N + 1) × Fin (N + 1),
        dyadicScale k ^ 2 * ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2) *
          Real.exp (γ * h (dyadicScale k * dyadicScale m) ((dyadicScale k : ℂ) *
            sqGridPt (N + 1) i.2.1 i.2.2 + lqgSquareCentre i.1) -
              γ ^ 2 * (-Real.log (dyadicScale k * dyadicScale m)) / 2)) atTop
      (𝓝 (∑ s : Fin 2, (lqgApprox γ h (dyadicScale (k + m)) (lqgSubSquare k s)).toReal)) := by
  have hR := dyadicScale_pos' k
  have hδ := dyadicScale_pos' m
  have hε : 0 < dyadicScale k * dyadicScale m := mul_pos hR hδ
  simp_rw [exp_sub_variance_div_two hε]
  rw [show (fun N : ℕ => ∑ i : Fin 2 × Fin (N + 1) × Fin (N + 1),
      dyadicScale k ^ 2 * ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2) *
        ((dyadicScale k * dyadicScale m) ^ (γ ^ 2 / 2) * Real.exp (γ * h (dyadicScale k * dyadicScale m)
          ((dyadicScale k : ℂ) * sqGridPt (N + 1) i.2.1 i.2.2 + lqgSquareCentre i.1)))) =
      fun N : ℕ => ∑ s : Fin 2, ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
        dyadicScale k ^ 2 * ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2) *
        ((dyadicScale k * dyadicScale m) ^ (γ ^ 2 / 2) * Real.exp (γ * h (dyadicScale k * dyadicScale m)
          ((dyadicScale k : ℂ) * sqGridPt (N + 1) a b + lqgSquareCentre s))) from
    funext fun N => sum_gridIdx (N + 1) fun s a b => dyadicScale k ^ 2 *
      ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2) *
        ((dyadicScale k * dyadicScale m) ^ (γ ^ 2 / 2) * Real.exp (γ * h (dyadicScale k * dyadicScale m)
          ((dyadicScale k : ℂ) * sqGridPt (N + 1) a b + lqgSquareCentre s)))]
  refine tendsto_finsetSum _ fun s _ => ?_
  have hc' : Continuous ((fun t w => h (dyadicScale k * t) ((dyadicScale k : ℂ) * w +
      lqgSquareCentre s) - h (dyadicScale k) (lqgSquareCentre s)) (dyadicScale m)) := by
    have : Continuous fun w : ℂ => (dyadicScale k : ℂ) * w + lqgSquareCentre s := by fun_prop
    exact (hc.comp this).sub continuous_const
  have key := ((tendsto_gridSum_lqgApprox γ hδ (fun t w => h (dyadicScale k * t)
    ((dyadicScale k : ℂ) * w + lqgSquareCentre s) - h (dyadicScale k) (lqgSquareCentre s)) hc').comp (tendsto_add_atTop_nat 1)).const_mul
    (dyadicFactor γ k (h (dyadicScale k) (lqgSquareCentre s))).toReal
  rw [← ENNReal.toReal_mul, dyadicFactor_mul_lqgApprox_recentred hγ h k m s] at key
  refine key.congr fun N => ?_
  simp only [Function.comp_apply, dyadicFactor, Finset.mul_sum]
  rw [ENNReal.toReal_ofReal (by positivity)]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rpow_two_add_half_sq hR γ, Real.mul_rpow hR.le hδ.le, mul_sub, Real.exp_sub]
  field_simp

/-- `exp(γ (G + H + g) - γ² (1 - log R - log δ) / 2)` as a lognormal weight times a field density. -/
theorem exp_comparison_eq {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (γ G H g : ℝ) :
    Real.exp (γ * (G + H + g) - γ ^ 2 * (1 - Real.log R - Real.log δ) / 2) =
      Real.exp (γ * g - γ ^ 2 / 2) * Real.exp (γ * G) *
        (R ^ (γ ^ 2 / 2) * (δ ^ (γ ^ 2 / 2) * Real.exp (γ * H))) := by
  rw [Real.rpow_def_of_pos hR, Real.rpow_def_of_pos hδ]
  simp only [← Real.exp_add]
  congr 1
  ring

/-- **Limit of the grid sums of the comparison vector.** With the lognormal weight
`W_s = e^{γ g - γ²/2} R^{2+γ²/2} e^{γ G_s}` the sums converge to `∑_s W_s · μ'_s([-1/8,1/8]²)`,
where `μ'_s` is the approximate measure of the `s`-th copy at scale `δ`. -/
theorem tendsto_gridSum_subSquareComparison (γ : ℝ) (k m : ℕ) (G : Fin 2 → ℝ) (g : ℝ)
    (h : Fin 2 → ℝ → ℂ → ℝ) (hc : ∀ s, Continuous (h s (dyadicScale m))) :
    Tendsto (fun N : ℕ => ∑ i : Fin 2 × Fin (N + 1) × Fin (N + 1),
        dyadicScale k ^ 2 * ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2) *
          Real.exp (γ * (G i.1 + h i.1 (dyadicScale m) (sqGridPt (N + 1) i.2.1 i.2.2) + g) -
            γ ^ 2 * (1 - Real.log (dyadicScale k) - Real.log (dyadicScale m)) / 2)) atTop
      (𝓝 (∑ s : Fin 2, Real.exp (γ * g - γ ^ 2 / 2) * dyadicScale k ^ (2 + γ ^ 2 / 2) *
        Real.exp (γ * G s) * (lqgApprox γ (h s) (dyadicScale m) lqgSquare).toReal)) := by
  have hR := dyadicScale_pos' k
  have hδ := dyadicScale_pos' m
  rw [show (fun N : ℕ => ∑ i : Fin 2 × Fin (N + 1) × Fin (N + 1),
      dyadicScale k ^ 2 * ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2) *
          Real.exp (γ * (G i.1 + h i.1 (dyadicScale m) (sqGridPt (N + 1) i.2.1 i.2.2) + g) -
            γ ^ 2 * (1 - Real.log (dyadicScale k) - Real.log (dyadicScale m)) / 2)) =
      fun N : ℕ => ∑ s : Fin 2, ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
        dyadicScale k ^ 2 * ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2) *
          Real.exp (γ * (G s + h s (dyadicScale m) (sqGridPt (N + 1) a b) + g) -
            γ ^ 2 * (1 - Real.log (dyadicScale k) - Real.log (dyadicScale m)) / 2) from
    funext fun N => sum_gridIdx (N + 1) fun s a b => dyadicScale k ^ 2 *
      ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2) *
          Real.exp (γ * (G s + h s (dyadicScale m) (sqGridPt (N + 1) a b) + g) -
            γ ^ 2 * (1 - Real.log (dyadicScale k) - Real.log (dyadicScale m)) / 2)]
  refine tendsto_finsetSum _ fun s _ => ?_
  have key := ((tendsto_gridSum_lqgApprox γ hδ (h s) (hc s)).comp (tendsto_add_atTop_nat 1)).const_mul
    (Real.exp (γ * g - γ ^ 2 / 2) * dyadicScale k ^ (2 + γ ^ 2 / 2) * Real.exp (γ * G s))
  refine key.congr fun N => ?_
  simp only [Function.comp_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [exp_comparison_eq hR hδ, rpow_two_add_half_sq hR γ]
  ring

theorem lqgApproxMass_lqgSquare (γ : ℝ) (h : ℝ → ℂ → ℝ) (m : ℕ) :
    lqgApproxMass γ h (lqgSquare.indicator 1) m = lqgApprox γ h (dyadicScale m) lqgSquare := by
  unfold lqgApproxMass
  rw [lintegral_indicator_one measurableSet_lqgSquare]

end LatticeProb.LQG

namespace LatticeProb.Gauss

open LatticeProb LatticeProb.LQG LQGDyadicScaling

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Dominated convergence for the Laplace functionals `E[e^{-λ S_N}]` of nonnegative variables. -/
theorem tendsto_integral_exp_neg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {lam : ℝ} (hl : 0 ≤ lam) {S : ℕ → α → ℝ} {S' : α → ℝ}
    (hm : ∀ N, Measurable (S N)) (hnn : ∀ N a, 0 ≤ S N a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun N => S N a) atTop (𝓝 (S' a))) :
    Tendsto (fun N => ∫ a, Real.exp (-lam * S N a) ∂μ) atTop (𝓝 (∫ a, Real.exp (-lam * S' a) ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun N => (Real.measurable_exp.comp (measurable_const.mul (hm N))).aestronglyMeasurable)
    (integrable_const 1) (fun N => ae_of_all _ fun a => ?_) (hlim.mono fun a ha => ?_)
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by have := mul_nonneg hl (hnn N a); linarith)
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto _).comp ha

/-- Almost surely the circle averages at a fixed radius are continuous in the centre. -/
theorem IsWholePlaneGFF.ae_continuous_circle_fixed (hh : IsWholePlaneGFF P hC hcirc) {t : ℝ}
    (ht : 0 < t) : ∀ᵐ ω ∂P, Continuous (hcirc ω t) := by
  filter_upwards [hh.ae_continuousOn_circle] with ω hω
  exact hω.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨ht, mem_univ z⟩

/-- The lognormal weight `e^{γ g - γ²/2} R^{2+γ²/2} e^{γ h_R(z_s)}` of the `s`-th sub-square in the
comparison model `(Ω × ℝ) × Ω²`. -/
def subSquareWeight (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ) (x : (Ω × ℝ) × (Fin 2 → Ω))
    (s : Fin 2) : ℝ :=
  Real.exp (γ * x.1.2 - γ ^ 2 / 2) * dyadicScale k ^ (2 + γ ^ 2 / 2) *
    Real.exp (γ * hcirc x.1.1 (dyadicScale k) (lqgSquareCentre s))

theorem norm_sqGridPt_add_le {N a b : ℕ} (ha : a < N) (hb : b < N) {δ : ℝ} (hδ : δ ≤ 1 / 2) :
    ‖sqGridPt N a b‖ + δ ≤ 1 := by
  have := mem_closedBall_zero_iff.1 (lqgSquare_subset_closedBall (sqGridPt_mem_lqgSquare ha hb))
  linarith

/-- **Comparison of the Laplace functional of the sub-square masses with the lognormal model.** For a
whole-plane GFF, `k ≥ 4`, `m ≥ 1` and `λ ≥ 0`, the Laplace functional of the total mass of the two
sub-squares `z_s + 2^{-k} [-1/8, 1/8]²` for the approximation at scale `2^{-(k+m)}` is at most that of
`∑_s W_s Z̃_s`, where `W_s` is the lognormal weight `subSquareWeight` and `Z̃_s` the mass of
`[-1/8, 1/8]²` at scale `2^{-m}` for the `s`-th independent copy of the field. -/
theorem IsWholePlaneGFF.integral_exp_neg_subSquareMass_le (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : γ ≠ 0) {lam : ℝ} (hl : 0 ≤ lam) {k : ℕ} (hk : 4 ≤ k) {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, Real.exp (-lam * ∑ s : Fin 2,
        (lqgApprox γ (hcirc ω) (dyadicScale (k + m)) (lqgSubSquare k s)).toReal) ∂P ≤
      ∫ x, Real.exp (-lam * ∑ s : Fin 2, subSquareWeight γ hcirc k x s *
        (lqgApproxMass γ (hcirc (x.2 s)) (lqgSquare.indicator 1) m).toReal) ∂(subSquareMeasure P) := by
  have : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hR := dyadicScale_pos' k
  have hδ := dyadicScale_pos' m
  have hε : 0 < dyadicScale k * dyadicScale m := mul_pos hR hδ
  have hδ2 : dyadicScale m ≤ 1 / 2 := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [dyadicScale_succ_eq_half]
    have := dyadicScale_le_one' m'
    linarith
  have hz : ∀ s, ‖lqgSquareCentre s‖ + dyadicScale k ≤ 1 := fun s =>
    norm_lqgSquareCentre_add_dyadicScale_le_one hk s
  simp only [lqgApproxMass_lqgSquare]
  have hpt : ∀ (N : ℕ) (a b : Fin (N + 1)), ‖sqGridPt (N + 1) a b‖ + dyadicScale m ≤ 1 :=
    fun N a b => norm_sqGridPt_add_le a.2 b.2 hδ2
  have hvarX : ∀ (N : ℕ) (i : Fin 2 × Fin (N + 1) × Fin (N + 1)),
      Var[fun ω => subSquareField γ hcirc (dyadicScale k) (dyadicScale k * dyadicScale m)
        (fun i => i.1) (fun i => sqGridPt (N + 1) i.2.1 i.2.2) ω i; P] =
        γ ^ 2 * (-Real.log (dyadicScale k * dyadicScale m)) := fun N i =>
    hh.variance_subSquareField γ hε _ _ i (norm_rescaled_add_le hR (hz i.1) (hpt N i.2.1 i.2.2))
  have hvarY : ∀ (N : ℕ) (i : Fin 2 × Fin (N + 1) × Fin (N + 1)),
      Var[fun x => subSquareComparison γ hcirc (dyadicScale k) (dyadicScale m)
        (fun i => i.1) (fun i => sqGridPt (N + 1) i.2.1 i.2.2) x i; subSquareMeasure P] =
        γ ^ 2 * (1 - Real.log (dyadicScale k) - Real.log (dyadicScale m)) := fun N i =>
    hh.variance_subSquareComparison γ hR hδ _ _ i (hz i.1) (hpt N i.2.1 i.2.2)
  have hK : ∀ N : ℕ, ∫ ω, Real.exp (-lam * ∑ i : Fin 2 × Fin (N + 1) × Fin (N + 1),
        (dyadicScale k ^ 2 * ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2)) *
          Real.exp (subSquareField γ hcirc (dyadicScale k) (dyadicScale k * dyadicScale m)
            (fun i => i.1) (fun i => sqGridPt (N + 1) i.2.1 i.2.2) ω i -
              γ ^ 2 * (-Real.log (dyadicScale k * dyadicScale m)) / 2)) ∂P ≤
      ∫ x, Real.exp (-lam * ∑ i : Fin 2 × Fin (N + 1) × Fin (N + 1),
        (dyadicScale k ^ 2 * ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2)) *
          Real.exp (subSquareComparison γ hcirc (dyadicScale k) (dyadicScale m)
            (fun i => i.1) (fun i => sqGridPt (N + 1) i.2.1 i.2.2) x i -
              γ ^ 2 * (1 - Real.log (dyadicScale k) - Real.log (dyadicScale m)) / 2))
        ∂(subSquareMeasure P) := by
    intro N
    have := hh.integral_exp_neg_subSquareField_le γ hl hk hδ hδ2
      (fun i : Fin 2 × Fin (N + 1) × Fin (N + 1) => i.1)
      (fun i => sqGridPt (N + 1) i.2.1 i.2.2) (fun i => sqGridPt_mem_lqgSquare i.2.1.2 i.2.2.2)
      (p := fun _ => dyadicScale k ^ 2 * ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2))
      (fun _ => by positivity)
    simpa only [hvarX N, hvarY N] using this
  have hXm : ∀ (N : ℕ) (i : Fin 2 × Fin (N + 1) × Fin (N + 1)), Measurable fun ω =>
      subSquareField γ hcirc (dyadicScale k) (dyadicScale k * dyadicScale m)
        (fun i => i.1) (fun i => sqGridPt (N + 1) i.2.1 i.2.2) ω i := fun N i =>
    measurable_const.mul (hh.measurable_circle _ _ hε)
  have hYm : ∀ (N : ℕ) (i : Fin 2 × Fin (N + 1) × Fin (N + 1)), Measurable fun x =>
      subSquareComparison γ hcirc (dyadicScale k) (dyadicScale m)
        (fun i => i.1) (fun i => sqGridPt (N + 1) i.2.1 i.2.2) x i := fun N i =>
    ((((hh.measurable_circle _ _ hR).comp (measurable_fst.comp measurable_fst)).add
      ((hh.measurable_circle _ _ hδ).comp ((measurable_pi_apply i.1).comp measurable_snd))).add
      (measurable_snd.comp measurable_fst)).const_mul γ
  have hX := tendsto_integral_exp_neg (μ := P) hl
    (S := fun (N : ℕ) ω => ∑ i : Fin 2 × Fin (N + 1) × Fin (N + 1),
        (dyadicScale k ^ 2 * ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2)) *
          Real.exp (subSquareField γ hcirc (dyadicScale k) (dyadicScale k * dyadicScale m)
            (fun i => i.1) (fun i => sqGridPt (N + 1) i.2.1 i.2.2) ω i -
              γ ^ 2 * (-Real.log (dyadicScale k * dyadicScale m)) / 2))
    (S' := fun ω => ∑ s : Fin 2,
        (lqgApprox γ (hcirc ω) (dyadicScale (k + m)) (lqgSubSquare k s)).toReal)
    (fun N => Finset.measurable_sum _ fun i _ => measurable_const.mul
      (Real.measurable_exp.comp ((hXm N i).sub measurable_const)))
    (fun N ω => Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (Real.exp_pos _).le)
    (by
      filter_upwards [hh.ae_continuous_circle_fixed hε] with ω hω
      exact tendsto_gridSum_subSquareMass hγ m (hcirc ω) hω)
  have hae : ∀ᵐ x ∂(subSquareMeasure P), ∀ s : Fin 2, Continuous (hcirc (x.2 s) (dyadicScale m)) := by
    rw [ae_all_iff]
    intro s
    exact (measurePreserving_subSquare_eval s).quasiMeasurePreserving.ae
      (hh.ae_continuous_circle_fixed hδ)
  have hY := tendsto_integral_exp_neg (μ := subSquareMeasure P) hl
    (S := fun (N : ℕ) x => ∑ i : Fin 2 × Fin (N + 1) × Fin (N + 1),
        (dyadicScale k ^ 2 * ((2 * (1 / 8 : ℝ)) ^ 2 / (((N + 1 : ℕ) : ℝ)) ^ 2)) *
          Real.exp (subSquareComparison γ hcirc (dyadicScale k) (dyadicScale m)
            (fun i => i.1) (fun i => sqGridPt (N + 1) i.2.1 i.2.2) x i -
              γ ^ 2 * (1 - Real.log (dyadicScale k) - Real.log (dyadicScale m)) / 2))
    (S' := fun x => ∑ s : Fin 2, subSquareWeight γ hcirc k x s *
        (lqgApprox γ (hcirc (x.2 s)) (dyadicScale m) lqgSquare).toReal)
    (fun N => Finset.measurable_sum _ fun i _ => measurable_const.mul
      (Real.measurable_exp.comp ((hYm N i).sub measurable_const)))
    (fun N x => Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (Real.exp_pos _).le)
    (by
      filter_upwards [hae] with x hx
      exact tendsto_gridSum_subSquareComparison γ k m
        (fun s => hcirc x.1.1 (dyadicScale k) (lqgSquareCentre s)) x.1.2 (fun s => hcirc (x.2 s)) hx)
  exact le_of_tendsto_of_tendsto' hX hY hK

end LatticeProb.Gauss
