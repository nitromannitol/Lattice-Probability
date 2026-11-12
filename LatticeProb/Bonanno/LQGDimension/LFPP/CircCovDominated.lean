/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.CircCovDominated at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.HeatKernel

/-!
# Node `L31d` (`Draft.CircCovDominated`)

We prove `Blueprint.Draft.CircCovDominated`:

1. for `ε > 0` and a zero-mass nondegenerate segment combination `c`,
   `c.circCov ε c ≤ c.logCov c`;
2. the log kernel `logCov` is positive semidefinite on zero-mass nondegenerate families.

## Strategy

* **Fourier representation of the Gaussian kernel** (`gaussPair_fourier`).  With `γ` the
  standard Gaussian measure on `ℂ ≅ ℝ²` and `λ = (√2 t)⁻¹`,
  `e^{-|z-w|²/(4t²)} = ∫ cos(λ⟪x, z - w⟫) dγ(x)`, hence
  `gaussPair t c c' = ∫ (C_c C_{c'} + S_c S_{c'}) dγ` where `C_c(x) = ⟨cos(λ⟪x,·⟫), c⟩` and
  `S_c(x) = ⟨sin(λ⟪x,·⟫), c⟩`.  This gives positivity of `gaussPair` on finite families and,
  since translating `c` by `α` rotates `(C_c, S_c)` by the angle `λ⟪x, α⟫`,
  `gaussPair t (c + α) (c + β) ≤ gaussPair t c c`.
* With the heat-kernel representation (`HeatKernel.gaussPair_heatRep`) this gives the PSD
  property of `logCov` and `logCov (c + α) (c + β) ≤ logCov c c`.
* **Circle averages** (`segCircCov_eq`, `integral_grInt_eq`, `circCov_le_logCov`).  For
  zero-mass `c`, by Fubini (the integrand has integrable logarithmic singularities, uniformly
  in the circle parameters: `integrable_log_tDist`), `circCov ε c c` is the average over
  `(θ, φ) ∈ (0, 2π]²` of `logCov (c + ε e^{iθ}) (c + ε e^{iφ})`; the `log max(|·|, 1)` terms of
  `gffGreen` cancel by zero mass.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.CircDom

open Blueprint.Draft HeatKernel

/-! ## 1. Fourier representation of the Gaussian kernel -/

/-- The frequency scale `(√2 t)⁻¹`. -/
def hkFreq (t : ℝ) : ℝ := (Real.sqrt 2 * t)⁻¹

/-- Cosine feature `z ↦ cos(λ⟪x, z⟫)`. -/
def cosF (t : ℝ) (x z : ℂ) : ℝ := Real.cos (hkFreq t * ⟪x, z⟫)

/-- Sine feature `z ↦ sin(λ⟪x, z⟫)`. -/
def sinF (t : ℝ) (x z : ℂ) : ℝ := Real.sin (hkFreq t * ⟪x, z⟫)

lemma continuous_cosF (t : ℝ) : Continuous fun p : ℂ × ℂ => cosF t p.1 p.2 := by
  unfold cosF; fun_prop

lemma continuous_sinF (t : ℝ) : Continuous fun p : ℂ × ℂ => sinF t p.1 p.2 := by
  unfold sinF; fun_prop

lemma integral_cos_inner (u : ℂ) :
    ∫ x, Real.cos ⟪x, u⟫ ∂(stdGaussian ℂ) = Real.exp (-‖u‖ ^ 2 / 2) := by
  have h := charFun_stdGaussian (E := ℂ) u
  rw [charFun_apply] at h
  have hint : Integrable (fun x : ℂ => Complex.exp (⟪x, u⟫ * Complex.I)) (stdGaussian ℂ) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have h2 := integral_re hint
  rw [h] at h2
  simp only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] at h2
  rw [h2, show (-(‖u‖ : ℂ) ^ 2 / 2) = ((-‖u‖ ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.exp_ofReal_re _

/-- `e^{-|z-w|²/(4t²)} = ∫ (cos cos + sin sin) dγ`. -/
lemma exp_kernel_eq (t : ℝ) (z w : ℂ) :
    Real.exp (-‖z - w‖ ^ 2 / (4 * t ^ 2)) =
      ∫ x, (cosF t x z * cosF t x w + sinF t x z * sinF t x w) ∂(stdGaussian ℂ) := by
  have hfun : (fun x : ℂ => cosF t x z * cosF t x w + sinF t x z * sinF t x w) =
      fun x => Real.cos ⟪x, (hkFreq t : ℝ) • (z - w)⟫ := by
    funext x
    simp only [cosF, sinF, inner_smul_right, inner_sub_right, mul_sub]
    rw [Real.cos_sub]
  rw [hfun, integral_cos_inner, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hkFreq]
  congr 1
  rw [inv_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

lemma abs_cos_mul_add_sin_mul_le (a b c d : ℝ) :
    |Real.cos a * Real.cos b + Real.sin c * Real.sin d| ≤ 2 := by
  have h1 := Real.abs_cos_le_one a
  have h2 := Real.abs_cos_le_one b
  have h3 := Real.abs_sin_le_one c
  have h4 := Real.abs_sin_le_one d
  calc _ ≤ |Real.cos a * Real.cos b| + |Real.sin c * Real.sin d| := abs_add_le _ _
    _ = |Real.cos a| * |Real.cos b| + |Real.sin c| * |Real.sin d| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * 1 + 1 * 1 := by gcongr
    _ = 2 := by norm_num

lemma continuous_feat {g : ℂ → ℂ → ℝ} (hg : Continuous fun p : ℂ × ℂ => g p.1 p.2) (x u v : ℂ) :
    Continuous fun s : ℝ => g x (u + (s : ℂ) * (v - u)) :=
  hg.comp (by fun_prop : Continuous fun s : ℝ => (x, u + (s : ℂ) * (v - u)))

/-- Integrable bounded continuous functions on `unitSq`. -/
lemma integrable_unitSq_of_continuous {g : ℝ × ℝ → ℝ} (hg : Continuous g) :
    Integrable g unitSq := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hg.continuousOn (s := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [ae_mem_unitSq] with q hq
  exact hC q (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self hq)

/-- Fourier representation of one entry `pairHeat`. -/
lemma pairHeat_fourier (a b a' b' : ℂ) (t : ℝ) :
    Integrable (fun x => segAvg (cosF t x) a b * segAvg (cosF t x) a' b' +
      segAvg (sinF t x) a b * segAvg (sinF t x) a' b') (stdGaussian ℂ) ∧
    pairHeat a b a' b' t = ∫ x, (segAvg (cosF t x) a b * segAvg (cosF t x) a' b' +
      segAvg (sinF t x) a b * segAvg (sinF t x) a' b') ∂(stdGaussian ℂ) := by
  set z : ℝ → ℂ := fun s => a + (s : ℂ) * (b - a) with hz
  set z' : ℝ → ℂ := fun s => a' + (s : ℂ) * (b' - a') with hz'
  set K : (ℝ × ℝ) → ℂ → ℝ := fun q x => cosF t x (z q.1) * cosF t x (z' q.2) +
    sinF t x (z q.1) * sinF t x (z' q.2) with hK
  have hKc : Continuous (Function.uncurry K) := by
    simp only [hK, hz, hz', cosF, sinF]
    fun_prop
  have hKi : Integrable (Function.uncurry K) (unitSq.prod (stdGaussian ℂ)) := by
    refine Integrable.of_bound hKc.aestronglyMeasurable 2 (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, hK, cosF, sinF, Real.norm_eq_abs]
    exact abs_cos_mul_add_sin_mul_le _ _ _ _
  have h1 : pairHeat a b a' b' t = ∫ q, ∫ x, K q x ∂(stdGaussian ℂ) ∂unitSq := by
    rw [pairHeat_eq]
    congr 1
    funext q
    simp only [segDist, hK]
    exact exp_kernel_eq t (z q.1) (z' q.2)
  have hcs : ∀ (g : ℂ → ℂ → ℝ), Continuous (fun p : ℂ × ℂ => g p.1 p.2) → ∀ x (u v : ℂ),
      Continuous fun s : ℝ => g x (u + (s : ℂ) * (v - u)) := by
    intro g hg x u v
    exact hg.comp (by fun_prop : Continuous fun s : ℝ => (x, u + (s : ℂ) * (v - u)))
  have hinner : ∀ x, ∫ q, K q x ∂unitSq =
      segAvg (cosF t x) a b * segAvg (cosF t x) a' b' +
        segAvg (sinF t x) a b * segAvg (sinF t x) a' b' := by
    intro x
    have hc1 := hcs _ (continuous_cosF t) x a b
    have hc2 := hcs _ (continuous_cosF t) x a' b'
    have hs1 := hcs _ (continuous_sinF t) x a b
    have hs2 := hcs _ (continuous_sinF t) x a' b'
    have i1 : Integrable (fun q : ℝ × ℝ => cosF t x (z q.1) * cosF t x (z' q.2)) unitSq :=
      integrable_unitSq_of_continuous ((hc1.comp continuous_fst).mul (hc2.comp continuous_snd))
    have i2 : Integrable (fun q : ℝ × ℝ => sinF t x (z q.1) * sinF t x (z' q.2)) unitSq :=
      integrable_unitSq_of_continuous ((hs1.comp continuous_fst).mul (hs2.comp continuous_snd))
    simp only [hK]
    rw [integral_add i1 i2]
    unfold unitSq
    rw [integral_prod_mul (fun s => cosF t x (z s)) (fun s => cosF t x (z' s)),
      integral_prod_mul (fun s => sinF t x (z s)) (fun s => sinF t x (z' s))]
    simp only [segAvg, intervalIntegral.integral_of_le zero_le_one, hz, hz']
  refine ⟨?_, ?_⟩
  · have := hKi.integral_prod_right
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [Function.uncurry]
    exact hinner x
  · rw [h1, integral_integral_swap hKi]
    exact integral_congr_ae (ae_of_all _ hinner)

/-- `Σ_p Σ_p' w w' (f p f p' + g p g p') = (Σ w f)(Σ w' f) + (Σ w g)(Σ w' g)`. -/
lemma list_double_sum (c c' : SegComb) (f g : ℝ × ℂ × ℂ → ℝ) :
    (c.map fun p => (c'.map fun p' => p.1 * p'.1 * (f p * f p' + g p * g p')).sum).sum =
      (c.map fun p => p.1 * f p).sum * (c'.map fun p' => p'.1 * f p').sum +
        (c.map fun p => p.1 * g p).sum * (c'.map fun p' => p'.1 * g p').sum := by
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have : (c'.map fun p' => p.1 * p'.1 * (f p * f p' + g p * g p')).sum =
        p.1 * f p * (c'.map fun p' => p'.1 * f p').sum +
          p.1 * g p * (c'.map fun p' => p'.1 * g p').sum := by
      clear ih
      induction c' with
      | nil => simp
      | cons q c' ih' =>
        simp only [List.map_cons, List.sum_cons, ih']
        ring
    rw [this]
    ring

/-- **Fourier representation of `gaussPair`.** -/
theorem gaussPair_fourier (t : ℝ) (c c' : SegComb) :
    Integrable (fun x => c.avg (cosF t x) * c'.avg (cosF t x) +
      c.avg (sinF t x) * c'.avg (sinF t x)) (stdGaussian ℂ) ∧
    gaussPair t c c' = ∫ x, (c.avg (cosF t x) * c'.avg (cosF t x) +
      c.avg (sinF t x) * c'.avg (sinF t x)) ∂(stdGaussian ℂ) := by
  set Φ : ℝ × ℂ × ℂ → ℝ × ℂ × ℂ → ℂ → ℝ := fun p p' x =>
    p.1 * p'.1 * (segAvg (cosF t x) p.2.1 p.2.2 * segAvg (cosF t x) p'.2.1 p'.2.2 +
      segAvg (sinF t x) p.2.1 p.2.2 * segAvg (sinF t x) p'.2.1 p'.2.2) with hΦ
  have hpt : ∀ x, (c.map fun p => (c'.map fun p' => Φ p p' x).sum).sum =
      c.avg (cosF t x) * c'.avg (cosF t x) + c.avg (sinF t x) * c'.avg (sinF t x) := by
    intro x
    simp only [hΦ, SegComb.avg]
    exact list_double_sum c c' (fun p => segAvg (cosF t x) p.2.1 p.2.2)
      (fun p => segAvg (sinF t x) p.2.1 p.2.2)
  have hin : ∀ p ∈ c, Integrable (fun x => (c'.map fun p' => Φ p p' x).sum) (stdGaussian ℂ) ∧
      ∫ x, (c'.map fun p' => Φ p p' x).sum ∂(stdGaussian ℂ) =
        (c'.map fun p' => p.1 * p'.1 * pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t).sum := by
    intro p _
    obtain ⟨h1, h2⟩ := integral_list_sum_map (μ := stdGaussian ℂ) c' (fun p' x => Φ p p' x)
      (fun p' _ => ((pairHeat_fourier p.2.1 p.2.2 p'.2.1 p'.2.2 t).1.const_mul _))
    refine ⟨h1, h2.trans (congrArg List.sum (List.map_congr_left fun p' _ => ?_))⟩
    simp only [hΦ]
    rw [integral_const_mul, ← (pairHeat_fourier p.2.1 p.2.2 p'.2.1 p'.2.2 t).2]
  obtain ⟨h1, h2⟩ := integral_list_sum_map (μ := stdGaussian ℂ) c
    (fun p x => (c'.map fun p' => Φ p p' x).sum) (fun p hp => (hin p hp).1)
  refine ⟨h1.congr (ae_of_all _ hpt), ?_⟩
  rw [← integral_congr_ae (ae_of_all _ hpt), h2, gaussPair_eq]
  exact congrArg List.sum (List.map_congr_left fun p hp => (hin p hp).2.symm)

lemma gaussPair_comm (t : ℝ) (c c' : SegComb) : gaussPair t c c' = gaussPair t c' c := by
  rw [(gaussPair_fourier t c c').2, (gaussPair_fourier t c' c).2]
  congr 1
  funext x
  ring

/-! ## 2. Positivity and translation domination -/

/-- Positive definiteness of the Gaussian kernel on finite families of segment combinations. -/
lemma gaussPair_quadForm_nonneg {ι : Type*} (s : Finset ι) (c : ι → SegComb) (x : ι → ℝ)
    (t : ℝ) : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, x i * x j * gaussPair t (c i) (c j) := by
  set Φ : ι → ι → ℂ → ℝ := fun i j y => x i * x j * ((c i).avg (cosF t y) * (c j).avg (cosF t y) +
    (c i).avg (sinF t y) * (c j).avg (sinF t y)) with hΦ
  have hint : ∀ i j, Integrable (Φ i j) (stdGaussian ℂ) := fun i j =>
    (gaussPair_fourier t (c i) (c j)).1.const_mul _
  have heq : ∑ i ∈ s, ∑ j ∈ s, x i * x j * gaussPair t (c i) (c j) =
      ∫ y, ∑ i ∈ s, ∑ j ∈ s, Φ i j y ∂(stdGaussian ℂ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ]
    simp only
    rw [integral_const_mul, ← (gaussPair_fourier t (c i) (c j)).2]
  rw [heq]
  refine integral_nonneg fun y => ?_
  have : ∑ i ∈ s, ∑ j ∈ s, Φ i j y = (∑ i ∈ s, x i * (c i).avg (cosF t y)) ^ 2 +
      (∑ i ∈ s, x i * (c i).avg (sinF t y)) ^ 2 := by
    simp only [hΦ, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  positivity

/-- The translate `c + α` of a segment combination. -/
abbrev translate (α : ℂ) (c : SegComb) : SegComb := c.image fun z => z + α

lemma segAvg_cosF_translate (t : ℝ) (y a b α : ℂ) :
    segAvg (cosF t y) (a + α) (b + α) =
      Real.cos (hkFreq t * ⟪y, α⟫) * segAvg (cosF t y) a b -
        Real.sin (hkFreq t * ⟪y, α⟫) * segAvg (sinF t y) a b := by
  have hc : Continuous fun s : ℝ => cosF t y (a + (s : ℂ) * (b - a)) :=
    continuous_feat (continuous_cosF t) y a b
  have hs : Continuous fun s : ℝ => sinF t y (a + (s : ℂ) * (b - a)) :=
    continuous_feat (continuous_sinF t) y a b
  have hpt : ∀ s : ℝ, cosF t y (a + α + (s : ℂ) * (b + α - (a + α))) =
      Real.cos (hkFreq t * ⟪y, α⟫) * cosF t y (a + (s : ℂ) * (b - a)) -
        Real.sin (hkFreq t * ⟪y, α⟫) * sinF t y (a + (s : ℂ) * (b - a)) := by
    intro s
    rw [show a + α + (s : ℂ) * (b + α - (a + α)) = (a + (s : ℂ) * (b - a)) + α by ring]
    simp only [cosF, sinF, inner_add_right, mul_add, Real.cos_add]
    ring
  unfold segAvg
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub ((hc.intervalIntegrable 0 1).const_mul _)
    ((hs.intervalIntegrable 0 1).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

lemma segAvg_sinF_translate (t : ℝ) (y a b α : ℂ) :
    segAvg (sinF t y) (a + α) (b + α) =
      Real.sin (hkFreq t * ⟪y, α⟫) * segAvg (cosF t y) a b +
        Real.cos (hkFreq t * ⟪y, α⟫) * segAvg (sinF t y) a b := by
  have hc : Continuous fun s : ℝ => cosF t y (a + (s : ℂ) * (b - a)) :=
    continuous_feat (continuous_cosF t) y a b
  have hs : Continuous fun s : ℝ => sinF t y (a + (s : ℂ) * (b - a)) :=
    continuous_feat (continuous_sinF t) y a b
  have hpt : ∀ s : ℝ, sinF t y (a + α + (s : ℂ) * (b + α - (a + α))) =
      Real.sin (hkFreq t * ⟪y, α⟫) * cosF t y (a + (s : ℂ) * (b - a)) +
        Real.cos (hkFreq t * ⟪y, α⟫) * sinF t y (a + (s : ℂ) * (b - a)) := by
    intro s
    rw [show a + α + (s : ℂ) * (b + α - (a + α)) = (a + (s : ℂ) * (b - a)) + α by ring]
    simp only [cosF, sinF, inner_add_right, mul_add, Real.sin_add]
    ring
  unfold segAvg
  simp_rw [hpt]
  rw [intervalIntegral.integral_add ((hc.intervalIntegrable 0 1).const_mul _)
    ((hs.intervalIntegrable 0 1).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

lemma avg_cosF_translate (t : ℝ) (y α : ℂ) (c : SegComb) :
    (translate α c).avg (cosF t y) =
      Real.cos (hkFreq t * ⟪y, α⟫) * c.avg (cosF t y) -
        Real.sin (hkFreq t * ⟪y, α⟫) * c.avg (sinF t y) := by
  induction c with
  | nil => simp [SegComb.avg, SegComb.image]
  | cons p c ih =>
    simp only [SegComb.avg, SegComb.image, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, segAvg_cosF_translate]
    ring

lemma avg_sinF_translate (t : ℝ) (y α : ℂ) (c : SegComb) :
    (translate α c).avg (sinF t y) =
      Real.sin (hkFreq t * ⟪y, α⟫) * c.avg (cosF t y) +
        Real.cos (hkFreq t * ⟪y, α⟫) * c.avg (sinF t y) := by
  induction c with
  | nil => simp [SegComb.avg, SegComb.image]
  | cons p c ih =>
    simp only [SegComb.avg, SegComb.image, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, segAvg_sinF_translate]
    ring

lemma rot_ineq (cA sA cB sB C S : ℝ) (hA : sA ^ 2 + cA ^ 2 = 1) (hB : sB ^ 2 + cB ^ 2 = 1) :
    (cA * C - sA * S) * (cB * C - sB * S) + (sA * C + cA * S) * (sB * C + cB * S) ≤
      C * C + S * S := by
  have h1 : (cA * C - sA * S) * (cB * C - sB * S) + (sA * C + cA * S) * (sB * C + cB * S) =
      (cA * cB + sA * sB) * (C * C + S * S) := by ring
  have h2 : cA * cB + sA * sB ≤ 1 := by nlinarith [sq_nonneg (cA - cB), sq_nonneg (sA - sB)]
  have h3 : 0 ≤ C * C + S * S := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  rw [h1]
  nlinarith

/-- Translating the two arguments of `gaussPair` independently can only decrease it. -/
theorem gaussPair_translate_le (t : ℝ) (α β : ℂ) (c : SegComb) :
    gaussPair t (translate α c) (translate β c) ≤ gaussPair t c c := by
  obtain ⟨h1, h2⟩ := gaussPair_fourier t (translate α c) (translate β c)
  obtain ⟨h3, h4⟩ := gaussPair_fourier t c c
  rw [h2, h4]
  refine integral_mono h1 h3 fun y => ?_
  simp only [avg_cosF_translate, avg_sinF_translate]
  exact rot_ineq _ _ _ _ _ _ (Real.sin_sq_add_cos_sq _) (Real.sin_sq_add_cos_sq _)

lemma mass_translate (α : ℂ) (c : SegComb) : (translate α c).mass = c.mass := by
  simp [SegComb.mass, SegComb.image, List.map_map, Function.comp_def]

lemma nondeg_translate {c : SegComb} (hc : c.Nondeg) (α : ℂ) : (translate α c).Nondeg := by
  intro p hp hw
  simp only [SegComb.image, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  intro h
  exact hc q hq hw (add_right_cancel h)

/-- `logCov (c + α) (c + β) ≤ logCov c c` on zero-mass nondegenerate combinations. -/
theorem logCov_translate_le (α β : ℂ) {c : SegComb} (hm : c.mass = 0) (hn : c.Nondeg) :
    (translate α c).logCov (translate β c) ≤ c.logCov c := by
  obtain ⟨i1, e1⟩ := gaussPair_heatRep (translate α c) (translate β c)
    (by rw [mass_translate]; exact hm) (nondeg_translate hn β)
  obtain ⟨i2, e2⟩ := gaussPair_heatRep c c hm hn
  rw [e1, e2]
  refine setIntegral_mono_on i1 i2 measurableSet_Ioi fun t ht => ?_
  exact div_le_div_of_nonneg_right (gaussPair_translate_le t α β c) (le_of_lt ht)

theorem logCov_comm {c c' : SegComb} (hm : c.mass = 0) (hn : c.Nondeg) (hm' : c'.mass = 0)
    (hn' : c'.Nondeg) : c.logCov c' = c'.logCov c := by
  rw [logCov_eq_integral_gaussPair c c' hm hn', logCov_eq_integral_gaussPair c' c hm' hn]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [gaussPair_comm]

/-- **PSD part of `L31d`.** -/
theorem logCov_psdOn {ι : Type*} (F : Finset ι) (c : ι → SegComb)
    (hc : ∀ i ∈ F, (c i).mass = 0 ∧ (c i).Nondeg) :
    PSDOn F (fun i j => (c i).logCov (c j)) := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [star_trivial, Matrix.of_apply]
    exact logCov_comm (hc j j.2).1 (hc j j.2).2 (hc i i.2).1 (hc i i.2).2
  · rw [star_trivial]
    have h1 : dotProduct x (Matrix.mulVec (Matrix.of fun i j : F => (c i).logCov (c j)) x) =
        ∑ i : F, ∑ j : F, x i * x j * (c i).logCov (c j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hint : ∀ i j : F, IntegrableOn (fun t => gaussPair t (c i) (c j) / t) (Ioi 0) :=
      fun i j => integrableOn_gaussPair_div _ _ (hc i i.2).1 (hc j j.2).2
    have h2 : ∑ i : F, ∑ j : F, x i * x j * (c i).logCov (c j) =
        ∫ t in Ioi 0, ∑ i : F, ∑ j : F, x i * x j * (gaussPair t (c i) (c j) / t) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        (hint i j).const_mul _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, logCov_eq_integral_gaussPair _ _ (hc i i.2).1 (hc j j.2).2]
    rw [h1, h2]
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have h3 : ∑ i : F, ∑ j : F, x i * x j * (gaussPair t (c i) (c j) / t) =
        (∑ i : F, ∑ j : F, x i * x j * gaussPair t (c i) (c j)) / t := by
      simp only [Finset.sum_div, mul_div_assoc]
    rw [h3]
    exact div_nonneg (gaussPair_quadForm_nonneg _ (fun i : F => c i) x t) (le_of_lt ht)

/-! ## 3. Circle averages: Fubini with logarithmic singularities -/

/-- The measure `dθ dφ` on `(0, 2π]²`. -/
def circSq : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (0 : ℝ) (2 * π))).prod (volume.restrict (Ioc (0 : ℝ) (2 * π)))

instance : IsFiniteMeasure circSq := by unfold circSq; infer_instance

lemma circSq_real_univ : circSq.real univ = (2 * π) ^ 2 := by
  have h : (0 : ℝ) ≤ 2 * π := by positivity
  simp [circSq, measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod, Real.volume_Ioc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.pi_pos.le, sq]

lemma ae_mem_circSq : ∀ᵐ r ∂circSq, r ∈ Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π) := by
  rw [circSq, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with r hr
  exact Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self hr

/-- The compact parameter box `[0,2π]² × [0,1]²`. -/
def box : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π)) ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)

lemma isCompact_box : IsCompact box :=
  (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)

lemma ae_mem_box : ∀ᵐ x ∂(circSq.prod unitSq), x ∈ box := by
  rw [circSq, unitSq, Measure.prod_restrict, Measure.prod_restrict, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem ((measurableSet_Ioc.prod measurableSet_Ioc).prod
    (measurableSet_Ioc.prod measurableSet_Ioc))] with x hx
  exact Set.prod_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self) hx

lemma integrable_box_of_continuous {g : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hg : Continuous g) :
    Integrable g (circSq.prod unitSq) := by
  obtain ⟨C, hC⟩ := isCompact_box.exists_bound_of_continuousOn hg.continuousOn
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [ae_mem_box] with x hx
  exact hC x hx

/-- The point `ε e^{iθ}`. -/
def cpt (ε θ : ℝ) : ℂ := (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

lemma continuous_cpt (ε : ℝ) : Continuous (cpt ε) := by unfold cpt; fun_prop

/-- The `log max(|·|, 1)` term of `gffGreen` along a translated segment. -/
def lmx (a b : ℂ) (ε s θ : ℝ) : ℝ := Real.log (max ‖a + (s : ℂ) * (b - a) + cpt ε θ‖ 1)

lemma continuous_lmx (a b : ℂ) (ε : ℝ) : Continuous fun p : ℝ × ℝ => lmx a b ε p.1 p.2 := by
  unfold lmx
  refine Continuous.log ?_ fun p => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have := continuous_cpt ε
  fun_prop

/-- `∫₀¹ log max(|a + s(b-a) + ε e^{iθ}|, 1) ds`. -/
def lmInt (a b : ℂ) (ε θ : ℝ) : ℝ := ∫ s in Ioc (0 : ℝ) 1, lmx a b ε s θ

/-- Distance between points of the segments `[a,b] + ε e^{iθ}` and `[a',b'] + ε e^{iφ}`. -/
def tDist (ε : ℝ) (a b a' b' : ℂ) (r q : ℝ × ℝ) : ℝ :=
  segDist (a + cpt ε r.1) (b + cpt ε r.1) (a' + cpt ε r.2) (b' + cpt ε r.2) q

lemma continuous_tDist (ε : ℝ) (a b a' b' : ℂ) :
    Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => tDist ε a b a' b' x.1 x.2 := by
  have := continuous_cpt ε
  unfold tDist segDist
  fun_prop

lemma segProj_translate (a b a' b' α β : ℂ) (s : ℝ) :
    segProj (a + α) (b + α) (a' + β) (b' + β) s =
      ((a + α + (s : ℂ) * (b - a) - (a' + β)).re * (b' - a').re +
        (a + α + (s : ℂ) * (b - a) - (a' + β)).im * (b' - a').im) /
      ((b' - a').re ^ 2 + (b' - a').im ^ 2) := by
  simp only [segProj, add_sub_add_right_eq_sub]

lemma continuous_tProj (ε : ℝ) (a b a' b' : ℂ) :
    Continuous fun x : (ℝ × ℝ) × ℝ =>
      segProj (a + cpt ε x.1.1) (b + cpt ε x.1.1) (a' + cpt ε x.1.2) (b' + cpt ε x.1.2) x.2 := by
  simp only [segProj_translate]
  have := continuous_cpt ε
  fun_prop

/-- `∫_{unitSq} |log(s' - σ(s))| ≤ ∫_{-(K+1)}^{K+1} |log u|` when `|σ| ≤ K` on `[0,1]`. -/
lemma integral_abs_log_sub_unitSq_le {σ : ℝ → ℝ} (hσ : Continuous σ) {K : ℝ}
    (hK : ∀ s ∈ Icc (0 : ℝ) 1, |σ s| ≤ K) :
    ∫ q, |Real.log (q.2 - σ q.1)| ∂unitSq ≤ ∫ u in (-(K + 1))..(K + 1), |Real.log u| := by
  have hint := integrable_abs_log_sub_unitSq hσ
  unfold unitSq at hint ⊢
  rw [integral_prod _ hint]
  have hb : ∀ s ∈ Ioc (0 : ℝ) 1, ‖∫ s' in Ioc (0 : ℝ) 1, |Real.log ((s, s').2 - σ (s, s').1)|‖ ≤
      ∫ u in (-(K + 1))..(K + 1), |Real.log u| := by
    intro s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
    exact setIntegral_abs_log_sub_le (hK s (Ioc_subset_Icc_self hs))
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) 1)
    measure_Ioc_lt_top hb
  refine (Real.le_norm_self _).trans (h.trans (le_of_eq ?_))
  simp [Real.volume_real_Ioc]

/-- Uniform bound for `∫ |log D|` over the unit square. -/
lemma integral_abs_log_segDist_le (a b a' b' : ℂ) (hb' : a' ≠ b') {R K : ℝ}
    (hR : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, segDist a b a' b' q ≤ R)
    (hK : ∀ s ∈ Icc (0 : ℝ) 1, |segProj a b a' b' s| ≤ K) :
    ∫ q, |Real.log (segDist a b a' b' q)| ∂unitSq ≤
      R + |Real.log ‖b' - a'‖| + ∫ u in (-(K + 1))..(K + 1), |Real.log u| := by
  have h1 : Integrable (fun q => |Real.log (segDist a b a' b' q)|) unitSq :=
    (integrable_log_segDist a b a' b' hb').abs
  have h2' : Integrable (fun q : ℝ × ℝ => |Real.log (q.2 - segProj a b a' b' q.1)|) unitSq :=
    integrable_abs_log_sub_unitSq (continuous_segProj a b a' b')
  have h2 : Integrable (fun q : ℝ × ℝ => R + |Real.log ‖b' - a'‖| +
      |Real.log (q.2 - segProj a b a' b' q.1)|) unitSq := (integrable_const _).add h2'
  calc ∫ q, |Real.log (segDist a b a' b' q)| ∂unitSq ≤
        ∫ q, (R + |Real.log ‖b' - a'‖| + |Real.log (q.2 - segProj a b a' b' q.1)|) ∂unitSq := by
        refine integral_mono_ae h1 h2 ?_
        filter_upwards [ae_mem_unitSq, ae_ne_graph_unitSq (continuous_segProj a b a' b').measurable]
          with q hq hne
        exact abs_log_segDist_le a b a' b' hb' hR q
          (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self hq) hne
    _ = R + |Real.log ‖b' - a'‖| + ∫ q, |Real.log (q.2 - segProj a b a' b' q.1)| ∂unitSq := by
        rw [integral_add (integrable_const _) h2', integral_const, unitSq_real_univ, one_smul]
    _ ≤ _ := by
        gcongr
        exact integral_abs_log_sub_unitSq_le (continuous_segProj a b a' b') hK

lemma integrable_log_tDist_slice (ε : ℝ) (a b a' b' : ℂ) (hb' : a' ≠ b') (r : ℝ × ℝ) :
    Integrable (fun q => Real.log (tDist ε a b a' b' r q)) unitSq := by
  unfold tDist
  exact integrable_log_segDist _ _ _ _ fun h => hb' (add_right_cancel h)

lemma integral_abs_log_tDist_le (ε : ℝ) (a b a' b' : ℂ) (hb' : a' ≠ b') {R K : ℝ}
    (hR : ∀ x ∈ box, ‖tDist ε a b a' b' x.1 x.2‖ ≤ R)
    (hK : ∀ x ∈ (Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π)) ×ˢ Icc (0 : ℝ) 1,
      ‖segProj (a + cpt ε x.1.1) (b + cpt ε x.1.1) (a' + cpt ε x.1.2) (b' + cpt ε x.1.2) x.2‖ ≤ K)
    (r : ℝ × ℝ) (hr : r ∈ Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π)) :
    ∫ q, |Real.log (tDist ε a b a' b' r q)| ∂unitSq ≤
      R + |Real.log ‖b' - a'‖| + ∫ u in (-(K + 1))..(K + 1), |Real.log u| := by
  have key := integral_abs_log_segDist_le (a + cpt ε r.1) (b + cpt ε r.1) (a' + cpt ε r.2)
    (b' + cpt ε r.2) (fun h => hb' (add_right_cancel h)) (R := R) (K := K)
    (fun q hq => (le_abs_self _).trans (by
      have := hR (r, q) ⟨hr, hq⟩
      rw [Real.norm_eq_abs] at this
      exact this))
    (fun s hs => by
      have := hK (r, s) ⟨hr, hs⟩
      rw [Real.norm_eq_abs] at this
      exact this)
  rw [add_sub_add_right_eq_sub] at key
  exact key

/-- **Integrability of the logarithmic singularity in all four variables.** -/
lemma integrable_log_tDist (ε : ℝ) (a b a' b' : ℂ) (hb' : a' ≠ b') :
    Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Real.log (tDist ε a b a' b' x.1 x.2))
      (circSq.prod unitSq) := by
  have hmeas : Measurable fun x : (ℝ × ℝ) × (ℝ × ℝ) => Real.log (tDist ε a b a' b' x.1 x.2) :=
    (continuous_tDist ε a b a' b').measurable.log
  obtain ⟨R, hR⟩ := isCompact_box.exists_bound_of_continuousOn
    (continuous_tDist ε a b a' b').continuousOn
  obtain ⟨K, hK⟩ := ((isCompact_Icc.prod isCompact_Icc).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn
    (continuous_tProj ε a b a' b').continuousOn
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun r => integrable_log_tDist_slice ε a b a' b' hb' r, ?_⟩
  refine Integrable.of_bound hmeas.aestronglyMeasurable.norm.integral_prod_right'
    (R + |Real.log ‖b' - a'‖| + ∫ u in (-(K + 1))..(K + 1), |Real.log u|) ?_
  filter_upwards [ae_mem_circSq] with r hr
  have h0 : 0 ≤ ∫ q, ‖Real.log (tDist ε a b a' b' r q)‖ ∂unitSq :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  simp only [Real.norm_eq_abs]
  exact integral_abs_log_tDist_le ε a b a' b' hb' hR hK r hr

/-- The integrand of `segCircCov` in the variables `((θ, φ), (s, s'))`. -/
def grInt (ε : ℝ) (a b a' b' : ℂ) (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  gffGreen (a + (x.2.1 : ℂ) * (b - a) + (ε : ℂ) * Complex.exp ((x.1.1 : ℂ) * Complex.I))
    (a' + (x.2.2 : ℂ) * (b' - a') + (ε : ℂ) * Complex.exp ((x.1.2 : ℂ) * Complex.I))

lemma grInt_eq (ε : ℝ) (a b a' b' : ℂ) (x : (ℝ × ℝ) × (ℝ × ℝ)) :
    grInt ε a b a' b' x = -Real.log (tDist ε a b a' b' x.1 x.2) + lmx a b ε x.2.1 x.1.1 +
      lmx a' b' ε x.2.2 x.1.2 := by
  have h : ∀ (α β s s' : ℂ), a + α + s * (b + α - (a + α)) - (a' + β + s' * (b' + β - (a' + β))) =
      a + s * (b - a) + α - (a' + s' * (b' - a') + β) := by intros; ring
  simp only [grInt, gffGreen, tDist, segDist, lmx, cpt, h]

lemma integrable_grInt (ε : ℝ) (a b a' b' : ℂ) (hb' : a' ≠ b') :
    Integrable (grInt ε a b a' b') (circSq.prod unitSq) := by
  have h1 := (integrable_log_tDist ε a b a' b' hb').neg
  have h2 : Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => lmx a b ε x.2.1 x.1.1) (circSq.prod unitSq) :=
    integrable_box_of_continuous ((continuous_lmx a b ε).comp
      (by fun_prop : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => (x.2.1, x.1.1)))
  have h3 : Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => lmx a' b' ε x.2.2 x.1.2)
      (circSq.prod unitSq) :=
    integrable_box_of_continuous ((continuous_lmx a' b' ε).comp
      (by fun_prop : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => (x.2.2, x.1.2)))
  exact ((h1.add h2).add h3).congr (ae_of_all _ fun x => (grInt_eq ε a b a' b' x).symm)

/-- **Fubini for one pair of segments**: `segCircCov` is the average over the circle
parameters of the inner integral over the segment parameters. -/
lemma segCircCov_eq (ε : ℝ) (a b a' b' : ℂ) (hb' : a' ≠ b') :
    segCircCov ε a b a' b' =
      (2 * π)⁻¹ ^ 2 * ∫ r, ∫ q, grInt ε a b a' b' (r, q) ∂unitSq ∂circSq := by
  have hf := integrable_grInt ε a b a' b' hb'
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  set H : ℝ × ℝ → ℝ := fun q => ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π,
    grInt ε a b a' b' ((θ, φ), q) with hH
  have hHae : H =ᵐ[unitSq] fun q => ∫ r, grInt ε a b a' b' (r, q) ∂circSq := by
    filter_upwards [hf.prod_left_ae] with q hq
    simp only [hH]
    unfold circSq at hq ⊢
    rw [integral_prod _ hq]
    simp only [intervalIntegral.integral_of_le h2π]
  have hHi : Integrable H unitSq := hf.integral_prod_right.congr hHae.symm
  have hseg : segCircCov ε a b a' b' = (2 * π)⁻¹ ^ 2 * ∫ q, H q ∂unitSq := by
    unfold unitSq at hHi ⊢
    rw [integral_prod _ hHi]
    simp only [segCircCov, gffCircleCov, hH, grInt, intervalIntegral.integral_of_le zero_le_one,
      integral_const_mul]
  rw [hseg, integral_congr_ae hHae, ← integral_prod_symm _ hf, integral_prod _ hf]

/-- The inner integral over the segment parameters, for fixed circle parameters. -/
lemma integral_grInt_eq (ε : ℝ) (a b a' b' : ℂ) (hb' : a' ≠ b') (r : ℝ × ℝ) :
    ∫ q, grInt ε a b a' b' (r, q) ∂unitSq =
      segLogPair (a + cpt ε r.1) (b + cpt ε r.1) (a' + cpt ε r.2) (b' + cpt ε r.2) +
        lmInt a b ε r.1 + lmInt a' b' ε r.2 := by
  have hb2 : a' + cpt ε r.2 ≠ b' + cpt ε r.2 := fun h => hb' (add_right_cancel h)
  have i1 : Integrable (fun q => -Real.log (segDist (a + cpt ε r.1) (b + cpt ε r.1)
      (a' + cpt ε r.2) (b' + cpt ε r.2) q)) unitSq := (integrable_log_segDist _ _ _ _ hb2).neg
  have i2 : Integrable (fun q : ℝ × ℝ => lmx a b ε q.1 r.1) unitSq :=
    integrable_unitSq_of_continuous ((continuous_lmx a b ε).comp
      (by fun_prop : Continuous fun q : ℝ × ℝ => (q.1, r.1)))
  have i3 : Integrable (fun q : ℝ × ℝ => lmx a' b' ε q.2 r.2) unitSq :=
    integrable_unitSq_of_continuous ((continuous_lmx a' b' ε).comp
      (by fun_prop : Continuous fun q : ℝ × ℝ => (q.2, r.2)))
  have hpt : ∀ q, grInt ε a b a' b' (r, q) = -Real.log (segDist (a + cpt ε r.1) (b + cpt ε r.1)
      (a' + cpt ε r.2) (b' + cpt ε r.2) q) + lmx a b ε q.1 r.1 + lmx a' b' ε q.2 r.2 := by
    intro q
    rw [grInt_eq]
    rfl
  have i12 : Integrable (fun q => -Real.log (segDist (a + cpt ε r.1) (b + cpt ε r.1)
      (a' + cpt ε r.2) (b' + cpt ε r.2) q) + lmx a b ε q.1 r.1) unitSq := i1.add i2
  simp only [hpt]
  rw [integral_add i12 i3, integral_add i1 i2, integral_neg, segLogPair_eq _ _ _ _ hb2]
  unfold unitSq
  rw [integral_fun_fst (fun s => lmx a b ε s r.1), integral_fun_snd (fun s => lmx a' b' ε s r.2)]
  simp [lmInt, Real.volume_real_Ioc]

/-! ## 4. Assembly -/

lemma list_sum_split (c c' : SegComb) (S : ℝ × ℂ × ℂ → ℝ × ℂ × ℂ → ℝ)
    (X Y : ℝ × ℂ × ℂ → ℝ) :
    (c.map fun p => (c'.map fun p' => p.1 * p'.1 * (S p p' + X p + Y p')).sum).sum =
      (c.map fun p => (c'.map fun p' => p.1 * p'.1 * S p p').sum).sum +
        (c.map fun p => p.1 * X p).sum * c'.mass +
          c.mass * (c'.map fun p' => p'.1 * Y p').sum := by
  unfold SegComb.mass
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have : (c'.map fun p' => p.1 * p'.1 * (S p p' + X p + Y p')).sum =
        (c'.map fun p' => p.1 * p'.1 * S p p').sum + p.1 * X p * (c'.map fun p' => p'.1).sum +
          p.1 * (c'.map fun p' => p'.1 * Y p').sum := by
      clear ih
      induction c' with
      | nil => simp
      | cons q c' ih' =>
        simp only [List.map_cons, List.sum_cons, ih']
        ring
    rw [this]
    ring

lemma logCov_translate_eq (α β : ℂ) (c : SegComb) :
    (translate α c).logCov (translate β c) = (c.map fun p => (c.map fun p' => p.1 * p'.1 *
      segLogPair (p.2.1 + α) (p.2.2 + α) (p'.2.1 + β) (p'.2.2 + β)).sum).sum := by
  simp only [SegComb.logCov, SegComb.image, List.map_map, Function.comp_def]

/-- **Domination part of `L31d`**: `circCov ε c c ≤ logCov c c` for zero-mass nondegenerate
`c` (any radius `ε`). -/
theorem circCov_le_logCov (ε : ℝ) {c : SegComb} (hm : c.mass = 0) (hn : c.Nondeg) :
    c.circCov ε c ≤ c.logCov c := by
  set G : ℝ × ℂ × ℂ → ℝ × ℂ × ℂ → ℝ × ℝ → ℝ := fun p p' r =>
    p.1 * p'.1 * ∫ q, grInt ε p.2.1 p.2.2 p'.2.1 p'.2.2 (r, q) ∂unitSq with hG
  have hpair : ∀ p ∈ c, ∀ p' ∈ c, Integrable (G p p') circSq ∧
      p.1 * p'.1 * segCircCov ε p.2.1 p.2.2 p'.2.1 p'.2.2 =
        (2 * π)⁻¹ ^ 2 * ∫ r, G p p' r ∂circSq := by
    intro p _ p' hp'
    by_cases hw : p'.1 = 0
    · simp [hG, hw]
    · have hb' := hn p' hp' hw
      refine ⟨(integrable_grInt ε _ _ _ _ hb').integral_prod_left.const_mul _, ?_⟩
      rw [segCircCov_eq ε _ _ _ _ hb', hG]
      simp only
      rw [integral_const_mul]
      ring
  have hval : ∀ r, (c.map fun p => (c.map fun p' => G p p' r).sum).sum =
      (translate (cpt ε r.1) c).logCov (translate (cpt ε r.2) c) := by
    intro r
    have hpt : ∀ p ∈ c, ∀ p' ∈ c, G p p' r = p.1 * p'.1 *
        (segLogPair (p.2.1 + cpt ε r.1) (p.2.2 + cpt ε r.1) (p'.2.1 + cpt ε r.2)
          (p'.2.2 + cpt ε r.2) + lmInt p.2.1 p.2.2 ε r.1 + lmInt p'.2.1 p'.2.2 ε r.2) := by
      intro p _ p' hp'
      by_cases hw : p'.1 = 0
      · simp [hG, hw]
      · rw [hG]
        simp only
        rw [integral_grInt_eq ε _ _ _ _ (hn p' hp' hw) r]
    calc (c.map fun p => (c.map fun p' => G p p' r).sum).sum
        = (c.map fun p => (c.map fun p' => p.1 * p'.1 *
          (segLogPair (p.2.1 + cpt ε r.1) (p.2.2 + cpt ε r.1) (p'.2.1 + cpt ε r.2)
            (p'.2.2 + cpt ε r.2) + lmInt p.2.1 p.2.2 ε r.1 + lmInt p'.2.1 p'.2.2 ε r.2)).sum).sum :=
          congrArg List.sum (List.map_congr_left fun p hp =>
            congrArg List.sum (List.map_congr_left fun p' hp' => hpt p hp p' hp'))
      _ = (translate (cpt ε r.1) c).logCov (translate (cpt ε r.2) c) := by
          rw [list_sum_split, hm, mul_zero, zero_mul, add_zero, add_zero, logCov_translate_eq]
  have hL : ∀ p ∈ c, Integrable (fun r => (c.map fun p' => G p p' r).sum) circSq ∧
      ∫ r, (c.map fun p' => G p p' r).sum ∂circSq = (c.map fun p' => ∫ r, G p p' r ∂circSq).sum :=
    fun p hp => integral_list_sum_map c (fun p' => G p p') (fun p' hp' => (hpair p hp p' hp').1)
  obtain ⟨hI, hE⟩ := integral_list_sum_map c (fun p r => (c.map fun p' => G p p' r).sum)
    (fun p hp => (hL p hp).1)
  have hpi : (0 : ℝ) < 2 * π := by positivity
  calc c.circCov ε c
      = (c.map fun p => (c.map fun p' => (2 * π)⁻¹ ^ 2 * ∫ r, G p p' r ∂circSq).sum).sum :=
        congrArg List.sum (List.map_congr_left fun p hp =>
          congrArg List.sum (List.map_congr_left fun p' hp' => (hpair p hp p' hp').2))
    _ = (2 * π)⁻¹ ^ 2 * (c.map fun p => (c.map fun p' => ∫ r, G p p' r ∂circSq).sum).sum := by
        simp only [List.sum_map_mul_left]
    _ = (2 * π)⁻¹ ^ 2 * ∫ r, (c.map fun p => (c.map fun p' => G p p' r).sum).sum ∂circSq := by
        rw [hE]
        congr 1
        exact congrArg List.sum (List.map_congr_left fun p hp => (hL p hp).2.symm)
    _ ≤ (2 * π)⁻¹ ^ 2 * ∫ _r, c.logCov c ∂circSq := by
        refine mul_le_mul_of_nonneg_left (integral_mono hI (integrable_const _) fun r => ?_)
          (by positivity)
        dsimp only
        rw [hval r]
        exact logCov_translate_le _ _ hm hn
    _ = c.logCov c := by
        rw [integral_const, circSq_real_univ, smul_eq_mul, ← mul_assoc, ← mul_pow,
          inv_mul_cancel₀ hpi.ne', one_pow, one_mul]

end LQGDimension.CircDom

namespace LQGDimension

/-- **Node `L31d`** (`Blueprint.Draft.CircCovDominated`): circle averaging decreases the
variance of zero-mass nondegenerate segment combinations, and the log kernel is positive
semidefinite on zero-mass nondegenerate families. -/
theorem circCovDominated : Blueprint.Draft.CircCovDominated :=
  ⟨fun ε _ _ hm hn => CircDom.circCov_le_logCov ε hm hn,
    fun _ F c hc => CircDom.logCov_psdOn F c hc⟩

end LQGDimension
