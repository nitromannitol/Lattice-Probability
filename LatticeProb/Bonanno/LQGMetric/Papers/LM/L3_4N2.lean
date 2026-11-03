/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4N2 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4N1

/-!
# LM Lemma 3.4, increment input: exponential moments and `LMIncrLeaf` from the nesting

Source: MQ arXiv:1812.03913 (`lqg_geodesics.tex`), proof of Lemma 4.4 (l. 633–657), Remark
eq. `(zero-boundary)` (l. 659–667), proof of Prop 4.3 l. 693–700 ("`𝔥_{0,r_ℓ} = 𝔥_{0,1} +
𝔥̃_{0,r_ℓ}`, where `𝔥̃_{0,r_ℓ}` is harmonic in `B(0,r_ℓ)` and agrees with a zero-boundary GFF in
`B(0,1)` outside of `B(0,r_ℓ)` … `𝔥̃_{0,r_ℓ}` is independent of `𝓕_{0,1}`"); LM arXiv:1905.00379
Lemma 3.4 (l. 696–706).

* `lintegral_exp_nestPhi_le` — MQ Lemma 4.4 / Remark (zero-boundary), exponential-moment form:
  if `D` is independent of `Y − D`, `Y` a whole-plane GFF and `Y − D` centred, then
  `E exp(κ Φ(D)) ≤ 2 exp((κ|B_ρ|)² radK δ ρ / 2)`. MQ use the Gaussian law of `𝔥̃(y) − 𝔥̃(0)`;
  we use instead `E e^{tD(φ)} ≤ E e^{tY(φ)}` (independence and Jensen), which avoids proving that
  the harmonic part is Gaussian.
* `LMNestLeaf` — the nesting of the Markov decompositions across scales (MQ l. 693–700) together
  with `𝔥^{r}(0) = h_r(0)`, as an exact open statement.
* `lmIncrLeaf_of_nest`, `lmLem3_1a_of_nest`, `lmLem3_1b_of_nest`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM

section Moment

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma measurable_eval_distC (φ : TestC) : Measurable fun T : DistC => T φ :=
  measurable_distOn_apply φ

/-- `E e^{a|D(φ)|} ≤ 2 e^{a² logCov(φ,φ)/2}` for a mean-zero test function `φ`. -/
theorem lintegral_exp_abs_pair_le {Y D : Ω → DistC} (hY : IsWholePlaneGFF Y P)
    (hD : Measurable D) (hind : IndepFun D (fun ω => Y ω - D ω) P)
    (hR : ∀ φ : TestC0, Integrable (fun ω => (Y ω - D ω) φ.1) P ∧
      ∫ ω, (Y ω - D ω) φ.1 ∂P = 0) (φ : TestC0) (a : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |D ω φ.1|)) ∂P ≤
      2 * ENNReal.ofReal (Real.exp (logCov φ.1 φ.1 * a ^ 2 / 2)) := by
  have hYg : HasGaussianLaw (fun ω => Y ω φ.1) P := hY.gaussian.hasGaussianLaw_eval φ
  have hvar : Var[fun ω => Y ω φ.1; P] = logCov φ.1 φ.1 := by
    have hm : AEMeasurable (fun ω => Y ω φ.1) P :=
      ((measurable_eval_distC φ.1).comp hY.measurable).aemeasurable
    rw [← covariance_self hm]
    exact hY.covariance_eq φ φ
  have one : ∀ t : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (t * D ω φ.1)) ∂P ≤
      ENNReal.ofReal (Real.exp (logCov φ.1 φ.1 * t ^ 2 / 2)) := fun t => by
    have hX : Measurable fun ω => t * D ω φ.1 :=
      ((measurable_eval_distC φ.1).comp hD).const_mul t
    have hZ : Measurable fun ω => t * (Y ω - D ω) φ.1 := by
      have : (fun ω => t * (Y ω - D ω) φ.1) = fun ω => t * (Y ω φ.1 - D ω φ.1) := by
        funext ω; rfl
      rw [this]
      exact (((measurable_eval_distC φ.1).comp hY.measurable).sub
        ((measurable_eval_distC φ.1).comp hD)).const_mul t
    have hi : IndepFun (fun ω => t * D ω φ.1) (fun ω => t * (Y ω - D ω) φ.1) P :=
      hind.comp (f := fun ω => D ω) (g := fun ω => Y ω - D ω) (φ := fun T : DistC => t * T φ.1)
        (ψ := fun T : DistC => t * T φ.1) ((measurable_eval_distC φ.1).const_mul t)
        ((measurable_eval_distC φ.1).const_mul t)
    have h1 := lintegral_exp_le_of_indepFun hX hZ hi ((hR φ).1.const_mul t)
      (by rw [integral_const_mul, (hR φ).2, mul_zero])
    have he : ∀ ω, t * D ω φ.1 + t * (Y ω - D ω) φ.1 = t * Y ω φ.1 := fun ω => by
      show t * D ω φ.1 + t * (Y ω φ.1 - D ω φ.1) = _
      ring
    simp_rw [he] at h1
    rw [lintegral_exp_gauss hYg (hY.centered φ) t, hvar] at h1
    exact h1
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |D ω φ.1|)) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (a * D ω φ.1)) +
          ENNReal.ofReal (Real.exp (-a * D ω φ.1))) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rcases abs_cases (D ω φ.1) with ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [h1]; linarith [Real.exp_pos (-a * D ω φ.1)]
        · rw [h1, mul_neg, ← neg_mul]; linarith [Real.exp_pos (a * D ω φ.1)]
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (a * D ω φ.1)) ∂P +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-a * D ω φ.1)) ∂P :=
        lintegral_add_left (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (((measurable_eval_distC φ.1).comp hD).const_mul a))) _
    _ ≤ _ := by
        rw [two_mul]
        refine add_le_add (one a) ((one (-a)).trans_eq ?_)
        rw [neg_sq]

/-- **MQ Lemma 4.4 / Remark (zero-boundary), exponential-moment form**:
`E exp(κ Φ(D)) ≤ 2 exp((κ |B̄_ρ|)² radK δ ρ / 2)`. -/
theorem lintegral_exp_nestPhi_le {Y D : Ω → DistC} (hY : IsWholePlaneGFF Y P)
    (hD : Measurable D) (hind : IndepFun D (fun ω => Y ω - D ω) P)
    (hR : ∀ φ : TestC0, Integrable (fun ω => (Y ω - D ω) φ.1) P ∧
      ∫ ω, (Y ω - D ω) φ.1 ∂P = 0) {δ ρ κ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hκ : 0 ≤ κ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (κ * nestPhi hδ.le ρ (D ω))) ∂P ≤
      ENNReal.ofReal (2 * Real.exp ((κ * (volume (closedBall (0 : ℂ) ρ)).toReal) ^ 2 *
        radK δ ρ / 2)) := by
  set B := closedBall (0 : ℂ) ρ
  have hB0 : volume B ≠ 0 := (measure_closedBall_pos volume (0 : ℂ) hρ).ne'
  have hBt : volume B ≠ ∞ := measure_closedBall_lt_top.ne
  set m := (volume B).toReal with hm
  have hm0 : 0 < m := ENNReal.toReal_pos hB0 hBt
  set a := κ * m
  have ha : 0 ≤ a := mul_nonneg hκ hm0.le
  set X : Ω → ℂ → ℝ := fun ω y => |D ω (radDiff hδ.le y 0).1|
  have hXm : Measurable (Function.uncurry X) :=
    continuous_abs.measurable.comp ((measurable_pair_radDiff hδ.le).comp
      ((hD.comp measurable_fst).prodMk measurable_snd))
  -- Jensen, pointwise in `ω`
  have hJ : ∀ ω, ENNReal.ofReal (Real.exp (κ * nestPhi hδ.le ρ (D ω))) ≤
      ENNReal.ofReal m⁻¹ * ∫⁻ y in B, ENNReal.ofReal (Real.exp (a * X ω y)) := by
    intro ω
    have hc : Continuous (X ω) := (continuous_pair_radDiff hδ.le (D ω)).abs
    have hi1 : IntegrableOn (fun y => a * X ω y) B :=
      (hc.const_mul a).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    have hi2 : IntegrableOn (fun y => Real.exp (a * X ω y)) B :=
      (Real.continuous_exp.comp (hc.const_mul a)).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)
    have hjen := ConvexOn.map_set_average_le (s := univ) (g := Real.exp) convexOn_exp
      Real.continuous_exp.continuousOn isClosed_univ hB0 hBt
      (Eventually.of_forall fun _ => mem_univ _) hi1 hi2
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, integral_const_mul,
      measureReal_def, ← hm] at hjen
    have hk : m⁻¹ * (a * ∫ y in B, X ω y) = κ * nestPhi hδ.le ρ (D ω) := by
      rw [nestPhi_eq]; simp only [a]; field_simp
      try rfl
    rw [hk] at hjen
    refine (ENNReal.ofReal_le_ofReal hjen).trans_eq ?_
    rw [ENNReal.ofReal_mul (inv_nonneg.2 ENNReal.toReal_nonneg), ← hm,
      ofReal_integral_eq_lintegral_ofReal hi2 (Eventually.of_forall fun y => (Real.exp_pos _).le)]
  have hjm : Measurable (Function.uncurry fun ω y => ENNReal.ofReal (Real.exp (a * X ω y))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hXm.const_mul a))
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (κ * nestPhi hδ.le ρ (D ω))) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal m⁻¹ * ∫⁻ y in B, ENNReal.ofReal (Real.exp (a * X ω y))) ∂P :=
        lintegral_mono hJ
    _ = ENNReal.ofReal m⁻¹ * ∫⁻ y in B, (∫⁻ ω, ENNReal.ofReal (Real.exp (a * X ω y)) ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap
          hjm.aemeasurable]
    _ ≤ ENNReal.ofReal m⁻¹ * ∫⁻ _y in B,
          2 * ENNReal.ofReal (Real.exp (radK δ ρ * a ^ 2 / 2)) := by
        refine mul_le_mul' le_rfl (setLIntegral_mono measurable_const fun y hy => ?_)
        refine (lintegral_exp_abs_pair_le hY hD hind hR (radDiff hδ.le y 0) a).trans ?_
        have hy' : ‖y - 0‖ ≤ ρ := by rw [sub_zero, ← dist_zero_right]; exact hy
        gcongr
        exact logCov_radDiff_le hδ hρ.le hy'
    _ = _ := by
        rw [setLIntegral_const, ← ENNReal.ofReal_toReal hBt, ← hm]
        have e : ∀ x y z w : ℝ≥0∞, x * (y * z * w) = y * z * (x * w) := fun x y z w => by ring
        rw [e, ← ENNReal.ofReal_mul (inv_nonneg.2 hm0.le), inv_mul_cancel₀ hm0.ne',
          ENNReal.ofReal_one, mul_one, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
          mul_comm (radK δ ρ)]

end Moment

/-- **The nesting of the Markov decompositions across scales** (MQ l. 693–700, LM Lemma 2.1 at
two scales) **and `𝔥^{r_k}(0) = h_{r_k}(0)`**, exact open statement. With `Y_j = lmScaled h r_j`:
`D_j` (the scaled increment `(𝔥^{r_j} − 𝔥^{r_{j−1}})(r_j ·)`, `D_0 = 𝔥^{r_0}(r_0 ·) − h_{r_0}(0)`)
is `F_j`-measurable, independent of `F_{j−1}` and of `Y_j − D_j` (which is centred), and the
scaled harmonic part at scale `r_k` is the telescoping sum of the `D_j`. -/
def LMNestLeaf (s₁ : ℝ) : Prop :=
  ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ r : ℕ → ℝ, (∀ k, 0 < r k) → Antitone r →
    (∀ k, r (k + 1) / r k ≤ s₁) →
    ∃ (F : ℕ → MeasurableSpace Ω) (D : ℕ → Ω → DistC), Monotone F ∧ (∀ j, F j ≤ mΩ) ∧
      (∀ j, Measurable[F j] (D j)) ∧
      (∀ j, Indep (MeasurableSpace.comap (D (j + 1)) inferInstance) (F j) P) ∧
      (∀ j, IndepFun (D j) (fun ω => lmScaled h (r j) ω - D j ω) P) ∧
      (∀ j (φ : TestC0), Integrable (fun ω => (lmScaled h (r j) ω - D j ω) φ.1) P ∧
        ∫ ω, (lmScaled h (r j) ω - D j ω) φ.1 ∂P = 0) ∧
      ∀ hh0 hz G : ℕ → Ω → DistC, (∀ k, IsLMRep P h (r k) (hh0 k) (hz k) (G k)) →
        ∀ k, ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (ball (0 : ℂ) 1) ∧
          (∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (G k ω) φ = ∫ x, g x * φ x) ∧
          ∃ d : ℕ → ℂ → ℝ, (∀ j ≤ k, HarmonicOnNhd (d j) (ball (0 : ℂ) 1) ∧
            ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (D j ω) φ = ∫ x, d j x * φ x) ∧
          ∀ u ∈ ball (0 : ℂ) 1, g u - circleAvg (lmScaled h (r k) ω) 1 0 =
            ∑ j ∈ range (k + 1), (d j ((r k / r j : ℝ) • u) - d j 0)

lemma oscC_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ oscC δ := by
  unfold oscC
  have := expNegInvGlue.nonneg (δ ^ 2)
  have := integral_radProf_pos hδ
  positivity

/-- **`LMIncrLeaf` from the nesting** (MQ l. 693–700 with Lemma 4.4 / Remark). -/
theorem lmIncrLeaf_of_nest {s₁ s₂ : ℝ} (hs₂0 : 0 < s₂) (hs₂ : s₂ < 1) (hN : LMNestLeaf s₁) :
    LMIncrLeaf s₁ s₂ := by
  set s₃ := lmS3 s₂ with hs₃
  have hs₃1 : s₃ < 1 := by rw [hs₃]; unfold lmS3; linarith
  set δ := (1 - s₃) / 3 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set ρ := s₃ + δ with hρdef
  have hρδ : ρ + δ < 1 := by rw [hρdef, hδdef]; linarith
  have hρ : 0 < ρ := by rw [hρdef, hs₃]; unfold lmS3; linarith
  set κ := oscC δ
  have hκ : 0 ≤ κ := oscC_nonneg hδ
  refine ⟨2 * Real.exp ((κ * (volume (closedBall (0 : ℂ) ρ)).toReal) ^ 2 * radK δ ρ / 2),
    by positivity, ?_⟩
  intro Ω mΩ P _ h hh r hr0 hrA hrs
  obtain ⟨F, D, hF, hFle, hDm, hDi, hDR, hR, hdec⟩ := hN P h hh r hr0 hrA hrs
  refine ⟨F, fun j ω => κ * nestPhi hδ.le ρ (D j ω), hF, hFle,
    fun j ω => mul_nonneg hκ (nestPhi_nonneg _ _ _),
    fun j => ((measurable_nestPhi hδ.le ρ).const_mul κ).comp (hDm j), fun j => ?_,
    fun j => lintegral_exp_nestPhi_le (isWholePlaneGFF_lmScaled hh.1 (hr0 j))
      ((hDm j).mono (hFle j) le_rfl) (hDR j) (hR j) hδ hρ hκ, ?_⟩
  · refine indep_of_indep_of_le_left (hDi j) ?_
    have hf : Measurable fun T : DistC => κ * nestPhi hδ.le ρ T :=
      (measurable_nestPhi hδ.le ρ).const_mul κ
    exact (MeasurableSpace.comap_comp (f := fun T : DistC => κ * nestPhi hδ.le ρ T)
      (g := D (j + 1))).symm.le.trans
        (MeasurableSpace.comap_mono hf.comap_le)
  · intro hh0 hz G hrep k
    filter_upwards [hdec hh0 hz G hrep k] with ω ⟨g, hg, hgrep, d, hd, hsum⟩
    refine ⟨g, hg, hgrep, d, fun j hj => ⟨(hd j hj).1.mono (ball_subset_ball hs₃1.le),
      fun y hy => osc_le_nestPhi hδ hρδ (hd j hj).1 (hd j hj).2 ?_⟩, fun u hu => hsum u
        (ball_subset_ball (by linarith) hu)⟩
    rw [mem_ball, dist_zero_right] at hy
    rw [hρdef]; linarith

/-- **LM Lemma 3.1 (1)** (`N = 0`) from the nesting `LMNestLeaf`. -/
theorem lmLem3_1a_of_nest (hN : ∀ s₁ : ℝ, 0 < s₁ → s₁ < 1 → LMNestLeaf s₁) : LMLem3_1a :=
  lmLem3_1a_of_incr fun s₁ _ h1 h2 h3 => lmIncrLeaf_of_nest (h1.trans h2) h3 (hN s₁ h1 (h2.trans h3))

end LQGMetric.LM
