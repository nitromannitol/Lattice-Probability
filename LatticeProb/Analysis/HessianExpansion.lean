import Mathlib
import LatticeProb.Analysis.W2pApprox

/-!
# First-order expansion of the limit gradient of a `W^{2,p}` approximation, `p > d`

Let `uε n` be smooth approximations of `u` on an open set `U` whose Hessians converge in `L^p` on
compact subsets of `U` to `G` (`IsW2pApprox`), and let `V` be the locally uniform limit of the
gradients `D (uε n)`. Assuming Morrey's oscillation estimate on balls, `V` is Lipschitz in the mean
with respect to `G`, and it is differentiable with derivative `G x` at every strong `L^p` Lebesgue
point `x` of `G`.

## Main results

* `enorm_sub_sub_le_of_isW2pApprox`: the limiting Morrey inequality
  `‖V y - V x - G x (y - x)‖ ≤ c ‖G - G x‖_{L^p(B(x, r))}` for `y ∈ B(x, r)` and
  `closedBall x r ⊆ U`, whenever the Morrey estimate on `B(x, r)` holds with factor `c`.
* `hasFDerivAt_of_enorm_sub_sub_le`: a remainder bound of Morrey type on small balls gives
  differentiability at a strong `L^p` Lebesgue point.
* `hessianExpansion_of_morrey_gradientLimit`: both statements, with the constant of Morrey's
  estimate.
-/

open MeasureTheory Metric Filter Topology Asymptotics Set
open scoped InnerProductSpace ContDiff ENNReal NNReal

namespace LatticeProb.PegdenSmart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {p : ℝ≥0∞}

omit [FiniteDimensional ℝ E] in
/-- Triangle inequality in `L^p(B(x, r))` for functions with values in `E →L[ℝ] E →L[ℝ] ℝ`, the
first term being bounded by its `L^p` norm on `closedBall x r`. -/
private theorem eLpNorm_add_le_indicator_closedBall (hp : 1 ≤ p) (a b : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x : E) (r : ℝ) :
    eLpNorm (fun w => a w + b w) p (μ.restrict (ball x r)) ≤
      eLpNorm ((closedBall x r).indicator a) p μ + eLpNorm b p (μ.restrict (ball x r)) := by
  let _ : ESeminormedAddMonoid (E →L[ℝ] E →L[ℝ] ℝ) :=
    (NormedAddGroup.toENormedAddMonoid (F := E →L[ℝ] E →L[ℝ] ℝ)).toESeminormedAddMonoid
  have _ : ContinuousAdd (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup (E →L[ℝ] E →L[ℝ] ℝ)).toContinuousAdd
  have ha : eLpNorm a p (μ.restrict (ball x r)) ≤ eLpNorm ((closedBall x r).indicator a) p μ :=
    calc eLpNorm a p (μ.restrict (ball x r)) ≤ eLpNorm a p (μ.restrict (closedBall x r)) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono_set μ ball_subset_closedBall)
      _ = eLpNorm ((closedBall x r).indicator a) p μ :=
          (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall).symm
  exact (eLpNorm_add_le (f := a) (g := b) hp).trans (add_le_add ha le_rfl)

/-- Limiting Morrey inequality: if the Morrey estimate holds on `B(x, r)` with factor `c`, then the
locally uniform limit `V` of the gradients of a `W^{2,p}` approximation satisfies
`‖V y - V x - G x (y - x)‖ ≤ c ‖G - G x‖_{L^p(B(x, r))}` for `y ∈ B(x, r)`, when
`closedBall x r ⊆ U`. -/
theorem enorm_sub_sub_le_of_isW2pApprox (hp : 1 ≤ p) {U : Set E} {u : E → ℝ}
    {uε : ℕ → E → ℝ} {ε : ℕ → ℝ} {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hW : IsW2pApprox μ p U u uε ε G) {V : E → E →L[ℝ] ℝ}
    (hV : ∀ K : Set E, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n => fderiv ℝ (uε n)) V atTop K)
    {x : E} {r : ℝ} (hr : 0 < r) (hxr : closedBall x r ⊆ U) {y : E} (hy : y ∈ ball x r)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hM : ∀ f : E → E →L[ℝ] ℝ, ContDiffOn ℝ 1 f (ball x r) →
      ‖f y - f x‖ₑ ≤ c * eLpNorm (fderiv ℝ f) p (μ.restrict (ball x r))) :
    ‖V y - V x - G x (y - x)‖ₑ ≤ c * eLpNorm (fun w => G w - G x) p (μ.restrict (ball x r)) := by
  obtain ⟨hU, -, hε, hsmooth, -, -, hL⟩ := hW
  have hcK : IsCompact (closedBall x r) := isCompact_closedBall x r
  obtain ⟨δ, hδ, hδU⟩ := hcK.exists_cthickening_subset_open hU hxr
  have hev : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (uε n) (ball x r) := by
    filter_upwards [(tendsto_order.1 hε).2 δ hδ] with n hn
    refine (hsmooth n).mono fun z hz w hw => hδU ?_
    exact mem_cthickening_of_dist_le w z δ _ (ball_subset_closedBall hz)
      ((mem_closedBall.1 hw).trans hn.le)
  set A := eLpNorm (fun w => G w - G x) p (μ.restrict (ball x r))
  have key : ∀ᶠ n in atTop, ‖fderiv ℝ (uε n) y - G x y - (fderiv ℝ (uε n) x - G x x)‖ₑ ≤
      c * (eLpNorm ((closedBall x r).indicator
        fun w => fderiv ℝ (fderiv ℝ (uε n)) w - G w) p μ + A) := by
    filter_upwards [hev] with n hn
    have hd : ContDiffOn ℝ 1 (fderiv ℝ (uε n)) (ball x r) :=
      hn.fderiv_of_isOpen isOpen_ball (WithTop.coe_le_coe.2 le_top)
    have hf : ContDiffOn ℝ 1 (fun w => fderiv ℝ (uε n) w - G x w) (ball x r) :=
      hd.sub (G x).contDiff.contDiffOn
    have hfd : ∀ w ∈ ball x r, fderiv ℝ (fun w => fderiv ℝ (uε n) w - G x w) w =
        fderiv ℝ (fderiv ℝ (uε n)) w - G x := by
      intro w hw
      have hdw : DifferentiableAt ℝ (fderiv ℝ (uε n)) w :=
        (hd.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hw)
      exact (hdw.hasFDerivAt.sub (G x).hasFDerivAt).fderiv
    calc ‖fderiv ℝ (uε n) y - G x y - (fderiv ℝ (uε n) x - G x x)‖ₑ
        ≤ c * eLpNorm (fderiv ℝ fun w => fderiv ℝ (uε n) w - G x w) p
            (μ.restrict (ball x r)) := hM (fun w => fderiv ℝ (uε n) w - G x w) hf
      _ = c * eLpNorm (fun w => (fderiv ℝ (fderiv ℝ (uε n)) w - G w) + (G w - G x)) p
            (μ.restrict (ball x r)) := by
          congr 1
          apply eLpNorm_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
          rw [hfd w hw]
          abel
      _ ≤ _ := by
          gcongr
          exact eLpNorm_add_le_indicator_closedBall hp _ _ x r
  have hlim : Tendsto (fun n => ‖fderiv ℝ (uε n) y - G x y - (fderiv ℝ (uε n) x - G x x)‖ₑ)
      atTop (𝓝 ‖V y - G x y - (V x - G x x)‖ₑ) := by
    have hy' := (hV {y} isCompact_singleton
      (singleton_subset_iff.2 (hxr (ball_subset_closedBall hy)))).tendsto_at (mem_singleton y)
    have hx' := (hV {x} isCompact_singleton
      (singleton_subset_iff.2 (hxr (mem_closedBall_self hr.le)))).tendsto_at (mem_singleton x)
    exact ((hy'.sub_const _).sub (hx'.sub_const _)).enorm
  have hlim' : Tendsto (fun n => c * (eLpNorm ((closedBall x r).indicator
      fun w => fderiv ℝ (fderiv ℝ (uε n)) w - G w) p μ + A)) atTop (𝓝 (c * (0 + A))) :=
    ENNReal.Tendsto.const_mul ((hL _ hcK hxr).add tendsto_const_nhds) (Or.inr hc)
  have hle := le_of_tendsto_of_tendsto hlim hlim' key
  rw [zero_add] at hle
  calc ‖V y - V x - G x (y - x)‖ₑ = ‖V y - G x y - (V x - G x x)‖ₑ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ c * A := hle

/-- A first-order remainder bound of Morrey type on small balls gives differentiability at a strong
`L^p` Lebesgue point: if `‖V y - V x - H x (y - x)‖ ≤ C r^{1 - d/p} ‖H - H x‖_{L^p(B(x, r))}` for
`y ∈ B(x, r)` and `0 < r < δ`, and `⨍_{B_r(x)} |H - H x|^p → 0`, then `V` has derivative `H x`
at `x`. -/
theorem hasFDerivAt_of_enorm_sub_sub_le [μ.IsAddHaarMeasure] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {V : E → F} {H : E → E →L[ℝ] F} (hH : AEStronglyMeasurable H μ) {x : E}
    {δ : ℝ} (hδ : 0 < δ) (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {C : ℝ≥0}
    (hb : ∀ r, 0 < r → r < δ → ∀ y ∈ ball x r, ‖V y - V x - H x (y - x)‖ₑ ≤
      (C : ℝ≥0∞) * ENNReal.ofReal r ^ (1 - (Module.finrank ℝ E : ℝ) / p.toReal) *
        eLpNorm (fun w => H w - H x) p (μ.restrict (ball x r)))
    (hx : Tendsto
      (fun r => (∫⁻ y in closedBall x r, ‖H y - H x‖ₑ ^ p.toReal ∂μ) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 0)) :
    HasFDerivAt V (H x) x := by
  set q := p.toReal with hq_def
  have hq : 0 < q := ENNReal.toReal_pos hp0 hpt
  set A : ℝ → ℝ≥0∞ := fun r =>
    (∫⁻ y in closedBall x r, ‖H y - H x‖ₑ ^ q ∂μ) / μ (closedBall x r) with hA
  set K : ℝ≥0∞ := (C : ℝ≥0∞) * μ (closedBall (0 : E) 1) ^ (1 / q)
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_closedBall_lt_top.ne)
  have hb' : ∀ r, 0 < r → r < δ → ∀ y ∈ ball x r,
      ‖V y - V x - H x (y - x)‖ₑ ≤ K * A r ^ (1 / q) * ENNReal.ofReal r := by
    intro r hr hrδ y hy
    refine (hb r hr hrδ y hy).trans ?_
    have hm0 : μ (closedBall x r) ≠ 0 := (measure_closedBall_pos μ x hr).ne'
    have hmt : μ (closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hR0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
    have hRt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
    have hL : eLpNorm (fun w => H w - H x) p (μ.restrict (ball x r)) ≤
        A r ^ (1 / q) * (ENNReal.ofReal r ^ ((Module.finrank ℝ E : ℝ) / q) *
          μ (closedBall (0 : E) 1) ^ (1 / q)) := by
      calc eLpNorm (fun w => H w - H x) p (μ.restrict (ball x r))
          ≤ eLpNorm (fun w => H w - H x) p (μ.restrict (closedBall x r)) :=
            eLpNorm_mono_measure _ (Measure.restrict_mono_set μ ball_subset_closedBall)
        _ = (A r * μ (closedBall x r)) ^ (1 / q) := by
            have hHm : AEStronglyMeasurable (fun w => H w - H x) (μ.restrict (closedBall x r)) :=
              (hH.sub aestronglyMeasurable_const).restrict
            rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hHm, hA,
              ENNReal.div_mul_cancel hm0 hmt]
        _ = _ := by
            rw [Measure.addHaar_closedBall' μ x hr.le, ENNReal.ofReal_pow hr.le,
              ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
              ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_natCast,
              ← ENNReal.rpow_mul, mul_one_div]
    calc (C : ℝ≥0∞) * ENNReal.ofReal r ^ (1 - (Module.finrank ℝ E : ℝ) / q) *
          eLpNorm (fun w => H w - H x) p (μ.restrict (ball x r))
        ≤ (C : ℝ≥0∞) * ENNReal.ofReal r ^ (1 - (Module.finrank ℝ E : ℝ) / q) *
          (A r ^ (1 / q) * (ENNReal.ofReal r ^ ((Module.finrank ℝ E : ℝ) / q) *
            μ (closedBall (0 : E) 1) ^ (1 / q))) := by gcongr
      _ = K * A r ^ (1 / q) * (ENNReal.ofReal r ^ (1 - (Module.finrank ℝ E : ℝ) / q) *
            ENNReal.ofReal r ^ ((Module.finrank ℝ E : ℝ) / q)) := by ring
      _ = K * A r ^ (1 / q) * ENNReal.ofReal r := by
            rw [← ENNReal.rpow_add _ _ hR0 hRt, sub_add_cancel, ENNReal.rpow_one]
  have hT : Tendsto (fun r => K * A r ^ (1 / q)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r => A r ^ (1 / q)) (𝓝[>] 0) (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto 0).comp hx
      rwa [ENNReal.zero_rpow_of_pos (by positivity)] at this
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hK)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hP : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi 0 ∧ r < δ ∧ K * A r ^ (1 / q) < ENNReal.ofReal (c / 2) :=
    eventually_mem_nhdsWithin.and (((eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds).and
      (hT.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.2 (half_pos hc)))))
  have h2 : Tendsto (fun h : E => 2 * ‖h‖) (𝓝[≠] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun h : E => 2 * ‖h‖) (𝓝 0) (𝓝 (2 * ‖(0 : E)‖)) :=
        (continuous_const.mul continuous_norm).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact mul_pos two_pos (norm_pos_iff.2 hh)
  filter_upwards [eventually_nhdsWithin_iff.1 (h2.eventually hP)] with h hh
  rcases eq_or_ne h 0 with rfl | h0
  · simp
  obtain ⟨hr0, hrδ, hlt⟩ := hh h0
  have hhpos : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hy : x + h ∈ ball x (2 * ‖h‖) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    linarith
  have hbd := hb' _ hr0 hrδ _ hy
  rw [add_sub_cancel_left] at hbd
  have h3 : ‖V (x + h) - V x - H x h‖ₑ ≤ ENNReal.ofReal (c * ‖h‖) := by
    calc ‖V (x + h) - V x - H x h‖ₑ ≤ K * A (2 * ‖h‖) ^ (1 / q) * ENNReal.ofReal (2 * ‖h‖) := hbd
      _ ≤ ENNReal.ofReal (c / 2) * ENNReal.ofReal (2 * ‖h‖) := by gcongr
      _ = ENNReal.ofReal (c * ‖h‖) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  rw [← ofReal_norm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

/-- The limit `V` of the gradients is Lipschitz in the mean with respect to `G`, and differentiable at
every strong `L^p` Lebesgue point `x` of `G`, with derivative `G x`, given Morrey's oscillation
estimate. -/
theorem hessianExpansion_of_morrey_gradientLimit
    (h3 : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
      (p : ℝ≥0∞), (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
      ∃ C : ℝ≥0, ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        (f : E → F) (a : E) (r : ℝ), 0 < r → ContDiffOn ℝ 1 f (ball a r) →
        ∀ z ∈ ball a r, ∀ z' ∈ ball a r,
          ‖f z - f z'‖ₑ ≤ (C : ℝ≥0∞) * ENNReal.ofReal r ^ (1 - (Module.finrank ℝ E : ℝ) / p.toReal) *
            eLpNorm (fderiv ℝ f) p (μ.restrict (ball a r))) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
      (p : ℝ≥0∞), (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
      ∃ C : ℝ≥0, ∀ (U : Set E) (u : E → ℝ) (uε : ℕ → E → ℝ) (ε : ℕ → ℝ)
        (G : E → E →L[ℝ] E →L[ℝ] ℝ), IsW2pApprox μ p U u uε ε G → ∀ V : E → E →L[ℝ] ℝ,
        (∀ K : Set E, IsCompact K → K ⊆ U →
          TendstoUniformlyOn (fun n => fderiv ℝ (uε n)) V atTop K) →
        (∀ (x : E) (r : ℝ), 0 < r → closedBall x r ⊆ U → ∀ y ∈ ball x r,
          ‖V y - V x - G x (y - x)‖ₑ ≤
            (C : ℝ≥0∞) * ENNReal.ofReal r ^ (1 - (Module.finrank ℝ E : ℝ) / p.toReal) *
              eLpNorm (fun w => G w - G x) p (μ.restrict (ball x r))) ∧
        (∀ x ∈ U, Tendsto
          (fun r => (∫⁻ y in closedBall x r, ‖G y - G x‖ₑ ^ p.toReal ∂μ) / μ (closedBall x r))
          (𝓝[>] 0) (𝓝 0) → HasFDerivAt V (G x) x) := by
  intro E _ _ _ _ _ _ μ _ p hdp hpt
  obtain ⟨C, hC⟩ := h3 E μ p hdp hpt
  have hp1 : 1 ≤ p := le_trans (by exact_mod_cast Module.finrank_pos) hdp.le
  have hp0 : p ≠ 0 := (lt_of_le_of_lt zero_le hdp).ne'
  refine ⟨C, fun U u uε ε G hW V hV => ?_⟩
  have hi : ∀ (x : E) (r : ℝ), 0 < r → closedBall x r ⊆ U → ∀ y ∈ ball x r,
      ‖V y - V x - G x (y - x)‖ₑ ≤
        (C : ℝ≥0∞) * ENNReal.ofReal r ^ (1 - (Module.finrank ℝ E : ℝ) / p.toReal) *
          eLpNorm (fun w => G w - G x) p (μ.restrict (ball x r)) :=
    fun x r hr hxr y hy => enorm_sub_sub_le_of_isW2pApprox hp1 hW hV hr hxr hy
      (ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.rpow_ne_top_of_nonneg' (ENNReal.ofReal_pos.2 hr) ENNReal.ofReal_ne_top))
      fun f hf => hC _ f x r hr hf y hy x (mem_ball_self hr)
  refine ⟨hi, fun x hx hL => ?_⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hW.1 x hx
  exact hasFDerivAt_of_enorm_sub_sub_le hW.2.2.2.2.2.1.aestronglyMeasurable hδ hp0 hpt
    (fun r hr hrδ y hy => hi x r hr ((closedBall_subset_ball hrδ).trans hδU) y hy) hL

end LatticeProb.PegdenSmart
