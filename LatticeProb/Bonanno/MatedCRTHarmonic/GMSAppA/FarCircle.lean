/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.FarCircle at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgIndep2

/-!
# Circle averages over an enclosing circle are independent of the field inside

For a whole-plane GFF `h` (any additive constant) and two nested closed disks `B̄_ρ(z) ⊆ B̄_r(w)`, the circle-average
increment `h_ρ(z) − h_r(w)` is independent of `(h − h_ρ(z))|_U` for every open `U ⊆ B̄_ρ(z)`.

This is the non-concentric form of LQGMetric's `CircleAvgIndep.indepFun_circleAvg_restrict` (concentric circles,
DFGPS T:2275–2276), with the same proof: the family `{h_ρ(z) − h_r(w)} ∪ {(h − h_ρ(z))(φ) : φ ∈ 𝓓(U)}` is an a.s.
limit of pairings of `h` with mean-zero test functions, hence a centred Gaussian process, and the cross-covariances
vanish because the logarithmic potential of `σ_{z,ρ} − σ_{w,r}` is the constant `log ρ − log r` on `B̄_ρ(z)`
(Newton's theorem `circLog w r u = log max(r, |w − u|)`, and `|w − u| ≤ r` on `B̄_ρ(z) ⊆ B̄_r(w)`).

It is the input of [18] (GMS, arXiv 1807.07511v3) Lemmas A.1 and A.2 (`GMSAppA.Lemma A1A2`): conditioning a whole-plane
GFF normalized by `h_1(0) = 0` on its average over a circle `∂B_R(w)` enclosing `𝔻̄` does not change the law of
`h|_𝔻` at all.

* `GMSAppA.tendsto_logCov_inside_nested` — Newton's theorem in the limit, nested circles.
* `GMSAppA.indepFun_circleAvg_restrict_nested` — the independence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open LQGMetric LQGMetric.CircleAvg LQGMetric.CircleAvgIndep

namespace MatedCRTHarmonic.GMSAppA

/-- **Newton's theorem in the limit, nested circles**: for `φ` vanishing off `B̄_ρ(z)` and `B̄_ρ(z) ⊆ B̄_r(w)`, the
`logCov` of `φ − (∫φ) Φ_n^{z,ρ}` against `Φ_n^{z,ρ} − Φ_n^{w,r}` tends to `0`. -/
theorem tendsto_logCov_inside_nested {z w : ℂ} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hnest : closedBall z ρ ⊆ closedBall w r) (φ : TestC) (hφ : ∀ x, ρ < ‖x - z‖ → φ x = 0) :
    Tendsto (fun n => logCov (fun x => φ x - (∫ y, φ y) * circBump n z ρ x)
      (circDiff n z ρ n w r).1) atTop (𝓝 0) := by
  set c := ∫ y, φ y
  set κ := Real.log ρ - Real.log r
  set f := circLogDiff hρ.ne' hr.ne' z w
  set e : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ n / ρ + (2 : ℝ)⁻¹ ^ n / r
  have hf : ∀ x, ‖x - z‖ ≤ ρ → f x = κ := by
    intro x hx
    have hxw : ‖w - x‖ ≤ r := by
      have := hnest (show x ∈ closedBall z ρ by rw [mem_closedBall, dist_eq_norm]; exact hx)
      rw [mem_closedBall, dist_eq_norm] at this
      rwa [norm_sub_rev]
    have hpl : ∀ (s : ℝ) (c' : ℂ), 0 < s → ‖c' - x‖ ≤ s → Real.posLog (s⁻¹ * ‖c' - x‖) = 0 := by
      intro s c' hs hcs
      rw [Real.posLog_eq_zero_iff, abs_of_nonneg (by positivity)]
      rw [inv_mul_le_iff₀ hs, mul_one]
      exact hcs
    show circLog z ρ x - circLog w r x = κ
    rw [circLog_eq hρ.ne', circLog_eq hr.ne', hpl ρ z hρ (by rwa [norm_sub_rev]), hpl r w hr hxw]
    ring
  have hφf : ∀ x, φ x * f x = φ x * κ := by
    intro x
    by_cases hx : ‖x - z‖ ≤ ρ
    · rw [hf x hx]
    · rw [hφ x (not_le.1 hx), zero_mul, zero_mul]
  have hψ : ∀ n x, |φ x - c * circBump n z ρ x| ≤ |φ x| + |c| * circBump n z ρ x := by
    intro n x
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_nonneg (circBump_nonneg _ _ _ _)]
  have hint_ψ : ∀ n, Integrable fun x => |φ x| + |c| * circBump n z ρ x := fun n =>
    (integrable_testC φ).abs.add ((integrable_testC _).const_mul _)
  have hdec : ∀ n, logCov (fun x => φ x - c * circBump n z ρ x) (circDiff n z ρ n w r).1 =
      (∫ x, (φ x - c * circBump n z ρ x) * (logPot (circDiff n z ρ n w r).1 x + f x)) -
        (c * κ - c * mollAvg (ofCont f) n z ρ) := by
    intro n
    set D := (circDiff n z ρ n w r).1
    have hψf : Integrable fun x => (φ x - c * circBump n z ρ x) * f x := by
      have : (fun x => (φ x - c * circBump n z ρ x) * f x) =
          fun x => φ x * f x - c * (circBump n z ρ x * f x) := by funext x; ring
      rw [this]
      exact (integrable_test_mul φ f).sub ((integrable_test_mul _ f).const_mul c)
    have hψe : Integrable fun x => (φ x - c * circBump n z ρ x) * (logPot D x + f x) := by
      refine Integrable.mono' ((hint_ψ n).mul_const (e n))
        (((integrable_testC φ).sub ((integrable_testC _).const_mul _)).aestronglyMeasurable.mul
          ((measurable_logPot D).add f.continuous.measurable).aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hψ n x) (abs_logPot_circDiff_add_le hρ hr n z w x) (abs_nonneg _)
        (by have := circBump_nonneg n z ρ x; positivity)
    rw [logCov_eq_integral_logPot]
    have e1 : (fun x => (φ x - c * circBump n z ρ x) * logPot D x) = fun x =>
        (φ x - c * circBump n z ρ x) * (logPot D x + f x) -
          (φ x - c * circBump n z ρ x) * f x := by funext x; ring
    rw [e1, integral_sub hψe hψf]
    congr 1
    have e2 : (fun x => (φ x - c * circBump n z ρ x) * f x) =
        fun x => φ x * κ - c * (circBump n z ρ x * f x) := by
      funext x; rw [sub_mul, hφf]; ring
    rw [e2, integral_sub ((integrable_testC φ).mul_const κ)
      ((integrable_test_mul _ f).const_mul c), integral_mul_const, integral_const_mul,
      integral_circBump_mul]
  have hκ : Real.circleAverage f z ρ = κ := by
    refine Real.circleAverage_const_on_circle fun x hx => hf x ?_
    rw [mem_sphere_iff_norm, abs_of_pos hρ] at hx
    exact hx.le
  have hlim2 : Tendsto (fun n => c * κ - c * mollAvg (ofCont f) n z ρ) atTop (𝓝 0) := by
    have := ((tendsto_mollAvg_ofCont f ρ z).const_mul c).const_sub (c * κ)
    rwa [hκ, sub_self] at this
  have he : Tendsto (fun n => (∫ x, |φ x|) * e n + |c| * e n) atTop (𝓝 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    have h2 : Tendsto e atTop (𝓝 0) := by
      simpa [e] using (h1.div_const ρ).add (h1.div_const r)
    simpa using (h2.const_mul (∫ x, |φ x|)).add (h2.const_mul |c|)
  have hlim1 : Tendsto (fun n => ∫ x, (φ x - c * circBump n z ρ x) *
      (logPot (circDiff n z ρ n w r).1 x + f x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) he
    have hb : ∀ x, ‖(φ x - c * circBump n z ρ x) * (logPot (circDiff n z ρ n w r).1 x + f x)‖ ≤
        (|φ x| + |c| * circBump n z ρ x) * e n := by
      intro x
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hψ n x) (abs_logPot_circDiff_add_le hρ hr n z w x) (abs_nonneg _)
        (by have := circBump_nonneg n z ρ x; positivity)
    refine (norm_integral_le_of_norm_le ((hint_ψ n).mul_const _)
      (Eventually.of_forall hb)).trans (le_of_eq ?_)
    rw [integral_mul_const, integral_add (integrable_testC φ).abs
      ((integrable_testC _).const_mul _), integral_const_mul, integral_circBump]
    ring
  simp_rw [hdec]
  simpa using hlim1.sub hlim2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- the approximating mean-zero test functions, nested circles -/
def testNested (z : ℂ) (ρ : ℝ) (w : ℂ) (r : ℝ) (U : Opens ℂ) (n : ℕ) : Unit ⊕ TestOn U → TestC0
  | Sum.inl _ => circDiff n z ρ n w r
  | Sum.inr φ => testN z ρ ρ U n (Sum.inr φ)

/-- the limit family: `h_ρ(z) − h_r(w)` and the pairings of `(h − h_ρ(z))|_U` -/
def incResNested (h : Ω → DistC) (z : ℂ) (ρ : ℝ) (w : ℂ) (r : ℝ) (U : Opens ℂ) :
    Unit ⊕ TestOn U → Ω → ℝ
  | Sum.inl _ => fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r w
  | Sum.inr φ => fun ω => restrictTo U (addConst (h ω) (-circleAvg (h ω) ρ z)) φ

/-- **Nested-circle independence**: for a whole-plane GFF `h`, `B̄_ρ(z) ⊆ B̄_r(w)` and open `U ⊆ B̄_ρ(z)`, the
increment `h_ρ(z) − h_r(w)` is independent of `(h − h_ρ(z))|_U`. -/
theorem indepFun_circleAvg_restrict_nested (hh : IsWholePlaneGFF h P) {z w : ℂ} {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hnest : closedBall z ρ ⊆ closedBall w r) (U : Opens ℂ)
    (hU : (U : Set ℂ) ⊆ closedBall z ρ) :
    IndepFun (fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r w)
      (fun ω => restrictTo U (addConst (h ω) (-circleAvg (h ω) ρ z))) P := by
  have := hh.gaussian.isProbabilityMeasure
  set Zn : ℕ → Unit ⊕ TestOn U → Ω → ℝ := fun n i ω => h ω (testNested z ρ w r U n i).1
  have hG : ∀ n, IsGaussianProcess (Zn n) P := fun n =>
    hh.gaussian.comp_right (testNested z ρ w r U n)
  have hc : ∀ n i, P[Zn n i] = 0 := fun n i => hh.centered _
  have hm : ∀ i, Measurable (incResNested h z ρ w r U i) := by
    rintro (_ | φ)
    · exact CircleAvg.measurable_cInc hh ρ z r w
    · have e : incResNested h z ρ w r U (Sum.inr φ) = fun ω =>
          h ω (GM.testIncl U ⊤ φ) + (∫ y, GM.testIncl U ⊤ φ y) * (-circleAvg (h ω) ρ z) :=
        funext fun ω => incRes_inr (h := h) z ρ ρ U φ ω
      rw [e]
      exact ((measurable_distOn_apply _).comp hh.measurable).add
        ((((measurable_circleAvg_left ρ z).comp hh.measurable).neg).const_mul _)
  have hlim : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => Zn n i ω) atTop
      (𝓝 (incResNested h z ρ w r U i ω)) := by
    rintro (_ | φ)
    · filter_upwards [CircleAvg.ae_tendsto_mInc hh hρ hr z w] with ω hω
      refine hω.congr fun n => ?_
      simp only [Zn, testNested, CircleAvg.mInc]
      exact mollAvg_sub_eq _ _ _ _ _ _ _
    · filter_upwards [ae_tendsto_mollAvg hh z hρ] with ω ⟨a, ha⟩
      have e0 : incResNested h z ρ w r U (Sum.inr φ) ω =
          h ω (GM.testIncl U ⊤ φ) + (∫ y, GM.testIncl U ⊤ φ y) * (-circleAvg (h ω) ρ z) :=
        incRes_inr (h := h) z ρ ρ U φ ω
      rw [e0, circleAvg_eq_of_tendsto ha]
      have e : ∀ n, Zn n (Sum.inr φ) ω =
          h ω (GM.testIncl U ⊤ φ) - (∫ y, GM.testIncl U ⊤ φ y) * mollAvg (h ω) n z ρ := by
        intro n
        simp only [Zn, testNested, testN, map_sub, map_smul, smul_eq_mul, mollAvg_eq]
      simp_rw [e]
      have := (ha.const_mul (∫ y, GM.testIncl U ⊤ φ y)).const_sub (h ω (GM.testIncl U ⊤ φ))
      convert this using 2
      ring
  have hGP : IsGaussianProcess (incResNested h z ρ w r U) P :=
    isGaussianProcess_of_ae_tendsto hG hc hm hlim
  have hcov : ∀ φ : TestOn U,
      cov[incResNested h z ρ w r U (Sum.inl ()), incResNested h z ρ w r U (Sum.inr φ); P] = 0 := by
    intro φ
    have h1 := tendsto_covariance_of_ae_tendsto hG hc hm hlim (Sum.inl ()) (Sum.inr φ)
    have h2 : Tendsto (fun n => cov[Zn n (Sum.inl ()), Zn n (Sum.inr φ); P]) atTop (𝓝 0) := by
      have hφ : ∀ x, ρ < ‖x - z‖ → (GM.testIncl U ⊤ φ : TestC) x = 0 := by
        intro x hx
        rw [coe_testIncl_top]
        refine φ.zero_on_compl fun hxU => ?_
        have := hU hxU
        rw [mem_closedBall, dist_eq_norm] at this
        linarith
      refine (tendsto_logCov_inside_nested hρ hr hnest _ hφ).congr fun n => ?_
      rw [covariance_comm]
      simp only [Zn]
      rw [hh.covariance_eq]
      congr 1
    exact tendsto_nhds_unique h1 h2
  have hGP' : IsGaussianProcess (Sum.elim (fun (_ : Unit) => incResNested h z ρ w r U (Sum.inl ()))
      (fun φ : TestOn U => incResNested h z ρ w r U (Sum.inr φ))) P := by
    convert hGP using 1
    funext i
    rcases i with (_ | φ) <;> rfl
  have H := hGP'.indepFun_of_covariance_eq_zero (fun _ => (hm _).aemeasurable)
    (fun φ => (hm _).aemeasurable) fun _ φ => hcov φ
  have H' := H.comp (measurable_pi_apply ()) measurable_id
  rw [IndepFun_iff_Indep] at H' ⊢
  have e2 : MeasurableSpace.comap (fun ω => restrictTo U (addConst (h ω) (-circleAvg (h ω) ρ z)))
      inferInstance = MeasurableSpace.comap
        (id ∘ fun ω (t : TestOn U) => incResNested h z ρ w r U (Sum.inr t) ω)
          MeasurableSpace.pi := by
    show MeasurableSpace.comap _ (MeasurableSpace.comap _ MeasurableSpace.pi) = _
    rw [MeasurableSpace.comap_comp]
    rfl
  rw [e2]
  exact H'

end MatedCRTHarmonic.GMSAppA
