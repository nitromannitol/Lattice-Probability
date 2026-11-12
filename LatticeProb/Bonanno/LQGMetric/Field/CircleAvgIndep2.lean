/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgIndep2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgIndep
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepZB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `h_ρ(z) − h_r(z)` is independent of `(h − h_ρ(z))|_{B_ρ(z)}` (task P2-DFA7b)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, T:2275–2276, proof of Lemma 3.19):
"`h_{2ε𝕣}(z) − h_𝕣(z)` is centered Gaussian of variance `log ε⁻¹ − log 2` and is independent from
`(h − h_{2ε𝕣}(z))|_{B_{2ε𝕣}(z)}`." This is the standard consequence of the Markov property /
the covariance structure of the whole-plane GFF (Duplantier–Sheffield arXiv:0808.1560 §3.1).

Proof (as in the handoff `handoff/P2-DFA7.md`, step 1): the family
`{h_ρ(z) − h_r(z)} ∪ {(h − h_ρ(z))(φ) : φ ∈ 𝓓(U)}`, `U ⊆ B̄_ρ(z)`, is the a.s. limit of the
pairings of `h` with the mean-zero test functions `circDiff n z ρ n z r` and
`φ − (∫φ) circBump n z ρ`, hence a centred Gaussian process (`CircleAvgIndep`), and its
cross-covariances are limits of `logCov`, which vanish in the limit because the logarithmic
potential of `σ_{z,ρ} − σ_{z,r}` is the constant `log ρ − log r` on `B̄_ρ(z)` (Newton's theorem:
`circLog z s u = log max(s, |z − u|)`, `CircleAvg.circLog_eq`). Zero covariance gives
independence (mathlib `IsGaussianProcess.indepFun_of_covariance_eq_zero`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace

namespace LQGMetric
namespace CircleAvgIndep

open CircleAvg

/-- **Newton's theorem in the limit**: for `φ` vanishing off `B̄_ρ(z)`, `ρ ≤ r`, the
`logCov` of `φ − (∫φ) Φ_n^{z,ρ}` against `Φ_n^{z,ρ} − Φ_n^{z,r}` tends to `0`. -/
theorem tendsto_logCov_inside {z : ℂ} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (φ : TestC)
    (hφ : ∀ x, ρ < ‖x - z‖ → φ x = 0) :
    Tendsto (fun n => logCov (fun x => φ x - (∫ y, φ y) * circBump n z ρ x)
      (circDiff n z ρ n z r).1) atTop (𝓝 0) := by
  have hr : 0 < r := hρ.trans_le hρr
  set c := ∫ y, φ y
  set κ := Real.log ρ - Real.log r
  set f := circLogDiff hρ.ne' hr.ne' z z
  set e : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ n / ρ + (2 : ℝ)⁻¹ ^ n / r
  have hf : ∀ x, ‖x - z‖ ≤ ρ → f x = κ := by
    intro x hx
    have hpl : ∀ s : ℝ, 0 < s → ρ ≤ s → Real.posLog (s⁻¹ * ‖z - x‖) = 0 := by
      intro s hs hρs
      rw [Real.posLog_eq_zero_iff, abs_of_nonneg (by positivity), norm_sub_rev]
      rw [inv_mul_le_iff₀ hs, mul_one]
      exact hx.trans hρs
    show circLog z ρ x - circLog z r x = κ
    rw [circLog_eq hρ.ne', circLog_eq hr.ne', hpl ρ hρ le_rfl, hpl r hr hρr]
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
  have hdec : ∀ n, logCov (fun x => φ x - c * circBump n z ρ x) (circDiff n z ρ n z r).1 =
      (∫ x, (φ x - c * circBump n z ρ x) * (logPot (circDiff n z ρ n z r).1 x + f x)) -
        (c * κ - c * mollAvg (ofCont f) n z ρ) := by
    intro n
    set D := (circDiff n z ρ n z r).1
    have hψi : Integrable fun x => φ x - c * circBump n z ρ x :=
      (integrable_testC φ).sub ((integrable_testC _).const_mul _)
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
      exact mul_le_mul (hψ n x) (abs_logPot_circDiff_add_le hρ hr n z z x) (abs_nonneg _)
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
      (logPot (circDiff n z ρ n z r).1 x + f x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) he
    have hb : ∀ x, ‖(φ x - c * circBump n z ρ x) * (logPot (circDiff n z ρ n z r).1 x + f x)‖ ≤
        (|φ x| + |c| * circBump n z ρ x) * e n := by
      intro x
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hψ n x) (abs_logPot_circDiff_add_le hρ hr n z z x) (abs_nonneg _)
        (by have := circBump_nonneg n z ρ x; positivity)
    refine (norm_integral_le_of_norm_le ((hint_ψ n).mul_const _)
      (Eventually.of_forall hb)).trans (le_of_eq ?_)
    rw [integral_mul_const, integral_add (integrable_testC φ).abs
      ((integrable_testC _).const_mul _), integral_const_mul, integral_circBump]
    ring
  simp_rw [hdec]
  simpa using hlim1.sub hlim2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

lemma coe_testIncl_top (U : Opens ℂ) (φ : TestOn U) : ((GM.testIncl U ⊤ φ : TestC) : ℂ → ℝ) = φ :=
  GM.coe_testIncl le_top φ

/-- the approximating mean-zero test functions -/
def testN (z : ℂ) (ρ r : ℝ) (U : Opens ℂ) (n : ℕ) : Unit ⊕ TestOn U → TestC0
  | Sum.inl _ => circDiff n z ρ n z r
  | Sum.inr φ => ⟨GM.testIncl U ⊤ φ - (∫ y, GM.testIncl U ⊤ φ y) • circBump n z ρ, by
      have e : ⇑(GM.testIncl U ⊤ φ - (∫ y, GM.testIncl U ⊤ φ y) • circBump n z ρ) =
          fun x => GM.testIncl U ⊤ φ x - (∫ y, GM.testIncl U ⊤ φ y) * circBump n z ρ x := by
        ext x; simp
      rw [e, integral_sub (integrable_testC _) ((integrable_testC _).const_mul _),
        integral_const_mul, integral_circBump, mul_one, sub_self]⟩

/-- the limit family: `h_ρ(z) − h_r(z)` and the pairings of `(h − h_ρ(z))|_U` -/
def incRes (h : Ω → DistC) (z : ℂ) (ρ r : ℝ) (U : Opens ℂ) : Unit ⊕ TestOn U → Ω → ℝ
  | Sum.inl _ => fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z
  | Sum.inr φ => fun ω => restrictTo U (addConst (h ω) (-circleAvg (h ω) ρ z)) φ

omit [MeasurableSpace Ω] in
lemma incRes_inr (z : ℂ) (ρ r : ℝ) (U : Opens ℂ) (φ : TestOn U) (ω : Ω) :
    incRes h z ρ r U (Sum.inr φ) ω =
      h ω (GM.testIncl U ⊤ φ) + (∫ y, GM.testIncl U ⊤ φ y) * (-circleAvg (h ω) ρ z) :=
  GFFInv.addConst_apply _ _ _

/-- **`h_ρ(z) − h_r(z)` is independent of `(h − h_ρ(z))|_U` for open `U ⊆ B̄_ρ(z)`, `ρ ≤ r`**
(DFGPS T:2275–2276). -/
theorem indepFun_circleAvg_restrict (hh : IsWholePlaneGFF h P) (z : ℂ) {ρ r : ℝ} (hρ : 0 < ρ)
    (hρr : ρ ≤ r) (U : Opens ℂ) (hU : (U : Set ℂ) ⊆ closedBall z ρ) :
    IndepFun (fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z)
      (fun ω => restrictTo U (addConst (h ω) (-circleAvg (h ω) ρ z))) P := by
  have := hh.gaussian.isProbabilityMeasure
  have hr : 0 < r := hρ.trans_le hρr
  set Zn : ℕ → Unit ⊕ TestOn U → Ω → ℝ := fun n i ω => h ω (testN z ρ r U n i).1
  have hG : ∀ n, IsGaussianProcess (Zn n) P := fun n => hh.gaussian.comp_right (testN z ρ r U n)
  have hc : ∀ n i, P[Zn n i] = 0 := fun n i => hh.centered _
  have hm : ∀ i, Measurable (incRes h z ρ r U i) := by
    rintro (_ | φ)
    · exact CircleAvg.measurable_cInc hh ρ z r z
    · have e : incRes h z ρ r U (Sum.inr φ) = fun ω =>
          h ω (GM.testIncl U ⊤ φ) + (∫ y, GM.testIncl U ⊤ φ y) * (-circleAvg (h ω) ρ z) :=
        funext fun ω => incRes_inr z ρ r U φ ω
      rw [e]
      exact ((measurable_distOn_apply _).comp hh.measurable).add
        ((((measurable_circleAvg_left ρ z).comp hh.measurable).neg).const_mul _)
  have hlim : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => Zn n i ω) atTop (𝓝 (incRes h z ρ r U i ω)) := by
    rintro (_ | φ)
    · filter_upwards [CircleAvg.ae_tendsto_mInc hh hρ hr z z] with ω hω
      refine hω.congr fun n => ?_
      simp only [Zn, testN, CircleAvg.mInc]
      exact mollAvg_sub_eq _ _ _ _ _ _ _
    · filter_upwards [ae_tendsto_mollAvg hh z hρ] with ω ⟨a, ha⟩
      rw [incRes_inr, circleAvg_eq_of_tendsto ha]
      have e : ∀ n, Zn n (Sum.inr φ) ω =
          h ω (GM.testIncl U ⊤ φ) - (∫ y, GM.testIncl U ⊤ φ y) * mollAvg (h ω) n z ρ := by
        intro n
        simp only [Zn, testN, map_sub, map_smul, smul_eq_mul, mollAvg_eq]
      simp_rw [e]
      have := (ha.const_mul (∫ y, GM.testIncl U ⊤ φ y)).const_sub (h ω (GM.testIncl U ⊤ φ))
      convert this using 2
      ring
  have hGP : IsGaussianProcess (incRes h z ρ r U) P :=
    isGaussianProcess_of_ae_tendsto hG hc hm hlim
  have hcov : ∀ φ : TestOn U,
      cov[incRes h z ρ r U (Sum.inl ()), incRes h z ρ r U (Sum.inr φ); P] = 0 := by
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
      refine (tendsto_logCov_inside hρ hρr _ hφ).congr fun n => ?_
      rw [covariance_comm]
      simp only [Zn]
      rw [hh.covariance_eq]
      congr 1
    exact tendsto_nhds_unique h1 h2
  have hGP' : IsGaussianProcess (Sum.elim (fun (_ : Unit) => incRes h z ρ r U (Sum.inl ()))
      (fun φ : TestOn U => incRes h z ρ r U (Sum.inr φ))) P := by
    convert hGP using 1
    funext i
    rcases i with (_ | φ) <;> rfl
  have H := hGP'.indepFun_of_covariance_eq_zero (fun _ => (hm _).aemeasurable)
    (fun φ => (hm _).aemeasurable) fun _ φ => hcov φ
  have H' := H.comp (measurable_pi_apply ()) measurable_id
  rw [IndepFun_iff_Indep] at H' ⊢
  have e2 : MeasurableSpace.comap (fun ω => restrictTo U (addConst (h ω) (-circleAvg (h ω) ρ z)))
      inferInstance = MeasurableSpace.comap
        (id ∘ fun ω (t : TestOn U) => incRes h z ρ r U (Sum.inr t) ω) MeasurableSpace.pi := by
    show MeasurableSpace.comap _ (MeasurableSpace.comap _ MeasurableSpace.pi) = _
    rw [MeasurableSpace.comap_comp]
    rfl
  rw [e2]
  exact H'

end CircleAvgIndep
end LQGMetric
