import LatticeProb.Bonanno.LQGMetric.Field.CirclePairing

/-!
# Mollified circle measures: differences, radial integrands and measurable modifications

Facts about the test functions `TestC` and the mollified uniform measures `circBump k z r` on circles:

* pointwise and functional identities for differences of test functions;
* `circBump k z r` vanishes on a neighbourhood of the origin
  when the origin is at distance more than `2^{-k}` from the circle `∂B_r(z)`,
  and its support lies in the closed ball `B̄(z, r + 2^{-k})`;
* the integral of a difference of mollified circle measures vanishes;
* integrability and integral identities for radial integrands `x ↦ R x` that are continuous away from the origin;
* the radii `ρ (1 - 2^{-(n+1)})` increase to `ρ` and stay in `(0, ρ)`;
* an almost-everywhere limit of `m`-measurable random variables agrees almost everywhere with an `m`-measurable one.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real ENNReal

open LQGMetric LQGMetric.CircleAvg

namespace LatticeProb
namespace CirclePairing

/-! ### Differences of test functions -/

/-- The value of a difference of test functions is the difference of the values. -/
lemma coe_sub_apply (a b : TestC) (y : ℂ) : (a - b : TestC) y = a y - b y := rfl

/-- The underlying function of a difference of test functions is the difference of the underlying functions. -/
lemma coe_sub_fun (a b : TestC) : ((a - b : TestC) : ℂ → ℝ) = ⇑a - ⇑b :=
  funext (coe_sub_apply a b)

/-! ### Mollified circle measures -/

/-- `circBump k z r` vanishes on a neighbourhood of `0` when `2^{-k} < |‖z‖ - r|`. -/
lemma circBump_eventuallyEq_zero {k : ℕ} {z : ℂ} {r : ℝ} (hr : 0 < r) (hk : (2 : ℝ)⁻¹ ^ k < |‖z‖ - r|) :
    (circBump k z r : ℂ → ℝ) =ᶠ[𝓝 0] 0 := by
  have hopen : IsOpen {w : ℂ | (2 : ℝ)⁻¹ ^ k < |‖w - z‖ - r|} :=
    isOpen_lt continuous_const (by fun_prop)
  have h0 : (0 : ℂ) ∈ {w : ℂ | (2 : ℝ)⁻¹ ^ k < |‖w - z‖ - r|} := by
    show (2 : ℝ)⁻¹ ^ k < |‖0 - z‖ - r|
    rwa [zero_sub, norm_neg]
  filter_upwards [hopen.mem_nhds h0] with w hw
  have hw' : (2 : ℝ)⁻¹ ^ k < |‖w - z‖ - r| := hw
  refine circBump_eq_zero_of_forall_le hr fun c hc => ?_
  have h1 := abs_dist_sub_le w c z
  rw [mem_sphere] at hc
  rw [hc, dist_eq_norm w z] at h1
  exact hw'.le.trans h1

/-- The support of `circBump k z r` lies in the closed ball of radius `r + 2^{-k}` about `z`. -/
lemma tsupport_circBump_subset_closedBall {k : ℕ} {z : ℂ} {r : ℝ} (hr : 0 < r) :
    tsupport (circBump k z r : ℂ → ℝ) ⊆ closedBall z (r + (2 : ℝ)⁻¹ ^ k) := by
  refine closure_minimal (fun w hw => ?_) isClosed_closedBall
  by_contra hwb
  apply hw
  refine circBump_eq_zero_of_forall_le hr fun c hc => ?_
  rw [mem_closedBall, not_le] at hwb
  rw [mem_sphere] at hc
  have := dist_triangle w c z
  linarith

/-- The difference of two mollified circle measures integrates to zero. -/
lemma integral_circBump_sub (k : ℕ) (x y : ℂ) (ε s : ℝ) :
    ∫ w, (circBump k x ε - circBump k y s : TestC) w = 0 := by
  simp only [coe_sub_apply]
  rw [integral_sub (integrable_testC _) (integrable_testC _), integral_circBump, integral_circBump, sub_self]

/-! ### Radial integrands -/

/-- The composition `x ↦ f ‖x‖ 0` is continuous on `ℂ ∖ {0}` when `f` is jointly continuous on `(0, ∞) × ℂ`. -/
lemma continuousOn_radial_ne {f : ℝ → ℂ → ℝ} (h : ContinuousOn (fun p : ℝ × ℂ => f p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun x : ℂ => f ‖x‖ 0) {x | x ≠ 0} :=
  h.comp (continuous_norm.continuousOn.prodMk continuousOn_const) fun _ hx =>
    Set.mk_mem_prod (norm_pos_iff.2 hx) (mem_univ _)

/-- A test function vanishing near `0` times a radial integrand continuous away from `0` is integrable. -/
lemma integrable_mul_radial {R : ℂ → ℝ} (hR : ContinuousOn R {x | x ≠ 0}) (a : TestC)
    (ha : (a : ℂ → ℝ) =ᶠ[𝓝 0] 0) : Integrable fun x => a x * R x := by
  refine Continuous.integrable_of_hasCompactSupport ?_ a.hasCompactSupport.mul_right
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x = 0
  · subst hx
    have h0 : (fun y => a y * R y) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [ha] with y hy
      simp [hy]
    exact (continuousAt_congr h0).2 continuousAt_const
  · exact a.continuous.continuousAt.mul (hR.continuousAt (isOpen_ne.mem_nhds hx))

/-- The integral of a radial integrand against a difference of two test functions vanishing near `0`
is the difference of the integrals. -/
lemma integral_sub_mul_radial {R : ℂ → ℝ} (hR : ContinuousOn R {x | x ≠ 0}) {a b : TestC}
    (ha : (a : ℂ → ℝ) =ᶠ[𝓝 0] 0) (hb : (b : ℂ → ℝ) =ᶠ[𝓝 0] 0) :
    ∫ x, (a - b : TestC) x * R x = (∫ x, a x * R x) - ∫ x, b x * R x := by
  rw [← integral_sub (integrable_mul_radial hR a ha) (integrable_mul_radial hR b hb)]
  congr 1
  funext x
  rw [coe_sub_apply]
  ring

/-! ### Radii and measurable modifications -/

/-- The radii `ρ (1 - 2^{-(n+1)})` tend to `ρ`. -/
lemma tendsto_radius (ρ : ℝ) : Tendsto (fun n : ℕ => ρ * (1 - (2 : ℝ)⁻¹ ^ (n + 1))) atTop (𝓝 ρ) := by
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hpow
  rw [sub_zero] at h
  simpa using h.const_mul ρ

/-- The radii `ρ (1 - 2^{-(n+1)})` lie in `(0, ρ)` for `ρ > 0`. -/
lemma radius_pos_lt {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    0 < ρ * (1 - (2 : ℝ)⁻¹ ^ (n + 1)) ∧ ρ * (1 - (2 : ℝ)⁻¹ ^ (n + 1)) < ρ := by
  have hq : 0 < (2 : ℝ)⁻¹ ^ (n + 1) := by positivity
  have hq1 : (2 : ℝ)⁻¹ ^ (n + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  exact ⟨mul_pos hρ (by linarith), mul_lt_of_lt_one_right hρ (by linarith)⟩

/-- An almost-everywhere limit of `m`-measurable real random variables is almost everywhere equal to an
`m`-measurable one. -/
lemma exists_measurable_ae_eq_of_ae_tendsto {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (m : MeasurableSpace Ω) {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ k, Measurable[m] (f k)) (hfg : ∀ᵐ ω ∂P, Tendsto (fun k => f k ω) atTop (𝓝 (g ω))) :
    ∃ D : Ω → ℝ, Measurable[m] D ∧ g =ᵐ[P] D := by
  refine ⟨fun ω => limsup (fun k => f k ω) atTop, ?_, ?_⟩
  · let _ : MeasurableSpace Ω := m
    exact Measurable.limsup hf
  · filter_upwards [hfg] with ω h
    exact h.limsup_eq.symm

end CirclePairing
end LatticeProb
