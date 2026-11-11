import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Super-mean-value inequality and minimum principles in the plane

The local defining inequality of superharmonic functions on an open subset of `ℂ`, in the sphere-average form of
Armitage and Gardiner, *Classical Potential Theory* (Springer, 2001), §3.1, and the strong and weak minimum
principles of §3.2. Further sources: Axler, Bourdon and Ramey, *Harmonic Function Theory*, 2nd ed., Theorem 11.2;
Doob, *Classical Potential Theory and Its Probabilistic Counterpart* (1984), Ch. II §5.
-/

open Metric Set Filter Topology MeasureTheory Real

namespace LatticeProb

/-- The super-mean-value inequality on `U`, the local defining property of a superharmonic function
(Armitage and Gardiner, *Classical Potential Theory*, §3.1): for every closed disc `closedBall c r ⊆ U` with
`0 < r`, the value `f c` dominates the average of `f` over the circle `sphere c r` with respect to normalized
arc length, that is, `Real.circleAverage f c r ≤ f c`. -/
def SuperMeanValueOn (f : ℂ → ℝ) (U : Set ℂ) : Prop :=
  ∀ c : ℂ, ∀ r : ℝ, 0 < r → closedBall c r ⊆ U → Real.circleAverage f c r ≤ f c

/-- A continuous, nonnegative, `2π`-periodic real function whose integral over one period vanishes is identically
zero (the mean-zero step of the minimum principle on a circle). -/
theorem eq_zero_of_periodic_of_nonneg_of_integral_eq_zero {h : ℝ → ℝ} (hc : Continuous h)
    (hp : Function.Periodic h (2 * π)) (hnn : ∀ θ, 0 ≤ h θ) (hint : ∫ θ in (0:ℝ)..2 * π, h θ = 0) (θ₀ : ℝ) :
    h θ₀ = 0 := by
  by_contra hne
  have hpos : 0 < h θ₀ := lt_of_le_of_ne (hnn θ₀) (Ne.symm hne)
  have hev : ∀ᶠ θ in 𝓝 θ₀, 0 < h θ := (hc.tendsto θ₀).eventually (lt_mem_nhds hpos)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨δ, hδpos, hδε, hδπ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ π :=
    ⟨min ε π, lt_min hε Real.pi_pos, min_le_left _ _, min_le_right _ _⟩
  have hsmall : ∀ θ ∈ Ioo (θ₀ - δ) (θ₀ + δ), 0 < h θ := by
    intro θ hθ
    apply hball
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [hθ.1, hθ.2]
  have hper : ∫ θ in (θ₀ - π)..(θ₀ - π) + 2 * π, h θ = ∫ θ in (0:ℝ)..0 + 2 * π, h θ :=
    hp.intervalIntegral_add_eq (θ₀ - π) 0
  have hend : θ₀ - π + 2 * π = θ₀ + π := by ring
  rw [hend, zero_add, hint] at hper
  have hmono : ∫ θ in (θ₀ - δ)..(θ₀ + δ), h θ ≤ ∫ θ in (θ₀ - π)..(θ₀ + π), h θ :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (MeasureTheory.ae_of_all _ fun θ => hnn θ) (hc.intervalIntegrable _ _)
  have hpos' : 0 < ∫ θ in (θ₀ - δ)..(θ₀ + δ), h θ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _) hsmall (by linarith)
  linarith

/-- Circle form of the mean-value rigidity: if `f` is continuous on the circle `sphere c r`, lies at least `m` there,
and has circle average at most `m`, then `f = m` on the whole circle. -/
theorem eq_of_mem_sphere_of_circleAverage_le {f : ℂ → ℝ} {c : ℂ} {r m : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (sphere c r)) (hge : ∀ z ∈ sphere c r, m ≤ f z)
    (havg : Real.circleAverage f c r ≤ m) {z : ℂ} (hz : z ∈ sphere c r) : f z = m := by
  have hcomp : Continuous fun θ : ℝ => f (circleMap c r θ) :=
    hf.comp_continuous (continuous_circleMap c r) fun θ => circleMap_mem_sphere c hr.le θ
  have hcont : Continuous fun θ : ℝ => f (circleMap c r θ) - m := hcomp.sub continuous_const
  have hper : Function.Periodic (fun θ : ℝ => f (circleMap c r θ) - m) (2 * π) := by
    intro θ
    simp only [periodic_circleMap c r θ]
  have hnn : ∀ θ : ℝ, 0 ≤ f (circleMap c r θ) - m := fun θ =>
    sub_nonneg.mpr (hge _ (circleMap_mem_sphere c hr.le θ))
  have h2π : (0:ℝ) < 2 * π := by positivity
  have hfi : IntervalIntegrable (fun θ : ℝ => f (circleMap c r θ)) volume 0 (2 * π) :=
    hcomp.intervalIntegrable _ _
  have hle : ∫ θ in (0:ℝ)..2 * π, (f (circleMap c r θ) - m) ≤ 0 := by
    have havg' := havg
    rw [Real.circleAverage_def, smul_eq_mul] at havg'
    have hmul := mul_le_mul_of_nonneg_left havg' h2π.le
    rw [mul_inv_cancel_left₀ h2π.ne'] at hmul
    rw [intervalIntegral.integral_sub hfi intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul, sub_zero]
    linarith
  have hcI : ∫ θ in (0:ℝ)..2 * π, (f (circleMap c r θ) - m) = 0 :=
    le_antisymm hle (intervalIntegral.integral_nonneg h2π.le fun θ _ => hnn θ)
  obtain ⟨θ, rfl⟩ : ∃ θ : ℝ, circleMap c r θ = z := by
    have hzr : z ∈ Set.range (circleMap c r) := by
      rw [range_circleMap, abs_of_pos hr]
      exact hz
    exact hzr
  have h0 := eq_zero_of_periodic_of_nonneg_of_integral_eq_zero hcont hper hnn hcI θ
  linarith

/-- Local rigidity of the super-mean-value inequality: if `f` is continuous and super-mean-value on the open set
`U`, `f ≥ m` on `U`, and `f x = m` at some `x ∈ U`, then `f = m` on a disc around `x`. -/
theorem exists_ball_eq_of_superMeanValueOn {f : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hsup : SuperMeanValueOn f U) {m : ℝ} (hge : ∀ z ∈ U, m ≤ f z) {x : ℂ} (hx : x ∈ U) (hxm : f x = m) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧ ∀ z ∈ ball x r, f z = m := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨r, hr, hrU, fun z hz => ?_⟩
  rcases eq_or_ne z x with rfl | hzx
  · exact hxm
  · have hρpos : 0 < dist z x := dist_pos.mpr hzx
    have hρr : dist z x < r := mem_ball.mp hz
    have hsub : closedBall x (dist z x) ⊆ U := fun w hw =>
      hrU (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hw) hρr))
    have havg : Real.circleAverage f x (dist z x) ≤ m := (hsup x (dist z x) hρpos hsub).trans hxm.le
    have hsphere : sphere x (dist z x) ⊆ U := sphere_subset_closedBall.trans hsub
    exact eq_of_mem_sphere_of_circleAverage_le hρpos (hf.mono hsphere) (fun w hw => hge w (hsphere hw)) havg
      (mem_sphere.mpr rfl)

/-- **Strong minimum principle** for superharmonic functions in the plane (Armitage and Gardiner, *Classical Potential
Theory*, §3.2; Axler, Bourdon and Ramey, Theorem 11.2, applied to `-f`). If `U` is open and connected, `f` is
continuous on `U` and super-mean-value on `U`, and `f` attains its infimum over `U` at `x₀ ∈ U`, then `f` is constant
on `U`. -/
theorem SuperMeanValueOn.strong_minimum_principle {f : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsConnected U) (hf : ContinuousOn f U) (hsup : SuperMeanValueOn f U) {x₀ : ℂ} (hx₀ : x₀ ∈ U)
    (hmin : ∀ x ∈ U, f x₀ ≤ f x) : ∀ x ∈ U, f x = f x₀ := by
  have hopen : IsOpen {x | x ∈ U ∧ f x = f x₀} := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hxU, hxm⟩
    obtain ⟨r, hr, hrU, hball⟩ := exists_ball_eq_of_superMeanValueOn hU hf hsup hmin hxU hxm
    exact ⟨r, hr, fun z hz => ⟨hrU hz, hball z hz⟩⟩
  have hclosed : closure {x | x ∈ U ∧ f x = f x₀} ∩ U ⊆ {x | x ∈ U ∧ f x = f x₀} := by
    rintro z ⟨hzc, hzU⟩
    refine ⟨hzU, ?_⟩
    have hSU : {x | x ∈ U ∧ f x = f x₀} ⊆ U := fun x hx => hx.1
    have hNB : NeBot (𝓝[{x | x ∈ U ∧ f x = f x₀}] z) := mem_closure_iff_nhdsWithin_neBot.mp hzc
    have h1 : Tendsto f (𝓝[{x | x ∈ U ∧ f x = f x₀}] z) (𝓝 (f z)) := (hf z hzU).mono hSU
    have hEq : (fun _ => f x₀) =ᶠ[𝓝[{x | x ∈ U ∧ f x = f x₀}] z] f :=
      eventually_nhdsWithin_of_forall fun w hw => hw.2.symm
    have h2 : Tendsto f (𝓝[{x | x ∈ U ∧ f x = f x₀}] z) (𝓝 (f x₀)) :=
      Filter.Tendsto.congr' hEq tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hsub := hconn.isPreconnected.subset_of_closure_inter_subset hopen ⟨x₀, hx₀, hx₀, rfl⟩ hclosed
  intro x hx
  exact (hsub hx).2

/-- **Strong minimum principle**, nonnegative form: if `f ≥ 0` on the open connected set `U`, `f` is continuous and
super-mean-value on `U`, and `f x₀ = 0` at some `x₀ ∈ U`, then `f = 0` on `U`. -/
theorem SuperMeanValueOn.strong_minimum_principle_of_nonneg {f : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsConnected U) (hf : ContinuousOn f U) (hsup : SuperMeanValueOn f U) (hnn : ∀ x ∈ U, 0 ≤ f x)
    {x₀ : ℂ} (hx₀ : x₀ ∈ U) (hzero : f x₀ = 0) : ∀ x ∈ U, f x = 0 := by
  intro x hx
  have hmin : ∀ y ∈ U, f x₀ ≤ f y := fun y hy => by rw [hzero]; exact hnn y hy
  have h := SuperMeanValueOn.strong_minimum_principle hU hconn hf hsup hx₀ hmin x hx
  rw [h, hzero]

/-- **Minimum principle with boundary data** for superharmonic functions in the plane (Armitage and Gardiner,
*Classical Potential Theory*, §3.2; Doob, *Classical Potential Theory and Its Probabilistic Counterpart*, Ch. II §5).
If `U` is open and bounded, `f` is continuous on `closure U` and super-mean-value on `U`, and `f ≥ 0` on the frontier
of `U`, then `f ≥ 0` on `U`. -/
theorem SuperMeanValueOn.minimum_principle_of_frontier {f : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hbdd : Bornology.IsBounded U) (hf : ContinuousOn f (closure U)) (hsup : SuperMeanValueOn f U)
    (hfr : ∀ x ∈ frontier U, 0 ≤ f x) : ∀ x ∈ U, 0 ≤ f x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀U, hx₀neg⟩ := hcon
  have hcpt : IsCompact (closure U) := hbdd.isCompact_closure
  obtain ⟨y, hyK, hymin⟩ := hcpt.exists_isMinOn ⟨x₀, subset_closure hx₀U⟩ hf
  have hmin : ∀ v ∈ closure U, f y ≤ f v := fun v hv => isMinOn_iff.mp hymin v hv
  have hmneg : f y < 0 := lt_of_le_of_lt (hmin x₀ (subset_closure hx₀U)) hx₀neg
  have hin : ∀ w ∈ closure U, f w = f y → w ∈ U := by
    intro w hw hwm
    by_contra hwU
    have hwfr : w ∈ frontier U := by
      rw [frontier, hU.interior_eq]
      exact ⟨hw, hwU⟩
    have := hfr w hwfr
    linarith
  have hmin' : ∀ z ∈ U, f y ≤ f z := fun z hz => hmin z (subset_closure hz)
  have hS'closed : IsClosed (closure U ∩ f ⁻¹' {f y}) :=
    hf.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
  have hS'open : IsOpen (closure U ∩ f ⁻¹' {f y}) := by
    rw [Metric.isOpen_iff]
    rintro w ⟨hwc, hwm⟩
    have hwm' : f w = f y := hwm
    have hwU : w ∈ U := hin w hwc hwm'
    obtain ⟨r, hr, hrU, hball⟩ :=
      exists_ball_eq_of_superMeanValueOn hU (hf.mono subset_closure) hsup hmin' hwU hwm'
    exact ⟨r, hr, fun z hz => ⟨subset_closure (hrU hz), hball z hz⟩⟩
  have hS'eq : closure U ∩ f ⁻¹' {f y} = univ :=
    IsClopen.eq_univ ⟨hS'closed, hS'open⟩ ⟨y, hyK, rfl⟩
  have hsubU : (univ : Set ℂ) ⊆ closure U := by
    rw [← hS'eq]
    exact inter_subset_left
  have hbdd_univ : Bornology.IsBounded (univ : Set ℂ) := hbdd.closure.subset hsubU
  exact (NormedSpace.unbounded_univ ℝ ℂ) hbdd_univ

end LatticeProb
