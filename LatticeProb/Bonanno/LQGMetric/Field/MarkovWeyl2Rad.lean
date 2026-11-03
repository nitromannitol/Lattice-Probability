/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovWeyl2Rad at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeyl2Pot
import LatticeProb.Bonanno.LQGMetric.Field.MarkovHarm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Weakly harmonic distributions do not see the shape of radial mollifiers (task P2-MKH)

For a distribution `T` on `V` with `T(−Δf/2π) = 0` for all `f ∈ C_c^∞(V)`, and radial test
functions `ρ₁, ρ₂` vanishing off `B̄(0, r)` with `∫ρ₁ = ∫ρ₂`, `T(ρ₁(· − c)) = T(ρ₂(· − c))`
whenever `B̄(c, r) ⊆ V` (`pair_eq_of_radial`): `ρ₁ − ρ₂ = −Δf/2π` with `f ∈ C_c^∞(B̄(0, r))`
(`exists_poisson_radial`). This is the radial step of the mollification proof of Weyl's lemma
(Hörmander, *ALPDO I*, Thm 4.4.1). We fix the radial mollifiers
`rbump r = c_r · exp(−1/(r² − |y|²))₊` (mathlib `ContDiffBump` is not provably radial) and define
`weylFun T z = T(rbump s (· − z))` (independent of `s` with `B̄(z, s) ⊆ V`, `weylFun_eq`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric Laplacian InnerProductSpace TopologicalSpace
open scoped Real

namespace LQGMetric
namespace MarkovWeyl2

/-- rotation invariance -/
def IsRad (ρ : ℂ → ℝ) : Prop := ∀ (a : Circle) (y : ℂ), ρ (a * y) = ρ y

/-- a smooth function vanishing off `B̄(c, r) ⊆ V` as a test function on `V` -/
def ofBall {V : Opens ℂ} {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) {c : ℂ} {r : ℝ}
    (hs : ∀ x, r < ‖x - c‖ → ψ x = 0) (hV : closedBall c r ⊆ V) : TestOn V where
  toFun := ψ
  contDiff' := hψ
  hasCompactSupport' := HasCompactSupport.intro (isCompact_closedBall c r) fun x hx =>
    hs x (by simpa [mem_closedBall, dist_eq_norm] using hx)
  tsupport_subset' := (closure_minimal (fun x hx => by
    by_contra h
    exact hx (hs x (by simpa [mem_closedBall, dist_eq_norm] using h))) isClosed_closedBall).trans hV

@[simp] lemma ofBall_apply {V : Opens ℂ} {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    {c : ℂ} {r : ℝ} (hs : ∀ x, r < ‖x - c‖ → ψ x = 0) (hV : closedBall c r ⊆ V) (x : ℂ) :
    ofBall hψ hs hV x = ψ x := rfl

lemma laplacian_comp_sub (f : ℂ → ℝ) (c x : ℂ) : Δ (fun y => f (y - c)) x = Δ f (x - c) := by
  have e : (fun y => f (y - c)) = fun y => f (y + -c) := by funext y; rw [sub_eq_add_neg]
  rw [e, laplacian_eq_iteratedFDeriv_complexPlane, laplacian_eq_iteratedFDeriv_complexPlane]
  beta_reduce
  rw [iteratedFDeriv_comp_add_right, sub_eq_add_neg]

lemma integrable_of_vanish {ρ : ℂ → ℝ} (hρ : Continuous ρ) {r : ℝ}
    (hs : ∀ y, r < ‖y‖ → ρ y = 0) : Integrable ρ :=
  hρ.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall 0 r)
    fun x hx => hs x (by simpa [mem_closedBall, dist_zero_right] using hx))

/-- **Weakly harmonic distributions agree on radial test functions of equal mass.** -/
theorem pair_eq_of_radial {V : Opens ℂ} (T : DistOn V)
    (hT : ∀ f : MarkovZB.zsSub (V : Set ℂ), T (MarkovHarm.cmTestOn f) = 0)
    {ρ₁ ρ₂ : ℂ → ℝ} (h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ₁)
    (h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ₂) (hr1 : IsRad ρ₁) (hr2 : IsRad ρ₂) {r : ℝ}
    (hs1 : ∀ y, r < ‖y‖ → ρ₁ y = 0) (hs2 : ∀ y, r < ‖y‖ → ρ₂ y = 0)
    (hint : ∫ y, ρ₁ y = ∫ y, ρ₂ y) {c : ℂ} (hV : closedBall c r ⊆ V) {φ₁ φ₂ : TestOn V}
    (hφ1 : ∀ x, φ₁ x = ρ₁ (x - c)) (hφ2 : ∀ x, φ₂ x = ρ₂ (x - c)) : T φ₁ = T φ₂ := by
  obtain ⟨f, hf, hfs, hΔ⟩ := exists_poisson_radial (σ := fun y => ρ₁ y - ρ₂ y) (h1.sub h2)
    (fun a y => by simp only [hr1 a y, hr2 a y]) (fun y hy => by simp [hs1 y hy, hs2 y hy])
    (by rw [integral_sub (integrable_of_vanish h1.continuous hs1)
      (integrable_of_vanish h2.continuous hs2), hint, sub_self])
  have hFc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => f (x - c)) :=
    hf.comp (contDiff_id.sub contDiff_const)
  set φF := ofBall hFc (fun x hx => hfs _ hx) hV
  have hF : (fun x => f (x - c)) ∈ QuantumZipper.zeroSpace (V : Set ℂ) :=
    ⟨φF.contDiff, φF.hasCompactSupport, φF.tsupport_subset⟩
  have key : MarkovHarm.cmTestOn (⟨_, hF⟩ : MarkovZB.zsSub (V : Set ℂ)) = φ₁ - φ₂ := by
    refine TestFunction.ext fun x => ?_
    rw [MarkovHarm.cmTestOn_apply, cmTest_apply]
    show -(2 * π)⁻¹ * Δ (fun x => f (x - c)) x = φ₁ x - φ₂ x
    rw [laplacian_comp_sub, hΔ, hφ1, hφ2]
  have := hT ⟨_, hF⟩
  rwa [key, map_sub, sub_eq_zero] at this

/-! ## Radial mollifiers -/

/-- unnormalized radial bump `exp(−1/(r² − |y|²))₊` -/
def rbump0 (r : ℝ) (y : ℂ) : ℝ := expNegInvGlue (r ^ 2 - ‖y‖ ^ 2)

lemma contDiff_rbump0 (r : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rbump0 r) :=
  (expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_const.sub (contDiff_norm_sq ℝ))

lemma rbump0_eq_zero {r : ℝ} (hr : 0 ≤ r) {y : ℂ} (hy : r < ‖y‖) : rbump0 r y = 0 :=
  expNegInvGlue.zero_of_nonpos (by nlinarith [norm_nonneg y])

lemma integral_rbump0_pos {r : ℝ} (hr : 0 < r) : 0 < ∫ y, rbump0 r y := by
  refine QuantumZipper.K3.integral_pos_of_pos_on_ball (contDiff_rbump0 r).continuous
    (HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) r) fun x hx => rbump0_eq_zero hr.le
      (by simpa [mem_closedBall, dist_zero_right] using hx))
    (fun x => expNegInvGlue.nonneg _) (z := 0) hr fun x hx => expNegInvGlue.pos_of_pos ?_
  rw [mem_ball, dist_zero_right] at hx
  nlinarith [norm_nonneg x]

/-- the radial mollifier of radius `r` and mass `1` -/
def rbump (r : ℝ) (y : ℂ) : ℝ := rbump0 r y / ∫ x, rbump0 r x

lemma contDiff_rbump (r : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rbump r) :=
  (contDiff_rbump0 r).div_const _

lemma rbump_eq_zero {r : ℝ} (hr : 0 ≤ r) {y : ℂ} (hy : r < ‖y‖) : rbump r y = 0 := by
  rw [rbump, rbump0_eq_zero hr hy, zero_div]

lemma isRad_rbump (r : ℝ) : IsRad (rbump r) := fun a y => by
  simp [rbump, rbump0]

lemma integral_rbump {r : ℝ} (hr : 0 < r) : ∫ y, rbump r y = 1 := by
  unfold rbump
  rw [integral_div, div_self (integral_rbump0_pos hr).ne']

lemma rbump_nonneg (r : ℝ) (y : ℂ) : 0 ≤ rbump r y :=
  div_nonneg (expNegInvGlue.nonneg _) (integral_nonneg fun _ => expNegInvGlue.nonneg _)

/-- the translated mollifier `rbump s (· − z)` as a test function on `V` -/
def rbTest {V : Opens ℂ} {z : ℂ} {s : ℝ} (hs : 0 < s) (hV : closedBall z s ⊆ V) : TestOn V :=
  ofBall ((contDiff_rbump s).comp (contDiff_id.sub contDiff_const))
    (fun x hx => rbump_eq_zero hs.le hx) hV

@[simp] lemma rbTest_apply {V : Opens ℂ} {z : ℂ} {s : ℝ} (hs : 0 < s) (hV : closedBall z s ⊆ V)
    (x : ℂ) : rbTest hs hV x = rbump s (x - z) := rfl

/-- the pairings with the mollifiers do not depend on the radius -/
lemma pair_rbTest_eq {V : Opens ℂ} (T : DistOn V)
    (hT : ∀ f : MarkovZB.zsSub (V : Set ℂ), T (MarkovHarm.cmTestOn f) = 0) {z : ℂ} {s s' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') (hV : closedBall z s ⊆ V) (hV' : closedBall z s' ⊆ V) :
    T (rbTest hs hV) = T (rbTest hs' hV') := by
  have hm : closedBall z (max s s') ⊆ V := by
    rcases max_cases s s' with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> assumption
  refine pair_eq_of_radial T hT (contDiff_rbump s) (contDiff_rbump s') (isRad_rbump s)
    (isRad_rbump s') (r := max s s') (fun y hy => rbump_eq_zero hs.le ((le_max_left _ _).trans_lt hy))
    (fun y hy => rbump_eq_zero hs'.le ((le_max_right _ _).trans_lt hy))
    (by rw [integral_rbump hs, integral_rbump hs']) hm (fun _ => rfl) (fun _ => rfl)

open Classical in
/-- the candidate harmonic function `g(z) = T(rbump s (· − z))` -/
def weylFun {V : Opens ℂ} (T : DistOn V) (z : ℂ) : ℝ :=
  if h : ∃ s, 0 < s ∧ closedBall z s ⊆ V then T (rbTest h.choose_spec.1 h.choose_spec.2) else 0

lemma weylFun_eq {V : Opens ℂ} (T : DistOn V)
    (hT : ∀ f : MarkovZB.zsSub (V : Set ℂ), T (MarkovHarm.cmTestOn f) = 0) {z : ℂ} {s : ℝ}
    (hs : 0 < s) (hV : closedBall z s ⊆ V) : weylFun T z = T (rbTest hs hV) := by
  have h : ∃ s, 0 < s ∧ closedBall z s ⊆ V := ⟨s, hs, hV⟩
  rw [weylFun, dif_pos h]
  exact pair_rbTest_eq T hT _ _ _ _

end MarkovWeyl2
end LQGMetric
