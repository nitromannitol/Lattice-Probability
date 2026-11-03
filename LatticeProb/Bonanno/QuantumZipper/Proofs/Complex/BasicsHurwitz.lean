/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.BasicsHurwitz at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Hurwitz's theorem (EXT-CA node A5)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.A, node **A5**.

* `hurwitz_eventually_exists_eq`: if `F n → f` locally uniformly on an open `U`, the `F n` are
  holomorphic, `f z₀ = w` and `f` is not identically `w` near `z₀`, then for every `ε > 0`
  and all large `n` the equation `F n z = w` has a solution in `U ∩ ball z₀ ε`.
* `hurwitz_eventually_exists_zero`: the version on a preconnected `U` with `f` nonconstant.
* `hurwitz_injOn`: a locally uniform limit of injective holomorphic maps on a preconnected
  open set is injective or constant.

Proof route (as prescribed by the blueprint, no argument principle): the zero of `f - w` at
`z₀` is isolated; on a small circle `‖f - w‖ ≥ m > 0`, so `‖F n - w‖ > m/2` there for large `n`
while `‖F n z₀ - w‖ < m/2`; if `F n - w` had no zero in the closed disk, the maximum modulus
principle for `1/(F n - w)` would give `‖F n z₀ - w‖ ≥ m/2`. Statement: Ahlfors, *Complex
Analysis*, 3rd ed. 1979, Ch. 5 §1.1, Theorem 2 (Hurwitz), p. 178, proved there with the
argument principle; the minimum-modulus variant used here is our own (elementary) route, as
the blueprint prescribes. (b) follows from (a) as in Ahlfors, Ch. 6 §1.1, p. 231 (univalence
of the limit in the proof of the Riemann mapping theorem): two distinct preimages of one value
would give two distinct preimages for `F n`, `n` large.
-/

noncomputable section

open Set Metric Filter Topology

namespace QuantumZipper.CA

/-- **Hurwitz's theorem**, local form: solutions of `F n z = w` accumulate at every isolated
solution of `f z = w`. -/
theorem hurwitz_eventually_exists_eq {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hlim : TendstoLocallyUniformlyOn F f atTop U)
    {z₀ w : ℂ} (hz₀ : z₀ ∈ U) (hfw : f z₀ = w) (hnw : ¬ ∀ᶠ z in 𝓝 z₀, f z = w)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ z ∈ U, z ∈ ball z₀ ε ∧ F n z = w := by
  have hfd : DifferentiableOn ℂ f U := hlim.differentiableOn (Eventually.of_forall hF) hU
  have hfa : AnalyticAt ℂ (fun z => f z - w) z₀ :=
    (hfd.analyticAt (hU.mem_nhds hz₀)).sub analyticAt_const
  have hne : ∀ᶠ z in 𝓝[≠] z₀, f z - w ≠ 0 := by
    refine hfa.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h => hnw ?_
    filter_upwards [h] with z hz using sub_eq_zero.1 hz
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
  obtain ⟨ρ, hρ, hρne⟩ := hne
  set r := min (min ε δ) ρ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hm1 : min (min ε δ) ρ ≤ min ε δ := min_le_left _ _
  have hm2 : min (min ε δ) ρ ≤ ρ := min_le_right _ _
  have hm3 : min ε δ ≤ ε := min_le_left _ _
  have hm4 : min ε δ ≤ δ := min_le_right _ _
  have hrε : r < ε := by rw [hr]; linarith
  have hrδ : r < δ := by rw [hr]; linarith
  have hrρ : r < ρ := by rw [hr]; linarith
  have hcb : closedBall z₀ r ⊆ U := (closedBall_subset_ball hrδ).trans hδU
  have hsph : ∀ z ∈ sphere z₀ r, f z - w ≠ 0 := by
    intro z hz
    rw [mem_sphere] at hz
    refine hρne (by rw [hz]; exact hrρ) ?_
    intro h
    rw [mem_singleton_iff] at h
    rw [h, dist_self] at hz
    linarith
  have hsphU : sphere z₀ r ⊆ U := sphere_subset_closedBall.trans hcb
  obtain ⟨x, hx, hxmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr0.le)
    ((hfd.continuousOn.mono hsphU).sub continuousOn_const).norm
  set m := ‖f x - w‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (hsph x hx)
  have hmle : ∀ z ∈ sphere z₀ r, m ≤ ‖f z - w‖ := fun z hz => hxmin hz
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hlim _ hcb
    (isCompact_closedBall _ _)
  have hev := Metric.tendstoUniformlyOn_iff.1 hunif (m / 2) (by positivity)
  filter_upwards [hev] with n hn
  by_contra hno
  push Not at hno
  have hnz : ∀ z ∈ closedBall z₀ r, F n z - w ≠ 0 := fun z hz =>
    sub_ne_zero.2 (hno z (hcb hz) (closedBall_subset_ball hrε hz))
  set g : ℂ → ℂ := fun z => (F n z - w)⁻¹ with hg
  have hgd : DifferentiableOn ℂ g (closedBall z₀ r) :=
    (((hF n).mono hcb).sub_const w).inv hnz
  have hgc : DiffContOnCl ℂ g (ball z₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball z₀ hr0.ne']
  have key : ∀ z ∈ closedBall z₀ r, ‖f z - F n z‖ < m / 2 := fun z hz => by
    rw [← dist_eq_norm]; exact hn z hz
  have hfront : ∀ z ∈ frontier (ball z₀ r), ‖g z‖ ≤ (m / 2)⁻¹ := by
    intro z hz
    rw [frontier_ball z₀ hr0.ne'] at hz
    have h1 := hmle z hz
    have h2 := key z (sphere_subset_closedBall hz)
    have h3 : m / 2 ≤ ‖F n z - w‖ := by
      have := norm_sub_norm_le (f z - w) (F n z - w)
      have e : f z - w - (F n z - w) = f z - F n z := by ring
      rw [e] at this
      linarith
    rw [hg, norm_inv]
    exact inv_anti₀ (by positivity) h3
  have hz0 := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hgc hfront
    (subset_closure (mem_ball_self hr0))
  rw [hg, norm_inv] at hz0
  have hpos : 0 < ‖F n z₀ - w‖ := norm_pos_iff.2 (hnz z₀ (mem_closedBall_self hr0.le))
  have h4 : m / 2 ≤ ‖F n z₀ - w‖ := (inv_le_inv₀ hpos (by positivity)).1 hz0
  have h5 := key z₀ (mem_closedBall_self hr0.le)
  rw [hfw] at h5
  have e : ‖w - F n z₀‖ = ‖F n z₀ - w‖ := norm_sub_rev _ _
  linarith

/-- A holomorphic function on a preconnected open set which is locally constant near one
point is constant (identity theorem). -/
theorem not_eventually_eq_of_not_const {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f U) (hnc : ¬ ∃ c, EqOn f (fun _ => c) U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) : ¬ ∀ᶠ z in 𝓝 z₀, f z = f z₀ := by
  intro h
  exact hnc ⟨f z₀, (hfd.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hUc hz₀ h⟩

/-- **Hurwitz's theorem** (blueprint A5(a)): if `F n → f` locally uniformly on a preconnected
open `U`, `f` nonconstant and `f z₀ = 0`, then for large `n`, `F n` has a zero near `z₀`. -/
theorem hurwitz_eventually_exists_zero {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) (hnc : ¬ ∃ c, EqOn f (fun _ => c) U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hf0 : f z₀ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ z ∈ U, z ∈ ball z₀ ε ∧ F n z = 0 := by
  have hfd : DifferentiableOn ℂ f U := hlim.differentiableOn (Eventually.of_forall hF) hU
  have := not_eventually_eq_of_not_const hU hUc hfd hnc hz₀
  rw [hf0] at this
  exact hurwitz_eventually_exists_eq hU hF hlim hz₀ hf0 this hε

/-- **Hurwitz's theorem on univalent limits** (blueprint A5(b)): a locally uniform limit of
injective holomorphic maps on a preconnected open set is injective unless it is constant. -/
theorem hurwitz_injOn {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hinj : ∀ n, InjOn (F n) U) (hlim : TendstoLocallyUniformlyOn F f atTop U)
    (hnc : ¬ ∃ c, EqOn f (fun _ => c) U) : InjOn f U := by
  have hfd : DifferentiableOn ℂ f U := hlim.differentiableOn (Eventually.of_forall hF) hU
  intro a ha b hb hab
  by_contra hne
  have hd : 0 < dist a b := dist_pos.2 hne
  have h1 := hurwitz_eventually_exists_eq hU hF hlim ha rfl
    (not_eventually_eq_of_not_const hU hUc hfd hnc ha) (half_pos hd)
  have h2 := hurwitz_eventually_exists_eq hU hF hlim hb hab.symm
    (by rw [hab]; exact not_eventually_eq_of_not_const hU hUc hfd hnc hb) (half_pos hd)
  obtain ⟨n, ⟨z, hzU, hz, hFz⟩, ⟨z', hz'U, hz', hFz'⟩⟩ := (h1.and h2).exists
  have hzz : z = z' := hinj n hzU hz'U (hFz.trans hFz'.symm)
  subst hzz
  rw [mem_ball] at hz hz'
  have := dist_triangle a z b
  rw [dist_comm a z] at this
  linarith

end QuantumZipper.CA
