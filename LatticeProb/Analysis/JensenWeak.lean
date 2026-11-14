import LatticeProb.Analysis.JensenSmooth
import LatticeProb.Analysis.WeakLaplaceMollify
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Jensen's lemma for continuous weak solutions of the Laplace equation

Let `u` be continuous on an open set `U` containing a closed ball `B = closedBall c r`, and a weak
solution of `Δ u = s` in `U` with `s` measurable and `|s| ≤ K` almost everywhere on `U`. If `u` is
smaller on the sphere than `u x₀ - 2 δ r` for some `x₀` in the open ball, then the set of points of `B`
that maximise `u + ⟪p, ·⟫` over `B` for some slope `‖p‖ < δ` satisfies
`μ (ball 0 δ) ≤ K ^ dim E * μ (that set)`.

The proof mollifies `u` (`weakLaplace_mollify`), applies the smooth Jensen lemma (`jensen_smooth`) to
the mollifications, and passes to the limit: a point that is a maximiser, with slope of norm at most
`δ' < δ`, for infinitely many mollifications is a maximiser for `u` with a limit slope, by uniform
convergence and compactness of the slopes. The measures of the limsup sets are controlled by
continuity of the measure from above.
-/

open MeasureTheory Metric Filter Topology Set
open scoped InnerProductSpace ContDiff
open Laplacian

namespace LatticeProb.PegdenSmart

section JensenWeak

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A continuous function that is strictly below `a` on a compact set is below `a` by a uniform margin. -/
theorem exists_margin {S : Set E} (hS : IsCompact S) {f : E → ℝ} (hf : ContinuousOn f S) {a : ℝ}
    (h : ∀ y ∈ S, f y < a) : ∃ g > 0, ∀ y ∈ S, f y + g ≤ a := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun y hy => absurd hy (notMem_empty y)⟩
  · obtain ⟨y₀, hy₀, hmax⟩ := hS.exists_isMaxOn hne hf
    refine ⟨(a - f y₀) / 2, by linarith [h y₀ hy₀], fun y hy => ?_⟩
    have h1 : f y ≤ f y₀ := hmax hy
    have h2 := h y₀ hy₀
    linarith

variable [MeasurableSpace E] [BorelSpace E]

/-- A sequence of smooth nonnegative mollifiers of integral one with supports shrinking to the origin. -/
theorem exists_mollifier_sequence (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ (ε : ℕ → ℝ) (ρ : ℕ → E → ℝ), (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n, ContDiff ℝ ∞ (ρ n) ∧ HasCompactSupport (ρ n) ∧ tsupport (ρ n) ⊆ closedBall 0 (ε n) ∧
        (∀ x, 0 ≤ ρ n x) ∧ ∫ x, ρ n x ∂μ = 1 := by
  let f : ℕ → ContDiffBump (0 : E) := fun n =>
    { rIn := 1 / (2 * ((n : ℝ) + 1))
      rOut := 1 / ((n : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        rw [div_lt_div_iff₀ (by positivity) this]
        nlinarith }
  refine ⟨fun n => 1 / ((n : ℝ) + 1), fun n => (f n).normed μ, fun n => by positivity,
    tendsto_one_div_add_atTop_nhds_zero_nat, fun n => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (f n).contDiff_normed (n := ⊤)
  · exact (f n).hasCompactSupport_normed
  · exact (f n).tsupport_normed_eq.subset
  · exact fun x => (f n).nonneg_normed x
  · exact (f n).integral_normed

omit [MeasurableSpace E] [BorelSpace E] in
/-- The limsup of the maximiser sets of a sequence of functions converging pointwise on the compact
set `B` consists of maximisers of the limit with a limit slope. -/
theorem mem_maximisers_of_mem_limsup {B : Set E} {G : ℕ → E → ℝ} {u : E → ℝ} {δ δ' : ℝ}
    (hδ : δ' < δ) (hconv : ∀ x ∈ B, Tendsto (fun m => G m x) atTop (𝓝 (u x))) {x : E}
    (hx : x ∈ ⋂ N : ℕ, ⋃ m ≥ N, {x ∈ B | ∃ p : E, ‖p‖ < δ' ∧
      ∀ y ∈ B, G m y + ⟪p, y⟫_ℝ ≤ G m x + ⟪p, x⟫_ℝ}) :
    x ∈ B ∧ ∃ p : E, ‖p‖ < δ ∧ ∀ y ∈ B, u y + ⟪p, y⟫_ℝ ≤ u x + ⟪p, x⟫_ℝ := by
  have hfreq : ∃ᶠ m in atTop, x ∈ {x ∈ B | ∃ p : E, ‖p‖ < δ' ∧
      ∀ y ∈ B, G m y + ⟪p, y⟫_ℝ ≤ G m x + ⟪p, x⟫_ℝ} := by
    refine Filter.frequently_atTop.mpr fun N => ?_
    obtain ⟨m, hm, hmx⟩ := mem_iUnion₂.mp (mem_iInter.mp hx N)
    exact ⟨m, hm, hmx⟩
  obtain ⟨φ, hφ, hφS⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose p hp hmax using fun k => (hφS k).2
  obtain ⟨pl, hpl, ψ, hψ, hlim⟩ := (isCompact_closedBall (0 : E) δ').tendsto_subseq
    (x := p) (fun k => mem_closedBall_zero_iff.2 (hp k).le)
  have hxB : x ∈ B := (hφS 0).1
  refine ⟨hxB, pl, lt_of_le_of_lt (mem_closedBall_zero_iff.mp hpl) hδ, fun y hy => ?_⟩
  have hφψ : Tendsto (fun k => φ (ψ k)) atTop atTop :=
    hφ.tendsto_atTop.comp hψ.tendsto_atTop
  have h1 : Tendsto (fun k => G (φ (ψ k)) y + ⟪p (ψ k), y⟫_ℝ) atTop (𝓝 (u y + ⟪pl, y⟫_ℝ)) :=
    ((hconv y hy).comp hφψ).add (hlim.inner tendsto_const_nhds)
  have h2 : Tendsto (fun k => G (φ (ψ k)) x + ⟪p (ψ k), x⟫_ℝ) atTop (𝓝 (u x + ⟪pl, x⟫_ℝ)) :=
    ((hconv x hxB).comp hφψ).add (hlim.inner tendsto_const_nhds)
  exact le_of_tendsto_of_tendsto' h1 h2 fun k => hmax (ψ k) y hy


/-- Core of Jensen's lemma: a uniformly convergent sequence of smooth functions with `Δ ≥ -K`, whose
maximisers (for slopes of norm below `δ'`) are interior, gives the measure bound for the maximisers
of the limit (for slopes of norm below `δ`). -/
theorem jensen_weak_core (μ : Measure E) [μ.IsAddHaarMeasure] (u : E → ℝ) (F : ℕ → E → ℝ)
    (c x₀ : E) (r K δ δ' g : ℝ) (hr : 0 < r) (hK : 0 ≤ K) (hδ' : 0 < δ') (hδδ' : δ' < δ)
    (hx₀ : x₀ ∈ ball c r)
    (hgm : ∀ y ∈ sphere c r, u y + g ≤ u x₀ - 2 * δ * r)
    (hcont : ∀ n, ContinuousOn (F n) (closedBall c r)) (hC2 : ∀ n, ContDiffOn ℝ 2 (F n) (ball c r))
    (hΔ : ∀ n, ∀ x ∈ ball c r, -K ≤ Δ (F n) x)
    (hclose : ∀ n, ∀ x ∈ closedBall c r, dist (u x) (F n x) < g / 2)
    (hconv : ∀ x ∈ closedBall c r, Tendsto (fun n => F n x) atTop (𝓝 (u x))) :
    μ (ball (0 : E) δ') ≤ ENNReal.ofReal K ^ Module.finrank ℝ E *
      μ {x ∈ closedBall c r | ∃ p : E, ‖p‖ < δ ∧
        ∀ y ∈ closedBall c r, u y + ⟪p, y⟫_ℝ ≤ u x + ⟪p, x⟫_ℝ} := by
  have hBc : IsCompact (closedBall c r) := isCompact_closedBall c r
  have hint : ∀ n, ∀ p : E, ‖p‖ < δ' → ∀ x ∈ closedBall c r,
      (∀ y ∈ closedBall c r, F n y + ⟪p, y⟫_ℝ ≤ F n x + ⟪p, x⟫_ℝ) → x ∈ ball c r := by
    intro n p hp x hx hmax
    by_contra hxb
    have hxs : x ∈ sphere c r := by
      rw [mem_sphere]
      rw [mem_closedBall] at hx
      rw [mem_ball, not_lt] at hxb
      exact le_antisymm hx hxb
    have h1 := hgm x hxs
    have h2 := hmax x₀ (ball_subset_closedBall hx₀)
    have hxx₀ : ‖x - x₀‖ ≤ 2 * r := by
      have h3 := dist_triangle x c x₀
      rw [mem_sphere.mp hxs, dist_comm c x₀] at h3
      have h4 := mem_ball.mp hx₀
      rw [dist_eq_norm] at h3
      linarith
    have h3 : ⟪p, x - x₀⟫_ℝ ≤ 2 * δ * r := by
      calc ⟪p, x - x₀⟫_ℝ ≤ ‖p‖ * ‖x - x₀‖ := real_inner_le_norm _ _
        _ ≤ δ * (2 * r) := mul_le_mul (hp.le.trans hδδ'.le) hxx₀ (norm_nonneg _) (by linarith)
        _ = 2 * δ * r := by ring
    have hx0 := hclose n x₀ (ball_subset_closedBall hx₀)
    have hx1 := hclose n x hx
    rw [Real.dist_eq, abs_lt] at hx0 hx1
    rw [inner_sub_right] at h3
    linarith [hx0.1, hx0.2, hx1.1, hx1.2]
  have hSm : ∀ n, MeasurableSet {x ∈ closedBall c r | ∃ p : E, ‖p‖ < δ' ∧
      ∀ y ∈ closedBall c r, F n y + ⟪p, y⟫_ℝ ≤ F n x + ⟪p, x⟫_ℝ} := fun n =>
    measurableSet_maximisers hBc (hcont n) δ'
  have hS : ∀ n, μ (ball (0 : E) δ') ≤ ENNReal.ofReal K ^ Module.finrank ℝ E *
      μ {x ∈ closedBall c r | ∃ p : E, ‖p‖ < δ' ∧
        ∀ y ∈ closedBall c r, F n y + ⟪p, y⟫_ℝ ≤ F n x + ⟪p, x⟫_ℝ} := fun n =>
    jensen_smooth μ (F n) c r K δ' hr hK hδ' (hcont n) (hC2 n) (hΔ n) (hint n)
  set A : ℕ → Set E := fun N => ⋃ m ≥ N, {x ∈ closedBall c r | ∃ p : E, ‖p‖ < δ' ∧
    ∀ y ∈ closedBall c r, F m y + ⟪p, y⟫_ℝ ≤ F m x + ⟪p, x⟫_ℝ} with hA
  have hAm : ∀ N, MeasurableSet (A N) := fun N =>
    MeasurableSet.biUnion (to_countable _) fun m _ => hSm m
  have hAanti : Antitone A := fun a b hab x hx => by
    obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨m, hab.trans hm, hxm⟩
  have hfin : μ (A 0) ≠ ⊤ :=
    ((measure_mono (iUnion₂_subset fun m _ => fun x (hx : x ∈ _) => hx.1)).trans_lt
      hBc.measure_lt_top).ne
  have hlim := tendsto_measure_iInter_atTop (fun N => (hAm N).nullMeasurableSet) hAanti ⟨0, hfin⟩
  have hbound : ∀ N, μ (ball (0 : E) δ') ≤ ENNReal.ofReal K ^ Module.finrank ℝ E * μ (A N) :=
    fun N => (hS N).trans (mul_le_mul' le_rfl (measure_mono (subset_iUnion₂ (s := fun m (_ : N ≤ m) =>
      {x ∈ closedBall c r | ∃ p : E, ‖p‖ < δ' ∧
        ∀ y ∈ closedBall c r, F m y + ⟪p, y⟫_ℝ ≤ F m x + ⟪p, x⟫_ℝ}) N le_rfl)))
  have hle : μ (ball (0 : E) δ') ≤ ENNReal.ofReal K ^ Module.finrank ℝ E * μ (⋂ N, A N) :=
    ge_of_tendsto (ENNReal.Tendsto.const_mul hlim
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))) (Filter.Eventually.of_forall hbound)
  refine hle.trans (mul_le_mul' le_rfl (measure_mono fun x hx => ?_))
  exact mem_maximisers_of_mem_limsup (B := closedBall c r) (G := F) hδδ' hconv hx

/-- Jensen's lemma for slopes of norm below `δ' < δ`. -/
theorem jensen_weak_aux (μ : Measure E) [μ.IsAddHaarMeasure] (U : Set E) (u s : E → ℝ)
    (c x₀ : E) (r K δ δ' : ℝ) (hU : IsOpen U) (hcU : closedBall c r ⊆ U) (hr : 0 < r)
    (hK : 0 ≤ K) (hδ' : 0 < δ') (hδδ' : δ' < δ) (hu : ContinuousOn u U)
    (hweak : IsWeakSolutionLaplace μ U u s) (hsm : AEStronglyMeasurable s (μ.restrict U))
    (hs : ∀ᵐ x ∂μ.restrict U, |s x| ≤ K) (hx₀ : x₀ ∈ ball c r)
    (hmargin : ∀ y ∈ sphere c r, u y < u x₀ - 2 * δ * r) :
    μ (ball (0 : E) δ') ≤ ENNReal.ofReal K ^ Module.finrank ℝ E *
      μ {x ∈ closedBall c r | ∃ p : E, ‖p‖ < δ ∧
        ∀ y ∈ closedBall c r, u y + ⟪p, y⟫_ℝ ≤ u x + ⟪p, x⟫_ℝ} := by
  obtain ⟨ε, ρ, hε0, hε, hρ⟩ := exists_mollifier_sequence (E := E) μ
  obtain ⟨hC1, hC2, hC3, hC4, -⟩ :=
    weakLaplace_mollify μ U u s K ε ρ hU hu hK hs hsm hweak hε0 hε hρ
  have hBc : IsCompact (closedBall c r) := isCompact_closedBall c r
  obtain ⟨g, hg, hgm⟩ := exists_margin (isCompact_sphere c r)
    (hu.mono (sphere_subset_closedBall.trans hcU)) hmargin
  obtain ⟨θ, hθ, hthick⟩ := hBc.exists_thickening_subset_open hU hcU
  have hunif0 := hC4 (closedBall c r) hBc hcU
  have hunif := Metric.tendstoUniformlyOn_iff.mp hunif0
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    ((hε.eventually (gt_mem_nhds hθ)).and (hunif (g / 2) (half_pos hg)))
  have hnb : ∀ n ≥ N0, ∀ x ∈ closedBall c r, closedBall x (ε n) ⊆ U := by
    intro n hn x hx t ht
    refine hthick ?_
    rw [mem_thickening_iff]
    exact ⟨x, hx, lt_of_le_of_lt (mem_closedBall.mp ht) (hN0 n hn).1⟩
  refine jensen_weak_core μ u (fun m => convolution (U.indicator u) (ρ (m + N0))
    (ContinuousLinearMap.mul ℝ ℝ) μ) c x₀ r K δ δ' g hr hK hδ' hδδ' hx₀ hgm ?_ ?_ ?_ ?_ ?_
  · intro m
    exact (hC1 (m + N0)).continuousOn.mono fun x hx => hnb (m + N0) (Nat.le_add_left _ _) x hx
  · intro m
    exact ((hC1 (m + N0)).mono fun x hx =>
      hnb (m + N0) (Nat.le_add_left _ _) x (ball_subset_closedBall hx)).of_le (by simp)
  · intro m x hx
    have hxm : x ∈ {x | closedBall x (ε (m + N0)) ⊆ U} :=
      hnb (m + N0) (Nat.le_add_left _ _) x (ball_subset_closedBall hx)
    have h1 := hC2 (m + N0) x hxm
    have h2 := hC3 (m + N0) x
    show -K ≤ Δ (convolution (U.indicator u) (ρ (m + N0)) (ContinuousLinearMap.mul ℝ ℝ) μ) x
    rw [h1]
    exact neg_le_of_abs_le h2
  · intro m x hx
    exact (hN0 (m + N0) (Nat.le_add_left _ _)).2 x hx
  · intro x hx
    exact (hunif0.tendsto_at hx).comp (tendsto_add_atTop_nat N0)


/-- **Jensen's lemma** for a continuous weak solution of `Δ u = s` with `|s| ≤ K` almost everywhere:
if `u` on the sphere `sphere c r` is smaller than `u x₀ - 2 δ r` for some `x₀` in the open ball, then the
set of points of the closed ball that maximise `u + ⟪p, ·⟫` over the closed ball for some `‖p‖ < δ`
satisfies `μ (ball 0 δ) ≤ K ^ dim E * μ (that set)`. -/
theorem jensen_weak (μ : Measure E) [μ.IsAddHaarMeasure] (U : Set E) (u s : E → ℝ) (c x₀ : E)
    (r K δ : ℝ) (hU : IsOpen U) (hcU : closedBall c r ⊆ U) (hr : 0 < r) (hK : 0 ≤ K)
    (hδ : 0 < δ) (hu : ContinuousOn u U) (hweak : IsWeakSolutionLaplace μ U u s)
    (hsm : AEStronglyMeasurable s (μ.restrict U)) (hs : ∀ᵐ x ∂μ.restrict U, |s x| ≤ K)
    (hx₀ : x₀ ∈ ball c r) (hmargin : ∀ y ∈ sphere c r, u y < u x₀ - 2 * δ * r) :
    μ (ball (0 : E) δ) ≤ ENNReal.ofReal K ^ Module.finrank ℝ E *
      μ {x ∈ closedBall c r | ∃ p : E, ‖p‖ < δ ∧
        ∀ y ∈ closedBall c r, u y + ⟪p, y⟫_ℝ ≤ u x + ⟪p, x⟫_ℝ} := by
  set δn : ℕ → ℝ := fun n => δ * (1 - 1 / ((n : ℝ) + 2)) with hδn
  have hinv : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 2) ∧ 1 / ((n : ℝ) + 2) ≤ 1 / 2 := fun n =>
    ⟨by positivity, one_div_le_one_div_of_le (by norm_num) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])⟩
  have hδn_pos : ∀ n, 0 < δn n := fun n => by
    have := hinv n
    exact mul_pos hδ (by linarith)
  have hδn_lt : ∀ n, δn n < δ := fun n => by
    have := hinv n
    nlinarith
  have hδn_mono : Monotone δn := fun a b hab => by
    have : 1 / ((b : ℝ) + 2) ≤ 1 / ((a : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [(Nat.cast_le (α := ℝ)).mpr hab])
    exact mul_le_mul_of_nonneg_left (by linarith) hδ.le
  have hmono : Monotone fun n => ball (0 : E) (δn n) := fun a b hab =>
    ball_subset_ball (hδn_mono hab)
  have hunion : ⋃ n, ball (0 : E) (δn n) = ball 0 δ := by
    refine subset_antisymm (iUnion_subset fun n => ball_subset_ball (hδn_lt n).le) fun x hx => ?_
    rw [mem_ball_zero_iff] at hx
    have hpos : 0 < δ - ‖x‖ := sub_pos.mpr hx
    obtain ⟨n, hn⟩ := exists_nat_gt (δ / (δ - ‖x‖))
    refine mem_iUnion.mpr ⟨n, ?_⟩
    rw [mem_ball_zero_iff]
    have h1 : δ / (δ - ‖x‖) < (n : ℝ) + 2 := by linarith
    rw [div_lt_iff₀ hpos] at h1
    have h2 : δ / ((n : ℝ) + 2) < δ - ‖x‖ := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    calc ‖x‖ < δ - δ / ((n : ℝ) + 2) := by linarith
      _ = δn n := by simp only [hδn]; ring
  have hmain : ∀ n, μ (ball (0 : E) (δn n)) ≤ ENNReal.ofReal K ^ Module.finrank ℝ E *
      μ {x ∈ closedBall c r | ∃ p : E, ‖p‖ < δ ∧
        ∀ y ∈ closedBall c r, u y + ⟪p, y⟫_ℝ ≤ u x + ⟪p, x⟫_ℝ} := fun n =>
    jensen_weak_aux μ U u s c x₀ r K δ (δn n) hU hcU hr hK (hδn_pos n) (hδn_lt n) hu hweak hsm hs
      hx₀ hmargin
  have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hunion] at hlim
  exact le_of_tendsto' hlim hmain

end JensenWeak

end LatticeProb.PegdenSmart
