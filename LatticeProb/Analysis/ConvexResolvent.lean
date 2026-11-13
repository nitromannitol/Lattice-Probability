import LatticeProb.Analysis.ConvexSubgradient

/-!
# The resolvent of a convex function

For a convex function `f : E → ℝ` on a finite-dimensional real inner product space, the resolvent
`J y = (I + ∂f)⁻¹ y` is the unique minimiser of `q ↦ f q + ‖y - q‖ ^ 2 / 2` (the proximal point of `y`).
It is characterised by `y - J y ∈ ∂f (J y)`, and it is single valued, nonexpansive and onto.

`convexResolvent f y` is defined by choice as a minimiser of the energy `q ↦ f q + ‖y - q‖ ^ 2 / 2`,
which exists when `f` is convex; for every convex `f` it is the point `q` with `y - q ∈ ∂f q`.

## Main results

* `LatticeProb.ConvexAnalysis.isSubgradientAt_convexResolvent`: `y - J y` is a subgradient at `J y`.
* `LatticeProb.ConvexAnalysis.convexResolvent_eq_of_isSubgradientAt`: `J (z + g) = z` whenever `g` is a
  subgradient at `z`.
* `LatticeProb.ConvexAnalysis.lipschitzWith_one_convexResolvent`: `J` is nonexpansive.
* `LatticeProb.ConvexAnalysis.surjective_convexResolvent`: `J` is onto.
-/

open Set Filter Topology
open scoped InnerProductSpace

namespace LatticeProb.ConvexAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ}

/-- A convex function on a finite-dimensional inner product space has a minimiser of the energy
`q ↦ f q + ‖y - q‖ ^ 2 / 2`. -/
theorem exists_forall_energy_le (hf : ConvexOn ℝ Set.univ f) (y : E) :
    ∃ q, ∀ p, f q + ‖y - q‖ ^ 2 / 2 ≤ f p + ‖y - p‖ ^ 2 / 2 := by
  have hcont := continuous_of_convexOn_univ hf
  obtain ⟨g₀, hg₀⟩ := exists_isSubgradientAt hf 0
  set R : ℝ := 2 * (‖y‖ + ‖g₀‖) + 1 with hR
  have hRpos : 0 < R := by positivity
  have hF : Continuous fun q => f q + ‖y - q‖ ^ 2 / 2 := by fun_prop
  obtain ⟨q₀, hq₀, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hRpos.le⟩ hF.continuousOn
  refine ⟨q₀, fun p => ?_⟩
  by_cases hp : p ∈ Metric.closedBall (0 : E) R
  · exact hmin hp
  · have hp' : R < ‖p‖ := by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hp
      exact hp
    have h0 : f q₀ + ‖y - q₀‖ ^ 2 / 2 ≤ f 0 + ‖y - 0‖ ^ 2 / 2 :=
      hmin (Metric.mem_closedBall_self hRpos.le)
    have h1 : f 0 + ⟪g₀, p - 0⟫_ℝ ≤ f p := hg₀ p
    have h2 : -(‖g₀‖ * ‖p‖) ≤ ⟪g₀, p - 0⟫_ℝ := by
      rw [sub_zero]
      exact neg_le_of_abs_le (abs_real_inner_le_norm g₀ p)
    have h3 : ‖p‖ - ‖y‖ ≤ ‖y - p‖ := by
      have := norm_sub_norm_le p y
      rwa [norm_sub_rev] at this
    have hyR : ‖y‖ ≤ R := by rw [hR]; linarith [norm_nonneg g₀, norm_nonneg y]
    have h4 : (‖p‖ - ‖y‖) ^ 2 ≤ ‖y - p‖ ^ 2 := pow_le_pow_left₀ (by linarith) h3 2
    have h5 : 0 ≤ ‖p‖ * (‖p‖ - 2 * (‖y‖ + ‖g₀‖)) :=
      mul_nonneg (norm_nonneg _) (by linarith)
    rw [sub_zero] at h0
    nlinarith [h0, h1, h2, h4, h5]

omit [FiniteDimensional ℝ E] in
/-- A minimiser `q` of the energy `p ↦ f p + ‖y - p‖ ^ 2 / 2` of a convex function `f` satisfies
`y - q ∈ ∂f q`. -/
theorem isSubgradientAt_of_forall_energy_le (hf : ConvexOn ℝ Set.univ f) {y q : E}
    (hq : ∀ p, f q + ‖y - q‖ ^ 2 / 2 ≤ f p + ‖y - p‖ ^ 2 / 2) :
    IsSubgradientAt f q (y - q) := by
  intro z
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      f q + ⟪y - q, z - q⟫_ℝ ≤ f z + t * (‖z - q‖ ^ 2 / 2) := by
    intro t ht ht1
    have hconv := hf.2 (Set.mem_univ q) (Set.mem_univ z) (sub_nonneg.mpr ht1) ht.le
      (sub_add_cancel 1 t)
    have hu : (1 - t) • q + t • z = q + t • (z - q) := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [hu, smul_eq_mul, smul_eq_mul] at hconv
    have hmin := hq (q + t • (z - q))
    have hy : y - (q + t • (z - q)) = (y - q) - t • (z - q) := by abel
    rw [hy, norm_sub_sq_real (y - q) (t • (z - q)), norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs,
      sq_abs] at hmin
    have : t * (f q + ⟪y - q, z - q⟫_ℝ) ≤ t * (f z + t * (‖z - q‖ ^ 2 / 2)) := by
      nlinarith [hmin, hconv]
    exact le_of_mul_le_mul_left this ht
  have hlim : Tendsto (fun t : ℝ => f z + t * (‖z - q‖ ^ 2 / 2)) (𝓝[>] 0) (𝓝 (f z)) := by
    have h : Tendsto (fun t : ℝ => f z + t * (‖z - q‖ ^ 2 / 2)) (𝓝 0)
        (𝓝 (f z + 0 * (‖z - q‖ ^ 2 / 2))) :=
      (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f q + ⟪y - q, z - q⟫_ℝ ≤ f z + t * (‖z - q‖ ^ 2 / 2) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) fun t ht => key t ht.1 ht.2.le
  have := ge_of_tendsto hlim hev
  simpa using this

/-- The resolvent `(I + ∂f)⁻¹` of `f`: a minimiser of `q ↦ f q + ‖y - q‖ ^ 2 / 2`. For convex `f` the
minimiser exists (`exists_forall_energy_le`) and is unique; for other `f` the value is arbitrary. -/
noncomputable def convexResolvent (f : E → ℝ) (y : E) : E :=
  Classical.epsilon fun q => ∀ p, f q + ‖y - q‖ ^ 2 / 2 ≤ f p + ‖y - p‖ ^ 2 / 2

/-- The resolvent minimises the energy `q ↦ f q + ‖y - q‖ ^ 2 / 2`. -/
theorem convexResolvent_energy_le (hf : ConvexOn ℝ Set.univ f) (y p : E) :
    f (convexResolvent f y) + ‖y - convexResolvent f y‖ ^ 2 / 2 ≤ f p + ‖y - p‖ ^ 2 / 2 :=
  Classical.epsilon_spec (exists_forall_energy_le hf y) p

/-- `y - J y` is a subgradient of `f` at `J y`. -/
theorem isSubgradientAt_convexResolvent (hf : ConvexOn ℝ Set.univ f) (y : E) :
    IsSubgradientAt f (convexResolvent f y) (y - convexResolvent f y) :=
  isSubgradientAt_of_forall_energy_le hf (convexResolvent_energy_le hf y)

/-- If `g` is a subgradient of `f` at `z`, then `J (z + g) = z`. -/
theorem convexResolvent_eq_of_isSubgradientAt (hf : ConvexOn ℝ Set.univ f) {z g : E}
    (h : IsSubgradientAt f z g) : convexResolvent f (z + g) = z := by
  set q := convexResolvent f (z + g) with hq
  have h2 := (isSubgradientAt_convexResolvent hf (z + g)).inner_sub_nonneg h
  rw [← hq] at h2
  have e : z + g - q - g = -(q - z) := by abel
  rw [e, inner_neg_left, real_inner_self_eq_norm_sq] at h2
  have h4 : ‖q - z‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4))

/-- The resolvent of a convex function is nonexpansive. -/
theorem lipschitzWith_one_convexResolvent (hf : ConvexOn ℝ Set.univ f) :
    LipschitzWith 1 (convexResolvent f) := by
  refine LipschitzWith.mk_one fun y y' => ?_
  have h := (isSubgradientAt_convexResolvent hf y).inner_sub_nonneg
    (isSubgradientAt_convexResolvent hf y')
  set q := convexResolvent f y
  set q' := convexResolvent f y'
  have e : y - q - (y' - q') = (y - y') - (q - q') := by abel
  rw [e, inner_sub_left, real_inner_self_eq_norm_sq] at h
  have h2 := real_inner_le_norm (y - y') (q - q')
  rw [dist_eq_norm, dist_eq_norm]
  by_cases h0 : ‖q - q'‖ = 0
  · rw [h0]
    exact norm_nonneg _
  · have hpos : 0 < ‖q - q'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    refine le_of_mul_le_mul_right ?_ hpos
    nlinarith [h, h2]

/-- The resolvent of a convex function is onto. -/
theorem surjective_convexResolvent (hf : ConvexOn ℝ Set.univ f) :
    Function.Surjective (convexResolvent f) := fun z => by
  obtain ⟨g, hg⟩ := exists_isSubgradientAt hf z
  exact ⟨z + g, convexResolvent_eq_of_isSubgradientAt hf hg⟩

end LatticeProb.ConvexAnalysis
