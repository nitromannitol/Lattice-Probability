import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Convergence in measure, uniformly over a compact set of parameters

Let `F y z ω ∈ [0, ∞]` be a family of random distances indexed by pairs of points of a
pseudo-metric space `X`, satisfying the triangle inequality `F y z ≤ F c y + F c z` through any
third point `c`. A typical example is `F y z ω = sup_t d(Y_z(ω)(t), Y_y(ω)(t))` for a family of
random paths `Y_y` indexed by their starting point `y`, all built on one probability space.

If for every point `c` of a compact set `K` the distance `F c z` tends to `0` in measure as
`z → c`, then the convergence is uniform on `K`: for all `ε, θ > 0` there is `δ > 0` such that
`μ {F y z ≥ ε} ≤ θ` for every `y ∈ K` and every `z` with `dist z y < δ`. The proof is the usual
covering argument (Lebesgue number lemma). No measurability is needed for this step: the
estimate holds for the outer measure.

Pointwise convergence in measure in turn follows from almost-everywhere convergence along every
sequence `z_n → c`, for (almost everywhere) measurable distances on a finite measure space.

## Main statements

* `LatticeProb.UniformInMeasure.exists_forall_measure_le_of_tendsto`: uniformity on a compact
  set from pointwise convergence in measure.
* `LatticeProb.UniformInMeasure.tendsto_measure_le_of_tendsto_ae`: for `[0, ∞]`-valued
  a.e.-measurable random variables on a finite measure space, a.e. convergence to `0` implies
  `μ {ε ≤ f n} → 0`.
* `LatticeProb.UniformInMeasure.tendsto_nhds_measure_le_of_seq_ae`: the same along a
  neighbourhood filter, from a.e. convergence along every sequence.
* `LatticeProb.UniformInMeasure.exists_forall_measure_le_of_seq_ae`: the combination.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal

namespace LatticeProb.UniformInMeasure

variable {X Ω : Type*} [PseudoMetricSpace X] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Convergence in measure is uniform on compact sets of parameters.** If the random distances
`F` satisfy the triangle inequality through any third point and `F c z → 0` in measure as
`z → c` for every `c ∈ K`, with `K` compact, then for all `ε, θ > 0` some `δ > 0` gives
`μ {ε ≤ F y z} ≤ θ` for all `y ∈ K` and `dist z y < δ`. The measure may be evaluated on
non-measurable sets (outer measure). -/
theorem exists_forall_measure_le_of_tendsto {K : Set X} (hK : IsCompact K)
    {F : X → X → Ω → ℝ≥0∞} (htri : ∀ c y z ω, F y z ω ≤ F c y ω + F c z ω)
    (hconv : ∀ c ∈ K, ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun z => μ {ω | ε ≤ F c z ω}) (𝓝 c) (𝓝 0))
    {ε θ : ℝ≥0∞} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ y ∈ K, ∀ z, dist z y < δ → μ {ω | ε ≤ F y z ω} ≤ θ := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hθ2 : 0 < θ / 2 := ENNReal.half_pos hθ.ne'
  have hloc : ∀ c : K, ∃ r > 0, ∀ z : X, dist z (c : X) < r →
      μ {ω | ε / 2 ≤ F c z ω} ≤ θ / 2 := by
    intro c
    have h := (hconv c c.2 (ε / 2) hε2).eventually (eventually_le_nhds hθ2)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 h
    exact ⟨r, hr, fun z hz => hball hz⟩
  choose r hr hloc using hloc
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK
    (c := fun c : K => ball (c : X) (r c)) (fun _ => isOpen_ball)
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, mem_ball_self (hr _)⟩)
  refine ⟨δ, hδ, fun y hy z hz => ?_⟩
  obtain ⟨c, hc⟩ := hleb y hy
  have hyc : dist y c < r c := hc (mem_ball_self hδ)
  have hzc : dist z c < r c := hc hz
  calc μ {ω | ε ≤ F y z ω}
      ≤ μ ({ω | ε / 2 ≤ F c y ω} ∪ {ω | ε / 2 ≤ F c z ω}) := by
        refine measure_mono fun ω hω => ?_
        have hω' : ε ≤ F y z ω := hω
        rcases le_or_gt (ε / 2) (F c y ω) with h1 | h1
        · exact Or.inl h1
        rcases le_or_gt (ε / 2) (F c z ω) with h2 | h2
        · exact Or.inr h2
        have hlt : F y z ω < ε := by
          calc F y z ω ≤ F c y ω + F c z ω := htri c y z ω
            _ < ε / 2 + ε / 2 := ENNReal.add_lt_add h1 h2
            _ = ε := ENNReal.add_halves ε
        exact absurd hω' (not_le.2 hlt)
    _ ≤ θ / 2 + θ / 2 :=
        (measure_union_le _ _).trans (add_le_add (hloc c y hyc) (hloc c z hzc))
    _ = θ := ENNReal.add_halves θ

/-- **Almost-everywhere convergence implies convergence in measure** for `[0, ∞]`-valued
a.e.-measurable random variables on a finite measure space: if `f n → 0` a.e., then
`μ {ε ≤ f n} → 0` for every `ε > 0`. -/
theorem tendsto_measure_le_of_tendsto_ae [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ) (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) : Tendsto (fun n => μ {ω | ε ≤ f n ω}) atTop (𝓝 0) := by
  set g : ℕ → Ω → ℝ≥0 := fun n ω => (min (f n ω) 1).toNNReal with hg_def
  have hg : ∀ n, AEStronglyMeasurable (g n) μ := fun n =>
    (((hf n).min aemeasurable_const).ennreal_toNNReal).aestronglyMeasurable
  have hglim : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 ((fun _ => (0 : ℝ≥0)) ω)) := by
    filter_upwards [hlim] with ω hω
    have h1 : Tendsto (fun n => min (f n ω) 1) atTop (𝓝 (min 0 1)) :=
      hω.min tendsto_const_nhds
    rw [min_eq_left (zero_le_one' ℝ≥0∞)] at h1
    have h2 := (ENNReal.tendsto_toNNReal ENNReal.zero_ne_top).comp h1
    rw [ENNReal.toNNReal_zero] at h2
    exact h2
  have hT := tendstoInMeasure_of_tendsto_ae hg hglim (min ε 1) (lt_min hε one_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => bot_le)
    fun n => measure_mono fun ω hω => ?_
  have hω' : ε ≤ f n ω := hω
  have hne : min (f n ω) 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have key : edist (g n ω) 0 = min (f n ω) 1 := by
    rw [edist_dist, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, hg_def,
      ENNReal.coe_toNNReal hne]
  show min ε 1 ≤ edist (g n ω) 0
  rw [key]
  exact min_le_min hω' le_rfl

/-- Convergence in measure along a neighbourhood filter from almost-everywhere convergence
along every sequence: if `G (u n) → 0` a.e. for every sequence `u n → c`, and every `G z` is
a.e.-measurable on a finite measure space, then `μ {ε ≤ G z} → 0` as `z → c`. -/
theorem tendsto_nhds_measure_le_of_seq_ae [IsFiniteMeasure μ] {c : X} {G : X → Ω → ℝ≥0∞}
    (hG : ∀ z, AEMeasurable (G z) μ)
    (hae : ∀ u : ℕ → X, Tendsto u atTop (𝓝 c) →
      ∀ᵐ ω ∂μ, Tendsto (fun n => G (u n) ω) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) : Tendsto (fun z => μ {ω | ε ≤ G z ω}) (𝓝 c) (𝓝 0) :=
  tendsto_iff_seq_tendsto.2 fun u hu =>
    tendsto_measure_le_of_tendsto_ae (fun n => hG (u n)) (hae u hu) hε

/-- **Uniform convergence in measure on a compact set from a.e. sequential convergence.** For
a.e.-measurable random distances `F` on a finite measure space satisfying the triangle
inequality through any third point, if `F c (u n) → 0` a.e. for every `c ∈ K` and every
sequence `u n → c`, with `K` compact, then for all `ε, θ > 0` some `δ > 0` gives
`μ {ε ≤ F y z} ≤ θ` for all `y ∈ K` and `dist z y < δ`. -/
theorem exists_forall_measure_le_of_seq_ae [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K)
    {F : X → X → Ω → ℝ≥0∞} (htri : ∀ c y z ω, F y z ω ≤ F c y ω + F c z ω)
    (hF : ∀ y z, AEMeasurable (F y z) μ)
    (hae : ∀ c ∈ K, ∀ u : ℕ → X, Tendsto u atTop (𝓝 c) →
      ∀ᵐ ω ∂μ, Tendsto (fun n => F c (u n) ω) atTop (𝓝 0))
    {ε θ : ℝ≥0∞} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ y ∈ K, ∀ z, dist z y < δ → μ {ω | ε ≤ F y z ω} ≤ θ :=
  exists_forall_measure_le_of_tendsto hK htri
    (fun c hc _ hε' => tendsto_nhds_measure_le_of_seq_ae (hF c) (hae c hc) hε') hε hθ

end LatticeProb.UniformInMeasure
