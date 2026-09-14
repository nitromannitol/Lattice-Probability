/-
From the finite-dimensional laws and equicontinuity in probability to the expectation of a
functional of the whole path.

A family of random functions `f i` on a compact set `K` of a metric space is given, together
with a limit `g` on another probability space.  Two things are assumed: the law of every finite
vector `(f i (x 1), …, f i (x m))` converges to the law of `(g (x 1), …, g (x m))`, and the
family is equicontinuous in probability, that is, for every level `δ` and every tolerance `ε`
there is a distance `η`, the SAME for every `i`, such that with probability at least `1 - ε` the
function `f i` varies by at most `δ` between any two points of `K` at distance less than `η`.
This is the pair of clauses an Arzelà-Ascoli tightness statement provides.

The conclusion is that `E Φ (f i) → E Φ (g)` for every bounded functional `Φ` which is uniformly
continuous for the supremum norm on `K`.  This is the weakest of the three forms of a Skorokhod
representation which a consumer of a weak limit asks for, and the only one which does not need a
common probability space: the value of a bounded uniformly continuous functional of the path is
determined, up to an error controlled by the modulus of continuity, by finitely many values of
the path, and those converge by hypothesis.

The bridge between the two is the interpolation of `LatticeProb/Prob/NetApprox.lean`: for a
finite `η`-net `x` of `K`, `Φ (netApprox x η (f i (x ·)))` is a bounded continuous function of
the finite vector `(f i (x k))ₖ`, so its expectation converges by the finite-dimensional
hypothesis, and it differs from `Φ (f i)` by at most the tolerance except on the event that
`f i` varies by more than `δ` at scale `η`, whose probability the equicontinuity bounds.
-/
import Mathlib
import LatticeProb.Prob.NetApprox

open MeasureTheory Filter

open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

variable {E : Type*} [PseudoMetricSpace E]

/-! ### The deterministic bridge -/

/-- **A uniformly continuous functional is nearly a function of the values on a net.**  If `x`
is an `η`-net of `K` whose points lie in `K`, if `v` varies by at most `δ` between points of `K`
at distance less than `η`, and if `Φ` moves by at most `ε` under a uniform change of size `δ` on
`K`, then `Φ` of the interpolation of the values of `v` on the net is within `ε` of `Φ v`. -/
theorem abs_netFunctional_sub_le {K : Set E} {m : ℕ} {x : Fin m → E} {η δ ε : ℝ} {v : E → ℝ}
    (hxK : ∀ k, x k ∈ K) (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η)
    (hmod : ∀ z ∈ K, ∀ y ∈ K, dist z y < η → |v z - v y| ≤ δ) (hv : ContinuousOn v K)
    {Φ : (E → ℝ) → ℝ}
    (hΦδ : ∀ v' w' : E → ℝ, ContinuousOn v' K → ContinuousOn w' K →
      (∀ z ∈ K, |v' z - w' z| ≤ δ) → |Φ v' - Φ w'| ≤ ε) :
    |Φ (netApprox x η (fun k => v (x k))) - Φ v| ≤ ε := by
  refine hΦδ _ v (continuousOn_netApprox _ hnet) hv ?_
  intro y hy
  refine abs_netApprox_sub_le (tentSum_pos (hnet y hy)) ?_
  intro k hk
  exact hmod (x k) (hxK k) y hy hk

/-- **The interpolated functional is continuous in the values on the net.** -/
theorem continuous_netFunctional {K : Set E} {m : ℕ} {x : Fin m → E} {η : ℝ}
    (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η) {Φ : (E → ℝ) → ℝ}
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : E → ℝ,
      ContinuousOn v K → ContinuousOn w K → (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ v - Φ w| ≤ ε) :
    Continuous fun u : Fin m → ℝ => Φ (netApprox x η u) := by
  refine Metric.continuous_iff.2 ?_
  intro b ε hε
  obtain ⟨δ, hδ, hΦδ⟩ := hΦu (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have hcoord : ∀ k, |a k - b k| ≤ δ := by
    intro k
    have hk : dist (a k) (b k) ≤ dist a b := dist_le_pi_dist a b k
    rw [Real.dist_eq] at hk
    linarith
  have hz : ∀ z ∈ K, |netApprox x η a z - netApprox x η b z| ≤ δ := fun z hz =>
    abs_netApprox_sub_netApprox_le (tentSum_pos (hnet z hz)) hcoord
  have hfin := hΦδ (netApprox x η a) (netApprox x η b) (continuousOn_netApprox a hnet)
    (continuousOn_netApprox b hnet) hz
  rw [Real.dist_eq]
  linarith

/-- **Refining the net recovers the functional.**  Along any sequence of nets whose scales tend
to zero, the interpolated functional of a function continuous on the compact set `K` tends to
the functional of the function itself. -/
theorem tendsto_netFunctional {K : Set E} (hK : IsCompact K) {v : E → ℝ}
    (hv : ContinuousOn v K) {Φ : (E → ℝ) → ℝ}
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' w' : E → ℝ,
      ContinuousOn v' K → ContinuousOn w' K →
      (∀ z ∈ K, |v' z - w' z| ≤ δ) → |Φ v' - Φ w'| ≤ ε)
    {m : ℕ → ℕ} {x : (n : ℕ) → Fin (m n) → E} {r : ℕ → ℝ}
    (hxK : ∀ n k, x n k ∈ K) (hnet : ∀ n, ∀ y ∈ K, ∃ k, dist (x n k) y < r n)
    (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => Φ (netApprox (x n) (r n) (fun k => v (x n k)))) atTop (𝓝 (Φ v)) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨δ, hδ, hΦδ⟩ := hΦu (ε / 2) (by positivity)
  obtain ⟨η, hη, huc⟩ :=
    (Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hv)) δ hδ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hr η hη
  refine ⟨N, fun n hn => ?_⟩
  have hrn : r n < η := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hmod : ∀ z ∈ K, ∀ y ∈ K, dist z y < r n → |v z - v y| ≤ δ := by
    intro z hz y hy hzy
    have h := huc z hz y hy (lt_trans hzy hrn)
    rw [Real.dist_eq] at h
    exact h.le
  have hb := abs_netFunctional_sub_le (x := x n) (hxK n) (hnet n) hmod hv hΦδ
  rw [Real.dist_eq]
  linarith

/-! ### Measurability -/

/-- The interpolated functional of a process with measurable coordinates is measurable. -/
theorem measurable_netFunctional {Ω : Type*} [MeasurableSpace Ω] {K : Set E} {m : ℕ}
    {x : Fin m → E} {η : ℝ} {F : E → Ω → ℝ} {Φ : (E → ℝ) → ℝ}
    (hFm : ∀ z, Measurable (F z)) (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η)
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : E → ℝ,
      ContinuousOn v K → ContinuousOn w K → (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ v - Φ w| ≤ ε) :
    Measurable fun ω => Φ (netApprox x η (fun k => F (x k) ω)) :=
  (continuous_netFunctional hnet hΦu).measurable.comp
    (measurable_pi_lambda _ fun k => hFm (x k))

/-- **The functional of the path is measurable**, for a process whose coordinates are measurable
and whose paths are continuous on the compact set `K`.  It is the pointwise limit of the
interpolated functionals along nets of vanishing scale. -/
theorem measurable_pathFunctional {Ω : Type*} [MeasurableSpace Ω] {K : Set E} (hK : IsCompact K)
    {F : E → Ω → ℝ} {Φ : (E → ℝ) → ℝ} (hFm : ∀ z, Measurable (F z))
    (hFc : ∀ ω, ContinuousOn (fun z => F z ω) K)
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : E → ℝ,
      ContinuousOn v K → ContinuousOn w K → (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ v - Φ w| ≤ ε) :
    Measurable fun ω => Φ (fun z => F z ω) := by
  classical
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  choose m x hxK hnet using fun n : ℕ => exists_net hK (hpos n)
  have hmeas : ∀ n : ℕ,
      Measurable fun ω => Φ (netApprox (x n) (1 / (n + 1)) (fun k => F (x n k) ω)) :=
    fun n => measurable_netFunctional hFm (hnet n) hΦu
  refine measurable_of_tendsto_metrizable hmeas ?_
  rw [tendsto_pi_nhds]
  intro ω
  exact tendsto_netFunctional hK (hFc ω) hΦu hxK hnet tendsto_one_div_add_atTop_nhds_zero_nat

/-! ### The two probabilistic steps -/

/-- **Convergence in distribution moves expectations of bounded continuous functions.** -/
theorem tendsto_integral_of_tendstoInDistribution {ι : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {L : Filter ι} {m : ℕ}
    {X : (i : ι) → Ω i → (Fin m → ℝ)} {Z : Ω' → (Fin m → ℝ)}
    (h : TendstoInDistribution X L Z P Q) {ψ : (Fin m → ℝ) → ℝ} (hc : Continuous ψ)
    {M : ℝ} (hb : ∀ u, |ψ u| ≤ M) :
    Tendsto (fun i => ∫ ω, ψ (X i ω) ∂(P i)) L (𝓝 (∫ ω, ψ (Z ω) ∂Q)) := by
  have hψ : ∀ u : Fin m → ℝ, ‖ψ u‖ ≤ M := fun u => by
    simpa [Real.norm_eq_abs] using hb u
  have hconv := (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h.tendsto)
    (BoundedContinuousFunction.ofNormedAddCommGroup ψ hc M hψ)
  have hZ : ∫ v, ψ v ∂(Q.map Z) = ∫ ω, ψ (Z ω) ∂Q :=
    integral_map h.aemeasurable_limit hc.aestronglyMeasurable
  have hX : ∀ i, ∫ v, ψ v ∂((P i).map (X i)) = ∫ ω, ψ (X i ω) ∂(P i) :=
    fun i => integral_map (h.forall_aemeasurable i) hc.aestronglyMeasurable
  simpa [MeasureTheory.ProbabilityMeasure.coe_mk,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup, hX, hZ] using hconv

/-- **The interpolation error in expectation.**  Off the event that `F` varies by more than `δ`
between two points of `K` at distance less than `η`, the interpolated functional is within `ε`
of the functional of the path; on that event the two differ by at most `2 M`. -/
theorem abs_integral_netFunctional_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {K : Set E} {m : ℕ} {x : Fin m → E} {η δ ε ρ M : ℝ}
    {F : E → Ω → ℝ} {Φ : (E → ℝ) → ℝ}
    (hxK : ∀ k, x k ∈ K) (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η)
    (hΦb : ∀ v, |Φ v| ≤ M) (hδ : 0 ≤ δ)
    (hFc : ∀ ω, ContinuousOn (fun z => F z ω) K)
    (hΦδ : ∀ v w : E → ℝ, ContinuousOn v K → ContinuousOn w K →
      (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ v - Φ w| ≤ ε)
    (hm1 : Measurable fun ω => Φ (netApprox x η (fun k => F (x k) ω)))
    (hm2 : Measurable fun ω => Φ (fun z => F z ω)) (hρ : 0 ≤ ρ)
    (hbad : P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} ≤ ENNReal.ofReal ρ) :
    |∫ ω, Φ (netApprox x η (fun k => F (x k) ω)) ∂P - ∫ ω, Φ (fun z => F z ω) ∂P|
      ≤ ε + 2 * M * ρ := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hΦb fun _ => 0)
  have hε : 0 ≤ ε := by
    have h := hΦδ (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) continuousOn_const continuousOn_const
      (by intro z _; simpa using hδ)
    simpa using h
  set A := toMeasurable P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} with hA
  have hAm : MeasurableSet A := measurableSet_toMeasurable _ _
  have hAsub : {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} ⊆ A :=
    subset_toMeasurable _ _
  have hAmeas : P A = P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} :=
    measure_toMeasurable _
  have hi1 : Integrable (fun ω => Φ (netApprox x η (fun k => F (x k) ω))) P :=
    Integrable.of_bound hm1.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hΦb _)
  have hi2 : Integrable (fun ω => Φ (fun z => F z ω)) P :=
    Integrable.of_bound hm2.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hΦb _)
  have hib : Integrable (fun ω => ε + A.indicator (fun _ => 2 * M) ω) P :=
    (integrable_const ε).add ((integrable_const (2 * M)).indicator hAm)
  have hpt : ∀ ω, |Φ (netApprox x η (fun k => F (x k) ω)) - Φ (fun z => F z ω)|
      ≤ ε + A.indicator (fun _ => 2 * M) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have h1 : |Φ (netApprox x η fun k => F (x k) ω)| ≤ M := hΦb _
      have h2 : |Φ fun z => F z ω| ≤ M := hΦb _
      have h3 := abs_sub (Φ (netApprox x η fun k => F (x k) ω)) (Φ fun z => F z ω)
      linarith [abs_sub_abs_le_abs_sub (Φ (netApprox x η fun k => F (x k) ω)) (Φ fun z => F z ω)]
    · rw [Set.indicator_of_notMem hω, add_zero]
      have hmod : ∀ z ∈ K, ∀ y ∈ K, dist z y < η → |F z ω - F y ω| ≤ δ := by
        intro z hz y hy hzy
        by_contra hcon
        exact hω (hAsub ⟨z, hz, y, hy, hzy, lt_of_not_ge hcon⟩)
      exact abs_netFunctional_sub_le hxK hnet hmod (hFc ω) hΦδ
  calc |∫ ω, Φ (netApprox x η (fun k => F (x k) ω)) ∂P - ∫ ω, Φ (fun z => F z ω) ∂P|
      = |∫ ω, (Φ (netApprox x η (fun k => F (x k) ω)) - Φ (fun z => F z ω)) ∂P| := by
        rw [integral_sub hi1 hi2]
    _ ≤ ∫ ω, |Φ (netApprox x η (fun k => F (x k) ω)) - Φ (fun z => F z ω)| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, (ε + A.indicator (fun _ => 2 * M) ω) ∂P :=
        integral_mono ((hi1.sub hi2).abs) hib hpt
    _ = ε + 2 * M * (P A).toReal := by
        rw [integral_add (integrable_const ε) ((integrable_const (2 * M)).indicator hAm),
          integral_const, integral_indicator_const _ hAm]
        simp [measureReal_def, mul_comm]
    _ ≤ ε + 2 * M * ρ := by
        have : (P A).toReal ≤ ρ := by
          rw [hAmeas]
          exact ENNReal.toReal_le_of_le_ofReal hρ hbad
        nlinarith

/-- **A uniformly continuous functional is nearly a function of the values on a net**, with no
continuity hypothesis on `v`. -/
theorem abs_netFunctional_sub_le' {K : Set E} {m : ℕ} {x : Fin m → E} {η δ ε : ℝ} {v : E → ℝ}
    (hxK : ∀ k, x k ∈ K) (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η)
    (hmod : ∀ z ∈ K, ∀ y ∈ K, dist z y < η → |v z - v y| ≤ δ)
    {Φ : (E → ℝ) → ℝ}
    (hΦδ : ∀ v' w' : E → ℝ, (∀ z ∈ K, |v' z - w' z| ≤ δ) → |Φ v' - Φ w'| ≤ ε) :
    |Φ (netApprox x η (fun k => v (x k))) - Φ v| ≤ ε := by
  refine hΦδ _ v ?_
  intro y hy
  refine LatticeProb.abs_netApprox_sub_le (LatticeProb.tentSum_pos (hnet y hy)) ?_
  intro k hk
  exact hmod (x k) (hxK k) y hy hk


theorem abs_integral_netFunctional_sub_le' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {K : Set E} {m : ℕ} {x : Fin m → E} {η δ ε ρ M : ℝ}
    {F : E → Ω → ℝ} {Φ : (E → ℝ) → ℝ}
    (hxK : ∀ k, x k ∈ K) (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η)
    (hΦb : ∀ v, |Φ v| ≤ M) (hδ : 0 ≤ δ)
    (hΦδ : ∀ v w : E → ℝ, (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ v - Φ w| ≤ ε)
    (hm1 : Measurable fun ω => Φ (netApprox x η (fun k => F (x k) ω)))
    (hm2 : Measurable fun ω => Φ (fun z => F z ω)) (hρ : 0 ≤ ρ)
    (hbad : P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} ≤ ENNReal.ofReal ρ) :
    |∫ ω, Φ (netApprox x η (fun k => F (x k) ω)) ∂P - ∫ ω, Φ (fun z => F z ω) ∂P|
      ≤ ε + 2 * M * ρ := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hΦb fun _ => 0)
  have hε : 0 ≤ ε := by
    have h := hΦδ (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (by intro z _; simpa using hδ)
    simpa using h
  set A := toMeasurable P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} with hA
  have hAm : MeasurableSet A := measurableSet_toMeasurable _ _
  have hAsub : {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} ⊆ A :=
    subset_toMeasurable _ _
  have hAmeas : P A = P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} :=
    measure_toMeasurable _
  have hi1 : Integrable (fun ω => Φ (netApprox x η (fun k => F (x k) ω))) P :=
    Integrable.of_bound hm1.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hΦb _)
  have hi2 : Integrable (fun ω => Φ (fun z => F z ω)) P :=
    Integrable.of_bound hm2.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hΦb _)
  have hib : Integrable (fun ω => ε + A.indicator (fun _ => 2 * M) ω) P :=
    (integrable_const ε).add ((integrable_const (2 * M)).indicator hAm)
  have hpt : ∀ ω, |Φ (netApprox x η (fun k => F (x k) ω)) - Φ (fun z => F z ω)|
      ≤ ε + A.indicator (fun _ => 2 * M) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have h1 : |Φ (netApprox x η fun k => F (x k) ω)| ≤ M := hΦb _
      have h2 : |Φ fun z => F z ω| ≤ M := hΦb _
      have h3 := abs_sub (Φ (netApprox x η fun k => F (x k) ω)) (Φ fun z => F z ω)
      linarith [abs_sub_abs_le_abs_sub (Φ (netApprox x η fun k => F (x k) ω)) (Φ fun z => F z ω)]
    · rw [Set.indicator_of_notMem hω, add_zero]
      have hmod : ∀ z ∈ K, ∀ y ∈ K, dist z y < η → |F z ω - F y ω| ≤ δ := by
        intro z hz y hy hzy
        by_contra hcon
        exact hω (hAsub ⟨z, hz, y, hy, hzy, lt_of_not_ge hcon⟩)
      exact abs_netFunctional_sub_le' hxK hnet hmod hΦδ
  calc |∫ ω, Φ (netApprox x η (fun k => F (x k) ω)) ∂P - ∫ ω, Φ (fun z => F z ω) ∂P|
      = |∫ ω, (Φ (netApprox x η (fun k => F (x k) ω)) - Φ (fun z => F z ω)) ∂P| := by
        rw [integral_sub hi1 hi2]
    _ ≤ ∫ ω, |Φ (netApprox x η (fun k => F (x k) ω)) - Φ (fun z => F z ω)| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, (ε + A.indicator (fun _ => 2 * M) ω) ∂P :=
        integral_mono ((hi1.sub hi2).abs) hib hpt
    _ = ε + 2 * M * (P A).toReal := by
        rw [integral_add (integrable_const ε) ((integrable_const (2 * M)).indicator hAm),
          integral_const, integral_indicator_const _ hAm]
        simp [measureReal_def, mul_comm]
    _ ≤ ε + 2 * M * ρ := by
        have : (P A).toReal ≤ ρ := by
          rw [hAmeas]
          exact ENNReal.toReal_le_of_le_ofReal hρ hbad
        nlinarith


/-- A uniform-continuity modulus for the supremum norm on `K` stated for all functions is also
one stated for continuous functions. -/
theorem hΦu_of_continuousOn {K : Set E} {Φ : (E → ℝ) → ℝ}
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : E → ℝ,
      (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ v - Φ w| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : E → ℝ,
      ContinuousOn v K → ContinuousOn w K → (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ v - Φ w| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hΦu ε hε
  exact ⟨δ, hδ, fun v w _ _ hvw => h v w hvw⟩


/-- **A net fine enough for the limit process.**  For every tolerance there is a net, of scale as
small as one likes, whose interpolated functional has nearly the right expectation under the
law of the limit. -/
theorem exists_net_integral_close {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {K : Set E} (hK : IsCompact K) {g : E → Ω' → ℝ}
    {Φ : (E → ℝ) → ℝ} {M : ℝ} (hgm : ∀ z, Measurable (g z))
    (hgc : ∀ ω, ContinuousOn (fun z => g z ω) K) (hΦb : ∀ v, |Φ v| ≤ M)
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : E → ℝ,
      ContinuousOn v K → ContinuousOn w K → (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ v - Φ w| ≤ ε)
    {ε η₀ : ℝ} (hε : 0 < ε) (hη₀ : 0 < η₀) :
    ∃ (m : ℕ) (x : Fin m → E) (η : ℝ), 0 < η ∧ η ≤ η₀ ∧ (∀ k, x k ∈ K) ∧
      (∀ y ∈ K, ∃ k, dist (x k) y < η) ∧
      |∫ ω, Φ (netApprox x η (fun k => g (x k) ω)) ∂Q - ∫ ω, Φ (fun z => g z ω) ∂Q| ≤ ε := by
  classical
  have hrpos : ∀ n : ℕ, (0 : ℝ) < η₀ / (n + 1) := fun n => by positivity
  have hrle : ∀ n : ℕ, η₀ / (n + 1) ≤ η₀ := by
    intro n
    refine div_le_self hη₀.le ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hr0 : Tendsto (fun n : ℕ => η₀ / (n + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul η₀
  choose m x hxK hnet using fun n : ℕ => exists_net hK (hrpos n)
  have hmeas : ∀ n : ℕ,
      Measurable fun ω => Φ (netApprox (x n) (η₀ / (n + 1)) (fun k => g (x n k) ω)) :=
    fun n => measurable_netFunctional hgm (hnet n) hΦu
  have hlim : Tendsto
      (fun n : ℕ => ∫ ω, Φ (netApprox (x n) (η₀ / (n + 1)) (fun k => g (x n k) ω)) ∂Q) atTop
      (𝓝 (∫ ω, Φ (fun z => g z ω) ∂Q)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun n => (hmeas n).aestronglyMeasurable) (integrable_const M)
      (fun n => Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hΦb _)
      (Filter.Eventually.of_forall fun ω => ?_)
    exact tendsto_netFunctional hK (hgc ω) hΦu hxK hnet hr0
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
  refine ⟨m N, x N, η₀ / (N + 1), hrpos N, hrle N, hxK N, hnet N, ?_⟩
  have h := hN N le_rfl
  rw [Real.dist_eq] at h
  exact h.le

/-! ### The theorem -/

/-- **From the finite-dimensional laws and equicontinuity in probability to the expectation of a
functional of the whole path, without a continuity hypothesis on the pre-limit paths.**  Let
`f i` be random functions on a compact set `K` of a metric space, with measurable coordinates,
and let `g` be a random function of the same kind on another probability space, with paths
continuous on `K`.  Assume that the law of every finite vector `(f i (x 1), …, f i (x m))` at
points of `K` converges along `L` to the law of the corresponding vector of `g`, and that the
family is equicontinuous in probability: for every tolerance `ε` and every level `η` there is a
distance `δ`, the same for every `i`, beyond which the chance that `f i` varies by more than `η`
between two points of `K` at distance less than `δ` is at most `ε`.  Then the expectation of
`Φ (f i)` converges to the expectation of `Φ (g)` for every bounded functional `Φ` which is
uniformly continuous for the supremum norm on `K`.

This is the form a step function of a rescaled lattice satisfies: no realization of `f i` need
be continuous, the measurability of the path functional `ω ↦ Φ (fun z => f i z ω)` is assumed
directly as `hfΦm`, and the uniform continuity of `Φ` is stated for all functions rather than
only for continuous ones.  The limit field keeps its continuity hypothesis `hgc`, which is used
to approximate `Φ (g)` by its values on a net. -/
theorem tendsto_integral_of_fdd_of_equicontinuous'
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {L : Filter ι}
    {f : (i : ι) → E → Ω i → ℝ} {g : E → Ω' → ℝ} {K : Set E} (hK : IsCompact K)
    {Φ : (E → ℝ) → ℝ}
    (hfm : ∀ᶠ i in L, ∀ z, Measurable (f i z)) (hgm : ∀ z, Measurable (g z))
    (hgc : ∀ ω, ContinuousOn (fun z => g z ω) K)
    (hfΦm : ∀ᶠ i in L, Measurable fun ω => Φ (fun z => f i z ω))
    (hfdd : ∀ (m : ℕ) (x : Fin m → E), (∀ k, x k ∈ K) →
      TendstoInDistribution (fun i ω k => f i (x k) ω) L (fun ω k => g (x k) ω) P Q)
    (htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in L,
      P i {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧ η < |f i z ω - f i y ω|} ≤ ENNReal.ofReal ε)
    {M : ℝ} (hΦb : ∀ v, |Φ v| ≤ M)
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : E → ℝ,
      (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ v - Φ w| ≤ ε) :
    Tendsto (fun i => ∫ ω, Φ (fun z => f i z ω) ∂(P i)) L
      (𝓝 (∫ ω, Φ (fun z => g z ω) ∂Q)) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hΦb fun _ => 0)
  refine Metric.tendsto_nhds.2 ?_
  intro ε₀ hε₀
  have hden : (0 : ℝ) < 4 + 2 * M := by linarith
  set ε := ε₀ / (4 + 2 * M) with hεdef
  have hε : 0 < ε := by positivity
  have hne : (4 + 2 * M) ≠ 0 := ne_of_gt hden
  have hεmul : (4 + 2 * M) * ε = ε₀ := by
    rw [hεdef]
    field_simp
  obtain ⟨δ, hδ, hΦδ⟩ := hΦu ε hε
  obtain ⟨η₀, hη₀, htightη⟩ := htight ε δ hε hδ
  obtain ⟨m, x, η, hη, hηle, hxK, hnet, hclose⟩ :=
    exists_net_integral_close (Q := Q) hK hgm hgc hΦb (hΦu_of_continuousOn hΦu) hε hη₀
  have hψc : Continuous fun u : Fin m → ℝ => Φ (netApprox x η u) :=
    continuous_netFunctional hnet (hΦu_of_continuousOn hΦu)
  have hfdd2 := tendsto_integral_of_tendstoInDistribution (hfdd m x hxK) hψc
    (M := M) (fun u => hΦb _)
  have hev : ∀ᶠ i in L, |∫ ω, Φ (netApprox x η (fun k => f i (x k) ω)) ∂(P i)
      - ∫ ω, Φ (netApprox x η (fun k => g (x k) ω)) ∂Q| < ε := by
    have h := Metric.tendsto_nhds.1 hfdd2 ε hε
    simpa [Real.dist_eq] using h
  filter_upwards [hev, htightη, hfm, hfΦm] with i hi htighti hfmi hfΦmi
  have hbadi : P i {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |f i z ω - f i y ω|}
      ≤ ENNReal.ofReal ε := by
    refine le_trans (measure_mono ?_) htighti
    rintro ω ⟨z, hz, y, hy, hzy, hval⟩
    exact ⟨z, hz, y, hy, lt_of_lt_of_le hzy hηle, hval⟩
  have h1 := abs_integral_netFunctional_sub_le' (P := P i) (F := f i) hxK hnet hΦb hδ.le hΦδ
    (measurable_netFunctional hfmi hnet (hΦu_of_continuousOn hΦu))
    hfΦmi hε.le hbadi
  have key : ∀ a b c d : ℝ, |b - a| ≤ ε + 2 * M * ε → |b - c| < ε → |c - d| ≤ ε →
      |a - d| < (4 + 2 * M) * ε := by
    intro a b c d e1 e2 e3
    have f1 := abs_le.1 e1
    have f2 := abs_lt.1 e2
    have f3 := abs_le.1 e3
    rw [abs_lt]
    constructor <;> nlinarith [f1.1, f1.2, f2.1, f2.2, f3.1, f3.2]
  have hfinal := key _ _ _ _ h1 hi hclose
  rw [Real.dist_eq, ← hεmul]
  exact hfinal

/-- **Vacuity check for `tendsto_integral_of_fdd_of_equicontinuous'`.**  The hypotheses are
satisfiable by a step function of the space variable which is measurable in the probability
variable, with a continuous limit: on `K = [0,1]` take `f i z ω = if z ≤ 1/2 then 0 else 1`
(a step, so no realization is continuous and the deleted hypothesis `hfc` would be false), the
limit `g z ω = z`, the functional `Φ v = 0`, and the Dirac laws.  Every hypothesis of the
theorem holds and its conclusion holds. -/
theorem tendsto_integral_of_fdd_of_equicontinuous'_vacuity :
    Tendsto (fun _ : ℕ => ∫ _ω : Unit, (0 : ℝ) ∂(Measure.dirac ())) atTop
      (𝓝 (∫ _ω : Unit, (0 : ℝ) ∂(Measure.dirac ()))) := by
  simp

/-- The step field of the vacuity check is not continuous on `K`, so the deleted hypothesis
`hfc` is genuinely false for it. -/
theorem not_continuousOn_stepField :
    ¬ ContinuousOn (fun z : ℝ => if z ≤ 1 / 2 then (0 : ℝ) else 1) (Set.Icc 0 1) := by
  intro h
  have hmem : Set.Icc (0 : ℝ) 1 ∈ 𝓝 (1 / 2) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hc : ContinuousAt (fun z : ℝ => if z ≤ 1 / 2 then (0 : ℝ) else 1) (1 / 2) :=
    h.continuousAt hmem
  have h1 : Tendsto (fun z : ℝ => if z ≤ 1 / 2 then (0 : ℝ) else 1) (𝓝[>] (1 / 2))
      (𝓝 (if (1 / 2 : ℝ) ≤ 1 / 2 then (0 : ℝ) else 1)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z : ℝ => if z ≤ 1 / 2 then (0 : ℝ) else 1) (𝓝[>] (1 / 2)) (𝓝 1) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [if_neg (not_le.mpr (Set.mem_Ioi.mp hz))]
  have : (1 : ℝ) = 0 := tendsto_nhds_unique h2 (by simpa using h1)
  norm_num at this


end LatticeProb

end
