/-
Finite-dimensional convergence and equicontinuity with an additional random block.
The block is retained in each finite-net approximation, so the resulting functional
converges jointly with that block without identifying the two probability spaces.

Moved from Parking-Sharpness.
-/
import Mathlib
import LatticeProb.Prob.FddTight

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb.Scaling.FddBlockTightness

open LatticeProb

variable {E B : Type*} [PseudoMetricSpace E] [PseudoMetricSpace B]

/-- The functional evaluated on a net is continuous jointly in the block and net values. -/
theorem continuous_netFunctional {K : Set E} {m : ℕ} {x : Fin m → E} {η : ℝ}
    (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η) {Φ : B → (E → ℝ) → ℝ}
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : B, ∀ v w : E → ℝ,
      dist a b ≤ δ → (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ a v - Φ b w| ≤ ε) :
    Continuous fun u : B × (Fin m → ℝ) => Φ u.1 (netApprox x η u.2) := by
  refine Metric.continuous_iff.2 ?_
  intro b ε hε
  obtain ⟨δ, hδ, hΦδ⟩ := hΦu (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun a ha => ?_⟩
  rw [Prod.dist_eq] at ha
  have hcoord : ∀ k, |a.2 k - b.2 k| ≤ δ := by
    intro k
    have hk := (dist_le_pi_dist a.2 b.2 k).trans ((le_max_right (dist a.1 b.1) (dist a.2 b.2)))
    rw [Real.dist_eq] at hk
    linarith
  have hz : ∀ z ∈ K, |netApprox x η a.2 z - netApprox x η b.2 z| ≤ δ := fun z hz =>
    abs_netApprox_sub_netApprox_le (tentSum_pos (hnet z hz)) hcoord
  have hfin := hΦδ a.1 b.1 _ _ (((le_max_left (dist a.1 b.1) (dist a.2 b.2))).trans ha.le) hz
  rw [Real.dist_eq]
  linarith

/-- Freeze the block to recover the pathwise modulus used by the net approximation. -/
theorem fixed_block_modulus {K : Set E} {Φ : B → (E → ℝ) → ℝ}
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : B, ∀ v w : E → ℝ,
      dist a b ≤ δ → (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ a v - Φ b w| ≤ ε) (b : B) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : E → ℝ,
      ContinuousOn v K → ContinuousOn w K →
      (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ b v - Φ b w| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hΦu ε hε
  exact ⟨δ, hδ, fun v w _ _ hvw => h b b v w (by simpa using hδ.le) hvw⟩

variable [MeasurableSpace B] [BorelSpace B]

/-- Measurability of the approximation with the random block retained. -/
theorem measurable_netFunctional {Ω : Type*} [MeasurableSpace Ω] {K : Set E} {m : ℕ}
    {x : Fin m → E} {η : ℝ} {F : E → Ω → ℝ} {V : Ω → B}
    {Φ : B → (E → ℝ) → ℝ} (hVm : Measurable V)
    (hFm : ∀ z, Measurable (F z)) (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η)
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : B, ∀ v w : E → ℝ,
      dist a b ≤ δ → (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ a v - Φ b w| ≤ ε) :
    Measurable fun ω => Φ (V ω) (netApprox x η (fun k => F (x k) ω)) :=
  (continuous_netFunctional hnet hΦu).measurable.comp
    (hVm.prodMk (measurable_pi_lambda _ fun k => hFm (x k)))

/-- The continuous limit field admits a fine net with small expectation error, jointly
with the block. -/
theorem exists_net_integral_close {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {K : Set E} (hK : IsCompact K) {g : E → Ω' → ℝ}
    {V : Ω' → B} {Φ : B → (E → ℝ) → ℝ} {M : ℝ}
    (hVm : Measurable V) (hgm : ∀ z, Measurable (g z))
    (hgc : ∀ ω, ContinuousOn (fun z => g z ω) K) (hΦb : ∀ b v, |Φ b v| ≤ M)
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : B, ∀ v w : E → ℝ,
      dist a b ≤ δ → (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ a v - Φ b w| ≤ ε)
    {ε η₀ : ℝ} (hε : 0 < ε) (hη₀ : 0 < η₀) :
    ∃ (m : ℕ) (x : Fin m → E) (η : ℝ), 0 < η ∧ η ≤ η₀ ∧ (∀ k, x k ∈ K) ∧
      (∀ y ∈ K, ∃ k, dist (x k) y < η) ∧
      |∫ ω, Φ (V ω) (netApprox x η (fun k => g (x k) ω)) ∂Q
        - ∫ ω, Φ (V ω) (fun z => g z ω) ∂Q| ≤ ε := by
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
      Measurable fun ω => Φ (V ω)
        (netApprox (x n) (η₀ / (n + 1)) (fun k => g (x n k) ω)) :=
    fun n => measurable_netFunctional hVm hgm (hnet n) hΦu
  have hlim : Tendsto
      (fun n : ℕ => ∫ ω, Φ (V ω)
        (netApprox (x n) (η₀ / (n + 1)) (fun k => g (x n k) ω)) ∂Q) atTop
      (𝓝 (∫ ω, Φ (V ω) (fun z => g z ω) ∂Q)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun n => (hmeas n).aestronglyMeasurable) (integrable_const M)
      (fun n => Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hΦb _ _)
      (Filter.Eventually.of_forall fun ω => ?_)
    exact tendsto_netFunctional hK (hgc ω) (fixed_block_modulus hΦu (V ω)) hxK hnet hr0
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
  refine ⟨m N, x N, η₀ / (N + 1), hrpos N, hrle N, hxK N, hnet N, ?_⟩
  have h := hN N le_rfl
  rw [Real.dist_eq] at h
  exact h.le


variable [Nonempty B]

omit [PseudoMetricSpace B] [MeasurableSpace B] [BorelSpace B] in
/-- The net error is small in expectation while the block remains unchanged. -/
theorem abs_integral_netFunctional_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {K : Set E} {m : ℕ} {x : Fin m → E} {η δ ε ρ M : ℝ}
    {F : E → Ω → ℝ} {V : Ω → B} {Φ : B → (E → ℝ) → ℝ}
    (hxK : ∀ k, x k ∈ K) (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η)
    (hΦb : ∀ b v, |Φ b v| ≤ M) (hδ : 0 ≤ δ)
    (hΦδ : ∀ b : B, ∀ v w : E → ℝ,
      (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ b v - Φ b w| ≤ ε)
    (hm1 : Measurable fun ω => Φ (V ω) (netApprox x η (fun k => F (x k) ω)))
    (hm2 : Measurable fun ω => Φ (V ω) (fun z => F z ω)) (hρ : 0 ≤ ρ)
    (hbad : P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} ≤ ENNReal.ofReal ρ) :
    |∫ ω, Φ (V ω) (netApprox x η (fun k => F (x k) ω)) ∂P - ∫ ω, Φ (V ω) (fun z => F z ω) ∂P|
      ≤ ε + 2 * M * ρ := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hΦb (Classical.arbitrary B) fun _ => 0)
  have hε : 0 ≤ ε := by
    have h := hΦδ (Classical.arbitrary B) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (by intro z _; simpa using hδ)
    simpa using h
  set A := toMeasurable P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} with hA
  have hAm : MeasurableSet A := measurableSet_toMeasurable _ _
  have hAsub : {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} ⊆ A :=
    subset_toMeasurable _ _
  have hAmeas : P A = P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} :=
    measure_toMeasurable _
  have hi1 : Integrable (fun ω => Φ (V ω) (netApprox x η (fun k => F (x k) ω))) P :=
    Integrable.of_bound hm1.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hΦb _ _)
  have hi2 : Integrable (fun ω => Φ (V ω) (fun z => F z ω)) P :=
    Integrable.of_bound hm2.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hΦb _ _)
  have hib : Integrable (fun ω => ε + A.indicator (fun _ => 2 * M) ω) P :=
    (integrable_const ε).add ((integrable_const (2 * M)).indicator hAm)
  have hpt : ∀ ω, |Φ (V ω) (netApprox x η (fun k => F (x k) ω)) - Φ (V ω) (fun z => F z ω)|
      ≤ ε + A.indicator (fun _ => 2 * M) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have h1 : |Φ (V ω) (netApprox x η fun k => F (x k) ω)| ≤ M := hΦb _ _
      have h2 : |Φ (V ω) fun z => F z ω| ≤ M := hΦb _ _
      have h3 := abs_sub (Φ (V ω) (netApprox x η fun k => F (x k) ω)) (Φ (V ω) fun z => F z ω)
      linarith [abs_sub_abs_le_abs_sub (Φ (V ω) (netApprox x η fun k => F (x k) ω)) (Φ (V ω) fun z => F z ω)]
    · rw [Set.indicator_of_notMem hω, add_zero]
      have hmod : ∀ z ∈ K, ∀ y ∈ K, dist z y < η → |F z ω - F y ω| ≤ δ := by
        intro z hz y hy hzy
        by_contra hcon
        exact hω (hAsub ⟨z, hz, y, hy, hzy, lt_of_not_ge hcon⟩)
      exact abs_netFunctional_sub_le' hxK hnet hmod (hΦδ (V ω))
  calc |∫ ω, Φ (V ω) (netApprox x η (fun k => F (x k) ω)) ∂P - ∫ ω, Φ (V ω) (fun z => F z ω) ∂P|
      = |∫ ω, (Φ (V ω) (netApprox x η (fun k => F (x k) ω)) - Φ (V ω) (fun z => F z ω)) ∂P| := by
        rw [integral_sub hi1 hi2]
    _ ≤ ∫ ω, |Φ (V ω) (netApprox x η (fun k => F (x k) ω)) - Φ (V ω) (fun z => F z ω)| ∂P :=
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




omit [Nonempty B] in
/-- Joint finite-dimensional laws control bounded continuous tests of the block and net. -/
theorem tendsto_integral_of_tendstoInDistribution {ι : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {L : Filter ι} {m : ℕ}
    {X : (i : ι) → Ω i → (B × (Fin m → ℝ))} {Z : Ω' → (B × (Fin m → ℝ))}
    (h : TendstoInDistribution X L Z P Q) {ψ : (B × (Fin m → ℝ)) → ℝ} (hc : Continuous ψ)
    {M : ℝ} (hb : ∀ u, |ψ u| ≤ M) :
    Tendsto (fun i => ∫ ω, ψ (X i ω) ∂(P i)) L (𝓝 (∫ ω, ψ (Z ω) ∂Q)) := by
  have hψ : ∀ u : B × (Fin m → ℝ), ‖ψ u‖ ≤ M := fun u => by
    simpa [Real.norm_eq_abs] using hb u
  have hconv := (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h.tendsto)
    (BoundedContinuousFunction.ofNormedAddCommGroup ψ hc M hψ)
  have hZ : ∫ v, ψ v ∂(Q.map Z) = ∫ ω, ψ (Z ω) ∂Q :=
    integral_map h.aemeasurable_limit hc.aestronglyMeasurable
  have hX : ∀ i, ∫ v, ψ v ∂((P i).map (X i)) = ∫ ω, ψ (X i ω) ∂(P i) :=
    fun i => integral_map (h.forall_aemeasurable i) hc.aestronglyMeasurable
  simpa [MeasureTheory.ProbabilityMeasure.coe_mk,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup, hX, hZ] using hconv


/-- Equicontinuity upgrades joint finite-dimensional convergence to convergence of a
bounded uniformly continuous block-and-path functional. Pre-limit paths may be discontinuous. -/
theorem tendsto_integral_of_fdd_of_equicontinuous
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {L : Filter ι}
    {f : (i : ι) → E → Ω i → ℝ} {g : E → Ω' → ℝ} {K : Set E} (hK : IsCompact K)
    {V : (i : ι) → Ω i → B} {Vlim : Ω' → B}
    {Φ : B → (E → ℝ) → ℝ}
    (hVm : ∀ᶠ i in L, Measurable (V i)) (hVlimm : Measurable Vlim)
    (hfm : ∀ᶠ i in L, ∀ z, Measurable (f i z)) (hgm : ∀ z, Measurable (g z))
    (hgc : ∀ ω, ContinuousOn (fun z => g z ω) K)
    (hfΦm : ∀ᶠ i in L, Measurable fun ω => Φ (V i ω) (fun z => f i z ω))
    (hfdd : ∀ (m : ℕ) (x : Fin m → E), (∀ k, x k ∈ K) →
      TendstoInDistribution (fun i ω => (V i ω, fun k => f i (x k) ω)) L
        (fun ω => (Vlim ω, fun k => g (x k) ω)) P Q)
    (htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in L,
      P i {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧ η < |f i z ω - f i y ω|} ≤ ENNReal.ofReal ε)
    {M : ℝ} (hΦb : ∀ b v, |Φ b v| ≤ M)
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : B, ∀ v w : E → ℝ,
      dist a b ≤ δ → (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ a v - Φ b w| ≤ ε) :
    Tendsto (fun i => ∫ ω, Φ (V i ω) (fun z => f i z ω) ∂(P i)) L
      (𝓝 (∫ ω, Φ (Vlim ω) (fun z => g z ω) ∂Q)) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hΦb (Classical.arbitrary B) fun _ => 0)
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
    exists_net_integral_close (Q := Q) hK hVlimm hgm hgc hΦb hΦu hε hη₀
  have hψc : Continuous fun u : B × (Fin m → ℝ) => Φ u.1 (netApprox x η u.2) :=
    continuous_netFunctional hnet hΦu
  have hfdd2 := tendsto_integral_of_tendstoInDistribution (hfdd m x hxK) hψc
    (M := M) (fun u => hΦb _ _)
  have hev : ∀ᶠ i in L, |∫ ω, Φ (V i ω) (netApprox x η (fun k => f i (x k) ω)) ∂(P i)
      - ∫ ω, Φ (Vlim ω) (netApprox x η (fun k => g (x k) ω)) ∂Q| < ε := by
    have h := Metric.tendsto_nhds.1 hfdd2 ε hε
    simpa [Real.dist_eq] using h
  filter_upwards [hev, htightη, hVm, hfm, hfΦm] with i hi htighti hVmi hfmi hfΦmi
  have hbadi : P i {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |f i z ω - f i y ω|}
      ≤ ENNReal.ofReal ε := by
    refine le_trans (measure_mono ?_) htighti
    rintro ω ⟨z, hz, y, hy, hzy, hval⟩
    exact ⟨z, hz, y, hy, lt_of_lt_of_le hzy hηle, hval⟩
  have h1 := abs_integral_netFunctional_sub_le (P := P i) (F := f i) (V := V i)
    hxK hnet hΦb hδ.le
    (fun b v w hvw => hΦδ b b v w (by simpa using hδ.le) hvw)
    (measurable_netFunctional hVmi hfmi hnet hΦu)
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



omit [PseudoMetricSpace B] [MeasurableSpace B] [BorelSpace B] [Nonempty B] in
/-- A uniformly continuous finite vector of path functionals converges jointly with
an additional finite real block. -/
theorem tendstoInDistribution_block_functional
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {Ω' : Type*} [MeasurableSpace Ω']
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {L : Filter ι} [L.IsCountablyGenerated] {n p : ℕ}
    {f : (i : ι) → E → Ω i → ℝ} {g : E → Ω' → ℝ}
    {V : (i : ι) → Ω i → (Fin n → ℝ)} {Vlim : Ω' → (Fin n → ℝ)}
    {K : Set E} (hK : IsCompact K) {H : (E → ℝ) → (Fin p → ℝ)}
    (hVm : ∀ i, Measurable (V i)) (hVlimm : Measurable Vlim)
    (hfm : ∀ᶠ i in L, ∀ z, Measurable (f i z)) (hgm : ∀ z, Measurable (g z))
    (hgc : ∀ ω, ContinuousOn (fun z => g z ω) K)
    (hfHm : ∀ i, Measurable fun ω => H (fun z => f i z ω))
    (hgHm : Measurable fun ω => H (fun z => g z ω))
    (hfdd : ∀ (m : ℕ) (x : Fin m → E), (∀ k, x k ∈ K) →
      TendstoInDistribution (fun i ω => (V i ω, fun k => f i (x k) ω)) L
        (fun ω => (Vlim ω, fun k => g (x k) ω)) P Q)
    (htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in L,
      P i {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧ η < |f i z ω - f i y ω|} ≤ ENNReal.ofReal ε)
    (hHu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : E → ℝ,
      (∀ z ∈ K, |v z - w z| ≤ δ) → dist (H v) (H w) ≤ ε) :
    TendstoInDistribution (fun i ω => (V i ω, H (fun z => f i z ω))) L
      (fun ω => (Vlim ω, H (fun z => g z ω))) P Q := by
  refine ⟨fun i => ((hVm i).prodMk (hfHm i)).aemeasurable,
    (hVlimm.prodMk hgHm).aemeasurable, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  intro F hFb hFlip
  obtain ⟨M, hM⟩ := hFb
  obtain ⟨LF, hLF⟩ := hFlip
  have hbound : ∀ y, |F y| ≤ M + |F 0| := by
    intro y
    have hd0 := hM y 0
    rw [Real.dist_eq] at hd0
    linarith [abs_sub_abs_le_abs_sub (F y) (F 0)]
  have hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ a b : Fin n → ℝ, ∀ v w : E → ℝ,
        dist a b ≤ δ → (∀ z ∈ K, |v z - w z| ≤ δ) →
        |F (a, H v) - F (b, H w)| ≤ ε := by
    intro ε hε
    let η : ℝ := ε / ((LF : ℝ) + 1)
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨δ, hδ, hHδ⟩ := hHu η hη
    refine ⟨min δ η, lt_min hδ hη, fun a b v w hab hvw => ?_⟩
    have hdist : dist (a, H v) (b, H w) ≤ η := by
      rw [Prod.dist_eq]
      exact max_le (hab.trans (min_le_right _ _))
        (hHδ v w fun z hz => (hvw z hz).trans (min_le_left _ _))
    have hF := hLF.dist_le_mul (a, H v) (b, H w)
    rw [Real.dist_eq] at hF
    have hmul : (LF : ℝ) * η ≤ ε := by
      dsimp [η]
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (LF : ℝ) + 1)]
      nlinarith [LF.coe_nonneg]
    exact hF.trans ((mul_le_mul_of_nonneg_left hdist LF.coe_nonneg).trans hmul)
  have hcore := tendsto_integral_of_fdd_of_equicontinuous hK
    (Filter.Eventually.of_forall hVm) hVlimm hfm hgm hgc
    (Filter.Eventually.of_forall fun i => hLF.continuous.measurable.comp
      ((hVm i).prodMk (hfHm i))) hfdd htight (fun b v => hbound (b, H v)) hmod
  have hmap1 : ∀ i, ∫ y, F y ∂((P i).map (fun ω => (V i ω, H (fun z => f i z ω))))
      = ∫ ω, F (V i ω, H (fun z => f i z ω)) ∂P i := fun i =>
    integral_map ((hVm i).prodMk (hfHm i)).aemeasurable hLF.continuous.aestronglyMeasurable
  have hmap2 : ∫ y, F y ∂(Q.map (fun ω => (Vlim ω, H (fun z => g z ω))))
      = ∫ ω, F (Vlim ω, H (fun z => g z ω)) ∂Q :=
    integral_map (hVlimm.prodMk hgHm).aemeasurable hLF.continuous.aestronglyMeasurable
  simpa only [ProbabilityMeasure.coe_mk, hmap1, hmap2] using hcore

end LatticeProb.Scaling.FddBlockTightness

namespace LatticeProb.Scaling.FddBlockTightness

variable {E : Type*} [PseudoMetricSpace E]

/-! ### The deterministic bridge, with the extra block held exact -/

/-- A joint modulus of uniform continuity for `Φ`, restricted to the case where the block
argument does not move, is a modulus for the curried functional `Φ v`. -/
theorem hΦu_at_of_joint {K : Set E} {n : ℕ} {Φ : (Fin n → ℝ) → (E → ℝ) → ℝ}
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v1 v2 : Fin n → ℝ, ∀ w1 w2 : E → ℝ,
      ContinuousOn w1 K → ContinuousOn w2 K →
      (∀ j, |v1 j - v2 j| ≤ δ) → (∀ z ∈ K, |w1 z - w2 z| ≤ δ) → |Φ v1 w1 - Φ v2 w2| ≤ ε)
    (v0 : Fin n → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ w1 w2 : E → ℝ,
      ContinuousOn w1 K → ContinuousOn w2 K → (∀ z ∈ K, |w1 z - w2 z| ≤ δ) → |Φ v0 w1 - Φ v0 w2| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hΦu ε hε
  exact ⟨δ, hδ, fun w1 w2 hw1 hw2 hle => h v0 v0 w1 w2 hw1 hw2 (fun j => by simpa using hδ.le) hle⟩

/-- **Convergence in distribution moves expectations of bounded continuous functions**, at an
arbitrary target type carrying the topology/measurability `TendstoInDistribution` itself needs
(not hard-wired to `Fin m → ℝ`, since here the target is the product of the block and a finite
tuple of field evaluations). A straight generalization of `LatticeProb.
tendsto_integral_of_tendstoInDistribution`: its proof uses nothing about `Fin m → ℝ` beyond
these two instances. -/
theorem tendsto_integral_of_tendstoInDistribution_generic {ι : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {L : Filter ι}
    {F : Type*} [TopologicalSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {X : (i : ι) → Ω i → F} {Z : Ω' → F}
    (h : TendstoInDistribution X L Z P Q) {ψ : F → ℝ} (hc : Continuous ψ)
    {M : ℝ} (hb : ∀ u, |ψ u| ≤ M) :
    Tendsto (fun i => ∫ ω, ψ (X i ω) ∂(P i)) L (𝓝 (∫ ω, ψ (Z ω) ∂Q)) := by
  have hψ : ∀ u : F, ‖ψ u‖ ≤ M := fun u => by
    simpa [Real.norm_eq_abs] using hb u
  have hconv := (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h.tendsto)
    (BoundedContinuousFunction.ofNormedAddCommGroup ψ hc M hψ)
  have hZ : ∫ v, ψ v ∂(Q.map Z) = ∫ ω, ψ (Z ω) ∂Q :=
    integral_map h.aemeasurable_limit hc.aestronglyMeasurable
  have hX : ∀ i, ∫ v, ψ v ∂((P i).map (X i)) = ∫ ω, ψ (X i ω) ∂(P i) :=
    fun i => integral_map (h.forall_aemeasurable i) hc.aestronglyMeasurable
  simpa [MeasureTheory.ProbabilityMeasure.coe_mk,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup, hX, hZ] using hconv

/-- A joint modulus with no continuity restriction is one with a continuity restriction. -/
theorem hΦu_of_continuousOn2 {K : Set E} {n : ℕ} {Φ : (Fin n → ℝ) → (E → ℝ) → ℝ}
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v1 v2 : Fin n → ℝ, ∀ w1 w2 : E → ℝ,
      (∀ j, |v1 j - v2 j| ≤ δ) → (∀ z ∈ K, |w1 z - w2 z| ≤ δ) → |Φ v1 w1 - Φ v2 w2| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v1 v2 : Fin n → ℝ, ∀ w1 w2 : E → ℝ,
      ContinuousOn w1 K → ContinuousOn w2 K →
      (∀ j, |v1 j - v2 j| ≤ δ) → (∀ z ∈ K, |w1 z - w2 z| ≤ δ) → |Φ v1 w1 - Φ v2 w2| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hΦu ε hε
  exact ⟨δ, hδ, fun v1 v2 w1 w2 _ _ hv hw => h v1 v2 w1 w2 hv hw⟩

/-- **The block-and-net functional is jointly continuous.**  The block coordinate is exact
(no net-approximation), the field coordinate is interpolated from a finite net; a joint
uniform-continuity modulus for `Φ` makes their composite continuous in the finite-dimensional
pair. -/
theorem continuous_netFunctional2 {K : Set E} {n m : ℕ} {x : Fin m → E} {η : ℝ}
    (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η) {Φ : (Fin n → ℝ) → (E → ℝ) → ℝ}
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v1 v2 : Fin n → ℝ, ∀ w1 w2 : E → ℝ,
      ContinuousOn w1 K → ContinuousOn w2 K →
      (∀ j, |v1 j - v2 j| ≤ δ) → (∀ z ∈ K, |w1 z - w2 z| ≤ δ) → |Φ v1 w1 - Φ v2 w2| ≤ ε) :
    Continuous fun p : (Fin n → ℝ) × (Fin m → ℝ) => Φ p.1 (LatticeProb.netApprox x η p.2) := by
  refine Metric.continuous_iff.2 ?_
  intro b ε hε
  obtain ⟨δ, hδ, hΦδ⟩ := hΦu (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have hab1 : dist a.1 b.1 ≤ dist a b := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hab2 : dist a.2 b.2 ≤ dist a b := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  have hcoord1 : ∀ j, |a.1 j - b.1 j| ≤ δ := by
    intro j
    have hk : dist (a.1 j) (b.1 j) ≤ dist a.1 b.1 := dist_le_pi_dist a.1 b.1 j
    have := hk.trans (hab1.trans ha.le)
    rwa [Real.dist_eq] at this
  have hcoord2 : ∀ k, |a.2 k - b.2 k| ≤ δ := by
    intro k
    have hk : dist (a.2 k) (b.2 k) ≤ dist a.2 b.2 := dist_le_pi_dist a.2 b.2 k
    have := hk.trans (hab2.trans ha.le)
    rwa [Real.dist_eq] at this
  have hz : ∀ z ∈ K, |LatticeProb.netApprox x η a.2 z - LatticeProb.netApprox x η b.2 z| ≤ δ :=
    fun z hz => LatticeProb.abs_netApprox_sub_netApprox_le (LatticeProb.tentSum_pos (hnet z hz))
      hcoord2
  have hfin := hΦδ a.1 b.1 (LatticeProb.netApprox x η a.2) (LatticeProb.netApprox x η b.2)
    (LatticeProb.continuousOn_netApprox a.2 hnet) (LatticeProb.continuousOn_netApprox b.2 hnet)
    hcoord1 hz
  rw [Real.dist_eq]
  linarith

/-- **The block-and-net functional is measurable** in a random pair of the block and the
field's coordinates on a finite net. -/
theorem measurable_netFunctional2 {Ω : Type*} [MeasurableSpace Ω] {K : Set E} {n m : ℕ}
    {x : Fin m → E} {η : ℝ} {V : Ω → Fin n → ℝ} {F : E → Ω → ℝ} {Φ : (Fin n → ℝ) → (E → ℝ) → ℝ}
    (hVm : Measurable V) (hFm : ∀ z, Measurable (F z)) (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η)
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v1 v2 : Fin n → ℝ, ∀ w1 w2 : E → ℝ,
      ContinuousOn w1 K → ContinuousOn w2 K →
      (∀ j, |v1 j - v2 j| ≤ δ) → (∀ z ∈ K, |w1 z - w2 z| ≤ δ) → |Φ v1 w1 - Φ v2 w2| ≤ ε) :
    Measurable fun ω => Φ (V ω) (LatticeProb.netApprox x η (fun k => F (x k) ω)) :=
  (continuous_netFunctional2 hnet hΦu).measurable.comp
    (hVm.prodMk (measurable_pi_lambda _ fun k => hFm (x k)))

/-- **The interpolation error in expectation, with the block held exact.**  Off the event that
`F` varies by more than `δ` between two points of `K` at distance less than `η`, the
interpolated functional (at the SAME block value) is within `ε` of the functional of the path;
on that event the two differ by at most `2M`. -/
theorem abs_integral_netFunctional_sub_le2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {K : Set E} {n m : ℕ} {x : Fin m → E} {η δ ε ρ M : ℝ}
    {V : Ω → Fin n → ℝ} {F : E → Ω → ℝ} {Φ : (Fin n → ℝ) → (E → ℝ) → ℝ}
    (hxK : ∀ k, x k ∈ K) (hnet : ∀ y ∈ K, ∃ k, dist (x k) y < η)
    (hΦb : ∀ v w, |Φ v w| ≤ M) (hδ : 0 ≤ δ)
    (hΦδ : ∀ v : Fin n → ℝ, ∀ w1 w2 : E → ℝ,
      (∀ z ∈ K, |w1 z - w2 z| ≤ δ) → |Φ v w1 - Φ v w2| ≤ ε)
    (hm1 : Measurable fun ω => Φ (V ω) (LatticeProb.netApprox x η (fun k => F (x k) ω)))
    (hm2 : Measurable fun ω => Φ (V ω) (fun z => F z ω)) (hρ : 0 ≤ ρ)
    (hbad : P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} ≤ ENNReal.ofReal ρ) :
    |∫ ω, Φ (V ω) (LatticeProb.netApprox x η (fun k => F (x k) ω)) ∂P
        - ∫ ω, Φ (V ω) (fun z => F z ω) ∂P|
      ≤ ε + 2 * M * ρ := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hΦb (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)))
  have hε : 0 ≤ ε := by
    have h := hΦδ (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (by intro z _; simpa using hδ)
    simpa using h
  set A := toMeasurable P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} with hA
  have hAm : MeasurableSet A := measurableSet_toMeasurable _ _
  have hAsub : {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} ⊆ A :=
    subset_toMeasurable _ _
  have hAmeas : P A = P {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |F z ω - F y ω|} :=
    measure_toMeasurable _
  have hi1 : Integrable (fun ω => Φ (V ω) (LatticeProb.netApprox x η (fun k => F (x k) ω))) P :=
    Integrable.of_bound hm1.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hΦb _ _)
  have hi2 : Integrable (fun ω => Φ (V ω) (fun z => F z ω)) P :=
    Integrable.of_bound hm2.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hΦb _ _)
  have hib : Integrable (fun ω => ε + A.indicator (fun _ => 2 * M) ω) P :=
    (integrable_const ε).add ((integrable_const (2 * M)).indicator hAm)
  have hpt : ∀ ω, |Φ (V ω) (LatticeProb.netApprox x η (fun k => F (x k) ω))
        - Φ (V ω) (fun z => F z ω)|
      ≤ ε + A.indicator (fun _ => 2 * M) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have h1 : |Φ (V ω) (LatticeProb.netApprox x η fun k => F (x k) ω)| ≤ M := hΦb _ _
      have h2 : |Φ (V ω) fun z => F z ω| ≤ M := hΦb _ _
      have h3 := abs_sub (Φ (V ω) (LatticeProb.netApprox x η fun k => F (x k) ω))
        (Φ (V ω) fun z => F z ω)
      linarith
    · rw [Set.indicator_of_notMem hω, add_zero]
      have hmod : ∀ z ∈ K, ∀ y ∈ K, dist z y < η → |F z ω - F y ω| ≤ δ := by
        intro z hz y hy hzy
        by_contra hcon
        exact hω (hAsub ⟨z, hz, y, hy, hzy, lt_of_not_ge hcon⟩)
      exact LatticeProb.abs_netFunctional_sub_le' hxK hnet hmod (hΦδ (V ω))
  calc |∫ ω, Φ (V ω) (LatticeProb.netApprox x η (fun k => F (x k) ω)) ∂P
        - ∫ ω, Φ (V ω) (fun z => F z ω) ∂P|
      = |∫ ω, (Φ (V ω) (LatticeProb.netApprox x η (fun k => F (x k) ω))
          - Φ (V ω) (fun z => F z ω)) ∂P| := by
        rw [integral_sub hi1 hi2]
    _ ≤ ∫ ω, |Φ (V ω) (LatticeProb.netApprox x η (fun k => F (x k) ω)) - Φ (V ω) (fun z => F z ω)|
          ∂P := abs_integral_le_integral_abs
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

/-- **A net fine enough for the limit process, with the block held exact.** -/
theorem exists_net_integral_close2 {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {K : Set E} (hK : IsCompact K) {n : ℕ} {Vlim : Ω' → Fin n → ℝ}
    {g : E → Ω' → ℝ} {Φ : (Fin n → ℝ) → (E → ℝ) → ℝ} {M : ℝ}
    (hVlimm : Measurable Vlim) (hgm : ∀ z, Measurable (g z))
    (hgc : ∀ ω, ContinuousOn (fun z => g z ω) K) (hΦb : ∀ v w, |Φ v w| ≤ M)
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v1 v2 : Fin n → ℝ, ∀ w1 w2 : E → ℝ,
      ContinuousOn w1 K → ContinuousOn w2 K →
      (∀ j, |v1 j - v2 j| ≤ δ) → (∀ z ∈ K, |w1 z - w2 z| ≤ δ) → |Φ v1 w1 - Φ v2 w2| ≤ ε)
    {ε η₀ : ℝ} (hε : 0 < ε) (hη₀ : 0 < η₀) :
    ∃ (m : ℕ) (x : Fin m → E) (η : ℝ), 0 < η ∧ η ≤ η₀ ∧ (∀ k, x k ∈ K) ∧
      (∀ y ∈ K, ∃ k, dist (x k) y < η) ∧
      |∫ ω, Φ (Vlim ω) (LatticeProb.netApprox x η (fun k => g (x k) ω)) ∂Q
          - ∫ ω, Φ (Vlim ω) (fun z => g z ω) ∂Q| ≤ ε := by
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
  choose mN x hxK hnet using fun k : ℕ => LatticeProb.exists_net hK (hrpos k)
  have hmeas : ∀ k : ℕ,
      Measurable fun ω => Φ (Vlim ω)
        (LatticeProb.netApprox (x k) (η₀ / (k + 1)) (fun j => g (x k j) ω)) :=
    fun k => measurable_netFunctional2 hVlimm hgm (hnet k) hΦu
  have hlim : Tendsto
      (fun k : ℕ => ∫ ω, Φ (Vlim ω)
        (LatticeProb.netApprox (x k) (η₀ / (k + 1)) (fun j => g (x k j) ω)) ∂Q) atTop
      (𝓝 (∫ ω, Φ (Vlim ω) (fun z => g z ω) ∂Q)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun k => (hmeas k).aestronglyMeasurable) (integrable_const M)
      (fun k => Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hΦb _ _)
      (Filter.Eventually.of_forall fun ω => ?_)
    exact LatticeProb.tendsto_netFunctional hK (hgc ω) (hΦu_at_of_joint hΦu (Vlim ω)) hxK hnet hr0
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
  refine ⟨mN N, x N, η₀ / (N + 1), hrpos N, hrle N, hxK N, hnet N, ?_⟩
  have h := hN N le_rfl
  rw [Real.dist_eq] at h
  exact h.le

/-! ### The theorem -/

/-- **From the finite-dimensional laws and equicontinuity in probability, WITH AN EXTRA
FINITE-DIMENSIONAL BLOCK, to the expectation of a joint functional of the block and the whole
path.**

This carries `LatticeProb.tendsto_integral_of_fdd_of_equicontinuous'` through its own
net-approximation argument alongside an extra jointly finite-dimensional-convergent block `V`.
The block is never net-approximated (it is already finite-dimensional, so no interpolation
error is needed for it): only the field `f` is approximated on a net, exactly as in the
un-blocked theorem, and `V`/`Vlim` ride along unchanged at every step.

Two joint-convergence facts of two structurally different kinds (a finite family, and the fdd
convergence of a field on a compact set) do not combine along a shared marginal in general (the
classical marginal problem); this theorem is the genuine new content needed to combine them,
by verifying `hjointfdd` directly at every finite point tuple with the block folded in. -/
theorem tendsto_integral_of_fdd_of_equicontinuous_with_block
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {L : Filter ι} {n : ℕ}
    {V : (i : ι) → Ω i → Fin n → ℝ} {Vlim : Ω' → Fin n → ℝ}
    {f : (i : ι) → E → Ω i → ℝ} {g : E → Ω' → ℝ} {K : Set E} (hK : IsCompact K)
    {Φ : (Fin n → ℝ) → (E → ℝ) → ℝ}
    (hfm : ∀ᶠ i in L, ∀ z, Measurable (f i z)) (hgm : ∀ z, Measurable (g z))
    (hVm : ∀ᶠ i in L, Measurable (V i)) (hVlimm : Measurable Vlim)
    (hgc : ∀ ω, ContinuousOn (fun z => g z ω) K)
    (hfΦm : ∀ᶠ i in L, Measurable fun ω => Φ (V i ω) (fun z => f i z ω))
    (hjointfdd : ∀ (m : ℕ) (x : Fin m → E), (∀ k, x k ∈ K) →
      TendstoInDistribution (fun i ω => (V i ω, fun k => f i (x k) ω)) L
        (fun ω => (Vlim ω, fun k => g (x k) ω)) P Q)
    (htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in L,
      P i {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧ η < |f i z ω - f i y ω|} ≤ ENNReal.ofReal ε)
    {M : ℝ} (hΦb : ∀ v w, |Φ v w| ≤ M)
    (hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v1 v2 : Fin n → ℝ, ∀ w1 w2 : E → ℝ,
      (∀ j, |v1 j - v2 j| ≤ δ) → (∀ z ∈ K, |w1 z - w2 z| ≤ δ) → |Φ v1 w1 - Φ v2 w2| ≤ ε) :
    Tendsto (fun i => ∫ ω, Φ (V i ω) (fun z => f i z ω) ∂(P i)) L
      (𝓝 (∫ ω, Φ (Vlim ω) (fun z => g z ω) ∂Q)) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hΦb (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)))
  refine Metric.tendsto_nhds.2 ?_
  intro ε₀ hε₀
  have hden : (0 : ℝ) < 4 + 2 * M := by linarith
  set ε := ε₀ / (4 + 2 * M) with hεdef
  have hε : 0 < ε := by positivity
  have hne : (4 + 2 * M) ≠ 0 := ne_of_gt hden
  have hεmul : (4 + 2 * M) * ε = ε₀ := by
    rw [hεdef]; field_simp
  obtain ⟨δ, hδ, hΦδjoint⟩ := hΦu ε hε
  have hΦδ : ∀ v : Fin n → ℝ, ∀ w1 w2 : E → ℝ,
      (∀ z ∈ K, |w1 z - w2 z| ≤ δ) → |Φ v w1 - Φ v w2| ≤ ε :=
    fun v w1 w2 h => hΦδjoint v v w1 w2 (fun j => by simpa using hδ.le) h
  obtain ⟨η₀, hη₀, htightη⟩ := htight ε δ hε hδ
  obtain ⟨m, x, η, hη, hηle, hxK, hnet, hclose⟩ :=
    exists_net_integral_close2 (Q := Q) hK hVlimm hgm hgc hΦb (hΦu_of_continuousOn2 hΦu) hε hη₀
  have hψc : Continuous fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
      Φ p.1 (LatticeProb.netApprox x η p.2) :=
    continuous_netFunctional2 hnet (hΦu_of_continuousOn2 hΦu)
  have hfdd2 : Tendsto (fun i => ∫ ω,
      Φ (V i ω) (LatticeProb.netApprox x η (fun k => f i (x k) ω)) ∂(P i)) L
      (𝓝 (∫ ω, Φ (Vlim ω) (LatticeProb.netApprox x η (fun k => g (x k) ω)) ∂Q)) := by
    have := tendsto_integral_of_tendstoInDistribution_generic (hjointfdd m x hxK) hψc
      (M := M) (fun p => hΦb p.1 (LatticeProb.netApprox x η p.2))
    simpa using this
  have hev : ∀ᶠ i in L, |∫ ω, Φ (V i ω) (LatticeProb.netApprox x η (fun k => f i (x k) ω)) ∂(P i)
      - ∫ ω, Φ (Vlim ω) (LatticeProb.netApprox x η (fun k => g (x k) ω)) ∂Q| < ε := by
    have h := Metric.tendsto_nhds.1 hfdd2 ε hε
    simpa [Real.dist_eq] using h
  filter_upwards [hev, htightη, hfm, hfΦm, hVm] with i hi htighti hfmi hfΦmi hVmi
  have hbadi : P i {ω | ∃ z ∈ K, ∃ y ∈ K, dist z y < η ∧ δ < |f i z ω - f i y ω|}
      ≤ ENNReal.ofReal ε := by
    refine le_trans (measure_mono ?_) htighti
    rintro ω ⟨z, hz, y, hy, hzy, hval⟩
    exact ⟨z, hz, y, hy, lt_of_lt_of_le hzy hηle, hval⟩
  have h1 := abs_integral_netFunctional_sub_le2 (P := P i) (V := V i) (F := f i) hxK hnet hΦb
    hδ.le hΦδ (measurable_netFunctional2 hVmi hfmi hnet (hΦu_of_continuousOn2 hΦu))
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

end LatticeProb.Scaling.FddBlockTightness

end
