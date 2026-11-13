import Mathlib

/-!
# Joint continuity of the reversibility pairing on the law-field space

The path space is `C(ℝ≥0, ℂ)` with the compact-open topology and its Borel σ-algebra;
`ProbabilityMeasure C(ℝ≥0, ℂ)` carries the topology of weak convergence, and the law fields
`z ↦ P_z` form `C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))` with the compact-open topology. Finite measures
`ν` on `ℂ` carry the topology of weak convergence.

* `continuous_integral_comp_eval_time`: for a bounded Lipschitz `g : ℂ → ℝ`, `(P, s) ↦ E_P[g(X_s)]`
  is jointly continuous.
* `continuous_integral_comp_eval_lawField`: `(P, s, z) ↦ E_{P_z}[g(X_s)]` is jointly continuous.
* `continuous_reversibilityPairing`: for bounded Lipschitz `f, g` and a continuous compactly supported
  `ψ`, the reversibility pairing
  `(ν, P, s) ↦ ∫ f(z) E_{P_z}[g(X_s)] ψ(z) dν(z) - ∫ g(z) E_{P_z}[f(X_s)] ψ(z) dν(z)`
  is jointly continuous.

The first is an instance of `continuous_integral_probabilityMeasure_of_continuous`: for a uniformly
bounded jointly continuous family `G t` of continuous functions indexed by a proper metric space,
`(P, t) ↦ ∫ G t dP` is continuous. The modulus `x ↦ sup_{t ∈ B̄(t₀, r)} |G t x - G t₀ x|`
(`familyModulus`) is bounded and continuous, and decreases to zero as `r → 0`, so its integral against
`P₀` is small by dominated convergence and stays small for `P` near `P₀`. The third combines the joint
continuity of `(ν, H) ↦ ∫ H dν` for `H` bounded continuous with the uniform norm
(`continuous_integral_finiteMeasure_boundedContinuousFunction`) with the uniform continuity of a jointly
continuous integrand on the compact support of `ψ`
(`continuous_integral_finiteMeasure_of_eq_zero_of_notMem`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped NNReal ENNReal BoundedContinuousFunction

namespace LatticeProb

/-! ### The modulus of a family of functions over a set of parameters -/

/-- The modulus `x ↦ sup_{t ∈ K} |G t x - G t₀ x|` of the family `G` at the parameter `t₀` over the
set of parameters `K`. -/
noncomputable def familyModulus {E T : Type*} (G : T → E → ℝ) (t₀ : T) (K : Set T) (x : E) : ℝ :=
  sSup ((fun t => |G t x - G t₀ x|) '' K)

theorem familyModulus_bddAbove {E T : Type*} {G : T → E → ℝ} {C : ℝ} (hC : ∀ t x, |G t x| ≤ C)
    (t₀ : T) (K : Set T) (x : E) : BddAbove ((fun t => |G t x - G t₀ x|) '' K) := by
  refine ⟨2 * C, ?_⟩
  rintro _ ⟨t, -, rfl⟩
  show |G t x - G t₀ x| ≤ 2 * C
  have h1 := abs_le.1 (hC t x)
  have h2 := abs_le.1 (hC t₀ x)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem le_familyModulus {E T : Type*} {G : T → E → ℝ} {C : ℝ} (hC : ∀ t x, |G t x| ≤ C) (t₀ : T)
    {K : Set T} {t : T} (ht : t ∈ K) (x : E) : |G t x - G t₀ x| ≤ familyModulus G t₀ K x :=
  le_csSup (familyModulus_bddAbove hC t₀ K x) (mem_image_of_mem _ ht)

theorem familyModulus_le_of_forall {E T : Type*} {G : T → E → ℝ} {t₀ : T} {K : Set T}
    (hK : K.Nonempty) {x : E} {a : ℝ} (h : ∀ t ∈ K, |G t x - G t₀ x| ≤ a) :
    familyModulus G t₀ K x ≤ a :=
  csSup_le (hK.image _) (by rintro _ ⟨t, ht, rfl⟩; exact h t ht)

theorem continuous_familyModulus {E T : Type*} [TopologicalSpace E] [TopologicalSpace T]
    {G : T → E → ℝ} (hG : Continuous fun p : T × E => G p.1 p.2) (t₀ : T) {K : Set T}
    (hK : IsCompact K) : Continuous fun x => familyModulus G t₀ K x := by
  have hf : Continuous fun p : E × T => |G p.2 p.1 - G t₀ p.1| :=
    ((hG.comp continuous_swap).sub (hG.comp (continuous_const.prodMk continuous_fst))).abs
  exact hK.continuous_sSup (f := fun x t => |G t x - G t₀ x|) hf

/-! ### Integrals of a jointly continuous family against probability measures -/

/-- For a uniformly bounded family `G t` of functions on `E`, indexed by a proper metric space and
jointly continuous in `(t, x)`, the integral `(P, t) ↦ ∫ G t dP` is jointly continuous on
`ProbabilityMeasure E × T`. -/
theorem continuous_integral_probabilityMeasure_of_continuous {E T : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [PseudoMetricSpace T] [ProperSpace T]
    {G : T → E → ℝ} (hG : Continuous fun p : T × E => G p.1 p.2) {C : ℝ}
    (hC : ∀ t x, |G t x| ≤ C) :
    Continuous fun q : ProbabilityMeasure E × T => ∫ x, G q.2 x ∂(q.1 : Measure E) := by
  have hGt : ∀ t, Continuous (G t) := fun t => hG.comp (continuous_const.prodMk continuous_id)
  let Gb : T → E →ᵇ ℝ := fun t => BoundedContinuousFunction.ofNormedAddCommGroup (G t) (hGt t) C
    (fun x => by rw [Real.norm_eq_abs]; exact hC t x)
  have hint : ∀ (P : ProbabilityMeasure E) t, Integrable (G t) (P : Measure E) :=
    fun P t => (Gb t).integrable _
  have hweak : ∀ (P₀ : ProbabilityMeasure E) (f : E →ᵇ ℝ),
      Tendsto (fun P : ProbabilityMeasure E => ∫ x, f x ∂(P : Measure E)) (𝓝 P₀)
        (𝓝 (∫ x, f x ∂(P₀ : Measure E))) :=
    fun _ f => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 tendsto_id f
  rw [continuous_iff_continuousAt]
  rintro ⟨P₀, t₀⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hr : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hne : ∀ n : ℕ, (closedBall t₀ (1 / ((n : ℝ) + 1))).Nonempty :=
    fun n => nonempty_closedBall.2 (hr n).le
  let ω : ℕ → E → ℝ := fun n x => familyModulus G t₀ (closedBall t₀ (1 / ((n : ℝ) + 1))) x
  have hω_cont : ∀ n, Continuous (ω n) :=
    fun n => continuous_familyModulus hG t₀ (isCompact_closedBall _ _)
  have hω_nonneg : ∀ n x, 0 ≤ ω n x := fun n x => by
    have := le_familyModulus hC t₀
      (show t₀ ∈ closedBall t₀ (1 / ((n : ℝ) + 1)) from mem_closedBall_self (hr n).le) x
    rwa [sub_self, abs_zero] at this
  have hω_le : ∀ n x, ω n x ≤ 2 * C := fun n x =>
    familyModulus_le_of_forall (hne n) fun t _ => by
      have h1 := abs_le.1 (hC t x)
      have h2 := abs_le.1 (hC t₀ x)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  let ωb : ℕ → E →ᵇ ℝ := fun n => BoundedContinuousFunction.ofNormedAddCommGroup (ω n) (hω_cont n)
    (2 * C) (fun x => by rw [Real.norm_of_nonneg (hω_nonneg n x)]; exact hω_le n x)
  -- the moduli decrease to zero pointwise
  have hω_lim : ∀ x, Tendsto (fun n => ω n x) atTop (𝓝 0) := by
    intro x
    have hcx : Continuous fun t => G t x := hG.comp (continuous_id.prodMk continuous_const)
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨ρ, hρ, hρδ⟩ := Metric.continuous_iff.1 hcx t₀ (δ / 2) (half_pos hδ)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
    refine ⟨N, fun n hn => ?_⟩
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hrn : 1 / ((n : ℝ) + 1) < ρ :=
      lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by linarith)) hN
    have hle : ω n x ≤ δ / 2 := familyModulus_le_of_forall (hne n) fun t ht => by
      have := hρδ t (lt_of_le_of_lt (mem_closedBall.1 ht) hrn)
      rw [Real.dist_eq] at this
      exact this.le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hω_nonneg n x)]
    linarith
  -- dominated convergence against `P₀`
  have hint_lim : Tendsto (fun n => ∫ x, ω n x ∂(P₀ : Measure E)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := (P₀ : Measure E)) (F := ω)
      (f := fun _ => (0 : ℝ)) (fun _ => 2 * C)
      (fun n => ((ωb n).integrable (P₀ : Measure E)).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hω_nonneg n x)]; exact hω_le n x)
      (ae_of_all _ hω_lim)
    simpa using h
  obtain ⟨n, hn⟩ := (hint_lim.eventually_lt_const (show (0 : ℝ) < ε / 3 by positivity)).exists
  have h1 : ∀ᶠ P : ProbabilityMeasure E in 𝓝 P₀, ∫ x, ω n x ∂(P : Measure E) < 2 * ε / 3 :=
    (hweak P₀ (ωb n)).eventually_lt_const
      (by change ∫ x, ω n x ∂(P₀ : Measure E) < 2 * ε / 3; linarith)
  have h2 : ∀ᶠ P : ProbabilityMeasure E in 𝓝 P₀,
      dist (∫ x, G t₀ x ∂(P : Measure E)) (∫ x, G t₀ x ∂(P₀ : Measure E)) < ε / 3 :=
    Metric.tendsto_nhds.1 (hweak P₀ (Gb t₀)) (ε / 3) (by positivity)
  have h3 : ∀ᶠ t in 𝓝 t₀, t ∈ closedBall t₀ (1 / ((n : ℝ) + 1)) := closedBall_mem_nhds t₀ (hr n)
  have e1 := (continuous_fst.tendsto (P₀, t₀)).eventually h1
  have e2 := (continuous_fst.tendsto (P₀, t₀)).eventually h2
  have e3 := (continuous_snd.tendsto (P₀, t₀)).eventually h3
  filter_upwards [e1, e2, e3] with q hq1 hq2 hq3
  obtain ⟨P, t⟩ := q
  dsimp only at hq1 hq2 hq3 ⊢
  have hsplit : ∫ x, G t x ∂(P : Measure E) - ∫ x, G t₀ x ∂(P₀ : Measure E) =
      ∫ x, (G t x - G t₀ x) ∂(P : Measure E) +
        (∫ x, G t₀ x ∂(P : Measure E) - ∫ x, G t₀ x ∂(P₀ : Measure E)) := by
    rw [integral_sub (hint P t) (hint P t₀)]
    ring
  have hmod : |∫ x, (G t x - G t₀ x) ∂(P : Measure E)| ≤ ∫ x, ω n x ∂(P : Measure E) :=
    (abs_integral_le_integral_abs).trans
      (integral_mono ((hint P t).sub (hint P t₀)).abs ((ωb n).integrable _)
        fun x => le_familyModulus hC t₀ hq3 x)
  rw [Real.dist_eq] at hq2 ⊢
  rw [hsplit]
  have ha := abs_le.1 hmod
  have hb := abs_lt.1 hq2
  rw [abs_lt]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-! ### Integrals against finite measures -/

/-- The pairing `(ν, H) ↦ ∫ H dν` is jointly continuous on `FiniteMeasure Z × (Z →ᵇ ℝ)`, for the
topology of weak convergence of finite measures and the uniform norm on bounded continuous
functions. -/
theorem continuous_integral_finiteMeasure_boundedContinuousFunction {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z] :
    Continuous fun q : FiniteMeasure Z × (Z →ᵇ ℝ) => ∫ z, q.2 z ∂(q.1 : Measure Z) := by
  have hweak : ∀ (ν₀ : FiniteMeasure Z) (H : Z →ᵇ ℝ),
      Tendsto (fun ν : FiniteMeasure Z => ∫ z, H z ∂(ν : Measure Z)) (𝓝 ν₀)
        (𝓝 (∫ z, H z ∂(ν₀ : Measure Z))) :=
    fun _ H => FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 tendsto_id H
  let one : Z →ᵇ ℝ := BoundedContinuousFunction.const Z 1
  have hone : ∀ z : Z, one z = 1 := fun _ => rfl
  have hbound : ∀ (ν : FiniteMeasure Z) (H : Z →ᵇ ℝ),
      |∫ z, H z ∂(ν : Measure Z)| ≤ (∫ z, one z ∂(ν : Measure Z)) * ‖H‖ := by
    intro ν H
    have h := H.norm_integral_le_mul_norm (μ := (ν : Measure Z))
    simpa [one, integral_const] using h
  have hone_nonneg : ∀ ν : FiniteMeasure Z, 0 ≤ ∫ z, one z ∂(ν : Measure Z) :=
    fun _ => integral_nonneg fun z => by rw [hone z]; exact zero_le_one
  rw [continuous_iff_continuousAt]
  rintro ⟨ν₀, H₀⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set m₀ := ∫ z, one z ∂(ν₀ : Measure Z)
  have hm₀ : 0 < m₀ + 1 := by linarith [hone_nonneg ν₀]
  have e1 := (continuous_fst.tendsto (ν₀, H₀)).eventually
    (Metric.tendsto_nhds.1 (hweak ν₀ H₀) (ε / 2) (half_pos hε))
  have e2 := (continuous_fst.tendsto (ν₀, H₀)).eventually
    ((hweak ν₀ one).eventually_lt_const (lt_add_one m₀))
  have e3 := (continuous_snd.tendsto (ν₀, H₀)).eventually
    (Metric.ball_mem_nhds H₀ (div_pos (half_pos hε) hm₀))
  filter_upwards [e1, e2, e3] with q h1 h2 h3
  obtain ⟨ν, H⟩ := q
  dsimp only at h1 h2 h3 ⊢
  have hsub : ∫ z, (H - H₀) z ∂(ν : Measure Z) =
      ∫ z, H z ∂(ν : Measure Z) - ∫ z, H₀ z ∂(ν : Measure Z) := by
    simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
    exact integral_sub (H.integrable _) (H₀.integrable _)
  have hsplit : ∫ z, H z ∂(ν : Measure Z) - ∫ z, H₀ z ∂(ν₀ : Measure Z) =
      ∫ z, (H - H₀) z ∂(ν : Measure Z) +
        (∫ z, H₀ z ∂(ν : Measure Z) - ∫ z, H₀ z ∂(ν₀ : Measure Z)) := by
    rw [hsub]
    ring
  have h3' : ‖H - H₀‖ < ε / 2 / (m₀ + 1) := by
    rw [dist_eq_norm] at h3
    exact h3
  have hprod : (∫ z, one z ∂(ν : Measure Z)) * ‖H - H₀‖ < ε / 2 := by
    calc (∫ z, one z ∂(ν : Measure Z)) * ‖H - H₀‖ ≤ (m₀ + 1) * ‖H - H₀‖ :=
          mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)
      _ < (m₀ + 1) * (ε / 2 / (m₀ + 1)) := mul_lt_mul_of_pos_left h3' hm₀
      _ = ε / 2 := by field_simp
  rw [Real.dist_eq] at h1 ⊢
  rw [hsplit]
  calc |∫ z, (H - H₀) z ∂(ν : Measure Z) +
        (∫ z, H₀ z ∂(ν : Measure Z) - ∫ z, H₀ z ∂(ν₀ : Measure Z))|
      ≤ |∫ z, (H - H₀) z ∂(ν : Measure Z)| +
        |∫ z, H₀ z ∂(ν : Measure Z) - ∫ z, H₀ z ∂(ν₀ : Measure Z)| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add ((hbound ν (H - H₀)).trans_lt hprod) h1
    _ = ε := add_halves ε

/-- Let `h : W → Z → ℝ` be jointly continuous and vanish off a compact set `K ⊆ Z`. Then
`(ν, w) ↦ ∫ h w dν` is jointly continuous on `FiniteMeasure Z × W`. -/
theorem continuous_integral_finiteMeasure_of_eq_zero_of_notMem {Z W : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z] [TopologicalSpace W] {h : W → Z → ℝ}
    (hh : Continuous fun p : W × Z => h p.1 p.2) {K : Set Z} (hK : IsCompact K)
    (hhK : ∀ w, ∀ z ∉ K, h w z = 0) :
    Continuous fun q : FiniteMeasure Z × W => ∫ z, h q.2 z ∂(q.1 : Measure Z) := by
  have hcont : ∀ w, Continuous (h w) := fun w => hh.comp (continuous_const.prodMk continuous_id)
  have hbdd : ∀ w, ∃ C, ∀ z, ‖h w z‖ ≤ C := by
    intro w
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont w).continuousOn
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ K
    · exact (hC z hz).trans (le_max_left _ _)
    · rw [hhK w z hz, norm_zero]
      exact le_max_right _ _
  let hb : W → Z →ᵇ ℝ := fun w => BoundedContinuousFunction.ofNormedAddCommGroup (h w) (hcont w)
    (hbdd w).choose (hbdd w).choose_spec
  have hb_cont : Continuous hb := by
    rw [continuous_iff_continuousAt]
    intro w₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro δ hδ
    have hd : Continuous fun p : W × Z => dist (h p.1 p.2) (h w₀ p.2) :=
      hh.dist (hh.comp (continuous_const.prodMk continuous_snd))
    have hev : ∀ᶠ w in 𝓝 w₀, ∀ z ∈ K, dist (h w z) (h w₀ z) < δ / 2 := by
      refine hK.eventually_forall_of_forall_eventually fun z _ => ?_
      refine (hd.tendsto (w₀, z)).eventually_lt_const ?_
      show dist (h w₀ z) (h w₀ z) < δ / 2
      rw [dist_self]
      exact half_pos hδ
    filter_upwards [hev] with w hw
    refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hδ).le).2 fun z => ?_)
      (half_lt_self hδ)
    show dist (h w z) (h w₀ z) ≤ δ / 2
    by_cases hz : z ∈ K
    · exact (hw z hz).le
    · rw [hhK w z hz, hhK w₀ z hz, dist_self]
      exact (half_pos hδ).le
  exact (continuous_integral_finiteMeasure_boundedContinuousFunction (Z := Z)).comp
    (continuous_fst.prodMk (hb_cont.comp continuous_snd))

/-! ### The reversibility pairing on the law-field space -/

/-- For a bounded Lipschitz `g : ℂ → ℝ`, `(P, s) ↦ E_P[g(X_s)]` is jointly continuous on
`ProbabilityMeasure C(ℝ≥0, ℂ) × ℝ≥0`. -/
theorem continuous_integral_comp_eval_time {g : ℂ → ℝ} (hgb : ∃ C, ∀ z, |g z| ≤ C) {K : ℝ≥0}
    (hgl : LipschitzWith K g) :
    Continuous fun q : ProbabilityMeasure C(ℝ≥0, ℂ) × ℝ≥0 =>
      ∫ X, g (X q.2) ∂(q.1 : Measure C(ℝ≥0, ℂ)) := by
  obtain ⟨C, hC⟩ := hgb
  have hev : Continuous fun p : C(ℝ≥0, ℂ) × ℝ≥0 => p.1 p.2 := continuous_eval
  have hG : Continuous fun p : ℝ≥0 × C(ℝ≥0, ℂ) => g (p.2 p.1) :=
    hgl.continuous.comp (hev.comp continuous_swap)
  exact continuous_integral_probabilityMeasure_of_continuous
    (G := fun s (X : C(ℝ≥0, ℂ)) => g (X s)) hG (fun s X => hC (X s))

/-- For a bounded Lipschitz `g : ℂ → ℝ`, `(P, s, z) ↦ E_{P_z}[g(X_s)]` is jointly continuous on
`C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0 × ℂ`. -/
theorem continuous_integral_comp_eval_lawField {g : ℂ → ℝ} (hgb : ∃ C, ∀ z, |g z| ≤ C) {K : ℝ≥0}
    (hgl : LipschitzWith K g) :
    Continuous fun q : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0 × ℂ =>
      ∫ X, g (X q.2.1) ∂((q.1 q.2.2 : ProbabilityMeasure C(ℝ≥0, ℂ)) : Measure C(ℝ≥0, ℂ)) := by
  have hev : Continuous fun p : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℂ => p.1 p.2 :=
    continuous_eval
  have hpair : Continuous fun q : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0 × ℂ =>
      (q.1, q.2.2) := by
    fun_prop
  have hmap : Continuous fun q : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0 × ℂ =>
      (q.1 q.2.2, q.2.1) :=
    (hev.comp hpair).prodMk (continuous_fst.comp continuous_snd)
  exact (continuous_integral_comp_eval_time hgb hgl).comp hmap

/-- One half of the reversibility pairing, `(ν, P, s) ↦ ∫ a(z) E_{P_z}[b(X_s)] ψ(z) dν(z)`, is jointly
continuous for `a` continuous, `b` bounded Lipschitz and `ψ` continuous with compact support. -/
theorem continuous_integral_mul_lawField_mul {a b ψ : ℂ → ℝ} (ha : Continuous a)
    (hbb : ∃ C, ∀ z, |b z| ≤ C) {L : ℝ≥0} (hbl : LipschitzWith L b) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) :
    Continuous fun q : FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0 =>
      ∫ z, a z * (∫ X, b (X q.2.2) ∂(q.2.1 z : Measure C(ℝ≥0, ℂ))) * ψ z ∂(q.1 : Measure ℂ) := by
  have hu := continuous_integral_comp_eval_lawField hbb hbl
  have hm : Continuous fun p : (C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0) × ℂ =>
      (p.1.1, p.1.2, p.2) := by
    fun_prop
  refine continuous_integral_finiteMeasure_of_eq_zero_of_notMem
    (h := fun (p : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0) z =>
      a z * (∫ X, b (X p.2) ∂(p.1 z : Measure C(ℝ≥0, ℂ))) * ψ z)
    (((ha.comp continuous_snd).mul (hu.comp hm)).mul (hψ.comp continuous_snd)) hψc ?_
  intro p z hz
  show a z * _ * ψ z = 0
  rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

/-- **Joint continuity of the reversibility pairing.** For bounded Lipschitz `f, g : ℂ → ℝ` and a
continuous compactly supported `ψ`, the pairing
`(ν, P, s) ↦ ∫ f(z) E_{P_z}[g(X_s)] ψ(z) dν(z) - ∫ g(z) E_{P_z}[f(X_s)] ψ(z) dν(z)` is jointly
continuous on `FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0`. -/
theorem continuous_reversibilityPairing {f g ψ : ℂ → ℝ} (hfb : ∃ C, ∀ z, |f z| ≤ C) {Kf : ℝ≥0}
    (hfl : LipschitzWith Kf f) (hgb : ∃ C, ∀ z, |g z| ≤ C) {Kg : ℝ≥0} (hgl : LipschitzWith Kg g)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Continuous fun q : FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)) × ℝ≥0 =>
      (∫ z, f z * (∫ X, g (X q.2.2) ∂(q.2.1 z : Measure C(ℝ≥0, ℂ))) * ψ z ∂(q.1 : Measure ℂ))
        - ∫ z, g z * (∫ X, f (X q.2.2) ∂(q.2.1 z : Measure C(ℝ≥0, ℂ))) * ψ z
            ∂(q.1 : Measure ℂ) :=
  (continuous_integral_mul_lawField_mul hfl.continuous hgb hgl hψ hψc).sub
    (continuous_integral_mul_lawField_mul hgl.continuous hfb hfl hψ hψc)

end LatticeProb
