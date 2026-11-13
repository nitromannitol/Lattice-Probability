/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.WeakConvergenceTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Util.AssertNoSorry

/-!
# Convergence in law transfers to uniformly close paths

The abstract analytic core of the path-level transfers for GMS Theorem 1.16.  If continuous paths
`I i` converge in law (weak convergence of their pushforward laws in `C(ℝ≥0, Plane)`, i.e. mathlib's
weak topology on `ProbabilityMeasure` over the compact-open topology), and paths `Y i` are close to
them uniformly on every compact time window in (outer) probability, then the laws of `Y i` have the
same limit:

* `convergesWeaklyInC_of_close` — `Y i` continuous: `ConvergesWeaklyInC`, the form of the
  conclusion of `GMS.Theorem1_16`;
* `tendsto_integral_of_tendsto_of_close` — `Y i` arbitrary product-measurable paths, tested against
  bounded functionals continuous for the topology of uniform convergence on compacts (GMS's local
  uniform topology for step paths);
* `convergesWeaklyInC_of_quenched`, `convergesWeaklyInC_of_quenched_of_close` — the same starting
  from the corpus's `QuenchedWeakLimitAtFixedStart` for one continuous path `Iu`, whose rescalings
  are `t ↦ ε • Iu(t / ε²)`.

No tightness of the continuous paths is used.  For a test functional `G`, the sets
`A n = {f | every path within 1/(n+1) of f on [0,n] has |G g - G f| ≤ η}` increase, and every
continuous path lies in the interior of one of them (continuity of `G`, and the compact-convergence
neighbourhood basis of `C(ℝ≥0, Plane)`).  The portmanteau bound on the closed complements of these
interiors then gives the needed uniform control.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ReflectedGMS.GMS.WeakConvergenceTransfer

/-- Continuity of `G` for the topology of uniform convergence on compacts, at one path `g₀`,
unpacked to a single compact window `[0, T]` and a uniform radius `δ`. -/
theorem exists_window_of_continuous {G : (ℝ≥0 → Plane) → ℝ}
    (hGc : Continuous (fun f : UniformOnFun ℝ≥0 Plane {s : Set ℝ≥0 | IsCompact s} =>
      G (UniformOnFun.toFun _ f)))
    (g₀ : ℝ≥0 → Plane) {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ g : ℝ≥0 → Plane,
      (∀ t ≤ T, dist (g t) (g₀ t) < δ) → |G g - G g₀| < η := by
  set 𝔖 : Set (Set ℝ≥0) := {s : Set ℝ≥0 | IsCompact s} with h𝔖
  have hmem : (fun f : UniformOnFun ℝ≥0 Plane 𝔖 => G (UniformOnFun.toFun 𝔖 f)) ⁻¹'
      Metric.ball (G g₀) η ∈ 𝓝 (UniformOnFun.ofFun 𝔖 g₀) :=
    hGc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hη)
  obtain ⟨⟨S, δ⟩, ⟨hS, hδ⟩, hsub⟩ :=
    (UniformOnFun.hasBasis_nhds_of_basis ℝ≥0 Plane 𝔖 (UniformOnFun.ofFun 𝔖 g₀)
      ⟨∅, isCompact_empty⟩ (directedOn_of_sup_mem fun _ _ => IsCompact.union)
      Metric.uniformity_basis_dist).mem_iff.mp hmem
  obtain ⟨T, hT⟩ := (show IsCompact S from hS).bddAbove
  refine ⟨T, δ, hδ, fun g hg => ?_⟩
  have hg' : UniformOnFun.ofFun 𝔖 g ∈ {g' : UniformOnFun ℝ≥0 Plane 𝔖 |
      (g', UniformOnFun.ofFun 𝔖 g₀) ∈
        UniformOnFun.gen 𝔖 S {p : Plane × Plane | dist p.1 p.2 < δ}} :=
    fun x hx => hg x (hT hx)
  have h := hsub hg'
  simp only [mem_preimage, Metric.mem_ball, UniformOnFun.toFun_ofFun, Real.dist_eq] at h
  exact h

/-- A uniform neighbourhood on `[0, T]` is a neighbourhood in `C(ℝ≥0, Plane)` (compact-open
topology). -/
theorem setOf_forall_dist_lt_mem_nhds (f : BouRabeeGwynne.BrownianPath 2) (T : ℝ≥0) {δ : ℝ}
    (hδ : 0 < δ) :
    {g : BouRabeeGwynne.BrownianPath 2 | ∀ t ≤ T, dist (f t) (g t) < δ} ∈ 𝓝 f := by
  rw [UniformSpace.mem_nhds_iff]
  refine ⟨_, ContinuousMap.hasBasis_compactConvergenceUniformity.mem_of_mem
    (i := (Icc (0 : ℝ≥0) T, {p : Plane × Plane | dist p.1 p.2 < δ}))
    ⟨isCompact_Icc, Metric.dist_mem_uniformity hδ⟩, ?_⟩
  intro g hg t ht
  exact hg t ⟨by positivity, ht⟩

/-- Portmanteau for an increasing family of sets whose interiors exhaust the space: for any
`η > 0` one of the closed complements of the interiors eventually has mass `< η` along a weakly
convergent family of probability measures. -/
theorem exists_eventually_measure_compl_interior_lt
    {Ω' ι : Type*} [MeasurableSpace Ω'] [TopologicalSpace Ω'] [OpensMeasurableSpace Ω']
    [HasOuterApproxClosed Ω'] {L : Filter ι} {μ : ProbabilityMeasure Ω'}
    {μs : ι → ProbabilityMeasure Ω'} (hlim : Tendsto μs L (𝓝 μ))
    (A : ℕ → Set Ω') (hA : Monotone A) (hcov : ∀ x, ∃ n, A n ∈ 𝓝 x)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ n, ∀ᶠ i in L, (μs i : Measure Ω') (interior (A n))ᶜ < η := by
  set F : ℕ → Set Ω' := fun n => (interior (A n))ᶜ with hF
  have hFc : ∀ n, IsClosed (F n) := fun n => isOpen_interior.isClosed_compl
  have hanti : Antitone F := fun n m hnm =>
    compl_subset_compl.mpr (interior_mono (hA hnm))
  have hinter : (⋂ n, F n) = ∅ := by
    refine Set.subset_empty_iff.mp fun x hx => ?_
    obtain ⟨n, hn⟩ := hcov x
    exact (mem_iInter.mp hx n) (mem_interior_iff_mem_nhds.mpr hn)
  have hlim0 : Tendsto (fun n => (μ : Measure Ω') (F n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := (μ : Measure Ω'))
      (fun n => (hFc n).measurableSet.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hinter, measure_empty] at h
    exact h
  obtain ⟨n, hn⟩ := (hlim0.eventually (gt_mem_nhds hη)).exists
  exact ⟨n, eventually_lt_of_limsup_lt
    (lt_of_le_of_lt (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim (hFc n)) hn)⟩

/-- A bounded measurable real function of a measurable path is integrable. -/
theorem integrable_comp_of_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {β : Type*} [MeasurableSpace β] {G : β → ℝ} (hGm : Measurable G)
    {C : ℝ} (hC : ∀ f, |G f| ≤ C) {Y : Ω → β} (hY : Measurable Y) :
    Integrable (fun ω => G (Y ω)) P :=
  (integrable_const C).mono' (hGm.comp hY).aestronglyMeasurable
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC (Y ω))

/-- **Abstract transfer of convergence in law to uniformly close paths (general path type).**
`β` is a type of paths, read through `path : β → ℝ≥0 → Plane`, into which the continuous paths
embed by `emb`.  Continuous paths `I i` whose laws converge weakly to `μ`, and measurable `β`-paths
`Y i` which are uniformly close to them on every window `[0, T]` in outer probability: for every
bounded measurable `G : β → ℝ` which is continuous on the embedded continuous paths and continuous
at them uniformly on compact windows (`hwin`), the integrals of `G (Y i)` converge to the
`μ`-integral of `G ∘ emb`. -/
theorem tendsto_integral_of_tendsto_of_close_gen
    {Ω ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    [IsProbabilityMeasure P] {L : Filter ι}
    (path : β → ℝ≥0 → Plane) (emb : BouRabeeGwynne.BrownianPath 2 → β)
    (hemb : ∀ f t, path (emb f) t = f t) (hembm : Measurable emb)
    (I : ι → Ω → BouRabeeGwynne.BrownianPath 2) (hI : ∀ i, Measurable (I i))
    (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (hlim : Tendsto (fun i => P.toProbabilityMeasure.map (I i)) L (𝓝 μ))
    (Y : ι → Ω → β) (hY : ∀ i, Measurable (Y i))
    (hclose : ∀ (T : ℝ≥0) (δ : ℝ), 0 < δ →
      Tendsto (fun i => P {ω | ∃ t ≤ T, δ < ‖path (Y i ω) t - I i ω t‖}) L (𝓝 0))
    (G : β → ℝ) (C : ℝ) (hC : ∀ b, |G b| ≤ C) (hGm : Measurable G)
    (hcont : Continuous (fun f : BouRabeeGwynne.BrownianPath 2 => G (emb f)))
    (hwin : ∀ (f : BouRabeeGwynne.BrownianPath 2) (η : ℝ), 0 < η → ∃ T : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ b : β, (∀ t ≤ T, dist (path b t) (f t) < δ) → |G b - G (emb f)| < η) :
    Tendsto (fun i => ∫ ω, G (Y i ω) ∂P) L
      (𝓝 (∫ f, G (emb f) ∂(μ : Measure (BouRabeeGwynne.BrownianPath 2)))) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (emb 0))
  -- the continuous paths: convergence of the integrals
  let g : BoundedContinuousFunction (BouRabeeGwynne.BrownianPath 2) ℝ :=
    BoundedContinuousFunction.mkOfBound
      (⟨fun f => G (emb f), hcont⟩ : C(BouRabeeGwynne.BrownianPath 2, ℝ)) (2 * C)
      (fun f f' => by
        show dist (G (emb f)) (G (emb f')) ≤ 2 * C
        rw [Real.dist_eq]
        have h1 := abs_le.mp (hC (emb f))
        have h2 := abs_le.mp (hC (emb f'))
        exact abs_le.mpr ⟨by linarith, by linarith⟩)
  have hIlim : Tendsto (fun i => ∫ ω, G (emb (I i ω)) ∂P) L
      (𝓝 (∫ f, G (emb f) ∂(μ : Measure (BouRabeeGwynne.BrownianPath 2)))) := by
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) g
    have hval : (∫ f, g f ∂(μ : Measure (BouRabeeGwynne.BrownianPath 2))) =
        ∫ f, G (emb f) ∂(μ : Measure (BouRabeeGwynne.BrownianPath 2)) := rfl
    rw [hval] at h
    refine h.congr fun i => ?_
    show ∫ f, G (emb f) ∂(P.map (I i)) = _
    rw [integral_map (hI i).aemeasurable hcont.aestronglyMeasurable]
  -- the difference of the two integrals is eventually small
  have hdiff : ∀ η' : ℝ, 0 < η' → ∀ᶠ i in L,
      |∫ ω, G (Y i ω) ∂P - ∫ ω, G (emb (I i ω)) ∂P| < η' := by
    intro η' hη'
    set η : ℝ := η' / (2 + 4 * C) with hηdef
    have hden : 0 < 2 + 4 * C := by linarith
    have hη : 0 < η := div_pos hη' hden
    have hηbound : η + 2 * C * (2 * η) < η' := by
      have h : η * (2 + 4 * C) = η' := div_mul_cancel₀ η' hden.ne'
      nlinarith
    let A : ℕ → Set (BouRabeeGwynne.BrownianPath 2) := fun n =>
      {f | ∀ b : β, (∀ t ≤ (n : ℝ≥0), ‖path b t - f t‖ ≤ 1 / ((n : ℝ) + 1)) →
        |G b - G (emb f)| ≤ η}
    have hAmono : Monotone A := by
      intro n m hnm f hf b hb
      apply hf b
      intro t ht
      refine (hb t (ht.trans (by exact_mod_cast hnm))).trans ?_
      have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
      gcongr
    have hAcov : ∀ f, ∃ n, A n ∈ 𝓝 f := by
      intro f
      obtain ⟨T, δ, hδ, hTδ⟩ := hwin f (η / 2) (half_pos hη)
      obtain ⟨n₁, hn₁⟩ := exists_nat_ge T
      obtain ⟨n₂, hn₂⟩ := exists_nat_one_div_lt (half_pos hδ)
      refine ⟨max n₁ n₂, mem_of_superset (setOf_forall_dist_lt_mem_nhds f T (half_pos hδ)) ?_⟩
      intro f' hf' b hb
      have hTn : T ≤ ((max n₁ n₂ : ℕ) : ℝ≥0) :=
        hn₁.trans (by exact_mod_cast le_max_left n₁ n₂)
      have hrad : 1 / (((max n₁ n₂ : ℕ) : ℝ) + 1) < δ / 2 := by
        refine lt_of_le_of_lt ?_ hn₂
        have : (n₂ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right n₁ n₂
        gcongr
      have h1 : |G b - G (emb f)| < η / 2 := hTδ b fun t ht => by
        have ha : ‖path b t - f' t‖ ≤ 1 / (((max n₁ n₂ : ℕ) : ℝ) + 1) := hb t (ht.trans hTn)
        have hb' : dist (f t) (f' t) < δ / 2 := hf' t ht
        calc dist (path b t) (f t) ≤ dist (path b t) (f' t) + dist (f' t) (f t) :=
              dist_triangle _ _ _
          _ < δ / 2 + δ / 2 := by
              rw [dist_eq_norm, dist_comm]
              linarith
          _ = δ := by ring
      have h2 : |G (emb f') - G (emb f)| < η / 2 := hTδ (emb f') fun t ht => by
        have hb' : dist (f t) (f' t) < δ / 2 := hf' t ht
        rw [hemb, dist_comm]
        linarith
      have h1' := abs_lt.mp h1
      have h2' := abs_lt.mp h2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    obtain ⟨n, hn⟩ := exists_eventually_measure_compl_interior_lt hlim A hAmono hAcov
      (ENNReal.ofReal_pos.mpr hη)
    have hcl : ∀ᶠ i in L,
        P {ω | ∃ t ≤ (n : ℝ≥0), 1 / ((n : ℝ) + 1) < ‖path (Y i ω) t - I i ω t‖} <
          ENNReal.ofReal η :=
      (hclose (n : ℝ≥0) (1 / ((n : ℝ) + 1)) (by positivity)).eventually
        (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
    filter_upwards [hn, hcl] with i hi1 hi2
    have hi1' : P ((I i) ⁻¹' (interior (A n))ᶜ) < ENNReal.ofReal η := by
      rw [← Measure.map_apply (hI i) isOpen_interior.isClosed_compl.measurableSet]
      exact hi1
    set B : Set Ω := (I i) ⁻¹' (interior (A n))ᶜ ∪
      {ω | ∃ t ≤ (n : ℝ≥0), 1 / ((n : ℝ) + 1) < ‖path (Y i ω) t - I i ω t‖} with hBdef
    have hB : P B < ENNReal.ofReal (2 * η) := by
      calc P B ≤ P ((I i) ⁻¹' (interior (A n))ᶜ) +
            P {ω | ∃ t ≤ (n : ℝ≥0), 1 / ((n : ℝ) + 1) < ‖path (Y i ω) t - I i ω t‖} :=
            measure_union_le _ _
        _ < ENNReal.ofReal η + ENNReal.ofReal η := ENNReal.add_lt_add hi1' hi2
        _ = ENNReal.ofReal (2 * η) := by
            rw [← ENNReal.ofReal_add hη.le hη.le, two_mul]
    set B' : Set Ω := toMeasurable P B with hB'def
    have hB'm : MeasurableSet B' := measurableSet_toMeasurable P B
    have hB' : P.real B' ≤ 2 * η := by
      rw [measureReal_def, hB'def, measure_toMeasurable]
      exact (ENNReal.toReal_lt_of_lt_ofReal hB).le
    have hpt : ∀ ω, ‖G (Y i ω) - G (emb (I i ω))‖ ≤ η + 2 * C * B'.indicator 1 ω := by
      intro ω
      rw [Real.norm_eq_abs]
      by_cases hω : ω ∈ B'
      · rw [indicator_of_mem hω, Pi.one_apply, mul_one]
        have h1 := abs_le.mp (hC (Y i ω))
        have h2 := abs_le.mp (hC (emb (I i ω)))
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · rw [indicator_of_notMem hω, mul_zero, add_zero]
        have hωB : ω ∉ B := fun h => hω (subset_toMeasurable P B h)
        have hI' : I i ω ∈ interior (A n) := by
          by_contra hc
          exact hωB (Or.inl hc)
        have hY' : ∀ t ≤ (n : ℝ≥0), ‖path (Y i ω) t - I i ω t‖ ≤ 1 / ((n : ℝ) + 1) := by
          intro t ht
          by_contra hc
          exact hωB (Or.inr ⟨t, ht, not_le.mp hc⟩)
        exact interior_subset hI' (Y i ω) hY'
    have hintY : Integrable (fun ω => G (Y i ω)) P :=
      integrable_comp_of_bound P hGm hC (hY i)
    have hintI : Integrable (fun ω => G (emb (I i ω))) P :=
      integrable_comp_of_bound P hGm hC (hembm.comp (hI i))
    have hintInd : Integrable (fun ω => B'.indicator (1 : Ω → ℝ) ω) P :=
      (integrable_const (1 : ℝ)).indicator hB'm
    have hintB : Integrable (fun ω => η + 2 * C * B'.indicator (1 : Ω → ℝ) ω) P :=
      (integrable_const η).add (hintInd.const_mul (2 * C))
    rw [← integral_sub hintY hintI, ← Real.norm_eq_abs]
    calc ‖∫ ω, (G (Y i ω) - G (emb (I i ω))) ∂P‖
        ≤ ∫ ω, (η + 2 * C * B'.indicator (1 : Ω → ℝ) ω) ∂P :=
          norm_integral_le_of_norm_le hintB (ae_of_all _ hpt)
      _ = η + 2 * C * P.real B' := by
          rw [integral_add (integrable_const η) (hintInd.const_mul (2 * C)), integral_const,
            integral_const_mul, integral_indicator_one hB'm]
          simp
      _ ≤ η + 2 * C * (2 * η) := by nlinarith
      _ < η' := hηbound
  have hdiff' : Tendsto (fun i => ∫ ω, G (Y i ω) ∂P - ∫ ω, G (emb (I i ω)) ∂P) L (𝓝 0) :=
    Metric.tendsto_nhds.mpr fun η' hη' => (hdiff η' hη').mono fun i hi => by
      rwa [Real.dist_eq, sub_zero]
  have h := hdiff'.add hIlim
  simp only [sub_add_cancel, zero_add] at h
  exact h

/-- **Function-space form.**  The same transfer for bounded functionals on all paths
`ℝ≥0 → Plane` that are measurable for the product σ-algebra and continuous for the topology of
uniform convergence on compacts (GMS's local uniform topology). -/
theorem tendsto_integral_of_tendsto_of_close
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {L : Filter ι}
    (I : ι → Ω → BouRabeeGwynne.BrownianPath 2) (hI : ∀ i, Measurable (I i))
    (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2))
    (hlim : Tendsto (fun i => P.toProbabilityMeasure.map (I i)) L (𝓝 μ))
    (Y : ι → Ω → ℝ≥0 → Plane) (hY : ∀ i, Measurable (Y i))
    (hclose : ∀ (T : ℝ≥0) (δ : ℝ), 0 < δ →
      Tendsto (fun i => P {ω | ∃ t ≤ T, δ < ‖Y i ω t - I i ω t‖}) L (𝓝 0))
    (G : (ℝ≥0 → Plane) → ℝ) (hGb : ∃ C, ∀ f, |G f| ≤ C) (hGm : Measurable G)
    (hGc : Continuous (fun f : UniformOnFun ℝ≥0 Plane {s : Set ℝ≥0 | IsCompact s} =>
      G (UniformOnFun.toFun _ f))) :
    Tendsto (fun i => ∫ ω, G (Y i ω) ∂P) L
      (𝓝 (∫ f, G (f : ℝ≥0 → Plane) ∂(μ : Measure (BouRabeeGwynne.BrownianPath 2)))) := by
  obtain ⟨C, hC⟩ := hGb
  have hcont : Continuous (fun f : BouRabeeGwynne.BrownianPath 2 => G (f : ℝ≥0 → Plane)) :=
    hGc.comp ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isInducing.continuous
  have hcoe : Measurable (fun f : BouRabeeGwynne.BrownianPath 2 => (f : ℝ≥0 → Plane)) :=
    measurable_pi_iff.mpr fun t => (continuous_eval_const t).measurable
  exact tendsto_integral_of_tendsto_of_close_gen P (fun b => b)
    (fun f : BouRabeeGwynne.BrownianPath 2 => (f : ℝ≥0 → Plane)) (fun _ _ => rfl) hcoe
    I hI μ hlim Y hY hclose G C hC hGm hcont
    (fun f η hη => exists_window_of_continuous hGc (f : ℝ≥0 → Plane) hη)

/-- Continuity of `G : C(ℝ≥0, Plane) → ℝ` at one path, unpacked to one compact window `[0, T]`
and a uniform radius `δ` (compact-convergence neighbourhood basis). -/
theorem exists_window_of_continuous_C {G : BouRabeeGwynne.BrownianPath 2 → ℝ}
    (hG : Continuous G) (f : BouRabeeGwynne.BrownianPath 2) {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ g : BouRabeeGwynne.BrownianPath 2,
      (∀ t ≤ T, dist (g t) (f t) < δ) → |G g - G f| < η := by
  have hmem : G ⁻¹' Metric.ball (G f) η ∈ 𝓝 f :=
    hG.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hη)
  obtain ⟨V, hV, hVsub⟩ := UniformSpace.mem_nhds_iff.mp hmem
  obtain ⟨⟨K, U⟩, ⟨hK, hU⟩, hKU⟩ :=
    ContinuousMap.hasBasis_compactConvergenceUniformity.mem_iff.mp hV
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨T, hT⟩ := (show IsCompact K from hK).bddAbove
  refine ⟨T, δ, hδ, fun g hg => ?_⟩
  have hfg : (f, g) ∈ V := hKU fun x hx => hδU (by rw [dist_comm]; exact hg x (hT hx))
  have h := hVsub hfg
  simp only [mem_preimage, Metric.mem_ball, Real.dist_eq] at h
  exact h

/-- **Transfer of weak convergence in `C(ℝ≥0, Plane)` to uniformly close continuous paths**
(`ConvergesWeaklyInC`, the form of GMS Theorem 1.16's conclusion). -/
theorem convergesWeaklyInC_of_close
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2) (hI : ∀ ε, Measurable (I ε))
    (target : StatementIngredients.AnisotropicBrownianTarget)
    (hlim : Tendsto (fun ε => P.toProbabilityMeasure.map (I ε)) (𝓝[>] 0) (𝓝 target.pathLaw))
    (Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2) (hY : ∀ ε, Measurable (Y ε))
    (hclose : ∀ (T : ℝ≥0) (δ : ℝ), 0 < δ →
      Tendsto (fun ε => P {ω | ∃ t ≤ T, δ < ‖Y ε ω t - I ε ω t‖}) (𝓝[>] 0) (𝓝 0)) :
    ConvergesWeaklyInC P Y target := by
  intro G hG hGb
  obtain ⟨C, hC⟩ := hGb
  exact tendsto_integral_of_tendsto_of_close_gen P
    (fun b : BouRabeeGwynne.BrownianPath 2 => (b : ℝ≥0 → Plane)) (fun f => f)
    (fun _ _ => rfl) measurable_id I hI target.pathLaw hlim Y hY hclose G C hC hG.measurable hG
    (fun f η hη => exists_window_of_continuous_C hG f hη)

/-- Weak convergence in `C` only sees each path up to almost-sure equality. -/
theorem convergesWeaklyInC_congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y Y' : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2}
    {target : StatementIngredients.AnisotropicBrownianTarget}
    (h : ∀ ε, ∀ᵐ ω ∂P, Y ε ω = Y' ε ω) (hY : ConvergesWeaklyInC P Y target) :
    ConvergesWeaklyInC P Y' target := by
  intro G hG hGb
  refine (hY G hG hGb).congr fun ε => ?_
  exact integral_congr_ae ((h ε).mono fun ω hω => congrArg G hω)

/-- The diffusive rescaling used by the corpus, `ε • ω(t / ε²)`, at every scale (at `ε = 0` both
sides are `0`). -/
theorem scaledBrownianPath_inv_apply_div (ε : ℝ≥0) (ω : BouRabeeGwynne.BrownianPath 2)
    (t : ℝ≥0) :
    BouRabeeGwynne.scaledBrownianPath ε⁻¹ ω t = (ε : ℝ) • ω (t / ε ^ 2) := by
  rw [BouRabeeGwynne.scaledBrownianPath_apply, NNReal.coe_inv, inv_inv, inv_pow,
    div_eq_mul_inv, mul_comm]

/-- The rescaled law of `Iu` is the law of the rescaled path. -/
theorem diffusivelyRescaledPathLaw_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Iu : Ω → BouRabeeGwynne.BrownianPath 2) (hIu : Measurable Iu)
    (ε : ℝ≥0) :
    StatementIngredients.diffusivelyRescaledPathLaw (P.toProbabilityMeasure.map Iu) ε =
      P.toProbabilityMeasure.map (fun ω => BouRabeeGwynne.scaledBrownianPath ε⁻¹ (Iu ω)) :=
  Subtype.ext (Measure.map_map (BouRabeeGwynne.measurable_scaledBrownianPath _) hIu)

/-- The corpus's quenched limit (`QuenchedWeakLimitAtFixedStart`, the form inside
`InterpolatedTwoClockLimit`) in terms of the rescaled paths themselves. -/
theorem tendsto_map_scaled_of_quenched {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Iu : Ω → BouRabeeGwynne.BrownianPath 2) (hIu : Measurable Iu)
    (target : StatementIngredients.AnisotropicBrownianTarget)
    (hq : StatementIngredients.QuenchedWeakLimitAtFixedStart
      (fun (_ : Unit) (_ : Unit) => P.toProbabilityMeasure.map Iu) target () ()) :
    Tendsto (fun ε => P.toProbabilityMeasure.map
      (fun ω => BouRabeeGwynne.scaledBrownianPath ε⁻¹ (Iu ω))) (𝓝[>] 0) (𝓝 target.pathLaw) := by
  have h : StatementIngredients.QuenchedWeakLimitAtFixedStart
      (fun (_ : Unit) (_ : Unit) => P.toProbabilityMeasure.map Iu) target () () := hq
  unfold StatementIngredients.QuenchedWeakLimitAtFixedStart at h
  exact h.congr fun ε => diffusivelyRescaledPathLaw_map P Iu hIu ε

/-- **Corpus form, exact paths.**  The corpus's quenched limit of one continuous path `Iu` is
`ConvergesWeaklyInC` for its diffusive rescalings `t ↦ ε • Iu(t / ε²)`. -/
theorem convergesWeaklyInC_of_quenched {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Iu : Ω → BouRabeeGwynne.BrownianPath 2) (hIu : Measurable Iu)
    (target : StatementIngredients.AnisotropicBrownianTarget)
    (hq : StatementIngredients.QuenchedWeakLimitAtFixedStart
      (fun (_ : Unit) (_ : Unit) => P.toProbabilityMeasure.map Iu) target () ()) :
    ConvergesWeaklyInC P (fun ε ω => BouRabeeGwynne.scaledBrownianPath ε⁻¹ (Iu ω)) target := by
  intro G hG hGb
  obtain ⟨C, hC⟩ := hGb
  let g : BoundedContinuousFunction (BouRabeeGwynne.BrownianPath 2) ℝ :=
    BoundedContinuousFunction.mkOfBound (⟨G, hG⟩ : C(BouRabeeGwynne.BrownianPath 2, ℝ)) (2 * C)
      (fun f f' => by
        show dist (G f) (G f') ≤ 2 * C
        rw [Real.dist_eq]
        have h1 := abs_le.mp (hC f)
        have h2 := abs_le.mp (hC f')
        exact abs_le.mpr ⟨by linarith, by linarith⟩)
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_map_scaled_of_quenched P Iu hIu target hq)) g
  have hval : (∫ f, g f ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2))) =
      ∫ f, G f ∂(target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) := rfl
  rw [hval] at h
  refine h.congr fun ε => ?_
  show ∫ f, G f ∂(P.map (fun ω => BouRabeeGwynne.scaledBrownianPath ε⁻¹ (Iu ω))) = _
  have hm : Measurable (fun ω => BouRabeeGwynne.scaledBrownianPath ε⁻¹ (Iu ω)) :=
    (BouRabeeGwynne.measurable_scaledBrownianPath _).comp hIu
  rw [integral_map hm.aemeasurable hG.aestronglyMeasurable]

/-- **Corpus form, close paths.**  The corpus's quenched limit of one continuous path `Iu`, and
continuous paths `Y ε` close to `t ↦ ε • Iu(t / ε²)` uniformly on compact windows in outer
probability: then `ConvergesWeaklyInC P Y target`. -/
theorem convergesWeaklyInC_of_quenched_of_close
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Iu : Ω → BouRabeeGwynne.BrownianPath 2) (hIu : Measurable Iu)
    (target : StatementIngredients.AnisotropicBrownianTarget)
    (hq : StatementIngredients.QuenchedWeakLimitAtFixedStart
      (fun (_ : Unit) (_ : Unit) => P.toProbabilityMeasure.map Iu) target () ())
    (Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2) (hY : ∀ ε, Measurable (Y ε))
    (hclose : ∀ (T : ℝ≥0) (δ : ℝ), 0 < δ →
      Tendsto (fun ε => P {ω | ∃ t ≤ T, δ < ‖Y ε ω t - (ε : ℝ) • Iu ω (t / ε ^ 2)‖})
        (𝓝[>] 0) (𝓝 0)) :
    ConvergesWeaklyInC P Y target := by
  refine convergesWeaklyInC_of_close P
    (fun ε ω => BouRabeeGwynne.scaledBrownianPath ε⁻¹ (Iu ω))
    (fun ε => (BouRabeeGwynne.measurable_scaledBrownianPath _).comp hIu) target
    (tendsto_map_scaled_of_quenched P Iu hIu target hq) Y hY ?_
  intro T δ hδ
  refine (hclose T δ hδ).congr fun ε => ?_
  congr 1
  ext ω
  simp only [mem_setOf_eq, scaledBrownianPath_inv_apply_div]

end ReflectedGMS.GMS.WeakConvergenceTransfer

assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.exists_window_of_continuous
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.setOf_forall_dist_lt_mem_nhds
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.exists_eventually_measure_compl_interior_lt
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.integrable_comp_of_bound
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.tendsto_integral_of_tendsto_of_close_gen
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.tendsto_integral_of_tendsto_of_close
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.exists_window_of_continuous_C
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.convergesWeaklyInC_of_close
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.convergesWeaklyInC_congr_ae
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.scaledBrownianPath_inv_apply_div
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.diffusivelyRescaledPathLaw_map
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.tendsto_map_scaled_of_quenched
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.convergesWeaklyInC_of_quenched
assert_no_sorry ReflectedGMS.GMS.WeakConvergenceTransfer.convergesWeaklyInC_of_quenched_of_close

#print axioms ReflectedGMS.GMS.WeakConvergenceTransfer.tendsto_integral_of_tendsto_of_close_gen
#print axioms ReflectedGMS.GMS.WeakConvergenceTransfer.tendsto_integral_of_tendsto_of_close
#print axioms ReflectedGMS.GMS.WeakConvergenceTransfer.convergesWeaklyInC_of_close
#print axioms ReflectedGMS.GMS.WeakConvergenceTransfer.convergesWeaklyInC_congr_ae
#print axioms ReflectedGMS.GMS.WeakConvergenceTransfer.convergesWeaklyInC_of_quenched
#print axioms ReflectedGMS.GMS.WeakConvergenceTransfer.convergesWeaklyInC_of_quenched_of_close
