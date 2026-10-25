import LatticeProb.Prob.Cadlag.HalfLine.RestrictionTight
import LatticeProb.Prob.Cadlag.HalfLine.Laws

/-!
# Restriction tightness from asymptotic averaged increments

Eventual bounds on each fixed averaging window pass to subsequential limits whose indices
tend to infinity. These limits have no terminal jump, so restriction preserves their weak
convergence. Constant-index subsequences handle the remaining laws, including early laws
with a terminal jump.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal

noncomputable section

/-- Sequential relative compactness implies compactness of the closure in a metrizable space.
The subsequential limits need not belong to the original set. -/
private theorem isCompact_closure_of_subsequences {X : Type*} [TopologicalSpace X]
    [MetrizableSpace X] {s : Set X}
    (hs : ∀ u : ℕ → X, (∀ n, u n ∈ s) →
      ∃ (a : X) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a)) :
    IsCompact (closure s) := by
  letI := TopologicalSpace.metrizableSpaceMetric X
  apply IsSeqCompact.isCompact
  intro u hu
  have happ (n : ℕ) : ∃ v ∈ s, dist (u n) v < 1 / (n + 1 : ℝ) :=
    Metric.mem_closure_iff.mp (hu n) _ (by positivity)
  choose v hv hd using happ
  obtain ⟨a, φ, hφ, ha⟩ := hs v hv
  have hd0 : Tendsto (fun n => dist (v n) (u n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _
      tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [dist_comm]
    exact (hd n).le
  have hlim := ha.congr_dist (hd0.comp hφ.tendsto_atTop)
  exact ⟨a, isClosed_closure.mem_of_tendsto hlim
    (Eventually.of_forall fun n => hu (φ n)), φ, hφ, hlim⟩

/-- A sequence of natural indices either repeats one index infinitely often or tends to
infinity. The first alternative supplies a constant subsequence. -/
private theorem indices_constant_or_tendsto (u : ℕ → ℕ) :
    (∃ (k : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ n, u (φ n) = k) ∨
      Tendsto u atTop atTop := by
  by_cases hc : ∃ k, ∃ᶠ n in atTop, u n = k
  · obtain ⟨k, hk⟩ := hc
    obtain ⟨φ, hφ, heq⟩ := extraction_of_frequently_atTop hk
    exact Or.inl ⟨k, φ, hφ, heq⟩
  · right
    apply tendsto_atTop.mpr
    intro b
    have he : ∀ k ∈ Finset.range b, ∀ᶠ n in atTop, u n ≠ k := by
      intro k _
      exact not_frequently.mp (fun hk => hc ⟨k, hk⟩)
    filter_upwards [(Finset.range b).eventually_all.mpr he] with n hn
    by_contra hnb
    exact hn (u n) (Finset.mem_range.mpr (lt_of_not_ge hnb)) rfl

variable {E : Type*} [NormedAddCommGroup E] [SeparableSpace E] [MeasurableSpace E]
  [BorelSpace E]

/-- Asymptotic averaged-increment control rules out a terminal jump in every weak limit
along indices tending to infinity. -/
theorem measure_jump_eq_zero_of_asymptotic_averagedIncrement
    (T : Time) (hT : 0 < T) (μ : ℕ → ProbabilityMeasure (D E))
    (hb : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∫ x, averagedIncrement T h x ∂(μ n : Measure (D E)) ≤ η)
    {u : ℕ → ℕ} (hu : Tendsto u atTop atTop) {ν : ProbabilityMeasure (D E)}
    (hν : Tendsto (μ ∘ u) atTop (𝓝 ν)) :
    (ν : Measure (D E)) {x | ¬ ContinuousAt x.1 T} = 0 := by
  let g : ℝ → ℝ := fun h => ∫ x, averagedIncrement T h x ∂(ν : Measure (D E))
  have hg : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hbδ⟩ := hb (ε / 2) (by positivity)
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < min δ (T : ℝ) :=
      (eventually_lt_nhds (lt_min hδ hT)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hsmall
    obtain ⟨N, hN⟩ := hbδ h hh (lt_of_lt_of_le hsmall (min_le_left _ _))
    have hc := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (averagedIncrementTest (E := E) T hh (lt_of_lt_of_le hsmall (min_le_right _ _)))
    have hle : g h ≤ ε / 2 := le_of_tendsto (hc.tendsto ν |>.comp hν)
      (hu.eventually (eventually_atTop.2 ⟨N, hN⟩))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (integral_nonneg fun x => averagedIncrement_nonneg T hh x)]
    exact hle.trans_lt (by linarith)
  exact measure_jump_at_T_eq_zero (fun _ : Unit => ν) T hT g hg
    (fun _ _ _ _ => le_rfl) (subset_closure ⟨(), rfl⟩)

/-- Relative compactness and asymptotically vanishing averaged increments give tightness of
all finite-horizon restricted laws, including every early index. -/
theorem isTightMeasureSet_restrict_of_asymptotic_averagedIncrement
    (T : Time) (hT : 0 < T)
    (hsep : SeparableSpace (Cadlag.D T E)) (hcm : IsCompletelyMetrizableSpace (Cadlag.D T E))
    (μ : ℕ → ProbabilityMeasure (D E)) (hcompact : IsCompact (closure (range μ)))
    (hb : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∫ x, averagedIncrement T h x ∂(μ n : Measure (D E)) ≤ η) :
    IsTightMeasureSet {(((μ n).map (measurable_restrict (E := E) T).aemeasurable :
      ProbabilityMeasure (Cadlag.D T E)) : Measure (Cadlag.D T E)) | n} := by
  letI := hsep
  letI := hcm
  let ρ : ℕ → ProbabilityMeasure (Cadlag.D T E) :=
    fun n => (μ n).map (measurable_restrict (E := E) T).aemeasurable
  have hρ : IsCompact (closure (range ρ)) := by
    apply isCompact_closure_of_subsequences
    intro v hv
    choose u hu using hv
    rcases indices_constant_or_tendsto u with ⟨k, φ, hφ, heq⟩ | hut
    · refine ⟨ρ k, φ, hφ, ?_⟩
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => ρ k) atTop (𝓝 (ρ k))) using 1
      funext n
      exact (hu (φ n)).symm.trans (congrArg ρ (heq n))
    · obtain ⟨ν, _, φ, hφ, hν⟩ := hcompact.tendsto_subseq
        (fun n => subset_closure (mem_range_self (f := μ) (u n)))
      have hj := measure_jump_eq_zero_of_asymptotic_averagedIncrement T hT μ hb
        (hut.comp hφ.tendsto_atTop) hν
      have hc : ∀ᵐ x ∂(ν : Measure (D E)), ContinuousAt (restrict (E := E) T) x :=
        (ae_iff.mpr hj).mono fun x hx => continuousAt_restrict hT hx
      have hm := ProbabilityMeasure.tendsto_map_of_ae_continuousAt hν
        (measurable_restrict T) hc
      refine ⟨ν.map (measurable_restrict T).aemeasurable, φ, hφ, ?_⟩
      exact hm.congr fun n => hu (φ n)
  have ht := isTightMeasureSet_of_isCompact_closure_of_polishSpace hρ
  convert ht using 1
  ext m
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨ρ n, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩

/-- Dirac laws at genuine constant paths satisfy the asymptotic criterion with zero
averaged increments. This gives an application of the restriction theorem. -/
theorem isTightMeasureSet_restrict_constantLaw
    (T : Time) (hT : 0 < T)
    (hsep : SeparableSpace (Cadlag.D T E)) (hcm : IsCompletelyMetrizableSpace (Cadlag.D T E))
    (a : E) :
    IsTightMeasureSet {(((constantLaw a).map
      (measurable_restrict (E := E) T).aemeasurable :
      ProbabilityMeasure (Cadlag.D T E)) : Measure (Cadlag.D T E)) | _n : ℕ} := by
  apply isTightMeasureSet_restrict_of_asymptotic_averagedIncrement T hT hsep hcm
    (fun _ => constantLaw a)
  · simpa only [range_const, closure_singleton] using
      (isCompact_singleton : IsCompact ({constantLaw a} : Set (ProbabilityMeasure (D E))))
  · intro η hη
    refine ⟨1, zero_lt_one, fun h _ _ => ⟨0, fun _ _ => ?_⟩⟩
    change ∫ x, averagedIncrement T h x ∂Measure.dirac (const a) ≤ η
    rw [integral_dirac, averagedIncrement_const]
    exact hη.le

end

end LatticeProb.Cadlag.HalfLine
