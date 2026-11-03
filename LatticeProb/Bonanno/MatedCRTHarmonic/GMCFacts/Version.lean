/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.Version at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.GMCInterfaces
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge

/-!
# A measurable version of a circle-average process

`LQGDimension.IsGFFCircleAverage H P` only asks each finite family of circle averages to be Gaussian (hence
a.e.-measurable) and every path `z ↦ H r z ω` to be continuous. For moment estimates we need each `H r z` to be
measurable and `(z, ω) ↦ H r z ω` jointly measurable. `exists_measurable_version` modifies `H`, radius by radius, on a
null set: for `r > 0` the new process is `𝟙_{G_r} · H r`, where `G_r` is a measurable full-measure event on which `H r`
agrees with measurable versions at the points of a dense sequence; on `G_r` the path is the limit of those versions
(continuity), which gives measurability. The new process is again a whole-plane GFF circle-average process, and for
each `r > 0` its whole path at radius `r` agrees with that of `H` almost surely. Own elementary measure theory.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-- For a continuous-path process indexed by a pseudometric space with a dense sequence, whose values at the points
of the sequence agree, on a measurable event `G`, with measurable functions, the restriction `𝟙_G · X t` is measurable
for every `t`. -/
lemma measurable_indicator_of_dense {T : Type*} [PseudoMetricSpace T] {X : T → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => X t ω)
    {d : ℕ → T} (hd : DenseRange d) {f : ℕ → Ω → ℝ} (hf : ∀ n, Measurable (f n)) {G : Set Ω}
    (hG : MeasurableSet G) (hGf : ∀ ω ∈ G, ∀ n, X (d n) ω = f n ω) (z : T) :
    Measurable (G.indicator (X z)) := by
  -- a sequence of indices with `d (u k) → z`
  have hex : ∀ k : ℕ, ∃ n, dist (d n) z < 1 / ((k : ℝ) + 1) := fun k => by
    obtain ⟨n, hn⟩ := hd.exists_dist_lt z (Nat.one_div_pos_of_nat (n := k))
    exact ⟨n, by rwa [dist_comm]⟩
  choose u hu using hex
  have hdu : Tendsto (fun k => d (u k)) atTop (𝓝 z) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => (hu k).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  refine measurable_of_tendsto_metrizable (f := fun k => G.indicator (f (u k)))
    (fun k => (hf (u k)).indicator hG) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω]
    have := ((hc ω).tendsto z).comp hdu
    refine this.congr fun k => ?_
    simp only [Function.comp_apply]
    exact hGf ω hω (u k)
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

/-- **Measurable version of a continuous-path process**: if every path `t ↦ Y t ω` is continuous (index a separable
pseudometric space) and every `Y t` is a.e.-measurable, there is a measurable full-measure event `G` with
`𝟙_G · Y t` measurable for every `t`. -/
lemma exists_goodSet_of_continuous {T : Type*} [PseudoMetricSpace T]
    [TopologicalSpace.SeparableSpace T] [Nonempty T] {Y : T → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => Y t ω) (hm : ∀ t, AEMeasurable (Y t) P) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ t, Measurable (G.indicator (Y t)) := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq T
  set f : ℕ → Ω → ℝ := fun n => (hm (d n)).mk _
  have hall : ∀ᵐ ω ∂P, ∀ n, Y (d n) ω = f n ω := ae_all_iff.2 fun n => (hm (d n)).ae_eq_mk
  set G : Set Ω := (toMeasurable P {ω | ∀ n, Y (d n) ω = f n ω}ᶜ)ᶜ
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGc : P Gᶜ = 0 := by
    simp only [G, compl_compl, measure_toMeasurable]
    exact ae_iff.1 hall
  have hGsub : G ⊆ {ω | ∀ n, Y (d n) ω = f n ω} := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  exact ⟨G, hGm, hGc, measurable_indicator_of_dense hc hd
    (fun n => (hm (d n)).measurable_mk) hGm (fun ω hω => hGsub hω)⟩

/-- The good event at one radius: a measurable full-measure event on which `𝟙_G · H r z` is measurable in `ω` for
every `z`. -/
lemma exists_goodSet (hH : LQGDimension.IsGFFCircleAverage H P) {r : ℝ} (hr : 0 < r) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ z, Measurable (G.indicator (H r z)) :=
  exists_goodSet_of_continuous (hH.continuous r hr) fun z =>
    hH.isGaussianProcess.aemeasurable (⟨r, hr⟩, z)

/-- **A measurable version** of a whole-plane GFF circle-average process: again `IsGFFCircleAverage`, every
coordinate measurable, and at each radius `r > 0` the whole path agrees with that of `H` almost surely. -/
theorem exists_measurable_version (hH : LQGDimension.IsGFFCircleAverage H P) :
    ∃ H' : ℝ → ℂ → Ω → ℝ, LQGDimension.IsGFFCircleAverage H' P ∧ (∀ r z, Measurable (H' r z)) ∧
      ∀ r, 0 < r → ∀ᵐ ω ∂P, ∀ z, H' r z ω = H r z ω := by
  classical
  have hG : ∀ r : ℝ, ∃ G : Set Ω, 0 < r → MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ z, Measurable (G.indicator (H r z)) := fun r => by
    by_cases hr : 0 < r
    · obtain ⟨G, h1, h2, h3⟩ := exists_goodSet hH hr
      exact ⟨G, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun h => absurd h hr⟩
  choose G hGp using hG
  set H' : ℝ → ℂ → Ω → ℝ := fun r z => if 0 < r then (G r).indicator (H r z) else 0
  have hae : ∀ r, 0 < r → ∀ᵐ ω ∂P, ∀ z, H' r z ω = H r z ω := fun r hr => by
    have hc : ∀ᵐ ω ∂P, ω ∈ G r := by
      rw [ae_iff]
      exact (hGp r hr).2.1
    filter_upwards [hc] with ω hω z
    simp only [H', hr, ↓reduceIte, indicator_of_mem hω]
  have hae' : ∀ r, 0 < r → ∀ z, H' r z =ᵐ[P] H r z := fun r hr z => by
    filter_upwards [hae r hr] with ω hω
    exact hω z
  refine ⟨H', ⟨hH.isProbabilityMeasure, ?_, ?_, ?_, ?_⟩, ?_, hae⟩
  · exact hH.isGaussianProcess.congr fun p => (hae' p.1 p.1.2 p.2).symm
  · intro ε hε z
    rw [integral_congr_ae (hae' ε hε z)]
    exact hH.integral_eq_zero ε hε z
  · intro ε hε δ hδ z w
    rw [LQGMetric.CircleAvg.covariance_congr_ae (hae' ε hε z) (hae' δ hδ w)]
    exact hH.covariance_eq ε hε δ hδ z w
  · intro ε hε ω
    simp only [H', hε, ↓reduceIte]
    by_cases hω : ω ∈ G ε
    · simp only [indicator_of_mem hω]
      exact hH.continuous ε hε ω
    · simp only [indicator_of_notMem hω]
      exact continuous_const
  · intro r z
    by_cases hr : 0 < r
    · simp only [H', hr, ↓reduceIte]
      exact (hGp r hr).2.2 z
    · simp only [H', hr, ↓reduceIte]
      exact measurable_const

end MatedCRTHarmonic.GMCFacts
