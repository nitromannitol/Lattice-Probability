/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8FinQ at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8LimPos
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Quantiles of continuous functionals of tight random metrics (DFGPS T:888–890)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:888–890): from tightness of
`λ_ε⁻¹ D_{h̊}^ε` and positivity of its subsequential limits, "this implies that `λ_ε` is bounded
above and below by `ε`-independent constants times the median `D̂_h^ε`-distance between the left
and right sides of `[0,1]²`". The probabilistic content is: for a continuous functional `Φ` of the
metric (the left–right distance) which is positive at metrics positive off the diagonal,
`Φ(A_δ)` is bounded above (tightness) and away from `0` (limits) in probability, uniformly in
small `δ`:

* `upper_quantile_of_tight`: `P(Φ(A_δ) > C) ≤ ζ` for all `δ ∈ (0,1)`;
* `lower_quantile_of_pos`: `P(Φ(A_δ) ≤ c) ≤ ζ` for all `δ ∈ (0, δ₀)` (contradiction argument:
  Prokhorov compactness + portmanteau for closed sets). Own standard argument (the paper says
  "this implies").
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Upper quantile from tightness.** -/
theorem upper_quantile_of_tight (A : ℝ → Ω → C(X × X, ℝ))
    (hAm : ∀ δ ∈ Ioo (0 : ℝ) 1, AEMeasurable (A δ) P)
    (hT : IsTightMeasureSet {μ | ∃ δ ∈ Ioo (0 : ℝ) 1, μ = P.map (A δ)})
    (Φ : C(X × X, ℝ) → ℝ) (hΦ : Continuous Φ) :
    ∀ ζ > 0, ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1, P {ω | C < Φ (A δ ω)} ≤ ENNReal.ofReal ζ := by
  intro ζ hζ
  obtain ⟨K, hK, hKm⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hT
    (ENNReal.ofReal ζ) (ENNReal.ofReal_pos.2 hζ)
  obtain ⟨C, hC⟩ := (hK.image hΦ).isBounded.bddAbove
  refine ⟨C, fun δ hδ => ?_⟩
  have hsub : {ω | C < Φ (A δ ω)} ⊆ A δ ⁻¹' Kᶜ := fun ω hω hK' =>
    (not_le.2 hω) (hC ⟨_, hK', rfl⟩)
  exact (measure_mono hsub).trans ((Measure.le_map_apply (hAm δ hδ) _).trans
    (hKm _ ⟨δ, hδ, rfl⟩))

/-- **Lower quantile from positivity of subsequential limits.** -/
theorem lower_quantile_of_pos [SecondCountableTopology X] (A : ℝ → Ω → C(X × X, ℝ))
    (hAm : ∀ δ ∈ Ioo (0 : ℝ) 1, AEMeasurable (A δ) P)
    (hT : IsTightMeasureSet {μ | ∃ δ ∈ Ioo (0 : ℝ) 1, μ = P.map (A δ)})
    (hpos : ∀ (δn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(X × X, ℝ))
      (μ : ProbabilityMeasure C(X × X, ℝ)),
      (∀ n, δn n ∈ Ioo (0 : ℝ) 1 ∧ (ν n : Measure _) = P.map (A (δn n))) →
      Tendsto δn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
      ∀ᵐ d ∂(μ : Measure C(X × X, ℝ)), IsPosOffDiag d)
    (Φ : C(X × X, ℝ) → ℝ) (hΦ : Continuous Φ) (hΦp : ∀ d, IsPosOffDiag d → 0 < Φ d) :
    ∀ ζ > 0, ∃ c > 0, ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | Φ (A δ ω) ≤ c} ≤ ENNReal.ofReal ζ := by
  intro ζ hζ
  by_contra hcon
  push_neg at hcon
  have hn : ∀ n : ℕ, ∃ δ ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 2)),
      ENNReal.ofReal ζ < P {ω | Φ (A δ ω) ≤ 1 / ((n : ℝ) + 1)} := fun n =>
    hcon _ (by positivity) _ (by positivity)
  choose δn hδn hlt using hn
  have hδ1 : ∀ n, δn n ∈ Ioo (0 : ℝ) 1 := fun n =>
    ⟨(hδn n).1, (hδn n).2.trans_le (by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])⟩
  have hδ0 : Tendsto δn atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (hδn n).1.le) (fun n => (hδn n).2.le) ?_
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) this
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  set ν : ℕ → ProbabilityMeasure C(X × X, ℝ) := fun n =>
    ⟨P.map (A (δn n)), (Measure.isProbabilityMeasure_map_iff (hAm _ (hδ1 n))).2 inferInstance⟩
  have hνT : IsTightMeasureSet {((μ : ProbabilityMeasure _) : Measure _) | μ ∈ range ν} :=
    hT.subset (by rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨δn n, hδ1 n, rfl⟩)
  obtain ⟨μ, -, ψ, hψ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hνT).tendsto_subseq
    (x := ν) fun n => subset_closure ⟨n, rfl⟩
  have hμpos := hpos (δn ∘ ψ) (ν ∘ ψ) μ (fun n => ⟨hδ1 _, rfl⟩)
    (hδ0.comp hψ.tendsto_atTop) hlim
  set F : ℕ → Set C(X × X, ℝ) := fun m => {d | Φ d ≤ 1 / ((m : ℝ) + 1)}
  have hFc : ∀ m, IsClosed (F m) := fun m => isClosed_le hΦ continuous_const
  have hge : ∀ m, ENNReal.ofReal ζ ≤ (μ : Measure _) (F m) := by
    intro m
    refine le_trans ?_ (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim (hFc m))
    refine Filter.le_limsup_of_frequently_le (Filter.Eventually.frequently ?_)
      (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop m] with n hn
    have hmn : m ≤ ψ n := hn.trans (hψ.id_le n)
    show ENNReal.ofReal ζ ≤ (P.map (A (δn (ψ n)))) (F m)
    refine (hlt (ψ n)).le.trans ((measure_mono ?_).trans
      (Measure.le_map_apply (hAm _ (hδ1 _)) _))
    intro ω hω
    show Φ (A (δn (ψ n)) ω) ≤ 1 / ((m : ℝ) + 1)
    refine le_trans hω (one_div_le_one_div_of_le (by positivity) ?_)
    have : (m : ℝ) ≤ ψ n := by exact_mod_cast hmn
    linarith
  have hanti : Antitone F := fun m m' hmm' d hd => by
    show Φ d ≤ 1 / ((m : ℝ) + 1)
    refine le_trans (show Φ d ≤ 1 / ((m' : ℝ) + 1) from hd)
      (one_div_le_one_div_of_le (by positivity) ?_)
    have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
    linarith
  have ht := tendsto_measure_iInter_atTop (μ := (μ : Measure _))
    (fun m => (hFc m).measurableSet.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have h0 : (μ : Measure _) (⋂ m, F m) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hμpos)
    intro d hd hposd
    have hp := hΦp d hposd
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hp
    have := mem_iInter.1 hd m
    simp only [F, mem_ofPred_eq] at this
    linarith
  rw [h0] at ht
  have := ge_of_tendsto ht (Eventually.of_forall hge)
  rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
  linarith

end LQGMetric.DFGPS
