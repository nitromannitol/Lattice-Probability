import LatticeProb.Analysis.VagueLimitCompactMass
import LatticeProb.LQG.AreaReparamMeasurable

/-!
# Measurability of the mass parametrization condition for LQG area approximations

For a field `h` and a continuous curve `η`, `CurveMassCondition (lqgAreaApprox γ h) η` is the
countable condition that, for all rational `s ≤ t`, the iterated limit of the integrals of the
compact cutoffs of `η([s, t])` against the dyadic `γ`-LQG area approximations of `h` equals `t - s`.
Once a vague limit of the approximations exists, it is equivalent to the statement that every vague
limit parametrizes `η` by its mass (`LatticeProb.VagueLimit.forall_isVagueLimit_measure_image_Icc_iff`).

This file proves that the condition defines a measurable set of pairs `(h, η)`
(`measurableSet_curveMassCondition_lqgAreaApprox`). The ingredients are:

* `infEDist_image_Icc_eq_iInf`: for a continuous curve and rational `s ≤ t`, the distance from a
  point to `η([s, t])` is the infimum of its distances to `η(q)` over the rational `q ∈ [s, t]`;
* `measurable_compactCutoff_image_Icc`: the compact cutoffs of `η([s, t])` are jointly measurable in
  the curve and the point;
* `measurable_integral_withDensity_ofReal_uncurry_param`: integrals of jointly measurable integrands
  against measures with jointly measurable densities depend measurably on the parameter.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG

open LQGMetric MatedCRTHarmonic.CellScaling LatticeProb.VagueLimit

/-- For rational `s ≤ t`, the rational points of `[s, t]` are dense in `[s, t]`. -/
theorem Icc_subset_closure_range_rat (s t : ℚ) (hst : s ≤ t) :
    Icc (s : ℝ) t ⊆ closure (range fun q : {q : ℚ // s ≤ q ∧ q ≤ t} => (q.1 : ℝ)) := by
  rcases hst.lt_or_eq with hlt | rfl
  · have hlt' : (s : ℝ) < t := by exact_mod_cast hlt
    rw [← closure_Ioo hlt'.ne]
    refine closure_minimal (fun x hx => ?_) isClosed_closure
    refine closure_mono ?_
      (Dense.open_subset_closure_inter (Rat.denseRange_cast (𝕜 := ℝ)) isOpen_Ioo hx)
    rintro y ⟨hy, q, rfl⟩
    exact ⟨⟨q, by exact_mod_cast hy.1.le, by exact_mod_cast hy.2.le⟩, rfl⟩
  · intro x hx
    rw [Icc_self] at hx
    exact subset_closure ⟨⟨s, le_rfl, le_rfl⟩, hx.symm⟩

/-- For a continuous curve `η` and rational `s ≤ t`, the distance from a point to `η([s, t])` is
the infimum of its distances to the points `η(q)`, `q ∈ [s, t]` rational. -/
theorem infEDist_image_Icc_eq_iInf {X : Type*} [PseudoEMetricSpace X] {η : ℝ → X}
    (hη : Continuous η) (s t : ℚ) (hst : s ≤ t) (z : X) :
    infEDist z (η '' Icc (s : ℝ) t) = ⨅ q : {q : ℚ // s ≤ q ∧ q ≤ t}, edist z (η q.1) := by
  set D := range fun q : {q : ℚ // s ≤ q ∧ q ≤ t} => (q.1 : ℝ)
  have hD : D ⊆ Icc (s : ℝ) t := by
    rintro _ ⟨q, rfl⟩
    exact ⟨Rat.cast_le.2 q.2.1, Rat.cast_le.2 q.2.2⟩
  have h2 : η '' Icc (s : ℝ) t ⊆ closure (η '' D) :=
    (image_mono (Icc_subset_closure_range_rat s t hst)).trans
      (image_closure_subset_closure_image hη)
  have heq : infEDist z (η '' Icc (s : ℝ) t) = infEDist z (η '' D) :=
    le_antisymm (infEDist_anti (image_mono hD))
      (by rw [← infEDist_closure (s := η '' D)]; exact infEDist_anti h2)
  rw [heq, ← range_comp]
  simp only [infEDist, iInf_range, Function.comp_apply]

/-- For rational `s ≤ t`, the distance from a point to the image of `[s, t]` under a continuous
curve is jointly measurable in the curve and the point. -/
theorem measurable_infEDist_image_Icc (s t : ℚ) (hst : s ≤ t) :
    Measurable fun p : C(ℝ, ℂ) × ℂ => infEDist p.2 (p.1 '' Icc (s : ℝ) t) := by
  have e : (fun p : C(ℝ, ℂ) × ℂ => infEDist p.2 (p.1 '' Icc (s : ℝ) t)) =
      fun p => ⨅ q : {q : ℚ // s ≤ q ∧ q ≤ t}, edist p.2 (p.1 q.1) := by
    funext p
    exact infEDist_image_Icc_eq_iInf p.1.continuous s t hst p.2
  rw [e]
  exact Measurable.iInf fun q =>
    measurable_snd.edist ((ContinuousMap.measurable_eval (q.1 : ℝ)).comp measurable_fst)

/-- For rational `s ≤ t`, the compact cutoffs of the image of `[s, t]` under a continuous curve are
jointly measurable in the curve and the point. -/
theorem measurable_compactCutoff_image_Icc (s t : ℚ) (hst : s ≤ t) (n : ℕ) :
    Measurable fun p : C(ℝ, ℂ) × ℂ => compactCutoff (p.1 '' Icc (s : ℝ) t) n p.2 := by
  have h := measurable_infEDist_image_Icc s t hst
  show Measurable fun p : C(ℝ, ℂ) × ℂ =>
    ((thickenedIndicatorAux (1 / ((n : ℝ) + 1)) (p.1 '' Icc (s : ℝ) t) p.2).toNNReal : ℝ)
  unfold thickenedIndicatorAux
  exact measurable_coe_nnreal_real.comp
    (ENNReal.measurable_toNNReal.comp (measurable_const.sub (h.div_const _)))

/-- Integrals of a jointly measurable integrand against measures on `ℂ` with jointly measurable
densities are measurable in the parameter. -/
theorem measurable_integral_withDensity_ofReal_uncurry_param {Ω : Type*} [MeasurableSpace Ω]
    {d : Ω → ℂ → ℝ} (hd : Measurable (Function.uncurry d)) (hd0 : ∀ ω z, 0 ≤ d ω z)
    {f : Ω → ℂ → ℝ} (hf : Measurable (Function.uncurry f)) :
    Measurable fun ω =>
      ∫ z, f ω z ∂((volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (d ω z)) := by
  have e : ∀ ω, ∫ z, f ω z ∂((volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (d ω z)) =
      ∫ z, d ω z * f ω z := by
    intro ω
    have hm : Measurable fun z => Real.toNNReal (d ω z) :=
      (hd.comp measurable_prodMk_left).real_toNNReal
    rw [show (fun z => ENNReal.ofReal (d ω z)) = fun z => ((Real.toNNReal (d ω z) : ℝ≥0) : ℝ≥0∞)
      from rfl, integral_withDensity_eq_integral_smul hm]
    congr 1
    funext z
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hd0 ω z), smul_eq_mul]
  simp_rw [e]
  exact (hd.mul hf).stronglyMeasurable.integral_prod_right'.measurable

/-- For rational `s ≤ t`, the integral of a compact cutoff of `η([s, t])` against the `k`-th
dyadic `γ`-LQG area approximation of `h` is a measurable function of the pair `(h, η)`. -/
theorem measurable_integral_compactCutoff_lqgAreaApprox (γ : ℝ) (s t : ℚ) (hst : s ≤ t)
    (n k : ℕ) : Measurable fun p : DistC × C(ℝ, ℂ) =>
      ∫ z, compactCutoff (p.2 '' Icc (s : ℝ) t) n z ∂(lqgAreaApprox γ p.1 k) := by
  have hφ : Measurable fun q : (DistC × C(ℝ, ℂ)) × ℂ => (q.1.1, q.2) :=
    measurable_fst.fst.prodMk measurable_snd
  have hψ : Measurable fun q : (DistC × C(ℝ, ℂ)) × ℂ => (q.1.2, q.2) :=
    measurable_fst.snd.prodMk measurable_snd
  have hd := (measurable_lqgAreaDensity_uncurry_field γ k).comp hφ
  have hf := (measurable_compactCutoff_image_Icc s t hst n).comp hψ
  exact measurable_integral_withDensity_ofReal_uncurry_param
    (d := fun (p : DistC × C(ℝ, ℂ)) (z : ℂ) =>
      dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg p.1 (dyadicScale k) z))
    (f := fun (p : DistC × C(ℝ, ℂ)) (z : ℂ) => compactCutoff (p.2 '' Icc (s : ℝ) t) n z) hd
    (fun _ _ => mul_nonneg (Real.rpow_nonneg (by unfold dyadicScale; positivity) _)
      (Real.exp_pos _).le) hf

/-- **Measurability of the mass parametrization condition.** The pairs `(h, η)` of a field and a
continuous curve such that the dyadic `γ`-LQG area approximations of `h` satisfy the countable
mass condition along `η` (for all rational `s ≤ t`, the iterated limit of the integrals of the
compact cutoffs of `η([s, t])` equals `t - s`) form a measurable set. -/
theorem measurableSet_curveMassCondition_lqgAreaApprox (γ : ℝ) :
    MeasurableSet {p : DistC × C(ℝ, ℂ) | CurveMassCondition (lqgAreaApprox γ p.1) p.2} := by
  have e : {p : DistC × C(ℝ, ℂ) | CurveMassCondition (lqgAreaApprox γ p.1) p.2} =
      ⋂ s : ℚ, ⋂ t : ℚ, ⋂ (_ : s ≤ t), {p : DistC × C(ℝ, ℂ) | Tendsto (fun n => limUnder atTop
        (fun k => ∫ z, compactCutoff (p.2 '' Icc (s : ℝ) t) n z ∂(lqgAreaApprox γ p.1 k)))
          atTop (𝓝 ((t : ℝ) - s))} := by
    ext p
    simp only [mem_iInter]
    exact Iff.rfl
  rw [e]
  exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun t => MeasurableSet.iInter
    fun hst => measurableSet_tendsto _ fun n => (StronglyMeasurable.limUnder fun k =>
      (measurable_integral_compactCutoff_lqgAreaApprox γ s t hst n k).stronglyMeasurable).measurable

/-- For measurable maps `ω ↦ h ω` to fields and `ω ↦ η ω` to continuous curves, the set of `ω` at
which the dyadic `γ`-LQG area approximations of `h ω` satisfy the countable mass condition along
`η ω` is measurable. -/
theorem measurableSet_curveMassCondition_lqgAreaApprox_comp {Ω : Type*} [MeasurableSpace Ω]
    (γ : ℝ) {h : Ω → DistC} {η : Ω → C(ℝ, ℂ)} (hh : Measurable h) (hη : Measurable η) :
    MeasurableSet {ω | CurveMassCondition (lqgAreaApprox γ (h ω)) (η ω)} := by
  simpa only [preimage_ofPred_eq] using
    (measurableSet_curveMassCondition_lqgAreaApprox γ).preimage (hh.prodMk hη)

end LatticeProb.LQG
