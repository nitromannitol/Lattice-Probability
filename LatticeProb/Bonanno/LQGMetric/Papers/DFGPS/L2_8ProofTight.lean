/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8ProofTight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.Tight

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8, tightness transfer (T:887–888)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:887–888): "a.s. the metrics
`D̂_{h̊}^ε` and `D̂_h^ε` are bi-Lipschitz equivalent with (random) `ε`-independent Lipschitz
constants. By combining this with the conclusion of the preceding paragraph … the laws … are
tight". Also T:898 ("the metrics `D_{h+f}^ε` and `D_h^ε` are bi-Lipschitz equivalent").

The step "tight + random `ε`-independent Lipschitz bound ⇒ tight" is the tightness criterion
DFGPS T:909–913 (Arzelà–Ascoli + Prokhorov + triangle inequality; sufficient direction proved in
`LFPP.isTightMeasureSet_of_modulus`), combined with its easy converse for one compact set of
`C(X × X, ℝ)` (a compact set of continuous functions on a compact space has a uniform modulus of
continuity: finite net + uniform continuity of each member; own elementary argument).

* `DFGPS.exists_modulus_of_isCompact` — uniform modulus of a compact set of `C(Y, ℝ)`;
* `DFGPS.isTightMeasureSet_of_le_mul` — tightness transfer under `B ≤ K · A`, `K` a.s. finite.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

/-- **Uniform modulus of continuity of a compact set** of `C(Y, ℝ)`, `Y` compact metric. -/
theorem exists_modulus_of_isCompact {Y : Type*} [MetricSpace Y] [CompactSpace Y]
    {C : Set C(Y, ℝ)} (hC : IsCompact C) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ δ > 0, ∀ d ∈ C, ∀ p q : Y, dist p q ≤ δ → |d p - d q| ≤ ζ := by
  obtain ⟨t, htf, hcov⟩ := (Metric.totallyBounded_iff.1 hC.totallyBounded) (ζ / 3)
    (by positivity)
  have huc : ∀ g ∈ t, ∃ δ > 0, ∀ p q : Y, dist p q < δ → dist (g p) (g q) < ζ / 3 := fun g _ =>
    Metric.uniformContinuous_iff.1 (CompactSpace.uniformContinuous_of_continuous g.continuous)
      (ζ / 3) (by positivity)
  choose! δg hδg hδgc using huc
  obtain ⟨δ0, hδ0le, hδ0⟩ : ∃ δ0, (∀ g ∈ t, δ0 ≤ δg g) ∧ 0 < δ0 := by
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ g ∈ t, δ ≤ δg g :=
      (Filter.eventually_all_finite htf).2 fun g hg =>
        (eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (hδg g hg)))
    exact (hev.and self_mem_nhdsWithin).exists
  refine ⟨δ0 / 2, by positivity, fun d hd p q hpq => ?_⟩
  obtain ⟨g, hg, hdg⟩ := Set.mem_iUnion₂.1 (hcov hd)
  have hdg' : dist d g < ζ / 3 := hdg
  have h1 : |d p - g p| ≤ ζ / 3 := by
    rw [← Real.dist_eq]; exact (ContinuousMap.dist_apply_le_dist p).trans hdg'.le
  have h2 : |d q - g q| ≤ ζ / 3 := by
    rw [← Real.dist_eq]; exact (ContinuousMap.dist_apply_le_dist q).trans hdg'.le
  have h3 : |g p - g q| ≤ ζ / 3 := by
    rw [← Real.dist_eq]
    exact (hδgc g hg p q (lt_of_le_of_lt hpq (by linarith [hδ0le g hg]))).le
  calc |d p - d q| = |(d p - g p) + (g p - g q) + (g q - d q)| := by ring_nf
    _ ≤ |d p - g p| + |g p - g q| + |g q - d q| := abs_add_three _ _ _
    _ ≤ ζ / 3 + ζ / 3 + ζ / 3 := by rw [abs_sub_comm (g q)]; linarith
    _ = ζ := by ring

/-- the pseudo-metric axioms used by the tightness criterion, as a set of `C(X × X, ℝ)` -/
def pmetSet (X : Type*) [TopologicalSpace X] : Set C(X × X, ℝ) :=
  {d | (∀ x, d (x, x) = 0) ∧ ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z)}

theorem isClosed_pmetSet (X : Type*) [TopologicalSpace X] : IsClosed (pmetSet X) := by
  have e : pmetSet X = (⋂ x, {d : C(X × X, ℝ) | d (x, x) = 0}) ∩
      ⋂ x, ⋂ y, ⋂ z, {d : C(X × X, ℝ) | d (x, z) ≤ d (x, y) + d (y, z)} := by
    ext d; simp only [pmetSet, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [e]
  exact (isClosed_iInter fun x => isClosed_eq (continuous_eval_const _)
      continuous_const).inter
    (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_le (continuous_eval_const _)
        ((continuous_eval_const _).add (continuous_eval_const _)))

theorem isClosed_modulusSet (X : Type*) [PseudoMetricSpace X] (δ ζ : ℝ) :
    IsClosed {d : C(X × X, ℝ) | ∀ z w : X, dist z w ≤ δ → d (z, w) ≤ ζ} := by
  have e : {d : C(X × X, ℝ) | ∀ z w : X, dist z w ≤ δ → d (z, w) ≤ ζ} =
      ⋂ z, ⋂ w, ⋂ (_ : dist z w ≤ δ), {d : C(X × X, ℝ) | d (z, w) ≤ ζ} := by
    ext d; simp only [mem_iInter, mem_ofPred_eq]
  rw [e]
  exact isClosed_iInter fun z => isClosed_iInter fun w => isClosed_iInter fun _ =>
    isClosed_le (continuous_eval_const _) continuous_const

/-- **Tightness transfer** (DFGPS T:887–888, T:898): if the laws of the random continuous
functions `A i` (`i ∈ I`) are tight and a.s. vanish on the diagonal, and the random
pseudo-metrics `B i` satisfy a.s. `B i ≤ K · A i` with one a.s. finite random constant `K`, then
the laws of the `B i` are tight. -/
theorem isTightMeasureSet_of_le_mul {X : Type*} [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} (I : Set ι) (A B : ι → Ω → C(X × X, ℝ)) (K : Ω → ℝ) (hK : Measurable K)
    (hA : IsTightMeasureSet {μ | ∃ i ∈ I, μ = P.map (A i)})
    (hAm : ∀ i ∈ I, AEMeasurable (A i) P) (hBm : ∀ i ∈ I, AEMeasurable (B i) P)
    (hAd : ∀ i ∈ I, ∀ᵐ ω ∂P, ∀ x, A i ω (x, x) = 0)
    (hBp : ∀ i ∈ I, ∀ᵐ ω ∂P, B i ω ∈ pmetSet X)
    (hle : ∀ i ∈ I, ∀ᵐ ω ∂P, ∀ p, B i ω p ≤ K ω * A i ω p) :
    IsTightMeasureSet {μ | ∃ i ∈ I, μ = P.map (B i)} := by
  refine LFPP.isTightMeasureSet_of_modulus _ ?_ ?_
  · rintro μ ⟨i, hi, rfl⟩
    change Measure.map (B i) P (pmetSet X)ᶜ = 0
    rw [Measure.map_apply₀ (hBm i hi) (isClosed_pmetSet X).isOpen_compl.measurableSet.nullMeasurableSet]
    exact measure_eq_zero_iff_ae_notMem.2 ((hBp i hi).mono fun ω hω h => h hω)
  intro ζ hζ
  -- `K` is a.s. bounded by `M` up to probability `ζ / 2`
  have hKt : Tendsto (fun n : ℕ => P {ω | (n : ℝ) < |K ω|}) atTop (𝓝 0) := by
    have hm : Antitone fun n : ℕ => {ω | (n : ℝ) < |K ω|} := fun m n hmn ω hω => by
      simp only [mem_ofPred_eq] at hω ⊢
      exact lt_of_le_of_lt (by exact_mod_cast hmn) hω
    have hI : (⋂ n : ℕ, {ω | (n : ℝ) < |K ω|}) = ∅ := by
      ext ω; simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
        not_lt]
      exact exists_nat_ge _
    have := tendsto_measure_iInter_atTop (μ := P)
      (fun n : ℕ => (measurableSet_lt measurable_const (continuous_abs.measurable.comp hK)).nullMeasurableSet) hm
      ⟨0, measure_ne_top _ _⟩
    simp only [Function.comp_def] at this
    rwa [hI, measure_empty] at this
  obtain ⟨n, hn⟩ := (hKt.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal (ζ / 2) by
    simp; positivity))).exists
  set M : ℝ := n + 1
  have hM : 0 < M := by positivity
  obtain ⟨C, hCc, hCμ⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hA)
    (ENNReal.ofReal (ζ / 2)) (by simp; positivity)
  obtain ⟨δ, hδ, hmod⟩ := exists_modulus_of_isCompact hCc (ζ := ζ / M) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  rintro μ ⟨i, hi, rfl⟩
  have hFm : MeasurableSet {d : C(X × X, ℝ) | ¬ ∀ z w : X, dist z w ≤ δ → d (z, w) ≤ ζ} :=
    (isClosed_modulusSet X δ ζ).isOpen_compl.measurableSet
  rw [Measure.map_apply₀ (hBm i hi) hFm.nullMeasurableSet]
  have hAC : P (A i ⁻¹' Cᶜ) ≤ ENNReal.ofReal (ζ / 2) := by
    rw [← Measure.map_apply₀ (hAm i hi) hCc.isClosed.isOpen_compl.measurableSet.nullMeasurableSet]
    exact hCμ _ ⟨i, hi, rfl⟩
  have hsub : ∀ᵐ ω ∂P, ω ∈ (B i ⁻¹' {d | ¬ ∀ z w : X, dist z w ≤ δ → d (z, w) ≤ ζ}) →
      ω ∈ {ω | (n : ℝ) < |K ω|} ∪ A i ⁻¹' Cᶜ := by
    filter_upwards [hAd i hi, hle i hi] with ω hd hl
    intro hω
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, mem_preimage, mem_compl_iff, not_or, not_lt,
      not_not] at hc
    refine hω fun z w hzw => ?_
    have h1 := hmod (A i ω) hc.2 (z, w) (z, z) (by
      rw [Prod.dist_eq, dist_self, dist_comm]; exact max_le hδ.le hzw)
    rw [hd z, sub_zero] at h1
    calc B i ω (z, w) ≤ K ω * A i ω (z, w) := hl _
      _ ≤ |K ω| * |A i ω (z, w)| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ M * (ζ / M) := mul_le_mul (by simp only [M]; linarith) h1 (abs_nonneg _) hM.le
      _ = ζ := by field_simp
  calc P _ ≤ P ({ω | (n : ℝ) < |K ω|} ∪ A i ⁻¹' Cᶜ) := measure_mono_ae hsub
    _ ≤ P {ω | (n : ℝ) < |K ω|} + P (A i ⁻¹' Cᶜ) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ζ / 2) + ENNReal.ofReal (ζ / 2) := add_le_add hn.le hAC
    _ = ENNReal.ofReal ζ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end LQGMetric.DFGPS
