import Mathlib
import LatticeProb.LQG.LQGMeasure

/-!
# Deterministic locality of the vague LQG limit: LP form

LP copy of `HarmonicBalls/Proofs/Sec2/LQGLimitLocality.lean` (111 lines). `IsLQGLimit γ hε m` is the deterministic vague-limit
statement defining the LQG measure (Duplantier-Sheffield 2011, Prop. 1.1; `LatticeProb/LQG/LQGMeasure.lean`). Two elementary
properties: if two circle-average families agree at all small dyadic scales on each compact subset of an open set `U`,
then their vague limits agree on `U` (`isLQGLimit_restrict_eq`), and the measures of compact sets are ordered accordingly.
The statements use no Harmonic-balls object.
-/

namespace LatticeProb.LQG.LQGMeasureNonatomicMass

open MeasureTheory Filter Topology Set

/-- If `ν`, `ν'` are locally finite and agree on integrals of continuous compactly supported functions with `tsupport ⊆ U`,
then `ν K ≤ ν' K` for compact `K ⊆ U` (LP copy of `HarmonicBalls.measure_le_of_integral_eq_of_tsupport_subset`). -/
theorem measure_le_of_integral_eq_of_tsupport_subset {U : Set ℂ} (hU : IsOpen U) {ν ν' : Measure ℂ}
    [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ν']
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∫ x, f x ∂ν = ∫ x, f x ∂ν')
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) : ν K ≤ ν' K := by
  rw [hK.measure_eq_iInf_isOpen (μ := ν')]
  refine le_iInf fun V => le_iInf fun hKV => le_iInf fun hV => ?_
  have hKVU : K ⊆ V ∩ U := subset_inter hKV hKU
  obtain ⟨f, hf1, hfc, hfV, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK (hV.inter hU) hKVU
  have hfcont : Continuous (f : ℂ → ℝ) := f.continuous
  have hfsupp : HasCompactSupport (f : ℂ → ℝ) := hfc
  have hfint : ∀ μ : Measure ℂ, [IsLocallyFiniteMeasure μ] → Integrable (f : ℂ → ℝ) μ := fun μ _ =>
    hfcont.integrable_of_hasCompactSupport hfsupp
  have hnn : ∀ x, 0 ≤ f x := fun x => (hf01 x).1
  have h1 : ν K ≤ ENNReal.ofReal (∫ x, f x ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hfint ν) (Eventually.of_forall hnn)]
    calc ν K = ∫⁻ x, K.indicator 1 x ∂ν := by
          rw [lintegral_indicator_one hK.measurableSet]
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ K
          · simp [hx, hf1 hx]
          · simp [hx]
  have h2 : ENNReal.ofReal (∫ x, f x ∂ν') ≤ ν' (V ∩ U) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hfint ν') (Eventually.of_forall hnn)]
    calc ∫⁻ x, ENNReal.ofReal (f x) ∂ν' ≤ ∫⁻ x, (V ∩ U).indicator 1 x ∂ν' := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ V ∩ U
          · have := (hf01 x).2
            simp [hx, this]
          · have : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hfV hx'))
            simp [hx, this]
      _ = ν' (V ∩ U) := by
          rw [lintegral_indicator_one (hV.inter hU).measurableSet]
  calc ν K ≤ ENNReal.ofReal (∫ x, f x ∂ν) := h1
    _ = ENNReal.ofReal (∫ x, f x ∂ν') := by rw [h f hfcont hfsupp (hfV.trans inter_subset_right)]
    _ ≤ ν' (V ∩ U) := h2
    _ ≤ ν' V := measure_mono inter_subset_left

/-- Two locally finite measures on `ℂ` with the same integrals of the continuous compactly supported functions supported in an
open set `U` agree on `U` (LP copy of `HarmonicBalls.restrict_eq_of_integral_eq_of_tsupport_subset`). -/
theorem restrict_eq_of_integral_eq_of_tsupport_subset {U : Set ℂ} (hU : IsOpen U) {ν ν' : Measure ℂ}
    [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ν']
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∫ x, f x ∂ν = ∫ x, f x ∂ν') :
    ν.restrict U = ν'.restrict U := by
  have hK : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ν K = ν' K := fun K hK hKU =>
    le_antisymm (measure_le_of_integral_eq_of_tsupport_subset hU h hK hKU)
      (measure_le_of_integral_eq_of_tsupport_subset hU (fun f hf hc hs => (h f hf hc hs).symm) hK hKU)
  have hopen : ∀ V : Set ℂ, IsOpen V → ν (V ∩ U) = ν' (V ∩ U) := by
    intro V hV
    rw [(hV.inter hU).measure_eq_iSup_isCompact ν, (hV.inter hU).measure_eq_iSup_isCompact ν']
    refine iSup_congr fun K => iSup_congr fun hKV => iSup_congr fun hKc => ?_
    exact hK K hKc (hKV.trans inter_subset_right)
  refine Measure.ext_of_generateFrom_of_iUnion (C := {s : Set ℂ | IsOpen s})
    (fun n : ℕ => Metric.ball (0 : ℂ) (n + 1)) ?_ isPiSystem_isOpen ?_ ?_ ?_ ?_
  · exact BorelSpace.measurable_eq (α := ℂ)
  · refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
    exact ⟨n, by simpa [Metric.mem_ball, dist_zero_right] using hn.trans (lt_add_one _)⟩
  · exact fun n => (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) (n + 1)))
  · intro n
    exact ((Measure.restrict_apply_le _ _).trans_lt measure_ball_lt_top).ne
  · intro V (hV : IsOpen V)
    rw [Measure.restrict_apply hV.measurableSet, Measure.restrict_apply hV.measurableSet]
    exact hopen V hV

/-- **Locality of the LQG limit** (LP copy of `HarmonicBalls.IsLQGLimit.restrict_eq`). If two circle-average functions agree, at
all small dyadic scales, on every compact subset of an open set `U`, then their vague limits agree on `U`. -/
theorem isLQGLimit_restrict_eq {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {m m' : Measure ℂ}
    (hm : IsLQGLimit γ hε m) (hm' : IsLQGLimit γ hε' m') {U : Set ℂ} (hU : IsOpen U)
    (hloc : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, hε (dyadicScale k) z = hε' (dyadicScale k) z) :
    m.restrict U = m'.restrict U := by
  have := hm.isLocallyFiniteMeasure
  have := hm'.isLocallyFiniteMeasure
  refine restrict_eq_of_integral_eq_of_tsupport_subset hU fun f hf hfc hfU => ?_
  have hK : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hzero : ∀ ν : Measure ℂ, ∫ x, f x ∂ν = ∫ x in tsupport f, f x ∂ν := fun ν =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport hx).symm
  have heq : (fun k : ℕ => ∫ z, f z ∂(lqgApprox γ hε (dyadicScale k))) =ᶠ[atTop]
      fun k : ℕ => ∫ z, f z ∂(lqgApprox γ hε' (dyadicScale k)) := by
    filter_upwards [hloc _ hfc hfU] with k hk
    have hme : (lqgApprox γ hε (dyadicScale k)).restrict (tsupport f) =
        (lqgApprox γ hε' (dyadicScale k)).restrict (tsupport f) := by
      simp only [lqgApprox]
      rw [restrict_withDensity hK, restrict_withDensity hK]
      refine withDensity_congr_ae ?_
      filter_upwards [ae_restrict_mem hK] with x hx
      rw [hk x hx]
    rw [hzero (lqgApprox γ hε (dyadicScale k)), hzero (lqgApprox γ hε' (dyadicScale k)), hme]
  exact tendsto_nhds_unique ((hm.tendsto_integral f hf hfc).congr' heq) (hm'.tendsto_integral f hf hfc)

end LatticeProb.LQG.LQGMeasureNonatomicMass
