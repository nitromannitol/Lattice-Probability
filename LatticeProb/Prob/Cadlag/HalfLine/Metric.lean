import LatticeProb.Prob.Cadlag.HalfLine.Triangle
import LatticeProb.Prob.Cadlag.HalfLine.ZeroDistance
import LatticeProb.Prob.Cadlag.HalfLine.PathMaps
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# The metric on half-line càdlàg paths

The finite Ethier–Kurtz distance equips the genuine càdlàg carrier with a metric.
The identity time change bounds this distance by uniform discrepancies.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

variable {E : Type*} [MetricSpace E]

/-- The Ethier–Kurtz distance defines the metric on half-line càdlàg paths. -/
instance : MetricSpace (D E) where
  dist := skorohodDistance
  dist_self := skorohodDistance_self
  dist_comm := skorohodDistance_comm
  dist_triangle := skorohodDistance_triangle
  eq_of_dist_eq_zero := eq_of_skorohodDistance_eq_zero

/-- The carrier distance is exactly the real Ethier–Kurtz distance. -/
theorem dist_eq_skorohodDistance (x y : D E) : dist x y = skorohodDistance x y := rfl

/-- Paths carry the Borel sigma algebra of the Skorokhod metric. -/
instance : MeasurableSpace (D E) := borel (D E)

/-- The chosen path sigma algebra is Borel. -/
instance : BorelSpace (D E) := ⟨rfl⟩

/-- With the identity time change, stopping is the supremum over the initial interval. -/
theorem discrepancy_identity (x y : D E) (u : Time) :
    discrepancy x y (OrderIso.refl Time) u = ⨆ t ≤ u, q (x.1 t) (y.1 t) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    exact le_iSup_of_le (min t u) (le_iSup_of_le (min_le_right _ _) le_rfl)
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    simpa only [discrepancy, OrderIso.refl_apply, min_eq_left ht] using
      (le_iSup (fun s => q (x.1 (min s u)) (y.1 (min s u))) t)

/-- Identity time change bounds the extended distance by the uniform discrepancy integral. -/
theorem skorohodDistanceExtended_le_uniform (x y : D E) :
    skorohodDistanceExtended x y ≤ ∫⁻ u : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-u)) * ⨆ t ≤ u.toNNReal, q (x.1 t) (y.1 t) := by
  apply (iInf_le _ identityChange).trans
  simp only [identityChange, gamma_identity, integratedDiscrepancy,
    discrepancy_identity, max_eq_right (show (0 : ℝ≥0∞) ≤ _ from zero_le)]
  exact le_rfl

/-- The uniform discrepancy integral has an exponentially small tail. -/
theorem uniformIntegral_le (x y : D E) (M : Time) :
    (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-u)) *
      ⨆ t ≤ u.toNNReal, q (x.1 t) (y.1 t)) ≤
      (⨆ t ≤ M, q (x.1 t) (y.1 t)) + ENNReal.ofReal (Real.exp (-(M : ℝ))) := by
  let S := ⨆ t ≤ M, q (x.1 t) (y.1 t)
  let f := fun u : ℝ => ENNReal.ofReal (Real.exp (-u)) *
    ⨆ t ≤ u.toNNReal, q (x.1 t) (y.1 t)
  have hS : S ≠ ∞ := ne_of_lt ((iSup_le fun t => iSup_le fun _ =>
    min_le_right (edist (x.1 t) (y.1 t)) 1).trans_lt ENNReal.one_lt_top)
  rw [← lintegral_inter_add_sdiff f (Ioi 0) measurableSet_Iic]
  apply add_le_add
  · calc
      ∫⁻ u in Ioi (0 : ℝ) ∩ Iic (M : ℝ), f u ≤
          ∫⁻ u in Ioi (0 : ℝ) ∩ Iic (M : ℝ),
            ENNReal.ofReal (Real.exp (-u)) * S := by
        apply setLIntegral_mono' (measurableSet_Ioi.inter measurableSet_Iic)
        intro u hu
        dsimp only [f]
        apply mul_le_mul_right
        apply iSup_le
        intro t
        apply iSup_le
        intro ht
        exact le_iSup_of_le t (le_iSup_of_le
          (ht.trans (Real.toNNReal_le_iff_le_coe.mpr hu.2)) le_rfl)
      _ ≤ ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-u)) * S :=
        lintegral_mono_set inter_subset_left
      _ = S := by rw [lintegral_mul_const' _ _ hS, exponential_mass, one_mul]
  · have hset : Ioi (0 : ℝ) \ Iic (M : ℝ) = Ioi (M : ℝ) := by
      ext u
      simp only [Set.mem_sdiff, mem_Ioi, mem_Iic, not_le]
      exact ⟨fun h => h.2, fun h => ⟨M.2.trans_lt h, h⟩⟩
    rw [hset]
    calc
      ∫⁻ u in Ioi (M : ℝ), f u ≤
          ∫⁻ u in Ioi (M : ℝ), ENNReal.ofReal (Real.exp (-u)) := by
        apply lintegral_mono
        intro u
        exact (mul_le_mul_right (iSup_le fun t => iSup_le fun _ =>
          min_le_right (edist (x.1 t) (y.1 t)) 1) _).trans_eq (mul_one _)
      _ = ENNReal.ofReal (Real.exp (-(M : ℝ))) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi _)
          (Eventually.of_forall fun u => (Real.exp_pos (-u)).le), integral_exp_neg_Ioi]

/-- The uniform discrepancy integral is finite because the weight has mass one. -/
theorem uniformIntegral_le_one (x y : D E) :
    (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-u)) *
      ⨆ t ≤ u.toNNReal, q (x.1 t) (y.1 t)) ≤ 1 := by
  calc
    _ ≤ ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-u)) := by
      apply lintegral_mono
      intro u
      exact (mul_le_mul_right (iSup_le fun t => iSup_le fun _ =>
        min_le_right (edist (x.1 t) (y.1 t)) 1) _).trans_eq (mul_one _)
    _ = 1 := exponential_mass

/-- The real metric is bounded by the real value of the uniform discrepancy integral. -/
theorem dist_le_uniformIntegral (x y : D E) :
    dist x y ≤ (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-u)) *
      ⨆ t ≤ u.toNNReal, q (x.1 t) (y.1 t)).toReal :=
  ENNReal.toReal_mono
    (ne_of_lt ((uniformIntegral_le_one x y).trans_lt ENNReal.one_lt_top))
    (skorohodDistanceExtended_le_uniform x y)

/-- Taking real values preserves the uniform integral cutoff estimate. -/
theorem uniformIntegral_toReal_le (x y : D E) (M : Time) :
    (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-u)) *
      ⨆ t ≤ u.toNNReal, q (x.1 t) (y.1 t)).toReal ≤
      (⨆ t ≤ M, q (x.1 t) (y.1 t)).toReal + Real.exp (-(M : ℝ)) := by
  have hS : (⨆ t ≤ M, q (x.1 t) (y.1 t)) ≠ ∞ :=
    ne_of_lt ((iSup_le fun t => iSup_le fun _ =>
      min_le_right (edist (x.1 t) (y.1 t)) 1).trans_lt ENNReal.one_lt_top)
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hS, ENNReal.ofReal_ne_top⟩) (uniformIntegral_le x y M)
  rw [ENNReal.toReal_add hS ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
  exact h

/-- Uniform control on an initial interval bounds the metric, with an exponential tail. -/
theorem dist_le_uniform (x y : D E) (M : Time) :
    dist x y ≤ (⨆ t ≤ M, q (x.1 t) (y.1 t)).toReal + Real.exp (-(M : ℝ)) := by
  exact (dist_le_uniformIntegral x y).trans (uniformIntegral_toReal_le x y M)

/-- Continuous paths embed continuously from the compact-open topology. -/
theorem continuous_ofContinuous : Continuous (D.ofContinuous (E := E)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hhalf))
  let M : Time := ⟨max R 0, le_max_right _ _⟩
  have htail : Real.exp (-(M : ℝ)) < ε / 2 := hR _ (le_max_left _ _)
  have hunif := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
    (tendsto_id : Tendsto (fun y : C(Time, E) => y) (𝓝 x) (𝓝 x))
    (Icc 0 M) isCompact_Icc
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif (ε / 2) hhalf] with y hy
  have hs : (⨆ t ≤ M, q ((D.ofContinuous y).1 t) ((D.ofContinuous x).1 t)) ≤
      ENNReal.ofReal (ε / 2) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    apply (min_le_left _ _).trans
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (by
      rw [dist_comm]
      exact (hy t ⟨bot_le, ht⟩).le)
  have hb := dist_le_uniform (D.ofContinuous y) (D.ofContinuous x) M
  have hsreal := ENNReal.toReal_le_of_le_ofReal hhalf.le hs
  exact hb.trans_lt (by linarith)

/-- Constant paths retain exactly the state metric truncated at one. -/
theorem dist_const_pair (a b : E) : dist (const a) (const b) = min (dist a b) 1 := by
  change (skorohodDistanceExtended (const a) (const b)).toReal = _
  rw [skorohodDistanceExtended_const_pair, q,
    ENNReal.toReal_min (edist_ne_top _ _) ENNReal.one_ne_top, edist_dist]
  simp only [ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_one]

end

end LatticeProb.Cadlag.HalfLine
