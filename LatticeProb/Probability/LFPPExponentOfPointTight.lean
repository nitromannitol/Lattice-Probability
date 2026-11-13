import LatticeProb.Probability.HeatCircleExponentCompare
import LatticeProb.Probability.LFPPDistanceCrossLen
import LatticeProb.Probability.TightRatioExponent
import LatticeProb.Bonanno.NV1Evidence
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsTwoSidedTight
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPNormalizer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPExponent

/-!
# The LFPP crossing exponent from point-to-point tightness

Let `ξ > 0` and let `Q` be the LFPP distance exponent of Ding and Gwynne, defined through medians
of the left-right crossing length of `[0,1]²` for the heat-kernel mollified normalized whole-plane
GFF (`SupercriticalLQGUniqueness.IsLFPPExponent`). Assume the point-to-point tightness of
Ding-Gwynne (Section 4 of *Tightness of supercritical Liouville first passage percolation*): for
the LFPP normalizers `𝔞_ε`, the rescaled crossing lengths `𝔞_ε⁻¹ D_ε(z, w; U)` of every connected
open set `U` between two distinct points `z, w ∈ U` are tight together with their reciprocals,
uniformly in `ε ∈ (0, 1)`.

Then `Q = Q(ξ) = distExp 2 ξ`: the point-to-point LFPP distance between `0` and `1` in
`(-2, 2)²` has exponent `1 - ξ Q` in probability by tightness and the median bounds, and exponent
`1 - ξ Q(ξ)` by the comparison of the heat-kernel and circle-average mollifications; limits in
probability are unique.

## Main results

* `LQGMetric.HeatCircle.eq_distExp_of_isLFPPExponent_of_pointTight`: `Q = distExp 2 ξ`.
* `LQGMetric.HeatCircle.isLFPPExponent_distExp_of_pointTight`: the LFPP distance exponent of `ξ`
  is `distExp 2 ξ`, for every `ξ > 0`.

The tightness input is an explicit hypothesis, stated exactly as the conclusion of the
point-to-point tightness theorem of Ding-Gwynne (Section 4).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.HeatCircle

open LQGMetric.DDDF (crossLenIn)

/-- The open square `(-2, 2)²` is convex. -/
theorem convex_U : Convex ℝ LQGDimension.U := by
  have hU : LQGDimension.U = Complex.re ⁻¹' Ioo (-2) 2 ∩ Complex.im ⁻¹' Ioo (-2) 2 := by
    ext z
    simp only [LQGDimension.U, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, abs_lt]
  rw [hU]
  exact ((convex_Ioo _ _).linear_preimage Complex.reLm).inter
    ((convex_Ioo _ _).linear_preimage Complex.imLm)

/-- The open square `(-2, 2)²` is open. -/
theorem isOpen_U : IsOpen LQGDimension.U := by
  have hU : LQGDimension.U = Complex.re ⁻¹' Ioo (-2) 2 ∩ Complex.im ⁻¹' Ioo (-2) 2 := by
    ext z
    simp only [LQGDimension.U, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, abs_lt]
  rw [hU]
  exact (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

theorem zero_mem_U : (0 : ℂ) ∈ LQGDimension.U := by
  simp only [LQGDimension.U, mem_ofPred_eq, Complex.zero_re, Complex.zero_im, abs_zero]
  norm_num

theorem one_mem_U : (1 : ℂ) ∈ LQGDimension.U := by
  simp only [LQGDimension.U, mem_ofPred_eq, Complex.one_re, Complex.one_im, abs_zero, abs_one]
  norm_num

/-- **The LFPP distance exponent from point-to-point tightness.** If `Q` is the LFPP distance
exponent of `ξ > 0` (medians of left-right crossing lengths of `[0,1]²`) and the rescaled
point-to-point crossing lengths `𝔞_ε⁻¹ D_ε(z, w; U)` are two-sided tight uniformly in
`ε ∈ (0, 1)` (Ding-Gwynne, Section 4), then `Q = Q(ξ) = distExp 2 ξ`. -/
theorem eq_distExp_of_isLFPPExponent_of_pointTight
    (hR1 : ∀ ξ : Ioi (0 : ℝ), ∀ Q : ℝ, SupercriticalLQGUniqueness.IsLFPPExponent ξ Q →
      ∀ m : Ioi (0 : ℝ) → Ioi (0 : ℝ),
        (∀ ε, SupercriticalLQGUniqueness.IsLFPPNormalizer ξ ε (m ε)) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
          SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P →
          ∀ X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
            (∀ ε, SupercriticalLQGUniqueness.IsHeatSmoothing P h ε (X ε)) →
            ∀ U : TopologicalSpace.Opens ℂ, IsConnected (U : Set ℂ) →
              ∀ z w : ℂ, z ∈ U → w ∈ U → z ≠ w →
                SupercriticalLQGUniqueness.IsTwoSidedTight P (fun (ε : Ioo (0 : ℝ) 1) ω =>
                  ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
                    crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
                      U {z} {w}))
    (ξ : Ioi (0 : ℝ)) {Q : ℝ} (hQ : SupercriticalLQGUniqueness.IsLFPPExponent ξ Q) :
    Q = HigherDimLQGMetric.distExp 2 ξ := by
  have hξ : 0 < (ξ : ℝ) := Set.mem_Ioi.mp ξ.2
  -- a realization: normalized whole-plane GFF, heat-kernel versions, LFPP normalizers
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := SupercriticalLQGUniqueness.exists_normalizedGFF
  have hXex : ∀ ε : ℝ, ∃ Y : Ω → C(ℂ, ℝ), ∀ hε : 0 < ε, ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (SupercriticalLQGUniqueness.positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n)) atTop
        (𝓝 (Y ω z)) := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨Y, -, hY⟩ := SupercriticalLQGUniqueness.exists_heatVersion hh ε hε
      exact ⟨Y, fun _ => hY⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hε⟩
  choose X hX using hXex
  have hmex : ∀ ε : Ioi (0 : ℝ), ∃ a : Ioi (0 : ℝ),
      SupercriticalLQGUniqueness.IsLFPPNormalizer ξ ε a :=
    fun ε => (SupercriticalLQGUniqueness.existsUnique_isLFPPNormalizer ξ ε).exists
  choose m hm using hmex
  have hmrex : ∀ ε : ℝ, ∃ a : ℝ, 0 < a ∧ ∀ hε : 0 < ε, a = (m ⟨ε, hε⟩ : ℝ) := by
    intro ε
    by_cases hε : 0 < ε
    · exact ⟨m ⟨ε, hε⟩, (m ⟨ε, hε⟩).2, fun _ => rfl⟩
    · exact ⟨1, one_pos, fun h' => absurd h' hε⟩
  choose mr hmr_pos hmr using hmrex
  -- the median bounds of the crossing exponent
  have hmed := hQ P h hh X (fun ε => ENNReal.ofReal (mr ε)) (fun ε hε => by
    refine ⟨hX ε hε, ?_⟩
    have hmed := hm ⟨ε, hε⟩ P h hh (X ε) (hX ε hε)
    rw [← hmr ε hε] at hmed
    exact hmed)
  have hbounds : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ε ^ (1 - (ξ : ℝ) * Q + δ) ≤ mr ε ∧ mr ε ≤ ε ^ (1 - (ξ : ℝ) * Q - δ) := by
    intro δ hδ
    filter_upwards [hmed δ hδ, self_mem_nhdsWithin] with ε hε hε0
    exact ⟨(ENNReal.ofReal_le_ofReal_iff (hmr_pos ε).le).1 hε.1,
      (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg (le_of_lt hε0) _)).1 hε.2⟩
  have hmexp := LatticeProb.Probability.tendsto_log_div_log_of_rpow_bounds hbounds
  -- the point-to-point tightness in the square `(-2, 2)²` between `0` and `1`
  let Uo : TopologicalSpace.Opens ℂ := ⟨LQGDimension.U, isOpen_U⟩
  have hT := hR1 ξ Q hQ m hm P h hh (fun ε => X ε) (fun ε => hX ε ε.2) Uo
    (convex_U.isConnected ⟨0, zero_mem_U⟩) 0 1 zero_mem_U one_mem_U zero_ne_one
  have hA := LatticeProb.Probability.tendstoInMeasure_log_div_of_ennreal_tails (P := P)
    (L := fun ε ω => crossLenIn ξ (X ε ω) LQGDimension.U {0} {1})
    (fun ε _ _ => hmr_pos ε) hmexp (by
      intro η hη
      obtain ⟨M, hM, hMb⟩ := hT.2 η hη
      refine ⟨M, hM, fun ε hε0 hε1 => ?_⟩
      rw [hmr ε hε0]
      exact hMb ⟨ε, hε0, hε1⟩)
  have hfun : (fun ε ω => Real.log (crossLenIn ξ (X ε ω) LQGDimension.U {0} {1}).toReal /
      Real.log ε) = fun ε ω => Real.log (LQGDimension.lfppDistance ξ (X ε ω)) / Real.log ε := by
    funext ε ω
    rw [toReal_crossLenIn_eq_lfppDistance (X ε ω).continuous]
  rw [hfun] at hA
  have hB := tendstoInMeasure_log_lfppDistance_heat_distExp hh X hX hξ
  obtain ⟨_, hω⟩ := (tendstoInMeasure_ae_unique hA hB).exists
  have hlin : (ξ : ℝ) * Q = ξ * HigherDimLQGMetric.distExp 2 ξ := by
    have hω' : 1 - (ξ : ℝ) * Q = 1 - ξ * HigherDimLQGMetric.distExp 2 ξ := hω
    linarith
  exact mul_left_cancel₀ hξ.ne' hlin

/-- **The LFPP distance exponent is `Q(ξ)`.** Under the point-to-point tightness of Ding-Gwynne
(Section 4), for every `ξ > 0` the LFPP distance exponent (medians of left-right crossing
lengths of `[0,1]²`) is `Q(ξ) = distExp 2 ξ`. -/
theorem isLFPPExponent_distExp_of_pointTight
    (hR1 : ∀ ξ : Ioi (0 : ℝ), ∀ Q : ℝ, SupercriticalLQGUniqueness.IsLFPPExponent ξ Q →
      ∀ m : Ioi (0 : ℝ) → Ioi (0 : ℝ),
        (∀ ε, SupercriticalLQGUniqueness.IsLFPPNormalizer ξ ε (m ε)) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
          SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P →
          ∀ X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
            (∀ ε, SupercriticalLQGUniqueness.IsHeatSmoothing P h ε (X ε)) →
            ∀ U : TopologicalSpace.Opens ℂ, IsConnected (U : Set ℂ) →
              ∀ z w : ℂ, z ∈ U → w ∈ U → z ≠ w →
                SupercriticalLQGUniqueness.IsTwoSidedTight P (fun (ε : Ioo (0 : ℝ) 1) ω =>
                  ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
                    crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
                      U {z} {w})) :
    ∀ ξ : Ioi (0 : ℝ),
      SupercriticalLQGUniqueness.IsLFPPExponent ξ (HigherDimLQGMetric.distExp 2 ξ) := by
  intro ξ
  obtain ⟨Q, hQ, -⟩ := SupercriticalLQGUniqueness.existsUnique_isLFPPExponent ξ
  rw [← eq_distExp_of_isLFPPExponent_of_pointTight hR1 ξ hQ]
  exact hQ

end LQGMetric.HeatCircle
