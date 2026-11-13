import LatticeProb.Probability.LFPPExponentOfPointTight
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import LatticeProb.Analysis.RpowComparableExponent

/-!
# The exponent of a weak LQG metric is the LFPP distance exponent

Let `ξ > 0`. A weak LQG metric with parameter `ξ` and exponent `Q` (Ding-Dubédat-Dunlap-Falconet;
`SupercriticalLQGUniqueness.IsWeakLQGMetric`) satisfies Pfeffer's weak metric axioms with the power
scale `c_r = r ^ (ξ Q)`. Pfeffer's comparison of scales (*Weak Liouville quantum gravity metrics
with matter central charge c ∈ (-∞, 25)*, Theorem 1.9, `SupercriticalLQGUniqueness.B2.Iface.PLThm19`),
applied with the LFPP distance exponent `Q(ξ) = distExp 2 ξ`, makes `r ^ (ξ Q)` comparable with
`r ^ (ξ Q(ξ))`, hence `Q = Q(ξ)`.

The identification `Q(ξ) = distExp 2 ξ` of the LFPP distance exponent rests on the point-to-point
tightness of Ding-Gwynne (Section 4), an explicit hypothesis here as in
`LQGMetric.HeatCircle.isLFPPExponent_distExp_of_pointTight`.

## Main results

* `LQGMetric.HeatCircle.isPfeWeakMetric_rpowScale_of_isWeakLQGMetric`: a weak LQG metric with
  exponent `Q` satisfies Pfeffer's weak metric axioms with scale `r ^ (ξ Q)`.
* `LQGMetric.HeatCircle.distExp_eq_of_isWeakLQGMetric_of_pointTight`: every weak LQG metric with
  parameter `ξ` has exponent `distExp 2 ξ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.HeatCircle

open LQGMetric.DDDF (crossLenIn)

/-- The power scale `r ↦ r ^ (ξ Q)`. -/
noncomputable def rpowScale (ξ : Ioi (0 : ℝ)) (Q : ℝ) : Ioi (0 : ℝ) → Ioi (0 : ℝ) :=
  fun r => ⟨(r : ℝ) ^ ((ξ : ℝ) * Q), Real.rpow_pos_of_pos r.property _⟩

/-- The power scale is multiplicative in the radius. -/
theorem rpowScale_ratio (ξ : Ioi (0 : ℝ)) (Q : ℝ) (δ : Ioo (0 : ℝ) 1) (r : Ioi (0 : ℝ)) :
    ((rpowScale ξ Q ⟨(δ : ℝ) * (r : ℝ), mul_pos δ.property.1 r.property⟩ : Ioi (0 : ℝ)) : ℝ) /
        (rpowScale ξ Q r : ℝ) = (δ : ℝ) ^ ((ξ : ℝ) * Q) := by
  simp only [rpowScale]
  rw [Real.mul_rpow δ.property.1.le r.property.le]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Real.rpow_pos_of_pos r.property _))

/-- **A weak LQG metric satisfies Pfeffer's weak metric axioms with the power scale.** If `D` is a
weak LQG metric with parameter `ξ` and exponent `Q`, then `D` satisfies Pfeffer's axioms with
`c_r = r ^ (ξ Q)`. (The argument is the one given for strong LQG metrics in Bonanno's
lean-formalizations, `SupercriticalLFPPAS.Compare.ScaleRatio`; it uses only the weak axioms.) -/
theorem isPfeWeakMetric_rpowScale_of_isWeakLQGMetric {ξ : Ioi (0 : ℝ)} {Q : ℝ}
    {D : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric}
    (hW : SupercriticalLQGUniqueness.IsWeakLQGMetric ξ Q D) :
    SupercriticalLQGUniqueness.B2.Iface.IsPfeWeakMetric ξ D (rpowScale ξ Q) := by
  rcases hW with ⟨hMeas, hLength, hInternal, hWeyl, hTranslate, hTight⟩
  refine ⟨hMeas, hLength, hInternal, hWeyl, hTranslate, ?_, ?_⟩
  · let Λ : ℝ := |(ξ : ℝ) * Q| + 2
    have hΛ : 1 < Λ := by
      have habs : 0 ≤ |(ξ : ℝ) * Q| := abs_nonneg _
      simp only [Λ]
      linarith
    refine ⟨Λ, hΛ, ?_⟩
    intro δ r hr
    let rI : Ioi (0 : ℝ) := ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩
    have hratio := rpowScale_ratio ξ Q δ rI
    have hδpos : 0 < (δ : ℝ) := δ.property.1
    have hδle : (δ : ℝ) ≤ 1 := le_of_lt δ.property.2
    have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ
    have hΛlower : Λ⁻¹ ≤ 1 := (inv_le_one₀ hΛpos).2 (le_of_lt hΛ)
    have hΛexp : |(ξ : ℝ) * Q| ≤ Λ := by
      simp only [Λ]
      linarith
    have hnegexp : -Λ ≤ -|(ξ : ℝ) * Q| := neg_le_neg hΛexp
    rw [hratio]
    constructor
    · calc
        Λ⁻¹ * (δ : ℝ) ^ Λ ≤ 1 * (δ : ℝ) ^ Λ :=
          mul_le_mul_of_nonneg_right hΛlower (Real.rpow_nonneg hδpos.le _)
        _ = (δ : ℝ) ^ Λ := one_mul _
        _ ≤ (δ : ℝ) ^ |(ξ : ℝ) * Q| :=
          Real.rpow_le_rpow_of_exponent_ge hδpos hδle hΛexp
        _ ≤ (δ : ℝ) ^ ((ξ : ℝ) * Q) :=
          Real.rpow_le_rpow_of_exponent_ge hδpos hδle (le_abs_self _)
    · calc
        (δ : ℝ) ^ ((ξ : ℝ) * Q) ≤ (δ : ℝ) ^ (-|(ξ : ℝ) * Q|) :=
          Real.rpow_le_rpow_of_exponent_ge hδpos hδle (neg_abs_le _)
        _ ≤ (δ : ℝ) ^ (-Λ) :=
          Real.rpow_le_rpow_of_exponent_ge hδpos hδle hnegexp
        _ ≤ Λ * (δ : ℝ) ^ (-Λ) := by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right (le_of_lt hΛ) (Real.rpow_nonneg hδpos.le _))
  · intro Ω _ P _ h hh a ha A
    have hpow (r : Ioi (0 : ℝ)) :
        ((rpowScale ξ Q r : Ioi (0 : ℝ)) : ℝ)⁻¹ = (r : ℝ) ^ (-((ξ : ℝ) * Q)) := by
      simp only [rpowScale]
      rw [← Real.rpow_neg r.property.le]
    simpa only [hpow] using hTight P h hh a ha A

/-- **The exponent of a weak LQG metric is `Q(ξ)`.** Assume Pfeffer's comparison of scales
(Theorem 1.9 of *Weak LQG metrics with matter central charge c ∈ (-∞, 25)*) and the
point-to-point tightness of Ding-Gwynne (Section 4). Then every weak LQG metric with parameter
`ξ > 0` and exponent `Q` has `Q = Q(ξ) = distExp 2 ξ`. -/
theorem distExp_eq_of_isWeakLQGMetric_of_pointTight
    (hPL : SupercriticalLQGUniqueness.B2.Iface.PLThm19)
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
    ∀ (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → SupercriticalLQGUniqueness.LSCMetric),
      SupercriticalLQGUniqueness.IsWeakLQGMetric ξ Q D → HigherDimLQGMetric.distExp 2 ξ = Q := by
  intro ξ Q D hD
  have hξ : 0 < (ξ : ℝ) := Set.mem_Ioi.mp ξ.2
  obtain ⟨⟨C, hC, hb⟩, -⟩ := hPL ξ _ (isLFPPExponent_distExp_of_pointTight hR1 ξ) D
    (rpowScale ξ Q) (isPfeWeakMetric_rpowScale_of_isWeakLQGMetric hD)
  have hab := LatticeProb.Analysis.eq_of_rpow_le_mul_rpow
    (a := (ξ : ℝ) * HigherDimLQGMetric.distExp 2 ξ) (b := (ξ : ℝ) * Q) hC
    (fun r hr => hb ⟨r, hr⟩)
  exact mul_left_cancel₀ hξ.ne' hab

end LQGMetric.HeatCircle
