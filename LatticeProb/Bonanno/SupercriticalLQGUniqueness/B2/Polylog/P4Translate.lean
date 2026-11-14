/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P4Translate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Event
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Transport

 














set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP
open Uniqueness.Toolkit.CompactPathInfimum (compactPathInf)

 
lemma acrossIn_translate_mul {m M : LSCMetric} {k : ℝ≥0∞} (hk0 : k ≠ 0) (hkt : k ≠ ∞) (z : ℂ)
    (hm : ∀ x y, m (x, y) = k * M (x + z, y + z)) (r₁ r₂ : ℝ) :
    acrossIn m 0 r₁ r₂ = k * acrossIn M z r₁ r₂ := by
  unfold acrossIn
  rw [compactPathInf_comp_mul hk0 hkt (Homeomorph.addRight z) hm]
  have himg : ∀ S : Set ℂ, (Homeomorph.addRight z) '' S = (fun x => x + z) '' S := fun _ => rfl
  rw [himg, himg, himg, image_add_closedAnn, image_add_sphere, image_add_sphere, zero_add]

 
lemma aroundDist_translate_mul {m M : LSCMetric} {k : ℝ≥0∞} (hk0 : k ≠ 0) (hkt : k ≠ ∞)
    (z : ℂ) (hm : ∀ x y, m (x, y) = k * M (x + z, y + z)) (r : Set.Ioi (0 : ℝ)) :
    aroundDist m (annAround 0 r) = k * aroundDist M (annAround z r) := by
  obtain ⟨h1, h2, h3⟩ := image_translate_annAt z 0 (2 * r) (3 * r) (two_r_pos r)
    (two_r_lt_three_r r)
  rw [zero_add] at h1 h2 h3
  exact aroundDist_comp_mul hk0 hkt (Homeomorph.addRight z) hm _ _ h1 h2 h3

lemma normD_eq_of_circleAvg {ξ : ℝ} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {g g' : DistC}
    {z : ℂ} {r : Set.Ioi (0 : ℝ)} {c₁ : ℝ}
    (hca : circleAvg g' r 0 = circleAvg g r z - c₁) :
    normD ξ c g' 0 r = normD ξ c g z r * ENNReal.ofReal (Real.exp (ξ * c₁)) := by
  unfold normD
  rw [hca, ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 (c r).2.le) (Real.exp_pos _).le),
    mul_assoc, ← Real.exp_add]
  congr 3; ring

lemma normL_eq_of_circleAvg {ξ : ℝ} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {ε : Set.Ioi (0 : ℝ)}
    {g g' : DistC} {z : ℂ} {r : Set.Ioi (0 : ℝ)} {c₁ : ℝ}
    (hca : circleAvg g' r 0 = circleAvg g r z - c₁) :
    normL ξ m ε g' 0 r = normL ξ m ε g z r * ENNReal.ofReal (Real.exp (ξ * c₁)) := by
  unfold normL
  rw [hca, ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 (lfppScaleFactor_pos m ε r).le)
    (Real.exp_pos _).le), mul_assoc, ← Real.exp_add]
  congr 3; ring

lemma exp_mul_cancel (ξ c₁ : ℝ) :
    ENNReal.ofReal (Real.exp (ξ * c₁)) * ENNReal.ofReal (Real.exp (ξ * -c₁)) = 1 := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, show ξ * c₁ + ξ * -c₁ = 0 by ring,
    Real.exp_zero, ENNReal.ofReal_one]

 
theorem ae_mem_plEventLoc_recenter_iff {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : ℝ) (z : ℂ)
    (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (C : ℝ) :
    ∀ᵐ ω ∂P, (recenter z (h ω) ∈ plEventLoc ξ D c m q 0 ε hε r C ↔
      h ω ∈ plEventLoc ξ D c m q z ε hε r C) := by
  have htrans : IsWholePlaneGFF (fun ω => translateDist z (h ω)) P := by
    simpa only [translateDist_eq_affineComp_one] using hh.1.affineComp one_pos z
  have hW := ae_addConst_eq_mul_of_pfe P (fun ω => translateDist z (h ω))
    (GM.Tight.isGFFPlusCont_of_wp htrans) hD (fun ω => -circleAvg (h ω) 1 z)
  have hT := hD.2.2.2.2.1 P h (GM.Tight.isGFFPlusCont_of_wp hh.1) z
  have hC := ae_circleAvg_normalized_translate hh z r
  filter_upwards [hW, hT, hC] with ω hw ht hc
  set c₁ := circleAvg (h ω) 1 z
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * -c₁))
  have hk0 : k ≠ 0 := by simpa [k] using Real.exp_pos _
  have hkt : k ≠ ∞ := ENNReal.ofReal_ne_top
  have hmD : ∀ x y, D (recenter z (h ω)) (x, y) = k * D (h ω) (x + z, y + z) := fun x y => by
    rw [show recenter z (h ω) = addConst (translateDist z (h ω)) (-c₁) from rfl, hw (x, y), ht x y]
  have hmL : ∀ x y, plLocMetric (ξ : ℝ) q m ε hε (recenter z (h ω)) (x, y) =
      k * plLocMetric (ξ : ℝ) q m ε hε (h ω) (x + z, y + z) :=
    fun x y => plLocMetric_recenter (ξ : ℝ) q m ε hε (h ω) z x y
  have hca : circleAvg (recenter z (h ω)) r 0 = circleAvg (h ω) r z - c₁ := hc
  have hnD := normD_eq_of_circleAvg (ξ := (ξ : ℝ)) (c := c) hca
  have hnL := normL_eq_of_circleAvg (ξ := (ξ : ℝ)) (m := m) (ε := ⟨ε, hε.1⟩) hca
  have hcancel := exp_mul_cancel (ξ : ℝ) c₁
  have key : ∀ (n n' X : ℝ≥0∞), n' = n * ENNReal.ofReal (Real.exp ((ξ : ℝ) * c₁)) →
      n' * (k * X) = n * X := fun n n' X hn => by
    rw [hn, mul_assoc, ← mul_assoc _ k, hcancel, one_mul]
  simp only [plEventLoc, mem_ofPred_eq]
  rw [acrossIn_translate_mul hk0 hkt z hmD, aroundDist_translate_mul hk0 hkt z hmD,
    acrossIn_translate_mul hk0 hkt z hmL, aroundDist_translate_mul hk0 hkt z hmL,
    key _ _ _ hnD, key _ _ _ hnD, key _ _ _ hnL, key _ _ _ hnL]

 
theorem prob_plEventLoc_eq_zero {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : ℝ) (z : ℂ)
    (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (C : ℝ) :
    P {ω | h ω ∈ plEventLoc ξ D c m q z ε hε r C} =
      P {ω | h ω ∈ plEventLoc ξ D c m q 0 ε hε r C} := by
  have hmeas := measurableSet_plEventLoc (ξ : ℝ) hD.1 c m q 0 ε hε r C
  have hlaw := map_normalized_translate_sub_circleAvg hh z
  have hrec : Measurable fun ω => recenter z (h ω) :=
    (normalized_translate_sub_circleAvg hh z).1.measurable
  calc P {ω | h ω ∈ plEventLoc ξ D c m q z ε hε r C}
      = P {ω | recenter z (h ω) ∈ plEventLoc ξ D c m q 0 ε hε r C} :=
        measure_congr ((ae_mem_plEventLoc_recenter_iff P h hh hD m q z ε hε r C).mono
          fun ω hω => propext hω.symm)
    _ = (P.map fun ω => recenter z (h ω)) (plEventLoc ξ D c m q 0 ε hε r C) :=
        (Measure.map_apply hrec hmeas).symm
    _ = (P.map h) (plEventLoc ξ D c m q 0 ε hε r C) := by
        rw [show (fun ω => recenter z (h ω)) =
          fun ω => addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z) from rfl, hlaw]
    _ = P {ω | h ω ∈ plEventLoc ξ D c m q 0 ε hε r C} :=
        Measure.map_apply hh.1.measurable hmeas

end SupercriticalLQGUniqueness.B2.Polylog
