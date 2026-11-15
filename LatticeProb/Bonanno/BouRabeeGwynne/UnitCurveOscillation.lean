/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.UnitCurveOscillation at commit fdb5cad; local imports and deprecated lemma name adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.UnitCurveExit
import Mathlib.Topology.Order.IntermediateValue

/-! A measurable oscillation event of the actual finite pasted curve, between
its two first-exit parameters. -/

open MeasureTheory Set
open scoped unitInterval

namespace BouRabeeGwynne

noncomputable def unitIntervalAffine (a b : unitInterval) : C(unitInterval, unitInterval) :=
  ⟨fun u ↦ ⟨(1 - (u : ℝ)) * a + (u : ℝ) * b, by
      constructor
      · exact add_nonneg
          (mul_nonneg (sub_nonneg.mpr u.property.2) a.property.1)
          (mul_nonneg u.property.1 b.property.1)
      · have h₁ := mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr u.property.2)
        have h₂ := mul_le_mul_of_nonneg_left b.property.2 u.property.1
        nlinarith⟩, by fun_prop⟩

@[simp] lemma unitIntervalAffine_zero (a b : unitInterval) : unitIntervalAffine a b 0 = a := by
  apply Subtype.ext
  simp [unitIntervalAffine]

@[simp] lemma unitIntervalAffine_one (a b : unitInterval) : unitIntervalAffine a b 1 = b := by
  apply Subtype.ext
  simp [unitIntervalAffine]

lemma unitIntervalAffine_mem_Icc (a b : unitInterval) (hab : a ≤ b) (u : unitInterval) :
    unitIntervalAffine a b u ∈ Icc a b := by
  change (a : ℝ) ≤ (1 - (u : ℝ)) * a + (u : ℝ) * b ∧
    (1 - (u : ℝ)) * a + (u : ℝ) * b ≤ b
  have hd : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr hab
  have h₁ := mul_nonneg u.property.1 hd
  have h₂ := mul_nonneg (sub_nonneg.mpr u.property.2) hd
  constructor <;> nlinarith

lemma unitIntervalAffine_surjOn (a b : unitInterval) :
    Icc a b ⊆ range (unitIntervalAffine a b) := by
  simpa only [unitIntervalAffine_zero, unitIntervalAffine_one] using
    intermediate_value_univ (0 : unitInterval) (1 : unitInterval)
      (unitIntervalAffine a b).continuous

noncomputable def unitCurveInterval {d : ℕ} (f : C(unitInterval, Euc d))
    (a b : unitInterval) : C(unitInterval, Euc d) := f.comp (unitIntervalAffine a b)

lemma measurable_unitCurveInterval {d : ℕ} :
    Measurable (fun p : C(unitInterval, Euc d) × unitInterval × unitInterval ↦
      unitCurveInterval p.1 p.2.1 p.2.2) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro u
  have ht : Measurable (fun p : C(unitInterval, Euc d) × unitInterval × unitInterval ↦
      unitIntervalAffine p.2.1 p.2.2 u) := by
    apply Measurable.subtype_mk
    change Measurable (fun p : C(unitInterval, Euc d) × unitInterval × unitInterval ↦
      (1 - (u : ℝ)) * (p.2.1 : ℝ) + (u : ℝ) * (p.2.2 : ℝ))
    fun_prop
  have heval : Measurable (fun p : C(unitInterval, Euc d) × unitInterval ↦ p.1 p.2) :=
    (by fun_prop : Continuous (fun p : C(unitInterval, Euc d) × unitInterval ↦ p.1 p.2)).measurable
  exact heval.comp (measurable_fst.prodMk ht)

def unitCurveDiameterBound {d : ℕ} (η : ℝ) : Set (C(unitInterval, Euc d)) :=
  {f | ∀ s t : unitInterval, dist (f s) (f t) ≤ η}

lemma isClosed_unitCurveDiameterBound {d : ℕ} (η : ℝ) :
    IsClosed (unitCurveDiameterBound (d := d) η) := by
  unfold unitCurveDiameterBound
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro t
  exact isClosed_le ((continuous_eval_const s).dist (continuous_eval_const t)) continuous_const

def unitCurveExitOscillationBad {d : ℕ} (U V : Set (Euc d)) (η : ℝ) :
    Set (C(unitInterval, Euc d)) :=
  {f | unitCurveInterval f (unitCurveExitTime U f) (unitCurveExitTime V f) ∉
    unitCurveDiameterBound η}

lemma measurableSet_unitCurveExitOscillationBad {d : ℕ} {U V : Set (Euc d)}
    (hU : IsOpen U) (hV : IsOpen V) (η : ℝ) :
    MeasurableSet (unitCurveExitOscillationBad U V η) := by
  have hm : Measurable (fun f : C(unitInterval, Euc d) ↦
      unitCurveInterval f (unitCurveExitTime U f) (unitCurveExitTime V f)) :=
    measurable_unitCurveInterval.comp (measurable_id.prodMk
      ((measurable_unitCurveExitTime hU).prodMk (measurable_unitCurveExitTime hV)))
  exact (isClosed_unitCurveDiameterBound η).measurableSet.compl.preimage hm

theorem unitCurve_oscillation_le_of_not_bad {d : ℕ} {U V : Set (Euc d)} {η : ℝ}
    {f : C(unitInterval, Euc d)} (hf : f ∉ unitCurveExitOscillationBad U V η)
    {s t : unitInterval}
    (hs : s ∈ Icc (unitCurveExitTime U f) (unitCurveExitTime V f))
    (ht : t ∈ Icc (unitCurveExitTime U f) (unitCurveExitTime V f)) : dist (f s) (f t) ≤ η := by
  have hgood : unitCurveInterval f (unitCurveExitTime U f) (unitCurveExitTime V f) ∈
      unitCurveDiameterBound η := not_not.mp hf
  obtain ⟨a, ha⟩ := unitIntervalAffine_surjOn _ _ hs
  obtain ⟨b, hb⟩ := unitIntervalAffine_surjOn _ _ ht
  simpa only [unitCurveInterval, ContinuousMap.comp_apply, ha, hb] using hgood a b

end BouRabeeGwynne
