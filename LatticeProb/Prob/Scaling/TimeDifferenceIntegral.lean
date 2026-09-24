/- Integral bounds for forward differences of continuous monotone functions.

Moved from Parking-Sharpness.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory Set Filter Topology

noncomputable section
namespace LatticeProb.Scaling.TimeDifference

/-- The integral of a time difference telescopes to two short end intervals. -/
theorem integral_difference {f : ℝ → ℝ} (hf : Continuous f) (a b h : ℝ) :
    (∫ s in a..b, (f (s + h) - f s) / h) =
      ((∫ s in b..b + h, f s) - ∫ s in a..a + h, f s) / h := by
  have hshift : Continuous (fun s => f (s + h)) := hf.comp (continuous_id.add_const h)
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (hshift.intervalIntegrable _ _) (hf.intervalIntegrable _ _),
    intervalIntegral.integral_comp_add_right]
  congr 1
  exact intervalIntegral.integral_interval_sub_interval_comm'
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- Monotonicity bounds the integral independently of the positive step size. -/
theorem integral_difference_le {f : ℝ → ℝ} (hf : Continuous f) (hm : Monotone f)
    (a b : ℝ) {h H : ℝ} (hh : 0 < h) (hH : h ≤ H) :
    (∫ s in a..b, (f (s + h) - f s) / h) ≤ f (b + H) - f a := by
  rw [integral_difference hf]
  apply (div_le_iff₀ hh).mpr
  have hb : (∫ s in b..b + h, f s) ≤ h * f (b + H) := by
    calc
      _ ≤ ∫ _ in b..b + h, f (b + H) :=
        intervalIntegral.integral_mono_on (by linarith) (hf.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) (fun s hs => hm (by linarith [hs.2]))
      _ = _ := by simp
  have ha : h * f a ≤ ∫ s in a..a + h, f s := by
    calc
      _ = ∫ _ in a..a + h, f a := by simp
      _ ≤ _ := intervalIntegral.integral_mono_on (by linarith)
        (continuous_const.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
        (fun s hs => hm hs.1)
  nlinarith

/-- On every compact space-time set, monotone continuous fields have uniformly
bounded local `L¹` norms of their forward quotients with steps in `(0,1]`. -/
theorem exists_integral_norm_difference_bound {d : ℕ}
    {u : ℝ × (Fin d → ℝ) → ℝ} (hu : Continuous u)
    (hm : ∀ x, Monotone fun s => u (s, x))
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 →
      IntegrableOn (fun p => (u (p.1 + h, p.2) - u p) / h) K ∧
      (∫ p in K, ‖(u (p.1 + h, p.2) - u p) / h‖) ≤ C := by
  obtain ⟨M, hM, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let J := Prod.snd '' K
  have hJ : IsCompact J := hK.image continuous_snd
  let B : Set (ℝ × (Fin d → ℝ)) := Icc (-M) M ×ˢ J
  have hB : IsCompact B := isCompact_Icc.prod hJ
  have hKB : K ⊆ B := by
    intro p hp
    have ht : ‖p.1‖ ≤ M := (norm_fst_le p).trans (hbound p hp)
    exact ⟨abs_le.mp ht, ⟨p, hp, rfl⟩⟩
  refine ⟨∫ x in J, u (M + 1, x) - u (-M, x), ?_⟩
  intro h hh hh1
  let D : ℝ × (Fin d → ℝ) → ℝ := fun p => (u (p.1 + h, p.2) - u p) / h
  have hDc : Continuous D :=
    ((hu.comp ((continuous_fst.add_const h).prodMk continuous_snd)).sub hu).div_const h
  have hDi : IntegrableOn D B := hDc.continuousOn.integrableOn_compact hB
  have hDn : ∀ p, 0 ≤ D p := fun p =>
    div_nonneg (sub_nonneg.mpr (hm p.2 (by linarith))) hh.le
  refine ⟨hDc.continuousOn.integrableOn_compact hK, ?_⟩
  change (∫ p in K, ‖D p‖) ≤ _
  simp_rw [Real.norm_of_nonneg (hDn _)]
  calc
    (∫ p in K, D p) ≤ ∫ p in B, D p :=
      setIntegral_mono_set hDi (Filter.Eventually.of_forall hDn)
        (Filter.Eventually.of_forall hKB)
    _ = ∫ x in J, ∫ s in Icc (-M) M, D (s, x) := by
      change (∫ p in Icc (-M) M ×ˢ J, D p) = _
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact integral_prod_symm D (by
        simpa only [IntegrableOn, Measure.volume_eq_prod, Measure.prod_restrict] using hDi)
    _ ≤ _ := by
      have hi : IntegrableOn (fun x => ∫ s in Icc (-M) M, D (s, x)) J := by
        apply Integrable.integral_prod_right
        simpa only [IntegrableOn, Measure.volume_eq_prod, Measure.prod_restrict] using hDi
      have hc : Continuous (fun x => u (M + 1, x) - u (-M, x)) :=
        (hu.comp (continuous_const.prodMk continuous_id)).sub
          (hu.comp (continuous_const.prodMk continuous_id))
      apply setIntegral_mono_on hi (hc.continuousOn.integrableOn_compact hJ) hJ.measurableSet
      intro x _
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -M ≤ M)]
      exact integral_difference_le (hu.comp (continuous_id.prodMk continuous_const))
        (hm x) (-M) M hh hh1

end LatticeProb.Scaling.TimeDifference
