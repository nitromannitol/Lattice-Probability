import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-! Recovering a smooth time derivative from smooth time increments and their average.

Moved from Parking-Sharpness.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.Scaling.TimeAverage

variable {d : ℕ}

/-- The average of the forward increments over a unit time interval. -/
def averageIncrement (u : ℝ × (Fin d → ℝ) → ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  ∫ r in (0 : ℝ)..1, u (p.1 + r, p.2) - u p

/-- Averaging continuous increments over a fixed compact interval preserves
joint continuity. -/
theorem continuous_averageIncrement {u : ℝ × (Fin d → ℝ) → ℝ} (hu : Continuous u) :
    Continuous (averageIncrement u) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hu.comp ((continuous_fst.fst.add continuous_snd).prodMk continuous_fst.snd)).sub
    (hu.comp continuous_fst)

/-- Fubini for a compact time average paired with a compactly supported
continuous function. The continuous integrand is integrable on the product
of the two compact sets. -/
theorem integral_compact_average_mul
    (F : ℝ → (ℝ × (Fin d → ℝ)) → ℝ) (hF : Continuous F.uncurry)
    (g : ℝ × (Fin d → ℝ) → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g)
    (J : Set ℝ) (hJ : IsCompact J) :
    (∫ p : ℝ × (Fin d → ℝ), (∫ r in J, F r p) * g p) =
      ∫ r in J, ∫ p : ℝ × (Fin d → ℝ), F r p * g p := by
  let K := tsupport g
  have hzero (p : ℝ × (Fin d → ℝ)) (hp : p ∉ K) : g p = 0 :=
    image_eq_zero_of_notMem_tsupport hp
  have hc : Continuous (fun q : ℝ × (ℝ × (Fin d → ℝ)) => F q.1 q.2 * g q.2) :=
    hF.mul (hg.comp continuous_snd)
  have hint : Integrable (fun q : ℝ × (ℝ × (Fin d → ℝ)) => F q.1 q.2 * g q.2)
      ((volume.restrict J).prod (volume.restrict K)) := by
    rw [Measure.prod_restrict]
    exact hc.continuousOn.integrableOn_compact (hJ.prod hgs)
  calc
    _ = ∫ p in K, (∫ r in J, F r p) * g p := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      simp [hzero p hp]
    _ = ∫ p in K, ∫ r in J, F r p * g p := by
      apply integral_congr_ae
      filter_upwards with p
      exact (integral_mul_const _ _).symm
    _ = ∫ r in J, ∫ p in K, F r p * g p := (integral_integral_swap hint).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with r
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      simp [hzero p hp]

/-- A unit time average can be moved to the outside of a test pairing. -/
theorem integral_averageIncrement_mul {u : ℝ × (Fin d → ℝ) → ℝ} (hu : Continuous u)
    (g : ℝ × (Fin d → ℝ) → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g) :
    (∫ p : ℝ × (Fin d → ℝ), averageIncrement u p * g p) =
      ∫ r in Set.Icc (0 : ℝ) 1, ∫ p : ℝ × (Fin d → ℝ),
        (u (p.1 + r, p.2) - u p) * g p := by
  have hF : Continuous (Function.uncurry
      (fun r (p : ℝ × (Fin d → ℝ)) => u (p.1 + r, p.2) - u p)) :=
    (hu.comp ((continuous_snd.fst.add continuous_fst).prodMk continuous_snd.snd)).sub
      (hu.comp continuous_snd)
  have heq (p : ℝ × (Fin d → ℝ)) : averageIncrement u p =
      ∫ r in Set.Icc (0 : ℝ) 1, u (p.1 + r, p.2) - u p := by
    rw [averageIncrement, intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  simp_rw [heq]
  exact integral_compact_average_mul _ hF g hg hgs _ isCompact_Icc

/-- A forward average is a moving time integral minus the original field. -/
theorem averageIncrement_eq {u : ℝ × (Fin d → ℝ) → ℝ} (hu : Continuous u)
    (p : ℝ × (Fin d → ℝ)) :
    averageIncrement u p = (∫ t in p.1..p.1 + 1, u (t, p.2)) - u p := by
  have hc : Continuous (fun r : ℝ => u (p.1 + r, p.2)) :=
    hu.comp ((continuous_const.add continuous_id).prodMk continuous_const)
  rw [averageIncrement, intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
    (intervalIntegrable_const)]
  have ht := intervalIntegral.integral_comp_add_left (fun t : ℝ => u (t, p.2)) p.1
    (a := 0) (b := 1)
  simpa using congrArg (fun z : ℝ => z - u p) ht

/-- The derivative of a moving unit-interval integral is the increment of its
continuous integrand at the two endpoints. -/
theorem hasDerivAt_movingIntegral {f : ℝ → ℝ} (hf : Continuous f) (s : ℝ) :
    HasDerivAt (fun t => ∫ r in t..t + 1, f r) (f (s + 1) - f s) s := by
  have hprim (t : ℝ) : HasDerivAt (fun b => ∫ r in (0 : ℝ)..b, f r) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have h := ((hprim (s + 1)).comp s ((hasDerivAt_id s).add_const 1)).sub (hprim s)
  simp only [mul_one] at h
  have heq : (fun t => (∫ r in (0 : ℝ)..t + 1, f r) - ∫ r in (0 : ℝ)..t, f r) =
      fun t => ∫ r in t..t + 1, f r := by
    funext t
    exact intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  change HasDerivAt (fun t => (∫ r in (0 : ℝ)..t + 1, f r) - ∫ r in (0 : ℝ)..t, f r)
    (f (s + 1) - f s) s at h
  rwa [heq] at h

/-- Smoothness of a fixed forward increment and of the average of increments
gives a smooth classical time derivative, using only the fundamental theorem
of calculus. No convergence of derivatives of the increment family is assumed. -/
theorem exists_smooth_time_derivative {u : ℝ × (Fin d → ℝ) → ℝ} (hu : Continuous u)
    {O : Set (ℝ × (Fin d → ℝ))} (hO : IsOpen O)
    (hD : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => u (p.1 + 1, p.2) - u p) O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (averageIncrement u) O) :
    ∃ v : ℝ × (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v O ∧
      ∀ p ∈ O, HasDerivAt (fun s => u (s, p.2)) (v p) p.1 := by
  let v : ℝ × (Fin d → ℝ) → ℝ := fun p =>
    u (p.1 + 1, p.2) - u p - fderiv ℝ (averageIncrement u) p (1, 0)
  have hAsmooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p => fderiv ℝ (averageIncrement u) p (1, 0)) O :=
    (hA.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  refine ⟨v, hD.sub hAsmooth, ?_⟩
  intro p hp
  have hAslice : HasDerivAt (fun s => averageIncrement u (s, p.2))
      (fderiv ℝ (averageIncrement u) p (1, 0)) p.1 := by
    simpa only [Function.comp_def, Prod.mk.eta, id_eq] using
      (((hA.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.1
        ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)))
  have hM := hasDerivAt_movingIntegral (f := fun t => u (t, p.2))
    (hu.comp (continuous_id.prodMk continuous_const)) p.1
  have h := hM.sub hAslice
  have heq : (fun t => (∫ r in t..t + 1, u (r, p.2)) - averageIncrement u (t, p.2)) =
      fun t => u (t, p.2) := by
    funext t
    rw [averageIncrement_eq hu]
    ring
  change HasDerivAt (fun t => (∫ r in t..t + 1, u (r, p.2)) - averageIncrement u (t, p.2))
    (v p) p.1 at h
  rwa [heq] at h

end LatticeProb.Scaling.TimeAverage

end
