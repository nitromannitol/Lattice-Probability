/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MatedCRT.BrownianPathFacts at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianLaw
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.TailTrivial
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.OccupationHit2

/-!
# One-sided Brownian coordinates of the mated-CRT path law

The covariance specification of [18] §1.1 restricts on each half-line to standard Brownian
motion. These facts are the probability input for local finiteness of the graph.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRTHarmonic.MatedCRT

/-- Restricting either coordinate of a correlated two-sided Brownian law to nonnegative times
produces a standard pre-Brownian motion. -/
theorem coordinate_isPreBrownianReal {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) :
    IsPreBrownianReal (fun t ω => lrCoord i t ω) μ := by
  have hGP : IsGaussianProcess (fun t : ℝ≥0 => lrCoord i t) μ :=
    hμ.isGaussianProcess.comp_right (fun t : ℝ≥0 => (i, (t : ℝ)))
  have hmean : ∀ t : ℝ≥0, μ[lrCoord i t] = 0 := by
    intro t
    exact hμ.integral_eq_zero i t
  have hcov : ∀ s t : ℝ≥0, s ≤ t →
      cov[lrCoord i s, lrCoord i t; μ] = s := by
    intro s t hst
    have h : cov[lrCoord i s, lrCoord i t; μ] = twoSidedMin s t := by
      simpa [lrCov] using hμ.covariance_eq i i s t
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    have hmin : twoSidedMin s t = (s : ℝ) := by
      simp [twoSidedMin, min_eq_left hst']
    rw [hmin] at h
    exact h
  exact hGP.isPreBrownianReal_of_covariance hmean hcov

/-- Reversing time on the negative half-line gives another standard pre-Brownian coordinate. -/
theorem coordinate_neg_isPreBrownianReal {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) :
    IsPreBrownianReal (fun t ω => lrCoord i (-(t : ℝ)) ω) μ := by
  have hGP : IsGaussianProcess (fun t : ℝ≥0 => lrCoord i (-(t : ℝ)) ) μ :=
    hμ.isGaussianProcess.comp_right (fun t : ℝ≥0 => (i, -(t : ℝ)))
  have hmean : ∀ t : ℝ≥0, μ[lrCoord i (-(t : ℝ))] = 0 := by
    intro t
    exact hμ.integral_eq_zero i (-(t : ℝ))
  have hcov : ∀ s t : ℝ≥0, s ≤ t →
      cov[lrCoord i (-(s : ℝ)), lrCoord i (-(t : ℝ)); μ] = s := by
    intro s t hst
    have h : cov[lrCoord i (-(s : ℝ)), lrCoord i (-(t : ℝ)); μ] =
        twoSidedMin (-(s : ℝ)) (-(t : ℝ)) := by
      simpa [lrCov] using hμ.covariance_eq i i (-(s : ℝ)) (-(t : ℝ))
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    have hmin : twoSidedMin (-(s : ℝ)) (-(t : ℝ)) = (s : ℝ) := by
      simp [twoSidedMin, min_eq_left hst']
    rw [hmin] at h
    exact h
  exact hGP.isPreBrownianReal_of_covariance hmean hcov

namespace BrownianPathFacts

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A Brownian sample has arbitrarily low values at integer times arbitrarily far out. -/
def unboundedBelowInt (B : ℝ≥0 → Ω → ℝ) : Set Ω :=
  {ω | ∀ m : ℕ, ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ B n ω < -(m : ℝ)}

private theorem gaussianStd_leftTail_pos :
    0 < gaussianReal 0 1 (Iio (-1 : ℝ)) := by
  have hvol : volume (Ioo (-2 : ℝ) (-1)) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  have habs := gaussianReal_absolutelyContinuous' (μ := 0) (v := (1 : ℝ≥0)) (by norm_num)
  have hne : gaussianReal 0 1 (Ioo (-2 : ℝ) (-1)) ≠ 0 := by
    intro hzero
    exact hvol (habs hzero)
  have hpos : 0 < gaussianReal 0 1 (Ioo (-2 : ℝ) (-1)) := pos_iff_ne_zero.mpr hne
  exact lt_of_lt_of_le hpos (measure_mono (by
    intro x hx
    exact hx.2))

private theorem gaussianReal_leftTail_ge {m n : ℕ} (hn : (m + 1) ^ 2 ≤ n) :
    gaussianReal 0 1 (Iio (-1 : ℝ)) ≤ gaussianReal 0 (n : ℝ≥0) (Iio (-(m : ℝ))) := by
  let S : ℝ → ℝ := fun z => Real.sqrt (n : ℝ) * z
  have hnreal : ((m + 1 : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn
  push_cast at hnreal
  have hroot : (m : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [hm0]
  have hpow : 0 < (m + 1) ^ 2 := pow_pos (Nat.succ_pos m) 2
  have h1n : 1 ≤ n := (Nat.succ_le_iff.mpr hpow).trans hn
  have hrootpos : 0 < Real.sqrt (n : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast (show (0 : ℕ) < n by omega)
  have hvar : (NNReal.mk (Real.sqrt (n : ℝ) ^ 2) (sq_nonneg _) * 1) = (n : ℝ≥0) := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
    rw [Real.sq_sqrt (by positivity)]
    norm_cast
  have hscale : (gaussianReal 0 1).map S = gaussianReal 0 (n : ℝ≥0) := by
    change (gaussianReal 0 1).map (fun z => Real.sqrt (n : ℝ) * z) = _
    rw [gaussianReal_map_const_mul, hvar]
    simp
  have hpre : Iio (-1 : ℝ) ⊆ S ⁻¹' Iio (-(m : ℝ)) := by
    intro z hz
    change z < -1 at hz
    change Real.sqrt (n : ℝ) * z < -(m : ℝ)
    have hz' : Real.sqrt (n : ℝ) * z < -Real.sqrt (n : ℝ) := by
      nlinarith [mul_lt_mul_of_pos_left hz hrootpos]
    linarith
  calc gaussianReal 0 1 (Iio (-1 : ℝ))
      ≤ gaussianReal 0 1 (S ⁻¹' Iio (-(m : ℝ))) := measure_mono hpre
    _ = (gaussianReal 0 1).map S (Iio (-(m : ℝ))) := by
      rw [MeasureTheory.Measure.map_apply (by fun_prop) measurableSet_Iio]
    _ = gaussianReal 0 (n : ℝ≥0) (Iio (-(m : ℝ))) := by rw [hscale]

/-- Every pre-Brownian motion is unbounded below along integer times, almost surely. The proof
uses Gaussian scaling for a uniform positive lower bound on each remote one-time tail, then the
large-time tail zero-one law. -/
theorem ae_unboundedBelowInt {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P, ω ∈ unboundedBelowInt B := by
  classical
  let A := unboundedBelowInt B
  have hAmeas : MeasurableSet A := by
    unfold A unboundedBelowInt
    simp only [Set.setOf_forall, Set.setOf_exists, Set.setOf_and]
    measurability
  have hAtail : MeasurableSet[QuantumZipper.TailTrivial.tailFar B] A := by
    apply (MeasurableSpace.measurableSet_iInf).2
    intro s
    let F : Ω → (Set.Ici s → ℝ) := fun ω u => B u ω
    have hF : Measurable[MeasurableSpace.comap F inferInstance] F :=
      comap_measurable F
    have hcoord (n : ℕ) (hn : s ≤ (n : ℝ≥0)) :
        Measurable[MeasurableSpace.comap F inferInstance] (B n) := by
      change Measurable[MeasurableSpace.comap F inferInstance] (fun ω => F ω ⟨n, hn⟩)
      exact (measurable_pi_apply ⟨n, hn⟩).comp hF
    have hEq : A = {ω | ∀ m : ℕ, ∀ k : ℕ, ∃ n : ℕ,
        max k ⌈(s : ℝ)⌉₊ ≤ n ∧ B n ω < -(m : ℝ)} := by
      ext ω
      simp only [A, unboundedBelowInt, Set.mem_setOf_eq]
      constructor
      · intro h m k
        obtain ⟨n, hn, hv⟩ := h m (max k ⌈(s : ℝ)⌉₊)
        exact ⟨n, hn, hv⟩
      · intro h m k
        obtain ⟨n, hn, hv⟩ := h m k
        exact ⟨n, (le_trans (le_max_left _ _) hn), hv⟩
    rw [hEq]
    simp only [Set.setOf_forall, Set.setOf_exists, Set.setOf_and]
    refine MeasurableSet.iInter fun m => MeasurableSet.iInter fun k =>
      MeasurableSet.iUnion fun n => ?_
    by_cases hn : max k ⌈(s : ℝ)⌉₊ ≤ n
    · have hsceil : (s : ℝ) ≤ (⌈(s : ℝ)⌉₊ : ℕ) := Nat.le_ceil _
      have hceiln : (⌈(s : ℝ)⌉₊ : ℕ) ≤ n := (le_max_right _ _).trans hn
      have hceiln' : (⌈(s : ℝ)⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hceiln
      have hsn : s ≤ (n : ℝ≥0) := NNReal.coe_le_coe.mpr (hsceil.trans hceiln')
      have hmeas : MeasurableSet[MeasurableSpace.comap F inferInstance]
          {ω | B n ω < -(m : ℝ)} := by
        change MeasurableSet[MeasurableSpace.comap F inferInstance]
          ((fun ω => B n ω) ⁻¹' Iio (-(m : ℝ)))
        exact measurableSet_preimage (hcoord n hsn) measurableSet_Iio
      simpa [hn, Set.setOf_and] using hmeas
    · simp [hn, Set.setOf_and]
  letI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let c : ℝ≥0∞ := gaussianReal 0 1 (Iio (-1 : ℝ))
  have htriv := QuantumZipper.TailTrivial.isTrivialSigma_tailFar hB hBm
  have hzeroone := htriv A hAtail
  have hc : 0 < c := gaussianStd_leftTail_pos
  let T (m k : ℕ) : Set Ω := ⋃ n : ℕ, {ω | k ≤ n ∧ B n ω < -(m : ℝ)}
  let U (m : ℕ) : Set Ω := ⋂ k : ℕ, T m k
  have hTm : ∀ m k, MeasurableSet (T m k) := by
    intro m k
    change MeasurableSet (⋃ n : ℕ, {ω | k ≤ n ∧ B n ω < -(m : ℝ)})
    refine MeasurableSet.iUnion fun n => ?_
    by_cases hkn : k ≤ n
    · rw [show {ω | k ≤ n ∧ B n ω < -(m : ℝ)} = {ω | B n ω < -(m : ℝ)} by
        ext ω
        simp [hkn]]
      exact measurableSet_preimage (hBm n) (measurableSet_Iio (a := -(m : ℝ)))
    · rw [show {ω | k ≤ n ∧ B n ω < -(m : ℝ)} = ∅ by
        ext ω
        simp [hkn]]
      exact MeasurableSet.empty
  have hTk : ∀ m k, c ≤ P (T m k) := by
    intro m k
    let n := max k ((m + 1) ^ 2)
    have hkn : k ≤ n := le_max_left _ _
    have hmn : (m + 1) ^ 2 ≤ n := le_max_right _ _
    have hprob : c ≤ P {ω | B n ω < -(m : ℝ)} := by
      calc c = gaussianReal 0 1 (Iio (-1 : ℝ)) := rfl
        _ ≤ gaussianReal 0 (n : ℝ≥0) (Iio (-(m : ℝ))) := gaussianReal_leftTail_ge hmn
        _ = P {ω | B n ω < -(m : ℝ)} := by
          symm
          calc P {ω | B n ω < -(m : ℝ)}
              = P ((B n) ⁻¹' Iio (-(m : ℝ))) := by rfl
            _ = (P.map (B n)) (Iio (-(m : ℝ))) := by
              symm
              exact MeasureTheory.Measure.map_apply (hBm n) measurableSet_Iio
            _ = gaussianReal 0 (n : ℝ≥0) (Iio (-(m : ℝ))) := by
              rw [(hB.hasLaw_eval (n : ℝ≥0)).map_eq]
    have hsub : {ω | B n ω < -(m : ℝ)} ⊆ T m k := by
      intro ω hw
      simp only [T, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨n, hkn, hw⟩
    exact hprob.trans (measure_mono hsub)
  have hTanti (m : ℕ) : Antitone (T m) := by
    intro k₁ k₂ hle ω hω
    rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨hle.trans hn.1, hn.2⟩⟩
  have hUprob : ∀ m, c ≤ P (U m) := by
    intro m
    have hcont := (hTanti m).measure_iInter
      (fun k => (hTm m k).nullMeasurableSet) ⟨0, measure_ne_top P (T m 0)⟩
    rw [hcont]
    exact le_iInf fun k => hTk m k
  have hUmeas : ∀ m, MeasurableSet (U m) := by
    intro m
    exact MeasurableSet.iInter (fun k => hTm m k)
  have hUanti : Antitone U := by
    intro m₁ m₂ hle ω hω
    simp only [U, Set.mem_iInter] at hω ⊢
    intro k
    have hk := hω k
    simp only [T, Set.mem_iUnion, Set.mem_setOf_eq] at hk ⊢
    rcases hk with ⟨n, hn⟩
    have hcast : (m₁ : ℝ) ≤ m₂ := by exact_mod_cast hle
    exact ⟨n, hn.1, by linarith⟩
  have hAeq : A = ⋂ m : ℕ, U m := by
    ext ω
    simp [A, unboundedBelowInt, U, T]
  have hAprob : 0 < P A := by
    have hcont := hUanti.measure_iInter
      (fun m => (hUmeas m).nullMeasurableSet) ⟨0, measure_ne_top P (U 0)⟩
    have hbound : c ≤ P (⋂ m : ℕ, U m) := by
      rw [hcont]
      exact le_iInf fun m => hUprob m
    rw [← hAeq] at hbound
    exact lt_of_lt_of_le hc hbound
  have hAone : P A = 1 := by
    rcases hzeroone with hzero | hone
    · exact False.elim ((ne_of_gt hAprob) hzero)
    · exact hone
  rw [ae_iff]
  change P Aᶜ = 0
  rw [measure_compl hAmeas (measure_ne_top P A)]
  simp [hAone]

end BrownianPathFacts

end MatedCRTHarmonic.MatedCRT
