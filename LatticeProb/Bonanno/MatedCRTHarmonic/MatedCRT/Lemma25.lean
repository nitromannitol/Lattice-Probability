/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MatedCRT.Lemma25 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.GraphMeasurability
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.LocalFiniteness
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Deg
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Brownian.OneStep
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.StrongMarkov
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.StrongMarkov
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.Markov
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStrongMarkov
import LatticeProb.Bonanno.LQGMetric.Prob.BinomialDomination

/-!
# [18] Lemma 2.5: exponential tail of mated-CRT degrees

Gwynne--Miller, *Harmonic functions on mated-CRT maps*, Lemma 2.5, source copy
, lines 925--941. The proof follows the corrected
stopping-time and binomial-tail route in, Details (c1).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRTHarmonic.MatedCRT

/-- Start a coordinate Brownian motion at time `-1`, so the initial interval used in the degree
condition is part of the Brownian past. -/
def lemma25BaseCoord (i : Fin 2) (t : ℝ≥0) (ω : Path2) : ℝ :=
  lrCoord i ((t : ℝ) - 1) ω - lrCoord i (-1) ω

private theorem lemma25_shifted_twoSidedMin {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) :
    twoSidedMin (s - 1) (t - 1) - twoSidedMin (s - 1) (-1) -
      twoSidedMin (-1) (t - 1) + twoSidedMin (-1) (-1) = s := by
  have hD : twoSidedMin (-1) (-1) = 1 := by
    unfold twoSidedMin
    norm_num
  have ht0 : 0 ≤ t := hs0.trans hst
  by_cases hs : s ≤ 1
  · by_cases ht : t ≤ 1
    · have hA : twoSidedMin (s - 1) (t - 1) = 1 - t := by
        unfold twoSidedMin
        have hp : max (s - 1) 0 = 0 := max_eq_right (by linarith)
        have hq : max (t - 1) 0 = 0 := max_eq_right (by linarith)
        have hn : max (-(s - 1)) 0 = 1 - s := by
          rw [show -(s - 1) = 1 - s by ring]
          exact max_eq_left (by linarith)
        have hm : max (-(t - 1)) 0 = 1 - t := by
          rw [show -(t - 1) = 1 - t by ring]
          exact max_eq_left (by linarith)
        rw [hp, hq, hn, hm]
        simp [min_eq_right (by linarith : 1 - t ≤ 1 - s)]
      have hB : twoSidedMin (s - 1) (-1) = 1 - s := by
        unfold twoSidedMin
        have hp : max (s - 1) 0 = 0 := max_eq_right (by linarith)
        have hn : max (-(s - 1)) 0 = 1 - s := by
          rw [show -(s - 1) = 1 - s by ring]
          exact max_eq_left (by linarith)
        rw [hp, max_eq_right (by norm_num : -1 ≤ (0 : ℝ)), hn,
          show -(-1 : ℝ) = 1 by norm_num, max_eq_left (by norm_num : 0 ≤ (1 : ℝ))]
        simp [min_eq_left (by linarith : 1 - s ≤ 1)]
      have hC : twoSidedMin (-1) (t - 1) = 1 - t := by
        unfold twoSidedMin
        have hn : max (-(t - 1)) 0 = 1 - t := by
          rw [show -(t - 1) = 1 - t by ring]
          exact max_eq_left (by linarith)
        rw [max_eq_right (by norm_num : -1 ≤ (0 : ℝ)), max_eq_right (by linarith : t - 1 ≤ 0),
          show -(-1 : ℝ) = 1 by norm_num, max_eq_left (by norm_num : 0 ≤ (1 : ℝ)), hn]
        rw [min_eq_right (by linarith [ht0] : 1 - t ≤ 1)]
        simp
      rw [hA, hB, hC, hD]
      ring
    · have htp : 0 < t - 1 := by linarith
      have hA : twoSidedMin (s - 1) (t - 1) = 0 := by
        unfold twoSidedMin
        have hn : max (-(s - 1)) 0 = 1 - s := by
          rw [show -(s - 1) = 1 - s by ring]
          exact max_eq_left (by linarith)
        have hm : max (-(t - 1)) 0 = 0 := max_eq_right (by linarith)
        rw [max_eq_right (by linarith : s - 1 ≤ 0), max_eq_left (le_of_lt htp), hn, hm]
        rw [min_eq_left (by linarith : (0 : ℝ) ≤ t - 1),
          min_eq_right (by linarith : (0 : ℝ) ≤ 1 - s)]
        ring
      have hB : twoSidedMin (s - 1) (-1) = 1 - s := by
        unfold twoSidedMin
        have hn : max (-(s - 1)) 0 = 1 - s := by
          rw [show -(s - 1) = 1 - s by ring]
          exact max_eq_left (by linarith)
        rw [max_eq_right (by linarith : s - 1 ≤ 0), max_eq_right (by norm_num : -1 ≤ (0 : ℝ)), hn,
          show -(-1 : ℝ) = 1 by norm_num, max_eq_left (by norm_num : 0 ≤ (1 : ℝ))]
        simp [min_eq_left (by linarith : 1 - s ≤ 1)]
      have hC : twoSidedMin (-1) (t - 1) = 0 := by
        unfold twoSidedMin
        have hn : max (-(t - 1)) 0 = 0 := max_eq_right (by linarith)
        rw [max_eq_right (by norm_num : -1 ≤ (0 : ℝ)), max_eq_left (le_of_lt htp),
          show -(-1 : ℝ) = 1 by norm_num, max_eq_left (by norm_num : 0 ≤ (1 : ℝ)), hn]
        rw [min_eq_left (by linarith : (0 : ℝ) ≤ t - 1), min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
        ring
      rw [hA, hB, hC, hD]
      linarith
  · have hsp : 0 < s - 1 := by linarith
    have hs1 : 1 ≤ s := by linarith [hsp]
    have htp : 0 < t - 1 := by linarith [hsp, hst]
    have hA : twoSidedMin (s - 1) (t - 1) = s - 1 := by
      unfold twoSidedMin
      have hns : -(s - 1) ≤ 0 := by linarith [hsp]
      have hn : max (-(s - 1)) 0 = 0 := max_eq_right hns
      have hm : max (-(t - 1)) 0 = 0 := max_eq_right (by linarith)
      rw [max_eq_left (le_of_lt hsp), max_eq_left (by linarith : 0 ≤ t - 1), hn, hm]
      rw [min_eq_left (by linarith : s - 1 ≤ t - 1)]
      simp
    have hB : twoSidedMin (s - 1) (-1) = 0 := by
      unfold twoSidedMin
      have hns : -(s - 1) ≤ 0 := by linarith [hsp]
      have hn : max (-(s - 1)) 0 = 0 := max_eq_right hns
      have hp : max (s - 1) 0 = s - 1 := max_eq_left (le_of_lt hsp)
      have hm : max (-1 : ℝ) 0 = 0 := max_eq_right (by norm_num)
      have hnn : -(-1 : ℝ) = 1 := by norm_num
      have h1 : max (1 : ℝ) 0 = 1 := max_eq_left (by norm_num)
      rw [hp, hm, hn, hnn, h1]
      rw [min_eq_right (by linarith [hsp] : (0 : ℝ) ≤ s - 1),
        min_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
      ring
    have hC : twoSidedMin (-1) (t - 1) = 0 := by
      unfold twoSidedMin
      have hnt : -(t - 1) ≤ 0 := by linarith [htp]
      have hn : max (-(t - 1)) 0 = 0 := max_eq_right hnt
      have hm : max (-1 : ℝ) 0 = 0 := max_eq_right (by norm_num)
      have hp : max (t - 1) 0 = t - 1 := max_eq_left (le_of_lt htp)
      have hnn : -(-1 : ℝ) = 1 := by norm_num
      have h1 : max (1 : ℝ) 0 = 1 := max_eq_left (by norm_num)
      rw [hm, hp, hnn, h1, hn]
      rw [min_eq_left (by linarith [htp] : (0 : ℝ) ≤ t - 1),
        min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      ring
    rw [hA, hB, hC, hD]
    ring

/-- The coordinate viewed from time `-1` is a standard Brownian motion, with its initial path
`[-1,0]` in the time interval `[0,1]`. -/
theorem lemma25_baseCoord_isPreBrownianReal {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) :
    IsPreBrownianReal (lemma25BaseCoord i) μ := by
  letI : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hGP : IsGaussianProcess (lemma25BaseCoord i) μ := by
    apply hμ.isGaussianProcess.of_isGaussianProcess
    intro t
    let p : Fin 2 × ℝ := (i, (t : ℝ) - 1)
    let q : Fin 2 × ℝ := (i, -1)
    let I : Finset (Fin 2 × ℝ) := {p, q}
    let L : (I → ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) ⟨p, by simp [I]⟩ -
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) ⟨q, by simp [I]⟩
    refine ⟨I, L, ?_⟩
    intro ω
    simp [lemma25BaseCoord, p, q, I, L]
  refine hGP.isPreBrownianReal_of_covariance ?_ ?_
  · intro t
    change ∫ ω, lrCoord i ((t : ℝ) - 1) ω - lrCoord i (-1) ω ∂μ = 0
    rw [integral_sub]
    · rw [hμ.integral_eq_zero, hμ.integral_eq_zero, sub_self]
    · exact (hμ.isGaussianProcess.hasGaussianLaw_eval (i, (t : ℝ) - 1)).integrable
    · exact (hμ.isGaussianProcess.hasGaussianLaw_eval (i, -1)).integrable
  · intro s t hst
    have hmem (u : ℝ) : MemLp (fun ω => lrCoord i u ω) 2 μ :=
      (hμ.isGaussianProcess.hasGaussianLaw_eval (i, u)).memLp_two
    change cov[(fun ω => lrCoord i ((s : ℝ) - 1) ω - lrCoord i (-1) ω),
      (fun ω => lrCoord i ((t : ℝ) - 1) ω - lrCoord i (-1) ω); μ] = (s : ℝ)
    rw [covariance_fun_sub_fun_sub (hmem _) (hmem _) (hmem _) (hmem _),
      hμ.covariance_eq, hμ.covariance_eq, hμ.covariance_eq, hμ.covariance_eq]
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    simp_rw [show lrCov γ i i = 1 by simp [lrCov]]
    simp only [one_mul]
    exact lemma25_shifted_twoSidedMin (NNReal.coe_nonneg s) hst'

/-- The shifted coordinate is a Brownian motion with continuous paths. -/
theorem lemma25_baseCoord_isBrownianReal {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) :
    IsBrownianReal (lemma25BaseCoord i) μ := by
  refine ⟨lemma25_baseCoord_isPreBrownianReal hμ i, ?_⟩
  filter_upwards [] with ω
  unfold lemma25BaseCoord lrCoord
  split_ifs <;> fun_prop

/-- Evaluation measurability for the shifted coordinate. -/
theorem lemma25_baseCoord_measurable (i : Fin 2) :
    ∀ t, Measurable (lemma25BaseCoord i t) := by
  intro t
  unfold lemma25BaseCoord
  exact (measurable_lrCoord (i, (t : ℝ) - 1)).sub (measurable_lrCoord (i, -1))

/-- Strong Markov at a finite stopping time for the filtration generated by the shifted
coordinate. -/
theorem lemma25_isBrownianAfterStopping {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) {T : Path2 → ℝ≥0}
    (hT : IsStoppingTime (QuantumZipper.Williams.pastFilt (lemma25BaseCoord i)
      (lemma25_baseCoord_measurable i)) (fun ω => (T ω : WithTop ℝ≥0))) :
    IsBrownianReal (QuantumZipper.StrongMarkov.smShift (lemma25BaseCoord i) T) μ := by
  letI : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let B := lemma25BaseCoord i
  let hm := lemma25_baseCoord_measurable i
  have hBm : ∀ t, Measurable (B t) := hm
  have hBc : ∀ ω, Continuous (B · ω) := fun ω => by
    unfold B lemma25BaseCoord lrCoord
    split_ifs <;> fun_prop
  have hind : ∀ t, Indep
      ((QuantumZipper.Williams.pastFilt B hm) t)
      (MeasurableSpace.comap (QuantumZipper.StrongMarkov.smPath B (fun _ => t))
        MeasurableSpace.pi) μ := by
    intro t
    exact QuantumZipper.StrongMarkov.indep_shift_of_le_past
      (lemma25_baseCoord_isPreBrownianReal hμ i) (fun _ => le_rfl) t
  exact QuantumZipper.StrongMarkov.isBrownianReal_smShift
    (lemma25_baseCoord_isPreBrownianReal hμ i) hBc hBm hind hT

private theorem lemma25_gaussianLeftTail_pos :
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

/-- At every finite stopping time, the restarted shifted coordinate has the same fixed positive
probability of ending the next unit interval at least one below its value at the stopping time.
This is the uniform success probability used in the stopping-time/binomial proof of [18], Lemma
2.5. -/
theorem lemma25_smShift_unitDropProbability {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) {T : Path2 → ℝ≥0}
    (hT : IsStoppingTime (QuantumZipper.Williams.pastFilt (lemma25BaseCoord i)
      (lemma25_baseCoord_measurable i)) (fun ω => (T ω : WithTop ℝ≥0))) :
    μ {ω | QuantumZipper.StrongMarkov.smShift (lemma25BaseCoord i) T 1 ω < -1} =
      gaussianReal 0 1 (Iio (-1 : ℝ)) := by
  letI : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hPost := lemma25_isBrownianAfterStopping hμ i hT
  have hm : ∀ t, Measurable (lemma25BaseCoord i t) := lemma25_baseCoord_measurable i
  have hc : ∀ ω, Continuous (lemma25BaseCoord i · ω) := fun ω => by
    unfold lemma25BaseCoord lrCoord
    split_ifs <;> fun_prop
  have hTm := QuantumZipper.StrongMarkov.measurable_of_isStoppingTime hT
  have hEval := QuantumZipper.StrongMarkov.measurable_smShift hc hm hTm (1 : ℝ≥0)
  have hlaw := hPost.toIsPreBrownianReal.hasLaw_eval (1 : ℝ≥0)
  calc μ {ω | QuantumZipper.StrongMarkov.smShift (lemma25BaseCoord i) T 1 ω < -1}
      = μ ((fun ω => QuantumZipper.StrongMarkov.smShift (lemma25BaseCoord i) T 1 ω) ⁻¹'
          Iio (-1 : ℝ)) := rfl
    _ = (μ.map (fun ω => QuantumZipper.StrongMarkov.smShift (lemma25BaseCoord i) T 1 ω))
          (Iio (-1 : ℝ)) := by
          symm
          exact Measure.map_apply hEval measurableSet_Iio
    _ = gaussianReal 0 1 (Iio (-1 : ℝ)) :=
      congrArg (fun ν : Measure ℝ => ν (Iio (-1 : ℝ))) hlaw.map_eq

/-- The strong Markov estimate in the conditional-expectation form consumed by the iterated
binomial-domination lemma. -/
theorem lemma25_condExp_unitDrop {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) {T : Path2 → ℝ≥0}
    (hT : IsStoppingTime (QuantumZipper.Williams.pastFilt (lemma25BaseCoord i)
      (lemma25_baseCoord_measurable i)) (fun ω => (T ω : WithTop ℝ≥0))) :
    μ[(fun ω =>
      {ω | QuantumZipper.StrongMarkov.smShift (lemma25BaseCoord i) T 1 ω < -1}.indicator
        (fun _ : Path2 => (1 : ℝ)) ω) | hT.measurableSpace] =ᵐ[μ] fun _ =>
        (gaussianReal 0 1 (Iio (-1 : ℝ))).toReal := by
  letI : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let B := lemma25BaseCoord i
  let hm := lemma25_baseCoord_measurable i
  have hBm : ∀ t, Measurable (B t) := hm
  have hBc : ∀ ω, Continuous (B · ω) := fun ω => by
    unfold B lemma25BaseCoord lrCoord
    split_ifs <;> fun_prop
  have hind := QuantumZipper.StrongMarkov.indep_smPath
    (lemma25_baseCoord_isPreBrownianReal hμ i) hBc hBm
    (fun t => QuantumZipper.StrongMarkov.indep_shift_of_le_past
      (lemma25_baseCoord_isPreBrownianReal hμ i) (fun _ => le_rfl) t) hT
  let mΩ : MeasurableSpace Path2 := inferInstance
  have hle₁ : hT.measurableSpace ≤ mΩ := hT.measurableSpace_le
  have hshift : Measurable (QuantumZipper.StrongMarkov.smPath B T) :=
    QuantumZipper.StrongMarkov.measurable_smPath hBc hBm
      (QuantumZipper.StrongMarkov.measurable_of_isStoppingTime hT)
  have hle₂ : MeasurableSpace.comap (QuantumZipper.StrongMarkov.smPath B T)
      MeasurableSpace.pi ≤ mΩ := hshift.comap_le
  let A : Set Path2 := {ω | QuantumZipper.StrongMarkov.smShift B T 1 ω < -1}
  have hA₂ : MeasurableSet[MeasurableSpace.comap
      (QuantumZipper.StrongMarkov.smPath B T) MeasurableSpace.pi] A := by
    change MeasurableSet[MeasurableSpace.comap
      (QuantumZipper.StrongMarkov.smPath B T) MeasurableSpace.pi]
        ((fun ω => QuantumZipper.StrongMarkov.smPath B T ω 1) ⁻¹' Iio (-1 : ℝ))
    exact measurableSet_preimage
      ((measurable_pi_apply (1 : ℝ≥0)).comp
        (comap_measurable (QuantumZipper.StrongMarkov.smPath B T))) measurableSet_Iio
  have hAm : MeasurableSet A := hle₂ _ hA₂
  have hf : StronglyMeasurable[MeasurableSpace.comap
      (QuantumZipper.StrongMarkov.smPath B T) MeasurableSpace.pi]
      (A.indicator (fun _ : Path2 => (1 : ℝ))) :=
    (measurable_const.indicator hA₂).stronglyMeasurable
  have hInd := MeasureTheory.condExp_indep_eq
    (m₁ := MeasurableSpace.comap (QuantumZipper.StrongMarkov.smPath B T) MeasurableSpace.pi)
    (m₂ := hT.measurableSpace) (m := mΩ) hle₂ hle₁ hf hind.symm
  have hp := lemma25_smShift_unitDropProbability hμ i hT
  have hint : ∫ ω, A.indicator (fun _ : Path2 => (1 : ℝ)) ω ∂μ =
      (gaussianReal 0 1 (Iio (-1 : ℝ))).toReal := by
    calc ∫ ω, A.indicator (fun _ : Path2 => (1 : ℝ)) ω ∂μ
        = μ.real A := by
          change ∫ ω, A.indicator (1 : Path2 → ℝ) ω ∂μ = μ.real A
          exact integral_indicator_one hAm
      _ = (gaussianReal 0 1 (Iio (-1 : ℝ))).toReal := by
        have hp' : μ A = gaussianReal 0 1 (Iio (-1 : ℝ)) := by
          simpa [A, B] using hp
        rw [MeasureTheory.Measure.real_def, hp']
  filter_upwards [hInd] with ω hω
  rw [hω, hint]

/-- The minimum of the shifted coordinate over the initial unit interval. -/
def lemma25InitialMinimum (i : Fin 2) (ω : Path2) : ℝ :=
  sInf ((fun t : ℝ≥0 => lemma25BaseCoord i t ω) '' Icc (0 : ℝ≥0) 1)

/-- A Gaussian oscillation tail for the initial minimum. The minimum is bounded below by the
negative Brownian oscillation on `[0,1]`. -/
theorem lemma25_initialMinimum_tail {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) {a : ℝ} (ha : 0 < a) :
    μ {ω | lemma25InitialMinimum i ω < -a} ≤
      ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / 2)) := by
  let B := lemma25BaseCoord i
  have hB := lemma25_baseCoord_isPreBrownianReal hμ i
  have hBm : ∀ t, Measurable (B t) := lemma25_baseCoord_measurable i
  have hBc : ∀ ω, Continuous (B · ω) := fun ω => by
    unfold B lemma25BaseCoord lrCoord
    split_ifs <;> fun_prop
  have hsubset : {ω | lemma25InitialMinimum i ω < -a} ⊆
      {ω | a < QuantumZipper.bmOsc B 0 1 ω} := by
    intro ω hω
    let X : ℝ≥0 → ℝ := fun t => B t ω
    let K := X '' Icc (0 : ℝ≥0) 1
    have hK : IsCompact K := isCompact_Icc.image (hBc ω)
    have hKn : K.Nonempty := ⟨X 0, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
    have hmem : sInf K ∈ K := hK.sInf_mem hKn
    obtain ⟨s, hs, hval⟩ := hmem
    have hslo : a < |B s ω| := by
      have hval' : B s ω = lemma25InitialMinimum i ω := by
        simpa [K, X, B, lemma25InitialMinimum] using hval
      change lemma25InitialMinimum i ω < -a at hω
      rw [← hval'] at hω
      have hneg : B s ω < 0 := lt_trans hω (by linarith)
      rw [abs_of_neg hneg]
      linarith
    have hs' : s ∈ Icc (0 : ℝ≥0) (0 + 1) := by simpa using hs
    have hosc := Brownian.abs_sub_le_bmOsc (B := B) (hBc ω)
      (t₀ := 0) (s := 1) (t := s) hs'
    have hB0 : B 0 ω = 0 := by
      simp [B, lemma25BaseCoord, lrCoord]
    rw [hB0, sub_zero] at hosc
    exact lt_of_lt_of_le hslo hosc
  calc μ {ω | lemma25InitialMinimum i ω < -a}
      ≤ μ {ω | a < QuantumZipper.bmOsc B 0 1 ω} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / 2)) := by
      simpa [B] using (QuantumZipper.BMOsc.bmOsc_tail hB hBm hBc 0 1
        (by norm_num) ha)

/-- Raw labelled edge ends leaving `x`, before using the a.s. local-finiteness witness to form
the frozen locally-finite multigraph. -/
def lemma25IncidentDarts (ε : ℝ) (ω : Path2) (x : ℤ) :
    Set ((ℤ × ℤ × Bool) × Bool) :=
  {d | IsEdge ε ω d.1 ∧ (if d.2 then d.1.2.1 else d.1.1) = x}

/-- Extended degree of `x`; it agrees with the frozen graph degree on locally finite paths. -/
def lemma25Degree (ε : ℝ) (ω : Path2) (x : ℤ) : ℕ∞ :=
  (lemma25IncidentDarts ε ω x).encard

private theorem measurable_lemma25IncidentDarts (ε : ℝ) (x : ℤ) :
    Measurable (fun ω : Path2 => lemma25IncidentDarts ε ω x) := by
  classical
  change Measurable (fun ω : Path2 => fun d : (ℤ × ℤ × Bool) × Bool =>
    IsEdge ε ω d.1 ∧ (if d.2 then d.1.2.1 else d.1.1) = x)
  apply measurable_pi_iff.mpr
  intro d
  have hm : Measurable (fun ω : Path2 => edgePredicate ε ω d.1) :=
    (measurable_pi_iff.mp (matedCRT_edgePredicate_measurable_holds ε)) d.1
  have h : Measurable (fun ω : Path2 => IsEdge ε ω d.1) := by
    simpa [edgePredicate] using hm.eq_const true
  exact h.and measurable_const

private def lemma25IncidentDarts_equiv {ε : ℝ} {ω : Path2} {x : ℤ}
    (hLF : IsLocallyFinite ε ω) :
    lemma25IncidentDarts ε ω x ≃ {d : (graph ε ω hLF).Dart |
      (graph ε ω hLF).dsrc d = x} := by
  let G := graph ε ω hLF
  refine
    { toFun := fun d => ⟨(⟨d.1.1, d.2.1⟩, d.1.2), ?_⟩
      invFun := fun d => ⟨(d.1.1.1, d.1.2), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change (if d.1.2 then d.1.1.2.1 else d.1.1.1) = x
    exact d.2.2
  · change IsEdge ε ω d.1.1.1 ∧
      (if d.1.2 then d.1.1.1.2.1 else d.1.1.1.1) = x
    exact ⟨d.1.1.2, by simpa [G, graph, LFMultigraph.dsrc] using d.2⟩
  · intro d
    apply Subtype.ext
    rfl
  · intro d
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl

theorem lemma25Degree_eq_graph_deg {ε : ℝ} {ω : Path2} {x : ℤ}
    (hLF : IsLocallyFinite ε ω) :
    lemma25Degree ε ω x = (LFMultigraph.deg (graph ε ω hLF) x : ℕ∞) := by
  let G := graph ε ω hLF
  have hset : {d : G.Dart | G.dsrc d = x} = (G.outDarts x : Set G.Dart) := by
    classical
    ext d
    change G.dsrc d = x ↔ d ∈ G.outDarts x
    simp only [LFMultigraph.outDarts, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and, and_true, Set.Finite.mem_toFinset]
    constructor
    · intro hd
      have hi : d.1 ∈ {e | G.src e = x ∨ G.tgt e = x} := by
        change G.src d.1 = x ∨ G.tgt d.1 = x
        by_cases hb : d.2
        · simp [LFMultigraph.dsrc, hb] at hd
          exact Or.inr hd
        · simp [LFMultigraph.dsrc, hb] at hd
          exact Or.inl hd
      exact ⟨hi, hd⟩
    · intro hd
      exact hd.2
  rw [lemma25Degree, Set.encard_congr (lemma25IncidentDarts_equiv hLF), hset,
    Set.encard_coe_eq_coe_finsetCard]
  rfl

theorem measurable_lemma25Degree (ε : ℝ) (x : ℤ) :
    Measurable (fun ω : Path2 => lemma25Degree ε ω x) := by
  exact measurable_encard.comp (measurable_lemma25IncidentDarts ε x)

end MatedCRTHarmonic.MatedCRT
