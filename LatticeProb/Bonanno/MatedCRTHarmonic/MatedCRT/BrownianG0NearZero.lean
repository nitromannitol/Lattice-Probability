/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MatedCRT.BrownianG0NearZero at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.BrownianMotion.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne

/-!
# Immediate Brownian oscillation for the G0 proof

The germ zero-one law and Gaussian scaling show that standard Brownian motion takes negative
values in every right neighborhood of zero. This is used to rule out a deterministic mesh point
being a minimizer shared by adjacent intervals.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open QuantumZipper.GermZeroOne

noncomputable section

namespace MatedCRTHarmonic.MatedCRT.BrownianG0NearZero

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Gaussian scaling lower bound for a linear threshold near time zero. -/
private lemma gaussianReal_Iio_ge {t : ℝ≥0} (ht : 0 < t) (ht1 : t ≤ 1) (c : ℝ) :
    gaussianReal 0 1 (Iio (-|c|)) ≤ gaussianReal 0 t (Iio (c * t)) := by
  have hmap : (gaussianReal 0 1).map ((√(t : ℝ)) * ·) = gaussianReal 0 t := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iio]
  refine measure_mono fun x hx => ?_
  simp only [mem_Iio, mem_preimage] at hx ⊢
  have hs : 0 < √(t : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast ht)
  have hs1 : √(t : ℝ) ≤ 1 := Real.sqrt_le_one.2 (by exact_mod_cast ht1)
  have htt : (t : ℝ) = √(t : ℝ) * √(t : ℝ) := (Real.mul_self_sqrt t.2).symm
  have h1 : √(t : ℝ) * x < √(t : ℝ) * (-|c|) := mul_lt_mul_of_pos_left hx hs
  have h2 : -|c| * √(t : ℝ) ≤ c * √(t : ℝ) :=
    mul_le_mul_of_nonneg_right (neg_abs_le c) hs.le
  have h3 : -|c| ≤ -|c| * √(t : ℝ) := by
    have := abs_nonneg c
    nlinarith
  have h5 : c * (t : ℝ) = (c * √(t : ℝ)) * √(t : ℝ) := by
    rw [mul_assoc, ← htt]
  have h6 : -|c| * √(t : ℝ) ≤ (-|c| * √(t : ℝ)) * √(t : ℝ) := by
    have := abs_nonneg c
    nlinarith
  have h7 := mul_le_mul_of_nonneg_right h2 hs.le
  rw [h5]
  linarith

private lemma gaussianReal_Iio_pos (a : ℝ) : 0 < gaussianReal 0 1 (Iio a) := by
  refine pos_iff_ne_zero.2 fun h => ?_
  have := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero h
  simp at this

/-- For each real slope, standard Brownian motion beats that slope at arbitrarily small
deterministic times, almost surely. -/
theorem ae_frequently_lt {B : ℝ≥0 → Ω → ℝ} [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (c : ℝ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ k, n ≤ k ∧
      B (QuantumZipper.GermZeroOne.epsSeq k) ω < c * QuantumZipper.GermZeroOne.epsSeq k := by
  let A : ℕ → Set Ω := fun k =>
    {ω | B (QuantumZipper.GermZeroOne.epsSeq k) ω < c * QuantumZipper.GermZeroOne.epsSeq k}
  let F : ℕ → Set Ω := fun n => ⋃ k, ⋃ (_ : n ≤ k), A k
  have hA : ∀ k, MeasurableSet (A k) := fun k => measurableSet_lt (hBm _) measurable_const
  have hF : ∀ n, MeasurableSet (F n) := fun n =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hA k
  have hanti : Antitone F := fun n m hnm => by
    intro ω hω
    simp only [F, mem_iUnion] at hω ⊢
    obtain ⟨k, hk, h⟩ := hω
    exact ⟨k, hnm.trans hk, h⟩
  let δ := gaussianReal 0 1 (Iio (-|c|))
  have hAδ : ∀ k, δ ≤ P (A k) := fun k => by
    have hL := hB.toIsPreBrownianReal.hasLaw_eval
      (QuantumZipper.GermZeroOne.epsSeq k)
    have hprob : P (A k) = gaussianReal 0
        (QuantumZipper.GermZeroOne.epsSeq k)
        (Iio (c * QuantumZipper.GermZeroOne.epsSeq k)) := by
      rw [← hL.map_eq, Measure.map_apply (hBm _) measurableSet_Iio]
      rfl
    rw [hprob]
    apply gaussianReal_Iio_ge (QuantumZipper.GermZeroOne.epsSeq_pos k)
    unfold QuantumZipper.GermZeroOne.epsSeq
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left bot_le)
  have hE : δ ≤ P (⋂ n, F n) := by
    rw [hanti.measure_iInter (fun n => (hF n).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
    exact le_iInf fun n => (hAδ n).trans (measure_mono fun ω h =>
      mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨le_rfl, h⟩⟩)
  have hG : MeasurableSet[⨅ n,
      QuantumZipper.GermZeroOne.bmPast B
        (QuantumZipper.GermZeroOne.epsSeq n)] (⋂ n, F n) := by
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    have e : (⋂ n, F n) = ⋂ n, F (n + m) := by
      ext ω
      simp only [mem_iInter]
      exact ⟨fun h n => h _, fun h n => hanti (Nat.le_add_right n m) (h n)⟩
    rw [e]
    refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
      MeasurableSet.iUnion fun hk => ?_
    exact measurableSet_lt
      (QuantumZipper.GermZeroOne.measurable_bmPast_coord
        (QuantumZipper.GermZeroOne.epsSeq_antitone (by omega))) measurable_const
  have h1 : P (⋂ n, F n) = 1 := by
    rcases QuantumZipper.GermZeroOne.isTrivialSigma_iInf_bmPast hB hBm _ hG with h | h
    · exfalso
      have hp := gaussianReal_Iio_pos (-|c|)
      rw [h] at hE
      exact hp.ne' (le_antisymm hE bot_le)
    · exact h
  have hae : ∀ᵐ ω ∂P, ω ∈ ⋂ n, F n :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iInter hF)).2 h1
  filter_upwards [hae] with ω hω n
  have hn := mem_iInter.1 hω n
  simp only [F, A, mem_iUnion, mem_ofPred_eq] at hn
  obtain ⟨k, hk, h⟩ := hn
  exact ⟨k, hk, h⟩

/-- Standard Brownian motion takes a negative value in every right neighborhood of zero,
almost surely. -/
theorem ae_negative_near_zero {B : ℝ≥0 → Ω → ℝ} [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ∃ r : ℝ≥0, 0 < r ∧ r < t ∧ B r ω < 0 := by
  filter_upwards [ae_frequently_lt hB hBm 0] with ω hω t ht
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < (t : ℝ) by exact_mod_cast ht)
  obtain ⟨k, hk, hneg⟩ := hω n
  refine ⟨QuantumZipper.GermZeroOne.epsSeq k,
    QuantumZipper.GermZeroOne.epsSeq_pos k, ?_, ?_⟩
  · have hkn : QuantumZipper.GermZeroOne.epsSeq k ≤
        QuantumZipper.GermZeroOne.epsSeq n :=
      QuantumZipper.GermZeroOne.epsSeq_antitone hk
    have hn' : (QuantumZipper.GermZeroOne.epsSeq n : ℝ) < t := by
      simpa [QuantumZipper.GermZeroOne.epsSeq, one_div] using hn
    exact lt_of_le_of_lt hkn (by exact_mod_cast hn')
  · simpa using hneg

end MatedCRTHarmonic.MatedCRT.BrownianG0NearZero

end
