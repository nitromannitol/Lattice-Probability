/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.VaryingJointTransfer at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

private theorem varying_complement_zero
    {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (P : ∀ n, Measure (V n)) [∀ n, IsProbabilityMeasure (P n)]
    (A : ∀ n, Set (V n)) (hA : ∀ n, MeasurableSet (A n))
    (h : Tendsto (fun n => P n (A n)) atTop (𝓝 1)) :
    Tendsto (fun n => P n (A n)ᶜ) atTop (𝓝 0) := by
  have hpair : Tendsto (fun n : ℕ => ((1 : ENNReal), P n (A n)))
      atTop (𝓝 ((1 : ENNReal), (1 : ENNReal))) := by
    simpa only [nhds_prod_eq] using
      (show Tendsto (fun _ : ℕ => (1 : ENNReal)) atTop (𝓝 1)
        from tendsto_const_nhds).prodMk h
  have hsub : Tendsto (fun n : ℕ => (1 : ENNReal) - P n (A n))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, tsub_self] using
      (ENNReal.tendsto_sub (Or.inl ENNReal.one_ne_top)).comp hpair
  apply hsub.congr'
  filter_upwards [] with n
  have hfin : P n (A n) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one)
  have hc := measure_compl (hA n) hfin
  rw [show P n Set.univ = (1 : ENNReal) from measure_univ] at hc
  exact hc.symm

 

theorem varying_probability_inter_tendsto_one
    {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (P : ∀ n, Measure (V n)) [∀ n, IsProbabilityMeasure (P n)]
    (A B : ∀ n, Set (V n))
    (hA : ∀ n, MeasurableSet (A n))
    (hB : ∀ n, MeasurableSet (B n))
    (ha : Tendsto (fun n => P n (A n)) atTop (𝓝 1))
    (hb : Tendsto (fun n => P n (B n)) atTop (𝓝 1)) :
    Tendsto (fun n => P n (A n ∩ B n)) atTop (𝓝 1) := by
  have hac := varying_complement_zero P A hA ha
  have hbc := varying_complement_zero P B hB hb
  have hbad : Tendsto (fun n => P n (A n ∩ B n)ᶜ) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => P n (A n)ᶜ + P n (B n)ᶜ)
        atTop (𝓝 0) := by simpa only [zero_add] using hac.add hbc
    apply Filter.Tendsto.squeeze' tendsto_const_nhds hsum
      (Filter.Eventually.of_forall fun n => bot_le) ?_
    filter_upwards [] with n
    rw [compl_inter]
    exact measure_union_le _ _
  have hpair : Tendsto (fun n : ℕ => ((1 : ENNReal), P n (A n ∩ B n)ᶜ))
      atTop (𝓝 ((1 : ENNReal), (0 : ENNReal))) := by
    simpa only [nhds_prod_eq] using
      (show Tendsto (fun _ : ℕ => (1 : ENNReal)) atTop (𝓝 1)
        from tendsto_const_nhds).prodMk hbad
  have hsub : Tendsto (fun n => (1 : ENNReal) - P n (A n ∩ B n)ᶜ)
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, tsub_zero] using
      (ENNReal.tendsto_sub (Or.inl ENNReal.one_ne_top)).comp hpair
  apply hsub.congr'
  filter_upwards [] with n
  have hm : MeasurableSet (A n ∩ B n)ᶜ := ((hA n).inter (hB n)).compl
  have hfin : P n (A n ∩ B n)ᶜ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one)
  have hc := measure_compl hm hfin
  rw [show P n Set.univ = (1 : ENNReal) from measure_univ] at hc
  simpa only [compl_compl] using hc.symm

 

theorem varying_joint_comparison_upper_window
    {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    {Ω : Type*} [MeasurableSpace Ω]
    (D : ∀ n, Measure (V n)) (P : Measure Ω)
    (J : ∀ n, Measure (V n × Ω))
    [∀ n, IsProbabilityMeasure (J n)]
    (X : ∀ n, V n → ℝ) (Y : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hD : ∀ n, (J n).map Prod.fst = D n)
    (hP : ∀ n, (J n).map Prod.snd = P)
    (ξ Q : ℝ)
    (hwhite : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => P {ω | Y n ω ≤
        (2 : ℝ) ^ (-(1 - ξ * Q - δ) * (n : ℝ))}) atTop (𝓝 1))
    (hjoint : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => J n {v | X n v.1 ≤
        (2 : ℝ) ^ ((1 + δ) * (n : ℝ)) * Y n v.2}) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => D n {v | X n v ≤
        (2 : ℝ) ^ ((ξ * Q + ε) * (n : ℝ))}) atTop (𝓝 1) := by
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let A : ∀ n, Set (V n × Ω) := fun n =>
    {v | Y n v.2 ≤ (2 : ℝ) ^ (-(1 - ξ * Q - δ) * (n : ℝ))}
  let B : ∀ n, Set (V n × Ω) := fun n =>
    {v | X n v.1 ≤ (2 : ℝ) ^ ((1 + δ) * (n : ℝ)) * Y n v.2}
  have hAm : ∀ n, MeasurableSet (A n) := by
    intro n
    exact ((hY n).comp measurable_snd) measurableSet_Iic
  have hBm : ∀ n, MeasurableSet (B n) := by
    intro n
    exact measurableSet_le ((hX n).comp measurable_fst)
      (measurable_const.mul ((hY n).comp measurable_snd))
  have hAw : Tendsto (fun n => J n (A n)) atTop (𝓝 1) := by
    have hw := hwhite δ hδ
    convert hw using 1
    funext n
    rw [← hP n]
    exact (Measure.map_apply measurable_snd
      ((hY n) measurableSet_Iic)).symm
  have hAB := varying_probability_inter_tendsto_one J A B hAm hBm
    hAw (hjoint δ hδ)
  apply Filter.Tendsto.squeeze' hAB tendsto_const_nhds ?_
    (Filter.Eventually.of_forall fun n => by
      have hu : D n Set.univ = 1 := by rw [← hD n]; exact measure_univ
      exact (measure_mono (Set.subset_univ _)).trans_eq hu)
  exact Filter.Eventually.of_forall fun n => by
    have hmeas : MeasurableSet {v : V n | X n v ≤
        (2 : ℝ) ^ ((ξ * Q + ε) * (n : ℝ))} := (hX n) measurableSet_Iic
    rw [← hD n, Measure.map_apply measurable_fst hmeas]
    apply measure_mono
    intro v hv
    have hpow : (2 : ℝ) ^ ((1 + δ) * (n : ℝ)) *
        (2 : ℝ) ^ (-(1 - ξ * Q - δ) * (n : ℝ)) =
        (2 : ℝ) ^ ((ξ * Q + ε) * (n : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      dsimp [δ]
      ring
    calc
      X n v.1 ≤ (2 : ℝ) ^ ((1 + δ) * (n : ℝ)) * Y n v.2 := hv.2
      _ ≤ (2 : ℝ) ^ ((1 + δ) * (n : ℝ)) *
          (2 : ℝ) ^ (-(1 - ξ * Q - δ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hv.1 (by positivity)
      _ = _ := hpow

end SupercriticalLQGUniqueness.B2.QPos
