import LatticeProb.Analysis.UniformLimitWeightedSetIntegrals

/-!
# Uniformly Cauchy weighted primitives

Let `f k` (`k : ℕ`) be nonnegative continuous densities on `ℝ` whose primitives
`A k t = ∫₀ᵗ f k` are uniformly Cauchy on `[0, T]`. If continuous weights `w k` converge uniformly
on `[0, T]` to a continuous function `v`, then the weighted primitives `t ↦ ∫₀ᵗ f k * w k` are
uniformly Cauchy on `[0, T]` as well.

This is the form in which a time change `∫₀ᵗ e^{γ h_ε(B_s)} ds` (`h_ε` a regularized field) is
transferred to the field plus a continuous function `g`: the weight is `e^{γ g_ε(B_s)}`, where
`g_ε → g` uniformly. The proof identifies `A k` with the distribution functions of the measures
`f k ds` on `(0, T]`, realizes the uniform limit of `A k` as the distribution function of a
Stieltjes measure, and applies `tendstoUniformlyOn_setIntegral_Ioc_weighted`.

## Main results

* `LatticeProb.tendstoUniformlyOn_intervalIntegral_mul_of_uniformCauchySeqOn`: the weighted
  primitives converge uniformly on `[0, T]` to `t ↦ ∫_{(0, t]} v dν` for a finite measure `ν`
  whose distribution function on `[0, T]` is the uniform limit of `A k`.
* `LatticeProb.uniformCauchySeqOn_intervalIntegral_mul`: the weighted primitives are uniformly
  Cauchy on `[0, T]`.
-/

open MeasureTheory Set Filter

namespace LatticeProb

/-- The primitive `t ↦ ∫₀ᵗ f` of a nonnegative continuous function is monotone on `[0, ∞)`. -/
theorem intervalIntegral_le_of_nonneg {f : ℝ → ℝ} (hf0 : ∀ s, 0 ≤ f s) (hf : Continuous f)
    {x y : ℝ} (hxy : x ≤ y) : ∫ s in (0 : ℝ)..x, f s ≤ ∫ s in (0 : ℝ)..y, f s := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 x) (hf.intervalIntegrable x y)
  have hnn : 0 ≤ ∫ s in x..y, f s := intervalIntegral.integral_nonneg hxy fun s _ => hf0 s
  linarith

/-- **Weighted primitives converge.** If the primitives `t ↦ ∫₀ᵗ f k` of nonnegative continuous
densities are uniformly Cauchy on `[0, T]` and continuous weights `w k` converge uniformly on
`[0, T]` to a continuous `v`, then there are a finite measure `ν` on `ℝ` and a function `A` such
that `∫₀ᵗ f k → A t` uniformly on `[0, T]`, `ν (0, t] = A t` on `[0, T]`, and
`∫₀ᵗ f k * w k → ∫_{(0, t]} v dν` uniformly on `[0, T]`. -/
theorem tendstoUniformlyOn_intervalIntegral_mul_of_uniformCauchySeqOn {f w : ℕ → ℝ → ℝ}
    {v : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hf0 : ∀ k s, 0 ≤ f k s) (hf : ∀ k, Continuous (f k))
    (hA : UniformCauchySeqOn (fun k t => ∫ s in (0 : ℝ)..t, f k s) atTop (Icc 0 T))
    (hw : ∀ k, Continuous (w k)) (hv : Continuous v)
    (hwv : TendstoUniformlyOn w v atTop (Icc 0 T)) :
    ∃ (ν : Measure ℝ) (A : ℝ → ℝ), IsFiniteMeasure ν ∧
      TendstoUniformlyOn (fun k t => ∫ s in (0 : ℝ)..t, f k s) A atTop (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ν.real (Ioc 0 t) = A t) ∧
      TendstoUniformlyOn (fun k t => ∫ s in (0 : ℝ)..t, f k s * w k s)
        (fun t => ∫ s in Ioc 0 t, v s ∂ν) atTop (Icc 0 T) := by
  -- the uniform limit `A` of the primitives
  set P : ℕ → ℝ → ℝ := fun k t => ∫ s in (0 : ℝ)..t, f k s with hP
  set A : ℝ → ℝ := fun t => limUnder atTop (fun k => P k t) with hAdef
  have hlim : ∀ t ∈ Icc 0 T, Tendsto (fun k => P k t) atTop (nhds (A t)) :=
    fun t ht => (hA.cauchySeq ht).tendsto_limUnder
  have hAu : TendstoUniformlyOn P A atTop (Icc 0 T) := hA.tendstoUniformlyOn_of_tendsto hlim
  have hPcont : ∀ k, Continuous (P k) := fun k =>
    intervalIntegral.continuous_primitive (fun a b => (hf k).intervalIntegrable a b) 0
  have hAcont : ContinuousOn A (Icc 0 T) :=
    hAu.continuousOn (Eventually.of_forall fun k => (hPcont k).continuousOn).frequently
  have hAmono : MonotoneOn A (Icc 0 T) := fun x hx y hy hxy =>
    le_of_tendsto_of_tendsto' (hlim x hx) (hlim y hy) fun k =>
      intervalIntegral_le_of_nonneg (hf0 k) (hf k) hxy
  have hA0 : A 0 = 0 := by
    have h := hlim 0 ⟨le_rfl, hT⟩
    simp only [hP, intervalIntegral.integral_same] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  -- the Stieltjes measure of `A` extended constantly outside `[0, T]`
  set F : ℝ → ℝ := fun x => A (projIcc 0 T hT x) with hF
  have hFmono : Monotone F := fun x y hxy =>
    hAmono (projIcc 0 T hT x).2 (projIcc 0 T hT y).2 (monotone_projIcc hT hxy)
  have hFcont : Continuous F :=
    hAcont.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun x => (projIcc 0 T hT x).2
  have hFeq : ∀ t ∈ Icc 0 T, F t = A t := fun t ht => by
    simp only [hF, projIcc_of_mem hT ht]
  let sf : StieltjesFunction ℝ := ⟨F, hFmono, fun x => hFcont.continuousWithinAt⟩
  have hsf : ∀ x, sf x = F x := fun _ => rfl
  have hνfin : IsFiniteMeasure sf.measure := by
    refine sf.isFiniteMeasure_of_forall_abs_le (C := max |A 0| |A T|) fun x => ?_
    rw [hsf]
    exact abs_le_max_abs_abs
      (hAmono ⟨le_rfl, hT⟩ (projIcc 0 T hT x).2 (projIcc 0 T hT x).2.1)
      (hAmono (projIcc 0 T hT x).2 ⟨hT, le_rfl⟩ (projIcc 0 T hT x).2.2)
  have hνA : ∀ t ∈ Icc 0 T, sf.measure.real (Ioc 0 t) = A t := by
    intro t ht
    rw [measureReal_def, sf.measure_Ioc, hsf, hsf, hFeq t ht, hFeq 0 ⟨le_rfl, hT⟩, hA0, sub_zero]
    exact ENNReal.toReal_ofReal (hA0 ▸ hAmono ⟨le_rfl, hT⟩ ht ht.1)
  -- the measures `f k ds` on `(0, T]`
  set μ : ℕ → Measure ℝ := fun k =>
    (volume.restrict (Ioc 0 T)).withDensity (fun s => ((f k s).toNNReal : ENNReal)) with hμ
  have hμfin : ∀ k, IsFiniteMeasure (μ k) := fun k =>
    isFiniteMeasure_withDensity_ofReal
      (((hf k).integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self).hasFiniteIntegral
  have hint : ∀ k (g : ℝ → ℝ), ∀ t ∈ Icc 0 T,
      ∫ s in Ioc 0 t, g s ∂μ k = ∫ s in (0 : ℝ)..t, f k s * g s := by
    intro k g t ht
    have hmeas : Measurable fun s => (f k s).toNNReal :=
      (hf k).measurable.real_toNNReal
    rw [hμ, setIntegral_withDensity_eq_setIntegral_smul hmeas g measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.2 (Ioc_subset_Ioc_right ht.2), intervalIntegral.integral_of_le ht.1]
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hf0 k s), smul_eq_mul]
  have hμA : ∀ k, ∀ t ∈ Icc 0 T, (μ k).real (Ioc 0 t) = P k t := by
    intro k t ht
    have h := hint k (fun _ => 1) t ht
    simp only [setIntegral_const, smul_eq_mul, mul_one] at h
    exact h
  have hμu : TendstoUniformlyOn (fun k t => (μ k).real (Ioc 0 t))
      (fun t => sf.measure.real (Ioc 0 t)) atTop (Icc 0 T) :=
    (hAu.congr (Eventually.of_forall fun k t ht => (hμA k t ht).symm)).congr_right
      fun t ht => (hνA t ht).symm
  have hmain := tendstoUniformlyOn_setIntegral_Ioc_weighted (a := 0) (b := T) hμu hv.continuousOn
    hwv fun k => (hw k).aestronglyMeasurable
  refine ⟨sf.measure, A, hνfin, hAu, hνA, ?_⟩
  exact hmain.congr (Eventually.of_forall fun k t ht => hint k (w k) t ht)

/-- **Weighted primitives are uniformly Cauchy.** If the primitives `t ↦ ∫₀ᵗ f k` of nonnegative
continuous densities are uniformly Cauchy on `[0, T]` and continuous weights `w k` converge
uniformly on `[0, T]` to a continuous `v`, then the weighted primitives `t ↦ ∫₀ᵗ f k * w k` are
uniformly Cauchy on `[0, T]`. -/
theorem uniformCauchySeqOn_intervalIntegral_mul {f w : ℕ → ℝ → ℝ} {v : ℝ → ℝ} {T : ℝ}
    (hf0 : ∀ k s, 0 ≤ f k s) (hf : ∀ k, Continuous (f k))
    (hA : UniformCauchySeqOn (fun k t => ∫ s in (0 : ℝ)..t, f k s) atTop (Icc 0 T))
    (hw : ∀ k, Continuous (w k)) (hv : Continuous v)
    (hwv : TendstoUniformlyOn w v atTop (Icc 0 T)) :
    UniformCauchySeqOn (fun k t => ∫ s in (0 : ℝ)..t, f k s * w k s) atTop (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · intro u _
    exact Eventually.of_forall fun _ x hx => absurd (hx.1.trans hx.2) (not_le.2 hT)
  obtain ⟨ν, A, -, -, -, h⟩ :=
    tendstoUniformlyOn_intervalIntegral_mul_of_uniformCauchySeqOn hT hf0 hf hA hw hv hwv
  exact h.uniformCauchySeqOn

end LatticeProb
