/- The weak limit of a family of real random variables from truncated approximations, by
Prokhorov compactness, for an arbitrary probability space.

The setting this abstracts: a family `X n` on a probability space `(Ω, P)` is approximated, at
each cutoff level `A`, by a family `Y A n` whose law converges for every fixed `A`; the
approximation error is uniformly small in `L¹` as `A → ∞`, and the means of `X` are uniformly
bounded.  Then the laws of `X n` themselves converge weakly, with no continuum object built by
hand: convergence against bounded Lipschitz test functions is stable under a uniform `L¹`
perturbation, so the integrals of those test functions form Cauchy sequences and converge; the
uniform bound on the means makes the laws tight, so Prokhorov's theorem gives a limit point, and
a limit point against which every bounded Lipschitz integral converges is the weak limit.  The
convergence is then read against all bounded continuous test functions
(`exists_weak_limit_of_cutoff`, `exists_weak_limit`).
-/
import Mathlib.MeasureTheory.Measure.Prokhorov

noncomputable section
namespace LatticeProb.WeakLimit
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A uniform bound on `P {|X n| > M}` makes the laws of the `X n` a tight set of measures. -/
theorem tightLaws (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ, ∀ n, P {ω | M < |X n ω|} ≤ ε) :
    IsTightMeasureSet (Set.range (fun n : ℕ => P.map (X n))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨M, hM⟩ := htight ε hε
  refine ⟨Set.Icc (-M) M, isCompact_Icc, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hpre : (X n) ⁻¹' (Set.Icc (-M) M)ᶜ = {ω | M < |X n ω|} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq,
      ← abs_le, not_le]
  rw [Measure.map_apply (hX n) (measurableSet_Icc.compl), hpre]
  exact hM n

/-- **Markov's inequality makes a uniformly bounded family of means tight.** -/
theorem tight_of_integral_abs_le (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hint : ∀ n, Integrable (X n) P) {C : ℝ} (hC : ∀ n, ∫ ω, |X n ω| ∂P ≤ C) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ, ∀ n, P {ω | M < |X n ω|} ≤ ε := by
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨0, fun _ => le_top⟩
  have hC0 : 0 ≤ C := le_trans (integral_nonneg fun ω => abs_nonneg _) (hC 0)
  have hr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  set M : ℝ := C / ε.toReal + 1 with hMdef
  have hM0 : 0 < M := by positivity
  refine ⟨M, fun n => ?_⟩
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun ω => |X n ω|) (Filter.Eventually.of_forall fun ω => abs_nonneg _)
    (hint n).abs M
  have h1 : M * P.real {ω | M ≤ |X n ω|} ≤ C := le_trans hmk (hC n)
  have hdivle : C / M ≤ ε.toReal := by
    rw [div_le_iff₀ hM0, hMdef]
    field_simp
    linarith
  have hle : P.real {ω | M ≤ |X n ω|} ≤ ε.toReal := by
    have h2 : P.real {ω | M ≤ |X n ω|} ≤ C / M := by
      rw [le_div_iff₀ hM0]; linarith
    linarith
  have hsub : {ω | M < |X n ω|} ⊆ {ω | M ≤ |X n ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact le_of_lt hω
  have hfin : P {ω | M ≤ |X n ω|} ≠ ⊤ := measure_ne_top P _
  calc P {ω | M < |X n ω|} ≤ P {ω | M ≤ |X n ω|} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | M ≤ |X n ω|}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal hfin]
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hle
    _ = ε := ENNReal.ofReal_toReal hεtop

/-- **The weak limit from tightness and convergence against bounded Lipschitz functions.**
A tight family whose bounded Lipschitz integrals all converge has a weak limit, and the
convergence then holds against every bounded continuous test function. -/
theorem exists_weak_limit (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ, ∀ n, P {ω | M < |X n ω|} ≤ ε)
    (hcauchy : ∀ f : ℝ → ℝ, (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) → (∃ K, LipschitzWith K f) →
      ∃ c : ℝ, Tendsto (fun n => ∫ ω, f (X n ω) ∂P) atTop (𝓝 c)) :
    ∃ (L : Measure ℝ) (_ : IsProbabilityMeasure L),
      ∀ F : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n => ∫ ω, F (X n ω) ∂P) atTop (𝓝 (∫ x, F x ∂L)) := by
  classical
  set μs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨P.map (X n), Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩ with hμs
  have hmapint : ∀ (n : ℕ) (g : ℝ → ℝ), Continuous g →
      ∫ x, g x ∂(μs n : Measure ℝ) = ∫ ω, g (X n ω) ∂P := by
    intro n g hg
    simpa [hμs] using integral_map (hX n).aemeasurable hg.aestronglyMeasurable
  have hsets : {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range μs}
      = Set.range (fun n : ℕ => P.map (X n)) := by
    ext ν
    constructor
    · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨μs n, ⟨n, rfl⟩, rfl⟩
  have hcomp : IsCompact (closure (Set.range μs)) :=
    isCompact_closure_of_isTightMeasureSet (by rw [hsets]; exact tightLaws P X hX htight)
  have hmem : ∀ n, μs n ∈ closure (Set.range μs) := fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨L, hLmem, hLcl⟩ := hcomp.exists_clusterPt (f := map μs atTop)
    (le_principal_iff.2 (Filter.mem_map.2 (Filter.Eventually.of_forall hmem)))
  have hconv : Tendsto μs atTop (𝓝 L) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro f hfb hflip
    obtain ⟨K, hK⟩ := hflip
    obtain ⟨c, hc⟩ := hcauchy f hfb ⟨K, hK⟩
    let f' : BoundedContinuousFunction ℝ ℝ :=
      { toFun := f, continuous_toFun := hK.continuous, map_bounded' := hfb }
    have hΨ : Continuous fun ν : ProbabilityMeasure ℝ => ∫ x, f' x ∂(ν : Measure ℝ) :=
      ProbabilityMeasure.continuous_integral_boundedContinuousFunction f'
    have hcn : Tendsto (fun n => ∫ x, f x ∂(μs n : Measure ℝ)) atTop (𝓝 c) := by
      refine hc.congr ?_
      intro n
      exact (hmapint n f hK.continuous).symm
    haveI : (𝓝 L ⊓ map μs atTop).NeBot := hLcl
    have h1 : Tendsto (fun ν : ProbabilityMeasure ℝ => ∫ x, f' x ∂(ν : Measure ℝ))
        (𝓝 L ⊓ map μs atTop) (𝓝 (∫ x, f' x ∂(L : Measure ℝ))) :=
      (hΨ.continuousAt).mono_left inf_le_left
    have h2 : Tendsto (fun ν : ProbabilityMeasure ℝ => ∫ x, f' x ∂(ν : Measure ℝ))
        (𝓝 L ⊓ map μs atTop) (𝓝 c) :=
      (tendsto_map' hcn).mono_left inf_le_right
    have hval : ∫ x, f x ∂(L : Measure ℝ) = c := tendsto_nhds_unique h1 h2
    rw [hval]
    exact hcn
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hconv
  refine ⟨(L : Measure ℝ), L.2, fun F => ?_⟩
  exact (hconv F).congr fun n => hmapint n F F.continuous

/-- A sequence uniformly approximated by convergent sequences converges. -/
theorem exists_tendsto_of_uniform_approx (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hv : ∀ A, ∃ c : ℝ, Tendsto (v A) atTop (𝓝 c))
    (hb : Tendsto b atTop (𝓝 0))
    (happ : ∀ A n, |u n - v A n| ≤ b A) :
    ∃ c : ℝ, Tendsto u atTop (𝓝 c) := by
  have hcau : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    have h4 : (0 : ℝ) < δ / 4 := by linarith
    obtain ⟨A, hA⟩ : ∃ A : ℕ, b A < δ / 4 := (hb.eventually (gt_mem_nhds h4)).exists
    obtain ⟨c, hc⟩ := hv A
    have hvc : CauchySeq (v A) := hc.cauchySeq
    rw [Metric.cauchySeq_iff] at hvc
    obtain ⟨N, hN⟩ := hvc (δ / 2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := abs_le.mp (happ A m)
    have h2 := abs_le.mp (happ A n)
    have h3 := hN m hm n hn
    rw [Real.dist_eq] at h3 ⊢
    have h3' := abs_lt.mp h3
    rw [abs_lt]
    constructor <;> linarith
  exact cauchySeq_tendsto_of_complete hcau

/-- A bounded continuous function of a measurable random variable is integrable. -/
theorem integrable_comp_of_bounded (P : Measure Ω) [IsProbabilityMeasure P]
    {f : ℝ → ℝ} (hfc : Continuous f) {C : ℝ} (hb : ∀ x y, dist (f x) (f y) ≤ C)
    {X : Ω → ℝ} (hX : Measurable X) : Integrable (fun ω => f (X ω)) P := by
  refine Integrable.mono' (g := fun _ => C + |f 0|) (integrable_const _)
    (hfc.measurable.comp hX).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have h := hb (X ω) 0
  rw [Real.dist_eq] at h
  have h2 : |f (X ω)| ≤ |f (X ω) - f 0| + |f 0| := by
    calc |f (X ω)| = |(f (X ω) - f 0) + f 0| := by congr 1; ring
      _ ≤ |f (X ω) - f 0| + |f 0| := abs_add_le _ _
  simp only [Real.norm_eq_abs]
  linarith

/-- The means of a bounded Lipschitz test function move by at most the Lipschitz constant
times the `L¹` distance of the arguments. -/
theorem abs_integral_comp_sub_le_of_lipschitz (P : Measure Ω) [IsProbabilityMeasure P]
    {f : ℝ → ℝ} {K : ℝ≥0} (hK : LipschitzWith K f) {C : ℝ} (hb : ∀ x y, dist (f x) (f y) ≤ C)
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X P) (hYi : Integrable Y P) :
    |∫ ω, f (X ω) ∂P - ∫ ω, f (Y ω) ∂P| ≤ (K : ℝ) * ∫ ω, |X ω - Y ω| ∂P := by
  have hfX := integrable_comp_of_bounded P hK.continuous hb hX
  have hfY := integrable_comp_of_bounded P hK.continuous hb hY
  have hd : Integrable (fun ω => |X ω - Y ω|) P := (hXi.sub hYi).abs
  have hbound : ∀ ω, |f (X ω) - f (Y ω)| ≤ (K : ℝ) * |X ω - Y ω| := by
    intro ω
    have := hK.dist_le_mul (X ω) (Y ω)
    rwa [Real.dist_eq, Real.dist_eq] at this
  have habs : Integrable (fun ω => |f (X ω) - f (Y ω)|) P := (hfX.sub hfY).abs
  calc |∫ ω, f (X ω) ∂P - ∫ ω, f (Y ω) ∂P|
      = |∫ ω, (f (X ω) - f (Y ω)) ∂P| := by rw [integral_sub hfX hfY]
    _ ≤ ∫ ω, |f (X ω) - f (Y ω)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (K : ℝ) * |X ω - Y ω| ∂P :=
        integral_mono habs (hd.const_mul _) hbound
    _ = (K : ℝ) * ∫ ω, |X ω - Y ω| ∂P := integral_const_mul _ _

/-- **The removal of the spatial cutoff.**  If at every cutoff level the truncated variables
converge in law, the truncation error is uniformly small in `L¹` as the level grows, and the
means are uniformly bounded, then the laws of the untruncated variables converge weakly. -/
theorem exists_weak_limit_of_cutoff (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ A n, Measurable (Y A n))
    (hXi : ∀ n, Integrable (X n) P) (hYi : ∀ A n, Integrable (Y A n) P)
    {C : ℝ} (hC : ∀ n, ∫ ω, |X n ω| ∂P ≤ C)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (happ : ∀ A n, ∫ ω, |X n ω - Y A n ω| ∂P ≤ e A)
    (hYconv : ∀ A : ℕ, ∀ f : ℝ → ℝ, (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) →
      (∃ K, LipschitzWith K f) →
      ∃ c : ℝ, Tendsto (fun n => ∫ ω, f (Y A n ω) ∂P) atTop (𝓝 c)) :
    ∃ (L : Measure ℝ) (_ : IsProbabilityMeasure L),
      ∀ F : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n => ∫ ω, F (X n ω) ∂P) atTop (𝓝 (∫ x, F x ∂L)) := by
  refine exists_weak_limit P X hX (tight_of_integral_abs_le P X hXi hC) ?_
  rintro f ⟨Cf, hCf⟩ ⟨K, hK⟩
  refine exists_tendsto_of_uniform_approx (fun n => ∫ ω, f (X n ω) ∂P)
    (fun A n => ∫ ω, f (Y A n ω) ∂P) (fun A => (K : ℝ) * e A)
    (fun A => hYconv A f ⟨Cf, hCf⟩ ⟨K, hK⟩) (by simpa using he.const_mul (K : ℝ)) ?_
  intro A n
  refine le_trans (abs_integral_comp_sub_le_of_lipschitz P hK hCf (hX n) (hY A n)
    (hXi n) (hYi A n)) (mul_le_mul_of_nonneg_left (happ A n) K.coe_nonneg)

end LatticeProb.WeakLimit
end
