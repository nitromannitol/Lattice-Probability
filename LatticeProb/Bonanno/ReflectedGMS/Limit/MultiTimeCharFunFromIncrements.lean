/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.MultiTimeCharFunFromIncrements at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ConditionalGaussianIdentification
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Multi-time characteristic-function limits from one-increment conditional limits

The finite-dimensional characteristic function of a sequence of processes at a finite
family of times and directions,

  `∫ exp (i ∑ⱼ ⟪θⱼ, Xₖ(uⱼ)⟫) dP`,

converges to the Gaussian value `exp (-(∑ᵢⱼ B(θᵢ,θⱼ)(uᵢ ∧ uⱼ))/2)` as soon as

* the processes start at `0` in the limit (`hzero`), and
* the conditional characteristic function of **one** increment given the past converges
  in `L¹` to the Gaussian factor `exp (-B(η,η)(t-s)/2)` (`hinc`).

Everything happens on **one fixed sample space with filtrations**, where the project's
Lindeberg / characteristic-function chain lives; no path space, no weak convergence and no
limit law appears.  The argument is the classical peeling of the last increment:

* sort the times (`Tuple.sort`), prepend the time `0`, and extend the grid to `ℕ`
  (`clampExt`), so that the functional is `gridSum θ v X n`;
* write `gridSum θ v X (m+2) = gridSum θ' v X (m+1) + ⟪θ_{m+1}, X(v_{m+1}) - X(v_m)⟫` with
  the direction `θ_{m+1}` folded into `θ' = update θ m (θ_m + θ_{m+1})`
  (`gridSum_succ_succ`), and the matching identity for the quadratic form
  (`gridQuad_succ_succ`);
* the past factor `exp (i gridSum θ' …)` is bounded by `1` and measurable at time `v_m`, so
  `ConditionalGaussianIdentification.norm_integral_mul_sub_mul_le_integralNorm` bounds the
  error by (the error of the past factor) + (the `L¹` error of the conditional
  characteristic function of the last increment); induction on the number of times closes.

Also provided: the comparison lemma `tendsto_integral_cexp_sub_of_tendstoInMeasure` —
two exponential integrals have the same limit when the phases differ by a quantity tending
to `0` in probability — and the small `TendstoInMeasure` toolkit it needs.

CONDITIONAL: nothing about the reflected walk is proved here; the increment limit is an
input.  Nothing conclusion-shaped (no fdd convergence of laws, no tightness, no scaling
limit) is assumed anywhere.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ReflectedGMS.MultiTimeCharFun

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Elementary bounds -/

/-- `|e^{ia} - e^{ib}| ≤ min 2 |a - b|`. -/
theorem norm_cexp_sub_cexp_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖
      ≤ min 2 |a - b| := by
  have hfac : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((b : ℂ) * Complex.I)
        * (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine le_min ?_ ?_
  · calc ‖Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ ‖Complex.exp (((a - b : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  · have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
    rw [mul_comm] at h
    simpa [Real.norm_eq_abs] using h

/-- The unit-modulus exponential of a measurable real phase is integrable. -/
theorem integrable_cexp_ofReal_mul_I [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) :
    Integrable (fun ω => Complex.exp ((f ω : ℂ) * Complex.I)) P :=
  Integrable.of_bound
    (Complex.continuous_exp.comp_stronglyMeasurable
      ((Complex.continuous_ofReal.comp_stronglyMeasurable hf.stronglyMeasurable).mul_const
        Complex.I)).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by rw [Complex.norm_exp_ofReal_mul_I])

/-! ## Convergence in probability: a small toolkit -/

/-- A sequence dominated almost surely by a deterministic null sequence tends to `0` in
probability. -/
theorem tendstoInMeasure_zero_of_ae_norm_le {F : Type*} [NormedAddCommGroup F]
    {f : ℕ → Ω → F} {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hf : ∀ k, ∀ᵐ ω ∂P, ‖f k ω‖ ≤ c k) :
    TendstoInMeasure P f atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro δ hδ
  simp only [Pi.zero_apply, sub_zero]
  have hev : ∀ᶠ k in atTop, P {ω | δ ≤ ‖f k ω‖} = 0 := by
    filter_upwards [hc.eventually (gt_mem_nhds hδ)] with k hk
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hf k] with ω hω
    exact not_le.2 (lt_of_le_of_lt hω hk)
  exact tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm)

/-- Domination by a constant multiple of a sequence tending to `0` in probability. -/
theorem tendstoInMeasure_zero_of_norm_le {F G : Type*} [NormedAddCommGroup F]
    [NormedAddCommGroup G] {f : ℕ → Ω → F} {g : ℕ → Ω → G} {c : ℝ} (hc : 0 ≤ c)
    (hfg : ∀ k ω, ‖f k ω‖ ≤ c * ‖g k ω‖) (hg : TendstoInMeasure P g atTop 0) :
    TendstoInMeasure P f atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hg ⊢
  intro δ hδ
  simp only [Pi.zero_apply, sub_zero] at hg ⊢
  have hδ' : 0 < δ / (c + 1) := by positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg _ hδ')
    (fun k => zero_le) (fun k => measure_mono ?_)
  intro ω hω
  have hω' : δ ≤ ‖f k ω‖ := hω
  show δ / (c + 1) ≤ ‖g k ω‖
  have h1 : δ ≤ c * ‖g k ω‖ := le_trans hω' (hfg k ω)
  have h2 : c * ‖g k ω‖ ≤ (c + 1) * ‖g k ω‖ := by nlinarith [norm_nonneg (g k ω)]
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- The sum of two sequences tending to `0` in probability tends to `0` in probability. -/
theorem tendstoInMeasure_zero_add {F : Type*} [NormedAddCommGroup F] {f g : ℕ → Ω → F}
    (hf : TendstoInMeasure P f atTop 0) (hg : TendstoInMeasure P g atTop 0) :
    TendstoInMeasure P (fun k ω => f k ω + g k ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro δ hδ
  simp only [Pi.zero_apply, sub_zero] at hf hg ⊢
  have hδ' : 0 < δ / 2 := by positivity
  have hlim : Tendsto (fun k => P {ω | δ / 2 ≤ ‖f k ω‖} + P {ω | δ / 2 ≤ ‖g k ω‖}) atTop
      (𝓝 0) := by
    simpa using (hf _ hδ').add (hg _ hδ')
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun k => zero_le) (fun k => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  have hω' : δ ≤ ‖f k ω + g k ω‖ := hω
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h1' : ¬ (δ / 2 ≤ ‖f k ω‖) := h1
  have h2' : ¬ (δ / 2 ≤ ‖g k ω‖) := h2
  have h1'' := not_le.1 h1'
  have h2'' := not_le.1 h2'
  linarith [norm_add_le (f k ω) (g k ω)]

/-- A finite sum of sequences tending to `0` in probability tends to `0` in probability. -/
theorem tendstoInMeasure_zero_finset_sum {F : Type*} [NormedAddCommGroup F] {ι : Type*}
    (s : Finset ι) {f : ι → ℕ → Ω → F}
    (h : ∀ i ∈ s, TendstoInMeasure P (f i) atTop 0) :
    TendstoInMeasure P (fun k ω => ∑ i ∈ s, f i k ω) atTop 0 := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => ?_) (fun a s ha ih h => ?_)
  · simp only [Finset.sum_empty]
    exact tendstoInMeasure_zero_of_ae_norm_le (c := fun _ => 0) tendsto_const_nhds
      (fun k => Eventually.of_forall fun ω => by simp)
  · simp only [Finset.sum_insert ha]
    exact tendstoInMeasure_zero_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## The comparison lemma -/

/-- **Two exponential integrals have the same limit when the phases differ by a quantity
tending to `0` in probability.** -/
theorem tendsto_integral_cexp_sub_of_tendstoInMeasure [IsProbabilityMeasure P]
    {a b : ℕ → Ω → ℝ} (ha : ∀ k, Measurable (a k)) (hb : ∀ k, Measurable (b k))
    (h : TendstoInMeasure P (fun k ω => a k ω - b k ω) atTop 0) :
    Tendsto (fun k => (∫ ω, Complex.exp ((a k ω : ℂ) * Complex.I) ∂P)
      - ∫ ω, Complex.exp ((b k ω : ℂ) * Complex.I) ∂P) atTop (𝓝 0) := by
  have hbound : ∀ (k : ℕ) (δ : ℝ), 0 < δ →
      ‖(∫ ω, Complex.exp ((a k ω : ℂ) * Complex.I) ∂P)
          - ∫ ω, Complex.exp ((b k ω : ℂ) * Complex.I) ∂P‖
        ≤ 2 * P.real {ω | δ ≤ ‖a k ω - b k ω‖} + δ := by
    intro k δ hδ
    have hS : MeasurableSet {ω | δ ≤ ‖a k ω - b k ω‖} :=
      measurableSet_le measurable_const ((ha k).sub (hb k)).norm
    rw [← integral_sub (integrable_cexp_ofReal_mul_I (ha k))
      (integrable_cexp_ofReal_mul_I (hb k))]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ ω, ‖Complex.exp ((a k ω : ℂ) * Complex.I)
          - Complex.exp ((b k ω : ℂ) * Complex.I)‖
        ≤ {ω | δ ≤ ‖a k ω - b k ω‖}.indicator (fun _ => (2 : ℝ)) ω + δ := by
      intro ω
      refine (norm_cexp_sub_cexp_le _ _).trans ?_
      by_cases hω : δ ≤ ‖a k ω - b k ω‖
      · have hmem : ω ∈ {ω | δ ≤ ‖a k ω - b k ω‖} := hω
        rw [Set.indicator_of_mem hmem]
        linarith [min_le_left (2 : ℝ) |a k ω - b k ω|]
      · have hnot : ω ∉ {ω | δ ≤ ‖a k ω - b k ω‖} := hω
        rw [Set.indicator_of_notMem hnot, zero_add]
        push_neg at hω
        rw [Real.norm_eq_abs] at hω
        linarith [min_le_right (2 : ℝ) |a k ω - b k ω|]
    have hint : Integrable
        (fun ω => {ω | δ ≤ ‖a k ω - b k ω‖}.indicator (fun _ => (2 : ℝ)) ω + δ) P :=
      ((integrable_const (2 : ℝ)).indicator hS).add (integrable_const δ)
    calc ∫ ω, ‖Complex.exp ((a k ω : ℂ) * Complex.I)
            - Complex.exp ((b k ω : ℂ) * Complex.I)‖ ∂P
        ≤ ∫ ω, ({ω | δ ≤ ‖a k ω - b k ω‖}.indicator (fun _ => (2 : ℝ)) ω + δ) ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) hint
            (Eventually.of_forall hpt)
      _ = 2 * P.real {ω | δ ≤ ‖a k ω - b k ω‖} + δ := by
          rw [integral_add ((integrable_const (2 : ℝ)).indicator hS) (integrable_const δ),
            integral_indicator_const _ hS, integral_const]
          simp [smul_eq_mul, mul_comm]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  refine tendsto_order.2 ⟨fun c hc => Eventually.of_forall fun k =>
    lt_of_lt_of_le hc (norm_nonneg _), fun c hc => ?_⟩
  have hδ : 0 < c / 4 := by positivity
  have hmeas := (tendstoInMeasure_iff_measureReal_norm.mp h) (c / 4) hδ
  simp only [Pi.zero_apply, sub_zero] at hmeas
  filter_upwards [hmeas.eventually (gt_mem_nhds hδ)] with k hk
  calc ‖(∫ ω, Complex.exp ((a k ω : ℂ) * Complex.I) ∂P)
        - ∫ ω, Complex.exp ((b k ω : ℂ) * Complex.I) ∂P‖
      ≤ 2 * P.real {ω | c / 4 ≤ ‖a k ω - b k ω‖} + c / 4 := hbound k (c / 4) hδ
    _ < 2 * (c / 4) + c / 4 := by linarith
    _ < c := by linarith

/-! ## Grid functionals -/

/-- The multi-time linear functional `∑_{i<n} ⟪θ i, X (v i)⟫` of a process along a grid. -/
noncomputable def gridSum (θ : ℕ → E) (v : ℕ → ℝ≥0) (X : ℝ≥0 → Ω → E) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, ⟪θ i, X (v i) ω⟫_ℝ

/-- The Gaussian quadratic form `∑_{i,j<n} B(θ i, θ j) (v i ∧ v j)` of a grid. -/
noncomputable def gridQuad (B : E → E → ℝ) (θ : ℕ → E) (v : ℕ → ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    B (θ i) (θ j) * ((min (v i) (v j) : ℝ≥0) : ℝ)

/-- The Gaussian factor `exp (-B(η,η)(t-s)/2)` of one increment, as a complex number. -/
noncomputable def gaussFactor (B : E → E → ℝ) (η : E) (s t : ℝ≥0) : ℂ :=
  ((Real.exp (-(B η η * ((t : ℝ) - (s : ℝ)) / 2)) : ℝ) : ℂ)

theorem norm_gaussFactor_le_one (B : E → E → ℝ) (hBnn : ∀ a, 0 ≤ B a a) (η : E)
    {s t : ℝ≥0} (hst : s ≤ t) : ‖gaussFactor B η s t‖ ≤ 1 := by
  rw [gaussFactor, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_one_iff.2 ?_
  have : (0 : ℝ) ≤ B η η * ((t : ℝ) - (s : ℝ)) :=
    mul_nonneg (hBnn η) (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))
  linarith

/-- Peeling the last time of the quadratic form. -/
theorem gridQuad_succ (B : E → E → ℝ) (hBsymm : ∀ a b, B a b = B b a) (θ : ℕ → E)
    (v : ℕ → ℝ≥0) (n : ℕ) :
    gridQuad B θ v (n + 1)
      = gridQuad B θ v n
        + 2 * (∑ i ∈ Finset.range n, B (θ i) (θ n) * ((min (v i) (v n) : ℝ≥0) : ℝ))
        + B (θ n) (θ n) * ((min (v n) (v n) : ℝ≥0) : ℝ) := by
  simp only [gridQuad, Finset.sum_range_succ, Finset.sum_add_distrib]
  have hsw : ∑ j ∈ Finset.range n, B (θ n) (θ j) * ((min (v n) (v j) : ℝ≥0) : ℝ)
      = ∑ i ∈ Finset.range n, B (θ i) (θ n) * ((min (v i) (v n) : ℝ≥0) : ℝ) :=
    Finset.sum_congr rfl fun i _ => by rw [hBsymm, min_comm]
  rw [hsw]
  ring

/-- Updating a direction beyond the grid does not change the quadratic form. -/
theorem gridQuad_update_of_le (B : E → E → ℝ) (θ : ℕ → E) (v : ℕ → ℝ≥0) {m n : ℕ}
    (hnm : n ≤ m) (x : E) :
    gridQuad B (Function.update θ m x) v n = gridQuad B θ v n := by
  unfold gridQuad
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (ne_of_lt (lt_of_lt_of_le (Finset.mem_range.1 hi) hnm)),
    Function.update_of_ne (ne_of_lt (lt_of_lt_of_le (Finset.mem_range.1 hj) hnm))]

/-- **Peeling the last increment of the linear functional.** -/
theorem gridSum_succ_succ (θ : ℕ → E) (v : ℕ → ℝ≥0) (X : ℝ≥0 → Ω → E) (m : ℕ) (ω : Ω)
    (θ' : ℕ → E) (hθ' : θ' = Function.update θ m (θ m + θ (m + 1))) :
    gridSum θ v X (m + 1 + 1) ω
      = gridSum θ' v X (m + 1) ω + ⟪θ (m + 1), X (v (m + 1)) ω - X (v m) ω⟫_ℝ := by
  have h1 : ∑ i ∈ Finset.range m, ⟪θ' i, X (v i) ω⟫_ℝ
      = ∑ i ∈ Finset.range m, ⟪θ i, X (v i) ω⟫_ℝ :=
    Finset.sum_congr rfl fun i hi => by
      rw [hθ', Function.update_of_ne (ne_of_lt (Finset.mem_range.1 hi))]
  have h2 : θ' m = θ m + θ (m + 1) := by rw [hθ', Function.update_self]
  simp only [gridSum, Finset.sum_range_succ, h1, h2, inner_add_left, inner_sub_right]
  ring

/-- **Peeling the last increment of the quadratic form.** -/
theorem gridQuad_succ_succ (B : E → E → ℝ) (hBadd : ∀ a b c, B (a + b) c = B a c + B b c)
    (hBsymm : ∀ a b, B a b = B b a) (θ : ℕ → E) (v : ℕ → ℝ≥0) (hv : Monotone v) (m : ℕ)
    (θ' : ℕ → E) (hθ' : θ' = Function.update θ m (θ m + θ (m + 1))) :
    gridQuad B θ v (m + 1 + 1)
      = gridQuad B θ' v (m + 1)
        + B (θ (m + 1)) (θ (m + 1)) * ((v (m + 1) : ℝ) - (v m : ℝ)) := by
  have hBadd' : ∀ a b c, B a (b + c) = B a b + B a c := fun a b c => by
    rw [hBsymm, hBadd, hBsymm b a, hBsymm c a]
  have hθ'm : θ' m = θ m + θ (m + 1) := by rw [hθ', Function.update_self]
  have hθ'i : ∀ i ∈ Finset.range m, θ' i = θ i := fun i hi => by
    rw [hθ', Function.update_of_ne (ne_of_lt (Finset.mem_range.1 hi))]
  have hquad' : gridQuad B θ' v m = gridQuad B θ v m := by
    rw [hθ']
    exact gridQuad_update_of_le B θ v le_rfl _
  rw [gridQuad_succ B hBsymm θ v (m + 1), gridQuad_succ B hBsymm θ v m,
    gridQuad_succ B hBsymm θ' v m, hquad', Finset.sum_range_succ]
  have hmm : min (v m) (v m) = v m := min_self _
  have hm1 : min (v (m + 1)) (v (m + 1)) = v (m + 1) := min_self _
  have hmm1 : min (v m) (v (m + 1)) = v m := min_eq_left (hv (Nat.le_succ m))
  have hsum1 : ∑ i ∈ Finset.range m, B (θ i) (θ (m + 1)) * ((min (v i) (v (m + 1)) : ℝ≥0) : ℝ)
      = ∑ i ∈ Finset.range m, B (θ i) (θ (m + 1)) * ((min (v i) (v m) : ℝ≥0) : ℝ) :=
    Finset.sum_congr rfl fun i hi => by
      have hi' : i ≤ m := le_of_lt (Finset.mem_range.1 hi)
      rw [min_eq_left (hv (hi'.trans (Nat.le_succ m))), min_eq_left (hv hi')]
  have hsum2 : ∑ i ∈ Finset.range m, B (θ' i) (θ' m) * ((min (v i) (v m) : ℝ≥0) : ℝ)
      = ∑ i ∈ Finset.range m, B (θ i) (θ m) * ((min (v i) (v m) : ℝ≥0) : ℝ)
        + ∑ i ∈ Finset.range m, B (θ i) (θ (m + 1)) * ((min (v i) (v m) : ℝ≥0) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hθ'i i hi, hθ'm, hBadd', add_mul]
  rw [hsum1, hsum2, hθ'm, hmm, hm1, hmm1, hBadd, hBadd', hBadd', hBsymm (θ (m + 1)) (θ m)]
  ring

/-! ## The multi-time limit from one-increment limits -/

/-- **Multi-time characteristic-function limits along a grid, from the one-increment
conditional limits.**  The grid `v` is monotone with `v 0 = 0`; the hypotheses are the
convergence `X k 0 → 0` in law (`hzero`) and the `L¹` convergence of the conditional
characteristic function of every increment given the past to the Gaussian factor
(`hinc`).  Nothing else. -/
theorem tendsto_integral_cexp_gridSum [IsProbabilityMeasure P]
    (𝔽 : ℕ → Filtration ℝ≥0 mΩ) (X : ℕ → ℝ≥0 → Ω → E)
    (hadapt : ∀ k t, StronglyMeasurable[𝔽 k t] (X k t))
    (B : E → E → ℝ) (hBadd : ∀ a b c, B (a + b) c = B a c + B b c)
    (hBsymm : ∀ a b, B a b = B b a) (hBnn : ∀ a, 0 ≤ B a a)
    (v : ℕ → ℝ≥0) (hv : Monotone v) (hv0 : v 0 = 0)
    (hzero : ∀ θ : E, Tendsto
      (fun k => ∫ ω, Complex.exp ((⟪θ, X k 0 ω⟫_ℝ : ℂ) * Complex.I) ∂P) atTop (𝓝 1))
    (hinc : ∀ (η : E) (s t : ℝ≥0), s ≤ t →
      Tendsto (fun k => ∫ ω, ‖(P[fun ω => Complex.exp
          ((⟪η, X k t ω - X k s ω⟫_ℝ : ℂ) * Complex.I) | 𝔽 k s]) ω
            - gaussFactor B η s t‖ ∂P) atTop (𝓝 0))
    (n : ℕ) (θ : ℕ → E) :
    Tendsto (fun k => ∫ ω, Complex.exp ((gridSum θ v (X k) n ω : ℂ) * Complex.I) ∂P) atTop
      (𝓝 (((Real.exp (-(gridQuad B θ v n) / 2)) : ℝ) : ℂ)) := by
  induction n generalizing θ with
  | zero =>
    simp only [gridSum, gridQuad, Finset.sum_range_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, integral_const, probReal_univ, one_smul, neg_zero, zero_div,
      Real.exp_zero, Complex.ofReal_one]
    exact tendsto_const_nhds
  | succ n ih =>
    cases n with
    | zero =>
      have hs : ∀ k ω, gridSum θ v (X k) 1 ω = ⟪θ 0, X k 0 ω⟫_ℝ := fun k ω => by
        simp [gridSum, hv0]
      have hq : gridQuad B θ v 1 = 0 := by simp [gridQuad, hv0]
      simp only [hs, hq, neg_zero, zero_div, Real.exp_zero, Complex.ofReal_one]
      exact hzero (θ 0)
    | succ m =>
      obtain ⟨θ', hθ'⟩ : ∃ θ' : ℕ → E, θ' = Function.update θ m (θ m + θ (m + 1)) :=
        ⟨_, rfl⟩
      have hstep := hinc (θ (m + 1)) (v m) (v (m + 1)) (hv (Nat.le_succ m))
      have hih := ih θ'
      have hV : ∀ k, StronglyMeasurable[𝔽 k (v m)]
          (fun ω => Complex.exp ((gridSum θ' v (X k) (m + 1) ω : ℂ) * Complex.I)) := by
        intro k
        have hsum : StronglyMeasurable[𝔽 k (v m)] (fun ω => gridSum θ' v (X k) (m + 1) ω) :=
          Finset.stronglyMeasurable_fun_sum (Finset.range (m + 1)) fun i hi =>
            stronglyMeasurable_const.inner ((hadapt k (v i)).mono
              ((𝔽 k).mono (hv (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))))
        exact Complex.continuous_exp.comp_stronglyMeasurable
          ((Complex.continuous_ofReal.comp_stronglyMeasurable hsum).mul_const Complex.I)
      have hVbdd : ∀ k ω,
          ‖Complex.exp ((gridSum θ' v (X k) (m + 1) ω : ℂ) * Complex.I)‖ ≤ 1 :=
        fun k ω => by rw [Complex.norm_exp_ofReal_mul_I]
      have hg : ∀ k, Integrable (fun ω => Complex.exp
          ((⟪θ (m + 1), X k (v (m + 1)) ω - X k (v m) ω⟫_ℝ : ℂ) * Complex.I)) P := by
        intro k
        refine integrable_cexp_ofReal_mul_I ?_
        exact (stronglyMeasurable_const.inner
          (((hadapt k _).mono ((𝔽 k).le _)).sub ((hadapt k _).mono ((𝔽 k).le _)))).measurable
      have hb : ‖gaussFactor B (θ (m + 1)) (v m) (v (m + 1))‖ ≤ 1 :=
        norm_gaussFactor_le_one B hBnn _ (hv (Nat.le_succ m))
      have hprod : ∀ k,
          (∫ ω, Complex.exp ((gridSum θ v (X k) (m + 1 + 1) ω : ℂ) * Complex.I) ∂P)
            = ∫ ω, Complex.exp ((gridSum θ' v (X k) (m + 1) ω : ℂ) * Complex.I)
                * Complex.exp
                  ((⟪θ (m + 1), X k (v (m + 1)) ω - X k (v m) ω⟫_ℝ : ℂ) * Complex.I) ∂P := by
        intro k
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        dsimp only
        rw [gridSum_succ_succ θ v (X k) m ω θ' hθ', ← Complex.exp_add]
        congr 1
        push_cast
        ring
      have hr : Tendsto (fun k => ‖(∫ ω, Complex.exp
          ((gridSum θ' v (X k) (m + 1) ω : ℂ) * Complex.I) ∂P)
            - (((Real.exp (-(gridQuad B θ' v (m + 1)) / 2)) : ℝ) : ℂ)‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.1 hih
      have hbound : ∀ k,
          ‖(∫ ω, Complex.exp ((gridSum θ v (X k) (m + 1 + 1) ω : ℂ) * Complex.I) ∂P)
              - (((Real.exp (-(gridQuad B θ' v (m + 1)) / 2)) : ℝ) : ℂ)
                * gaussFactor B (θ (m + 1)) (v m) (v (m + 1))‖
            ≤ ‖(∫ ω, Complex.exp ((gridSum θ' v (X k) (m + 1) ω : ℂ) * Complex.I) ∂P)
                - (((Real.exp (-(gridQuad B θ' v (m + 1)) / 2)) : ℝ) : ℂ)‖
              + ∫ ω, ‖(P[fun ω => Complex.exp
                  ((⟪θ (m + 1), X k (v (m + 1)) ω - X k (v m) ω⟫_ℝ : ℂ) * Complex.I)
                    | 𝔽 k (v m)]) ω
                  - gaussFactor B (θ (m + 1)) (v m) (v (m + 1))‖ ∂P := by
        intro k
        rw [hprod k]
        exact ReflectedGMS.MartingaleLimit.norm_integral_mul_sub_mul_le_integralNorm
          ⟨𝔽 k (v m), (𝔽 k).le _⟩ (hV k) (hVbdd k) (hg k) hb le_rfl le_rfl
      have hlim : Tendsto
          (fun k => ∫ ω, Complex.exp ((gridSum θ v (X k) (m + 1 + 1) ω : ℂ) * Complex.I) ∂P)
          atTop (𝓝 ((((Real.exp (-(gridQuad B θ' v (m + 1)) / 2)) : ℝ) : ℂ)
            * gaussFactor B (θ (m + 1)) (v m) (v (m + 1)))) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
        simpa using hr.add hstep
      have hcb : (((Real.exp (-(gridQuad B θ' v (m + 1)) / 2)) : ℝ) : ℂ)
          * gaussFactor B (θ (m + 1)) (v m) (v (m + 1))
            = (((Real.exp (-(gridQuad B θ v (m + 1 + 1)) / 2)) : ℝ) : ℂ) := by
        rw [gridQuad_succ_succ B hBadd hBsymm θ v hv m θ' hθ', gaussFactor,
          ← Complex.ofReal_mul, ← Real.exp_add]
        congr 2
        ring
      rw [← hcb]
      exact hlim

/-! ## From an arbitrary finite family of times to a grid -/

/-- The clamped extension of a `Fin (n+1)`-indexed family to `ℕ`. -/
def clampExt {α : Type*} {n : ℕ} (w : Fin (n + 1) → α) (i : ℕ) : α :=
  w ⟨min i n, Nat.lt_succ_of_le (min_le_right i n)⟩

theorem clampExt_apply_fin {α : Type*} {n : ℕ} (w : Fin (n + 1) → α) (i : Fin (n + 1)) :
    clampExt w (i : ℕ) = w i := by
  unfold clampExt
  congr 1
  exact Fin.ext (min_eq_left (Nat.lt_succ_iff.1 i.isLt))

theorem clampExt_zero {α : Type*} {n : ℕ} (w : Fin (n + 1) → α) : clampExt w 0 = w 0 := by
  have := clampExt_apply_fin w 0
  simpa using this

theorem monotone_clampExt {n : ℕ} {w : Fin (n + 1) → ℝ≥0} (hw : Monotone w) :
    Monotone (clampExt w) :=
  fun a b hab => hw (Fin.mk_le_mk.2 (min_le_min_right n hab))

/-- Prepending `0` to a monotone family keeps it monotone. -/
theorem monotone_cons_zero {n : ℕ} (u : Fin n → ℝ≥0) (hu : Monotone u) :
    Monotone (Fin.cons (0 : ℝ≥0) u : Fin (n + 1) → ℝ≥0) := by
  rw [Fin.monotone_iff_le_succ]
  rintro ⟨i, hi⟩
  cases i with
  | zero =>
    have h0 : (Fin.castSucc (⟨0, hi⟩ : Fin n) : Fin (n + 1)) = 0 := Fin.ext (by simp)
    rw [h0, Fin.cons_zero]
    exact zero_le
  | succ j =>
    have hj : j < n := Nat.lt_of_succ_lt hi
    have e1 : (Fin.castSucc (⟨j + 1, hi⟩ : Fin n) : Fin (n + 1)) = Fin.succ ⟨j, hj⟩ :=
      Fin.ext rfl
    have e2 : (⟨j + 1, hi⟩ : Fin n).succ = Fin.succ ⟨j + 1, hi⟩ := rfl
    rw [e1, e2, Fin.cons_succ, Fin.cons_succ]
    exact hu (Fin.mk_le_mk.2 (Nat.le_succ j))

/-- **Multi-time characteristic-function limits at an arbitrary finite family of times and
directions**, from the one-increment conditional limits.  The times are sorted with
`Tuple.sort`, the time `0` is prepended and the grid is extended to `ℕ`. -/
theorem tendsto_integral_cexp_finSum [IsProbabilityMeasure P]
    (𝔽 : ℕ → Filtration ℝ≥0 mΩ) (X : ℕ → ℝ≥0 → Ω → E)
    (hadapt : ∀ k t, StronglyMeasurable[𝔽 k t] (X k t))
    (B : E → E → ℝ) (hBadd : ∀ a b c, B (a + b) c = B a c + B b c)
    (hBsymm : ∀ a b, B a b = B b a) (hBnn : ∀ a, 0 ≤ B a a)
    (hzero : ∀ θ : E, Tendsto
      (fun k => ∫ ω, Complex.exp ((⟪θ, X k 0 ω⟫_ℝ : ℂ) * Complex.I) ∂P) atTop (𝓝 1))
    (hinc : ∀ (η : E) (s t : ℝ≥0), s ≤ t →
      Tendsto (fun k => ∫ ω, ‖(P[fun ω => Complex.exp
          ((⟪η, X k t ω - X k s ω⟫_ℝ : ℂ) * Complex.I) | 𝔽 k s]) ω
            - gaussFactor B η s t‖ ∂P) atTop (𝓝 0))
    (n : ℕ) (u : Fin n → ℝ≥0) (θ : Fin n → E) :
    Tendsto (fun k => ∫ ω, Complex.exp
        (((∑ i, ⟪θ i, X k (u i) ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂P)
      atTop (𝓝 (((Real.exp (-(∑ i, ∑ j, B (θ i) (θ j) * ((min (u i) (u j) : ℝ≥0) : ℝ)) / 2))
        : ℝ) : ℂ)) := by
  classical
  have hmono : Monotone (u ∘ Tuple.sort u) := Tuple.monotone_sort u
  have hw : Monotone (Fin.cons (0 : ℝ≥0) (u ∘ Tuple.sort u) : Fin (n + 1) → ℝ≥0) :=
    monotone_cons_zero _ hmono
  have hv : Monotone (clampExt (Fin.cons (0 : ℝ≥0) (u ∘ Tuple.sort u))) := monotone_clampExt hw
  have hv0 : clampExt (Fin.cons (0 : ℝ≥0) (u ∘ Tuple.sort u)) 0 = 0 := by
    rw [clampExt_zero, Fin.cons_zero]
  have hmain := tendsto_integral_cexp_gridSum 𝔽 X hadapt B hBadd hBsymm hBnn _ hv hv0 hzero hinc
    (n + 1) (clampExt (Fin.cons (0 : E) (θ ∘ Tuple.sort u)))
  have hz1 : ∀ a : ℝ≥0, min a 0 = 0 := fun a => min_eq_right zero_le
  have hz2 : ∀ a : ℝ≥0, min 0 a = 0 := fun a => min_eq_left zero_le
  have hS : ∀ k ω, gridSum (clampExt (Fin.cons (0 : E) (θ ∘ Tuple.sort u)))
      (clampExt (Fin.cons (0 : ℝ≥0) (u ∘ Tuple.sort u))) (X k) (n + 1) ω
        = ∑ i, ⟪θ i, X k (u i) ω⟫_ℝ := by
    intro k ω
    simp only [gridSum]
    rw [Finset.sum_range]
    simp only [clampExt_apply_fin, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Function.comp_apply, inner_zero_left, zero_add]
    exact Fintype.sum_equiv (Tuple.sort u) _ _ (fun _ => rfl)
  have hQ : gridQuad B (clampExt (Fin.cons (0 : E) (θ ∘ Tuple.sort u)))
      (clampExt (Fin.cons (0 : ℝ≥0) (u ∘ Tuple.sort u))) (n + 1)
        = ∑ i, ∑ j, B (θ i) (θ j) * ((min (u i) (u j) : ℝ≥0) : ℝ) := by
    simp only [gridQuad]
    simp only [Finset.sum_range]
    simp only [clampExt_apply_fin, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Function.comp_apply, hz1, hz2, NNReal.coe_zero, mul_zero, Finset.sum_const_zero,
      zero_add, add_zero]
    refine (Fintype.sum_equiv (Tuple.sort u) _ _ (fun i => ?_))
    exact Fintype.sum_equiv (Tuple.sort u) _ _ (fun _ => rfl)
  simp only [hS, hQ] at hmain
  exact hmain

end ReflectedGMS.MultiTimeCharFun
