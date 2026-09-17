/-
Almost sure convergence of the partial sums of the isonormal process.

`eq:dgt4-infinite-green-field` reads the Gaussian field
`V_∞(x) = ∑_z G(x,z)ζ(z)` as the limit of its partial sums over an exhausting
sequence of finite sets, and the human ruling of 2026-09-10 fixes that reading.
The series is not absolutely convergent: `∑_z G(x,z) = ∞`, and only
`∑_z G(x,z)^2 < ∞` holds.  What makes the box limit exist is that the difference
between the sum of the series and its partial sum over a finite set `s` is
again a centred Gaussian, of variance the tail `∑_{z ∉ s} G(x,z)^2`, so that
Chernoff's bound and Borel-Cantelli give the convergence as soon as the tails
decay at a polynomial rate.  That is what is proved here, for an arbitrary
square-summable family of coefficients and an arbitrary exhaustion with tails
`O(1/n)`; the Green-function instance is in `Support/LinGaussField.lean`.
-/
import LatticeProb.Gauss.Isonormal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.Isonormal

variable {ι : Type*}

/-- The restriction of a square-summable family of coefficients to a set. -/
noncomputable def lpRestrict (g : lp (fun _ : ι => ℝ) 2) (s : Set ι) : lp (fun _ : ι => ℝ) 2 :=
  ⟨Set.indicator s (g : ι → ℝ), by
    refine (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).2 ?_
    have hg := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).1 (lp.memℓp g)
    refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (norm_nonneg _) _)
      (fun i => ?_) hg
    by_cases h : i ∈ s
    · simp [Set.indicator_of_mem h]
    · simp only [Set.indicator_of_notMem h, norm_zero,
        Real.zero_rpow (by norm_num : ((2 : ℝ≥0∞)).toReal ≠ 0)]
      exact Real.rpow_nonneg (norm_nonneg _) _⟩

theorem coeFn_lpRestrict (g : lp (fun _ : ι => ℝ) 2) (s : Set ι) :
    ((lpRestrict g s : lp (fun _ : ι => ℝ) 2) : ι → ℝ) = Set.indicator s (g : ι → ℝ) := rfl

/-- A family is the sum of its restrictions to a set and to its complement. -/
theorem lpRestrict_add_compl (g : lp (fun _ : ι => ℝ) 2) (s : Set ι) :
    lpRestrict g s + lpRestrict g sᶜ = g := by
  refine Subtype.ext ?_
  funext i
  show Set.indicator s (g : ι → ℝ) i + Set.indicator sᶜ (g : ι → ℝ) i = (g : ι → ℝ) i
  by_cases h : i ∈ s <;> simp [h, Set.mem_compl_iff]

/-- The squared norm of a restricted family is the sum of the squares of its
coefficients over the set. -/
theorem norm_sq_lpRestrict (g : lp (fun _ : ι => ℝ) 2) (s : Set ι) :
    ‖lpRestrict g s‖ ^ 2 = ∑' i : s, ((g : ι → ℝ) (i : ι)) ^ 2 := by
  have hpow : ∀ x : ℝ, x ^ ((2 : ℝ≥0∞)).toReal = x ^ 2 := fun x => by
    rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (lpRestrict g s)
  simp only [hpow] at h
  rw [h, tsum_subtype s (fun j => ((g : ι → ℝ) j) ^ 2)]
  refine tsum_congr fun i => ?_
  show ‖Set.indicator s (g : ι → ℝ) i‖ ^ 2 = Set.indicator s (fun j => ((g : ι → ℝ) j) ^ 2) i
  by_cases hi : i ∈ s <;>
    simp [hi, Real.norm_eq_abs, sq_abs]

/-- The geometric sequence `exp (-(b n))` is summable. -/
theorem summable_exp_neg_mul (b : ℝ) (hb : 0 < b) :
    Summable (fun n : ℕ => Real.exp (-(b * (n : ℝ)))) := by
  have hfun : (fun n : ℕ => Real.exp (-(b * (n : ℝ)))) = fun n : ℕ => (Real.exp (-b)) ^ n := by
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h0 : 0 ≤ Real.exp (-b) := (Real.exp_pos _).le
  have h1 : Real.exp (-b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [hfun]
  exact summable_geometric_of_lt_one h0 h1

/-- Chernoff's bound for the centred real Gaussian: the upper tail at `a` is at
most `exp(-a^2/(2v))`. -/
theorem gaussianReal_measure_ge_le (v : ℝ≥0) (hv : 0 < (v : ℝ)) (a : ℝ) (ha : 0 ≤ a) :
    ((gaussianReal 0 v).real {x : ℝ | a ≤ x}) ≤ Real.exp (-(a ^ 2 / (2 * (v : ℝ)))) := by
  have key := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 v)
      (X := fun x : ℝ => x) (t := a / (v : ℝ)) a (by positivity)
      (ProbabilityTheory.integrable_exp_mul_gaussianReal (a / (v : ℝ)))
  rw [ProbabilityTheory.mgf_fun_id_gaussianReal] at key
  have h : Real.exp (-(a / (v : ℝ)) * a)
      * Real.exp (0 * (a / (v : ℝ)) + (v : ℝ) * (a / (v : ℝ)) ^ 2 / 2)
      = Real.exp (-(a ^ 2 / (2 * (v : ℝ)))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  exact key.trans_eq h

/-- The two-sided Gaussian tail, with the variance replaced by any upper bound
for it.  At variance zero the law is a Dirac mass and the tail vanishes. -/
theorem gaussianReal_abs_ge_le (w : ℝ≥0) (v : ℝ) (hwv : (w : ℝ) ≤ v) (_hv : 0 < v)
    (a : ℝ) (ha : 0 < a) :
    (gaussianReal 0 w) {x : ℝ | a ≤ |x|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / (2 * v)))) := by
  by_cases hw : w = 0
  · subst hw
    rw [ProbabilityTheory.gaussianReal_zero_var]
    have hmeas : MeasurableSet {x : ℝ | a ≤ |x|} :=
      measurableSet_le measurable_const measurable_id.abs
    rw [MeasureTheory.Measure.dirac_apply' (0 : ℝ) hmeas]
    have h0 : (0 : ℝ) ∉ {x : ℝ | a ≤ |x|} := by
      simp only [Set.mem_setOf_eq, abs_zero, not_le]
      exact ha
    rw [Set.indicator_of_notMem h0]
    exact zero_le
  · have hw0 : 0 < (w : ℝ) :=
      lt_of_le_of_ne w.coe_nonneg (fun h => hw (NNReal.coe_eq_zero.mp h.symm))
    have hup : (gaussianReal 0 w) {x : ℝ | a ≤ x}
        ≤ ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * (w : ℝ))))) := by
      have h := gaussianReal_measure_ge_le w hw0 a ha.le
      have hne : (gaussianReal 0 w) {x : ℝ | a ≤ x} ≠ ⊤ := measure_ne_top _ _
      rw [← ENNReal.ofReal_toReal hne]
      exact ENNReal.ofReal_le_ofReal (by rwa [← MeasureTheory.measureReal_def])
    have hmap : Measure.map (fun x : ℝ => -x) (gaussianReal 0 w) = gaussianReal 0 w := by
      have h := ProbabilityTheory.gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := w) (-1)
      simpa using h
    have hlow : (gaussianReal 0 w) {x : ℝ | a ≤ -x}
        ≤ ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * (w : ℝ))))) := by
      have hpre : {x : ℝ | a ≤ -x} = (fun x : ℝ => -x) ⁻¹' {x : ℝ | a ≤ x} := rfl
      have hmm : (gaussianReal 0 w) ((fun x : ℝ => -x) ⁻¹' {x : ℝ | a ≤ x})
          = (Measure.map (fun x : ℝ => -x) (gaussianReal 0 w)) {x : ℝ | a ≤ x} :=
        (Measure.map_apply measurable_neg
          (measurableSet_le measurable_const measurable_id)).symm
      rw [hpre, hmm, hmap]
      exact hup
    have hsub : {x : ℝ | a ≤ |x|} ⊆ {x : ℝ | a ≤ x} ∪ {x : ℝ | a ≤ -x} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      rcases le_total 0 x with h | h
      · left; simpa [abs_of_nonneg h] using hx
      · right; simpa [abs_of_nonpos h] using hx
    have hvar : Real.exp (-(a ^ 2 / (2 * (w : ℝ)))) ≤ Real.exp (-(a ^ 2 / (2 * v))) := by
      rw [Real.exp_le_exp]
      have h1 : a ^ 2 / (2 * v) ≤ a ^ 2 / (2 * (w : ℝ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
      linarith
    calc (gaussianReal 0 w) {x : ℝ | a ≤ |x|}
        ≤ (gaussianReal 0 w) ({x : ℝ | a ≤ x} ∪ {x : ℝ | a ≤ -x}) := measure_mono hsub
      _ ≤ (gaussianReal 0 w) {x : ℝ | a ≤ x} + (gaussianReal 0 w) {x : ℝ | a ≤ -x} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * (w : ℝ)))))
            + ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * (w : ℝ))))) := add_le_add hup hlow
      _ = ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / (2 * (w : ℝ))))) := by
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
          ring_nf
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / (2 * v)))) :=
          ENNReal.ofReal_le_ofReal (by linarith)

/-- The isonormal image of a family of coefficients supported in a finite set is
the corresponding finite linear combination of the coordinates. -/
theorem gaussIso_lpRestrict_coe (g : lp (fun _ : ι => ℝ) 2) (s : Finset ι) :
    (⇑(LatticeProb.gaussIso (lpRestrict g (s : Set ι))))
      =ᵐ[LatticeProb.gaussLaw ι] fun ω : ι → ℝ => ∑ i ∈ s, (g : ι → ℝ) i * ω i := by
  have hzero : ∀ i ∉ s, ((lpRestrict g (s : Set ι) : lp (fun _ : ι => ℝ) 2) : ι → ℝ) i
      • LatticeProb.gaussCoord i = 0 := by
    intro i hi
    rw [coeFn_lpRestrict, Set.indicator_of_notMem (by simpa using hi), zero_smul]
  have hfin : HasSum
      (fun i => ((lpRestrict g (s : Set ι) : lp (fun _ : ι => ℝ) 2) : ι → ℝ) i
        • LatticeProb.gaussCoord i)
      (∑ i ∈ s, ((lpRestrict g (s : Set ι) : lp (fun _ : ι => ℝ) 2) : ι → ℝ) i
        • LatticeProb.gaussCoord i) := hasSum_sum_of_ne_finset_zero hzero
  have heq : LatticeProb.gaussIso (lpRestrict g (s : Set ι))
      = ∑ i ∈ s, ((lpRestrict g (s : Set ι) : lp (fun _ : ι => ℝ) 2) : ι → ℝ) i
        • LatticeProb.gaussCoord i :=
    (LatticeProb.hasSum_gaussIso (lpRestrict g (s : Set ι))).unique hfin
  rw [heq]
  filter_upwards [LatticeProb.coeFn_sum_smul_gaussCoord
      (fun i => ((lpRestrict g (s : Set ι) : lp (fun _ : ι => ℝ) 2) : ι → ℝ) i) s] with ω hω
  rw [hω]
  simp only [LatticeProb.gaussSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [coeFn_lpRestrict, Set.indicator_of_mem (by simpa using hi)]

/-- Chernoff's bound for the isonormal image of a family of coefficients. -/
theorem measure_abs_ge_gaussIso_le [Countable ι] (f : lp (fun _ : ι => ℝ) 2)
    (v : ℝ) (hv : ‖f‖ ^ 2 ≤ v) (hv0 : 0 < v) (a : ℝ) (ha : 0 < a) :
    LatticeProb.gaussLaw ι {ω : ι → ℝ | a ≤ |⇑(LatticeProb.gaussIso f) ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / (2 * v)))) := by
  have hmeasY : AEMeasurable (⇑(LatticeProb.gaussIso f)) (LatticeProb.gaussLaw ι) :=
    (Lp.aestronglyMeasurable (LatticeProb.gaussIso f)).aemeasurable
  have hA : MeasurableSet {x : ℝ | a ≤ |x|} :=
    measurableSet_le measurable_const measurable_id.abs
  have hpre : {ω : ι → ℝ | a ≤ |⇑(LatticeProb.gaussIso f) ω|}
      = (⇑(LatticeProb.gaussIso f)) ⁻¹' {x : ℝ | a ≤ |x|} := rfl
  rw [hpre, ← Measure.map_apply_of_aemeasurable hmeasY hA, LatticeProb.map_gaussIso]
  refine gaussianReal_abs_ge_le (‖f‖ ^ 2).toNNReal v ?_ hv0 a ha
  rw [Real.coe_toNNReal _ (by positivity)]
  exact hv

/-- **Almost sure convergence of the partial sums of the isonormal process.**
If the tails of the sum of the squares of the coefficients outside the sets of an
exhausting sequence decay at the rate `1/n`, then the partial sums converge almost
surely to the isonormal image. -/
theorem ae_tendsto_partialSum [Countable ι] (g : lp (fun _ : ι => ℝ) 2) (s : ℕ → Finset ι)
    (C : ℝ) (hC : 0 < C)
    (htail : ∀ n : ℕ,
      ∑' i : {i : ι // i ∉ (s n : Set ι)}, ((g : ι → ℝ) (i : ι)) ^ 2 ≤ C / ((n : ℝ) + 1)) :
    ∀ᵐ ω ∂(LatticeProb.gaussLaw ι),
      Filter.Tendsto (fun n => ∑ i ∈ s n, (g : ι → ℝ) i * ω i) atTop
        (𝓝 (⇑(LatticeProb.gaussIso g) ω)) := by
  have hTnorm : ∀ n : ℕ, ‖lpRestrict g ((s n : Set ι))ᶜ‖ ^ 2 ≤ C / ((n : ℝ) + 1) := by
    intro n
    rw [norm_sq_lpRestrict]
    exact htail n
  have hsplit : ∀ n : ℕ, ∀ᵐ ω ∂(LatticeProb.gaussLaw ι),
      ⇑(LatticeProb.gaussIso g) ω
        = (∑ i ∈ s n, (g : ι → ℝ) i * ω i)
          + ⇑(LatticeProb.gaussIso (lpRestrict g ((s n : Set ι))ᶜ)) ω := by
    intro n
    have hadd : LatticeProb.gaussIso g
        = LatticeProb.gaussIso (lpRestrict g (s n : Set ι))
          + LatticeProb.gaussIso (lpRestrict g ((s n : Set ι))ᶜ) := by
      rw [← map_add, lpRestrict_add_compl]
    filter_upwards [gaussIso_lpRestrict_coe g (s n),
      Lp.coeFn_add (LatticeProb.gaussIso (lpRestrict g (s n : Set ι)))
        (LatticeProb.gaussIso (lpRestrict g ((s n : Set ι))ᶜ))] with ω h1 h2
    rw [hadd, h2, Pi.add_apply, h1]
  have hBC : ∀ m : ℕ, ∀ᵐ ω ∂(LatticeProb.gaussLaw ι), ∀ᶠ n in atTop,
      ω ∉ {ω : ι → ℝ | 1 / ((m : ℝ) + 1)
        ≤ |⇑(LatticeProb.gaussIso (lpRestrict g ((s n : Set ι))ᶜ)) ω|} := by
    intro m
    refine MeasureTheory.ae_eventually_notMem ?_
    have hbpos : 0 < (1 / ((m : ℝ) + 1)) ^ 2 / (2 * C) := by positivity
    have hbound : ∀ n : ℕ,
        LatticeProb.gaussLaw ι {ω : ι → ℝ | 1 / ((m : ℝ) + 1)
            ≤ |⇑(LatticeProb.gaussIso (lpRestrict g ((s n : Set ι))ᶜ)) ω|}
          ≤ ENNReal.ofReal
              (2 * Real.exp (-((1 / ((m : ℝ) + 1)) ^ 2 / (2 * C) * ((n : ℝ) + 1)))) := by
      intro n
      have hCn : 0 < C / ((n : ℝ) + 1) := by positivity
      have h := measure_abs_ge_gaussIso_le (lpRestrict g ((s n : Set ι))ᶜ)
        (C / ((n : ℝ) + 1)) (hTnorm n) hCn (1 / ((m : ℝ) + 1)) (by positivity)
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      have heq : (1 / ((m : ℝ) + 1)) ^ 2 / (2 * (C / ((n : ℝ) + 1)))
          = (1 / ((m : ℝ) + 1)) ^ 2 / (2 * C) * ((n : ℝ) + 1) := by
        have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp
      rw [heq]
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound) ?_)
    have hsummable : Summable (fun n : ℕ =>
        2 * Real.exp (-((1 / ((m : ℝ) + 1)) ^ 2 / (2 * C) * ((n : ℝ) + 1)))) := by
      have h := summable_exp_neg_mul ((1 / ((m : ℝ) + 1)) ^ 2 / (2 * C)) hbpos
      have hfun : (fun n : ℕ =>
          2 * Real.exp (-((1 / ((m : ℝ) + 1)) ^ 2 / (2 * C) * ((n : ℝ) + 1))))
          = fun n : ℕ => (2 * Real.exp (-((1 / ((m : ℝ) + 1)) ^ 2 / (2 * C))))
              * Real.exp (-((1 / ((m : ℝ) + 1)) ^ 2 / (2 * C) * (n : ℝ))) := by
        funext n
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      rw [hfun]
      exact h.mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable]
    exact ENNReal.ofReal_lt_top
  filter_upwards [MeasureTheory.ae_all_iff.2 hsplit, MeasureTheory.ae_all_iff.2 hBC]
    with ω hω1 hω2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hω2 m)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hω1 n
  have h2 := hN n hn
  simp only [not_le] at h2
  rw [Real.dist_eq]
  have h3 : (∑ i ∈ s n, (g : ι → ℝ) i * ω i) - ⇑(LatticeProb.gaussIso g) ω
      = -(⇑(LatticeProb.gaussIso (lpRestrict g ((s n : Set ι))ᶜ)) ω) := by
    rw [h1]; ring
  rw [h3, abs_neg]
  exact lt_trans h2 hm

/-! ### The finite-dimensional laws of the isonormal process -/

/-- The mean of an isonormal image is zero. -/
theorem integral_gaussIso [Countable ι] (f : lp (fun _ : ι => ℝ) 2) :
    ∫ ω, ⇑(LatticeProb.gaussIso f) ω ∂(LatticeProb.gaussLaw ι) = 0 := by
  have hm : AEMeasurable (⇑(LatticeProb.gaussIso f)) (LatticeProb.gaussLaw ι) :=
    (Lp.stronglyMeasurable (LatticeProb.gaussIso f)).measurable.aemeasurable
  have h := integral_map (μ := LatticeProb.gaussLaw ι) (φ := ⇑(LatticeProb.gaussIso f))
      (f := fun x : ℝ => x) hm (by fun_prop)
  rw [LatticeProb.map_gaussIso f] at h
  rw [← h]
  exact ProbabilityTheory.integral_id_gaussianReal

/-- The covariance of two isonormal images is the inner product of their
coefficient families. -/
theorem integral_gaussIso_mul (f g : lp (fun _ : ι => ℝ) 2) :
    ∫ ω, ⇑(LatticeProb.gaussIso f) ω * ⇑(LatticeProb.gaussIso g) ω ∂(LatticeProb.gaussLaw ι)
      = (inner ℝ f g : ℝ) := by
  have h := LatticeProb.gaussIso.inner_map_map f g
  rw [L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- A finite linear combination of isonormal images is the isonormal image of the
same combination of the coefficient families. -/
theorem coeFn_gaussIso_sum_smul {m : ℕ} (t : Fin m → ℝ) (gs : Fin m → lp (fun _ : ι => ℝ) 2) :
    ⇑(LatticeProb.gaussIso (∑ i, t i • gs i))
      =ᵐ[LatticeProb.gaussLaw ι] fun ω => ∑ i, t i * ⇑(LatticeProb.gaussIso (gs i)) ω := by
  have hmap : LatticeProb.gaussIso (∑ i, t i • gs i)
      = ∑ i, t i • LatticeProb.gaussIso (gs i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  rw [hmap]
  have key : ∀ s : Finset (Fin m),
      (⇑(∑ i ∈ s, t i • LatticeProb.gaussIso (gs i)) : (ι → ℝ) → ℝ)
        =ᵐ[LatticeProb.gaussLaw ι]
          fun ω => ∑ i ∈ s, t i * ⇑(LatticeProb.gaussIso (gs i)) ω := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.sum_empty]
        filter_upwards [Lp.coeFn_zero ℝ 2 (LatticeProb.gaussLaw ι)] with ω hω
        rw [hω]
        simp
    | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        filter_upwards [Lp.coeFn_add (t j • LatticeProb.gaussIso (gs j))
            (∑ i ∈ s, t i • LatticeProb.gaussIso (gs i)), ih,
          Lp.coeFn_smul (t j) (LatticeProb.gaussIso (gs j))] with ω h1 h2 h3
        rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Finset.sum_insert hj, smul_eq_mul]
  exact key Finset.univ

/-- The Gram matrix of a finite family of coefficient families. -/
noncomputable def gramMatrix {m : ℕ} (gs : Fin m → lp (fun _ : ι => ℝ) 2) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => (inner ℝ (gs i) (gs j) : ℝ)

/-- The squared norm of a linear combination is the quadratic form of the Gram
matrix. -/
theorem norm_sq_sum_smul {m : ℕ} (t : Fin m → ℝ) (gs : Fin m → lp (fun _ : ι => ℝ) 2) :
    ‖∑ i, t i • gs i‖ ^ 2 = ∑ i, ∑ j, t i * (gramMatrix gs i j * t j) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_right]
  simp only [gramMatrix, Matrix.of_apply]
  ring

/-- The Gram matrix is positive semidefinite. -/
theorem gramMatrix_posSemidef {m : ℕ} (gs : Fin m → lp (fun _ : ι => ℝ) 2) :
    (gramMatrix gs).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [gramMatrix, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    exact real_inner_comm _ _
  · have hx : (star x) ⬝ᵥ ((gramMatrix gs).mulVec x)
        = ∑ i, ∑ j, x i * (gramMatrix gs i j * x j) := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [hx, ← norm_sq_sum_smul x gs]
    positivity

/-- **The finite-dimensional laws of the isonormal process.**  The vector of the
isonormal images of a finite family of coefficient families is a centred Gaussian
vector whose covariance is the Gram matrix of the families. -/
theorem map_gaussIso_vector [Countable ι] {m : ℕ} (gs : Fin m → lp (fun _ : ι => ℝ) 2) :
    (LatticeProb.gaussLaw ι).map
        (fun ω => (WithLp.toLp 2 (fun i => ⇑(LatticeProb.gaussIso (gs i)) ω) :
          EuclideanSpace ℝ (Fin m)))
      = multivariateGaussian 0 (gramMatrix gs) := by
  have hcomp : ∀ i : Fin m, Measurable (fun ω : ι → ℝ => ⇑(LatticeProb.gaussIso (gs i)) ω) :=
    fun i => (Lp.stronglyMeasurable (LatticeProb.gaussIso (gs i))).measurable
  have hΦ : Measurable (fun ω : ι → ℝ =>
      (WithLp.toLp 2 (fun i => ⇑(LatticeProb.gaussIso (gs i)) ω) :
        EuclideanSpace ℝ (Fin m))) := by
    fun_prop
  haveI : IsProbabilityMeasure ((LatticeProb.gaussLaw ι).map
      (fun ω : ι → ℝ => (WithLp.toLp 2 (fun i => ⇑(LatticeProb.gaussIso (gs i)) ω) :
        EuclideanSpace ℝ (Fin m)))) := Measure.isProbabilityMeasure_map hΦ.aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_apply, integral_map hΦ.aemeasurable (by fun_prop)]
  have hae : ∀ᵐ ω ∂(LatticeProb.gaussLaw ι),
      Complex.exp ((inner ℝ (WithLp.toLp 2 (fun i => ⇑(LatticeProb.gaussIso (gs i)) ω) :
            EuclideanSpace ℝ (Fin m)) t : ℝ) * Complex.I)
        = Complex.exp ((⇑(LatticeProb.gaussIso (∑ i, t i • gs i)) ω : ℝ) * Complex.I) := by
    filter_upwards [coeFn_gaussIso_sum_smul t gs] with ω hω
    have hinner : (inner ℝ (WithLp.toLp 2 (fun i => ⇑(LatticeProb.gaussIso (gs i)) ω) :
          EuclideanSpace ℝ (Fin m)) t : ℝ)
        = ∑ i, t i * ⇑(LatticeProb.gaussIso (gs i)) ω := by
      simp [PiLp.inner_apply]
    rw [hω, hinner]
  rw [integral_congr_ae hae]
  have hY : AEMeasurable (⇑(LatticeProb.gaussIso (∑ i, t i • gs i))) (LatticeProb.gaussLaw ι) :=
    (Lp.stronglyMeasurable (LatticeProb.gaussIso (∑ i, t i • gs i))).measurable.aemeasurable
  rw [← integral_map (φ := ⇑(LatticeProb.gaussIso (∑ i, t i • gs i)))
      (f := fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) hY (by fun_prop),
    LatticeProb.map_gaussIso]
  rw [charFun_multivariateGaussian (gramMatrix_posSemidef gs) t]
  have hquad : (t.ofLp ⬝ᵥ (gramMatrix gs).mulVec t.ofLp) = ‖∑ i, t i • gs i‖ ^ 2 := by
    rw [norm_sq_sum_smul t gs]
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hnorm : ((‖∑ i, t i • gs i‖ ^ 2).toNNReal : ℝ) = ‖∑ i, t i • gs i‖ ^ 2 :=
    Real.coe_toNNReal _ (by positivity)
  have hchar : ∫ (x : ℝ), Complex.exp ((x : ℂ) * Complex.I)
      ∂gaussianReal 0 (‖∑ i, t i • gs i‖ ^ 2).toNNReal
      = Complex.exp (-((((‖∑ i, t i • gs i‖ ^ 2).toNNReal : ℝ) : ℂ) / 2)) := by
    have h := ProbabilityTheory.charFun_gaussianReal (μ := 0)
        (v := (‖∑ i, t i • gs i‖ ^ 2).toNNReal) 1
    rw [MeasureTheory.charFun_apply_real] at h
    simpa using h
  rw [hchar, hquad, hnorm]
  congr 1
  simp

end LatticeProb.Isonormal
