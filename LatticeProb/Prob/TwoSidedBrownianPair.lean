import LatticeProb.Prob.BrownianFourCopies

/-! # A pair of two-sided Brownian processes

Four independent one-sided Brownian motions give a centered jointly Gaussian pair
with the two-sided Brownian covariance and continuous paths.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two stitched coordinates. At negative times the second copy is read at `-t`,
with no additional sign change. Each half is recentered at its own initial value. -/
noncomputable def twoSidedBrownianPair (B : ℝ≥0 → Ω → ℝ)
    (p : ℝ × Fin 2) (ω : Fin 4 → Ω) : ℝ :=
  if 0 ≤ p.1 then
    let i : Fin 4 := if p.2 = 0 then 0 else 2
    B (Real.toNNReal p.1) (ω i) - B 0 (ω i)
  else
    let i : Fin 4 := if p.2 = 0 then 1 else 3
    B (Real.toNNReal (-p.1)) (ω i) - B 0 (ω i)

omit [MeasurableSpace Ω] in
/-- The stitched paths start at zero for every sample. -/
theorem two_sided_brownian_pair_zero (B : ℝ≥0 → Ω → ℝ) (i : Fin 2)
    (ω : Fin 4 → Ω) : twoSidedBrownianPair B (0, i) ω = 0 := by
  simp [twoSidedBrownianPair]

/-- Every fixed-time evaluation of the stitched process is measurable. -/
theorem measurable_two_sided_brownian_pair (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (p : ℝ × Fin 2) :
    Measurable (twoSidedBrownianPair B p) := by
  classical
  unfold twoSidedBrownianPair
  split <;> exact ((hm _).comp (measurable_pi_apply _)).sub
    ((hm 0).comp (measurable_pi_apply _))

omit [MeasurableSpace Ω] in
/-- The two pieces join continuously at zero on every sample path. -/
theorem continuous_two_sided_brownian_pair (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous fun t => B t ω) (i : Fin 2) (ω : Fin 4 → Ω) :
    Continuous fun t => twoSidedBrownianPair B (t, i) ω := by
  classical
  simp only [twoSidedBrownianPair]
  refine Continuous.if_le ?_ ?_ continuous_const continuous_id ?_
  · exact ((hc (ω (if i = 0 then 0 else 2))).comp continuous_real_toNNReal).sub
      (continuous_const : Continuous fun _ : ℝ => B 0 (ω (if i = 0 then 0 else 2)))
  · exact ((hc (ω (if i = 0 then 1 else 3))).comp
      (continuous_real_toNNReal.comp continuous_neg)).sub
      (continuous_const : Continuous fun _ : ℝ => B 0 (ω (if i = 0 then 1 else 3)))
  · intro t ht
    have : t = 0 := ht.symm
    subst t
    simp

/-- All finite-dimensional distributions of the stitched pair are jointly Gaussian. -/
theorem isGaussianProcess_two_sided_brownian_pair (B : ℝ≥0 → Ω → ℝ)
    {P : Measure Ω} (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) :
    IsGaussianProcess (twoSidedBrownianPair B) (Measure.pi fun _ : Fin 4 => P) := by
  classical
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let Q := Measure.pi fun _ : Fin 4 => P
  have hcopy := brownian_four_copies B hB hm hc
  refine ⟨fun I => ?_⟩
  let n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let tm : Fin n → ℝ≥0 := fun k =>
    let t := (e.symm k).1.1
    Real.toNNReal (if 0 ≤ t then t else -t)
  let idx : I → Fin 4 := fun p =>
    if 0 ≤ p.1.1 then (if p.1.2 = 0 then 0 else 2)
    else (if p.1.2 = 0 then 1 else 3)
  let X : Fin 4 → (Fin 4 → Ω) → (Fin n → ℝ) :=
    fun i ω k => brownianFourCopy B i (tm k) ω
  have hX : ∀ i, HasGaussianLaw (X i) Q := by
    intro i
    have hG := (hcopy.1 i).isGaussianProcess.comp_right tm
    let L : (↥(Finset.univ : Finset (Fin n)) → ℝ) →L[ℝ] (Fin n → ℝ) :=
      ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj ⟨k, Finset.mem_univ k⟩
    exact (hG.hasGaussianLaw Finset.univ).map L
  have hInd : iIndepFun X Q := hcopy.2.2.2 n (fun _ => tm)
  let L : (Fin 4 → Fin n → ℝ) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun p =>
      (ContinuousLinearMap.proj (e p) : (Fin n → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj (idx p))
  have hG : HasGaussianLaw (fun ω => L (fun i => X i ω)) Q :=
    (hInd.hasGaussianLaw hX).map L
  apply hG.congr
  filter_upwards [brownian_four_copies_start_zero B hB] with ω hzero
  ext p
  simp only [L, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, X, brownianFourCopy, tm, Equiv.symm_apply_apply,
    Finset.restrict_def, twoSidedBrownianPair, idx]
  simp only [brownianFourCopy] at hzero
  by_cases hp : 0 ≤ p.1.1 <;> simp [hp, hzero]

/-- Every value of the stitched pair is centered. -/
theorem integral_two_sided_brownian_pair (B : ℝ≥0 → Ω → ℝ)
    {P : Measure Ω} (hB : IsBrownianReal B P) (p : ℝ × Fin 2) :
    ∫ ω, twoSidedBrownianPair B p ω ∂(Measure.pi fun _ : Fin 4 => P) = 0 := by
  classical
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  by_cases hp : 0 ≤ p.1
  · let i : Fin 4 := if p.2 = 0 then 0 else 2
    calc
      _ = ∫ ω, brownianFourCopy B i (Real.toNNReal p.1) ω ∂(Measure.pi fun _ : Fin 4 => P) := by
        apply integral_congr_ae
        filter_upwards [brownian_four_copies_start_zero B hB] with ω hzero
        simp only [brownianFourCopy] at hzero
        simp [twoSidedBrownianPair, hp, brownianFourCopy, hzero, i]
      _ = 0 := (isBrownianReal_comp_eval (d := 4) hB i).integral_eval _
  · let i : Fin 4 := if p.2 = 0 then 1 else 3
    calc
      _ = ∫ ω, brownianFourCopy B i (Real.toNNReal (-p.1)) ω ∂(Measure.pi fun _ : Fin 4 => P) := by
        apply integral_congr_ae
        filter_upwards [brownian_four_copies_start_zero B hB] with ω hzero
        simp only [brownianFourCopy] at hzero
        simp [twoSidedBrownianPair, hp, brownianFourCopy, hzero, i]
      _ = 0 := (isBrownianReal_comp_eval (d := 4) hB i).integral_eval _

/-- Covariance of two evaluations of the four independent copies. -/
theorem brownian_four_copy_covariance_pair (B : ℝ≥0 → Ω → ℝ)
    {P : Measure Ω} (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (i j : Fin 4) (s t : ℝ≥0) :
    cov[brownianFourCopy B i s, brownianFourCopy B j t; Measure.pi fun _ : Fin 4 => P] =
      if i = j then (min s t : ℝ) else 0 := by
  classical
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  by_cases hij : i = j
  · subst j
    change cov[(fun ω => B s (ω i)), (fun ω => B t (ω i));
      Measure.pi fun _ : Fin 4 => P] = _
    simpa using (isBrownianReal_comp_eval (d := 4) hB i).covariance_eval s t
  · let u : Fin 4 → ℝ≥0 := fun k => if k = i then s else t
    have hind : iIndepFun (fun k ω => B (u k) (ω k))
        (Measure.pi fun _ : Fin 4 => P) :=
      iIndepFun_pi (fun k => (hm (u k)).aemeasurable)
    have hindij := hind.indepFun hij
    have hi := ((isBrownianReal_comp_eval (d := 4) hB i).isGaussianProcess
      |>.hasGaussianLaw_eval s).memLp_two
    have hj := ((isBrownianReal_comp_eval (d := 4) hB j).isGaussianProcess
      |>.hasGaussianLaw_eval t).memLp_two
    have hc := hindij.covariance_eq_zero (by simpa [u, brownianFourCopy] using hi)
      (by simpa [u, Ne.symm hij, brownianFourCopy] using hj)
    change cov[(fun ω => B s (ω i)), (fun ω => B t (ω j));
      Measure.pi fun _ : Fin 4 => P] = _
    simpa [u, hij, Ne.symm hij] using hc

/-- Covariance kernel of the stitched pair, including opposite signs and zero. -/
theorem two_sided_brownian_pair_covariance (B : ℝ≥0 → Ω → ℝ)
    {P : Measure Ω} (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (s t : ℝ) (i j : Fin 2) :
    cov[twoSidedBrownianPair B (s, i), twoSidedBrownianPair B (t, j);
      Measure.pi fun _ : Fin 4 => P] =
      if i = j then (|s| + |t| - |s - t|) / 2 else 0 := by
  classical
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let Q := Measure.pi fun _ : Fin 4 => P
  let c : ℝ × Fin 2 → Fin 4 := fun p =>
    if 0 ≤ p.1 then (if p.2 = 0 then 0 else 2) else (if p.2 = 0 then 1 else 3)
  let u : ℝ → ℝ≥0 := fun x => Real.toNNReal (if 0 ≤ x then x else -x)
  have heq (p : ℝ × Fin 2) : twoSidedBrownianPair B p =ᵐ[Q]
      brownianFourCopy B (c p) (u p.1) := by
    filter_upwards [brownian_four_copies_start_zero B hB] with ω hzero
    simp only [brownianFourCopy] at hzero
    by_cases hp : 0 ≤ p.1 <;> simp [twoSidedBrownianPair, c, u, hp, brownianFourCopy, hzero]
  have hc : cov[twoSidedBrownianPair B (s, i), twoSidedBrownianPair B (t, j); Q] =
      cov[brownianFourCopy B (c (s, i)) (u s), brownianFourCopy B (c (t, j)) (u t); Q] := by
    have h1 := heq (s, i)
    have h2 := heq (t, j)
    unfold covariance
    rw [integral_congr_ae h1, integral_congr_ae h2]
    apply integral_congr_ae
    filter_upwards [h1, h2] with ω h1ω h2ω
    rw [h1ω, h2ω]
  change cov[twoSidedBrownianPair B (s, i), twoSidedBrownianPair B (t, j); Q] = _
  rw [hc, brownian_four_copy_covariance_pair B hB hm]
  fin_cases i <;> fin_cases j <;> by_cases hs : 0 ≤ s <;> by_cases ht : 0 ≤ t <;>
    by_cases hst : s ≤ t <;>
    simp [c, u, hs, ht, Real.coe_toNNReal', min_def, abs_of_nonneg] <;>
    simp only [abs_eq_max_neg, max_def] <;> split_ifs <;> try linarith
  all_goals have htn : t ≤ 0 := by linarith
  all_goals simp_all only [and_true, not_le]
  all_goals linarith

/-- Four independent one-sided Brownian copies give a centered two-sided Gaussian pair. -/
theorem two_sided_brownian_pair (B : ℝ≥0 → Ω → ℝ)
    {P : Measure Ω} (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) :
    IsGaussianProcess (twoSidedBrownianPair B) (Measure.pi fun _ : Fin 4 => P) ∧
    (∀ p, ∫ ω, twoSidedBrownianPair B p ω ∂(Measure.pi fun _ : Fin 4 => P) = 0) ∧
    (∀ s t i j, cov[twoSidedBrownianPair B (s, i), twoSidedBrownianPair B (t, j);
      Measure.pi fun _ : Fin 4 => P] = if i = j then (|s| + |t| - |s - t|) / 2 else 0) ∧
    (∀ p, Measurable (twoSidedBrownianPair B p)) ∧
    (∀ i ω, Continuous fun t => twoSidedBrownianPair B (t, i) ω) ∧
    (∀ i ω, twoSidedBrownianPair B (0, i) ω = 0) :=
  ⟨isGaussianProcess_two_sided_brownian_pair B hB hm hc,
    integral_two_sided_brownian_pair B hB, two_sided_brownian_pair_covariance B hB hm,
    measurable_two_sided_brownian_pair B hm, continuous_two_sided_brownian_pair B hc,
    two_sided_brownian_pair_zero B⟩

end LatticeProb
