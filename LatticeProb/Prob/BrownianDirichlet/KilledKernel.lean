import LatticeProb.Prob.BrownianDirichlet.JointMeasurability
import LatticeProb.Prob.BrownianWeakMarkovPath
import LatticeProb.Prob.BrownianFiniteStopping
import LatticeProb.Prob.BrownianPathHarmonicExit
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The killed Brownian kernel

The strict-survival integral acts on bounded Borel data. Survival factors along
successive deterministic path segments, including their common endpoint.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

namespace LatticeProb

variable {d : ℕ}

noncomputable section


/-- Brownian evaluation at time `t`, killed at the first exit of the scaled path. -/
noncomputable def killed (B : Set (Euc d)) (σ : ℝ) (μ : Measure (BrownianPath d))
    (t : ℝ≥0) (b : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ ω, if (t : ℝ≥0∞) < scaledExit B σ x ω then b (x + σ • ω t) else 0 ∂μ

/-- Fixing time in the jointly measurable killed integrand preserves measurability. -/
lemma measurable_killed_integrand_fixed {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (t : ℝ≥0) {b : Euc d → ℝ} (hb : Measurable b) :
    Measurable (fun p : Euc d × BrownianPath d ↦
      if (t : ℝ≥0∞) < scaledExit B σ p.1 p.2 then b (p.1 + σ • p.2 t) else 0) :=
  (measurable_killed_integrand hB σ hb).comp (measurable_const.prodMk measurable_id)

/-- Integrating the jointly measurable integrand gives a Borel function of the start. -/
lemma measurable_killed {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} [SFinite μ] (t : ℝ≥0)
    {b : Euc d → ℝ} (hb : Measurable b) : Measurable (killed B σ μ t b) :=
  (measurable_killed_integrand_fixed hB σ t hb).stronglyMeasurable.integral_prod_right'
    |>.measurable

/-- Bounded Borel data give an integrable killed evaluation under a finite measure. -/
lemma integrable_killed_integrand {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} [IsFiniteMeasure μ] (t : ℝ≥0)
    {b : Euc d → ℝ} (hb : Measurable b) {C : ℝ} (hC : 0 ≤ C)
    (hbC : ∀ y, |b y| ≤ C) (x : Euc d) :
    Integrable (fun ω ↦ if (t : ℝ≥0∞) < scaledExit B σ x ω
      then b (x + σ • ω t) else 0) μ := by
  apply Integrable.of_bound
    (((measurable_killed_integrand_fixed hB σ t hb).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable) C
  exact Filter.Eventually.of_forall fun ω ↦ by
    dsimp only [Function.comp_apply, id_eq]
    split_ifs
    · exact (Real.norm_eq_abs _).trans_le (hbC _)
    · simpa only [norm_zero] using hC

/-- The killed kernel preserves every uniform absolute bound under a probability law. -/
lemma abs_killed_le {B : Set (Euc d)} (σ : ℝ)
    {μ : Measure (BrownianPath d)} [IsProbabilityMeasure μ] (t : ℝ≥0)
    {b : Euc d → ℝ} {C : ℝ} (hC : 0 ≤ C) (hbC : ∀ y, |b y| ≤ C)
    (x : Euc d) : |killed B σ μ t b x| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω ↦ if (t : ℝ≥0∞) < scaledExit B σ x ω
      then b (x + σ • ω t) else 0) (C := C) ?_
  · simpa only [killed, Real.norm_eq_abs, probReal_univ, mul_one] using h
  · exact Filter.Eventually.of_forall fun ω ↦ by
      split_ifs
      · exact (Real.norm_eq_abs _).trans_le (hbC _)
      · simpa only [norm_zero] using hC

/-- For bounded data, the kernel is bounded by the supremum of the absolute values. -/
lemma abs_killed_le_sup (B : Set (Euc d)) (σ : ℝ)
    {μ : Measure (BrownianPath d)} [IsProbabilityMeasure μ] (t : ℝ≥0)
    {b : Euc d → ℝ} (hb : BddAbove (Set.range (fun y ↦ |b y|))) (x : Euc d) :
    |killed B σ μ t b x| ≤ sSup (Set.range (fun y ↦ |b y|)) := by
  apply abs_killed_le σ t
  · exact (abs_nonneg (b 0)).trans (le_csSup hb ⟨0, rfl⟩)
  · intro y
    exact le_csSup hb ⟨y, rfl⟩

/-- Nonnegative data have nonnegative killed expectation. -/
lemma killed_nonneg (B : Set (Euc d)) (σ : ℝ) (μ : Measure (BrownianPath d))
    (t : ℝ≥0) {b : Euc d → ℝ} (hb : ∀ y, 0 ≤ b y) (x : Euc d) :
    0 ≤ killed B σ μ t b x := by
  apply integral_nonneg
  intro ω
  dsimp only [Pi.zero_apply]
  split_ifs
  · exact hb _
  · exact le_rfl

/-- Addition of bounded Borel data commutes with killed expectation. -/
lemma killed_add_data {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} [IsFiniteMeasure μ] (t : ℝ≥0)
    {b c : Euc d → ℝ} (hb : Measurable b) (hc : Measurable c)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbC : ∀ y, |b y| ≤ C) (hcD : ∀ y, |c y| ≤ D) (x : Euc d) :
    killed B σ μ t (fun y ↦ b y + c y) x =
      killed B σ μ t b x + killed B σ μ t c x := by
  unfold killed
  rw [← integral_add (integrable_killed_integrand hB σ t hb hC hbC x)
    (integrable_killed_integrand hB σ t hc hD hcD x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ by
    dsimp only
    split_ifs <;> simp only [add_zero]

/-- Scalar multiplication commutes with killed expectation. -/
lemma killed_smul_data (B : Set (Euc d)) (σ : ℝ) (μ : Measure (BrownianPath d))
    (t : ℝ≥0) (a : ℝ) (b : Euc d → ℝ) (x : Euc d) :
    killed B σ μ t (fun y ↦ a * b y) x = a * killed B σ μ t b x := by
  unfold killed
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ by
    dsimp only
    split_ifs <;> simp only [mul_zero]

/-- Survival through a compact segment means membership at every point of that segment. -/
lemma lt_scaledExit_iff {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (x : Euc d) (ω : BrownianPath d) (t : ℝ≥0) :
    (t : ℝ≥0∞) < scaledExit B σ x ω ↔ ∀ u ≤ t, x + σ • ω u ∈ B := by
  rw [← not_le, scaledExit_le_iff hB]
  exact not_not

/-- The restarted scaled position agrees exactly with the original position. -/
lemma shiftedBrownianPath_position (σ : ℝ) (x : Euc d) (ω : BrownianPath d)
    (s t : ℝ≥0) :
    (x + σ • ω s) + σ • shiftedBrownianPath s ω t = x + σ • ω (s + t) := by
  change (x + σ • ω s) + σ • (ω (s + t) - ω s) = _
  rw [smul_sub]
  abel

/-- Strict survival factors along the two closed path segments meeting at time `s`. -/
lemma survival_split {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (x : Euc d) (ω : BrownianPath d) (s t : ℝ≥0) :
    ((s + t : ℝ≥0) : ℝ≥0∞) < scaledExit B σ x ω ↔
      (s : ℝ≥0∞) < scaledExit B σ x ω ∧
      (t : ℝ≥0∞) < scaledExit B σ (x + σ • ω s) (shiftedBrownianPath s ω) := by
  simp only [lt_scaledExit_iff hB, shiftedBrownianPath_position]
  constructor
  · intro h
    exact ⟨fun u hu ↦ h u (hu.trans (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ t))),
      fun u hu ↦ h (s + u) (add_le_add le_rfl hu)⟩
  · rintro ⟨hpast, hfuture⟩ u hu
    by_cases hus : u ≤ s
    · exact hpast u hus
    · have hsu : s ≤ u := le_of_not_ge hus
      have hsub : u - s ≤ t := (tsub_le_iff_left).mpr hu
      have h := hfuture (u - s) hsub
      rwa [add_tsub_cancel_of_le hsu] at h

/-- Killed evaluation factors into past survival and future killed evaluation. -/
lemma killed_integrand_add {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (b : Euc d → ℝ) (x : Euc d) (ω : BrownianPath d) (s t : ℝ≥0) :
    (if ((s + t : ℝ≥0) : ℝ≥0∞) < scaledExit B σ x ω
      then b (x + σ • ω (s + t)) else 0) =
    (if (s : ℝ≥0∞) < scaledExit B σ x ω then 1 else 0) *
      (if (t : ℝ≥0∞) < scaledExit B σ (x + σ • ω s) (shiftedBrownianPath s ω)
        then b ((x + σ • ω s) + σ • shiftedBrownianPath s ω t) else 0) := by
  simp only [survival_split hB σ x ω s t, shiftedBrownianPath_position]
  split_ifs <;>
    simp_all only [one_mul, zero_mul, and_false, false_and, and_self, not_true_eq_false]

/-- At time zero the kernel equals the datum inside the open domain and zero outside. -/
lemma killed_zero {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (b : Euc d → ℝ) (x : Euc d) :
    killed B σ μ 0 b x = B.indicator b x := by
  classical
  letI : IsProbabilityMeasure μ := hμ.1
  apply integral_eq_const
  filter_upwards [standardBrownianLaw_eval_zero_ae hμ] with ω hω
  by_cases hx : x ∈ B
  · simp only [indicator_of_mem hx, ENNReal.coe_zero]
    rw [if_pos (scaledExit_pos hB σ hx hω), hω, smul_zero, add_zero]
  · have hn : ¬ (0 : ℝ≥0∞) < scaledExit B σ x ω := by
      intro h
      have := mem_of_lt_scaledExit (t := 0) h
      simp only [hω, smul_zero, add_zero] at this
      exact hx this
    simp only [indicator_of_notMem hx, ENNReal.coe_zero, if_neg hn]

/-- A Brownian path started outside the domain is killed at every time. -/
lemma killed_eq_zero_of_not_mem (B : Set (Euc d)) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) (b : Euc d → ℝ) {x : Euc d} (hx : x ∉ B) :
    killed B σ μ t b x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [standardBrownianLaw_eval_zero_ae hμ] with ω hω
  have he : scaledExit B σ x ω = 0 := by
    apply continuousExitTime_eq_zero_of_not_mem
    simpa only [scalePath_apply, hω, smul_zero, add_zero] using hx
  simp only [he, not_lt_zero, if_false, Pi.zero_apply]

/-- The past survival indicator and current position are measurable in the natural past. -/
lemma measurable_killed_past {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (x : Euc d) (s : ℝ≥0) :
    Measurable[brownianNaturalFiltration d s] (fun ω : BrownianPath d ↦
      ((if (s : ℝ≥0∞) < scaledExit B σ x ω then 1 else 0 : ℝ), x + σ • ω s)) := by
  have hs := (isStoppingTime_scaledExit hB σ x).measurableSet_gt s
  have heval : Measurable[brownianNaturalFiltration d s]
      (fun ω : BrownianPath d ↦ ω s) := by
    rw [brownianNaturalFiltration_eq_comap]
    have hm : Measurable (fun p : Iic s → Euc d ↦ p ⟨s, mem_Iic.mpr le_rfl⟩) :=
      measurable_pi_apply _
    exact hm.comp (comap_measurable (fun (ω : BrownianPath d) (u : Iic s) ↦ ω u))
  exact (Measurable.ite hs measurable_const measurable_const).prodMk
    (measurable_const.add (heval.const_smul σ))

/-- The future path is independent of the surviving past position. -/
lemma indepFun_killed_past_shift {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (x : Euc d) (s : ℝ≥0) :
    IndepFun (fun ω : BrownianPath d ↦
      ((if (s : ℝ≥0∞) < scaledExit B σ x ω then 1 else 0 : ℝ), x + σ • ω s))
      (shiftedBrownianPath s) μ := by
  apply (IndepFun_iff _ _ _).mpr
  intro A S hA hS
  have hA' := (measurable_killed_past hB σ x s).comap_le A hA
  rw [brownianNaturalFiltration_eq_comap] at hA'
  exact (standardBrownianLaw_indepFun_shiftedPath hμ s).symm.meas_inter hA' hS

/-- A bounded surviving evaluation stays integrable after multiplication by a bounded mark. -/
lemma integrable_killed_product {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} [IsFiniteMeasure μ]
    {ν : Measure (ℝ × Euc d)} [IsFiniteMeasure ν] (t : ℝ≥0)
    {b : Euc d → ℝ} (hb : Measurable b) {C : ℝ} (hC : 0 ≤ C)
    (hbC : ∀ y, |b y| ≤ C) (hν : ∀ᵐ a ∂ν, |a.1| ≤ (1 : ℝ)) :
    Integrable (fun p : (ℝ × Euc d) × BrownianPath d ↦
      p.1.1 * (if (t : ℝ≥0∞) < scaledExit B σ p.1.2 p.2
        then b (p.1.2 + σ • p.2 t) else 0)) (ν.prod μ) := by
  have hm := measurable_fst.fst.mul
    ((measurable_killed_integrand_fixed hB σ t hb).comp
      (measurable_fst.snd.prodMk measurable_snd))
  apply Integrable.of_bound hm.aestronglyMeasurable C
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).mpr
  filter_upwards [hν] with a ha
  exact Filter.Eventually.of_forall fun η ↦ by
    change ‖a.1 * (if (t : ℝ≥0∞) < scaledExit B σ a.2 η
      then b (a.2 + σ • η t) else 0)‖ ≤ C
    rw [norm_mul, Real.norm_eq_abs a.1]
    split_ifs
    · calc
        |a.1| * ‖b (a.2 + σ • η t)‖ ≤ 1 * C :=
          mul_le_mul ha ((Real.norm_eq_abs _).trans_le (hbC _)) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · simpa only [norm_zero, mul_zero] using hC

/-- Successive killed Brownian evolutions compose on bounded Borel data. -/
lemma killed_add {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (s t : ℝ≥0) {b : Euc d → ℝ} (hb : Measurable b)
    {C : ℝ} (hC : 0 ≤ C) (hbC : ∀ y, |b y| ≤ C) (x : Euc d) :
    killed B σ μ (s + t) b x = killed B σ μ s (killed B σ μ t b) x := by
  letI : IsProbabilityMeasure μ := hμ.1
  let past := fun ω : BrownianPath d ↦
    ((if (s : ℝ≥0∞) < scaledExit B σ x ω then 1 else 0 : ℝ), x + σ • ω s)
  let F := fun p : (ℝ × Euc d) × BrownianPath d ↦
    p.1.1 * (if (t : ℝ≥0∞) < scaledExit B σ p.1.2 p.2
      then b (p.1.2 + σ • p.2 t) else 0)
  have hpast : Measurable past :=
    (measurable_killed_past hB σ x s).mono ((brownianNaturalFiltration d).le s) le_rfl
  have hF := measurable_fst.fst.mul
    ((measurable_killed_integrand_fixed hB σ t hb).comp
      (measurable_fst.snd.prodMk measurable_snd))
  have hprod := (indepFun_killed_past_shift hB σ hμ x s).map_prod_eq_prod_map_map
    hpast.aemeasurable (measurable_shiftedBrownianPath s).aemeasurable
  rw [standardBrownianLaw_map_shift hμ s] at hprod
  have hpastbound : ∀ᵐ a ∂μ.map past, |a.1| ≤ (1 : ℝ) := by
    apply (ae_map_iff hpast.aemeasurable
      (measurableSet_le measurable_fst.abs measurable_const)).mpr
    exact Filter.Eventually.of_forall fun ω ↦ by
      dsimp [past]
      split_ifs <;> norm_num
  have hFintegrable : Integrable F ((μ.map past).prod μ) :=
    integrable_killed_product hB σ t hb hC hbC hpastbound
  calc
    killed B σ μ (s + t) b x = ∫ ω, F (past ω, shiftedBrownianPath s ω) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ killed_integrand_add hB σ b x ω s t
    _ = ∫ p, F p ∂((μ.map past).prod μ) := by
      rw [← hprod]
      exact (integral_map (hpast.prodMk
        (measurable_shiftedBrownianPath s)).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ a, ∫ η, F (a, η) ∂μ ∂(μ.map past) := integral_prod F hFintegrable
    _ = ∫ ω, ∫ η, F (past ω, η) ∂μ ∂μ :=
      integral_map hpast.aemeasurable
        hF.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    _ = killed B σ μ s (killed B σ μ t b) x := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      change (∫ η, (past ω).1 *
        (if (t : ℝ≥0∞) < scaledExit B σ (past ω).2 η
          then b ((past ω).2 + σ • η t) else 0) ∂μ) = _
      rw [integral_const_mul]
      change (if (s : ℝ≥0∞) < scaledExit B σ x ω then 1 else 0) *
        killed B σ μ t b (x + σ • ω s) = _
      by_cases hs : (s : ℝ≥0∞) < scaledExit B σ x ω
      · simp only [if_pos hs, one_mul]
      · simp only [if_neg hs, zero_mul]

end

end LatticeProb
