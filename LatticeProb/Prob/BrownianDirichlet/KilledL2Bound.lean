import LatticeProb.Prob.BrownianDirichlet.KilledKernel
import LatticeProb.Prob.BrownianDirichlet.Subinvariance
import Mathlib.Probability.Moments.Variance

/-!
# Square contraction for killed Brownian evaluation

Jensen's inequality and volume subinvariance give the square integral bound.
Consequently the kernel respects almost everywhere equality and contracts the L² norm.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

namespace LatticeProb

variable {d : ℕ}

noncomputable section

/-- Jensen's square inequality for bounded measurable killed evaluation. -/
lemma sq_killed_le {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} [IsProbabilityMeasure μ] (t : ℝ≥0)
    {b : Euc d → ℝ} (hb : Measurable b) {C : ℝ} (hC : 0 ≤ C)
    (hbC : ∀ y, |b y| ≤ C) (x : Euc d) :
    (killed B σ μ t b x) ^ 2 ≤ killed B σ μ t (fun y ↦ b y ^ 2) x := by
  let f := fun ω ↦ if (t : ℝ≥0∞) < scaledExit B σ x ω
    then b (x + σ • ω t) else 0
  have hf : MemLp f 2 μ := MemLp.of_bound
    (integrable_killed_integrand hB σ t hb hC hbC x).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω ↦ by
      dsimp [f]
      split_ifs
      · exact (Real.norm_eq_abs _).trans_le (hbC _)
      · simpa only [norm_zero, abs_zero] using hC)
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  have heq : (∫ ω, f ω ^ 2 ∂μ) = killed B σ μ t (fun y ↦ b y ^ 2) x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω ↦ by
      dsimp [f]
      split_ifs <;> simp only [sq, mul_zero]
  change 0 ≤ (∫ ω, f ω ^ 2 ∂μ) - (killed B σ μ t b x) ^ 2 at h
  rw [heq] at h
  exact sub_nonneg.mp h

/-- The real square expectation agrees with the nonnegative killed integral. -/
lemma killed_sq_eq_killedNN {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} [IsFiniteMeasure μ] (t : ℝ≥0)
    {b : Euc d → ℝ} (hb : Measurable b) {C : ℝ} (hC : 0 ≤ C)
    (hbC : ∀ y, |b y| ≤ C) (x : Euc d) :
    ENNReal.ofReal (killed B σ μ t (fun y ↦ b y ^ 2) x) =
      killedNN B σ μ t (fun y ↦ ENNReal.ofReal (b y ^ 2)) x := by
  have hbC2 : ∀ y, |b y ^ 2| ≤ C ^ 2 := by
    intro y
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 (hbC y)
  rw [killed, ofReal_integral_eq_lintegral_ofReal
    (integrable_killed_integrand hB σ t (hb.pow_const 2) (sq_nonneg C) hbC2 x)]
  · unfold killedNN
    apply lintegral_congr
    intro ω
    split_ifs <;> simp only [ENNReal.ofReal_zero]
  · exact Filter.Eventually.of_forall fun ω ↦ by
      dsimp only [Pi.zero_apply]
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl

/-- Volume subinvariance bounds the square integral of the killed expectation. -/
lemma lintegral_sq_killed_le {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0)
    {b : Euc d → ℝ} (hb : Measurable b) {C : ℝ} (hC : 0 ≤ C)
    (hbC : ∀ y, |b y| ≤ C) :
    (∫⁻ x in B, ENNReal.ofReal ((killed B σ μ t b x) ^ 2)) ≤
      ∫⁻ x in B, ENNReal.ofReal (b x ^ 2) := by
  letI : IsProbabilityMeasure μ := hμ.1
  calc
    _ ≤ ∫⁻ x in B, killedNN B σ μ t (fun y ↦ ENNReal.ofReal (b y ^ 2)) x := by
      apply lintegral_mono
      intro x
      rw [← killed_sq_eq_killedNN hB σ t hb hC hbC x]
      exact ENNReal.ofReal_le_ofReal (sq_killed_le hB σ t hb hC hbC x)
    _ ≤ _ := lintegral_killedNN_le hB σ hμ t (hb.pow_const 2).ennreal_ofReal

/-- Bounded measurable data equal almost everywhere have equal killed evaluations a.e. -/
lemma killed_congr_ae {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0)
    {b b' : Euc d → ℝ} (hb : Measurable b) (hb' : Measurable b')
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbC : ∀ y, |b y| ≤ C) (hbD : ∀ y, |b' y| ≤ D)
    (heq : b =ᵐ[volume.restrict B] b') :
    killed B σ μ t b =ᵐ[volume.restrict B] killed B σ μ t b' := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hdiff : ∀ y, |b y - b' y| ≤ C + D := fun y ↦
    (abs_sub (b y) (b' y)).trans (add_le_add (hbC y) (hbD y))
  have hbound := lintegral_sq_killed_le hB σ hμ t (hb.sub hb')
    (add_nonneg hC hD) hdiff
  have hrhs : (∫⁻ x in B, ENNReal.ofReal ((b x - b' x) ^ 2)) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [heq] with x hx
    simp only [hx, sub_self, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero,
      Pi.zero_apply]
  simp only [Pi.sub_apply] at hbound
  rw [hrhs] at hbound
  have hz := (lintegral_eq_zero_iff
    ((measurable_killed hB σ t (hb.sub hb')).pow_const 2).ennreal_ofReal).1
    (le_antisymm hbound bot_le)
  filter_upwards [hz] with x hx
  have hx0 : killed B σ μ t (fun y ↦ b y - b' y) x = 0 := by
    have hs : (killed B σ μ t (fun y ↦ b y - b' y) x) ^ 2 ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp hx
    exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
  have hadd := killed_add_data hB σ (μ := μ) t (c := fun y ↦ (-1 : ℝ) * b' y) hb
    ((measurable_const : Measurable (fun _ : Euc d ↦ (-1 : ℝ))).mul hb') hC hD hbC
    (fun y ↦ by simpa only [Pi.mul_apply, neg_one_mul, abs_neg] using hbD y) x
  have hsmul := killed_smul_data B σ μ t (-1) b' x
  simp only [neg_one_mul] at hadd hsmul
  have hsub : killed B σ μ t (fun y ↦ b y - b' y) x =
      killed B σ μ t b x - killed B σ μ t b' x := by
    simpa only [sub_eq_add_neg, hsmul] using hadd
  rw [hsub] at hx0
  exact sub_eq_zero.mp hx0

/-- The real L² seminorm is the square root of the nonnegative square integral. -/
lemma eLpNorm_two_eq_lintegral_sq {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : α → ℝ) :
    eLpNorm f 2 ν = (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  congr 1
  apply lintegral_congr
  intro x
  rw [ENNReal.rpow_two,
    ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2, Real.norm_eq_abs, sq_abs]

/-- Killed evaluation contracts the L² seminorm of bounded measurable data. -/
lemma eLpNorm_killed_le {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0)
    {b : Euc d → ℝ} (hb : Measurable b) {C : ℝ} (hC : 0 ≤ C)
    (hbC : ∀ y, |b y| ≤ C) :
    eLpNorm (killed B σ μ t b) 2 (volume.restrict B) ≤
      eLpNorm b 2 (volume.restrict B) := by
  rw [eLpNorm_two_eq_lintegral_sq, eLpNorm_two_eq_lintegral_sq]
  exact ENNReal.rpow_le_rpow (lintegral_sq_killed_le hB σ hμ t hb hC hbC)
    (by norm_num)

/-- On a finite-volume domain bounded measurable data give a killed L² function. -/
lemma memLp_killed {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0)
    [IsFiniteMeasure (volume.restrict B)]
    {b : Euc d → ℝ} (hb : Measurable b) {C : ℝ} (hC : 0 ≤ C)
    (hbC : ∀ y, |b y| ≤ C) : MemLp (killed B σ μ t b) 2 (volume.restrict B) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hbLp : MemLp b 2 (volume.restrict B) := MemLp.of_bound
    hb.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y ↦ (Real.norm_eq_abs _).trans_le (hbC y))
  exact ⟨(measurable_killed hB σ t hb).aestronglyMeasurable,
    (eLpNorm_killed_le hB σ hμ t hb hC hbC).trans_lt hbLp.2⟩

end

end LatticeProb
