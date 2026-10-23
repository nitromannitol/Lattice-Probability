import LatticeProb.Prob.JumpChain.Rates
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.StrongLaw

/-!
# Histories for the uniformized jump chain

Histories record a state and a clock interval at each natural-number index. The initial
state has the prescribed law, and each subsequent state is sampled from the uniformized
kernel. Every clock interval has the positive exponential law of the uniformization rate.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Set Preorder Function

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Type*}

/-- A history records the embedded chain and its successive clock intervals. -/
abbrev History (S : Type*) := ℕ → S × ℝ

namespace BoundedRates

/-- The exponential clock law gives no mass to nonpositive intervals. -/
theorem expMeasure_Iic_zero (rates : BoundedRates S) :
    expMeasure rates.R (Iic 0) = 0 := by
  letI := isProbabilityMeasure_expMeasure rates.R_pos
  rw [← ofReal_cdf, cdf_expMeasure_eq rates.R_pos]
  simp only [le_refl, ite_true, mul_zero, neg_zero, Real.exp_zero, sub_self,
    ENNReal.ofReal_zero]

/-- Exponential intervals are strictly positive almost surely. -/
theorem ae_expMeasure_pos (rates : BoundedRates S) :
    ∀ᵐ h ∂expMeasure rates.R, 0 < h := by
  rw [ae_iff]
  simpa only [Set.Iic, not_lt] using rates.expMeasure_Iic_zero

/-- The clock law is the exponential measure restricted to strictly positive intervals. -/
def clockLaw (rates : BoundedRates S) : Measure ℝ :=
  (expMeasure rates.R).restrict (Ioi 0)

/-- Restricting the exponential clock to positive intervals preserves its law. -/
theorem clockLaw_eq_expMeasure (rates : BoundedRates S) :
    rates.clockLaw = expMeasure rates.R := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact rates.ae_expMeasure_pos

/-- The positive clock law is a probability measure. -/
instance isProbabilityMeasure_clockLaw (rates : BoundedRates S) :
    IsProbabilityMeasure rates.clockLaw := by
  rw [rates.clockLaw_eq_expMeasure]
  exact isProbabilityMeasure_expMeasure rates.R_pos

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The next state follows the uniformized kernel, with an independent positive clock. -/
def historyStep (rates : BoundedRates S) (n : ℕ) :
    Kernel (↥(Finset.Iic n) → S × ℝ) (S × ℝ) :=
  (rates.kernel.comap (fun h ↦ (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1) (by fun_prop)).prod
    (Kernel.const _ rates.clockLaw)

/-- Every history transition is a probability kernel. -/
instance isMarkovKernel_historyStep (rates : BoundedRates S) (n : ℕ) :
    IsMarkovKernel (rates.historyStep n) := by
  unfold historyStep
  infer_instance

/-- The history law starts with an independent initial state and positive exponential clock. -/
def historyLaw (rates : BoundedRates S) (μ : Measure S) : Measure (History S) :=
  Kernel.trajMeasure (μ.prod rates.clockLaw) rates.historyStep

/-- A probability initial state law gives a probability law on infinite histories. -/
instance isProbabilityMeasure_historyLaw (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (rates.historyLaw μ) := by
  unfold historyLaw
  infer_instance

/-- The zeroth pair has exactly the prescribed product law. -/
theorem historyLaw_map_zero (rates : BoundedRates S) (μ : Measure S) :
    (rates.historyLaw μ).map (fun h ↦ h 0) = μ.prod rates.clockLaw := by
  have hmap : (Kernel.traj (X := fun _ ↦ S × ℝ) rates.historyStep 0).map (fun h ↦ h 0) =
      Kernel.deterministic
        (fun h : ↥(Finset.Iic 0) → S × ℝ ↦ h ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
        (by fun_prop) := by
    change (Kernel.traj (X := fun _ ↦ S × ℝ) rates.historyStep 0).map
      ((fun h : ↥(Finset.Iic 0) → S × ℝ ↦ h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
        frestrictLe 0) = _
    rw [Kernel.map_comp_right _ (measurable_frestrictLe _) (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Kernel.id_map]
  unfold historyLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), hmap, Measure.deterministic_comp_eq_map,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have heq : (fun h : ↥(Finset.Iic 0) → S × ℝ ↦ h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
      (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) ↦ S × ℝ)).symm = id := by
    funext x
    have hindex : (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : ↥(Finset.Iic 0)) = default :=
      Subsingleton.elim _ _
    dsimp only [Function.comp_apply, id_eq]
    rw [hindex]
    exact (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) ↦ S × ℝ)).apply_symm_apply x
  rw [heq, Measure.map_id]

/-- The initial embedded state has the requested initial law. -/
theorem historyLaw_map_initialState (rates : BoundedRates S) (μ : Measure S) :
    (rates.historyLaw μ).map (fun h ↦ (h 0).1) = μ := by
  change (rates.historyLaw μ).map (Prod.fst ∘ (fun h ↦ h 0)) = μ
  rw [← Measure.map_map measurable_fst (by fun_prop), rates.historyLaw_map_zero,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- A history step has the same exponential clock law at every input history. -/
theorem historyStep_map_clock (rates : BoundedRates S) (n : ℕ) :
    (rates.historyStep n).map Prod.snd = Kernel.const _ rates.clockLaw := by
  ext h : 1
  rw [Kernel.map_apply _ measurable_snd]
  unfold historyStep
  rw [Kernel.prod_apply, Measure.map_snd_prod, measure_univ, one_smul]

/-- The next clock is independent of the full preceding finite history. -/
theorem historyLaw_map_prefix_clock (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (rates.historyLaw μ).map (fun h ↦ (frestrictLe n h, (h (n + 1)).2)) =
      ((rates.historyLaw μ).map (frestrictLe n)).prod rates.clockLaw := by
  apply Measure.ext_prod
  intro a b ha hb
  have hclock (h : ↥(Finset.Iic n) → S × ℝ) :
      rates.historyStep n h (Prod.snd ⁻¹' b) = rates.clockLaw b := by
    have heq := congrArg (fun k : Kernel (↥(Finset.Iic n) → S × ℝ) ℝ ↦ k h b)
      (rates.historyStep_map_clock n)
    rw [Kernel.map_apply' _ measurable_snd _ hb] at heq
    exact heq
  calc
    _ = ((rates.historyLaw μ).map
        (fun h ↦ (frestrictLe n h, h (n + 1)))) (a ×ˢ (Prod.snd ⁻¹' b)) := by
      rw [Measure.map_apply (by fun_prop) (ha.prod hb),
        Measure.map_apply (by fun_prop) (ha.prod (measurable_snd hb))]
      rfl
    _ = (((rates.historyLaw μ).map (frestrictLe n)) ⊗ₘ rates.historyStep n)
        (a ×ˢ (Prod.snd ⁻¹' b)) := by
      have heq := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ ↦ S × ℝ) (μ₀ := μ.prod rates.clockLaw)
        (κ := rates.historyStep) (a := n)
      exact congrArg (fun ν ↦ ν (a ×ˢ (Prod.snd ⁻¹' b))) heq.symm
    _ = ((rates.historyLaw μ).map (frestrictLe n)) a * rates.clockLaw b := by
      rw [Measure.compProd_apply_prod ha (measurable_snd hb)]
      simp only [hclock, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
        univ_inter, mul_comm]
    _ = _ := (Measure.prod_prod _ _).symm

/-- Each recorded clock interval has the positive exponential law. -/
theorem historyLaw_map_clock (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (rates.historyLaw μ).map (fun h ↦ (h n).2) = rates.clockLaw := by
  cases n with
  | zero =>
    change (rates.historyLaw μ).map (Prod.snd ∘ (fun h ↦ h 0)) = _
    rw [← Measure.map_map measurable_snd (by fun_prop), rates.historyLaw_map_zero,
      Measure.map_snd_prod, measure_univ, one_smul]
  | succ n =>
    letI : IsProbabilityMeasure ((rates.historyLaw μ).map (frestrictLe n)) :=
      Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
    have heq := congrArg (fun ν ↦ ν.map Prod.snd) (rates.historyLaw_map_prefix_clock μ n)
    rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod,
      measure_univ, one_smul] at heq
    exact heq

/-- The next clock is independent of all observations of the preceding finite history. -/
theorem indepFun_prefix_clock (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) :
    IndepFun (frestrictLe n) (fun h : History S ↦ (h (n + 1)).2)
      (rates.historyLaw μ) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_frestrictLe n).aemeasurable
    (measurable_pi_apply (n + 1)).snd.aemeasurable).mpr
  rw [rates.historyLaw_map_clock, rates.historyLaw_map_prefix_clock]

/-- All recorded holding intervals are strictly positive almost surely. -/
theorem ae_clock_pos (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] :
    ∀ᵐ h ∂rates.historyLaw μ, ∀ n, 0 < (h n).2 := by
  rw [ae_all_iff]
  intro n
  apply ae_of_ae_map ((measurable_pi_apply n).snd.aemeasurable)
  rw [rates.historyLaw_map_clock, rates.clockLaw_eq_expMeasure]
  exact rates.ae_expMeasure_pos

end BoundedRates

/-- The time of the `n`th clock ring, with time zero before the first clock interval. -/
def jumpTime (h : History S) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (h k).2

/-- The initial clock-ring time is zero. -/
theorem jumpTime_zero (h : History S) : jumpTime h 0 = 0 := by
  simp only [jumpTime, Finset.range_zero, Finset.sum_empty]

/-- Consecutive ring times differ by the next recorded holding interval. -/
theorem jumpTime_succ (h : History S) (n : ℕ) :
    jumpTime h (n + 1) = jumpTime h n + (h n).2 := by
  exact Finset.sum_range_succ _ _

/-- Every clock-ring time is measurable as a function of the history. -/
@[fun_prop]
theorem measurable_jumpTime [MeasurableSpace S] (n : ℕ) :
    Measurable (fun h : History S ↦ jumpTime h n) := by
  unfold jumpTime
  fun_prop

namespace BoundedRates

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Distinct clock intervals are independent for every probability initial state law. -/
theorem pairwise_indepFun_clock (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] :
    Pairwise (fun i j ↦ IndepFun (fun h : History S ↦ (h i).2)
      (fun h : History S ↦ (h j).2) (rates.historyLaw μ)) := by
  have ordered (i j : ℕ) (hij : i < j) :
      IndepFun (fun h : History S ↦ (h i).2) (fun h ↦ (h j).2)
        (rates.historyLaw μ) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (rates.indepFun_prefix_clock μ n).comp
      (show Measurable
        (fun h : ↥(Finset.Iic n) → S × ℝ ↦ (h ⟨i, Finset.mem_Iic.mpr (by omega)⟩).2)
        by fun_prop)
      measurable_id
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact ordered i j h
  · exact (ordered j i h).symm

/-- The sum of the exponential holding intervals diverges almost surely. -/
theorem ae_tendsto_jumpTime (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] :
    ∀ᵐ h ∂rates.historyLaw μ, Filter.Tendsto (jumpTime h) Filter.atTop Filter.atTop := by
  let clip : ℝ → ℝ := fun x ↦ max 0 (min x 1)
  have clip_nonneg (x : ℝ) : 0 ≤ clip x := le_max_left _ _
  have clip_le_one (x : ℝ) : clip x ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have clip_pos {x : ℝ} (hx : 0 < x) : 0 < clip x :=
    lt_max_of_lt_right (lt_min hx zero_lt_one)
  have mclip : Measurable clip := by fun_prop
  let X : ℕ → History S → ℝ := fun n h ↦ clip (h n).2
  have mint (n : ℕ) : Integrable (X n) (rates.historyLaw μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall fun h ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (clip_nonneg _)]
      exact clip_le_one _
  have ident (n : ℕ) : IdentDistrib (X n) (X 0) (rates.historyLaw μ)
      (rates.historyLaw μ) := by
    apply IdentDistrib.comp _ mclip
    exact ⟨(measurable_pi_apply n).snd.aemeasurable,
      (measurable_pi_apply 0).snd.aemeasurable, by rw [rates.historyLaw_map_clock,
      rates.historyLaw_map_clock]⟩
  have independent : Pairwise ((· ⟂ᵢ[rates.historyLaw μ] ·) on X) := by
    intro i j hij
    exact (rates.pairwise_indepFun_clock μ hij).comp mclip mclip
  have mean_pos : 0 < ∫ h, X 0 h ∂rates.historyLaw μ := by
    by_contra hnot
    have hzero : ∫ h, X 0 h ∂rates.historyLaw μ = 0 :=
      le_antisymm (le_of_not_gt hnot) (integral_nonneg fun h ↦ clip_nonneg _)
    have hz := (integral_eq_zero_iff_of_nonneg (fun h ↦ clip_nonneg _) (mint 0)).mp hzero
    have hfalse : ∀ᵐ h ∂rates.historyLaw μ, False := by
      filter_upwards [hz, rates.ae_clock_pos μ] with h hh hp
      exact (ne_of_gt (clip_pos (hp 0))) hh
    exact (IsProbabilityMeasure.ne_zero (rates.historyLaw μ)) (by simpa using hfalse)
  filter_upwards [strong_law_ae_real X (mint 0) independent ident,
    rates.ae_clock_pos μ] with h hlimit hpos
  have ht := hlimit.pos_mul_atTop mean_pos
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ))
      Filter.atTop Filter.atTop)
  have hdiv : (fun n : ℕ ↦ ((∑ k ∈ Finset.range n, X k h) / n) * n) =
      (fun n ↦ ∑ k ∈ Finset.range n, X k h) := by
    funext n
    cases n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_div,
        zero_mul]
    | succ n => exact div_mul_cancel₀ _ (by positivity)
  rw [hdiv] at ht
  apply Filter.tendsto_atTop_mono _ ht
  intro n
  apply Finset.sum_le_sum
  intro k hk
  exact max_le (hpos k).le (min_le_left _ _)

end BoundedRates

end

end LatticeProb.JumpChain
