/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianSkeletonLaw at commit fdb5cad; local import paths and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.DependentKernelMap
import LatticeProb.Bonanno.BouRabeeGwynne.TrajectoryIdentification

/-! Exact joint law of the successive genuine Brownian excursions. The proof
uses the observed full history at the original path's stopping clock. -/

open MeasureTheory ProbabilityTheory Set Preorder
open scoped NNReal ENNReal
namespace BouRabeeGwynne

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

private lemma measurable_skeletonConstantExcursion :
    Measurable (fun x : Euc d ↦ ContinuousMap.const unitInterval x) :=
  ContinuousMap.measurable_iff_eval.mpr (fun _ ↦ measurable_id)

noncomputable def brownianSkeletonInitialLaw (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (μ : Measure (BrownianPath d)) [IsFiniteMeasure μ]
    (z : Euc d) (j₀ : J) :
    Measure (Bool × C(unitInterval, Euc d)) :=
  selectedExcursionKernel (fun j ↦ brownianExcursionKernel (hU j) μ)
    (ContinuousMap.const unitInterval) measurable_skeletonConstantExcursion (some j₀, z)

instance brownianSkeletonInitialLaw_isProbability (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (z : Euc d) (j₀ : J) :
    IsProbabilityMeasure (brownianSkeletonInitialLaw U hU μ z j₀) := by
  unfold brownianSkeletonInitialLaw
  infer_instance

noncomputable def brownianSkeletonKernel (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (μ : Measure (BrownianPath d)) [IsFiniteMeasure μ]
    (selector : ℕ → Euc d → Option J) (hselector : ∀ n, Measurable (selector n))
    (n : ℕ) : Kernel (Finset.Iic n → Bool × C(unitInterval, Euc d))
      (Bool × C(unitInterval, Euc d)) :=
  (absorbingExcursionKernel (fun j ↦ brownianExcursionKernel (hU j) μ)
    (fun c ↦ c 1) (ContinuousMap.measurable_eval 1)
    (ContinuousMap.const unitInterval) measurable_skeletonConstantExcursion
    (selector (n + 1)) (hselector (n + 1))).comap
      (fun h ↦ h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance brownianSkeletonKernel_isMarkov (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (selector : ℕ → Euc d → Option J) (hselector : ∀ n, Measurable (selector n)) (n : ℕ) :
    IsMarkovKernel (brownianSkeletonKernel U hU μ selector hselector n) := by
  unfold brownianSkeletonKernel
  infer_instance

theorem measurable_brownianSkeletonHistory_stopping (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    {selector : ℕ → Euc d → Option J} (hselector : ∀ n, Measurable (selector n)) (n : ℕ) :
    Measurable[(isStoppingTime_brownianSkeletonClock U hU z j₀ hselector n).measurableSpace]
      (fun ω ↦ frestrictLe n (fun k ↦ brownianSkeletonExcursion U z j₀ selector k ω)) := by
  let : MeasurableSpace (BrownianPath d) :=
    (isStoppingTime_brownianSkeletonClock U hU z j₀ hselector n).measurableSpace
  apply Measurable.of_eval
  intro i
  have hmono (ω : BrownianPath d) :
      Monotone (fun k ↦ (brownianSkeletonClock U z j₀ selector k ω).2) :=
    monotone_nat_of_le_succ (fun k ↦ brownianSkeletonClock_time_le_succ U z j₀ selector k ω)
  exact (measurable_brownianSkeletonExcursion_stopping U hU z j₀ hselector i.val).mono
    ((isStoppingTime_brownianSkeletonClock U hU z j₀ hselector i.val).measurableSpace_mono
      (isStoppingTime_brownianSkeletonClock U hU z j₀ hselector n)
      (fun ω ↦ hmono ω (Finset.mem_Iic.mp i.property))) le_rfl

theorem standardBrownianLaw_skeleton_history_next (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (hselector : ∀ n, Measurable (selector n)) (n : ℕ) :
    μ.map (fun ω ↦
      (frestrictLe n (fun k ↦ brownianSkeletonExcursion U z j₀ selector k ω),
        brownianSkeletonExcursion U z j₀ selector (n + 1) ω)) =
      μ.map (fun ω ↦ frestrictLe n (fun k ↦ brownianSkeletonExcursion U z j₀ selector k ω))
        ⊗ₘ brownianSkeletonKernel U hU μ selector hselector n := by
  let : IsProbabilityMeasure μ := hμ.1
  let H := Finset.Iic n → Bool × C(unitInterval, Euc d)
  let history : BrownianPath d → H :=
    fun ω ↦ frestrictLe n (fun k ↦ brownianSkeletonExcursion U z j₀ selector k ω)
  let future : BrownianPath d → BrownianPath d :=
    fun ω ↦ shiftedBrownianPath (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal ω
  let F : H → BrownianPath d → Bool × C(unitInterval, Euc d) :=
    fun h ω ↦ absorbingBrownianExcursionSampler U (selector (n + 1))
      (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) ω
  have htime := isStoppingTime_brownianSkeletonClock U hU z j₀ hselector n
  have hfinite := standardBrownianLaw_ae_finiteSkeletonClock hd hμ U hU hUb z j₀ hselector n
  have hH : Measurable[htime.measurableSpace] history :=
    measurable_brownianSkeletonHistory_stopping U hU z j₀ hselector n
  have hHm : Measurable history := hH.mono htime.measurableSpace_le le_rfl
  have hfuture : Measurable future := measurable_variable_shiftedBrownianPath
    (ENNReal.measurable_toNNReal.comp htime.measurable')
  have hlast : Measurable (fun h : H ↦ h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) :=
    measurable_pi_apply _
  have hargs : Measurable (fun p : H × BrownianPath d ↦
      (p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩, p.2)) :=
    (hlast.comp measurable_fst).prodMk measurable_snd
  have hF : Measurable (fun p : H × BrownianPath d ↦ F p.1 p.2) := by
    simpa only [F, Function.comp_def] using
      (measurable_absorbingBrownianExcursionSampler_joint U hU
        (selector (n + 1)) (hselector (n + 1))).comp hargs
  have hjoint := standardBrownianLaw_stopping_history_joint hμ htime hfinite hH
  have hmap : ∀ h : H, μ.map (F h) = brownianSkeletonKernel U hU μ selector hselector n h :=
    fun h ↦ absorbingBrownianExcursionSampler_map U hU μ
      (selector (n + 1)) (hselector (n + 1)) _
  have hprod := compProd_map_dependent_of_kernel_map (μ.map history)
    (Kernel.const H μ) (brownianSkeletonKernel U hU μ selector hselector n)
    id F measurable_id hF hmap
  rw [Measure.compProd_const, Measure.map_id] at hprod
  calc
    _ = μ.map (fun ω ↦ (history ω, F (history ω) (future ω))) := by
      apply Measure.map_congr
      filter_upwards [hfinite] with ω hω
      exact congrArg (fun e ↦ (history ω, e))
        (brownianSkeletonExcursion_eq_absorbingSampler U z j₀ selector n ω hω)
    _ = (μ.map (fun ω ↦ (history ω, future ω))).map (fun p ↦ (p.1, F p.1 p.2)) := by
      rw [Measure.map_map (measurable_fst.prodMk hF) (hHm.prodMk hfuture)]
      rfl
    _ = _ := by rw [hjoint]; exact hprod

/-- The original path's full excursion sequence has exactly the genuine
history-dependent trajectory law, with state zero the first real excursion. -/
theorem standardBrownianLaw_skeleton_map (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (hselector : ∀ n, Measurable (selector n)) :
    μ.map (fun ω k ↦ brownianSkeletonExcursion U z j₀ selector k ω) =
      Kernel.trajMeasure (X := fun _ ↦ Bool × C(unitInterval, Euc d))
        (brownianSkeletonInitialLaw U hU μ z j₀)
        (brownianSkeletonKernel U hU μ selector hselector) := by
  let : IsProbabilityMeasure μ := hμ.1
  apply TrajectoryCoupling.map_eq_trajMeasure_of_history_next μ _
    (Measurable.of_eval (fun n ↦ measurable_brownianSkeletonExcursion U hU z j₀ hselector n))
  · exact selectedBrownianExcursionSampler_map U hU μ (some j₀, z)
  · exact standardBrownianLaw_skeleton_history_next hd hμ U hU hUb z j₀ selector hselector

end BouRabeeGwynne
