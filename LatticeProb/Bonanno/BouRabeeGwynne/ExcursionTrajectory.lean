/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ExcursionTrajectory at commit fdb5cad; local import paths and two deprecated proof names are updated. -/
import LatticeProb.Bonanno.BouRabeeGwynne.TrajectoryCoupling
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionConcatenation
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws

/-! Measurable finite excursion chains extracted from the actual trajectory
law. Consecutive endpoints agree almost surely because the transition kernel
starts each new excursion at the preceding endpoint. The constant fallback
only defines the extraction on the null set of incompatible trajectories. -/

open MeasureTheory ProbabilityTheory Set Preorder
open scoped unitInterval ENNReal

namespace BouRabeeGwynne
namespace TrajectoryCoupling

/-- A measurable one-step support relation holds along the actual trajectory.
The relation may depend on the entire history. -/
theorem ae_next_relation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : (n : ℕ) → Kernel (Finset.Iic n → X) X) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) (R : (Finset.Iic n → X) × X → Prop)
    (hR : MeasurableSet {p | R p})
    (hstep : ∀ h, ∀ᵐ x ∂κ n h, R (h, x)) :
    ∀ᵐ ω ∂Kernel.trajMeasure (X := fun _ => X) μ κ,
      R (frestrictLe n ω, ω (n + 1)) := by
  have hprod : ∀ᵐ p ∂((Kernel.trajMeasure (X := fun _ => X) μ κ).map
      (frestrictLe n) ⊗ₘ κ n), R p :=
    Measure.ae_compProd_of_ae_ae hR (Filter.Eventually.of_forall hstep)
  rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure] at hprod
  exact ae_of_ae_map (by fun_prop) hprod

end TrajectoryCoupling

namespace ExcursionTrajectory

abbrev Excursion (d : ℕ) := C(unitInterval, EuclideanSpace ℝ (Fin d))

/-- The actual first `n+1` excursions have matching consecutive endpoints. -/
def compatiblePaths (n d : ℕ) : Set (ℕ → Excursion d) :=
  {ω | ∀ i j : Fin (n + 1), i.succ = j.castSucc → ω i.val 1 = ω j.val 0}

lemma measurableSet_compatiblePaths (n d : ℕ) :
    MeasurableSet (compatiblePaths n d) := by
  simp only [compatiblePaths, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_eq_fun
    ((ContinuousMap.measurable_eval 1).comp (measurable_pi_apply i.val))
    ((ContinuousMap.measurable_eval 0).comp (measurable_pi_apply j.val))

noncomputable def zeroChain (n d : ℕ) : ExcursionChain n d :=
  ⟨fun _ => ContinuousMap.const _ 0, fun _ _ _ => rfl⟩

/-- Extract the actual finite prefix whenever its endpoints agree. -/
noncomputable def prefixChain (n d : ℕ) (ω : ℕ → Excursion d) : ExcursionChain n d := by
  classical
  exact if h : ω ∈ compatiblePaths n d then ⟨fun i => ω i.val, h⟩ else zeroChain n d

lemma measurable_prefixChain (n d : ℕ) : Measurable (prefixChain n d) := by
  classical
  let F : compatiblePaths n d → ExcursionChain n d :=
    fun ω => ⟨fun i => ω.val i.val, ω.property⟩
  have hF : Measurable F := by
    apply Measurable.subtype_mk
    exact Measurable.of_eval fun _ => measurable_subtype_coe.eval
  exact hF.dite measurable_const (measurableSet_compatiblePaths n d)

lemma prefixChain_apply {n d : ℕ} {ω : ℕ → Excursion d}
    (hω : ω ∈ compatiblePaths n d) (i : Fin (n + 1)) :
    (prefixChain n d ω).val i = ω i.val := by
  simp only [prefixChain, dite_eq_left hω]

/-- A genuine Markov excursion kernel produces compatible finite chains with
probability one. The starting endpoint condition is a one-step support fact,
not an assumed full-path gluing or marginal identity. -/
theorem ae_compatiblePaths {d : ℕ}
    (μ : Measure (Excursion d)) [IsProbabilityMeasure μ]
    (κ : (n : ℕ) → Kernel (Finset.Iic n → Excursion d) (Excursion d))
    [∀ n, IsMarkovKernel (κ n)]
    (hstart : ∀ n h, ∀ᵐ c ∂κ n h, c 0 = h ⟨n, by simp⟩ 1)
    (k : ℕ) :
    ∀ᵐ ω ∂Kernel.trajMeasure (X := fun _ => Excursion d) μ κ,
      ω ∈ compatiblePaths k d := by
  have hnext (n : ℕ) :
      ∀ᵐ ω ∂Kernel.trajMeasure (X := fun _ => Excursion d) μ κ,
        ω (n + 1) 0 = ω n 1 := by
    apply TrajectoryCoupling.ae_next_relation μ κ n
      (fun p => p.2 0 = p.1 ⟨n, by simp⟩ 1)
    · exact measurableSet_eq_fun
        ((ContinuousMap.measurable_eval 0).comp measurable_snd)
        ((ContinuousMap.measurable_eval 1).comp
          ((measurable_pi_apply (⟨n, by simp⟩ : Finset.Iic n)).comp measurable_fst))
    · exact hstart n
  filter_upwards [ae_all_iff.mpr hnext] with ω hω
  intro i j hij
  have hindex : i.val + 1 = j.val := congrArg Fin.val hij
  exact ((hω i.val).symm.trans (congrArg (fun m => ω m 0) hindex))

/-- The measurable curve represented by the actual finite excursion prefix,
using the chosen deterministic time partition. -/
noncomputable def concatenatedCurve {n d : ℕ} (P : TimePartition n)
    (ω : ℕ → Excursion d) : CurveSpace d :=
  CurveSpace.project (P.concatenate (prefixChain n d ω))

lemma measurable_concatenatedCurve {n d : ℕ} (P : TimePartition n) :
    Measurable (concatenatedCurve (d := d) P) :=
  CurveSpace.continuous_project.measurable.comp
    (P.measurable_concatenate.comp (measurable_prefixChain n d))

end ExcursionTrajectory
end BouRabeeGwynne
