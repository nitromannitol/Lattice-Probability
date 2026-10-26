import LatticeProb.Prob.ErgodicClosedSets
import LatticeProb.Prob.Percolation.LatticeBondErgodicityConsumer
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A nonconstant closed-set family under canonical bond ergodicity

Assign the singleton zero to the all-open configuration event and the singleton one to
its complement. This family is pointwise nonconstant, has measurable open hits, and is
invariant under the actual vertical unit translation, hence is almost surely constant.
-/

namespace LatticeProb.Prob

open MeasureTheory LatticeProb.Percolation

/-- A closed singleton family distinguishing the actual all-open event from its complement. -/
noncomputable def allOpenSingletonFamily (ω : Configuration 2) : Set ℝ := by
  classical
  exact if ∀ e, ω e = true then {0} else {1}

/-- Every member of the all-open singleton family is closed. -/
theorem allOpenSingletonFamily_isClosed (ω : Configuration 2) :
    IsClosed (allOpenSingletonFamily ω) := by
  classical
  unfold allOpenSingletonFamily
  split_ifs <;> exact isClosed_singleton

/-- Every open-hit event of this family is measurable, as a two-piece event. -/
theorem allOpenSingletonFamily_hit_measurable (U : Set ℝ) :
    MeasurableSet {ω | (allOpenSingletonFamily ω ∩ U).Nonempty} := by
  classical
  have heq : {ω | (allOpenSingletonFamily ω ∩ U).Nonempty} =
      ({ω : Configuration 2 | ∀ e, ω e = true} ∩ {ω : Configuration 2 | (0 : ℝ) ∈ U}) ∪
      ({ω : Configuration 2 | ∀ e, ω e = true}ᶜ ∩ {ω : Configuration 2 | (1 : ℝ) ∈ U}) := by
    ext ω
    by_cases hω : ∀ e, ω e = true
    · simp only [Set.mem_setOf_eq, allOpenSingletonFamily, hω, forall_true_iff, ite_true,
        Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, true_and, not_true_eq_false,
        false_and, or_false, Set.singleton_inter_nonempty]
    · simp only [Set.mem_setOf_eq, allOpenSingletonFamily, hω, ite_false,
        Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, false_and, not_false_eq_true,
        true_and, false_or, Set.singleton_inter_nonempty]
  rw [heq]
  exact (allBondsOpen_measurable.inter (MeasurableSet.const _)).union
    (allBondsOpen_measurable.compl.inter (MeasurableSet.const _))

/-- Literal all-open invariance gives full covariance of the closed singleton family. -/
theorem allOpenSingletonFamily_vertical_covariant (ω : Configuration 2) :
    allOpenSingletonFamily (configurationTranslation (unit (1 : Fin 2)) ω) =
      allOpenSingletonFamily ω := by
  classical
  have hinv : (∀ e, configurationTranslation (unit (1 : Fin 2)) ω e = true) ↔
      ∀ e, ω e = true := Set.ext_iff.mp allBondsOpen_vertical_invariant ω
  simp only [allOpenSingletonFamily, hinv]

/-- Actual canonical vertical ergodicity makes the closed singleton family deterministic. -/
theorem allOpenSingletonFamily_ae_constant (p : unitInterval) :
    ∃ S : Set ℝ, IsClosed S ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, allOpenSingletonFamily ω = S :=
  exists_isClosed_ae_eq_of_ergodic (verticalUnit_configurationTranslation_ergodic p)
    allOpenSingletonFamily allOpenSingletonFamily_isClosed
    (fun U _ => allOpenSingletonFamily_hit_measurable U)
    allOpenSingletonFamily_vertical_covariant

/-- The all-open and all-closed configurations realize different closed sets. -/
theorem allOpenSingletonFamily_nonconstant :
    allOpenSingletonFamily (fun _ : Bond 2 => true) = {0} ∧
    allOpenSingletonFamily (fun _ : Bond 2 => false) = {1} ∧
    allOpenSingletonFamily (fun _ : Bond 2 => true) ≠
      allOpenSingletonFamily (fun _ : Bond 2 => false) := by
  classical
  have hopen : allOpenSingletonFamily (fun _ : Bond 2 => true) = {0} :=
    if_pos allBondsOpen_nontrivial.1
  have hclosed : allOpenSingletonFamily (fun _ : Bond 2 => false) = {1} :=
    if_neg allBondsOpen_nontrivial.2
  rw [hopen, hclosed]
  refine ⟨rfl, rfl, ?_⟩
  simp only [ne_eq, Set.singleton_eq_singleton_iff, zero_ne_one, not_false_eq_true]

end LatticeProb.Prob
