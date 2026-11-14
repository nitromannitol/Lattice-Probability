/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkStoppedHistory at commit fdb5cad; local imports are rewritten and two unused-section-variable lint checks are disabled. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkJointRestart
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-! Measurable observed histories and countable decomposition at a genuine
almost surely finite stopping time. The value at infinity is only a measurable
totalization and is not asserted to be a natural-number-valued stopping time. -/

open MeasureTheory ProbabilityTheory Set Preorder

namespace BouRabeeGwynne
namespace TrajectoryCoupling

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma compProd_restrict_first (μ : Measure X) [SFinite μ] (κ : Kernel X Y)
    [IsSFiniteKernel κ] {s : Set X} (hs : MeasurableSet s) :
    μ.restrict s ⊗ₘ κ = (μ ⊗ₘ κ).restrict (Prod.fst ⁻¹' s) := by
  ext t ht
  rw [Measure.compProd_apply ht, Measure.restrict_apply ht,
    Measure.compProd_apply (ht.inter (hs.preimage measurable_fst)),
    ← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    congr 1
    ext y
    simp [hx]
  · rw [Set.indicator_of_notMem hx]
    have he : Prod.mk x ⁻¹' (t ∩ Prod.fst ⁻¹' s) = ∅ := by
      ext y
      simp [hx]
    simp [he]

end TrajectoryCoupling

namespace FiniteConductanceNetwork

variable {V : Type*} [MeasurableSpace V]

/-- A finite history encoded by its length and constant terminal padding. -/
def paddedHistory (n : ℕ) (h : Finset.Iic n → V) : ℕ × (ℕ → V) :=
  (n, fun k => h ⟨min k n, Finset.mem_Iic.mpr (min_le_right _ _)⟩)

lemma measurable_paddedHistory (n : ℕ) : Measurable (paddedHistory (V := V) n) :=
  measurable_const.prodMk (Measurable.of_eval fun _ => measurable_pi_apply _)

def observedHistory (τ : (ℕ → V) → WithTop ℕ) (ω : ℕ → V) : ℕ × (ℕ → V) :=
  paddedHistory ((τ ω).untopD 0) (frestrictLe ((τ ω).untopD 0) ω)

def futureAt (τ : (ℕ → V) → WithTop ℕ) (ω : ℕ → V) : ℕ → V :=
  walkShift ((τ ω).untopD 0) ω

lemma measurable_observedHistory {τ : (ℕ → V) → WithTop ℕ} (hτ : Measurable τ) :
    Measurable (observedHistory τ) := by
  have hm : Measurable (fun p : (ℕ → V) × ℕ =>
      paddedHistory p.2 (frestrictLe p.2 p.1)) :=
    measurable_from_prod_countable_left fun n =>
      (measurable_paddedHistory n).comp (measurable_frestrictLe n)
  exact hm.comp (measurable_id.prodMk (hτ.untopD 0))

lemma measurable_futureAt {τ : (ℕ → V) → WithTop ℕ} (hτ : Measurable τ) :
    Measurable (futureAt τ) := by
  have hm : Measurable (fun p : (ℕ → V) × ℕ => walkShift p.2 p.1) :=
    measurable_from_prod_countable_left fun n => measurable_walkShift n
  exact hm.comp (measurable_id.prodMk (hτ.untopD 0))

set_option linter.unusedSectionVars false in
lemma observedHistory_of_eq {τ : (ℕ → V) → WithTop ℕ} {ω : ℕ → V} {n : ℕ}
    (hτ : τ ω = n) : observedHistory τ ω = paddedHistory n (frestrictLe n ω) := by
  change ((τ ω).untopD 0, fun k => ω (min k ((τ ω).untopD 0))) =
    (n, fun k => ω (min k n))
  rw [hτ]
  rfl

set_option linter.unusedSectionVars false in
lemma futureAt_of_eq {τ : (ℕ → V) → WithTop ℕ} {ω : ℕ → V} {n : ℕ}
    (hτ : τ ω = n) : futureAt τ ω = walkShift n ω := by
  simp only [futureAt, hτ]
  rfl

lemma stopping_event_prefix {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ) (n : ℕ) :
    ∃ s : Set (Finset.Iic n → V), MeasurableSet s ∧
      frestrictLe n ⁻¹' s = {ω | τ ω = n} := by
  have hm := hτ.measurableSet_eq n
  rw [Filtration.piLE_eq_comap_frestrictLe] at hm
  exact hm

lemma measure_eq_sum_stopping_slices (μ : Measure (ℕ → V))
    {τ : (ℕ → V) → WithTop ℕ} (hτ : Measurable τ)
    (hfin : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    μ = Measure.sum (fun n : ℕ => μ.restrict {ω | τ ω = n}) := by
  have hdisj : Pairwise (fun i j : ℕ => Disjoint {ω | τ ω = i} {ω | τ ω = j}) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun ω hi hj => hij ?_
    exact WithTop.coe_injective (hi.symm.trans hj)
  have hcover : ∀ᵐ ω ∂μ, ω ∈ ⋃ n : ℕ, {ω | τ ω = n} := by
    filter_upwards [hfin] with ω hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    exact Set.mem_iUnion.mpr ⟨n, hn.symm⟩
  calc
    μ = μ.restrict (⋃ n : ℕ, {ω | τ ω = n}) :=
      (Measure.restrict_eq_self_of_ae_mem hcover).symm
    _ = _ := Measure.restrict_iUnion hdisj
      (fun n => measurableSet_eq_fun hτ measurable_const)

end FiniteConductanceNetwork
end BouRabeeGwynne
