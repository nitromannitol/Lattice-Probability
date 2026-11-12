/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.Measurability at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
For a good sample `x` (`IsLQGGood γ x`), `qBoundaryMeasure γ x` and `qAreaMeasure γ x` are the
limits of the approximations `bdryApprox γ x k`, `areaApprox γ x k` (radius `2^{-k}`). Hence:

* for a continuous compactly supported `f`, `∫ f d(qBoundaryMeasure γ x)` agrees on good samples
  with the measurable function `liminf_k ∫ f d(bdryApprox γ x k)` (`bdryFun`), and similarly on
  `ℍ` (`areaFun`, for `tsupport f ⊆ H`);
* the measure of a bounded open set is a countable supremum of such integrals (`openBump`);
* a Dynkin (`π`–`λ`) argument on the finite-measure pieces `s ∩ V N` upgrades this to
  measurability into `Measure` with the Giry `σ`-algebra, on the subtype of good samples
  (`measurable_qBoundaryMeasure_good`, `measurable_qAreaMeasure_good`);
* `scaleParam` is an `sInf` of an up-closed set of radii tested at rationals
  (`measurable_scaleParam_good`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace LQGMeas

/-! ## Integrals against the approximating measures are measurable -/

/-! ## Convergence of the approximations on good samples -/

/-! ## Open sets as countable suprema of test functions -/

section OpenApprox

variable {α : Type*} [MetricSpace α]

/-- Continuous cut-offs increasing to the indicator of `U`, supported in `U`. -/
def openBump (U : Set α) (n : ℕ) (z : α) : ℝ :=
  min 1 (max 0 ((n : ℝ) * Metric.infDist z Uᶜ - 1))

theorem continuous_openBump (U : Set α) (n : ℕ) : Continuous (openBump U n) :=
  continuous_const.min (continuous_const.max
    ((continuous_const.mul (Metric.continuous_infDist_pt _)).sub continuous_const))

theorem openBump_nonneg (U : Set α) (n : ℕ) (z : α) : 0 ≤ openBump U n z :=
  le_min zero_le_one (le_max_left _ _)

theorem openBump_le_one (U : Set α) (n : ℕ) (z : α) : openBump U n z ≤ 1 := min_le_left _ _

theorem support_openBump_subset (U : Set α) (n : ℕ) :
    Function.support (openBump U n) ⊆ {z | 1 ≤ (n : ℝ) * Metric.infDist z Uᶜ} := by
  intro z hz
  simp only [mem_ofPred_eq]
  by_contra h
  rw [not_le] at h
  apply hz
  simp only [openBump]
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

theorem setOf_one_le_infDist_subset (U : Set α) (n : ℕ) :
    {z | 1 ≤ (n : ℝ) * Metric.infDist z Uᶜ} ⊆ U := by
  intro z hz
  by_contra h
  simp only [mem_ofPred_eq, Metric.infDist_zero_of_mem (show z ∈ Uᶜ from h), mul_zero] at hz
  linarith

theorem tsupport_openBump_subset (U : Set α) (n : ℕ) : tsupport (openBump U n) ⊆ U :=
  (closure_minimal (support_openBump_subset U n) (isClosed_le continuous_const
    (continuous_const.mul (Metric.continuous_infDist_pt _)))).trans
    (setOf_one_le_infDist_subset U n)

end OpenApprox

/-! ## Measures of open sets on good samples -/

/-! ## A Dynkin argument: measurability into `Measure` from open sets -/

/-! ## Giry measurability of the LQG measures on good samples -/

/-! ## `scaleParam` -/

/-- The infimum of an up-closed set of positive reals is measurable if membership of each
rational is. -/
theorem measurable_sInf_upClosed {X : Type*} [MeasurableSpace X] (S : X → Set ℝ)
    (hS : ∀ q : ℚ, MeasurableSet {x | (q : ℝ) ∈ S x})
    (hup : ∀ x a b, a ∈ S x → a ≤ b → b ∈ S x) (hpos : ∀ x a, a ∈ S x → 0 < a) :
    Measurable fun x => sInf (S x) := by
  refine measurable_of_Iio fun c => ?_
  have key : (fun x => sInf (S x)) ⁻¹' Iio c =
      {x | 0 < c} ∩ ((⋂ q : ℚ, {x | (q : ℝ) ∈ S x}ᶜ) ∪
        ⋃ q : ℚ, {x | (q : ℝ) < c} ∩ {x | (q : ℝ) ∈ S x}) := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_inter_iff, mem_ofPred_eq, mem_union, mem_iInter,
      mem_iUnion, mem_compl_iff]
    by_cases hne : (S x).Nonempty
    · have hbdd : BddBelow (S x) := ⟨0, fun a ha => (hpos x a ha).le⟩
      rw [csInf_lt_iff hbdd hne]
      constructor
      · rintro ⟨a, ha, hac⟩
        obtain ⟨q, haq, hqc⟩ := exists_rat_btwn hac
        exact ⟨(hpos x a ha).trans (haq.trans hqc), Or.inr ⟨q, hqc, hup x a q ha haq.le⟩⟩
      · rintro ⟨-, h | ⟨q, hqc, hq⟩⟩
        · obtain ⟨a, ha⟩ := hne
          obtain ⟨q, hq⟩ := exists_rat_gt a
          exact absurd (hup x a q ha hq.le) (h q)
        · exact ⟨q, hq, hqc⟩
    · rw [not_nonempty_iff_eq_empty.1 hne, Real.sInf_empty]
      simp
  rw [key]
  exact (MeasurableSet.const _).inter ((MeasurableSet.iInter fun q => (hS q).compl).union
    (MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter (hS q)))

/-! ## Global versions, conditional on the measurability of the good set -/

/-! ## First reduction towards M4-R5 (1): the canonical regularity witness -/

end LQGMeas

end QuantumZipper
