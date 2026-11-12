/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.Measurability at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# M4-R5 (measurability): the LQG measures are measurable functions of good samples

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

theorem openBump_mono (U : Set α) (z : α) : Monotone fun n => openBump U n z := by
  intro m n hmn
  have hd := Metric.infDist_nonneg (x := z) (s := Uᶜ)
  have : (m : ℝ) * Metric.infDist z Uᶜ ≤ n * Metric.infDist z Uᶜ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hd
  exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

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

theorem hasCompactSupport_openBump [ProperSpace α] {U : Set α} (hU : Bornology.IsBounded U) (n : ℕ) :
    HasCompactSupport (openBump U n) :=
  hU.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
    ((tsupport_openBump_subset U n).trans subset_closure)

theorem iSup_openBump {U : Set α} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) (z : α) :
    ⨆ n : ℕ, ENNReal.ofReal (openBump U n z) = U.indicator 1 z := by
  by_cases hz : z ∈ U
  · rw [indicator_of_mem hz, Pi.one_apply]
    refine le_antisymm (iSup_le fun n => ?_) ?_
    · exact ENNReal.ofReal_le_one.2 (openBump_le_one U n z)
    · have hd : 0 < Metric.infDist z Uᶜ :=
        (hU.isClosed_compl.notMem_iff_infDist_pos hUc).1 (fun h => h hz)
      obtain ⟨n, hn⟩ := exists_nat_gt (2 / Metric.infDist z Uᶜ)
      refine le_iSup_of_le n (le_of_eq ?_)
      have h2 : 2 ≤ (n : ℝ) * Metric.infDist z Uᶜ := by
        rw [div_lt_iff₀ hd] at hn; linarith
      rw [openBump, max_eq_right (by linarith), min_eq_left (by linarith), ENNReal.ofReal_one]
  · rw [indicator_of_notMem hz]
    refine le_antisymm (iSup_le fun n => ?_) zero_le
    have : openBump U n z = 0 := by
      by_contra h
      exact hz (tsupport_openBump_subset U n (subset_tsupport _ h))
    rw [this, ENNReal.ofReal_zero]

theorem measure_open_eq_iSup [MeasurableSpace α] [BorelSpace α] (μ : Measure α) {U : Set α} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    μ U = ⨆ n : ℕ, ∫⁻ z, ENNReal.ofReal (openBump U n z) ∂μ := by
  rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (openBump U n z))
    (fun n => ENNReal.measurable_ofReal.comp (continuous_openBump U n).measurable)
    (fun m n hmn z => ENNReal.ofReal_le_ofReal (openBump_mono U z hmn)),
    ← lintegral_indicator_one hU.measurableSet]
  congr 1
  funext z
  exact (iSup_openBump hU hUc z).symm

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
