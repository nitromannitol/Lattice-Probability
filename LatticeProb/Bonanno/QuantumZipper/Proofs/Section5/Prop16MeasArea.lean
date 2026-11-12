/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Section5.Prop16MeasArea at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Basic
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.LQG.Local

/-!
# Proposition 1.6, node D4-MEAS (part 3): measurability of local area pairings on random domains

For a measurable family of samples `x p` and random open domains `U p` exhausted by a measurable
family of continuous cut-offs `φ n p` (`IsBumpFamily`), on the event `goodSet` that the local
area measure `qAreaMeasureOn γ (x p) (U p)` is a genuine vague limit:

* `integral_qAreaMeasureOn_eq_Phi`: `∫ f d(qAreaMeasureOn γ (x p) (U p))` is an explicit countable
  limit of the measurable pre-limit integrals `∫ f φ_n d(areaApprox γ (x p) k)` (including the
  Bochner junk value `0` when `f` is not integrable, detected by `∫⁻ |f| < ∞`);
* `aemeasurable_integral_qAreaMeasureOn`: hence the pairing is a.e.-measurable in `p` as soon as
  `goodSet` is null-measurable (off `goodSet` the measure is the junk `0`).

Own elementary proof (monotone and dominated convergence; AGENT_GUIDE cost rule), following the
approach of `LQGMeas.measurable_qAreaMeasure_open` (`Proofs/LQG/Measurability.lean`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

namespace Meas

open LQGMeas

variable {α : Type*} [MeasurableSpace α]

/-- The event that the local area measure is a genuine vague limit. -/
def goodSet (γ : ℝ) (x : α → FieldSample) (U : α → Set ℂ) : Set α :=
  {p | ∃ m, IsVagueLimitOn (U p) (areaApprox γ (x p)) m}

theorem isVagueLimitOn_qAreaMeasureOn {γ : ℝ} {y : FieldSample} {V : Set ℂ}
    (hg : ∃ m, IsVagueLimitOn V (areaApprox γ y) m) :
    IsVagueLimitOn V (areaApprox γ y) (qAreaMeasureOn γ y V) := by
  unfold qAreaMeasureOn; rw [dif_pos hg]; exact hg.choose_spec

/-- Pre-limit integrals with a parameter-dependent integrand are measurable. -/
theorem measurable_integral_areaApprox_param (γ : ℝ) (k : ℕ) {x : α → FieldSample}
    (hx : Measurable x) {g : α → ℂ → ℝ} (hg : Measurable fun q : α × ℂ => g q.1 q.2) :
    Measurable fun p => ∫ z, g p z ∂areaApprox γ (x p) k := by
  let Dn : α × ℂ → ℝ := fun q => radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg (x q.1) k q.2)
  have hA : Measurable fun q : α × ℂ => avgReg (x q.1) k q.2 :=
    Measurable.comp (g := fun r : FieldSample × ℂ => avgReg r.1 k r.2)
      (f := fun q : α × ℂ => (x q.1, q.2)) (measurable_avgReg k)
      ((hx.comp measurable_fst).prodMk measurable_snd)
  have hDm : Measurable Dn := (Real.measurable_exp.comp (hA.const_mul γ)).const_mul _
  have hD0 : ∀ q, 0 ≤ Dn q := fun q =>
    mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  have heq : ∀ p, ∫ z, g p z ∂areaApprox γ (x p) k =
      ∫ z, Dn (p, z) * g p z ∂(volume.restrict H) := fun p =>
    GoodSample.integral_withDensity_ofReal (μ := volume.restrict H)
      (hDm.comp (measurable_const.prodMk measurable_id)) (fun z => hD0 _) (g p)
  simp_rw [heq]
  exact (StronglyMeasurable.integral_prod_right' (ν := volume.restrict H)
    (f := fun q : α × ℂ => Dn q * g q.1 q.2) (hDm.mul hg).stronglyMeasurable).measurable

/-- The limit of the pre-limit integrals (junk `0` if it does not exist). -/
def Psi (γ : ℝ) (x : α → FieldSample) (g : α → ℂ → ℝ) (p : α) : ℝ :=
  limUnder atTop fun k => ∫ z, g p z ∂areaApprox γ (x p) k

theorem measurable_Psi (γ : ℝ) {x : α → FieldSample} (hx : Measurable x) {g : α → ℂ → ℝ}
    (hg : Measurable fun q : α × ℂ => g q.1 q.2) : Measurable (Psi γ x g) :=
  (StronglyMeasurable.limUnder fun k =>
    (measurable_integral_areaApprox_param γ k hx hg).stronglyMeasurable).measurable

variable {γ : ℝ} {x : α → FieldSample} {U : α → Set ℂ} {φ : ℕ → α → ℂ → ℝ}

omit [MeasurableSpace α] in
theorem integral_eq_Psi {p : α} (hp : p ∈ goodSet γ x U) {g : α → ℂ → ℝ}
    (hc : Continuous (g p)) (hcs : HasCompactSupport (g p)) (hV : tsupport (g p) ⊆ U p) :
    ∫ z, g p z ∂qAreaMeasureOn γ (x p) (U p) = Psi γ x g p :=
  (((isVagueLimitOn_qAreaMeasureOn hp).2.2 _ hc hcs hV).limUnder_eq).symm

end Meas

end Prop16Area

end QuantumZipper
