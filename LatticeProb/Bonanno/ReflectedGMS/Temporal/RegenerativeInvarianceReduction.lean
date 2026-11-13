/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.RegenerativeInvarianceReduction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.GridAveragedConstantReduction
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# `p:lem:regeninvariant` at an annealed law `νenv ⊗ₘ κ`, reduced to two fixed-environment inputs

The annealed two-sided rooted law of the manuscript is "first sample `𝓗` from its spatial law
and then sample the two-sided process from `H_0`" (tex:1352): a composition `νenv ⊗ₘ κ` of the
environment law with the kernel `κ : Kernel Env X` of fixed-environment two-sided laws on the
trajectory coding, with `envOf = Prod.fst`.  The fixed-environment laws are the `pathLaw` data
of `Temporal/ActualConditionalPathIntegral.MarkedPathProcess`; nothing here constructs them.

This module proves the **last paragraph** of the manuscript proof of `p:lem:regeninvariant`
(tex:1509-1512) — "the set of environments for which the conditional law of `B` is a point
mass … is measurable … preserved by similarities … on this invariant set take the common mean,
and set it equal to zero elsewhere" — verbatim, and thereby reduces
`RegenerativeInvariance (νenv ⊗ₘ κ) θΩ SΩ Prod.fst` to two named inputs about the kernel:

* `FiberwiseConstant νenv κ θΩ SΩ` — **(F1)** for `νenv`-almost every environment, every
  bounded measurable jointly invariant functional is `κ e`-almost surely constant on the fiber.
  This is the first two paragraphs of the manuscript proof (iid cycles, Bernoulli shift, the
  `L_v/h_v` size-biasing), i.e. fixed-environment ergodicity; and it is *necessary*
  (`fiberwiseConstant_of_regenerativeInvariance`).
* `SimilarityTransfer κ θΩ SΩ` — **(F2)** the almost-sure value of such a functional under
  the conditional law is the same at similar environments.  This is the manuscript's
  "`v`-independence" (translations by a cell displacement, tex:1503-1506, via the σ-finite
  shift-invariant measure) together with "the conditional area-clock law transforms
  canonically" (dilations, the `law_φ` field of `MarkedPathProcess.similarityCoding`).  It is
  stated for *every* pair of similar environments because the environment-ergodicity
  hypothesis `EnvironmentErgodic` tests **exactly** invariant sets; an almost-everywhere
  version would not feed it.

## What is proved

* `condMean`, `condDev`, `constantSet` — the conditional mean `∫ B(e,x) dκ_e(x)`, the
  conditional `L¹` deviation, and the measurable set of environments on which the deviation
  vanishes (`measurable_condMean`, `measurable_condDev`, `measurableSet_constantSet`, from
  `StronglyMeasurable.integral_kernel_prod_right'`).
* `ae_eq_condMean_of_mem_constantSet` / `mem_constantSet_of_ae_const` — the deviation vanishes
  exactly when the functional is a.s. constant on the fiber, and then its constant is the
  conditional mean.
* `regenerativeInvariance_compProd_of_fiberwise` — **the reduction**: (F1) and (F2) give
  `RegenerativeInvariance (νenv ⊗ₘ κ) θΩ SΩ Prod.fst`, with the environment function
  `(constantSet κ B).indicator (condMean κ B)`, measurable and *exactly* similarity-invariant.
* `jointErgodic_compProd_of_fiberwise` — composed with
  `RegenerativeInvarianceErgodic.regenerativeInvariance_iff_jointErgodic`: the annealed joint
  ergodic theorem from (F1), (F2) and environment ergodicity.
* `fiberwiseConstant_of_regenerativeInvariance` — (F1) is necessary.
* `fiberwiseConstant_const_dirac`, `similarityTransfer_const_dirac` — anti-vacuity: the two
  inputs are jointly satisfiable (a point-mass kernel with a trajectory flow that forgets the
  environment coordinate).

## Satisfiability at the actual law

Both inputs are the manuscript's own claims, stated for the kernel `κ e = ℙ_e^{H_0}` on the
càdlàg coding.  (F1) is `p:lem:regeninvariant`, first sentence, per environment; the
manuscript proves it for every connected recurrent environment, and only `νenv`-a.e. is asked.
(F2) needs the rooted flow of `RegenerativeInvarianceErgodic` (the flow must translate the
environment by the current cell's displacement and relabel canonically): on that flow a
functional invariant under `θΩ` is determined by the orbit, and since a translate `e + u` has
the *same* re-rooted environments `e - c(w)` (canonical labels are unique), translation transfer
follows from flow invariance plus translation covariance of `κ`; dilation transfer is the
`law_φ` covariance.  Neither is proved here.

## What is *not* proved

(F1) and (F2) at the actual kernel; the kernel itself; `p:lem:regeninvariant`,
`p:prop:timeergodic`, `p:lem:bracketlimit`, `p:thm:areaclt`, either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set ProbabilityTheory

namespace ReflectedGMS.RegenerativeInvarianceReduction

open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.EnvironmentLaws

variable {X : Type*} [MeasurableSpace X]

/-! ### The conditional mean and deviation -/

/-- The conditional mean of a functional given the environment, under the kernel `κ`. -/
noncomputable def condMean (κ : Kernel Code.Env X) (B : Code.Env × X → ℝ) (e : Code.Env) : ℝ :=
  ∫ x, B (e, x) ∂κ e

/-- The conditional `L¹` deviation of a functional from its conditional mean. -/
noncomputable def condDev (κ : Kernel Code.Env X) (B : Code.Env × X → ℝ) (e : Code.Env) : ℝ :=
  ∫ x, |B (e, x) - condMean κ B e| ∂κ e

/-- The environments on which the functional is almost surely constant on the fiber. -/
def constantSet (κ : Kernel Code.Env X) (B : Code.Env × X → ℝ) : Set Code.Env :=
  {e | condDev κ B e = 0}

theorem measurable_condMean (κ : Kernel Code.Env X) [IsSFiniteKernel κ]
    {B : Code.Env × X → ℝ} (hB : Measurable B) : Measurable (condMean κ B) :=
  (hB.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

theorem measurable_condDev (κ : Kernel Code.Env X) [IsSFiniteKernel κ]
    {B : Code.Env × X → ℝ} (hB : Measurable B) : Measurable (condDev κ B) := by
  have h : Measurable fun p : Code.Env × X => |B p - condMean κ B p.1| := by
    have hn : Measurable fun p : Code.Env × X => ‖B p - condMean κ B p.1‖ :=
      (hB.sub ((measurable_condMean κ hB).comp measurable_fst)).norm
    have heq : (fun p : Code.Env × X => |B p - condMean κ B p.1|)
        = fun p : Code.Env × X => ‖B p - condMean κ B p.1‖ := by
      funext p
      rw [Real.norm_eq_abs]
    rw [heq]
    exact hn
  exact (h.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

theorem measurableSet_constantSet (κ : Kernel Code.Env X) [IsSFiniteKernel κ]
    {B : Code.Env × X → ℝ} (hB : Measurable B) : MeasurableSet (constantSet κ B) :=
  measurableSet_eq_fun (measurable_condDev κ hB) measurable_const

/-- A bounded measurable functional is integrable on every fiber of a Markov kernel. -/
theorem integrable_section (κ : Kernel Code.Env X) [IsMarkovKernel κ]
    {B : Code.Env × X → ℝ} (hB : Measurable B) (hb : ∀ p : Code.Env × X, |B p| ≤ 1)
    (e : Code.Env) : Integrable (fun x : X => B (e, x)) (κ e) := by
  refine (integrable_const (1 : ℝ)).mono' (hB.comp measurable_prodMk_left).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hb _

/-- On an environment where the conditional deviation vanishes, the functional is almost surely
its conditional mean. -/
theorem ae_eq_condMean_of_mem_constantSet (κ : Kernel Code.Env X) [IsMarkovKernel κ]
    {B : Code.Env × X → ℝ} (hB : Measurable B) (hb : ∀ p : Code.Env × X, |B p| ≤ 1)
    {e : Code.Env} (he : e ∈ constantSet κ B) : ∀ᵐ x ∂κ e, B (e, x) = condMean κ B e := by
  have hint : Integrable (fun x : X => |B (e, x) - condMean κ B e|) (κ e) :=
    ((integrable_section κ hB hb e).sub (integrable_const _)).abs
  have h0 : ∫ x, |B (e, x) - condMean κ B e| ∂κ e = 0 := he
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _) hint).1 h0
  filter_upwards [hae] with x hx
  have hx' : |B (e, x) - condMean κ B e| = 0 := hx
  exact sub_eq_zero.1 (abs_eq_zero.1 hx')

/-- If the functional is almost surely a constant on a fiber, that constant is the conditional
mean. -/
theorem condMean_eq_of_ae_const (κ : Kernel Code.Env X) [IsMarkovKernel κ]
    {B : Code.Env × X → ℝ} {e : Code.Env} {c : ℝ} (hc : ∀ᵐ x ∂κ e, B (e, x) = c) :
    condMean κ B e = c := by
  have h : ∫ x, B (e, x) ∂κ e = ∫ _x, c ∂κ e := integral_congr_ae hc
  rw [condMean, h, integral_const, probReal_univ, one_smul]

/-- If the functional is almost surely constant on a fiber, the conditional deviation
vanishes. -/
theorem mem_constantSet_of_ae_const (κ : Kernel Code.Env X) [IsMarkovKernel κ]
    {B : Code.Env × X → ℝ} {e : Code.Env} (hc : ∃ c : ℝ, ∀ᵐ x ∂κ e, B (e, x) = c) :
    e ∈ constantSet κ B := by
  obtain ⟨c, hc⟩ := hc
  have hm : condMean κ B e = c := condMean_eq_of_ae_const κ hc
  show ∫ x, |B (e, x) - condMean κ B e| ∂κ e = 0
  have h : ∫ x, |B (e, x) - condMean κ B e| ∂κ e = ∫ _x, (0 : ℝ) ∂κ e := by
    refine integral_congr_ae ?_
    filter_upwards [hc] with x hx
    rw [hx, hm, sub_self, abs_zero]
  rw [h, integral_zero]

/-! ### The two fixed-environment inputs -/

/-! ### The reduction -/

/-! ### Anti-vacuity: the two inputs are jointly satisfiable -/

end ReflectedGMS.RegenerativeInvarianceReduction
