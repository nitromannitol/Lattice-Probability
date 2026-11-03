/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.Measurable at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.Field
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Measurability of the field operations (FOUNDATIONS §9 item 3, part 1)

The σ-algebra on `𝒟'(U)` is the cylinder σ-algebra of the pairings `h ↦ ⟨h, φ⟩`
(`DistOn.measurableSpace`, D2/F1), so a map into `𝒟'(U)` is measurable iff all its pairings are
(`measurable_distOn_iff`). With this the operations `restrictTo`, `addConst`, `affineComp`,
`addFun` (jointly in `(h, f)`, `C(ℂ, ℝ)` with its Borel σ-algebra) and `ofCont` are measurable.

We also prove that a family `x ↦ Ψ x` of test functions supported in a fixed compact, whose
`y`-derivatives are jointly continuous in `(x, y)`, is continuous into `𝓓_K` and `𝓓(ℂ)`
(`continuous_testFamily`); this is the input for the joint measurability of `circleAvg` and
`heatMollify` (Carathéodory: mathlib `measurable_uncurry_of_continuous_of_measurable`).

These are standard facts with no specific published source; own elementary proofs
(the topology of `𝓓_K` is that of uniform convergence of all derivatives: mathlib
`ContDiffMapSupportedIn.continuous_iff_comp`; Heine–Cantor: `Continuous.tendstoUniformly`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped Distributions

namespace LQGMetric

/-! ### Pairings generate the σ-algebra -/

theorem measurable_distOn_apply {U : Opens ℂ} (φ : TestOn U) :
    Measurable fun h : DistOn U => h φ :=
  (measurable_pi_apply φ).comp (measurable_iff_comap_le.2 le_rfl)

/-- A map into `𝒟'(U)` is measurable iff all its pairings with test functions are. -/
theorem measurable_distOn_iff {U : Opens ℂ} {α : Type*} [MeasurableSpace α] {g : α → DistOn U} :
    Measurable g ↔ ∀ φ : TestOn U, Measurable fun a => g a φ := by
  refine ⟨fun hg φ => (measurable_distOn_apply φ).comp hg, fun hg => ?_⟩
  rw [measurable_iff_comap_le]
  show MeasurableSpace.comap g (MeasurableSpace.comap _ MeasurableSpace.pi) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact (measurable_pi_iff.2 hg).comap_le

/-! ### Restriction, constants, affine pullback -/

theorem measurable_restrictTo (U : Opens ℂ) : Measurable (restrictTo U) :=
  measurable_distOn_iff.2 fun _ => measurable_distOn_apply _

theorem measurable_affineComp (r : ℝ) (z : ℂ) : Measurable (affineComp r z) :=
  measurable_distOn_iff.2 fun φ =>
    (measurable_distOn_apply (testAffinePull r z φ)).const_smul ((r ^ 2)⁻¹)

/-! ### Adding a continuous function -/

theorem ofCont_apply (f : C(ℂ, ℝ)) (φ : TestC) : ofCont f φ = ∫ x, φ x * f x := by
  rw [ofCont, Distribution.ofFun_apply (f.continuous.locallyIntegrable.locallyIntegrableOn _)]
  rfl

theorem measurable_ofCont_apply (φ : TestC) : Measurable fun f : C(ℂ, ℝ) => ofCont f φ := by
  simp_rw [ofCont_apply]
  have hc : Continuous fun p : C(ℂ, ℝ) × ℂ => φ p.2 * p.1 p.2 :=
    (φ.continuous.comp continuous_snd).mul continuous_eval
  exact (hc.measurable.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem measurable_addFun : Measurable fun p : DistC × C(ℂ, ℝ) => addFun p.1 p.2 := by
  refine measurable_distOn_iff.2 fun φ => ?_
  show Measurable fun p : DistC × C(ℂ, ℝ) => p.1 φ + ofCont p.2 φ
  exact ((measurable_distOn_apply φ).comp measurable_fst).add
    ((measurable_ofCont_apply φ).comp measurable_snd)

theorem measurable_addFun_left (f : C(ℂ, ℝ)) : Measurable fun h : DistC => addFun h f :=
  measurable_addFun.comp (measurable_id.prodMk measurable_const)

/-! ### Continuous families of test functions -/

section family

/-- the family `x ↦ Ψ x` as elements of `𝓓_K` -/
def testFamK {X : Type*} (K : Compacts ℂ) (Ψ : X → ℂ → ℝ)
    (hs : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ x)) (hK : ∀ x, ∀ y ∉ (K : Set ℂ), Ψ x y = 0)
    (x : X) : 𝓓^{⊤}_{K}(ℂ, ℝ) where
  toFun := Ψ x
  contDiff' := hs x
  zero_on_compl' := fun y hy => hK x y hy

theorem continuous_testFamK {X : Type*} [UniformSpace X] [WeaklyLocallyCompactSpace X] (K : Compacts ℂ) (Ψ : X → ℂ → ℝ)
    (hs : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ x)) (hK : ∀ x, ∀ y ∉ (K : Set ℂ), Ψ x y = 0)
    (hD : ∀ i : ℕ, Continuous fun p : X × ℂ => iteratedFDeriv ℝ i (Ψ p.1) p.2) :
    Continuous (testFamK K Ψ hs hK) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hu := Continuous.tendstoUniformly (fun (x : X) (y : (K : Set ℂ)) =>
      iteratedFDeriv ℝ i (Ψ x) (y : ℂ))
    (by
      have := (hD i).comp (X := X × (K : Set ℂ))
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      exact this) x₀
  rw [Metric.tendstoUniformly_iff] at hu
  filter_upwards [hu (ε / 2) (half_pos hε)] with x hx
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun y => ?_)
    (half_lt_self hε)
  simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
  by_cases hy : y ∈ (K : Set ℂ)
  · rw [dist_comm]; exact (hx ⟨y, hy⟩).le
  · rw [(testFamK K Ψ hs hK x).iteratedFDeriv_zero_on_compl hy,
      (testFamK K Ψ hs hK x₀).iteratedFDeriv_zero_on_compl hy]
    simp [(half_pos hε).le]

/-- the `y`-derivatives of a jointly smooth `Ψ : ℂ × ℂ → ℝ` are jointly continuous -/
theorem continuous_iteratedFDeriv_snd {Ψ : ℂ → ℂ → ℝ}
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Ψ)) (i : ℕ) :
    Continuous fun p : ℂ × ℂ => iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
  let ι : ℂ →L[ℝ] ℂ × ℂ := ContinuousLinearMap.inr ℝ ℂ ℂ
  have key : ∀ p : ℂ × ℂ, iteratedFDeriv ℝ i (Ψ p.1) p.2 =
      (iteratedFDeriv ℝ i (Function.uncurry Ψ) p).compContinuousLinearMap fun _ => ι := by
    intro p
    have h1 : Ψ p.1 = (fun w => Function.uncurry Ψ (w + (p.1, 0))) ∘ ι := by
      funext y; simp [ι]
    have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun w => Function.uncurry Ψ (w + (p.1, 0)) :=
      hΨ.comp (contDiff_id.add contDiff_const)
    rw [h1, ι.iteratedFDeriv_comp_right hg _ (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    congr 2
    simp [ι]
  simp_rw [key]
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
    (E := fun _ : Fin i => ℂ) (E₁ := fun _ : Fin i => ℂ × ℂ) (F := ℝ) (fun _ => ι)
  exact L.continuous.comp (hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top))

end family

end LQGMetric
