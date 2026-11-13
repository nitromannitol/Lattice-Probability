import Mathlib
import LatticeProb.Prob.MarkovPathKernelDense

/-!
# The Markov property of the quenched limit path laws, for almost every environment

Let `νD` be a probability measure on a space `S₀` of environments and `K : S₀ → C(E, Prob C(ℝ≥0, E))` a
field of path laws, `K d z` being the law of the path started at `z` in the environment `d`.  Suppose a
random pair `(d, x)` has law `ν = νD ⊗ₘ κ₀` with `κ₀ d = K d z₀` (the path started at `z₀` has quenched law
`K d z₀`), and that `x` satisfies the Markov step at the time `t` in the sense of
`LatticeProb.compProd_eq_of_markov_step_pathShift`: the conditional law of `x (t + ·)` given `d` and the
stopped path `x (· ∧ t)` is `K d (x t)`.  Then for `νD`-almost every `d` the quenched laws have the Markov
property at `(z₀, t)`: `LatticeProb.MarkovAt (K d) z₀ t`.

* `LatticeProb.ae_markovAt_of_compProd`: the abstract statement, the Markov step being an identity of
  compositions-products on `S₀ × C(ℝ≥0, E) × C(ℝ≥0, E)`.
* `LatticeProb.ae_markovAt_of_markov_step_pathShift`: the same from the convergence-in-law hypotheses of
  `LatticeProb.compProd_eq_of_markov_step_pathShift`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

section AE

variable {S₀ E : Type*} [MeasurableSpace S₀]
  [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]

/-- **The Markov property for almost every environment.**  If `ν = νD ⊗ₘ κ₀` with `κ₀ d = K d z₀` and the
Markov step identity of the module documentation holds, with `t ≤ T`, then `MarkovAt (K d) z₀ t` for
`νD`-almost every `d`. -/
theorem ae_markovAt_of_compProd {νD : Measure S₀} [IsProbabilityMeasure νD]
    {K : S₀ → C(E, ProbabilityMeasure C(ℝ≥0, E))} {z₀ : E} {t T : ℝ≥0} (htT : t ≤ T)
    {κ₀ : Kernel S₀ C(ℝ≥0, E)} (hκ₀ : ∀ d, κ₀ d = (K d z₀ : Measure C(ℝ≥0, E)))
    {κ' : Kernel (S₀ × C(ℝ≥0, E)) C(ℝ≥0, E)} (hκ'p : ∀ y, κ' y = K y.1 (y.2 T))
    (h : (νD ⊗ₘ κ₀).map (fun q => ((q.1, stopPath q.2 t), pathShift q.2 t)) =
      ((νD ⊗ₘ κ₀).map fun q => (q.1, stopPath q.2 t)) ⊗ₘ κ') :
    ∀ᵐ d ∂νD, MarkovAt (K d) z₀ t := by
  classical
  have hM₀ : IsMarkovKernel κ₀ := ⟨fun d => by rw [hκ₀ d]; infer_instance⟩
  have hM' : IsMarkovKernel κ' := ⟨fun y => by rw [hκ'p y]; infer_instance⟩
  have hstop : Measurable fun x : C(ℝ≥0, E) => stopPath x t :=
    (continuous_stopPath_uncurry.comp (continuous_id.prodMk continuous_const)).measurable
  have hshift : Measurable fun x : C(ℝ≥0, E) => pathShift x t :=
    (continuous_pathShift_uncurry.comp (continuous_id.prodMk continuous_const)).measurable
  have hsS : Measurable fun x : C(ℝ≥0, E) => (stopPath x t, pathShift x t) := hstop.prodMk hshift
  have hMs : IsMarkovKernel (κ₀.map fun x => (stopPath x t, pathShift x t)) :=
    Kernel.IsMarkovKernel.map κ₀ hsS
  have hMt : IsMarkovKernel (κ₀.map fun x => stopPath x t) := Kernel.IsMarkovKernel.map κ₀ hstop
  -- the two sides of the Markov step as measures on `S₀ × (C × C)`
  have hA : (νD ⊗ₘ κ₀).map (fun q => (q.1, stopPath q.2 t)) =
      νD ⊗ₘ (κ₀.map fun x => stopPath x t) := (Measure.compProd_map hstop).symm
  have hB : (νD ⊗ₘ κ₀).map (fun q => ((q.1, stopPath q.2 t), pathShift q.2 t)) =
      (νD ⊗ₘ (κ₀.map fun x => (stopPath x t, pathShift x t))).map
        MeasurableEquiv.prodAssoc.symm := by
    rw [Measure.compProd_map hsS,
      Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (measurable_id.prodMap hsS)]
    rfl
  have hEq : νD ⊗ₘ (κ₀.map fun x => (stopPath x t, pathShift x t)) =
      νD ⊗ₘ ((κ₀.map fun x => stopPath x t) ⊗ₖ κ') := by
    have h2 := congrArg (fun μ => μ.map MeasurableEquiv.prodAssoc) h
    simp only [hA, hB] at h2
    rw [Measure.compProd_assoc'] at h2
    rwa [Measure.map_map MeasurableEquiv.prodAssoc.measurable
      MeasurableEquiv.prodAssoc.symm.measurable,
      show (⇑MeasurableEquiv.prodAssoc ∘ ⇑MeasurableEquiv.prodAssoc.symm) = id from
        funext fun _ => rfl, Measure.map_id] at h2
  have hae := Kernel.ae_eq_of_compProd_eq hEq
  filter_upwards [hae] with d hd g
  have e1 : ∫ x, g (stopPath x t, pathShift x t) ∂(K d z₀ : Measure C(ℝ≥0, E)) =
      ∫ p, g p ∂((κ₀.map fun x => (stopPath x t, pathShift x t)) d) := by
    rw [Kernel.map_apply _ hsS, integral_map hsS.aemeasurable g.continuous.aestronglyMeasurable,
      hκ₀ d]
  have hint : Integrable g (((κ₀.map fun x => stopPath x t) ⊗ₖ κ') d) := g.integrable _
  have hcont : Continuous fun y : C(ℝ≥0, E) =>
      ∫ w, g (y, w) ∂(K d (y T) : Measure C(ℝ≥0, E)) :=
    continuous_integral_of_continuous_measure
      ((K d).continuous.comp (continuous_eval_const T))
      (G := fun q : C(ℝ≥0, E) × C(ℝ≥0, E) => g (q.2, q.1))
      (g.continuous.comp (continuous_snd.prodMk continuous_fst)) (C := ‖g‖)
      fun q => g.norm_coe_le_norm _
  rw [e1, hd, ProbabilityTheory.integral_compProd hint, Kernel.map_apply _ hstop, hκ₀ d]
  simp only [hκ'p]
  rw [integral_map hstop.aemeasurable hcont.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [stopPath_apply, min_eq_right htT]

/-- **The Markov property of the quenched limit laws from the Markov step of the approximating
walks.**  Under the hypotheses of `compProd_eq_of_markov_step_pathShift`, if the limit law is
`ν = νD ⊗ₘ κ₀` with `κ₀ d = K d z₀`, then `MarkovAt (K d) z₀ t` for `νD`-almost every `d`. -/
theorem ae_markovAt_of_markov_step_pathShift
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace S₀] [SecondCountableTopology S₀] [BorelSpace S₀]
    [CompleteSpace E] [LocallyCompactSpace E]
    [MeasurableSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, E)))]
    [BorelSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, E)))]
    {D : ℕ → Ω → S₀} {X : ℕ → Ω → C(ℝ≥0, E)} (hD : ∀ n, Measurable (D n))
    (hX : ∀ n, Measurable (X n))
    {ν : Measure (S₀ × C(ℝ≥0, E))} [IsProbabilityMeasure ν]
    (hlaw : ∀ g : (S₀ × C(ℝ≥0, E)) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, g (D n ω, X n ω) ∂μ) atTop (𝓝 (∫ q, g q ∂ν)))
    {s : ℕ → ℝ≥0} {t T : ℝ≥0} (hs : Tendsto s atTop (𝓝 t)) (hsT : ∀ n, s n ≤ T)
    {K : S₀ → C(E, ProbabilityMeasure C(ℝ≥0, E))} (hK : Continuous K)
    {G : ℕ → MeasurableSpace Ω}
    (hYG : ∀ n, MeasurableSpace.comap (fun ω => (D n ω, stopPath (X n ω) (s n))) inferInstance ≤ G n)
    (hG : ∀ n, G n ≤ m₀)
    {κ : ℕ → Ω → ProbabilityMeasure C(ℝ≥0, E)}
    (hκ : ∀ n, AEMeasurable (fun ω => LevyProkhorov.ofMeasure (κ n ω)) μ)
    (hMarkov : ∀ (n : ℕ) (f : C(ℝ≥0, E) →ᵇ ℝ),
      μ[fun ω => f (pathShift (X n ω) (s n)) | G n] =ᵐ[μ]
        fun ω => ∫ x, f x ∂(κ n ω : Measure C(ℝ≥0, E)))
    (hclose : TendstoInMeasure μ
      (fun n ω => levyProkhorovDist (κ n ω : Measure C(ℝ≥0, E))
        (K (D n ω) (X n ω (s n)) : Measure C(ℝ≥0, E))) atTop 0)
    {νD : Measure S₀} [IsProbabilityMeasure νD] {κ₀ : Kernel S₀ C(ℝ≥0, E)} {z₀ : E}
    (hν : ν = νD ⊗ₘ κ₀) (hκ₀ : ∀ d, κ₀ d = (K d z₀ : Measure C(ℝ≥0, E))) :
    ∀ᵐ d ∂νD, MarkovAt (K d) z₀ t := by
  obtain ⟨κ', -, hκ'p, hκ'⟩ := compProd_eq_of_markov_step_pathShift hD hX hlaw hs hsT hK hYG hG hκ
    hMarkov hclose
  rw [hν] at hκ'
  exact ae_markovAt_of_compProd (le_of_tendsto' hs hsT) hκ₀ hκ'p hκ'

end AE

end LatticeProb
