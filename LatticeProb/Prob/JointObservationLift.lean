import LatticeProb.Prob.DependentKernelMap
import Mathlib.Probability.Kernel.CondDistrib

/-! # Lifting a joint law through a measurable observation -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LatticeProb

/-- A joint law of an observation and a second variable can be lifted to the
original variable, preserving the entire joint law. -/
theorem exists_joint_observation_lift
    {X Y Z : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [MeasurableEq Y] [MeasurableSpace Z]
    (ν : Measure X) [IsProbabilityMeasure ν] (ρ : Measure (Y × Z))
    [IsProbabilityMeasure ρ] (f : X → Y) (hf : Measurable f)
    (hρ : ρ.fst = ν.map f) :
    ∃ ξ : Measure (X × Z), IsProbabilityMeasure ξ ∧ ξ.fst = ν ∧
      ξ.map (fun p => (f p.1, p.2)) = ρ := by
  let κ := condDistrib id f ν
  let P : Measure ((Y × Z) × X) := ρ ⊗ₘ κ.comap Prod.fst measurable_fst
  have : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hfirst : P.map Prod.fst = ρ := Measure.fst_compProd ρ _
  change ρ.map Prod.fst = ν.map f at hρ
  have hpair : P.map (fun p => (p.1.1, p.2)) = ν.map (fun x => (f x, x)) := by
    dsimp only [P]
    rw [compProd_map_dependent_of_kernel_map ρ (κ.comap Prod.fst measurable_fst) κ
      Prod.fst (fun _ x => x) measurable_fst measurable_snd (fun _ => by simp), hρ]
    exact compProd_map_condDistrib hf.aemeasurable aemeasurable_id
  have hpairm : Measurable (fun p : (Y × Z) × X => (p.1.1, p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hfm : Measurable (fun x : X => (f x, x)) := hf.prodMk measurable_id
  have hgraph : MeasurableSet {p : Y × X | f p.2 = p.1} :=
    measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst
  have hgraph' : ∀ᵐ p ∂P, f p.2 = p.1.1 := by
    have hfull : ∀ᵐ p ∂(ν.map fun x => (f x, x)), f p.2 = p.1 :=
      (ae_map_iff (hf.prodMk measurable_id).aemeasurable hgraph).2
        (ae_of_all _ fun _ => rfl)
    rw [← hpair] at hfull
    exact (ae_map_iff hpairm.aemeasurable hgraph).1 hfull
  let g : ((Y × Z) × X) → X × Z := fun p => (p.2, p.1.2)
  have hg : Measurable g := measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  refine ⟨P.map g, inferInstance, ?_, ?_⟩
  · change (P.map g).map Prod.fst = ν
    rw [Measure.map_map measurable_fst hg]
    have hmap : P.map Prod.snd = ν := by
      have heq : P.map Prod.snd = (P.map (fun p => (p.1.1, p.2))).map Prod.snd := by
        rw [Measure.map_map measurable_snd
          hpairm]
        rfl
      rw [heq, hpair, Measure.map_map measurable_snd hfm]
      exact Measure.map_id
    exact hmap
  · have hfinal : Measurable (fun p : X × Z => (f p.1, p.2)) :=
      (hf.comp measurable_fst).prodMk measurable_snd
    rw [Measure.map_map hfinal hg]
    calc
      P.map ((fun p : X × Z => (f p.1, p.2)) ∘ g) = P.map Prod.fst := by
        apply Measure.map_congr
        filter_upwards [hgraph'] with p hp
        simp only [Function.comp_apply, g]
        exact Prod.ext hp rfl
      _ = ρ := hfirst

end LatticeProb
