/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V2

/-!
# LM Theorem 1.7, packet P-VAR (c): the resampled metric for any version of the conditional law

Same statement and proof as `t17v_resample_exists` (Papers/LM/T1_7V2.lean; LM l. 1013–1016), for an
arbitrary Markov kernel `κ'` satisfying the disintegration identity `law(Y) ⊗ κ' = law(Y, D)`
(e.g. the `θ`-slice of a jointly measurable conditional law, `t17v_slice`), and with the
conclusion kept in kernel form (`κ'(Y d with Y_i d' in slot i)`-a.e. `D^S`), so that its
exceptional sets are measurable in further parameters.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
variable {β : Type*} [MeasurableSpace β]

/-- **the resampled metric `D^S`, kernel form** -/
theorem t17v_resample_kernel [MeasurableEq E]
    (ν : Measure β) [IsProbabilityMeasure ν] {Y : β → ι → E} (hY : Measurable Y)
    (hprod : ν.map Y = Measure.pi fun j => ν.map fun d => Y d j) {F : β → ℝ} {Φ : (ι → E) → ℝ}
    (hΦ : Measurable Φ) (hFm : Measurable F) (hF : F =ᵐ[ν] Φ ∘ Y) (κ' : Kernel (ι → E) β)
    [IsMarkovKernel κ'] (hjoint : (ν.map Y) ⊗ₘ κ' = ν.map fun d => (Y d, d)) (R : β → β → Prop)
    (hR : ∀ π : Measure (β × β), π.map Prod.fst = ν → π.map Prod.snd = ν →
      ∀ᵐ p ∂π, R p.1 p.2) :
    ∀ᵐ d ∂ν, ∀ i, ∀ᵐ d' ∂ν, ∀ᵐ d'' ∂κ' (Function.update (Y d) i (Y d' i)),
      R d d'' ∧ Y d'' = Function.update (Y d) i (Y d' i) ∧
        F d'' = Φ (Function.update (Y d) i (Y d' i)) := by
  set μ : ι → Measure E := fun j => ν.map fun d => Y d j with hμ
  have : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    (Measure.isProbabilityMeasure_map_iff ((measurable_pi_apply j).comp hY).aemeasurable).2
      inferInstance
  refine ae_all_iff.2 fun i => ?_
  set yS : β × β → ι → E := fun p => Function.update (Y p.1) i (Y p.2 i) with hySdef
  have hyS : Measurable yS := (t17v_measurable_update i).comp (hY.prodMap hY)
  have hlaw : (ν.prod ν).map yS = ν.map Y := by
    have : yS = (fun q : (ι → E) × (ι → E) => Function.update q.1 i (q.2 i)) ∘ Prod.map Y Y :=
      rfl
    rw [this, ← Measure.map_map (t17v_measurable_update i) (hY.prodMap hY),
      ← Measure.map_prod_map _ _ hY hY, hprod, t17v_update_law μ i]
  -- the conditional law of `D` given its coordinates is carried by the right coordinates
  set SA : Set ((ι → E) × β) := {q | (∀ j, Y q.2 j = q.1 j) ∧ F q.2 = Φ q.1} with hSAdef
  have hSA : MeasurableSet SA := by
    simp only [hSAdef, Set.ofPred_and, Set.ofPred_forall]
    exact (MeasurableSet.iInter fun j => measurableSet_eq_fun
      ((measurable_pi_apply j).comp (hY.comp measurable_snd))
      ((measurable_pi_apply j).comp measurable_fst)).inter
      (measurableSet_eq_fun (hFm.comp measurable_snd) (hΦ.comp measurable_fst))
  have hA0 : ∀ᵐ y ∂ν.map Y, ∀ᵐ d'' ∂κ' y, (y, d'') ∈ SA := by
    refine (Measure.ae_compProd_iff (p := fun q => q ∈ SA) hSA).1 ?_
    rw [hjoint]
    refine (ae_map_iff (p := fun x => x ∈ SA) (hY.prodMk measurable_id).aemeasurable hSA).2 ?_
    filter_upwards [hF] with d hd
    exact ⟨fun j => rfl, hd⟩
  have hA : ∀ᵐ p ∂ν.prod ν, ∀ᵐ d'' ∂κ' (yS p), (yS p, d'') ∈ SA := by
    rw [← hlaw] at hA0
    exact ae_of_ae_map hyS.aemeasurable hA0
  -- the coupling `(d, D^S)` has both marginals `ν`
  set K : Kernel (β × β) β := κ'.comap yS hyS with hK
  set π' : Measure ((β × β) × β) := (ν.prod ν) ⊗ₘ K with hπ'
  set π : Measure (β × β) := π'.map fun q => (q.1.1, q.2) with hπ
  have hqm : Measurable fun q : (β × β) × β => (q.1.1, q.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have h1 : π.map Prod.fst = ν := by
    rw [hπ, Measure.map_map measurable_fst hqm]
    have : (Prod.fst ∘ fun q : (β × β) × β => (q.1.1, q.2)) = Prod.fst ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map measurable_fst measurable_fst]
    rw [show π'.map Prod.fst = π'.fst from rfl, hπ', Measure.fst_compProd,
      show (ν.prod ν).map Prod.fst = (ν.prod ν).fst from rfl, Measure.fst_prod]
  have h2 : π.map Prod.snd = ν := by
    rw [hπ, Measure.map_map measurable_snd hqm]
    have : (Prod.snd ∘ fun q : (β × β) × β => (q.1.1, q.2)) = Prod.snd := rfl
    rw [this, show π'.map Prod.snd = π'.snd from rfl, hπ', Measure.snd_compProd]
    ext A hA
    rw [Measure.bind_apply hA K.aemeasurable]
    simp only [hK, Kernel.comap_apply]
    rw [← lintegral_map (κ'.measurable_coe hA) hyS, hlaw,
      ← Measure.bind_apply hA κ'.aemeasurable]
    have := congrArg Measure.snd hjoint
    rw [Measure.snd_compProd, Measure.snd_map_prodMk hY (Y := fun d : β => d) measurable_id]
      at this
    erw [Measure.map_id] at this
    rw [show (ν.map Y).bind κ' = κ' ∘ₘ ν.map Y from rfl, this]
  have hRπ := hR π h1 h2
  have hR' : ∀ᵐ q ∂π', R q.1.1 q.2 := ae_of_ae_map hqm.aemeasurable hRπ
  have hR'' := Measure.ae_ae_of_ae_compProd hR'
  have hboth : ∀ᵐ p ∂ν.prod ν, ∀ᵐ d'' ∂κ' (yS p), R p.1 d'' ∧ (yS p, d'') ∈ SA := by
    filter_upwards [hA, hR''] with p hp1 hp2
    have hp2' : ∀ᵐ d'' ∂κ' (yS p), R p.1 d'' := by
      simpa only [hK, Kernel.comap_apply] using hp2
    exact hp2'.and hp1
  filter_upwards [Measure.ae_ae_of_ae_prod hboth] with d hd
  filter_upwards [hd] with d' hd'
  filter_upwards [hd'] with d'' ⟨hR1, hY1, hF1⟩
  exact ⟨hR1, funext hY1, hF1⟩

end LQGMetric.LM
