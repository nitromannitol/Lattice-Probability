import LatticeProb.Prob.JumpChain.StateChain
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Joint law of the exponential clocks

Finite clock restrictions have the product law. Uniqueness of the infinite product
then identifies the entire clock law and gives independence, also on regular histories.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Set Preorder

noncomputable section

namespace BoundedRates

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
variable (rates : BoundedRates S) (μ : Measure S) [IsProbabilityMeasure μ]

/-- The clock coordinates through index `n` have the finite product law. -/
theorem historyLaw_map_clocks_Iic (n : ℕ) :
    (rates.historyLaw μ).map (fun h (k : ↥(Finset.Iic n)) ↦ (h k).2) =
      Measure.pi (fun _ : ↥(Finset.Iic n) ↦ rates.clockLaw) := by
  have hs : Measurable (fun h : History S ↦ fun k : ↥(Finset.Iic n) ↦ (h k).1) := by
    fun_prop
  letI := Measure.isProbabilityMeasure_map (μ := rates.historyLaw μ) hs.aemeasurable
  have h := congrArg (fun ν ↦ ν.map Prod.snd)
    (rates.historyLaw_map_states_clocks_prefix μ n)
  rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod,
    measure_univ, one_smul] at h
  exact h

/-- Any injectively selected clocks in a bounded prefix have the product law. -/
theorem historyLaw_map_clocks_of_injective {ι : Type*} [Fintype ι]
    (n : ℕ) (f : ι → ↥(Finset.Iic n)) (hf : Function.Injective f) :
    (rates.historyLaw μ).map (fun h i ↦ (h (f i)).2) =
      Measure.pi (fun _ : ι ↦ rates.clockLaw) := by
  have h := congrArg (fun ν : Measure (↥(Finset.Iic n) → ℝ) ↦
    ν.map (fun x i ↦ x (f i))) (rates.historyLaw_map_clocks_Iic μ n)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.infinitePi_eq_pi, Measure.map_infinitePi_infinitePi_of_inj hf,
    Measure.infinitePi_eq_pi] at h
  exact h

/-- Every initial finite clock sequence has the finite product law. -/
theorem historyLaw_map_clock_prefix (n : ℕ) :
    (rates.historyLaw μ).map (fun h (k : Fin n) ↦ (h k).2) =
      Measure.pi (fun _ : Fin n ↦ rates.clockLaw) := by
  exact rates.historyLaw_map_clocks_of_injective μ n
    (fun (k : Fin n) ↦ ⟨k, Finset.mem_Iic.mpr (Nat.le_of_lt k.isLt)⟩)
    (fun a b h ↦ Fin.ext (congrArg Subtype.val h))

/-- The entire clock sequence has the infinite product exponential law. -/
theorem historyLaw_map_clocks :
    (rates.historyLaw μ).map (fun h k ↦ (h k).2) =
      Measure.infinitePi (fun _ : ℕ ↦ rates.clockLaw) := by
  apply ((Measure.isProjectiveLimit_infinitePi
    (fun _ : ℕ ↦ rates.clockLaw)).unique ?_).symm
  intro I
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact rates.historyLaw_map_clocks_of_injective μ (I.sup id)
    (fun (k : I) ↦ ⟨k, Finset.mem_Iic.mpr (Finset.le_sup (f := id) k.property)⟩)
    (fun a b h ↦ Subtype.ext
      (congrArg (fun x : ↥(Finset.Iic (I.sup id)) ↦ (x : ℕ)) h))

/-- All recorded clocks are mutually independent. -/
theorem iIndepFun_clocks :
    iIndepFun (fun k (h : History S) ↦ (h k).2) (rates.historyLaw μ) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by intro k; fun_prop)]
  simp_rw [rates.historyLaw_map_clock]
  exact rates.historyLaw_map_clocks μ

/-- The state sequence and independent exponential clock sequence have a product law. -/
theorem historyLaw_map_states_clocks :
    (rates.historyLaw μ).map (fun h ↦ ((fun k ↦ (h k).1), (fun k ↦ (h k).2))) =
      ((rates.historyLaw μ).map (fun h k ↦ (h k).1)).prod
        (Measure.infinitePi (fun _ : ℕ ↦ rates.clockLaw)) := by
  rw [← rates.historyLaw_map_clocks μ]
  exact (rates.indepFun_states_clocks μ).map_prod_eq_prod_map_map
    (measurable_pi_lambda _ (fun k ↦ (measurable_pi_apply k).fst)).aemeasurable
    (measurable_pi_lambda _ (fun k ↦ (measurable_pi_apply k).snd)).aemeasurable

/-- Finite clock prefixes retain their product law on regular histories. -/
theorem regularLaw_map_clock_prefix (n : ℕ) :
    (rates.regularLaw μ).map (fun h (k : Fin n) ↦ (h.val k).2) =
      Measure.pi (fun _ : Fin n ↦ rates.clockLaw) := by
  have h := rates.historyLaw_map_clock_prefix μ n
  rw [← rates.regularLaw_map_val μ,
    Measure.map_map (by fun_prop) measurable_subtype_coe] at h
  exact h

/-- The clock sequence on regular histories has the infinite product exponential law. -/
theorem regularLaw_map_clocks :
    (rates.regularLaw μ).map (fun h k ↦ (h.val k).2) =
      Measure.infinitePi (fun _ : ℕ ↦ rates.clockLaw) := by
  have h := rates.historyLaw_map_clocks μ
  rw [← rates.regularLaw_map_val μ,
    Measure.map_map (by fun_prop) measurable_subtype_coe] at h
  exact h

/-- The clocks remain mutually independent after transport to regular histories. -/
theorem regularLaw_iIndepFun_clocks :
    iIndepFun (fun k (h : RegularHistory S) ↦ (h.val k).2) (rates.regularLaw μ) := by
  have hc (k : ℕ) : Measurable (fun h : RegularHistory S ↦ (h.val k).2) := by
    exact (show Measurable (fun h : History S ↦ (h k).2) from
      (measurable_pi_apply k).snd).comp
        (measurable_subtype_coe :
          Measurable (Subtype.val : RegularHistory S → History S))
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map hc).mpr
  have marginal (k : ℕ) :
      (rates.regularLaw μ).map (fun h ↦ (h.val k).2) = rates.clockLaw := by
    have h := rates.historyLaw_map_clock μ k
    rw [← rates.regularLaw_map_val μ,
      Measure.map_map (by fun_prop) measurable_subtype_coe] at h
    exact h
  simp_rw [marginal]
  exact rates.regularLaw_map_clocks μ

/-- States and clocks retain their product law on regular histories. -/
theorem regularLaw_map_states_clocks :
    (rates.regularLaw μ).map
      (fun h ↦ ((fun k ↦ (h.val k).1), (fun k ↦ (h.val k).2))) =
      ((rates.regularLaw μ).map (fun h k ↦ (h.val k).1)).prod
        (Measure.infinitePi (fun _ : ℕ ↦ rates.clockLaw)) := by
  have h := rates.historyLaw_map_states_clocks μ
  rw [← rates.regularLaw_map_val μ,
    Measure.map_map (by fun_prop) measurable_subtype_coe,
    Measure.map_map (by fun_prop) measurable_subtype_coe] at h
  exact h

end BoundedRates

end

end LatticeProb.JumpChain
