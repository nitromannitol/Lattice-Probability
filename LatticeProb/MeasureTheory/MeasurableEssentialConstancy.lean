import LatticeProb.MeasureTheory.EssentialConstancyDistance

/-! # Measurability of essential constancy -/

set_option autoImplicit false

open MeasureTheory Filter

namespace LatticeProb

/-- For a jointly measurable family, the parameters whose sections are almost
 everywhere constant form a measurable set. -/
theorem measurableSet_ae_constant_section
    {Θ α E : Type*} [MeasurableSpace Θ] [MeasurableSpace α]
    [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure α) [SFinite μ] (hμ : μ ≠ 0)
    (F : Θ × α → E) (hF : Measurable F) :
    MeasurableSet {θ : Θ | ∃ c : E, ∀ᵐ x ∂μ, F (θ, x) = c} := by
  have hfirst : Measurable (fun z : Θ × (α × α) => F (z.1, z.2.1)) :=
    hF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hsecond : Measurable (fun z : Θ × (α × α) => F (z.1, z.2.2)) :=
    hF.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have htest : Measurable (fun θ : Θ =>
      ∫⁻ z : α × α, ENNReal.ofReal (min 1 (dist (F (θ, z.1)) (F (θ, z.2))))
        ∂(μ.prod μ)) :=
    ((measurable_const.min (hfirst.dist hsecond)).ennreal_ofReal).lintegral_prod_right'
  have hset := measurableSet_eq_fun htest
    (measurable_const : Measurable (fun _ : Θ => (0 : ENNReal)))
  convert hset using 1
  ext θ
  exact (lintegral_bounded_dist_eq_zero_iff_ae_constant μ hμ (fun x => F (θ, x))
    (hF.comp (measurable_const.prodMk measurable_id))).symm

end LatticeProb
