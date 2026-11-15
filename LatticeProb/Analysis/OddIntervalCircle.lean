import LatticeProb.Analysis.OddIntervalExtension
import Mathlib.Analysis.Fourier.AddCircle

/-! # Odd extensions on the circle -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- Away from the endpoint class, the lifted odd extension is odd. -/
theorem lift_oddIntervalExtension_neg {θ : ℝ} [Fact (0 < 2 * θ)]
    (f : ℝ → ℂ) {z : AddCircle (2 * θ)} (hz : z ≠ (θ : AddCircle (2 * θ))) :
    AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f) (-z) =
      -AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f) z := by
  let x : ℝ := AddCircle.equivIoc (2 * θ) (-θ) z
  have hx : x ∈ Ioc (-θ) (-θ + 2 * θ) :=
    (AddCircle.equivIoc (2 * θ) (-θ) z).property
  have hxcoe : (x : AddCircle (2 * θ)) = z := AddCircle.coe_equivIoc
  have hxne : x ≠ θ := by
    intro h
    apply hz
    simpa [h] using hxcoe.symm
  have hxlt : x < θ := by
    have hxle : x ≤ θ := by linarith [hx.2]
    exact lt_of_le_of_ne hxle hxne
  have hneg : -x ∈ Ioc (-θ) (-θ + 2 * θ) := by
    constructor <;> linarith [hx.1]
  rw [← hxcoe, ← AddCircle.coe_neg, AddCircle.liftIoc_coe_apply hneg,
    AddCircle.liftIoc_coe_apply hx, oddIntervalExtension_neg]

/-- The lifted odd extension is odd almost everywhere for normalized Haar measure. -/
theorem ae_lift_oddIntervalExtension_neg {θ : ℝ} [Fact (0 < 2 * θ)]
    (f : ℝ → ℂ) :
    ∀ᵐ z ∂AddCircle.haarAddCircle,
      AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f) (-z) =
        -AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f) z := by
  have hθ : 0 < θ := by linarith [Fact.out (p := 0 < 2 * θ)]
  have hθmem : θ ∈ Ioc (-θ) (-θ + 2 * θ) := by
    constructor <;> linarith
  have hv : ∀ᵐ z ∂(volume : Measure (AddCircle (2 * θ))),
      z ≠ (θ : AddCircle (2 * θ)) := by
    rw [← (AddCircle.measurePreserving_mk (2 * θ) (-θ)).map_eq]
    apply (ae_map_iff (AddCircle.measurePreserving_mk (2 * θ) (-θ)).measurable.aemeasurable
      (measurableSet_singleton _).compl).2
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc (-θ) (-θ + 2 * θ))).ae_ne θ] with x hx hne
    intro heq
    exact hne ((AddCircle.coe_eq_coe_iff_of_mem_Ioc hx hθmem).1 heq)
  rw [AddCircle.volume_eq_smul_haarAddCircle,
    Measure.ae_ennreal_smul_measure_eq (by positivity)] at hv
  filter_upwards [hv] with z hz
  exact lift_oddIntervalExtension_neg f hz

/-- The lift of an interval Lᵖ function is Lᵖ for normalized Haar measure. -/
theorem memLp_haar_lift_oddIntervalExtension {θ : ℝ} [Fact (0 < 2 * θ)]
    (hθ : 0 < θ) {p : ℝ≥0∞} {f : ℝ → ℂ}
    (hf : MemLp f p (volume.restrict (Ioo 0 θ))) :
    MemLp (AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f)) p
      AddCircle.haarAddCircle :=
  (memLp_haarAddCircle_iff).2 (memLp_lift_oddIntervalExtension hθ hf)

end LatticeProb
