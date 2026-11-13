/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48SecondMoment at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CircleConditioning

/-!
# The unconditional second-moment Fubini split

This is the corrected (4.30)–(4.31): the global good-event indicator is absent.
The only regularity inputs are integrability of the spatial product kernel and
of the squared spatial integral. These are ordinary Fubini hypotheses, not a
hypothesis of the desired near/far bound.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

/-- Fubini expands the second moment of a spatial integral into its signed
pair covariance. The product integral identity itself requires no pointwise
integrability assumption because the Bochner integral has the standard zero
convention; the stated joint integrability justifies changing the order. -/
theorem prop48_secondMoment_fubini
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    {P : Measure Ω} {μ : Measure V} [SFinite P] [SFinite μ]
    (a : Ω → V → ℝ)
    (htriple : Integrable (fun t : Ω × (V × V) =>
      a t.1 t.2.1 * a t.1 t.2.2) (P.prod (μ.prod μ))) :
    ∫ ω, (∫ z, a ω z ∂μ) ^ (2 : ℕ) ∂P =
      ∫ p : V × V, (∫ ω, a ω p.1 * a ω p.2 ∂P) ∂(μ.prod μ) := by
  calc
    (∫ ω, (∫ z, a ω z ∂μ) ^ (2 : ℕ) ∂P) =
        ∫ ω, (∫ p : V × V, a ω p.1 * a ω p.2 ∂(μ.prod μ)) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [integral_prod_mul]
      ring
    _ = ∫ p : V × V, (∫ ω, a ω p.1 * a ω p.2 ∂P) ∂(μ.prod μ) :=
      integral_integral_swap htriple

/-- Joint integrability of the pair kernel already implies integrability of
The squared spatial integral, so the latter need not be a separate source
assumption when applying the Fubini split. -/
theorem prop48_square_integrable_of_triple
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    {P : Measure Ω} {μ : Measure V} [SFinite P] [SFinite μ]
    (a : Ω → V → ℝ)
    (htriple : Integrable (fun t : Ω × (V × V) =>
      a t.1 t.2.1 * a t.1 t.2.2) (P.prod (μ.prod μ))) :
    Integrable (fun ω => (∫ z, a ω z ∂μ) ^ (2 : ℕ)) P := by
  have hi : Integrable (fun ω => ∫ p : V × V,
      a ω p.1 * a ω p.2 ∂(μ.prod μ)) P := htriple.integral_prod_left
  apply hi.congr
  filter_upwards [] with ω
  rw [integral_prod_mul]
  ring

/-- Source-faithful one-sided version of the split: the near calculation only
needs an upper bound on covariance. The far calculation can use the stronger
absolute A.3 estimate. -/
theorem prop48_secondMoment_near_far_positive_split
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    {P : Measure Ω} {μ : Measure V} [SFinite P] [SFinite μ]
    (a : Ω → V → ℝ)
    (S : Set (V × V)) (hS : MeasurableSet S)
    (htriple : Integrable (fun t : Ω × (V × V) =>
      a t.1 t.2.1 * a t.1 t.2.2) (P.prod (μ.prod μ)))
    (hsquare : Integrable (fun ω => (∫ z, a ω z ∂μ) ^ (2 : ℕ)) P) :
    (∫⁻ ω, ENNReal.ofReal ((∫ z, a ω z ∂μ) ^ (2 : ℕ)) ∂P) ≤
      (∫⁻ p in S, ENNReal.ofReal
        (∫ ω, a ω p.1 * a ω p.2 ∂P) ∂(μ.prod μ)) +
      (∫⁻ p in Sᶜ, ENNReal.ofReal
        (∫ ω, a ω p.1 * a ω p.2 ∂P) ∂(μ.prod μ)) := by
  let C : V × V → ℝ := fun p => ∫ ω, a ω p.1 * a ω p.2 ∂P
  have hnonneg : 0 ≤ᵐ[P] fun ω => (∫ z, a ω z ∂μ) ^ (2 : ℕ) :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hFubini := prop48_secondMoment_fubini a htriple
  have hC : Integrable C (μ.prod μ) := htriple.swap.integral_prod_left
  have hCpos : Integrable (fun p => max (C p) 0) (μ.prod μ) := hC.pos_part
  have hmono : ∫ p, C p ∂(μ.prod μ) ≤
      ∫ p, max (C p) 0 ∂(μ.prod μ) :=
    integral_mono hC hCpos fun p => le_max_left _ _
  calc
    (∫⁻ ω, ENNReal.ofReal ((∫ z, a ω z ∂μ) ^ (2 : ℕ)) ∂P) =
        ENNReal.ofReal (∫ ω, (∫ z, a ω z ∂μ) ^ (2 : ℕ) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hsquare hnonneg).symm
    _ = ENNReal.ofReal (∫ p, C p ∂(μ.prod μ)) := by rw [hFubini]
    _ ≤ ENNReal.ofReal (∫ p, max (C p) 0 ∂(μ.prod μ)) :=
      ENNReal.ofReal_le_ofReal hmono
    _ = ∫⁻ p, ENNReal.ofReal (max (C p) 0) ∂(μ.prod μ) :=
      ofReal_integral_eq_lintegral_ofReal hCpos
        (Filter.Eventually.of_forall fun p => le_max_right _ _)
    _ = ∫⁻ p, ENNReal.ofReal (C p) ∂(μ.prod μ) := by
      congr 1
      funext p
      simp [ENNReal.ofReal_max]
    _ = (∫⁻ p in S, ENNReal.ofReal (C p) ∂(μ.prod μ)) +
        (∫⁻ p in Sᶜ, ENNReal.ofReal (C p) ∂(μ.prod μ)) :=
      (lintegral_add_compl (μ := μ.prod μ) (fun p => ENNReal.ofReal (C p)) hS).symm

end MatedCRTHarmonic.GMS4

