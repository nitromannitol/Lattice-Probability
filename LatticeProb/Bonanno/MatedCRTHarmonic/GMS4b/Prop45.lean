/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.Prop45 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Lemma47

/-!
# [18] Proposition 4.5: the global regularity event `E^ε`

Source: [18] Proposition 4.5 and its proof. For
`ρ ∈ (0, 1)`, `q ∈ (0, 2/(2+γ)²)`, `ζ ∈ (0, q/4)`, `E^ε = E^ε(ρ, q, ζ)` is the event that
1. for each `z ∈ B_ρ(0)`, `diam(η([τ_z − ε, τ_z + ε])) ≤ ε^q` and `deg^ε_in(z) + deg^ε_out(z) ≤ ε^{−ζ}`;
2. `sup_{z ∈ B_ρ(0)} |h_{ε^{q−4ζ}}(z)| ≤ 2q log ε⁻¹`, and the same for the IG field `h^IG` (4.11).
"There exists `α = α(γ, q, ζ) > 0` such that for `ε ∈ (0, 1)`, `P[E^ε] ≥ 1 − O_ε(ε^α)`."

Proof (source): condition 1 from Lemmas 2.7, 4.6, 4.7 ("when we apply Lemma 2.7, we note that `η([τ_z − ε, τ_z + ε])`
is contained in the union of at most three of the cells"; here: two `ε`-segments containing `z`, with a slightly
larger `q′`), condition 2 from [MS16b] Proposition 2.4 (`CircleAverageSupBound`).

`prop45_holds` is stated on L27's cell model with the circle-average processes `H` of `h` and `H^IG` of `h^IG` as
parameters; its conclusion is `P[(E^ε)ᶜ] ≤ C ε^α`, i.e. G4's `L27RegularityFailureInput M.P (prop45Event …) (C ε^α)`
(`GMS4/Prop48.lean`, which unfolds to exactly this inequality). The inner-degree input is the conclusion of [18]
Lemma 4.6 (`InnerDegreeBound`), supplied by the inner-degree bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Asymptotics
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.GMSLemma27

variable {γ : ℝ}

/-- **The event `E^ε(ρ, q, ζ)` of [18] Proposition 4.5**, for circle-average processes
`H r z ω = h_r(z)` and `HIG r z ω = h^IG_r(z)`. -/
def prop45Event (M : CellModel γ) (H HIG : ℝ → ℂ → M.Ω → ℝ) (ε ρ q ζ : ℝ) : Set M.Ω :=
  {ω | ∀ z ∈ ball (0 : ℂ) ρ, windowDiam ε (M.curve ω) z ≤ ε ^ q ∧
      (((degreeIn ε (M.curve ω) z + degreeOut ε (M.curve ω) z : ℕ∞)) : ℝ≥0∞) ≤ ENNReal.ofReal (ε ^ (-ζ))} ∩
    {ω | ∀ z ∈ ball (0 : ℂ) ρ, |H (ε ^ (q - 4 * ζ)) z ω| ≤ 2 * q * Real.log ε⁻¹ ∧
      |HIG (ε ^ (q - 4 * ζ)) z ω| ≤ 2 * q * Real.log ε⁻¹}

/-- `(log ε⁻¹)^a ≤ ε^{−ζ}/2` for small `ε`. -/
theorem eventually_log_rpow_le (a : ℝ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.log ε⁻¹ ^ a ≤ ε ^ (-ζ) / 2 := by
  have h := (isLittleO_log_rpow_rpow_atTop a hζ).bound (show (0 : ℝ) < 1 / 2 by norm_num)
  have h' := tendsto_inv_nhdsGT_zero.eventually h
  filter_upwards [h', self_mem_nhdsWithin] with ε hε hpos
  have hpos' : (0 : ℝ) < ε := hpos
  have hx : (ε⁻¹) ^ ζ = ε ^ (-ζ) := by rw [Real.inv_rpow hpos'.le, Real.rpow_neg hpos'.le]
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos' _)] at hε
  calc Real.log ε⁻¹ ^ a ≤ |Real.log ε⁻¹ ^ a| := le_abs_self _
    _ ≤ 1 / 2 * ε ^ (-ζ) := hε
    _ = ε ^ (-ζ) / 2 := by ring

end MatedCRTHarmonic.GMS4b
