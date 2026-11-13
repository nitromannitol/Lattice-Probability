/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Lemma34 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Annulus
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Recurrence

/-!
# GMS [18] Lemma 3.4, deterministic form, and the conductance bound behind Theorem 1.4

Source: GMS [18] Lemma 3.4 and the proof of Theorem 1.4 ([18]): (3.15) reads `A / log(ε⁻¹ ∧ s⁻¹)` (∧, not ∨), and the
Dirichlet-principle step of Theorem 1.4 is an inequality.

Fix a centre `z` and radii `0 < r₁ < r₂`, the open annulus `D = annulusSet z r₁ r₂` and the harmonic
function `logRad z r₂ r₁` (`0` on `∂B_{r₂}(z)`, `1` on `∂B_{r₁}(z)`). [18]'s `f^s_ε` of Lemma 3.4 is the
sampled function (3.11) on `V(D)`, extended by `1` on `V(B̄_{r₁}(z))` and by `0` elsewhere:

* `annRef H z r₁ r₂ x`: a reference point of the cell `H_x`, on the inner circle if the cell meets it,
  else on the outer circle if it meets it (so that the sampled boundary values are exactly `1`, resp. `0`);
* `annTest H z r₁ r₂`: the extended sampled function;
* `energy_annTest_le` (**pasting**): if every cell meeting `B̄_{r₂}(z)` has diameter `< r₂ − r₁`, then
  `annTest` vanishes off `V(B_{r₂}(z))` and its energy is at most `Energy(f^ε; G(V(D)))`;
* `lemma34` (**[18] Lemma 3.4 with the conductance bound of Theorem 1.4**, centre `0`): on the Lemma 2.7
  event and the three Proposition 2.10 inputs `(D, |∇f|²)`, `(D, 1)`, `(B_{ρ₁}(0), g)`, the effective
  conductance from the root to the complement of `V(B_ρ(0))` is at most an explicit
  `lemma34Bound s ρ δ w A η`, whose leading term is `6πA / log(ρ/s)`; every other term is a power of
  `δ, w, η` against inverse powers of `s` and of `log(ρ/s)` (the dyadic grid of (c4) is replaced by taking
  `s` itself as the parameter).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped ENNReal Classical Topology

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-! ### Reference points and the sampled test function -/

/-- A reference point of `H_x` for the annulus between `r₁` and `r₂` about `z`: on the inner circle if
The cell meets it, else on the outer circle if it meets it, else any point of the cell. -/
def annRef (z : ℂ) (r₁ r₂ : ℝ) (x : V) : ℂ :=
  if h : (H.cell x ∩ {u | ‖u - z‖ = r₁}).Nonempty then h.some
  else if h' : (H.cell x ∩ {u | ‖u - z‖ = r₂}).Nonempty then h'.some
  else (cell_nonempty H x).some

theorem annRef_mem (z : ℂ) (r₁ r₂ : ℝ) (x : V) : annRef H z r₁ r₂ x ∈ H.cell x := by
  unfold annRef
  split_ifs with h h'
  · exact h.some_mem.1
  · exact h'.some_mem.1
  · exact (cell_nonempty H x).some_mem

theorem norm_annRef_inner {z : ℂ} {r₁ r₂ : ℝ} {x : V}
    (h : (H.cell x ∩ {u | ‖u - z‖ = r₁}).Nonempty) : ‖annRef H z r₁ r₂ x - z‖ = r₁ := by
  unfold annRef
  rw [dite_eq_left h]
  exact h.some_mem.2

theorem norm_annRef_outer {z : ℂ} {r₁ r₂ : ℝ} {x : V}
    (h : ¬ (H.cell x ∩ {u | ‖u - z‖ = r₁}).Nonempty)
    (h' : (H.cell x ∩ {u | ‖u - z‖ = r₂}).Nonempty) : ‖annRef H z r₁ r₂ x - z‖ = r₂ := by
  unfold annRef
  rw [dite_eq_right h, dite_eq_left h']
  exact h'.some_mem.2

/-! ### The Lemma 3.4 bound (centre `0`) -/

theorem ennreal_add_le_ofReal {x y : ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : x ≤ ENNReal.ofReal a) (hy : y ≤ ENNReal.ofReal b) : x + y ≤ ENNReal.ofReal (a + b) := by
  rw [ENNReal.ofReal_add ha hb]; exact add_le_add hx hy

theorem ennreal_mul_le_ofReal {x y : ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a)
    (hx : x ≤ ENNReal.ofReal a) (hy : y ≤ ENNReal.ofReal b) : x * y ≤ ENNReal.ofReal (a * b) := by
  rw [ENNReal.ofReal_mul ha]; exact mul_le_mul' hx hy

/-- The explicit error term of the deterministic Lemma 3.4 (`ℓ = log(ρ/s)`):
`3 [A·2π/ℓ + η + L_F δ (A π ρ² + η) + M_F (A V_g + η)] + 24 Λ² δ² [A π ρ² + η + A V_g + η]` with
`Λ = 4/(ℓ s²)`, `L_F = 2/(ℓ² s³)`, `M_F = 4/(ℓ² s²)` and `V_g = 8πw(s + 2w) + 8πw(ρ + 2w)`. -/
def lemma34Bound (s ρ δ w A η : ℝ) : ℝ :=
  3 * ((A * (2 * π / Real.log (ρ / s)) + η) +
      2 * ((Real.log (ρ / s)) ^ 2 * s ^ 3)⁻¹ * δ * (A * (π * ρ ^ 2) + η) +
      ((Real.log (ρ / s)) ^ 2 * (s / 2) ^ 2)⁻¹ *
        (A * (8 * π * w * (s + 2 * w) + 8 * π * w * (ρ + 2 * w)) + η)) +
    24 * (Real.log (ρ / s) * (s / 2) ^ 2)⁻¹ ^ 2 * δ ^ 2 *
      ((A * (π * ρ ^ 2) + η) + (A * (8 * π * w * (s + 2 * w) + 8 * π * w * (ρ + 2 * w)) + η))

theorem lemma34Bound_nonneg {s ρ δ w A η : ℝ} (hs : 0 < s) (hsρ : s < ρ) (hδ : 0 ≤ δ) (hw : 0 ≤ w)
    (hA : 0 ≤ A) (hη : 0 ≤ η) : 0 ≤ lemma34Bound s ρ δ w A η := by
  have hρ : 0 < ρ := hs.trans hsρ
  have hℓ : 0 < Real.log (ρ / s) := Real.log_pos ((one_lt_div hs).mpr hsρ)
  unfold lemma34Bound
  positivity

end MatedCRTHarmonic.GMS3
