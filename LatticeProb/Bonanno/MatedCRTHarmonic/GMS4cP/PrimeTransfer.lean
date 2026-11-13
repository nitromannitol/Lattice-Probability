/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.PrimeTransfer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TTransfer
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.L46SPrimeTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.LocalEvents

/-!
# The all-visit form of the (4.16) transfer of [18] Lemma 4.6

Source: [18] Lemma 4.6 and its proof via Lemma 4.3 and (4.16) (`2070–2116`).

The first-visit inner degree `deg^ε_in(z) = deg^ε_in(η, τ_z)` is not a function of the local data: the
excursions into an observation disk do not record which one visits `z` first. The **all-visit** event
`InnerAt c S ε N = {∃ t, c t ∈ S, deg^ε_in(c, t) ≥ N}` dominates the first-visit event, is local on the
non-escape event (`GMS4cP/LocalEvents.lean`), and the `innerDegreeBoundPolylog_prime_coupled` extends
L46S's Brownian-chain count to it on the γ-cone. Hölder's inequality (4.16) applied to the escape event and
The all-visit event then gives the first-visit polylog bound `InnerDegreeBoundPolylog` for the target.

`L43PLocalReconstruction` is the exact form of measurable Lemma 4.3 consumed here: one pair of Borel sets of
The observation `(h|_V, h^IG|_V, U)` which almost surely equals the escape and the all-visit non-escape events
under both laws.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4c

/-- The integer threshold equivalent to `deg > log(1/ε)^(k(1+ζ)+1)`. -/
def l43pThreshold (ε : ℝ) (k : ℕ) (ζ : ℝ) : ℕ :=
  ⌊Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)⌋₊ + 1

theorem ofReal_lt_coe_enat_iff (x : ℝ) (d : ℕ∞) :
    ENNReal.ofReal x < (d : ℝ≥0∞) ↔ ((⌊x⌋₊ + 1 : ℕ) : ℕ∞) ≤ d := by
  induction d using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rw [ENat.toENNReal_coe, Nat.cast_le]
    rcases le_or_gt x 0 with hx | hx
    · rw [ENNReal.ofReal_of_nonpos hx, Nat.floor_of_nonpos hx, zero_add, Nat.one_le_iff_ne_zero]
      simp [pos_iff_ne_zero]
    · rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx.le,
        Nat.add_one_le_iff, Nat.floor_lt hx.le]

end MatedCRTHarmonic.GMS4cP
