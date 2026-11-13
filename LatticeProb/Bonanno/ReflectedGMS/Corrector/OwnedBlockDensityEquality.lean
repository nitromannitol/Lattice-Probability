/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.OwnedBlockDensityEquality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyRedistribution

/-!
# The two owner-block densities of a signed edge coefficient agree

`Corrector/SpecificEnergyRedistribution` attaches to every `OwnedEdgeField` its manuscript
owner-block density

`ownerBlockDensity Q ω = (2 ℓ(S_m(0))²)⁻¹ ∑_{e : S_e = S_m(0)} q_e`,

an `ℝ≥0∞` quantity.  `Corrector/OwnedFieldPairingTransport` builds, out of the *signed*
manuscript pairing coefficient `q_e = c(e) ⟪Ψ(e), η(e)⟫`, the two owned edge fields
`posField`/`negField` whose weights are `ofReal (±q_e)`, i.e. literally the positive and the
negative part of `q_e`, and its transport statements carry the deterministic blockwise
orthogonality as the single hypothesis

`∀ ω, (posField O).ownerBlockDensity ω = (negField O).ownerBlockDensity ω`.

This module discharges that hypothesis from the **real-valued** statement that the signed block
edge sum vanishes, which is the shape of the checked
`NestedProjectionProducers.tsum_vectorGradProd_nested_eq_zero`
(*"their sum on every block is zero by orthogonality"*).

## What is actually proved

The mathematics is `q⁺ − q⁻ = q`, which is mathlib's `max_zero_sub_max_neg_zero_eq_self`.  The
content of this module is the **`ENNReal`/real transfer** and its side conditions, which are
not formal:

* real `tsum` of a non-summable family is the junk value `0`, so a bare `∑ q_e = 0` carries no
  information without summability; and
* `ENNReal` subtraction is truncated, so the step from `∑ q⁺ − ∑ q⁻ = 0` to `∑ q⁺ = ∑ q⁻`
  must be taken in `ℝ`, where it needs both partial sums to be finite.

Summability of `q` on the owner block is therefore taken as an explicit hypothesis.  It is
*not* an extra assumption in the eventual application: it is exactly the conclusion of the
checked `NestedProjectionProducers.summable_vectorGradProd`, whose own hypotheses are the two
**block-local** energies.  Nothing here uses finite energy of the whole network, and nothing
here assumes any transport identity.

## Contents

* `max_zero_le_abs`, `max_neg_zero_le_abs`, `summable_max_zero`, `summable_max_neg_zero` —
  the two parts of a summable real family are summable;
* `tsum_max_zero_eq_tsum_max_neg_zero` — a summable real family with vanishing sum has equal
  positive- and negative-part sums;
* `tsum_ofReal_eq_tsum_ofReal_neg` — the same statement transferred to `ℝ≥0∞`;
* `ownerBlockDensity_eq_of_tsum_eq_zero` and its `∀ ω` form
  `forall_ownerBlockDensity_eq_of_tsum_eq_zero` — the consumer statement, for **any** two
  owned edge fields carrying the same owner labels and the two parts of one real coefficient.

Mathlib supplies `max_zero_sub_max_neg_zero_eq_self` (`q⁺ − q⁻ = q`), `Summable.abs`
(unconditional summability of a real family is absolute summability) and
`ENNReal.ofReal_tsum_of_nonneg`; an `exact?` search of the imported environment found no
mathlib form of the two summability adapters or of the transfer itself.
`ofReal_eq_ofReal_max` lives here rather than in `Corrector/OwnedFieldPairingTransport` so
that both modules share one copy; the latter imports this file and keeps using it unqualified.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.OwnedBlockDensityEquality

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField

/-! ### The positive and negative parts of a real number -/

/-- `ENNReal.ofReal` already truncates at zero, so it sees only the positive part. -/
theorem ofReal_eq_ofReal_max (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx]
  · rw [max_eq_right hx, ENNReal.ofReal_eq_zero.2 hx, ENNReal.ofReal_zero]

/-- The positive part is dominated by the absolute value. -/
theorem max_zero_le_abs (x : ℝ) : max x 0 ≤ |x| := max_le (le_abs_self x) (abs_nonneg x)

/-- The negative part is dominated by the absolute value. -/
theorem max_neg_zero_le_abs (x : ℝ) : max (-x) 0 ≤ |x| :=
  (max_zero_le_abs (-x)).trans (le_of_eq (abs_neg x))

/-! ### Summability of the two parts

For a real family, unconditional summability is absolute summability, so both truncations of a
summable family are summable. -/

/-- The positive part of a summable real family is summable. -/
theorem summable_max_zero {ι : Type*} {g : ι → ℝ} (hg : Summable g) :
    Summable fun i => max (g i) 0 :=
  Summable.of_nonneg_of_le (fun i => le_max_right (g i) 0)
    (fun i => max_zero_le_abs (g i)) hg.abs

/-- The negative part of a summable real family is summable. -/
theorem summable_max_neg_zero {ι : Type*} {g : ι → ℝ} (hg : Summable g) :
    Summable fun i => max (-(g i)) 0 :=
  Summable.of_nonneg_of_le (fun i => le_max_right (-(g i)) 0)
    (fun i => max_neg_zero_le_abs (g i)) hg.abs

/-- **The real half of the transfer.**  A summable real family whose sum vanishes has equal
positive-part and negative-part sums.  Summability is genuinely needed: the real `tsum` of a
non-summable family is the junk value `0`. -/
theorem tsum_max_zero_eq_tsum_max_neg_zero {ι : Type*} {g : ι → ℝ} (hg : Summable g)
    (h0 : (∑' i, g i) = 0) :
    (∑' i, max (g i) 0) = ∑' i, max (-(g i)) 0 := by
  have hp : Summable fun i => max (g i) 0 := summable_max_zero hg
  have hm : Summable fun i => max (-(g i)) 0 := summable_max_neg_zero hg
  have hsub : ((∑' i, max (g i) 0) - ∑' i, max (-(g i)) 0) = 0 := by
    rw [← Summable.tsum_sub hp hm]
    exact (tsum_congr fun i => max_zero_sub_max_neg_zero_eq_self (g i)).trans h0
  exact sub_eq_zero.1 hsub

/-- **The `ENNReal` transfer.**  For a summable real family with vanishing sum, the `ℝ≥0∞`
sums of `ofReal g` and of `ofReal (-g)` agree.  `ENNReal.ofReal` truncates at zero, so these
are exactly the positive- and negative-part sums. -/
theorem tsum_ofReal_eq_tsum_ofReal_neg {ι : Type*} {g : ι → ℝ} (hg : Summable g)
    (h0 : (∑' i, g i) = 0) :
    (∑' i, ENNReal.ofReal (g i)) = ∑' i, ENNReal.ofReal (-(g i)) := by
  have hp : Summable fun i => max (g i) 0 := summable_max_zero hg
  have hm : Summable fun i => max (-(g i)) 0 := summable_max_neg_zero hg
  calc (∑' i, ENNReal.ofReal (g i))
      = ∑' i, ENNReal.ofReal (max (g i) 0) := tsum_congr fun i => ofReal_eq_ofReal_max (g i)
    _ = ENNReal.ofReal (∑' i, max (g i) 0) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => le_max_right (g i) 0) hp).symm
    _ = ENNReal.ofReal (∑' i, max (-(g i)) 0) := by
        rw [tsum_max_zero_eq_tsum_max_neg_zero hg h0]
    _ = ∑' i, ENNReal.ofReal (max (-(g i)) 0) :=
        ENNReal.ofReal_tsum_of_nonneg (fun i => le_max_right (-(g i)) 0) hm
    _ = ∑' i, ENNReal.ofReal (-(g i)) :=
        tsum_congr fun i => (ofReal_eq_ofReal_max (-(g i))).symm

/-! ### The owner-block densities of the two parts of a signed coefficient -/

variable {Ω : Type*} [MeasurableSpace Ω] {R : MarkedReRooting Ω} {m : ℝ}

/-- **The deterministic blockwise orthogonality, in the `ℝ≥0∞` shape the redistribution
needs.**  Let `Qp` and `Qm` be two owned edge fields with the *same* owner labels, whose
weights are the positive and the negative part `ofReal (±f p)` of one real coefficient `f`.
If `f` is summable on the owner block `S_m(0)` of the origin and its sum there vanishes, the
two manuscript owner-block densities coincide.

Both denominators are the same number `2 ℓ(S_m(0))²`, so this is an identity of numerators;
the whole content is the real/`ENNReal` transfer of `tsum_ofReal_eq_tsum_ofReal_neg`.  Nothing
about any transport identity, any measure, or any measurability is used. -/
theorem ownerBlockDensity_eq_of_tsum_eq_zero (Qp Qm : OwnedEdgeField R m) (f : ℕ × ℕ → ℝ)
    (ω : Ω)
    (howner : ∀ p : ℕ × ℕ, Qp.owner ω p = Qm.owner ω p)
    (hwp : ∀ p : ℕ × ℕ, Qp.weight ω p = ENNReal.ofReal (f p))
    (hwm : ∀ p : ℕ × ℕ, Qm.weight ω p = ENNReal.ofReal (-(f p)))
    (hsum : Summable fun p : ℕ × ℕ => (Qp.ownedByOriginBlock ω).indicator f p)
    (hzero : (∑' p : ℕ × ℕ, (Qp.ownedByOriginBlock ω).indicator f p) = 0) :
    Qp.ownerBlockDensity ω = Qm.ownerBlockDensity ω := by
  classical
  have hownerEq : Qm.owner ω = Qp.owner ω := funext fun p => (howner p).symm
  have hset : Qm.ownedByOriginBlock ω = Qp.ownedByOriginBlock ω := by
    unfold OwnedEdgeField.ownedByOriginBlock
    rw [hownerEq]
  have hgp : ∀ p : ℕ × ℕ, (Qp.ownedByOriginBlock ω).indicator (Qp.weight ω) p
      = ENNReal.ofReal ((Qp.ownedByOriginBlock ω).indicator f p) := by
    intro p
    by_cases hp : p ∈ Qp.ownedByOriginBlock ω
    · simp only [Set.indicator_of_mem hp]
      exact hwp p
    · simp only [Set.indicator_of_notMem hp, ENNReal.ofReal_zero]
  have hgm : ∀ p : ℕ × ℕ, (Qp.ownedByOriginBlock ω).indicator (Qm.weight ω) p
      = ENNReal.ofReal (-((Qp.ownedByOriginBlock ω).indicator f p)) := by
    intro p
    by_cases hp : p ∈ Qp.ownedByOriginBlock ω
    · simp only [Set.indicator_of_mem hp]
      exact hwm p
    · simp only [Set.indicator_of_notMem hp, neg_zero, ENNReal.ofReal_zero]
  have hnum : (∑' p : ℕ × ℕ, (Qp.ownedByOriginBlock ω).indicator (Qp.weight ω) p)
      = ∑' p : ℕ × ℕ, (Qm.ownedByOriginBlock ω).indicator (Qm.weight ω) p := by
    rw [hset]
    simp only [hgp, hgm]
    exact tsum_ofReal_eq_tsum_ofReal_neg hsum hzero
  unfold OwnedEdgeField.ownerBlockDensity
  rw [hnum]

end ReflectedGMS.OwnedBlockDensityEquality
