/-
# Archived: the constant-one maximal inputs of the `ℓ¹`-ball reduction

This file is not part of the built library.  It keeps the named `Prop`s and the two conditional
theorems that stood in `LatticeProb/Prob/AkcogluKrengelAE/KrengelLpBallReduction.lean`.  Each of
the three maximal inequalities below is false as stated, so the theorems assuming them say
nothing:

* `KrengelLpBallWeakType 1` fails on `ℤ/7` with the rotation for `f = 2δ` at `0`, `3t - δ` at `2`
  and `0` elsewhere (`0 < δ < t/2`): the level set of the centred `ℓ¹`-ball maximal function at
  `t` is `{1}`, where `f = 0`, so `t μ{M > t} = t/7 > 0 = ∫_{M > t} f`.
* `KrengelMaximalInputCentred d c` fails for every `d ≥ 1`: the supremum includes `N = 0`, where
  the box is empty and the centred average is `-∫ h` (`not_krengelMaximalInputCentred` in the
  library).  Consequently `L1BallCoverTransfer` is an implication from a false premise.
* `MultiParameterMaximalErgodicRestricted 1` fails for `c = (2)`, whose boxes have even lengths
  only: on `ℤ/n` (`n ≥ 5`) with the rotation, `f = ε` at `0`, `2t` at `1` and `0` elsewhere
  (`ε < t`) has level set `{0}`, so `t/n > ε/n = ∫_{level set} f`.

The target `KrengelLpBall d` itself (with some constant `C`) is the classical maximal theorem and
stays in `BallMaximalLp.lean`.
-/
import LatticeProb.Prob.AkcogluKrengelAE.KrengelLpBallReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The multiparameter **weak-type `(1,1)`** input for the `ℓ¹`-ball maximal. -/
def KrengelLpBallWeakType (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (T : Site d → Ω → Ω),
      (∀ x, MeasurePreserving (T x) μ μ) →
      (∀ x y, T (x + y) = T x ∘ T y) →
      ∀ f : Ω → ℝ≥0∞, Measurable f →
        ∀ t : ℝ, 0 < t →
          ENNReal.ofReal t * μ {ω | ENNReal.ofReal t < l1BallMax T f ω} ≤
            ∫⁻ ω, ({ω | ENNReal.ofReal t < l1BallMax T f ω}.indicator f) ω ∂μ


/-- **The Marcinkiewicz reduction.** -/
theorem KrengelLpBall_of_weakType (hweak : KrengelLpBallWeakType d) : KrengelLpBall d := by
  intro p hp
  refine ⟨(p / (p - 1)) ^ p, by positivity, ?_⟩
  intro Ω _ μ hprob T hT hadd f hf
  exact marcinkiewicz_abstract μ (l1BallMax T f) f p hp
    (measurable_l1BallMax (fun x => (hT x).measurable) hf) hf
    (hweak μ hprob T hT hadd f hf)


/-- **The centred anchored-box weak-type `(1,1)` input** (the true replacement for the false
`AnchoredBoxMaximal`).  To be identified with, and later replaced by,
`LatticeProb.AnchoredBoxMaximalCentred` (`AnchoredBoxMean.lean`, branch `ds-errata`) once both
branches reach `main`. -/
def KrengelMaximalInputCentred (d : ℕ) (c : Fin d → ℝ) : Prop :=
  (∀ i, 0 ≤ c i) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    ∀ (h : Ω → ℝ), Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
      ∀ t : ℝ, 0 < t →
        ENNReal.ofReal t * μ {ω | ENNReal.ofReal t <
            ⨆ N : ℕ, ENNReal.ofReal |anchoredBoxAvgCentred μ h τ c N ω|} ≤
          ∫⁻ ω, ({ω | ENNReal.ofReal t <
            ⨆ N : ℕ, ENNReal.ofReal |anchoredBoxAvgCentred μ h τ c N ω|}.indicator
              (fun ω => ENNReal.ofReal |h ω - ∫ ω, h ω ∂μ|)) ω ∂μ


/-- **The multiparameter anchored-box (`Følner`) restricted maximal ergodic theorem** — the one
missing ingredient of the transfer.  For `f : Ω → ℝ≥0∞` measurable and `t > 0`, the anchored-box
level set satisfies the *restricted* weak type `t · μ{E_t} ≤ ∫_{E_t} f`, with the supremum over ALL
`N` (the same index set as the level set and the restricted integral).

**Proof shape (not Garsia).**  Garsia's argument needs a downward-closed index set and therefore
does *not* apply to the anchored-box family when the box lengths `{⌈N cᵢ⌉}` form a proper
subsequence of the naturals.  The correct proof is the **Følner maximal lemma** (the
covering/overlap argument comparing the sum over the level set with the sum over its shift),
iterated over the `d` coordinates; in `d = 1` the family is the interval family `[0, ⌈N c₀⌉)`, and
for `c₀ = 1` it is the full interval family, so the claim then reduces to the library's
one-parameter `LatticeProb.maximalSet_restricted_le`.  Together with the centred input
`KrengelMaximalInputCentred` (whole-space weak type) and the pointwise domination
`l1BallMax_le_orthantBoxMax`, it is what `L1BallCoverTransfer` needs. -/
def MultiParameterMaximalErgodicRestricted (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (τ : Site d → Ω → Ω),
      (∀ z, MeasurePreserving (τ z) μ μ) →
      (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
      ∀ (c : Fin d → ℝ), (∀ i, 0 ≤ c i) →
      ∀ (f : Ω → ℝ≥0∞), Measurable f →
        ∀ t : ℝ, 0 < t →
          ENNReal.ofReal t * μ {ω | ENNReal.ofReal t <
              ⨆ N : ℕ, avg (anchoredBox c N) (fun y => f (τ y ω))} ≤
            ∫⁻ ω, ({ω | ENNReal.ofReal t <
              ⨆ N : ℕ, avg (anchoredBox c N) (fun y => f (τ y ω))}.indicator f) ω ∂μ


/-! ### The stated geometric transfer -/

/-- **The geometry transfer, stated.**  Assuming the centred anchored-box weak-type input for
every side vector `c`, the `ℓ¹`-ball weak type holds.  The finite-set geometry is now fully proved:
the cover `l1Ball 0 R ⊆ ⋃_s orthantBox s R` (`l1Ball_subset_boxFinset` +
`boxFinset_eq_biUnion_orthantBox`), the volume lower bound `card_l1Ball_ge`, and the average
comparison `avg_l1Ball_le_orthantBoxMax` with explicit constant `(2d)^d`, independent of the radius
(so no `d!` is needed).  What remains isolated here is only the action/measure-theoretic step:
replacing `f (x + z)` by `f (τ z ·)` via the measure-preserving additive action `τ`
(`avg_map_addRight` is the finite-set core of that). -/
def L1BallCoverTransfer (d : ℕ) : Prop :=
  (∀ c : Fin d → ℝ, KrengelMaximalInputCentred d c) → KrengelLpBallWeakType d

/-- **The full reduction.** -/
theorem KrengelLpBall_of_centredBox (htransfer : L1BallCoverTransfer d)
    (hbox : ∀ c : Fin d → ℝ, KrengelMaximalInputCentred d c) : KrengelLpBall d :=
  KrengelLpBall_of_weakType (htransfer hbox)

end

end LatticeProb
