/-
# Matching the thin-LSS bridge to the consumer vocabulary

The library's `thinLSS_bridge` is stated with the planar carrier `ℤ × ℤ`, the `ℓ^∞`
finite-range dependence predicate `KDependentPlanar 2`, the coordinatewise increasing-event
predicate `StrassenAux.IsIncreasingSet`, and the product Bernoulli field `bernoulliFieldPlanar
(1/8)`.  The rotor percolation argument consumes the same objects under the names `KDependent 2`,
`IsIncreasing`, and `bernoulliField (1/8)`.

This module records the exact match as an abstract statement inside the library, with no import
of the rotor development and no rotor file touched: it repeats the three consumer definitions
verbatim, proves each coincides definitionally with the library object, and restates the bridge
conclusion in that vocabulary.  A consumer can therefore apply the result directly after
identifying its own predicates with these.

The dense half remains an explicit hypothesis; no domination statement is proved here and no
`Prop` is frozen.
-/

import LatticeProb.Prob.Percolation.LSSThinFinal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-! ### The consumer vocabulary -/

set_option linter.deprecated false in
/-- The Bernoulli law on `Bool` with success probability `p`, as the consumer states it. -/
noncomputable def consumerBernoulli (p : NNReal) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

/-- The independent Bernoulli(`p`) product field on `ℤ × ℤ`, as the consumer states it. -/
noncomputable def consumerBernoulliField (p : NNReal) (hp : p ≤ 1) :
    Measure (PlanarCarrier → Bool) :=
  Measure.infinitePi (fun _ : PlanarCarrier => consumerBernoulli p hp)

/-- The consumer's increasing predicate: closure under increasing a `{0,1}`-field
coordinatewise. -/
def consumerIsIncreasing (A : Set (PlanarCarrier → Bool)) : Prop :=
  ∀ ω ω' : PlanarCarrier → Bool, ω ∈ A → (∀ z, ω z = true → ω' z = true) → ω' ∈ A

/-- The consumer's `k`-dependence predicate: finite index sets separated by more than `k` in one
coordinate have independent restrictions. -/
def consumerKDependent (k : ℕ) (μ : Measure (PlanarCarrier → Bool)) : Prop :=
  ∀ I J : Finset PlanarCarrier,
    (∀ i ∈ I, ∀ j ∈ J, (k : ℤ) < max |i.1 - j.1| |i.2 - j.2|) →
    IndepFun (fun ω : PlanarCarrier → Bool => fun i : I => ω i)
      (fun ω => fun j : J => ω j) μ

/-! ### The exact match -/

theorem consumerBernoulli_eq (p : NNReal) (hp : p ≤ 1) :
    consumerBernoulli p hp = bernoulli p hp :=
  rfl

theorem consumerBernoulliField_eq (p : NNReal) (hp : p ≤ 1) :
    consumerBernoulliField p hp = bernoulliFieldPlanar p hp :=
  rfl

theorem consumerIsIncreasing_iff (A : Set (PlanarCarrier → Bool)) :
    consumerIsIncreasing A ↔ StrassenAux.IsIncreasingSet A :=
  Iff.rfl

theorem consumerKDependent_iff (k : ℕ) (μ : Measure (PlanarCarrier → Bool)) :
    consumerKDependent k μ ↔ KDependentPlanar k μ :=
  Iff.rfl

/-! ### The bridge in the consumer vocabulary -/

/-- **The bridge in the consumer vocabulary.**  Given the dense domination hypothesis and a
fixed threshold `ε`, every probability `2`-dependent planar field with one-site probability at
most `2ε` is dominated by the product Bernoulli field of density `1/8` on increasing events.  The
statement is phrased with the consumer's predicates; the proof is the library bridge after the
definitional identifications above. -/
theorem consumerThin_of_dense {p ε : ℝ} (hε : 0 < ε) (hp : p ≤ 1 - 2 * ε)
    (hdense : DenseSevenEighths p) :
    ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
      (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
      ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
        μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A := by
  intro μ hμ hKD hsite A hA hinc
  rw [consumerKDependent_iff] at hKD
  rw [consumerIsIncreasing_iff] at hinc
  rw [consumerBernoulliField_eq]
  exact thinPlanar_of_dense (p := p) (ε := ε) hε.le hp hdense hKD hsite hA hinc

/-- **The existential form of the bridge in the consumer vocabulary.**  From the dense
domination hypothesis at density `p < 1`, there is `ε > 0` such that every probability
`2`-dependent planar field with one-site probability at most `2ε` is dominated by the product
Bernoulli field of density `1/8` on increasing events, with `ε` uniform over the field law. -/
theorem exists_consumerThin_of_dense {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
          μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A := by
  refine ⟨(1 - p) / 2, by linarith, ?_⟩
  intro μ hμ hKD hsite A hA hinc
  exact consumerThin_of_dense (p := p) (ε := (1 - p) / 2)
    (by linarith) (by linarith) hdense μ hμ hKD hsite A hA hinc

end LatticeProb.Percolation
