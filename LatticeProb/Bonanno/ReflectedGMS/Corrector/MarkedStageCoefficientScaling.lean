/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedStageCoefficientScaling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedStageFieldCovariance

/-!
# Quadratic scaling of the stage coefficients, and finiteness of the stage defects

Two independent consequences of `Corrector/MarkedStageFieldCovariance`, both feeding the
producer route for `SpecificEnergyConvergence.MarkedNestedProjectionBound`.

## 1. `q_e` scales quadratically (manuscript tex:480)

`MarkedMassTransportProducer.SimilarityCovariantField` (:337) — the structural hypothesis under
which the endpoint-spread/owner-block transport of a coefficient field is a legitimate degree
`-2` test kernel for `s:eq:MTP` — has four clauses.  Its *weight* clause,

`Q.weight (markedSimilarity s u hs p) (σ q.1, σ q.2) = ENNReal.ofReal (s ^ 2) * Q.weight p q`,

is the only one that mentions the field at all; the other three are statements about cells,
owner squares and areas.  For the two coefficients of `s:prop:projection` — the energy
coefficient `c_e ‖∇_e Φ‖²` and the signed pairing coefficient `c_e ⟪∇_e Φ₁, ∇_e Φ₂⟫` — that
clause is proved here at the level of decoded vertices
(`conductance_mul_normSq_relabel`, `conductance_mul_inner_relabel`), for **any** pair of fields
whose increments transport, hence in particular for the gated stage fields of
`Corrector/MarkedStageFieldCovariance`, at **every** marked configuration
(`conductance_mul_normSq_stageField`, `conductance_mul_inner_stageFields`).

Conductances are unchanged by a physical similarity and both increments pick up `s`, so the
coefficient picks up exactly `s²`.

## 2. The stage defects are finite as soon as the stage energies are

`Corrector/MarkedStagePythagoras`-style polarization routes to the keystone carry two separate
finiteness inputs, `e_n < ∞` and `‖g_m − g_n‖_*² < ∞`.  The second is not independent:
`markedStageDefect_ne_top` derives it from the two stage energies through the checked
`SpecificEnergyPolarization.rootedSpecificEnergyDensity_add_le` (`ρ_{θ+η} ≤ 2ρ_θ + 2ρ_η`) and
the sign symmetry `rootedSpecificEnergyDensity_neg` proved here.  Only `hmeas` is used besides.

## What is **not** proved

`SimilarityCovariantField` itself.  Its remaining obstruction is *not* the coefficient: it is the
**label-level bijection** `σ : ℕ ≃ ℕ` that all four clauses are quantified over, which must carry
the cells of `p.1` to the cells of `similarityTargetEnv s u hs p.1` — and in particular must map
inactive labels to inactive labels, since `labelCell` of an inactive label is empty.  A search of
the three trees finds `σ : ℕ ≃ ℕ` only inside the *statements*
`MarkedMassTransportProducer.SimilarityCovariantField`,
`SpecificEnergyRedistribution.OwnedEdgeField.ReRootingCovariant`,
`OwnedFieldPairingTransport.PairingReRooting` and
`MeasurableEndpointTransport`'s structural predicate: **no producer exists anywhere**, not even
for the translation case.  `EnvironmentLaws.isSimilarity_similarityTargetEnv` supplies only an
equivalence of the *active* vertex subtypes (`canonicalVertexEquiv`), and extending it to `ℕ`
needs the two inactive label sets to be equinumerous, which no checked result provides.

This file proves no main theorem.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.MarkedStageCoefficientScaling

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open MarkedMassTransportProducer SpecificEnergyDensitySimilarity MarkedStageFieldCovariance

/-! ### The coefficient scales quadratically -/

section Scaling

variable {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
  {rel : Vertex e.val ≃ Vertex e'.val}

/-- **The signed pairing coefficient `q_e = c_e ⟪∇_e Φ₁, ∇_e Φ₂⟫` scales quadratically.** -/
theorem conductance_mul_inner_relabel (h : IsSimilarityRelabel s u hs e e' rel)
    {Phi1 Phi2 : Vertex e.val → Plane} {Psi1 Psi2 : Vertex e'.val → Plane}
    (h1 : GradientTransported s rel Phi1 Psi1) (h2 : GradientTransported s rel Phi2 Psi2)
    (v w : Vertex e.val) :
    (decode e').graph.c (rel v) (rel w) *
        inner ℝ (Psi1 (rel w) - Psi1 (rel v)) (Psi2 (rel w) - Psi2 (rel v))
      = s ^ 2 * ((decode e).graph.c v w * inner ℝ (Phi1 w - Phi1 v) (Phi2 w - Phi2 v)) := by
  rw [h.2 v w, h1 v w, h2 v w, real_inner_smul_left, real_inner_smul_right]
  ring

end Scaling

/-! ### The same at the gated stage fields, at every marked configuration -/

section Stage

variable {s : ℝ} {u : Plane} {hs : 0 < s} {p : MarkedEnvironment}
  {rel : Vertex p.1.val ≃ Vertex (markedSimilarity s u hs p).1.val}

end Stage

/-! ### Finiteness of the stage defects -/

/-- The rooted specific-energy density does not see the sign of the field. -/
theorem rootedSpecificEnergyDensity_neg {V : Type*} [Countable V] (F : IndexedCells V)
    (Phi : V → Plane) (z : Plane) :
    rootedSpecificEnergyDensity F (fun u => -Phi u) z = rootedSpecificEnergyDensity F Phi z := by
  have hcell : ∀ v : V, specificEnergyDensity F (fun u => -Phi u) v
      = specificEnergyDensity F Phi v := by
    intro v
    show (∑' w : V, ENNReal.ofReal (F.graph.c v w) *
          ENNReal.ofReal (‖(fun u => -Phi u) w - (fun u => -Phi u) v‖ ^ 2)) /
        (2 * ENNReal.ofReal (StatementIngredients.cellArea F v))
      = (∑' w : V, ENNReal.ofReal (F.graph.c v w) * ENNReal.ofReal (‖Phi w - Phi v‖ ^ 2)) /
        (2 * ENNReal.ofReal (StatementIngredients.cellArea F v))
    congr 1
    refine tsum_congr fun w => ?_
    have hnorm : ‖(fun u => -Phi u) w - (fun u => -Phi u) v‖ = ‖Phi w - Phi v‖ := by
      show ‖-Phi w - -Phi v‖ = ‖Phi w - Phi v‖
      rw [neg_sub_neg, norm_sub_rev]
    rw [hnorm]
  show (rootAt F z).elim 0 (specificEnergyDensity F fun u => -Phi u)
    = (rootAt F z).elim 0 (specificEnergyDensity F Phi)
  cases hroot : rootAt F z with
  | none => simp
  | some v => simpa using hcell v

/-- The pointwise bound behind the finiteness of the stage defects:
`ρ(Φ₁ − Φ₂) ≤ 2 ρ(Φ₁) + 2 ρ(Φ₂)`. -/
theorem rootedSpecificEnergyDensity_sub_le {V : Type*} [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (Phi1 Phi2 : V → Plane) (z : Plane) :
    rootedSpecificEnergyDensity F (fun u => Phi1 u - Phi2 u) z
      ≤ 2 * rootedSpecificEnergyDensity F Phi1 z + 2 * rootedSpecificEnergyDensity F Phi2 z := by
  have hfun : (fun u => Phi1 u - Phi2 u) = fun u => Phi1 u + (fun w => -Phi2 w) u := by
    funext u
    exact sub_eq_add_neg _ _
  rw [hfun]
  refine le_trans
    (SpecificEnergyPolarization.rootedSpecificEnergyDensity_add_le F hF Phi1
      (fun w => -Phi2 w) z) ?_
  rw [rootedSpecificEnergyDensity_neg F Phi2 z]

/-- **The stage-`0` energy is finite with no projection input.**  `φ_0` is the centroid embedding
at every marked configuration, so `e_0 ≤ 2 M_π < ∞` by `s:lem:e0` alone.  This is the
anti-vacuity witness for the finiteness hypotheses below: their class is inhabited without
assuming the very bound they are used to prove. -/
theorem markedStageEnergy_zero_ne_top (ν : Measure Env) (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) : SpecificEnergyConvergence.markedStageEnergy ν 0 ≠ ∞ := by
  obtain ⟨hb, hM⟩ :=
    BaseSpecificEnergy.baseSpecificEnergy_le_two_mul_diamSqPiMoment_lt_top ν hν hFE.ne
  exact (lt_of_le_of_lt
    ((SpecificEnergyConvergence.markedStageEnergy_zero_le_baseSpecificEnergy ν).trans hb) hM).ne

end ReflectedGMS.MarkedStageCoefficientScaling
