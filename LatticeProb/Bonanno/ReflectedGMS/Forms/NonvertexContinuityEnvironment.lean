/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.NonvertexContinuityEnvironment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.NonvertexJumpsFromEnergyBudget
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialCutoffEnvironment

/-!
# `hcont` at the environment level, and `hlift` from `hΦ` alone

`Process/SpatialExtensionEnvironment.ae_hlift_of_cutoffs_and_continuity` reduces the `hlift`
binder of the invariance assembly to two inputs:

* `hcut`, the spatial cutoff family of manuscript `p:lem:spatialcutoffs` — already discharged
  from the harmonic-coordinate conclusions by
  `Process/SpatialCutoffEnvironment.ae_hasSpatialCutoffs_of_isHarmonicCoordinate`;
* `hcont`, the nonvertex half of manuscript `p:prop:purejump`.

This file discharges `hcont` **from the same `hcut`**, by instantiating
`Forms/NonvertexJumpsFromEnergyBudget.ae_noJumpsAtNonvertexTimes_of_cutoffs` at the canonical
summable fast clock — which is exactly where the `hcont` binder lives, and which is what
supplies the `Summable m` that the energy budget of `Forms/FullEnergyPathNoNonvertexJumps`
needs (`summableFastRate_spec`).  The plumbing is the same as in
`ae_hreg_of_inputs`: the fast-clock walk, the rate identity `π / (π / w) = w`, and the
compact-time spatial bound of `r:eq:localbounded`.

Consequence (`ae_hlift_of_isHarmonicCoordinate`): `hlift` follows from `hΦ` together with the
invariance assembly's own ambient hypotheses `MassTransport` and `FiniteEnergyMoment`.  No new
named input is introduced anywhere in this file.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.NonvertexContinuityEnvironment

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.PathwiseClockClauseLift ReflectedGMS.InvarianceAssemblyNoReturn
open ReflectedGMS.SpatialExtensionConstruction

/-- **`hcont` from `hcut`.**  The statement is verbatim the `hcont` binder of
`Process/SpatialExtensionEnvironment.ae_hreg_of_cutoffs_and_continuity`. -/
theorem ae_hcont_of_cutoffs (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hcut : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        HasSpatialCutoffs (decode e).graph (fastSpeed e D hG) (lexMinField.at e) (Φ.at e)) :
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
            SpatialExtensionChainJumps.NoJumpsAtNonvertexTimes
              (fun t => Existence.process D (summableFastRate e D hG) t ω) (Φ.at e) := by
  intro n
  have hMax := SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity
    ν hmt hFE.ne
  filter_upwards [hcut,
    AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses ν hmt hFE.ne hMax] with e hcute hlog
  intro hn hnt D hG hdat
  letI := hnt
  have hcutΦ := hcute hnt D hG hdat
  obtain ⟨hmin, hrate, hwalk, -⟩ := hdat
  obtain ⟨hw, hdom, hm, hmsum⟩ := summableFastRate_spec e D hG
  have hwalkw : IsReflectedWalk (decode e).graph (summableFastRate e D hG) hmin
      (Existence.processFamily D hG (summableFastRate e D hG)) :=
    canonical_isReflectedWalk_of_rate_le D hG hmin (summableFastRate e D hG) hw hdom
  have hrateq : (fun v => (decode e).graph.pi v / fastSpeed e D hG v) =
      summableFastRate e D hG := by
    funext v
    show (decode e).graph.pi v / ((decode e).graph.pi v / summableFastRate e D hG v) = _
    rw [div_div_eq_mul_div,
      mul_div_cancel_left₀ _ ((decode e).graph.pi_pos_of_connected hG v).ne']
  have hwalkm : IsReflectedWalk (decode e).graph
      (fun v => (decode e).graph.pi v / fastSpeed e D hG v) hmin
      (Existence.processFamily D hG (summableFastRate e D hG)) := by
    rw [hrateq]
    exact hwalkw
  have hm' : ∀ v, 0 < fastSpeed e D hG v := hm
  have hmsum' : Summable (fastSpeed e D hG) := hmsum
  obtain ⟨r₀, C, hr₀, hC, ho, hD, hW⟩ := hlog (lexMinField.at e) ⟨n, hn⟩
  have hbdd := LogCutoffSpatialBoundedness.reflected_ae_forall_bddAbove_norm_on_boundedTime
    (decode e) (decode_geometry e) (lexMinField.at e) (isCellRepresentative_lexMinField e)
    (Existence.processFamily D hG (summableFastRate e D hG)) hwalkw hw ⟨n, hn⟩ hr₀ hC ho hD hW
  exact NonvertexJumpsFromEnergyBudget.ae_noJumpsAtNonvertexTimes_of_cutoffs
    hwalkm hG hm' hmsum' (lexMinField.at e) (Φ.at e) hcutΦ ⟨n, hn⟩ hbdd

end ReflectedGMS.NonvertexContinuityEnvironment
