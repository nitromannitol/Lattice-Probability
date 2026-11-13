/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.SpatialCutoffEnvironment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialExtensionEnvironment
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpatialCutoffFromLocalMass

/-!
# `hcut` for the harmonic coordinate: manuscript `p:lem:spatialcutoffs`

This discharges the first of the two open inputs of
`Process/SpatialExtensionEnvironment.ae_hreg_of_cutoffs_and_continuity` — the spatial cutoff
family `hcut`, for the canonical summable fast speed `fastSpeed` and the canonical cell
representatives `lexMinField` — from the harmonic-coordinate conclusions `IsHarmonicCoordinate`
of main theorem 1, together with the main theorem's own hypotheses `MassTransport` and
`FiniteEnergyMoment`.

The three environment-level ingredients are all already proved elsewhere in the tree:

* `Spatial/SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity`
  and `Spatial/AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses` give, almost surely,
  the local diameter bound and the quadratic local-mass bound of Proposition `r:prop:log`;
* the `SublinearCorrector` clause of `IsHarmonicCoordinate` gives the uniform sublinear
  error of `Φ` against the representatives, hence a local bound on `Φ`;
* the `FullRectangleOrthogonality` clause gives finiteness of the patch energy of `Φ` on
  every rectangle.

The deterministic cutoff construction is `Forms/SpatialCutoffFromLocalMass`.  Nothing here
certifies `hcont` or any main theorem: this is an implication whose only open input is
`IsHarmonicCoordinate ν Φ`, which is exactly the `hΦ` binder of
`InvarianceAssemblyFourInputs.reflectedInvarianceConclusions_of_named_inputs_data_and_clocks_discharged`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.SpatialCutoffEnvironment

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks
open ReflectedWalk
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open QuenchedFormulation InvarianceMainStatement SpatialEnds
open ReflectedGMS.SpatialExtensionConstruction

/-! ## From the local mass bound to real summability -/

/-- Nonnegative real summability from a finite `ℝ≥0∞` series. -/
theorem summable_of_tsum_ofReal_ne_top {ι : Type*} (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (h : (∑' i, ENNReal.ofReal (f i)) ≠ ∞) : Summable f := by
  have hiff : (∑' i, ENNReal.ofReal (f i)) ≠ ∞ ↔ Summable f := by
    simpa only [ENNReal.ofReal, Real.coe_toNNReal _ (hf _)] using
      (ENNReal.tsum_coe_ne_top_iff_summable_coe (f := fun i => Real.toNNReal (f i)))
  exact hiff.1 h

/-- A finite diameter-weighted conductance mass on a patch is exactly the summability
hypothesis of the local radius-energy estimate. -/
theorem summable_diamSq_mul_pi_of_localMassENN_ne_top {V : Type*} [Countable V]
    (F : IndexedCells V) (A : Set V) (h : LogCutoff.localMassENN F A ≠ ∞) :
    Summable (fun v : A => Metric.diam (F.cell v.1 : Set Plane) ^ 2 * F.graph.pi v.1) := by
  refine summable_of_tsum_ofReal_ne_top _
    (fun v => mul_nonneg (sq_nonneg _) (F.graph.pi_nonneg v.1)) ?_
  rw [tsum_subtype A (fun v : V =>
      ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2 * F.graph.pi v)),
    ← AlmostSureCutoffBounds.localMassENN_eq_tsum_indicator F A]
  exact h

/-! ## `hcut` -/

/-- **The `hcut` input of `ae_hreg_of_cutoffs_and_continuity`, from the harmonic
coordinate.**  The conclusion is verbatim the `hcut` binder of that theorem (and of
`ae_hlift_of_cutoffs_and_continuity`).  The only open input is `IsHarmonicCoordinate ν Φ`,
i.e. the `hΦ` binder of the four-input invariance assembly. -/
theorem ae_hasSpatialCutoffs_of_isHarmonicCoordinate (ν : Measure Env)
    [IsProbabilityMeasure ν] (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ) :
    ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        HasSpatialCutoffs (decode e).graph (fastSpeed e D hG) (lexMinField.at e)
          (Φ.at e) := by
  have hMax := SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity
    ν hmt hFE.ne
  filter_upwards [AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses ν hmt hFE.ne hMax,
    hΦ.2.2.2.2.1] with e hlog hΦe
  intro hnt D hG _
  letI := hnt
  obtain ⟨r₀, C, hr₀, hC, ho, hD, hW⟩ := hlog (lexMinField.at e) (Classical.arbitrary _)
  obtain ⟨hwpos, hdom, hm, hmsum⟩ := summableFastRate_spec e D hG
  have hm' : ∀ v, 0 < fastSpeed e D hG v := hm
  have hmsum' : Summable (fastSpeed e D hG) := hmsum
  have hsub := hΦe.2.2.2.2.2 (lexMinField.at e) (isCellRepresentative_lexMinField e)
  have hpatch : ∀ Q : Rectangle,
      vectorEnergy (restrictGraph (decode e).graph (patchVertices (decode e) Q))
        (fun v => (Φ.at e) v.1) < ∞ := fun Q => (hΦe.2.2.1.1 Q).1
  have hmass : ∀ R : ℝ, r₀ ≤ R →
      Summable (fun v : {v : Vertex e.val |
          Hits (decode e) (Metric.closedBall (0 : Plane) R) v} =>
        Metric.diam ((decode e).cell v.1 : Set Plane) ^ 2 * (decode e).graph.pi v.1) :=
    fun R hR => summable_diamSq_mul_pi_of_localMassENN_ne_top (decode e) _
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hW R hR))
  exact fun i R => SpatialCutoff.exists_hilbertDomain_eqOn_closedBall (decode e)
    (decode_geometry e) (lexMinField.at e) (isCellRepresentative_lexMinField e) (Φ.at e)
    hsub hpatch hr₀ hD hmass (fastSpeed e D hG) hm' hmsum' i R

end ReflectedGMS.SpatialCutoffEnvironment
