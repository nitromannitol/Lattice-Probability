/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.SimilarityClosedGate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.AreaClockAdmissibleDischarge
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GoodEnvironmentSet
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedFiniteEnergyDensityMeasurable
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualSpatialDensityBridge

/-!
# A measurable, similarity-closed, conull admissibility gate

The regeneration kernel (`RegenerationKernel.rootedKernel`, `regenerationKernel`) is gated by a
measurable set `G` of environments at which the area clock is a reflected walk.  The gate
produced so far (`RegenerationKernel.exists_measurable_gate`,
`DirectionalBracketLLNGatesCoding.exists_rootedKernel_gate`) is the complement of a measurable
hull of a null set: it is measurable and conull, but it is **not closed under similarities**,
and then `ActualConditionalPathIntegral.DilationCoding.law_φ` is false at a pair `e ∈ G`,
`e' ∉ G` (cemetery Dirac against a real law).

This file builds ONE canonical gate, `similarityClosedGate : Set Env`, independent of any law:

* `measurableSet_similarityClosedGate`: it is measurable;
* `ae_mem_similarityClosedGate`, `measure_compl_similarityClosedGate`: it is conull for every
  probability law `ν` with `MassTransport ν` and `FiniteEnergyMoment ν`;
* `environmentAreaClockGeometry_of_mem`, `environmentAreaClockAdmissible_of_mem`: every member
  satisfies `AreaClockFastSpeedOccupation.EnvironmentAreaClockGeometry`, hence
  `EnvironmentAreaClockAdmissible`;
* `mem_similarityClosedGate_iff_of_isSimilarity`: for EVERY physical similarity
  `IsSimilarity s u hs e e'` (any ratio `s > 0`, any real centre `u`, any relabelling),
  `e ∈ G ↔ e' ∈ G`.  In particular `translateEnv w ⁻¹' G = G` and
  `similarityTargetEnv s u hs ⁻¹' G = G` (the two environment maps of the regeneration flow
  `reRootFlow` and of the scaling `reScale`).

## The gate

`G = {e | GoodEnvironment e ∧ EventualBallBound e}` where

* `GoodEnvironmentSet.GoodEnvironment e`: `D_R < ∞` at every radius and sublinear large-cell
  decay (already measurable and similarity-stable);
* `EventualBallBound e`: an EVENTUAL quadratic bound on the Lebesgue ball mass of the rooted
  (FE) density, `∫_{B̄(0,r)} ρ_FE ≤ r² M` for all `r ≥ r₁` (some finite `M`, some `r₁`).

The reason for "eventual": the checked a.e. ball bound
(`SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity`) holds at EVERY
radius `r > 0`, and at small radii it is NOT translation invariant (it constrains `ρ_FE` near the
origin only).  The only consumer, the local-mass bound of `r:prop:log`
(`AlmostSureCutoffBounds.localMassENN_hittingBall_le_of_ballBound`), reads it at radii
`R + R/100` with `R ≥ r₀` only, so the eventual form suffices
(`localMassENN_hittingBall_le_of_eventualBallBound`), and it is similarity covariant:
`ρ_FE` is a scale-invariant rooted observable
(`ActualSpatialDensityBridge.rootedFiniteEnergyDensity_similarity`), Lebesgue measure scales by
`s²` (`volume_eq_smul_map`), and a ball `B̄(0,r)` pulls back into `B̄(0, ‖u‖ + r/s)`
(`ballMass_le_of_isSimilarity`).  Measurability: `(e, x) ↦ ρ_FE(decode e, x)` is jointly
measurable (`RootedFiniteEnergyDensityMeasurable.measurable_rootedFiniteEnergyDensity`), so each
ball mass is a measurable function of `e`; the real quantifiers reduce to natural ones by
monotonicity (`eventualBallBound_iff_nat`).

Nothing here is probabilistic beyond the two checked a.e. inputs; nothing certifies
`p:lem:regeninvariant` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.SimilarityClosedGate

open Code EnvironmentLaws HarmonicLawIngredients
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.AreaClockFastSpeedOccupation
open ReflectedGMS.GoodEnvironmentSet ReflectedGMS.NonmacroscopicSelectedBlocks

/-! ### 1. Lebesgue measure under a positive similarity -/

theorem continuous_positiveSimilarity (s : ℝ) (u : Plane) :
    Continuous (positiveSimilarity s u) := by
  unfold positiveSimilarity
  fun_prop

theorem measurable_positiveSimilarity (s : ℝ) (u : Plane) :
    Measurable (positiveSimilarity s u) :=
  (continuous_positiveSimilarity s u).measurable

theorem surjective_positiveSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) :
    Function.Surjective (positiveSimilarity s u) := fun y =>
  ⟨positiveSimilarity s⁻¹ (-s • u) y, positiveSimilarity_inverse_right s u y hs⟩

/-- **Lebesgue measure is `s²` times its image under `z ↦ s (z - u)`.** -/
theorem volume_eq_smul_map (s : ℝ) (u : Plane) (hs : 0 < s) :
    (volume : Measure Plane)
      = ENNReal.ofReal (s ^ 2) • (volume : Measure Plane).map (positiveSimilarity s u) := by
  ext A hA
  rw [Measure.smul_apply, Measure.map_apply (measurable_positiveSimilarity s u) hA, smul_eq_mul]
  calc volume A
      = volume (positiveSimilarity s u '' (positiveSimilarity s u ⁻¹' A)) := by
        rw [Set.image_preimage_eq A (surjective_positiveSimilarity s u hs)]
    _ = ENNReal.ofReal (s ^ 2) * volume (positiveSimilarity s u ⁻¹' A) :=
        Spatial.volume_image_positiveSimilarity s u _

/-- **Change of variables for a positive similarity.** -/
theorem setLIntegral_eq_smul_preimage (s : ℝ) (u : Plane) (hs : 0 < s) {f : Plane → ℝ≥0∞}
    (hf : Measurable f) {A : Set Plane} (hA : MeasurableSet A) :
    ∫⁻ y in A, f y ∂volume
      = ENNReal.ofReal (s ^ 2) *
          ∫⁻ x in positiveSimilarity s u ⁻¹' A, f (positiveSimilarity s u x) ∂volume := by
  conv_lhs => rw [volume_eq_smul_map s u hs]
  rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    setLIntegral_map hA hf (measurable_positiveSimilarity s u)]

/-! ### 2. The ball mass of the rooted (FE) density -/

/-- The Lebesgue mass of the rooted (FE) density on the closed ball `B̄(0, r)`. -/
noncomputable def ballMass (e : Env) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Metric.closedBall (0 : Plane) r,
    RootDensities.rootedFiniteEnergyDensity (decode e) x ∂volume

theorem ballMass_mono (e : Env) {r r' : ℝ} (h : r ≤ r') : ballMass e r ≤ ballMass e r' :=
  lintegral_mono_set (Metric.closedBall_subset_closedBall h)

theorem measurable_ballMass (r : ℝ) : Measurable fun e : Env => ballMass e r :=
  RootedFiniteEnergyDensityMeasurable.measurable_rootedFiniteEnergyDensity.lintegral_prod_right'
    (ν := (volume : Measure Plane).restrict (Metric.closedBall (0 : Plane) r))

/-- Bridged through `Function.comp_def` with an explicitly typed `have`: a bare `.comp` unifies
against the deep `Code.decode` and the enlarged boundary mask, and exhausts the `isDefEq` budget. -/
theorem measurable_rootedFiniteEnergyDensity_env (e : Env) :
    Measurable fun x : Plane => RootDensities.rootedFiniteEnergyDensity (decode e) x := by
  have h : Measurable ((fun q : Env × Plane =>
      RootDensities.rootedFiniteEnergyDensity (decode q.1) q.2) ∘
      fun x : Plane => ((e, x) : Env × Plane)) :=
    RootedFiniteEnergyDensityMeasurable.measurable_rootedFiniteEnergyDensity.comp
      (measurable_const.prodMk measurable_id)
  simpa only [Function.comp_def] using h

/-- **Similarity covariance of the ball mass.**  `ρ_FE` is scale invariant, area scales by `s²`,
and `B̄(0, r)` pulls back into `B̄(0, ‖u‖ + r / s)`. -/
theorem ballMass_le_of_isSimilarity {s : ℝ} {u : Plane} (hs : 0 < s) {e e' : Env}
    (hsim : IsSimilarity s u hs e e') (r : ℝ) :
    ballMass e' r ≤ ENNReal.ofReal (s ^ 2) * ballMass e (‖u‖ + r / s) := by
  unfold ballMass
  rw [setLIntegral_eq_smul_preimage s u hs (measurable_rootedFiniteEnergyDensity_env e')
    Metric.isClosed_closedBall.measurableSet]
  refine mul_le_mul' le_rfl ?_
  have hpt : ∀ x : Plane,
      RootDensities.rootedFiniteEnergyDensity (decode e') (positiveSimilarity s u x)
        = RootDensities.rootedFiniteEnergyDensity (decode e) x :=
    fun x => ActualSpatialDensityBridge.rootedFiniteEnergyDensity_similarity hs hsim x
  simp_rw [hpt]
  refine lintegral_mono_set ?_
  intro x hx
  exact mem_closedBall_zero_iff.mpr (norm_le_of_positiveSimilarity_mem_closedBall hs u x hx)

/-! ### 3. The eventual quadratic ball bound -/

/-- **Eventual quadratic ball bound** for the rooted (FE) density: some finite `M` and some
radius `r₁` with `∫_{B̄(0,r)} ρ_FE ≤ r² M` for every `r ≥ r₁`. -/
def EventualBallBound (e : Env) : Prop :=
  ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∃ r₁ : ℝ, ∀ r : ℝ, r₁ ≤ r → ballMass e r ≤ ENNReal.ofReal (r ^ 2) * M

/-- The real quantifiers of `EventualBallBound` reduce to natural ones. -/
theorem eventualBallBound_iff_nat (e : Env) :
    EventualBallBound e ↔ ∃ m N : ℕ, ∀ n : {n : ℕ // N ≤ n},
      ballMass e (n.1 : ℝ) ≤ ENNReal.ofReal ((n.1 : ℝ) ^ 2) * (m : ℝ≥0∞) := by
  constructor
  · rintro ⟨M, hM, r₁, hr⟩
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hM
    refine ⟨m, ⌈r₁⌉₊, fun n => ?_⟩
    have hn : r₁ ≤ (n.1 : ℝ) :=
      le_trans (Nat.le_ceil r₁) (by exact_mod_cast n.2)
    exact le_trans (hr _ hn) (mul_le_mul' le_rfl hm.le)
  · rintro ⟨m, N, h⟩
    refine ⟨ENNReal.ofReal 4 * (m : ℝ≥0∞),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top m),
      max (N : ℝ) 1, fun r hr => ?_⟩
    have hN : (N : ℝ) ≤ r := le_trans (le_max_left _ _) hr
    have h1 : (1 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
    have hr0 : 0 ≤ r := by linarith
    have hNc : N ≤ ⌈r⌉₊ := by
      have : (N : ℝ) ≤ (⌈r⌉₊ : ℝ) := le_trans hN (Nat.le_ceil r)
      exact_mod_cast this
    have hc1 : (⌈r⌉₊ : ℝ) < r + 1 := Nat.ceil_lt_add_one hr0
    have h0 : (0 : ℝ) ≤ (⌈r⌉₊ : ℝ) := Nat.cast_nonneg _
    have hle : (⌈r⌉₊ : ℝ) ≤ 2 * r := by linarith
    have hsq : (⌈r⌉₊ : ℝ) ^ 2 ≤ 4 * r ^ 2 := by
      nlinarith [mul_self_le_mul_self h0 hle]
    calc ballMass e r ≤ ballMass e (⌈r⌉₊ : ℝ) := ballMass_mono e (Nat.le_ceil r)
      _ ≤ ENNReal.ofReal ((⌈r⌉₊ : ℝ) ^ 2) * (m : ℝ≥0∞) := h ⟨⌈r⌉₊, hNc⟩
      _ ≤ ENNReal.ofReal (4 * r ^ 2) * (m : ℝ≥0∞) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hsq) le_rfl
      _ = ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal 4 * (m : ℝ≥0∞)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
          ring

theorem setOf_eventualBallBound_eq :
    {e : Env | EventualBallBound e}
      = ⋃ m : ℕ, ⋃ N : ℕ, ⋂ n : {n : ℕ // N ≤ n},
          {e : Env | ballMass e (n.1 : ℝ) ≤ ENNReal.ofReal ((n.1 : ℝ) ^ 2) * (m : ℝ≥0∞)} := by
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
  exact eventualBallBound_iff_nat e

theorem measurableSet_eventualBallBound : MeasurableSet {e : Env | EventualBallBound e} := by
  rw [setOf_eventualBallBound_eq]
  exact MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    measurableSet_le (measurable_ballMass _) measurable_const

/-- **The eventual ball bound is similarity invariant** (constant `4 M`, radius
`max (s r₁) (s ‖u‖)`). -/
theorem eventualBallBound_of_isSimilarity {s : ℝ} {u : Plane} (hs : 0 < s) {e e' : Env}
    (hsim : IsSimilarity s u hs e e') (he : EventualBallBound e) : EventualBallBound e' := by
  obtain ⟨M, hM, r₁, hr⟩ := he
  refine ⟨ENNReal.ofReal 4 * M, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM,
    max (s * r₁) (s * ‖u‖), fun r hr' => ?_⟩
  have h1 : s * r₁ ≤ r := le_trans (le_max_left _ _) hr'
  have h2 : s * ‖u‖ ≤ r := le_trans (le_max_right _ _) hr'
  have hu0 : 0 ≤ s * ‖u‖ := mul_nonneg hs.le (norm_nonneg u)
  have hr1 : r₁ ≤ ‖u‖ + r / s := by
    have : r₁ ≤ r / s := (le_div_iff₀' hs).2 h1
    linarith [norm_nonneg u]
  have hRs : s * (r / s) = r := by field_simp
  have hkey : s * (‖u‖ + r / s) = s * ‖u‖ + r := by rw [mul_add, hRs]
  have hq : s ^ 2 * (‖u‖ + r / s) ^ 2 ≤ 4 * r ^ 2 := by
    have hsq : s ^ 2 * (‖u‖ + r / s) ^ 2 = (s * ‖u‖ + r) ^ 2 := by rw [← hkey]; ring
    rw [hsq]
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ s * ‖u‖ + 3 * r)]
  calc ballMass e' r ≤ ENNReal.ofReal (s ^ 2) * ballMass e (‖u‖ + r / s) :=
        ballMass_le_of_isSimilarity hs hsim r
    _ ≤ ENNReal.ofReal (s ^ 2) * (ENNReal.ofReal ((‖u‖ + r / s) ^ 2) * M) :=
        mul_le_mul' le_rfl (hr _ hr1)
    _ = ENNReal.ofReal (s ^ 2 * (‖u‖ + r / s) ^ 2) * M := by
        rw [ENNReal.ofReal_mul (sq_nonneg s), mul_assoc]
    _ ≤ ENNReal.ofReal (4 * r ^ 2) * M := mul_le_mul' (ENNReal.ofReal_le_ofReal hq) le_rfl
    _ = ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal 4 * M) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        ring

/-! ### 4. The eventual bound suffices for `r:prop:log` -/

/-- **`hW` of `r:prop:log` from the EVENTUAL ball bound.**  The proof of
`AlmostSureCutoffBounds.localMassENN_hittingBall_le_of_ballBound` reads the ball bound only at
radius `R + R/100` with `R ≥ r₀`; so a bound from radius `r₁ ≤ r₀` on suffices. -/
theorem localMassENN_hittingBall_le_of_eventualBallBound {V : Type*} [Countable V]
    (F : IndexedCells V) (hF : Geometry F) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr₁ : r₁ ≤ r₀)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    {M : ℝ≥0∞} (hMtop : M ≠ ∞)
    (hM : ∀ r : ℝ, r₁ ≤ r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity F x ∂volume) ≤ ENNReal.ofReal (r ^ 2) * M) :
    ∀ R : ℝ, r₀ ≤ R →
      LogCutoff.localMassENN F {v : V | Hits F (Metric.closedBall (0 : Plane) R) v}
        ≤ ENNReal.ofReal (2 * M.toReal * R ^ 2) := by
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le hr₀ hR
  have hcell : ∀ v ∈ {v : V | Hits F (Metric.closedBall (0 : Plane) R) v},
      (F.cell v : Set Plane) ⊆ Metric.closedBall (0 : Plane) (R + R / 100) :=
    fun v hv =>
      AlmostSureCutoffBounds.cell_subset_closedBall_of_hits_of_diam_le F hv (hD R hR v hv)
  have h1 :=
    AlmostSureCutoffBounds.localMassENN_le_setLIntegral_rootedFiniteEnergyDensity F hF hcell
  have h2 := hM (R + R / 100) (by linarith)
  have hm : (0 : ℝ) ≤ M.toReal := ENNReal.toReal_nonneg
  have hq : (R + R / 100) ^ 2 ≤ 2 * R ^ 2 := by nlinarith
  have hstep : ENNReal.ofReal ((R + R / 100) ^ 2) * ENNReal.ofReal M.toReal
      ≤ ENNReal.ofReal (2 * M.toReal * R ^ 2) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (R + R / 100) ^ 2 * M.toReal ≤ (2 * R ^ 2) * M.toReal :=
          mul_le_mul_of_nonneg_right hq hm
      _ = 2 * M.toReal * R ^ 2 := by ring
  have h3 : ENNReal.ofReal ((R + R / 100) ^ 2) * M
      ≤ ENNReal.ofReal (2 * M.toReal * R ^ 2) := by
    refine le_trans (le_of_eq ?_) hstep
    rw [ENNReal.ofReal_toReal hMtop]
  exact le_trans h1 (le_trans h2 h3)

/-! ### 5. The gate -/

/-- The gate predicate: good large-cell geometry and the eventual (FE) ball bound. -/
def SimilarityGate (e : Env) : Prop :=
  GoodEnvironment e ∧ EventualBallBound e

/-- **The similarity-closed admissibility gate.** -/
def similarityClosedGate : Set Env := {e | SimilarityGate e}

theorem similarityClosedGate_eq :
    similarityClosedGate = {e : Env | GoodEnvironment e} ∩ {e : Env | EventualBallBound e} :=
  rfl

theorem measurableSet_similarityClosedGate : MeasurableSet similarityClosedGate := by
  rw [similarityClosedGate_eq]
  exact measurableSet_goodEnvironment.inter measurableSet_eventualBallBound

/-- **Every member of the gate satisfies the geometric admissibility clause.** -/
theorem environmentAreaClockGeometry_of_mem {e : Env} (he : e ∈ similarityClosedGate) :
    EnvironmentAreaClockGeometry e := by
  obtain ⟨⟨hfin, hsub⟩, M, hM, r₁, hr⟩ := he
  refine AreaClockAdmissibleDischarge.environmentAreaClockGeometry_of_logCutoff e hfin
    (fun z o => ?_)
  obtain ⟨R₀, hR₀pos, hR₀⟩ :=
    AlmostSureCutoffBounds.exists_diameter_bound_of_maxDiamHittingBall_sublinear (decode e) hsub
  have hr₀ : 0 < max (max R₀ ‖z o‖) r₁ :=
    lt_of_lt_of_le hR₀pos (le_trans (le_max_left _ _) (le_max_left _ _))
  have hD : ∀ R : ℝ, max (max R₀ ‖z o‖) r₁ ≤ R → ∀ v : Vertex e.val,
      Hits (decode e) (Metric.closedBall (0 : Plane) R) v →
      Metric.diam ((decode e).cell v : Set Plane) ≤ R / 100 :=
    fun R hR v hv => hR₀ R (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR) v hv
  exact ⟨max (max R₀ ‖z o‖) r₁, 2 * M.toReal, hr₀, by positivity,
    le_trans (le_max_right _ _) (le_max_left _ _), hD,
    localMassENN_hittingBall_le_of_eventualBallBound (decode e) (decode_geometry e) hr₀
      (le_max_right _ _) hD hM hr⟩

/-- **Every member of the gate is admissible** (the kernel's `hwalk`). -/
theorem environmentAreaClockAdmissible_of_mem {e : Env} (he : e ∈ similarityClosedGate) :
    EnvironmentAreaClockAdmissible e :=
  environmentAreaClockAdmissible_of_geometry e (environmentAreaClockGeometry_of_mem he)

/-- **The gate is conull** for every probability law with mass transport and a finite (FE)
moment. -/
theorem ae_mem_similarityClosedGate (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    ∀ᵐ e ∂ν, e ∈ similarityClosedGate := by
  filter_upwards [ae_goodEnvironment ν hmt hFE.ne,
    SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity (ν := ν) hmt
      hFE.ne] with e hg hb
  obtain ⟨M, hM, hball⟩ := hb
  exact ⟨hg, M, hM, 1, fun r hr => hball r (lt_of_lt_of_le one_pos hr)⟩

theorem measure_compl_similarityClosedGate (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    ν similarityClosedGateᶜ = 0 :=
  ae_iff.1 (ae_mem_similarityClosedGate ν hmt hFE)

/-! ### 6. Similarity closure -/

/-- The inverse of a physical similarity is a physical similarity. -/
theorem isSimilarity_symm {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    (h : IsSimilarity s u hs e e') : IsSimilarity s⁻¹ (-s • u) (inv_pos.2 hs) e' e := by
  obtain ⟨relabel, h⟩ := h
  refine ⟨relabel.symm, fun v' => ?_, fun v' w' => ?_⟩
  · apply SetLike.coe_injective
    have hcell := h.1 (relabel.symm v')
    rw [Equiv.apply_symm_apply] at hcell
    rw [coe_transformCell, hcell, coe_transformCell, Set.image_image]
    have hid : (fun z : Plane => positiveSimilarity s⁻¹ (-s • u) (positiveSimilarity s u z))
        = id :=
      funext fun z => positiveSimilarity_inverse_left s u z hs
    rw [hid, Set.image_id]
  · have := h.2 (relabel.symm v') (relabel.symm w')
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm

/-- **The gate is closed under every physical similarity** (one direction). -/
theorem mem_similarityClosedGate_of_isSimilarity {s : ℝ} {u : Plane} (hs : 0 < s) {e e' : Env}
    (hsim : IsSimilarity s u hs e e') (he : e ∈ similarityClosedGate) :
    e' ∈ similarityClosedGate :=
  ⟨goodEnvironment_of_isSimilarity hs hsim he.1, eventualBallBound_of_isSimilarity hs hsim he.2⟩

/-- **The gate is invariant under every physical similarity**: for any ratio `s > 0`, any real
centre `u` and any relabelling witnessing `IsSimilarity s u hs e e'`, `e ∈ G ↔ e' ∈ G`. -/
theorem mem_similarityClosedGate_iff_of_isSimilarity {s : ℝ} {u : Plane} {hs : 0 < s}
    {e e' : Env} (hsim : IsSimilarity s u hs e e') :
    e ∈ similarityClosedGate ↔ e' ∈ similarityClosedGate :=
  ⟨mem_similarityClosedGate_of_isSimilarity hs hsim,
    mem_similarityClosedGate_of_isSimilarity (inv_pos.2 hs) (isSimilarity_symm hsim)⟩

/-- Closure under the canonical similarity action `similarityTargetEnv` (the environment map of
the scaling `reScale C = similarityTargetEnv C 0`, and of any similarity with real centre). -/
theorem similarityTargetEnv_mem_similarityClosedGate_iff (s : ℝ) (u : Plane) (hs : 0 < s)
    (e : Env) :
    similarityTargetEnv s u hs e ∈ similarityClosedGate ↔ e ∈ similarityClosedGate :=
  (mem_similarityClosedGate_iff_of_isSimilarity (isSimilarity_similarityTargetEnv s u hs e)).symm

/-- Closure under translation by ANY real vector with canonical relabelling (the environment map
of the re-rooting flow `reRootFlow`). -/
theorem translateEnv_mem_similarityClosedGate_iff (w : Plane) (e : Env) :
    ActualMarkedBlockTransport.translateEnv w e ∈ similarityClosedGate
      ↔ e ∈ similarityClosedGate :=
  (mem_similarityClosedGate_iff_of_isSimilarity
    (ActualMarkedBlockTransport.isSimilarity_translateEnv w e)).symm

/-! ### 7. The packaged gate -/

end ReflectedGMS.SimilarityClosedGate
