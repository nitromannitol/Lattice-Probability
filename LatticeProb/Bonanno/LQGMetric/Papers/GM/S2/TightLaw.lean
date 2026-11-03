/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightLaw at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightCore
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap

/-!
# GM S2.4: laws of the rescaled metrics, uniformly in the centre (task P2-TIGHT)

`scaledField ξ D c r z g = 𝔠_r⁻¹ e^{−ξ g_r(z)} D_g(r · + z, r · + z) ∈ C(ℂ × ℂ, ℝ)`: the
rescaled metric of GM l. 444 (Axiom V) centred at `z` (GM uses it "uniformly in z", via Axiom IV′;
decision D-A3, `decisions/DEC-A.md` (c), "Uniform in z").

* `map_scaledField_eq`: for a weak γ-LQG metric, the law of `scaledField r z (h)` is the same for
  every whole-plane GFF `h` (any probability space, any additive constant) and every centre `z`.
  Proof (D-A3): Axiom IV′ and the translation identity for circle averages give
  `scaledField r z h = scaledField r 0 (h(· + z))` a.s.; Weyl scaling for constants (GM.S1.6,
  `IsWeakLQGMetric.ae_dist_addConst`) and `(h + a)_r(0) = h_r(0) + a` give invariance under
  `h ↦ h − h_1(0)`; the normalized field has a unique law (`GFFLaw.map_eq_of_normalized_ae`).
* `tight_mapsTo`: the master statement behind S2.4a/b. For compact `A n` decreasing and open
  `U n` increasing in `ℝ` such that every continuous metric maps `⋂ A n` into `⋃ U n`, for each
  `ε > 0` some `n` has `P[scaledField r z h does not map A n into U n] < ε` for all `h, r, z`.
  Proof: Prokhorov (`isCompact_closure_of_isTightMeasureSet`) on the laws of Axiom V, the closure
  property of Axiom V, and `Tight.exists_measure_lt_of_isCompact_closure`.

Own argument (no source proves GM S2.4; D-A3, DEVIATIONS DA5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace GM
namespace Tight

/-- `(u, v) ↦ (r u + z, r v + z)` -/
def affArgs (r : ℝ) (z : ℂ) : C(ℂ × ℂ, ℂ × ℂ) :=
  ⟨fun p => ((r : ℂ) * p.1 + z, (r : ℂ) * p.2 + z), by fun_prop⟩

@[simp] lemma affArgs_apply (r : ℝ) (z : ℂ) (p : ℂ × ℂ) :
    affArgs r z p = ((r : ℂ) * p.1 + z, (r : ℂ) * p.2 + z) := rfl

/-- the rescaled metric `𝔠_r⁻¹ e^{−ξ g_r(z)} D_g(r · + z, r · + z)` (GM l. 444, centre `z`) -/
def scaledField (ξ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (r : ℝ) (z : ℂ) (g : DistC) :
    C(ℂ × ℂ, ℝ) :=
  ((c r)⁻¹ * Real.exp (-ξ * circleAvg g r z)) • (D g).1.comp (affArgs r z)

lemma scaledField_apply (ξ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (r : ℝ) (z : ℂ)
    (g : DistC) (p : ℂ × ℂ) :
    scaledField ξ D c r z g p = ((c r)⁻¹ * Real.exp (-ξ * circleAvg g r z)) *
      (D g).1 ((r : ℂ) * p.1 + z, (r : ℂ) * p.2 + z) := rfl

lemma scaledField_zero (ξ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (r : ℝ) (g : DistC) :
    scaledField ξ D c r 0 g =
      ((c r)⁻¹ * Real.exp (-ξ * circleAvg g r 0)) • (D g).1.comp (scaleArgs r) := by
  ext p; simp [scaledField, scaleArgs]

theorem measurable_scaledField {ξ : ℝ} {D : DistC → ContMetric} (hD : Measurable D)
    (c : ℝ → ℝ) (r : ℝ) (z : ℂ) : Measurable (scaledField ξ D c r z) := by
  have h1 : Measurable fun g : DistC => (D g).1.comp (affArgs r z) :=
    (ContinuousMap.continuous_precomp (affArgs r z)).measurable.comp
      (measurable_subtype_coe.comp hD)
  have h2 : Measurable fun g : DistC => (c r)⁻¹ * Real.exp (-ξ * circleAvg g r z) :=
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_circleAvg_left r z)))
  exact h2.smul h1

/-! ## Translation of circle averages -/

lemma testAffinePull_one_bumpTest (z : ℂ) (n : ℕ) (x : ℂ) :
    testAffinePull 1 z (bumpTest n x) = bumpTest n (x + z) := by
  ext y
  rw [testAffinePull_apply 1 z one_ne_zero, bumpTest_apply_eq, bumpTest_apply_eq n (x + z)]
  congr 1
  simp only [Complex.ofReal_one, div_one]; ring

/-- `(g(· + z))_r(0) = g_r(z)` (deterministic). -/
theorem circleAvg_affineComp_one (g : DistC) (r : ℝ) (z : ℂ) :
    circleAvg (affineComp 1 z g) r 0 = circleAvg g r z := by
  unfold circleAvg
  congr 1
  funext n
  have : (fun x => affineComp 1 z g (bumpTest n x)) = fun x => g (bumpTest n (x + z)) := by
    funext x
    rw [GFFInv.affineComp_apply, testAffinePull_one_bumpTest]
    simp
  rw [this]
  exact Real.circleAverage_map_add_const (f := fun x => g (bumpTest n x))

/-! ## Invariance of the law -/

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

lemma isGFFPlusCont_of_wp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) : IsGFFPlusCont h P := by
  refine ⟨hh.measurable, fun _ => 0, measurable_const, ?_⟩
  have h0 : ofCont 0 = 0 := by
    ext φ
    simp [ofCont]
  simpa [h0] using hh

/-- Centre `z` to centre `0`: a.s. `scaledField r z h = scaledField r 0 (h(· + z))`. -/
theorem ae_scaledField_translate (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (r : ℝ) (z : ℂ) :
    ∀ᵐ ω ∂P, scaledField (xiGamma γ) D c r z (h ω) =
      scaledField (xiGamma γ) D c r 0 (affineComp 1 z (h ω)) := by
  filter_upwards [hD.translation P h (isGFFPlusCont_of_wp hh) z] with ω hω
  ext p
  rw [scaledField_apply, scaledField_apply, circleAvg_affineComp_one, hω, add_zero, add_zero]

/-- Recentring by `h_1(0)`: a.s. `scaledField r 0 h = scaledField r 0 (h − h_1(0))`. -/
theorem ae_scaledField_normalize (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, scaledField (xiGamma γ) D c r 0 (h ω) =
      scaledField (xiGamma γ) D c r 0 (addConst (h ω) (-circleAvg (h ω) 1 0)) := by
  filter_upwards [hD.ae_dist_addConst (isGFFPlusCont_of_wp hh),
    CircleAvg.ae_circleAvg_addConst hh 0 hr] with ω hw hc
  ext p
  rw [scaledField_apply, scaledField_apply, hc, hw, ← mul_assoc]
  congr 1
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- the normalized field `h − h_1(0)` has a unique law -/
theorem map_normalize_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsWholePlaneGFF h P) (hh' : IsWholePlaneGFF h' P') :
    P.map (fun ω => addConst (h ω) (-circleAvg (h ω) 1 0)) =
      P'.map (fun ω => addConst (h' ω) (-circleAvg (h' ω) 1 0)) := by
  have hN := measurable_circleAvg_left 1 0
  have g1 := hh.addConst (hN.comp hh.measurable).neg
  have g2 := hh'.addConst (hN.comp hh'.measurable).neg
  refine GFFLaw.map_eq_of_normalized_ae (GFFLaw.integral_bumpTest 0 0) hN g1 g2
    (CircleAvg.ae_circleAvg_addConst_one_zero g1) (CircleAvg.ae_circleAvg_addConst_one_zero g2)
    ?_ ?_
  · filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
    rw [hω]; ring
  · filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh'] with ω hω
    rw [hω]; ring

/-- The law of the rescaled metric does not depend on the field, the probability space or the
centre. -/
theorem map_scaledField_eq (hD : IsWeakLQGMetric γ D c) {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsWholePlaneGFF h P) (hh' : IsWholePlaneGFF h' P') {r : ℝ} (hr : 0 < r) (z : ℂ) :
    P.map (fun ω => scaledField (xiGamma γ) D c r z (h ω)) =
      P'.map (fun ω => scaledField (xiGamma γ) D c r 0 (h' ω)) := by
  have hF := measurable_scaledField (ξ := xiGamma γ) hD.measurable c r 0
  have hz := hh.affineComp one_pos z
  have hN := measurable_circleAvg_left 1 0
  rw [Measure.map_congr (ae_scaledField_translate hD hh r z),
    Measure.map_congr (ae_scaledField_normalize hD hz hr),
    Measure.map_congr (ae_scaledField_normalize hD hh' hr)]
  have m1 : Measurable fun ω => addConst (affineComp 1 z (h ω))
      (-circleAvg (affineComp 1 z (h ω)) 1 0) :=
    (hz.addConst (hN.comp hz.measurable).neg).measurable
  have m2 : Measurable fun ω => addConst (h' ω) (-circleAvg (h' ω) 1 0) :=
    (hh'.addConst (hN.comp hh'.measurable).neg).measurable
  have e1 := Measure.map_map (μ := P) hF m1
  have e2 := Measure.map_map (μ := P') hF m2
  simp only [Function.comp_def] at e1 e2
  rw [← e1, ← e2, map_normalize_eq hz hh']

/-! ## The master statement -/

/-- **Master statement behind GM S2.4a/b** (D-A3): if every continuous metric maps `⋂ A n` into
`⋃ U n`, then uniformly over whole-plane GFFs `h`, scales `r > 0` and centres `z`, the rescaled
metric maps `A n` into `U n` except on an event of probability `< ε`, for some `n`. -/
theorem tight_mapsTo (hD : IsWeakLQGMetric γ D c) {A : ℕ → Set (ℂ × ℂ)}
    (hA : ∀ n, IsCompact (A n)) (hAa : Antitone A) {U : ℕ → Set ℝ} (hU : ∀ n, IsOpen (U n))
    (hUm : Monotone U)
    (hmet : ∀ d : C(ℂ × ℂ, ℝ), IsContinuousMetric d → ∀ x ∈ ⋂ n, A n, ∃ n, d x ∈ U n)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      P {ω | ¬ MapsTo (scaledField (xiGamma γ) D c r z (h ω)) (A n) (U n)} < ε := by
  by_cases hex : ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀)
      (_ : IsProbabilityMeasure P₀) (h₀ : Ω₀ → DistC), IsWholePlaneGFF h₀ P₀
  swap
  · exact ⟨0, fun P _ h hh => (hex ⟨_, _, P, inferInstance, h, hh⟩).elim⟩
  obtain ⟨Ω₀, _, P₀, _, h₀, hh₀⟩ := hex
  obtain ⟨hT, hcl⟩ := hD.tightness.2.2 P₀ h₀ hh₀
  have hXeq : ∀ r, (fun ω => scaledField (xiGamma γ) D c r 0 (h₀ ω)) = fun ω =>
      ((c r)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h₀ ω) r 0)) • (D (h₀ ω)).1.comp (scaleArgs r) :=
    fun r => funext fun ω => scaledField_zero _ _ _ _ _
  set S : Set (ProbabilityMeasure C(ℂ × ℂ, ℝ)) := {ν | ∃ r : ℝ, 0 < r ∧
    (ν : Measure C(ℂ × ℂ, ℝ)) = P₀.map (fun ω =>
      ((c r)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h₀ ω) r 0)) • (D (h₀ ω)).1.comp (scaleArgs r))}
  have hS : IsCompact (closure S) := by
    refine isCompact_closure_of_isTightMeasureSet (hT.subset ?_)
    rintro _ ⟨ν, ⟨r, hr, hν⟩, rfl⟩
    exact ⟨r, hr, hν⟩
  let C : ℕ → Set C(ℂ × ℂ, ℝ) := fun n => {d | ¬ MapsTo d (A n) (U n)}
  have hCc : ∀ n, IsClosed (C n) := fun n => isClosed_setOf_not_mapsTo (hA n) (hU n)
  have hCa : Antitone C := fun m n hmn d hd hd' =>
    hd (fun x hx => hUm hmn (hd' (hAa hmn hx)))
  have h0 : ∀ μ ∈ closure S, (μ : Measure C(ℂ × ℂ, ℝ)) (⋂ n, C n) = 0 := by
    intro μ hμ
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hcl μ hμ] with d hd hmem
    obtain ⟨x, hx, hxU⟩ :=
      exists_mem_iInter_of_not_mapsTo hA hAa hU hUm (d := d) (mem_iInter.1 hmem)
    obtain ⟨n, hn⟩ := hmet d hd x hx
    exact hxU n hn
  obtain ⟨n, hn⟩ := exists_measure_lt_of_isCompact_closure hS hCc hCa h0 hε
  refine ⟨n, fun P _ h hh r hr z => ?_⟩
  have hFm : Measurable fun ω => scaledField (xiGamma γ) D c r z (h ω) :=
    (measurable_scaledField (ξ := xiGamma γ) hD.measurable c r z).comp hh.measurable
  have e : P {ω | ¬ MapsTo (scaledField (xiGamma γ) D c r z (h ω)) (A n) (U n)} =
      (P.map fun ω => scaledField (xiGamma γ) D c r z (h ω)) (C n) := by
    rw [Measure.map_apply hFm (hCc n).measurableSet]; rfl
  rw [e, map_scaledField_eq hD hh hh₀ hr z]
  have hprob : IsProbabilityMeasure (P₀.map fun ω => scaledField (xiGamma γ) D c r 0 (h₀ ω)) :=
    inferInstance
  exact hn ⟨_, hprob⟩ ⟨r, hr, hXeq r ▸ rfl⟩

end Tight
end GM
end LQGMetric
