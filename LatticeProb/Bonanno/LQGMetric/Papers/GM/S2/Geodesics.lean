/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.Geodesics at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import LatticeProb.Bonanno.LQGMetric.Blueprint.MQGeodesic
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

/-!
# GM S1.1, S1.2: existence and a.s. uniqueness of `D_h`-geodesics (task P2-M2C, WP-M2c)

GM (arXiv:1905.00383v3, `uniqueness-final.tex` l. 645–648), the two facts used "without comment":

* **GM.S1.1** (l. 647): a.s., every `z, w ∈ ℂ` are joined by at least one `D_h`-geodesic. GM: "This
  follows from [BBI, Corollary 2.5.20] and the fact that `(ℂ, D_h)` is a boundedly compact length
  space ([DFGPS, Lemma 3.8])". Here: bounded compactness is `Blueprint.DFGPSLem3_8` (stated for
  `h_1(0) = 0`, transferred to any whole-plane GFF by Weyl scaling with a constant, Axiom III);
  bounded compactness gives `ProperSpace` (`properSpace_of_bcpt`), and the shortest path is
  `MetricGeometry.exists_isGeodesicCurve_unitSpeed` (BBI Cor. 2.5.20, proved), reparametrized on
  `[0,1]` at constant speed (`exists_isGeod01_of_bcpt`).
* **GM.S1.2** (l. 648): for fixed `z, w` the `D_h`-geodesic is a.s. unique: `Blueprint.MQThm1_2Weak`
  (MQ Thm 1.2 for weak metrics, decision D33) for `z ≠ w`; for `z = w` the constant curve is the
  only geodesic (`uniqueGeod_self`). Consequences: simultaneously for all pairs of points of `ℚ²`
  (`gm_S1_2_rat`), and simultaneously for two weak metrics `D, D̃` (`gm_S1_2_rat_pair`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-! ## Deterministic part -/

/-- closed `D`-bounded sets compact ⇒ `(ℂ, D)` is proper -/
theorem properSpace_of_bcpt (D : ContMetric)
    (hc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A) :
    ProperSpace D.Space := by
  refine ⟨fun x r => ?_⟩
  have hA : IsCompact (D.pt ⁻¹' Metric.closedBall x r) := by
    refine hc _ (Metric.isClosed_closedBall.preimage D.continuous_pt) ⟨2 * r, fun u hu v hv => ?_⟩
    have hu' : D.1 (u, D.unpt x) ≤ r := hu
    have hv' : D.1 (v, D.unpt x) ≤ r := hv
    have htri := D.2.triangle u (D.unpt x) v
    rw [D.2.symm (D.unpt x) v] at htri
    linarith
  have himg := hA.image D.continuous_pt
  rwa [Set.image_preimage_eq _ (fun y => ⟨D.unpt y, rfl⟩)] at himg

/-- **GM.S1.1, deterministic form** (BBI Cor. 2.5.20): in a boundedly compact length metric on `ℂ`,
any two points are joined by a constant-speed geodesic `η : [0,1] → ℂ`. -/
theorem exists_isGeod01_of_bcpt (D : ContMetric) (hL : D.IsLength)
    (hc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (z w : ℂ) : ∃ η, IsGeod01 D z w η := by
  have := properSpace_of_bcpt D hc
  obtain ⟨P, hP0, hP1, -, -, hPd⟩ := exists_isGeodesicCurve_unitSpeed hL (D.pt z) (D.pt w)
  set L := dist (D.pt z) (D.pt w) with hLdef
  have hL0 : 0 ≤ L := dist_nonneg
  have hmem : ∀ t : unitInterval, L * (t : ℝ) ∈ Icc 0 L := fun t =>
    ⟨mul_nonneg hL0 t.2.1, mul_le_of_le_one_right hL0 t.2.2⟩
  have hdist : ∀ s t : unitInterval, dist (P (L * s)) (P (L * t)) = |(t : ℝ) - s| * L := by
    intro s t
    rw [hPd _ (hmem s) _ (hmem t), ← mul_sub, abs_mul, abs_of_nonneg hL0, mul_comm]
  have hcont : Continuous fun t : unitInterval => P (L * t) := by
    refine (LipschitzWith.of_dist_le' (K := L) fun s t => ?_).continuous
    rw [hdist, Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    exact (mul_comm _ _).le
  refine ⟨⟨fun t => D.unpt (P (L * t)), D.continuous_unpt.comp hcont⟩, ?_, ?_, ?_⟩
  · show D.unpt (P (L * ((0 : unitInterval) : ℝ))) = z
    rw [Set.Icc.coe_zero, mul_zero, hP0]; rfl
  · show D.unpt (P (L * ((1 : unitInterval) : ℝ))) = w
    rw [Set.Icc.coe_one, mul_one, hP1]; rfl
  · intro s t
    exact hdist s t

/-- the constant curve is the unique geodesic from `z` to `z` -/
lemma uniqueGeod_self (D : ContMetric) (z : ℂ) : UniqueGeod D z z := by
  refine ⟨ContinuousMap.const _ z, ⟨rfl, rfl, fun s t => ?_⟩, fun η hη => ?_⟩
  · simp [D.2.self_eq_zero]
  · ext t
    have h0 := hη.2.2 0 t
    rw [hη.1, D.2.self_eq_zero, mul_zero] at h0
    exact (D.2.eq_of_eq_zero _ _ h0).symm

/-! ## GM.S1.1 -/

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- Bounded compactness of `(ℂ, D_h)` for any whole-plane GFF (DFGPS Lemma 3.8, T:1727–1731,
there for `h_1(0) = 0`; any additive constant by Axiom III). -/
theorem gm_S1_1_bcpt (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ A : Set ℂ, IsClosed A →
      (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, (D (h ω)).1 (u, v) ≤ M) → IsCompact A := by
  have hN := measurable_circleAvg_left 1 0
  have hn : IsNormalizedWPGFF (fun ω => addConst (h ω) (-circleAvg (h ω) 1 0)) P := by
    refine ⟨hh.addConst (hN.comp hh.measurable).neg, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
    rw [hω]; ring
  filter_upwards [h38 γ hγ hγ2 D c hD P _ hn,
    hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh)] with ω h1 h2
  rintro A hA ⟨M, hM⟩
  refine h1.2 A hA ⟨Real.exp (xiGamma γ * -circleAvg (h ω) 1 0) * M, fun u hu v hv => ?_⟩
  show (D (addConst (h ω) (-circleAvg (h ω) 1 0))).1 (u, v) ≤ _
  rw [h2]
  exact mul_le_mul_of_nonneg_left (hM u hu v hv) (Real.exp_pos _).le

/-- **GM.S1.1** (l. 647): a.s. every `z, w` are joined by a `D_h`-geodesic. -/
theorem gm_S1_1 (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ z w : ℂ, ∃ η, IsGeod01 (D (h ω)) z w η := by
  filter_upwards [gm_S1_1_bcpt h38 hγ hγ2 hD P h hh,
    hD.length P h (Tight.isGFFPlusCont_of_wp hh)] with ω hc hL z w
  exact exists_isGeod01_of_bcpt _ hL hc z w

/-! ## GM.S1.2 -/

/-- **GM.S1.2** (l. 648): for fixed `z, w`, a.s. the `D_h`-geodesic from `z` to `w` is unique. -/
theorem gm_S1_2 (hMQ : MQThm1_2Weak) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) (z w : ℂ) :
    ∀ᵐ ω ∂P, UniqueGeod (D (h ω)) z w := by
  by_cases hzw : z = w
  · subst hzw
    exact Filter.Eventually.of_forall fun ω => uniqueGeod_self _ _
  · exact hMQ γ hγ hγ2 D c hD P h hh z w hzw

/-- **GM.S1.2**, all pairs of points of `ℚ²` simultaneously. -/
theorem gm_S1_2_rat (hMQ : MQThm1_2Weak) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ a b : ℚ × ℚ, UniqueGeod (D (h ω)) (ratPt a) (ratPt b) := by
  rw [ae_all_iff]
  intro a
  rw [ae_all_iff]
  intro b
  exact gm_S1_2 hMQ hγ hγ2 hD P h hh _ _

end LQGMetric.GM
