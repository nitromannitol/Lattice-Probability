/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108M7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M6
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M1

/-!
# CONF Lemma 3.3, Step 3: S-cont-law for condition 2 of `E^U` (`CONFEUSContLaw`)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, C:667–669 ("such functionals are a.s.
continuous at `D_h` since the probability that the supremum … is exactly equal to `c` is zero.
This can be seen using Axiom III and the fact that adding a smooth compactly supported function to
`h` affects its law in an absolutely continuous way") and C:1240–1241 ("A similar justification
holds for `F_r(z)`").

The square diameters of condition 2 of `E^U` are computed in `𝔸_{2r,5r}(z)`, which is not inside
`U`, so the zero-boundary Cameron–Martin shift of S3D108K5 does not apply. Following CONF's
sentence for the whole field: the event `{diam(S; D_g(·,·;𝔸_{2r,5r})) = (c/100) 𝔠_r e^{ξ g_r(z)}}`
is invariant under adding constants to `g` (Axiom III with constants), so it can be computed for
the field `g = h − h_r(z)` normalized on `∂B_r(z)`; there the threshold is the constant
`(c/100) 𝔠_r`, and a whole-plane Cameron–Martin shift `g ↦ g + tφ` by a test function `φ = 1` on
`𝔸_{2r,5r}`, `φ = 0` on `∂B_r(z)` multiplies the diameter by `e^{ξt}` (S3D108K4,
`measure_level_eq_zero`). The frozen form follows by Fubini on the product law (independence).

* `ae_circleAvg_addFun_rz`: `(g + f)_r(z) = g_r(z) + (circle average of f)` a.s. (as
  `GM.ae_circleAvg_addFun`, at a general circle);
* `ac_shift_normalized`: the law of a normalized whole-plane GFF is absolutely continuous w.r.t.
  its shift by `tφ`, `φ = 0` on the normalizing circle (as `GM.measure_addFun_preimage_eq_zero`);
* `ae_internalDiam_ne_of_normalized`: unconditional S-cont-law at a constant level;
* **`confEUSContLaw_of`**: `CONFEUSContLaw γ D c p` for `p.c > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- `(h + f)_r(z) = h_r(z) + (circle average of f)` for all constants, a.s. -/
lemma ae_circleAvg_addFun_rz {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (f : C(ℂ, ℝ)) (z : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ c, circleAvg (addConst (addFun (h ω) f) c) r z =
      circleAvg (h ω) r z + c + Real.circleAverage f z r := by
  filter_upwards [CircleAvg.ae_tendsto_mollAvg hh z hr] with ω ⟨a, ha⟩ c
  have ha' : Tendsto (fun n => CircleAvg.mollAvg
      (addConst (addFun (h ω) f) c - ofCont f) n z r) atTop (𝓝 (a + c)) := by
    have e : addConst (addFun (h ω) f) c - ofCont f = addConst (h ω) c := by
      simp only [addConst, addFun]; abel
    rw [e]
    simp_rw [CircleAvg.mollAvg_addConst]
    exact ha.add_const c
  rw [(CircleAvg.circleAvg_eq_sub_ofCont_add ha').2, CircleAvg.circleAvg_eq_of_tendsto ha',
    CircleAvg.circleAvg_eq_of_tendsto ha]

/-- **Cameron–Martin, null-set form, for a whole-plane GFF normalized on `∂B_r(z)`**, for shifts
vanishing on `∂B_r(z)` (the argument of `GM.measure_addFun_preimage_eq_zero`) -/
lemma ac_shift_normalized [IsProbabilityMeasure P] {g : Ω → DistC} (hg : IsWholePlaneGFF g P)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (hn : ∀ᵐ ω ∂P, circleAvg (g ω) r z = 0) (φ : TestC)
    (hφ : ∀ x ∈ sphere z |r|, φ x = 0) (t : ℝ) :
    P.map g ≪ (P.map g).map fun x => addFun x (t • testCont φ) := by
  obtain ⟨F, hF, hfix⟩ := GM.exists_sigma0_fix (measurable_circleAvg_left r z)
  have htc : t • testCont φ = testCont (t • φ) := by ext; rfl
  have hca0 : Real.circleAverage (testCont (t • φ)) z r = 0 := by
    rw [Real.circleAverage_congr_sphere (f₂ := fun _ => (0 : ℝ)) fun x hx => by
      show t * φ x = 0
      rw [hφ x hx, mul_zero]]
    simp [Real.circleAverage]
  refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
  have hSm : Measurable fun x : DistC => addFun x (t • testCont φ) := measurable_addFun_left _
  rw [Measure.map_apply hSm hA, Measure.map_apply hg.measurable (hSm hA)] at h0
  rw [Measure.map_apply hg.measurable hA]
  have h0' : P ((fun ω => addFun (g ω) (testCont (t • φ))) ⁻¹' A) = 0 := by
    rw [← htc]; exact h0
  have hfY : ∀ᵐ ω ∂P, F (g ω) = g ω := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hg z hr, hn] with ω h1 h2
    exact hfix _ h1 h2
  have hfX : ∀ᵐ ω ∂P, F (addFun (g ω) (testCont (t • φ))) = addFun (g ω) (testCont (t • φ)) := by
    filter_upwards [ae_circleAvg_addFun_rz hg (testCont (t • φ)) z hr, hn] with ω h1 h2
    have h0'' := h1 0
    rw [GM.addConst_zero_eq, h2, hca0] at h0''
    refine hfix _ (fun c => ?_) (by rw [h0'']; ring)
    rw [h1 c, h2, hca0, h0'']; ring
  exact GM.measure_preimage_eq_zero_of_sigma0 hF (measurable_pair0_addFun hg (t • φ))
    (measurable_pair0_comp hg) (lawPair0_ac_addFun hg (t • φ)) hfX hfY hA h0'

/-- **S-cont-law at a constant level for a normalized whole-plane GFF** (CONF C:667–669) -/
theorem ae_internalDiam_ne_of_normalized [IsProbabilityMeasure P] {γ : ℝ} (hγ : 0 < γ)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {g : Ω → DistC}
    (hg : IsWholePlaneGFF g P) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hn : ∀ᵐ ω ∂P, circleAvg (g ω) r z = 0) {A V : Set ℂ} (hA : A.Countable) (hV : IsOpen V)
    (φ : TestC) (hφ1 : ∀ x ∈ V, φ x = 1) (hφ0 : ∀ x ∈ sphere z |r|, φ x = 0) {T₀ : ℝ≥0∞}
    (hT0 : T₀ ≠ 0) (hTt : T₀ ≠ ⊤) :
    ∀ᵐ ω ∂P, internalDiam (D (g ω)) A V ≠ T₀ := by
  have hξ : xiGamma γ ≠ 0 := (GM.xiGamma_pos hγ).ne'
  have hν : IsWholePlaneGFF id (P.map g) := GM.isWholePlaneGFF_id_map hg
  have hweν : ∀ᵐ x ∂(P.map g), WeylAt (xiGamma γ) D x :=
    hD.weyl (P.map g) id (GM.isGFFPlusCont_of_isWholePlaneGFF hν)
  obtain ⟨F, hFm, hF⟩ := measurable_internal hV
  set Y' : DistC → ℝ≥0∞ := fun x => ⨆ u ∈ A, ⨆ v ∈ A, F (D x, u, v) with hY'
  have hY'm : Measurable Y' := Measurable.biSup _ hA fun u _ => Measurable.biSup _ hA fun v _ =>
    hFm.comp (hD.measurable.prodMk measurable_const)
  have hYY : ∀ x, (D x).IsLength → internalDiam (D x) A V = Y' x := fun x hx => by
    simp only [internalDiam, hY', hF _ hx]
  have hscale : ∀ᵐ x ∂(P.map g), ∀ t : ℝ,
      Y' (addFun x (t • testCont φ)) = ENNReal.ofReal (Real.exp (xiGamma γ * t)) * Y' x := by
    filter_upwards [hweν] with x hx t
    rw [← hYY _ (isLength_of_weylAt hx _), ← hYY _ (isLength_of_weylAt0 hx)]
    exact internalDiam_addFun_const hx hV (φ := testCont φ) hφ1 A t
  have : IsProbabilityMeasure (P.map g) :=
    (Measure.isProbabilityMeasure_map_iff hg.measurable.aemeasurable).2 ‹_›
  have h0 := measure_level_eq_zero hξ hY'm hT0 hTt hscale
    (fun t => ac_shift_normalized hg hr z hn φ hφ0 t)
  rw [show {x | Y' x = T₀} = Y' ⁻¹' {T₀} from rfl,
    Measure.map_apply hg.measurable (hY'm (measurableSet_singleton _))] at h0
  have h0' : ∀ᵐ ω ∂P, Y' (g ω) ≠ T₀ := by
    rw [ae_iff]; simp only [ne_eq, not_not]; exact h0
  filter_upwards [h0', hD.weyl P g (GM.isGFFPlusCont_of_isWholePlaneGFF hg)] with ω h1 h2
  rw [hYY _ (isLength_of_weylAt0 h2)]; exact h1

end LQGMetric.CONF
