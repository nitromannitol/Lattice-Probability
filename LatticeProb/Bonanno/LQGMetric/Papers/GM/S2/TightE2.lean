/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightE2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightE2Core

/-!
# GM S2.4e: geodesics stay in a bounded region, uniformly in scale and centre (task P2-TIGHT)

GM (arXiv:1905.00383v3) l. 1434 (proof of Prop. 3.6, step 1) and l. 3605 (proof of Prop. 6.1,
step 1): with probability close to one, `sup_{u,v ∈ B_{2r}(z)} D_h(u, v) < D_h(B_{2r}(z),
∂B_{Rr}(z))`, uniformly in `r` and `z`. GM attribute this to Axiom V; decision D-A3
(`decisions/DEC-A.md` (c)) shows it needs DFGPS Thm 1.5 and LM Lemma 3.1, which enter here as the
explicit hypotheses `hT15 : Blueprint.DFGPSScaling` and `hL31 : Blueprint.LMLem3_1a`.

`gm_S2_4e`: the general statement, from `gm_S2_4e_normalized` (centre `0`, normalized field)
applied to `h(· + z) − h_1(z)` (a normalized whole-plane GFF: `IsWholePlaneGFF.affineComp`,
`IsWholePlaneGFF.addConst`, `CircleAvg.ae_circleAvg_addConst_one_zero`), using Axiom IV′ and
Weyl scaling for constants (`IsWeakLQGMetric.ae_dist_addConst`); the event is invariant under
multiplying `D_h` by a positive constant. Own argument; DEVIATIONS DA5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric
namespace GM
namespace Tight

open Blueprint

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- **GM.S2.4e** (D-A3): for every `β > 0` there is `R > 1` such that, uniformly over whole-plane
GFFs `h`, `r > 0` and `z`, with probability `> 1 − β` the `D_h`-diameter of `B̄_{2r}(z)` is
smaller than `D_h(B̄_{2r}(z), ∂B_{Rr}(z))` (a separating level `M`). -/
theorem gm_S2_4e (hT15 : DFGPSScaling) (hL31 : LMLem3_1a) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) {β : ℝ≥0∞} (hβ : 0 < β) :
    ∃ R : ℝ, 1 < R ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      P {ω | ¬ ∃ M : ℝ, (∀ u ∈ closedBall z (2 * r), ∀ v ∈ closedBall z (2 * r),
          (D (h ω)).1 (u, v) < M) ∧
        ∀ x ∈ closedBall z (2 * r), ∀ y ∈ sphere z (R * r), M < (D (h ω)).1 (x, y)} < β := by
  obtain ⟨R, hR, H⟩ := gm_S2_4e_normalized hT15 hL31 hγ0 hγ2 hD hβ
  refine ⟨R, hR, ?_⟩
  intro Ω _ P _ h hh r hr z
  have hz := hh.affineComp one_pos z
  have hN := measurable_circleAvg_left 1 0
  have hn : IsNormalizedWPGFF (fun ω => addConst (affineComp 1 z (h ω))
      (-circleAvg (affineComp 1 z (h ω)) 1 0)) P := by
    refine ⟨hz.addConst (hN.comp hz.measurable).neg, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hz] with ω hω
    rw [hω]; ring
  refine lt_of_le_of_lt (measure_mono_ae ?_) (H P _ hn r hr)
  filter_upwards [hD.translation P h (isGFFPlusCont_of_wp hh) z,
    hD.ae_dist_addConst (isGFFPlusCont_of_wp hz)] with ω htr hwc hbad
  rintro ⟨M, hM1, hM2⟩
  apply hbad
  set a := circleAvg (affineComp 1 z (h ω)) 1 0
  set e := Real.exp (xiGamma γ * -a) with he
  have hep : 0 < e := Real.exp_pos _
  have key : ∀ u v : ℂ, (D (addConst (affineComp 1 z (h ω)) (-a))).1 (u - z, v - z) =
      e * (D (h ω)).1 (u, v) := fun u v => by
    rw [hwc, htr, sub_add_cancel, sub_add_cancel]
  have hball : ∀ u, u ∈ closedBall z (2 * r) → u - z ∈ closedBall (0 : ℂ) (2 * r) :=
    fun u hu => by rwa [mem_closedBall, dist_zero_right, ← dist_eq_norm]
  refine ⟨M / e, fun u hu v hv => ?_, fun x hx y hy => ?_⟩
  · have := hM1 _ (hball u hu) _ (hball v hv)
    rw [key] at this
    rw [lt_div_iff₀ hep]; linarith
  · have hy' : y - z ∈ sphere (0 : ℂ) (R * r) := by
      rwa [mem_sphere, dist_zero_right, ← dist_eq_norm]
    have := hM2 _ (hball x hx) _ hy'
    rw [key] at this
    rw [div_lt_iff₀ hep]; linarith

end Tight
end GM
end LQGMetric
