import LatticeProb.Analysis.HarmonicBridge
import LatticeProb.Analysis.HarmonicScaling
import LatticeProb.Prob.BrownianExit
import LatticeProb.Prob.BrownianExitPosition
import LatticeProb.Prob.BrownianOpenExit
import LatticeProb.Prob.BrownianOpenExitFinite
import LatticeProb.Prob.BrownianPathCoords
import LatticeProb.Prob.BrownianPathHarmonicExit

/-!
# Harmonic exit identities for Brownian motion with open-set exit times

Let `B` be a Brownian motion on `Euc d` started at `x`, and let `U` be a bounded open set. The
exit position `B τ`, with `τ` the first exit time of `B` from `U`, satisfies
`𝔼 [f (B τ)] = f x` whenever `f` is harmonic on `U`.

The identity is first proved for compactly supported `C²` functions `f` harmonic on `U`
(`integral_openExit_harmonic_compactSupport`). The transfer to the Brownian motion is done
through the rescaled process `√d • (B - x)`, whose sample paths have a standard Brownian law, and
the harmonicity of `f` is transported by the affine change of variables `w ↦ x + (√d)⁻¹ • w`.
The form for a function harmonic on a neighbourhood of `closure U`
(`integral_openExit_harmonicNearClosure`) follows by a compactly supported extension that agrees
with the function near `closure U`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- The preimage of a bounded set under the affine map `w ↦ x + c • w` is bounded when
`c ≠ 0`. -/
theorem isBounded_preimage_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hUb : Bornology.IsBounded U) (x : E) {c : ℝ} (hc : c ≠ 0) :
    Bornology.IsBounded ((fun w : E ↦ x + c • w) ⁻¹' U) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).mp hUb
  refine (Metric.isBounded_closedBall :
    Bornology.IsBounded (Metric.closedBall (0 : E) (|c⁻¹| * (R + ‖x‖)))).subset ?_
  intro w hw
  have hy : ‖x + c • w‖ ≤ R := mem_closedBall_zero_iff.mp (hR hw)
  rw [mem_closedBall_zero_iff]
  have hwx : w = c⁻¹ • ((x + c • w) - x) := by
    rw [add_sub_cancel_left, inv_smul_smul₀ hc]
  calc ‖w‖ = ‖c⁻¹ • ((x + c • w) - x)‖ := by rw [← hwx]
    _ = |c⁻¹| * ‖(x + c • w) - x‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |c⁻¹| * (R + ‖x‖) := by
      gcongr
      linarith [norm_sub_le (x + c • w) x]

/-- For a Brownian motion `B` on `Euc d` with `1 ≤ d` started at `x`, and a bounded open set `U`,
the expectation of a compactly supported `C²` function `f`, harmonic on `U`, at the exit position
`B τ` of `U` equals `f x`. -/
theorem integral_openExit_harmonic_compactSupport {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {x : Euc d} {B : ℝ≥0 → Ω → Euc d} (hB : IsBrownianSpace d x B P)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    (hh : IsHarmonicOn f U) :
    ∫ ω, f (B (openExitTime B U ω).toNNReal ω) ∂P = f x := by
  haveI := hB.isProbabilityMeasure
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hsd : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hdpos).ne'
  have hc : (Real.sqrt d)⁻¹ ≠ 0 := inv_ne_zero hsd
  obtain ⟨C, hCm, hC, -, hCW, hcoord, hindep⟩ := hB.exists_continuousVersion
  have hμ : IsStandardBrownianLaw (P.map (pathMap C hC)) :=
    isStandardBrownianLaw_map_pathMap hCm hC hcoord hindep
  have hg : ContDiff ℝ 2 (fun w : Euc d ↦ f (x + (Real.sqrt d)⁻¹ • w)) :=
    hf.comp (by fun_prop)
  have hgsupp : HasCompactSupport (fun w : Euc d ↦ f (x + (Real.sqrt d)⁻¹ • w)) :=
    hsupp.comp_homeomorph ((Homeomorph.smulOfNeZero (Real.sqrt d)⁻¹ hc).trans
      (Homeomorph.addLeft x))
  have hVo : IsOpen ((fun w : Euc d ↦ x + (Real.sqrt d)⁻¹ • w) ⁻¹' U) :=
    hU.preimage (by fun_prop)
  have hVb : Bornology.IsBounded ((fun w : Euc d ↦ x + (Real.sqrt d)⁻¹ • w) ⁻¹' U) :=
    isBounded_preimage_affine hUb x hc
  have hgharm : IsHarmonicOn (fun w : Euc d ↦ f (x + (Real.sqrt d)⁻¹ • w))
      ((fun w : Euc d ↦ x + (Real.sqrt d)⁻¹ • w) ⁻¹' U) :=
    hh.comp_affine hU x (Real.sqrt d)⁻¹
  have key := standardBrownianLaw_integral_exit_harmonic_compactSupport hd hμ hVo hVb hg hgsupp
    hgharm 0
  simp only [zero_add, smul_zero, add_zero] at key
  rw [integral_exitPosition_eq_pathMap hd hU hCm hC hCW hf.continuous.measurable]
  exact key

/-- For a Brownian motion `B` on `Euc d` with `1 ≤ d` started at `x`, and a bounded open set `U`,
the expectation of a function `h`, harmonic on an open neighbourhood of `closure U`, at the exit
position `B τ` of `U` equals `h x`. If `x` lies outside `U`, the exit time is `0` almost surely
and the identity is trivial. -/
theorem integral_openExit_harmonicNearClosure {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {x : Euc d} {B : ℝ≥0 → Ω → Euc d} (hB : IsBrownianSpace d x B P)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {h : Euc d → ℝ} (hh : HarmonicNearClosure h U) :
    ∫ ω, h (B (openExitTime B U ω).toNNReal ω) ∂P = h x := by
  haveI := hB.isProbabilityMeasure
  by_cases hxU : x ∈ U
  · obtain ⟨W, hW, hUW, hhW⟩ := hh
    obtain ⟨g, V, -, hUV, -, hg, hgc, -, heq, hgharm⟩ :=
      hhW.exists_compactSupport_eq_near_compact hUb.isCompact_closure hW hUW
    have hUsub : U ⊆ V := subset_closure.trans hUV
    have hgharmU : IsHarmonicOn g U :=
      ⟨hg.contDiffOn, fun y hy ↦ hgharm.laplacian_eq_zero (hUsub hy)⟩
    have hA := integral_openExit_harmonic_compactSupport hd hB hU hUb hg hgc hgharmU
    have hae : ∀ᵐ ω ∂P,
        h (B (openExitTime B U ω).toNNReal ω) = g (B (openExitTime B U ω).toNNReal ω) := by
      filter_upwards [hB.start, ae_openExitTime_ne_top hd hB hUb, hB.cont]
        with ω hstart hfin hcont
      have hmem : B (openExitTime B U ω).toNNReal ω ∈ frontier U :=
        openExitTime_mem_frontier hU hcont (by rwa [hstart]) hfin
      exact (heq (hUV (frontier_subset_closure hmem))).symm
    rw [integral_congr_ae hae, hA]
    exact heq (hUsub hxU)
  · have hae : ∀ᵐ ω ∂P, h (B (openExitTime B U ω).toNNReal ω) = h x := by
      filter_upwards [hB.start] with ω hstart
      have h0 : B 0 ω ∉ U := by rwa [hstart]
      rw [openExitTime_eq_zero_of_not_mem h0]
      simp [hstart]
    rw [integral_congr_ae hae, integral_const]
    simp

namespace BrownianOpenHarmonicExitExample

/-- For a Brownian motion on `Euc 2` started at `x`, the expected coordinate `y ↦ y 0` of the exit
position from the open unit ball equals the coordinate of `x`. -/
theorem coord_integral_openExit_ball {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {x : Euc 2} {B : ℝ≥0 → Ω → Euc 2} (hB : IsBrownianSpace 2 x B P) :
    ∫ ω, (B (openExitTime B (Metric.ball 0 1) ω).toNNReal ω) 0 ∂P = x 0 :=
  integral_openExit_harmonicNearClosure (by norm_num) hB Metric.isOpen_ball
    Metric.isBounded_ball BrownianPathHarmonicExitExample.coord_harmonicNearClosure_ball

/-- For a Brownian motion on `Euc 2` started at `x`, the expected value of the constant function
`1` at the exit position from the open unit ball equals `1`. -/
theorem const_integral_openExit_ball {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {x : Euc 2} {B : ℝ≥0 → Ω → Euc 2} (hB : IsBrownianSpace 2 x B P) :
    ∫ ω, (fun _ : Euc 2 ↦ (1 : ℝ)) (B (openExitTime B (Metric.ball 0 1) ω).toNNReal ω) ∂P =
      (fun _ : Euc 2 ↦ (1 : ℝ)) x :=
  integral_openExit_harmonicNearClosure (by norm_num) hB Metric.isOpen_ball
    Metric.isBounded_ball BrownianPathHarmonicExitExample.const_harmonicNearClosure_ball

end BrownianOpenHarmonicExitExample

end LatticeProb
