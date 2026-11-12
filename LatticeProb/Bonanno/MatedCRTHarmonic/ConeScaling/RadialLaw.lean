/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeScaling.RadialLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.LastLevel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Radial
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasND
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeShiftHit
import LatticeProb.Bonanno.QuantumZipper.Proofs.Wire5

/-!
Let `W` be the radial path of the circle-average embedding of the γ-quantum cone (with
`W t = h_{e^{-t}}(0) = CellScaling.coneRadial γ γ B B' t`), as a random element of `C(ℝ, ℝ)`. Then for
every level `y ∈ ℝ` (`map_radShift_coneRadial`):

  `law (radShift Q y W) = law W`, `radShift Q y w t = w(t − L_y) + Q L_y − y`,
  `L_y = sup {s | w(−s) + Q s = y}`.

* `y < 0`: QuantumZipper's unconditional wedge translation (`Wire5.wedge_translation_uncond`, the
  Williams path decomposition) applied to the time-doubled MoT cone process
  (`MoTPort.Cone.isWedgeProcess_of_isConeProcess`). The adapter from the first-passage convention
  to the last-level convention (`neg_lastLevel_eq_hitTime`, `ae_neg_lastLevel_eq_hitTime`,
  `map_shift_neg_lastLevel`) is copied `CellScaling/JointScalingRadialShift.lean`
  (also proved in the cited module).
* `y = 0`: `L_0 = 0` on good paths (`radShift_zero_of_good`).
* `y > 0`: the involution `radShift Q y ∘ radShift Q (−y) = id` on good paths
  (`radShift_radShift_neg`) and the case `−y < 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Pointwise NNReal

namespace MatedCRTHarmonic.ConeScaling

open MatedCRTHarmonic.MoTPort QuantumZipper

/-! ### Negative levels -/

/-- First-passage times scale by one half when a path is run at twice the speed. -/
theorem hitTime_timeDouble (A : ℝ → ℝ) (c : ℝ) :
    WedgeTrans.hitTime (fun t => A (2 * t)) c = WedgeTrans.hitTime A c / 2 := by
  unfold WedgeTrans.hitTime
  let S : Set ℝ := {t | 0 ≤ t ∧ A t ≤ -c}
  have hset : {t : ℝ | 0 ≤ t ∧ A (2 * t) ≤ -c} = (2⁻¹ : ℝ) • S := by
    ext t
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by norm_num : (2⁻¹ : ℝ) ≠ 0)]
    simp only [Set.mem_ofPred_eq, inv_inv, smul_eq_mul, S]
    constructor
    · rintro ⟨ht, hA⟩
      exact ⟨by linarith, hA⟩
    · rintro ⟨ht, hA⟩
      exact ⟨by linarith, hA⟩
  rw [hset, Real.sInf_smul_of_nonneg (by positivity), smul_eq_mul]
  ring

/-- On a continuous cone-shaped path, `−sup {s | A(−s) = y}` is the first nonnegative time with
`A ≤ y`. -/
theorem neg_lastLevel_eq_hitTime {A : ℝ → ℝ} {y : ℝ} (hy : y < 0)
    (hcont : Continuous A) (hzero : A 0 = 0) (hneg : ∀ u < 0, 0 < A u)
    (hhit : ∃ t, 0 ≤ t ∧ A t ≤ y) :
    -sSup {s : ℝ | A (-s) = y} = WedgeTrans.hitTime A (-y) := by
  have hc : 0 < -y := neg_pos.mpr hy
  have hspec := WedgeTrans.hitTime_spec hcont hzero hc (by simpa using hhit)
  let T := WedgeTrans.hitTime A (-y)
  have hAT : A T = y := by simpa [T] using hspec.2.1
  have hgreatest : IsGreatest {s : ℝ | A (-s) = y} (-T) := by
    constructor
    · change A (-(-T)) = y
      simpa only [neg_neg] using hAT
    · intro s hs
      by_cases hs0 : 0 < s
      · have := hneg (-s) (by linarith)
        rw [hs] at this
        linarith
      · have hms : 0 ≤ -s := by linarith
        have hTle : T ≤ -s := hspec.2.2 (-s) hms (by simpa using le_of_eq hs)
        linarith
  rw [hgreatest.csSup_eq]
  simp [T]

section NegLevel

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α Q : ℝ} {A : ℝ → Ω → ℝ}

/-- For a cone process and a fixed negative level, the last-level convention agrees a.s. with the
first-passage convention of wedge translation. -/
theorem ae_neg_lastLevel_eq_hitTime (hA : IsConeProcess α Q A P) (haQ : α < Q)
    {y : ℝ} (hy : y < 0) :
    ∀ᵐ ω ∂P, -sSup {s : ℝ | A (-s) ω = y} =
      WedgeTrans.hitTime (fun t => A t ω) (-y) := by
  let W : ℝ → Ω → ℝ := fun t ω => A (2 * t) ω
  have hW : IsWedgeProcess (Q + 2 * (α - Q)) Q W P :=
    MatedCRTHarmonic.MoTPort.Cone.isWedgeProcess_of_isConeProcess hA
  have haWQ : Q + 2 * (α - Q) < Q := by linarith
  have hcont := (MatedCRTHarmonic.MoTPort.ConeMeas2.aemeasurable_conePath hA).2
  have hland := QuantumZipper.WedgeMeasND.ae_wedgeProcess_landmark haWQ hW
  obtain ⟨B, B', hB, hB', hI, hWB⟩ := hW
  obtain ⟨Bt, hBtm, hBtc, hBtB⟩ := QuantumZipper.WedgeRes.exists_good_version hB
  have hBtmt : ∀ t, Measurable (Bt t) := fun t => hBtm.of_uncurry_left
  have hBtpre : IsPreBrownianReal Bt P :=
    hB.toIsPreBrownianReal.congr fun s => hBtB.mono fun ω h => (h s).symm
  have hbelow := QuantumZipper.WedgeTrans.ae_exists_below hBtpre hBtmt
    (μ := Q - (Q + 2 * (α - Q))) (c := -y) (by linarith) (neg_pos.mpr hy)
  filter_upwards [hcont, hland, hbelow, hBtB] with ω hcont hland hbelow hBtB
  apply neg_lastLevel_eq_hitTime hy hcont
  · simpa [W] using hland.1
  · intro u hu
    have h := hland.2 (u / 2) (by linarith)
    change 0 < A (2 * (u / 2)) ω at h
    convert h using 1
    ring_nf
  · obtain ⟨n, hn⟩ := hbelow
    refine ⟨2 * (n : ℝ), by positivity, ?_⟩
    have hWn : W n ω < y := by
      rw [hWB ω n]
      simp only [wedgePath, Nat.cast_nonneg, ite_true, Real.toNNReal_natCast]
      rw [← hBtB n]
      convert hn using 1 <;> ring_nf
    simpa [W] using hWn.le

/-- **Negative-level cone radial shift law** : for `y < 0` and `L_y = sup {s | A(−s) = y}`,
the path `t ↦ A(−L_y + t) − y` has the law of `A`. -/
theorem map_shift_neg_lastLevel (hA : IsConeProcess α Q A P) (haQ : α < Q)
    {y : ℝ} (hy : y < 0) :
    P.map (fun ω t => A (-sSup {s : ℝ | A (-s) ω = y} + t) ω - y) =
      P.map (fun ω t => A t ω) := by
  let W : ℝ → Ω → ℝ := fun t ω => A (2 * t) ω
  have hW : IsWedgeProcess (Q + 2 * (α - Q)) Q W P :=
    MatedCRTHarmonic.MoTPort.Cone.isWedgeProcess_of_isConeProcess hA
  have haWQ : Q + 2 * (α - Q) < Q := by linarith
  let c : ℝ := -y
  have hc : 0 < c := by dsimp [c]; linarith
  have hUa : AEMeasurable (fun ω t => W t ω) P :=
    QuantumZipper.WedgeLaw.aemeasurable_pathA hW
  let U : Ω → (ℝ → ℝ) := hUa.mk _
  have hUm : Measurable U := hUa.measurable_mk
  have hUe : (fun ω t => W t ω) =ᵐ[P] U := hUa.ae_eq_mk
  have hshiftLaw : P.map (fun ω => QuantumZipper.F1.shiftPath c (U ω)) = P.map U := by
    have hraw := QuantumZipper.Wire5.wedge_translation_uncond hW haWQ hc
    calc
      P.map (fun ω => QuantumZipper.F1.shiftPath c (U ω)) =
          P.map (fun ω t => W
            (sInf {s | 0 ≤ s ∧ W s ω ≤ -c} + t) ω + c) := by
        refine Measure.map_congr ?_
        filter_upwards [hUe, QuantumZipper.WedgeCan4.ae_continuous_wedgeProcess hW]
          with ω hU hcont
        rw [← hU, QuantumZipper.F1.shiftPath_eq_of_continuous' hcont]
      _ = P.map (fun ω t => W t ω) := hraw
      _ = P.map U := Measure.map_congr hUe
  let rho : (ℝ → ℝ) → (ℝ → ℝ) := fun p t => p (t / 2)
  have hrho : Measurable rho := measurable_pi_iff.2 fun t => measurable_pi_apply (t / 2)
  have hmap := congrArg (Measure.map rho) hshiftLaw
  have hm1 : Measurable fun ω => QuantumZipper.F1.shiftPath c (U ω) :=
    (QuantumZipper.F1.measurable_shiftPath c).comp hUm
  rw [Measure.map_map hrho hm1, Measure.map_map hrho hUm] at hmap
  have hlast := ae_neg_lastLevel_eq_hitTime hA haQ hy
  have hcont := (MatedCRTHarmonic.MoTPort.ConeMeas2.aemeasurable_conePath hA).2
  calc
    P.map (fun ω t => A (-sSup {s : ℝ | A (-s) ω = y} + t) ω - y) =
        P.map (rho ∘ fun ω => QuantumZipper.F1.shiftPath c (U ω)) := by
      refine Measure.map_congr ?_
      filter_upwards [hUe, hcont, hlast] with ω hU hcont hlast
      funext t
      have hWcont : Continuous fun u => W u ω :=
        hcont.comp (continuous_const.mul continuous_id)
      rw [Function.comp_apply, ← hU, QuantumZipper.F1.shiftPath_eq_of_continuous' hWcont]
      have htime : sInf {s | 0 ≤ s ∧ W s ω ≤ -c} = -sSup {s : ℝ | A (-s) ω = y} / 2 := by
        rw [hlast]; exact hitTime_timeDouble (fun u => A u ω) c
      dsimp [rho]
      rw [htime]
      show A (-sSup {s : ℝ | A (-s) ω = y} + t) ω - y =
        A (2 * (-sSup {s : ℝ | A (-s) ω = y} / 2 + t / 2)) ω + -y
      rw [show 2 * (-sSup {s : ℝ | A (-s) ω = y} / 2 + t / 2) =
        -sSup {s : ℝ | A (-s) ω = y} + t by ring]
      ring
    _ = P.map (rho ∘ U) := hmap
    _ = P.map (fun ω t => A t ω) := by
      refine Measure.map_congr ?_
      filter_upwards [hUe] with ω hU
      funext t
      simp only [Function.comp_apply, rho, ← hU, W]
      congr 1
      ring

end NegLevel

/-! ### Laws on `C(ℝ, ℝ)` -/

/-- The Borel σ-algebra of `C(ℝ, ℝ)` is the trace of the product σ-algebra (as ). -/
theorem measurableSpace_continuousMap_eq_comap :
    (inferInstance : MeasurableSpace C(ℝ, ℝ)) =
      MeasurableSpace.comap (fun f : C(ℝ, ℝ) => (⇑f : ℝ → ℝ)) MeasurableSpace.pi := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, MeasurableSpace.pi,
    MeasurableSpace.comap_iSup]
  simp_rw [MeasurableSpace.comap_comp]
  rfl

theorem measurable_coeFn_continuousMap : Measurable fun f : C(ℝ, ℝ) => (⇑f : ℝ → ℝ) :=
  measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval t

/-- Measures on `C(ℝ, ℝ)` are determined by the laws of the underlying functions. -/
theorem continuousMap_measure_ext {μ ν : Measure C(ℝ, ℝ)}
    (h : μ.map (fun f : C(ℝ, ℝ) => (⇑f : ℝ → ℝ)) = ν.map (fun f : C(ℝ, ℝ) => (⇑f : ℝ → ℝ))) :
    μ = ν := by
  ext s hs
  have hs' : MeasurableSet[MeasurableSpace.comap (fun f : C(ℝ, ℝ) => (⇑f : ℝ → ℝ))
      MeasurableSpace.pi] s := by
    rw [← measurableSpace_continuousMap_eq_comap]; exact hs
  obtain ⟨t, ht, rfl⟩ := hs'
  rw [← Measure.map_apply measurable_coeFn_continuousMap ht,
    ← Measure.map_apply measurable_coeFn_continuousMap ht, h]

section Law

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Negative levels, for a `C(ℝ, ℝ)`-valued version `W = Q · + A` of a cone process. -/
theorem map_radShift_of_neg {α Q : ℝ} {A : ℝ → Ω → ℝ} (hA : IsConeProcess α Q A P)
    (haQ : α < Q) {W : Ω → C(ℝ, ℝ)} (hWm : Measurable W)
    (hWA : ∀ᵐ ω ∂P, ∀ t, W ω t = Q * t + A t ω) {y : ℝ} (hy : y < 0) :
    P.map (fun ω => radShift Q y (W ω)) = P.map W := by
  let D : (ℝ → ℝ) → (ℝ → ℝ) := fun a t => Q * t + a t
  have hD : Measurable D := measurable_pi_iff.2 fun t => (measurable_pi_apply t).const_add _
  let Dinv : (ℝ → ℝ) → (ℝ → ℝ) := fun a t => a t - Q * t
  have hDinv : Measurable Dinv := measurable_pi_iff.2 fun t => (measurable_pi_apply t).sub_const _
  have hDD : ∀ a, Dinv (D a) = a := fun a => by funext t; simp [D, Dinv]
  let S : Ω → ℝ → ℝ := fun ω t => A (-sSup {s : ℝ | A (-s) ω = y} + t) ω - y
  let Ap : Ω → ℝ → ℝ := fun ω t => A t ω
  have hcoe := measurable_coeFn_continuousMap
  have hRW : Measurable fun ω => radShift Q y (W ω) := (measurable_radShift Q y).comp hWm
  have hS : (fun ω => (⇑(radShift Q y (W ω)) : ℝ → ℝ)) =ᵐ[P] fun ω => D (S ω) := by
    filter_upwards [hWA] with ω hω
    have hL : lastLevel Q y (W ω) = sSup {s : ℝ | A (-s) ω = y} := by
      unfold lastLevel
      congr 1
      ext s
      simp only [Set.mem_ofPred_eq, hω]
      constructor <;> intro h <;> linarith
    funext t
    simp only [radShift_apply, hL, hω, D, S]
    ring_nf
  have hAp : (fun ω => (⇑(W ω) : ℝ → ℝ)) =ᵐ[P] fun ω => D (Ap ω) := by
    filter_upwards [hWA] with ω hω
    funext t
    simp only [hω, D, Ap]
  have hSm : AEMeasurable S P := by
    refine (hDinv.comp (hcoe.comp hRW)).aemeasurable.congr ?_
    filter_upwards [hS] with ω hω
    simp only [Function.comp_apply, hω, hDD]
  have hApm : AEMeasurable Ap P := by
    refine (hDinv.comp (hcoe.comp hWm)).aemeasurable.congr ?_
    filter_upwards [hAp] with ω hω
    simp only [Function.comp_apply, hω, hDD]
  apply continuousMap_measure_ext
  rw [Measure.map_map hcoe hRW, Measure.map_map hcoe hWm]
  change P.map (fun ω => (⇑(radShift Q y (W ω)) : ℝ → ℝ)) = P.map (fun ω => (⇑(W ω) : ℝ → ℝ))
  rw [Measure.map_congr hS, Measure.map_congr hAp]
  change P.map (D ∘ S) = P.map (D ∘ Ap)
  rw [← AEMeasurable.map_map_of_aemeasurable hD.aemeasurable hSm,
    ← AEMeasurable.map_map_of_aemeasurable hD.aemeasurable hApm]
  exact congrArg (Measure.map D) (map_shift_neg_lastLevel hA haQ hy)

omit [IsProbabilityMeasure P] in
/-- From negative levels to all levels, on a.s. good paths. -/
theorem map_radShift_of_good {Q : ℝ} {W : Ω → C(ℝ, ℝ)} (hWm : Measurable W)
    (hneg : ∀ y : ℝ, y < 0 → P.map (fun ω => radShift Q y (W ω)) = P.map W)
    (hgood : ∀ᵐ ω ∂P, IsGoodRadial Q (W ω)) (y : ℝ) :
    P.map (fun ω => radShift Q y (W ω)) = P.map W := by
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · exact hneg y hy
  · refine Measure.map_congr ?_
    filter_upwards [hgood] with ω hω
    exact radShift_zero_of_good hω
  · calc P.map (fun ω => radShift Q y (W ω)) = (P.map W).map (radShift Q y) :=
          (Measure.map_map (measurable_radShift Q y) hWm).symm
      _ = (P.map (fun ω => radShift Q (-y) (W ω))).map (radShift Q y) := by
          rw [hneg (-y) (by linarith)]
      _ = P.map (fun ω => radShift Q y (radShift Q (-y) (W ω))) :=
          Measure.map_map (measurable_radShift Q y) ((measurable_radShift Q (-y)).comp hWm)
      _ = P.map W := by
          refine Measure.map_congr ?_
          filter_upwards [hgood] with ω hω
          exact radShift_radShift_neg Q y hω

/-- **The radial law of the γ-quantum cone** (DMS Prop 4.13(i), radial part): if `W` is a measurable `C(ℝ, ℝ)`-valued version of the cone's radial path
`coneRadial γ γ B B'`, then for every level `y`, `radShift Q y W` has the law of `W`. -/
theorem map_radShift_coneRadial {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P) {W : Ω → C(ℝ, ℝ)} (hWm : Measurable W)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t)
    (y : ℝ) :
    P.map (fun ω => radShift (CellScaling.lqgQ γ) y (W ω)) = P.map W := by
  have hQ : CellScaling.lqgQ γ = QuantumZipper.Qc γ := by
    dsimp [CellScaling.lqgQ, QuantumZipper.Qc]
  let A : ℝ → Ω → ℝ := fun t ω =>
    LQGCone.motConeRadial γ γ (fun s => B s ω) (fun s => B' s ω) t
  have hA : IsConeProcess γ (CellScaling.lqgQ γ) A P := by
    rw [hQ]; exact LQGCone.isConeProcess_motConeRadial hB hB' hBB'
  have hγQ : γ < CellScaling.lqgQ γ := by linarith [CellScaling.lqgQ_sub_pos hγ hγ2]
  have hWA : ∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.lqgQ γ * t + A t ω := by
    filter_upwards [hW] with ω hω t
    rw [hω, LQGCone.coneRadial_eq_Q_add_motConeRadial]
  have hgood : ∀ᵐ ω ∂P, IsGoodRadial (CellScaling.lqgQ γ) (W ω) := by
    filter_upwards [hW, hB.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift hB' (CellScaling.lqgQ_sub_pos hγ hγ2)] with ω hω h0 hdrift
    refine ⟨?_, fun s hs => ?_⟩
    · rw [hω, CellScaling.coneRadial, ite_eq_left (le_refl (0 : ℝ))]
      simp [h0]
    · have e : W ω (-s) + CellScaling.lqgQ γ * s =
          CellScaling.coneLogRadial γ γ (fun t => B t ω) (fun t => B' t ω) s := by
        rw [hω]; rfl
      rw [e, CellScaling.coneLogRadial_of_pos _ _ _ _ hs]
      exact hdrift.pos_of_lastZeroR_lt (by linarith [hdrift.lastZeroR_nonneg])
  exact map_radShift_of_good hWm (fun y hy => map_radShift_of_neg hA hγQ hWm hWA hy) hgood y

end Law

end MatedCRTHarmonic.ConeScaling
