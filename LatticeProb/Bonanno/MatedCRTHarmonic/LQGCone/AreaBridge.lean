/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCone.AreaBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea6E
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea7
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Radial

/-!
# Two whole-plane LQG area constructions

This module identifies the dyadic area measure in the `CellScaling` definitions with the ported MoT
whole-plane area measure. The only difference in the approximants is the spelling of the same
dyadic radius.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.LQGCone

open MatedCRTHarmonic.CellScaling
open MatedCRTHarmonic.MoTPort
open QuantumZipper ProbabilityTheory

/-- MoT's cone process stores the radial average after subtracting its deterministic `Qt` drift. -/
def motConeRadial (γ α : ℝ) (b b' : ℝ≥0 → ℝ) : ℝ → ℝ :=
  fun t => coneRadial γ α b b' t - lqgQ γ * t

/-- The radial path in the `CellScaling` convention is `Qt` plus the MoT cone process. -/
theorem coneRadial_eq_Q_add_motConeRadial (γ α : ℝ) (b b' : ℝ≥0 → ℝ) (t : ℝ) :
    coneRadial γ α b b' t = lqgQ γ * t + motConeRadial γ α b b' t := by
  simp [motConeRadial]

theorem motConeRadial_eq_conePath (γ α : ℝ) (b b' : ℝ≥0 → ℝ) (t : ℝ) :
    motConeRadial γ α b b' t =
      MatedCRTHarmonic.MoTPort.conePath α (lqgQ γ) b b' t := by
  by_cases ht : 0 ≤ t
  · rw [motConeRadial, coneRadial, if_pos ht,
      MatedCRTHarmonic.MoTPort.Cone.conePath_of_nonneg α (lqgQ γ) b b' ht]
    simp [lqgQ]
    ring
  · have ht' : t < 0 := lt_of_not_ge ht
    rw [motConeRadial, coneRadial, if_neg ht,
      MatedCRTHarmonic.MoTPort.Cone.conePath_of_neg α (lqgQ γ) b b' ht']
    have htail : MatedCRTHarmonic.MoTPort.coneTail α (lqgQ γ) b' =
        fun u => b' u.toNNReal + (lqgQ γ - α) * u := by
      funext u
      simp [MatedCRTHarmonic.MoTPort.coneTail]
      ring
    rw [htail]
    let c : ℝ → ℝ := fun u => b' u.toNNReal + (lqgQ γ - α) * u
    have hlast : QuantumZipper.lastZero c = lastZeroR c := rfl
    change c (lastZeroR c - t) + lqgQ γ * t - lqgQ γ * t =
      c (-t + QuantumZipper.lastZero c)
    rw [hlast, add_sub_cancel_right]
    congr 1
    ring

/-- The `CellScaling` cone field is the ported MoT cone field after subtracting the `Qt` drift from the
radial process. -/
def motConeField (γ α : ℝ) (X : LQGMetric.DistC) (b b' : ℝ≥0 → ℝ) :
    LQGMetric.DistC :=
  MatedCRTHarmonic.MoTPort.coneField
    (MatedCRTHarmonic.MoTPort.lateralPartC X)
    (motConeRadial γ α b b') (QuantumZipper.Qc γ)

theorem coneField_eq_motConeField (γ α : ℝ) (X : LQGMetric.DistC)
    (b b' : ℝ≥0 → ℝ) :
    MatedCRTHarmonic.CellScaling.coneField X (coneRadial γ α b b') =
      motConeField γ α X b b' := by
  have hprofile :
      (fun z : ℂ => coneRadial γ α b b' (-Real.log ‖z‖)) =
        (fun z => QuantumZipper.Qc γ * (-Real.log ‖z‖) +
          motConeRadial γ α b b' (-Real.log ‖z‖)) := by
    funext z
    rw [coneRadial_eq_Q_add_motConeRadial]
    have hQ : lqgQ γ = QuantumZipper.Qc γ := by
      dsimp [lqgQ, QuantumZipper.Qc]
    rw [hQ]
  change MatedCRTHarmonic.CellScaling.lateralPart X +
      MatedCRTHarmonic.CellScaling.ofFunC _ =
    MatedCRTHarmonic.MoTPort.lateralPartC X +
      MatedCRTHarmonic.MoTPort.ofFunC _
  have hlateral : lateralPart X = MatedCRTHarmonic.MoTPort.lateralPartC X := rfl
  rw [hlateral, hprofile]
  rfl

/-- The Brownian pair in the `CellScaling` radial convention induces the corresponding MoT cone process. -/
theorem isConeProcess_motConeRadial {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α : ℝ} {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P) :
    MatedCRTHarmonic.MoTPort.IsConeProcess α (QuantumZipper.Qc γ)
      (fun t ω => motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t) P := by
  refine ⟨B, B', hB, hB', hBB', ?_⟩
  intro ω t
  have hQ : lqgQ γ = QuantumZipper.Qc γ := by
    dsimp [lqgQ, QuantumZipper.Qc]
  have h := motConeRadial_eq_conePath γ α (fun s => B s ω) (fun s => B' s ω) t
  rw [hQ] at h
  exact h

/-- Almost surely the cone field has the circle-average limits needed by the additive-constant
rule. Away from the cone point it is the whole-plane GFF plus a continuous function. -/
theorem ae_hasCircleAvgs_coneField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → LQGMetric.DistC} {α Q : ℝ}
    {A : ℝ → Ω → ℝ} (hX : LQGMetric.IsWholePlaneGFF X P)
    (hA : MatedCRTHarmonic.MoTPort.IsConeProcess α Q A P) :
    ∀ᵐ ω ∂P, MatedCRTHarmonic.MoTPort.ConeArea.HasCircleAvgs
      (MatedCRTHarmonic.MoTPort.coneField
        (MatedCRTHarmonic.MoTPort.lateralPartC (X ω)) (fun t => A t ω) Q) := by
  filter_upwards [MatedCRTHarmonic.MoTPort.ConeArea4.ae_radial_R2 hX,
    MatedCRTHarmonic.MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA,
    MatedCRTHarmonic.MoTPort.ConeArea3.ae_hasCircleAvgs hX,
    (MatedCRTHarmonic.MoTPort.ConeMeas2.aemeasurable_conePath hA).2]
    with ω hR hAl hc hAc
  obtain ⟨R, hRc, -, hxR, hRl⟩ := hR
  rw [MatedCRTHarmonic.MoTPort.ConeArea3.coneField_eq_add_ofFunC hxR hRl hAl]
  unfold MatedCRTHarmonic.MoTPort.ConeArea.HasCircleAvgs
  intro k
  have hsphereNull : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ Metric.sphere 0 (QuantumZipper.radius k) :=
    measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume 0 (QuantumZipper.radius k))
  filter_upwards [hc k, hsphereNull] with z ⟨a, ha⟩ hz
  have hzNorm : ‖z‖ ≠ QuantumZipper.radius k := by
    intro he
    apply hz
    rw [Metric.mem_sphere, dist_zero_right]
    exact he
  have hsph : Metric.sphere z (QuantumZipper.radius k) ⊆ Set.univ \ {0} := by
    intro w hw
    refine ⟨mem_univ _, ?_⟩
    intro hw0
    subst w
    apply hzNorm
    simpa [Metric.mem_sphere, dist_zero_left] using hw
  let g : ℂ → ℝ := MatedCRTHarmonic.MoTPort.ConeArea3.coneShift
    (fun t => A t ω) Q R
  have hgl : LocallyIntegrable g volume := hAl.sub hRl
  have hg : ContinuousOn g (Set.univ \ {0}) :=
    MatedCRTHarmonic.MoTPort.ConeArea3.continuousOn_coneShift hAc Q hRc
  have hU : IsOpen (Set.univ \ ({(0 : ℂ)} : Set ℂ)) :=
    isOpen_univ.sdiff isClosed_singleton
  have hlimG := MatedCRTHarmonic.MoTPort.ConeArea3.tendsto_mollAvg_ofFunC
    hgl hU hg (z := z) (r := QuantumZipper.radius k)
      (QuantumZipper.radius_pos k) hsph
  have hsplit : ∀ n, LQGMetric.CircleAvg.mollAvg
      (X ω + MatedCRTHarmonic.MoTPort.ofFunC g) n z (QuantumZipper.radius k) =
      LQGMetric.CircleAvg.mollAvg (X ω) n z (QuantumZipper.radius k) +
        LQGMetric.CircleAvg.mollAvg (MatedCRTHarmonic.MoTPort.ofFunC g)
          n z (QuantumZipper.radius k) := by
    intro n
    simp only [LQGMetric.CircleAvg.mollAvg_eq, ContinuousLinearMap.add_apply]
  have hsum := ha.add hlimG
  refine ⟨a + Real.circleAverage g z (QuantumZipper.radius k), ?_⟩
  exact hsum.congr (fun n => (hsplit n).symm)

/-- At every fixed logarithmic radius, the circle average of the cone field is its prescribed
radial process, almost surely. -/
theorem ae_circleAvg_coneField_exp {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ α : ℝ} {X : Ω → LQGMetric.DistC}
    {B B' : ℝ≥0 → Ω → ℝ}
    (hX : LQGMetric.IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P) :
    ∀ t : ℝ, ∀ᵐ ω ∂P,
      LQGMetric.circleAvg
        (MatedCRTHarmonic.CellScaling.coneField (X ω)
          (MatedCRTHarmonic.CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω)))
        (Real.exp (-t)) 0 =
          MatedCRTHarmonic.CellScaling.coneRadial γ α
            (fun s => B s ω) (fun s => B' s ω) t := by
  obtain ⟨H, hHc, hHae, hEv⟩ := MatedCRTHarmonic.MoTPort.ConeArea5.exists_radFt_version hX
  intro t
  let r : ℝ := Real.exp (-t)
  have hr : 0 < r := Real.exp_pos _
  let A : ℝ → Ω → ℝ := fun s ω =>
    motConeRadial γ α (fun u => B u ω) (fun u => B' u ω) s
  have hA : MatedCRTHarmonic.MoTPort.IsConeProcess α (QuantumZipper.Qc γ) A P :=
    isConeProcess_motConeRadial hB hB' hBB'
  filter_upwards [MatedCRTHarmonic.MoTPort.ConeArea4.ae_radial_R2 hX,
    MatedCRTHarmonic.MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA,
    MatedCRTHarmonic.MoTPort.ConeArea5.ae_ae_radFt_eq hX, hEv,
    LQGMetric.CircleAvg.ae_tendsto_mollAvg hX 0 hr, hHae r hr 0,
    (MatedCRTHarmonic.MoTPort.ConeMeas2.aemeasurable_conePath hA).2]
    with ω hR hAl hrad hEvω ⟨a, ha⟩ hHpoint hAc
  obtain ⟨R, hRc, -, hxR, hRl⟩ := hR
  let Rv : ℝ → ℝ := fun s => H s 0 ω + LQGMetric.circleAvg (X ω) 1 0
  have hRvc : ContinuousOn Rv (Ioi 0) := by
    dsimp [Rv]
    exact ((hHc ω).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ _⟩)).add continuousOn_const
  have hne : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 :=
    compl_mem_ae_iff.2 (measure_singleton 0)
  have hRvVersion : MatedCRTHarmonic.MoTPort.radialFun (X ω) =ᵐ[volume]
      fun z => Rv ‖z‖ := by
    filter_upwards [hrad, hne] with z hradz hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hev := hEvω ‖z‖ hzpos
    change LQGMetric.circleAvg (X ω) ‖z‖ 0 = Rv ‖z‖
    dsimp [Rv]
    have hradG := hradz.symm.trans hev
    dsimp [MatedCRTHarmonic.MoTPort.ConeArea4.radG] at hradG
    linarith
  have hRsame := MatedCRTHarmonic.MoTPort.ConeArea5.eqOn_of_ae_norm hRc hRvc
    (hxR.symm.trans hRvVersion) r hr
  have hRpoint : R r = LQGMetric.circleAvg (X ω) r 0 := by
    rw [hRsame]
    dsimp [Rv]
    rw [hHpoint]
    ring
  let g : ℂ → ℝ := MatedCRTHarmonic.MoTPort.ConeArea3.coneShift
    (fun s => A s ω) (QuantumZipper.Qc γ) R
  have hgl : LocallyIntegrable g volume := hAl.sub hRl
  have hg : ContinuousOn g (Set.univ \ {0}) :=
    MatedCRTHarmonic.MoTPort.ConeArea3.continuousOn_coneShift hAc (QuantumZipper.Qc γ) hRc
  have hU : IsOpen (Set.univ \ ({(0 : ℂ)} : Set ℂ)) := isOpen_univ.sdiff isClosed_singleton
  have hsph : Metric.sphere (0 : ℂ) r ⊆ Set.univ \ {(0 : ℂ)} := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    intro hz0
    subst z
    have : (0 : ℝ) = r := by simpa [Metric.mem_sphere] using hz
    exact (ne_of_gt hr) this.symm
  have hlimX := ha
  have hlimG := MatedCRTHarmonic.MoTPort.ConeArea3.tendsto_mollAvg_ofFunC
    hgl hU hg (z := 0) (r := r) hr hsph
  have hdecomp : MatedCRTHarmonic.MoTPort.coneField
      (MatedCRTHarmonic.MoTPort.lateralPartC (X ω)) (fun s => A s ω) (QuantumZipper.Qc γ) =
      X ω + MatedCRTHarmonic.MoTPort.ofFunC g :=
    MatedCRTHarmonic.MoTPort.ConeArea3.coneField_eq_add_ofFunC hxR hRl hAl
  have hsum : LQGMetric.circleAvg (X ω + MatedCRTHarmonic.MoTPort.ofFunC g) r 0 =
      LQGMetric.circleAvg (X ω) r 0 + Real.circleAverage g 0 r :=
    MatedCRTHarmonic.MoTPort.ConeArea3.circleAvg_add_ofFunC hgl hU hg hr hsph hlimX
  have hgAvg : Real.circleAverage g 0 r =
      QuantumZipper.Qc γ * (-Real.log r) + A (-Real.log r) ω - R r := by
    apply Real.circleAverage_const_on_circle
    intro z hz
    have hznorm : ‖z‖ = r := by
      have hh : ‖z‖ = |r| := by
        simpa [Metric.mem_sphere, dist_zero_right] using hz
      rw [abs_of_pos hr] at hh
      exact hh
    simp [g, MatedCRTHarmonic.MoTPort.ConeArea3.coneShift, hznorm]
  have hformula : LQGMetric.circleAvg
      (MatedCRTHarmonic.MoTPort.coneField
        (MatedCRTHarmonic.MoTPort.lateralPartC (X ω)) (fun s => A s ω)
        (QuantumZipper.Qc γ)) r 0 =
      QuantumZipper.Qc γ * (-Real.log r) + A (-Real.log r) ω := by
    calc
      _ = LQGMetric.circleAvg (X ω + MatedCRTHarmonic.MoTPort.ofFunC g) r 0 := by
        rw [hdecomp]
      _ = LQGMetric.circleAvg (X ω) r 0 + Real.circleAverage g 0 r := hsum
      _ = _ := by rw [hgAvg, hRpoint]; ring
  have hQ : QuantumZipper.Qc γ = lqgQ γ := by
    dsimp [lqgQ, QuantumZipper.Qc]
  have hradial := coneRadial_eq_Q_add_motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t
  calc
    _ = QuantumZipper.Qc γ * t + motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t := by
      rw [coneField_eq_motConeField]
      change LQGMetric.circleAvg
        (MatedCRTHarmonic.MoTPort.coneField
          (MatedCRTHarmonic.MoTPort.lateralPartC (X ω))
          (fun s => motConeRadial γ α (fun u => B u ω) (fun u => B' u ω) s)
          (QuantumZipper.Qc γ)) (Real.exp (-t)) 0 = _
      change LQGMetric.circleAvg
        (MatedCRTHarmonic.MoTPort.coneField
          (MatedCRTHarmonic.MoTPort.lateralPartC (X ω))
          (fun s => A s ω) (QuantumZipper.Qc γ)) r 0 = _
      rw [hformula, show -Real.log r = t by simp [r]]
    _ = MatedCRTHarmonic.CellScaling.coneRadial γ α
        (fun s => B s ω) (fun s => B' s ω) t := by
      rw [hQ]
      exact hradial.symm

theorem dyadicScale_eq_radius (k : ℕ) : dyadicScale k = QuantumZipper.radius k := by
  simp [dyadicScale, QuantumZipper.radius, zpow_neg]

theorem lqgAreaApprox_eq_areaApproxC (γ : ℝ) (h : LQGMetric.DistC) (k : ℕ) :
    lqgAreaApprox γ h k = areaApproxC γ h k := by
  rw [lqgAreaApprox, areaApproxC, dyadicScale_eq_radius]

theorem vagueLimitC_iff_vagueLimitOn_univ {γ : ℝ} {h : LQGMetric.DistC}
    {μ : Measure ℂ} :
    IsVagueLimitC (lqgAreaApprox γ h) μ ↔
      QuantumZipper.IsVagueLimitOn Set.univ (areaApproxC γ h) μ := by
  rw [IsVagueLimitC, QuantumZipper.IsVagueLimitOn]
  constructor
  · rintro ⟨hcompact, hf⟩
    refine ⟨?_, ?_, ?_⟩
    · simp
    · intro K hK hKU
      exact hcompact K hK
    · intro f hf1 hf2 hf3
      exact (hf f hf1 hf2).congr (fun k => by rw [lqgAreaApprox_eq_areaApproxC])
  · rintro ⟨h0, hcompact, hf⟩
    refine ⟨?_, ?_⟩
    · intro K hK
      exact hcompact K hK (subset_univ K)
    · intro f hf1 hf2
      exact (hf f hf1 hf2 (by simp)).congr (fun k => by rw [lqgAreaApprox_eq_areaApproxC])

theorem lqgArea_eq_qAreaC (γ : ℝ) (h : LQGMetric.DistC) :
    lqgArea γ h = qAreaC γ h := by
  by_cases hx : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ
  · have hy : ∃ μ, QuantumZipper.IsVagueLimitOn Set.univ (areaApproxC γ h) μ := by
      rcases hx with ⟨μ, hμ⟩
      exact ⟨μ, (vagueLimitC_iff_vagueLimitOn_univ).1 hμ⟩
    have hleft : IsVagueLimitC (lqgAreaApprox γ h) (lqgArea γ h) := by
      unfold lqgArea
      rw [dif_pos hx]
      exact Classical.choose_spec hx
    have hright : QuantumZipper.IsVagueLimitOn Set.univ (areaApproxC γ h) (qAreaC γ h) :=
      ConeArea.isVagueLimitOn_qAreaC hy
    apply QuantumZipper.isVagueLimitOn_unique isOpen_univ
      ((vagueLimitC_iff_vagueLimitOn_univ).1 hleft) hright
  · have hy : ¬ ∃ μ, QuantumZipper.IsVagueLimitOn Set.univ (areaApproxC γ h) μ := by
      intro hy
      apply hx
      rcases hy with ⟨μ, hμ⟩
      exact ⟨μ, (vagueLimitC_iff_vagueLimitOn_univ).2 hμ⟩
    simp [lqgArea, dif_neg hx, qAreaC, dif_neg hy]

/-- The area defined by the `CellScaling` dyadic approximations is locally finite, including its junk-zero
case. -/
theorem lqgArea_compact_lt_top (γ : ℝ) (h : LQGMetric.DistC) {K : Set ℂ}
    (hK : IsCompact K) : lqgArea γ h K < ⊤ := by
  rw [lqgArea_eq_qAreaC]
  exact MatedCRTHarmonic.MoTPort.ConeArea.qAreaC_compact_lt_top γ h hK

/-- Additive-constant covariance for the `CellScaling` area, obtained from the port's exact qAreaC rule. -/
theorem lqgArea_addConst_eq {γ : ℝ} {h : LQGMetric.DistC}
    (hh : MatedCRTHarmonic.MoTPort.ConeArea.HasCircleAvgs h)
    (hv : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ) (c : ℝ) :
    lqgArea γ (LQGMetric.addConst h c) =
      ENNReal.ofReal (Real.exp (γ * c)) • lqgArea γ h := by
  have hv' : ∃ μ, QuantumZipper.IsVagueLimitOn Set.univ (areaApproxC γ h) μ := by
    rcases hv with ⟨μ, hμ⟩
    exact ⟨μ, (vagueLimitC_iff_vagueLimitOn_univ).1 hμ⟩
  rw [lqgArea_eq_qAreaC, lqgArea_eq_qAreaC]
  exact MatedCRTHarmonic.MoTPort.ConeArea.qAreaC_addConst hh hv' c

/-- For every subcritical radial drift `α < Q`, the area approximations of the `CellScaling` cone field
have an a.s. vague limit. The Brownian and independence assumptions are exactly those used to
construct the ported MoT cone process. -/
theorem ae_isVagueLimitC_coneField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ α : ℝ} {X : Ω → LQGMetric.DistC}
    {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < QuantumZipper.Qc γ)
    (hX : LQGMetric.IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (hXA : IndepFun X (fun ω t =>
      motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t) P) :
    ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitC
      (lqgAreaApprox γ
        (MatedCRTHarmonic.CellScaling.coneField (X ω)
          (MatedCRTHarmonic.CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω)))) μ := by
  let W : ℝ := 2 * γ * (QuantumZipper.Qc γ - α)
  have hW : 0 < W := by dsimp [W]; positivity
  have hconeAlpha : MatedCRTHarmonic.MoTPort.coneAlpha γ W = α := by
    dsimp [MatedCRTHarmonic.MoTPort.coneAlpha, W]
    field_simp
    ring
  let A : ℝ → Ω → ℝ := fun t ω =>
    motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t
  have hA : MatedCRTHarmonic.MoTPort.IsConeProcess α (QuantumZipper.Qc γ) A P :=
    isConeProcess_motConeRadial hB hB' hBB'
  have hAlpha : MatedCRTHarmonic.MoTPort.IsConeProcess
      (MatedCRTHarmonic.MoTPort.coneAlpha γ W) (QuantumZipper.Qc γ) A P := by
    rw [hconeAlpha]
    exact hA
  have hpunct := MatedCRTHarmonic.MoTPort.ConeArea4.ae_isVagueLimitOn_coneField_punctured
    hX hA hγ hγ2
  have haway := MatedCRTHarmonic.MoTPort.ConeArea4.ae_fin_away_coneField
    hX hA hγ hγ2
  have htight := MatedCRTHarmonic.MoTPort.ConeArea6.b3' hγ hγ2 hW
    Ω _ P X A inferInstance hX hAlpha hXA
  let F : Ω → LQGMetric.DistC := fun ω =>
    MatedCRTHarmonic.MoTPort.coneField (MatedCRTHarmonic.MoTPort.lateralPartC (X ω))
      (fun t => A t ω) (QuantumZipper.Qc γ)
  filter_upwards [hpunct, haway, htight] with ω hp hf ht
  obtain ⟨μ, hμ⟩ := hp
  have hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop,
      MatedCRTHarmonic.MoTPort.areaApproxC γ (F ω) k K < ⊤ := by
    intro K hK
    exact MatedCRTHarmonic.MoTPort.ConeArea4.fin_of_away_of_tight
      hf ht hK
  have hfull := MatedCRTHarmonic.MoTPort.ConeArea2.isVagueLimitOn_univ_of_punctured
    hμ hfin ht
  have hprop : F ω = MatedCRTHarmonic.CellScaling.coneField (X ω)
      (MatedCRTHarmonic.CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω)) := by
    exact (coneField_eq_motConeField γ α (X ω) (fun s => B s ω) (fun s => B' s ω)).symm
  have hseq' := congrArg (fun h : LQGMetric.DistC =>
    MatedCRTHarmonic.MoTPort.areaApproxC γ h) hprop
  refine ⟨μ, (vagueLimitC_iff_vagueLimitOn_univ).2 ?_⟩
  rw [← hseq']
  exact hfull

/-- Almost surely the actual `lqgArea` value is the vague limit of the `CellScaling` cone approximations.
This also rules out the junk-zero branch in the definition of `lqgArea` on the cone event. -/
theorem ae_lqgArea_vagueLimitC_coneField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ α : ℝ} {X : Ω → LQGMetric.DistC}
    {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < QuantumZipper.Qc γ)
    (hX : LQGMetric.IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (hXA : IndepFun X (fun ω t =>
      motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t) P) :
    ∀ᵐ ω ∂P,
      IsVagueLimitC
        (lqgAreaApprox γ
          (MatedCRTHarmonic.CellScaling.coneField (X ω)
            (MatedCRTHarmonic.CellScaling.coneRadial γ α
              (fun s => B s ω) (fun s => B' s ω))))
        (lqgArea γ
          (MatedCRTHarmonic.CellScaling.coneField (X ω)
            (MatedCRTHarmonic.CellScaling.coneRadial γ α
              (fun s => B s ω) (fun s => B' s ω)))) := by
  filter_upwards [ae_isVagueLimitC_coneField hγ hγ2 hα hX hB hB' hBB' hXA] with ω hω
  rcases hω with ⟨μ, hμ⟩
  have hqExists : ∃ ν, QuantumZipper.IsVagueLimitOn Set.univ
      (areaApproxC γ (MatedCRTHarmonic.CellScaling.coneField (X ω)
        (MatedCRTHarmonic.CellScaling.coneRadial γ α
          (fun s => B s ω) (fun s => B' s ω)))) ν := by
    exact ⟨μ, (vagueLimitC_iff_vagueLimitOn_univ).1 hμ⟩
  have hq : QuantumZipper.IsVagueLimitOn Set.univ
      (areaApproxC γ (MatedCRTHarmonic.CellScaling.coneField (X ω)
        (MatedCRTHarmonic.CellScaling.coneRadial γ α
          (fun s => B s ω) (fun s => B' s ω))))
      (qAreaC γ (MatedCRTHarmonic.CellScaling.coneField (X ω)
        (MatedCRTHarmonic.CellScaling.coneRadial γ α
          (fun s => B s ω) (fun s => B' s ω)))) :=
    MatedCRTHarmonic.MoTPort.ConeArea.isVagueLimitOn_qAreaC hqExists
  rw [lqgArea_eq_qAreaC]
  exact (vagueLimitC_iff_vagueLimitOn_univ).2 hq

/-- Almost-sure additive-constant covariance for the `CellScaling` cone area. -/
theorem ae_lqgArea_addConst_coneField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ α : ℝ} {X : Ω → LQGMetric.DistC}
    {B B' : ℝ≥0 → Ω → ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < QuantumZipper.Qc γ) (hX : LQGMetric.IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (hXA : IndepFun X (fun ω t =>
      motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t) P) (c : ℝ) :
    ∀ᵐ ω ∂P,
      lqgArea γ (LQGMetric.addConst (MatedCRTHarmonic.CellScaling.coneField (X ω)
        (MatedCRTHarmonic.CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω))) c) =
        ENNReal.ofReal (Real.exp (γ * c)) •
          lqgArea γ (MatedCRTHarmonic.CellScaling.coneField (X ω)
            (MatedCRTHarmonic.CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω))) := by
  let A : ℝ → Ω → ℝ := fun t ω =>
    motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t
  have hA : MatedCRTHarmonic.MoTPort.IsConeProcess α (QuantumZipper.Qc γ) A P :=
    isConeProcess_motConeRadial hB hB' hBB'
  filter_upwards [ae_isVagueLimitC_coneField hγ hγ2 hα hX hB hB' hBB' hXA,
    ae_hasCircleAvgs_coneField hX hA] with ω hv hh
  have hfield : MatedCRTHarmonic.CellScaling.coneField (X ω)
      (MatedCRTHarmonic.CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω)) =
      motConeField γ α (X ω) (fun s => B s ω) (fun s => B' s ω) :=
    coneField_eq_motConeField γ α (X ω) (fun s => B s ω) (fun s => B' s ω)
  have hh' : MatedCRTHarmonic.MoTPort.ConeArea.HasCircleAvgs
      (MatedCRTHarmonic.CellScaling.coneField (X ω)
        (MatedCRTHarmonic.CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω))) := by
    simpa only [MatedCRTHarmonic.MoTPort.ConeArea.HasCircleAvgs, hfield, motConeField] using hh
  exact lqgArea_addConst_eq hh' hv c

/-- The γ-cone unit radius is normalized to one almost surely. -/
theorem ae_coneScale_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, MatedCRTHarmonic.CellScaling.coneScale γ γ
      (fun t => B t ω) (fun t => B' t ω) 1 = 1 :=
  MatedCRTHarmonic.CellScaling.ae_coneScale_one hγ hγ2 hB hB'

/-- Almost surely, for every level `b₀ > 1`, the γ-cone radial log profile attains its last (and
largest) passage of `γ⁻¹ log b₀` at `log R_{b₀}`. In particular this passage time is finite. -/
theorem ae_coneScale_attainedMaximum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (B : ℝ≥0 → Ω → ℝ)
    {B' : ℝ≥0 → Ω → ℝ} (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, ∀ b₀ : ℝ, 1 < b₀ →
      0 < Real.log (MatedCRTHarmonic.CellScaling.coneScale γ γ
        (fun t => B t ω) (fun t => B' t ω) b₀) ∧
      MatedCRTHarmonic.CellScaling.coneLogRadial γ γ (fun t => B t ω) (fun t => B' t ω)
        (Real.log (MatedCRTHarmonic.CellScaling.coneScale γ γ
          (fun t => B t ω) (fun t => B' t ω) b₀)) = γ⁻¹ * Real.log b₀ ∧
      ∀ s, MatedCRTHarmonic.CellScaling.coneLogRadial γ γ (fun t => B t ω) (fun t => B' t ω) s =
        γ⁻¹ * Real.log b₀ →
          s ≤ Real.log (MatedCRTHarmonic.CellScaling.coneScale γ γ
            (fun t => B t ω) (fun t => B' t ω) b₀) :=
  MatedCRTHarmonic.CellScaling.ae_coneScale_lastPassage hγ hγ2 B hB'

end MatedCRTHarmonic.LQGCone
