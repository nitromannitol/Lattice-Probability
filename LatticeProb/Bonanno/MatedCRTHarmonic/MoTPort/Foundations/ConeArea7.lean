/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea7 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea6E
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeasJoint
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1RadialMain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_3Tail
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
DMS (arXiv:1409.7055v4) Lemma `lem::c_spaces_orthogonal` (L2187) and Section
4.1: the whole-plane GFF splits as `h = h_{|·|}(0) + (h − h_{|·|}(0))`, the second summand (the
projection onto `H₂(ℂ)`, our `lateralPartC`) having mean zero on every circle about `0`. Paired
with a test function `φ` radial about `0` this says `⟨h − h_{|·|}(0), φ⟩ = 0`, i.e.

  `⟨h, φ⟩ = ∫ φ(x) h_{|x|}(0) dx = ∫_0^∞ 2π r φ(r) h_r(0) dr`,

the polar-coordinate formula of Ding–Falconet–Gwynne–Pfeffer–Sun (arXiv:1905.00380,
 T:715–717), proved in LQGMetric as
`DFGPS.lem2_1RadialPairing`. Here:

* `ae_radialFun_eq_version`: a.s. `x ↦ h_{|x|}(0)` agrees a.e. with a continuous circle-average
  version `H(|x|, 0)` (copied from `ConeArea4.ae_radial_version`, keeping the version explicit);
* **`ae_lateralPartC_radial`**: for every radial test function `φ`, a.s. `⟨lateralPartC h, φ⟩ = 0`
  (`lem2_1RadialPairing` and mathlib's polar formula `integral_fun_norm_addHaar`);
* **`ae_lateralPartC_dil`**: a.s. simultaneously for all dilations `φ(e^{-u} ·)` (`u ∈ ℝ`):
  rationals, then continuity of `u ↦ φ(e^{-u}·)` in `𝓓(ℂ)` (`ConeMeas.continuous_dilTest`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea7

open QuantumZipper LQGMetric

/-- `φ` is radial about `0` -/
def IsRadialTest (φ : TestC) : Prop := ∀ w : ℂ, φ w = φ ((‖w‖ : ℝ) : ℂ)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Field}

/-- a.s. the radial function `x ↦ h_{|x|}(0)` is a.e. a continuous circle-average version
(copied from `ConeArea4.ae_radial_version`, keeping the version) -/
theorem ae_radialFun_eq_version [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) :
    ∃ H : ℝ → ℂ → Ω → ℝ, DFGPS.IsCircleAvgVersion X P H ∧
      ∀ᵐ ω ∂P, radialFun (X ω) =ᵐ[volume] fun z => H ‖z‖ 0 ω := by
  obtain ⟨H, hHc, hHae⟩ := CircleAvg.exists_continuous_version_circleAvg hX
  have hg := ConeArea4.measurable_radG hX.measurable
  have hFt := ConeArea4.measurable_radFt hX.measurable
  have hG : ∀ᵐ ω ∂P, ∀ n j : ℕ, H (((j : ℝ) + 1) / 2 ^ n) 0 ω =
      ConeArea4.radG X (((j : ℝ) + 1) / 2 ^ n) ω := by
    simp only [ae_all_iff]
    intro n j
    exact hHae _ (by positivity) 0
  have hkey : ∀ ω, (∀ n j : ℕ, H (((j : ℝ) + 1) / 2 ^ n) 0 ω =
      ConeArea4.radG X (((j : ℝ) + 1) / 2 ^ n) ω) →
      ∀ r : ℝ, 0 < r → ConeArea4.radFt X (r, ω) = H r 0 ω := by
    intro ω hω r hr
    have hlim : Tendsto (fun n => H (ConeArea4.dyUp n r) 0 ω) atTop (𝓝 (H r 0 ω)) := by
      have hc := ((hHc ω) (r, 0) ⟨hr, mem_univ _⟩).tendsto
      have ht : Tendsto (fun n : ℕ => ((ConeArea4.dyUp n r, (0 : ℂ)) : ℝ × ℂ)) atTop
          (𝓝[Ioi 0 ×ˢ univ] (r, 0)) :=
        tendsto_nhdsWithin_iff.2 ⟨(ConeArea4.tendsto_dyUp hr.le).prodMk_nhds tendsto_const_nhds,
          Eventually.of_forall fun n =>
            (show ((ConeArea4.dyUp n r, (0 : ℂ)) : ℝ × ℂ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) from
              ⟨ConeArea4.dyUp_pos n r, mem_univ _⟩)⟩
      exact hc.comp ht
    have e : (fun n => ConeArea4.radG X (ConeArea4.dyUp n r) ω) =
        fun n => H (ConeArea4.dyUp n r) 0 ω :=
      funext fun n => (hω n _).symm
    show limUnder atTop (fun n => ConeArea4.radG X (ConeArea4.dyUp n r) ω) = _
    rw [e]
    exact hlim.limUnder_eq
  have hS : MeasurableSet {p : Ω × ℂ |
      ConeArea4.radFt X (‖p.2‖, p.1) = ConeArea4.radG X ‖p.2‖ p.1} :=
    measurableSet_eq_fun
      (hFt.comp (f := fun p : Ω × ℂ => (‖p.2‖, p.1))
        ((measurable_norm.comp measurable_snd).prodMk measurable_fst))
      (hg.comp (f := fun p : Ω × ℂ => (‖p.2‖, p.1))
        ((measurable_norm.comp measurable_snd).prodMk measurable_fst))
  have hne : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have hF : ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ),
      ConeArea4.radFt X (‖z‖, ω) = ConeArea4.radG X ‖z‖ ω := by
    rw [Measure.ae_ae_comm hS]
    filter_upwards [hne] with z hz
    have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
    filter_upwards [hG, hHae ‖z‖ hz' 0] with ω hω h1
    rw [hkey ω hω _ hz', h1]; rfl
  refine ⟨fun r z ω => H r z ω + circleAvg (X ω) 1 0,
    ⟨fun ω => (hHc ω).add continuousOn_const, fun r hr z => ?_⟩, ?_⟩
  · filter_upwards [hHae r hr z] with ω hω
    simp [hω]
  filter_upwards [hG, hF] with ω hω hFω
  filter_upwards [hFω, hne] with z h1 h2
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 h2
  rw [← hkey ω hω _ hz', h1]
  simp only [radialFun, ConeArea4.radG]
  ring

theorem volume_real_ball_one : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
  simp [Measure.real, Complex.volume_ball]

/-- **the lateral part kills radial test functions** (DMS L2187; DFGPS T:715–717) -/
theorem ae_lateralPartC_radial [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) {φ : TestC}
    (hφ : IsRadialTest φ) : ∀ᵐ ω ∂P, lateralPartC (X ω) φ = 0 := by
  obtain ⟨H, hH, hR⟩ := ae_radialFun_eq_version hX
  have hpair := DFGPS.lem2_1RadialPairing P X H hX hH 0 φ (fun w => by simpa using hφ w)
  filter_upwards [hpair, hR, ConeArea4.ae_radial_R2 hX] with ω h1 h2 h3
  obtain ⟨R, -, -, hRe, hRl⟩ := h3
  have hloc : LocallyIntegrable (radialFun (X ω)) volume := hRl.congr hRe.symm
  rw [lateralPartC_apply hloc, h1]
  have e : ∫ x, φ x * radialFun (X ω) x =
      ∫ x : ℂ, (fun r : ℝ => φ (r : ℂ) * H r 0 ω) ‖x‖ := by
    refine integral_congr_ae ?_
    filter_upwards [h2] with x hx
    show φ x * radialFun (X ω) x = φ ((‖x‖ : ℝ) : ℂ) * H ‖x‖ 0 ω
    rw [hx, ← hφ x]
  rw [e, integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => φ (r : ℂ) * H r 0 ω),
    Complex.finrank_real_complex, volume_real_ball_one,
    sub_eq_zero]
  simp only [nsmul_eq_mul, smul_eq_mul, zero_add, Nat.cast_ofNat, pow_one,
    show (2 : ℕ) - 1 = 1 from rfl]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  ring

end ConeArea7
end MatedCRTHarmonic.MoTPort
