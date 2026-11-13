/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLFPPAS.Field.RadialHeatIdentity at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_2
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedPolar
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedCont
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1RadialMain

/-!
# Radial integration for the heat field

For the heat kernel at time `δ²/2`, polar coordinates give the weight
`(2s/δ²) exp(-s²/δ²)`.  The proof reuses the DFGPS polar formula for the difference between the
heat field and its compactly supported radial cutoff, and the compact radial-pairing formula for
that cutoff.  The localized polar-pairing adapter supplies the latter simultaneously in all
positive scales and centers.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open LQGMetric (DistC heatMollify)
open LQGMetric.LFPP (locBump locMollify locTest)
open LQGMetric.DFGPS (locProf)
open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF)
open SupercriticalLQGUniqueness.B2.Polylog (polarInt locTestT)

namespace SupercriticalLFPPAS.Field

/-- Almost surely, the heat mollification is the radial integral of the circle-average process,
with the normalization for the kernel `p_{δ²/2}`. -/
theorem ae_heatMollify_eq_radialIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ H : ℝ → ℂ → Ω → ℝ, LQGMetric.DFGPS.IsCircleAvgVersion h P H ∧
      ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ z : ℂ,
        heatMollify δ (h ω) z =
          2 / δ ^ 2 * ∫ s in Ioi (0 : ℝ), s * H s z ω * Real.exp (-s ^ 2 / δ ^ 2) := by
  obtain ⟨H, hH⟩ := LQGMetric.DFGPS.exists_isCircleAvgVersion hh.1
  let profile : ℝ → ℝ → ℝ := fun ε r => locProf (Real.log ε) (r : ℂ)
  have hprofileCont : ContinuousOn (fun p : ℝ × ℝ => profile p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    have hlog : ContinuousOn (fun p : ℝ × ℝ => Real.log p.1)
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
      Real.continuousOn_log.comp continuous_fst.continuousOn fun p hp =>
        (ne_of_gt (mem_prod.mp hp).1)
    have hreal : ContinuousOn (fun p : ℝ × ℝ => (p.2 : ℂ))
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
      Complex.continuous_ofReal.comp_continuousOn continuous_snd.continuousOn
    exact LQGMetric.DFGPS.contDiff_locProf.continuous.comp_continuousOn
      (hlog.prodMk hreal)
  have hprofileBound : ∀ ε ∈ Ioi (0 : ℝ), ∀ r : ℝ, |profile ε r| ≤ 1 := by
    intro ε hε r
    have hr := LQGMetric.DFGPS.locProf_mem_Icc (Real.log ε) (r : ℂ)
    have hlow : 0 ≤ profile ε r := hr.1
    have hup : profile ε r ≤ 1 := hr.2
    rw [abs_le]
    exact ⟨by linarith, hup⟩
  have hK : ContinuousOn locTestT (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) :=
    SupercriticalLQGUniqueness.B2.Polylog.continuousOn_locTestT
  have hKw : ∀ ε ∈ Ioi (0 : ℝ), ∀ z x : ℂ,
      locTestT (ε, z) x = profile ε ‖x - z‖ * LQGMetric.heatKernel (ε ^ 2 / 2) z x := by
    intro ε hε z x
    have hε' : 0 < ε := hε
    rw [SupercriticalLQGUniqueness.B2.Polylog.locTestT_of_pos hε']
    rw [LQGMetric.DFGPS.locTest_apply']
    have hb : locBump ε hε' (z - x) = locBump ε hε' (‖x - z‖ : ℂ) := by
      rw [LQGMetric.LFPP.locBump_radial, norm_sub_rev]
    rw [hb, LQGMetric.DFGPS.locBump_eq_locProf hε']
  have hLocal := SupercriticalLQGUniqueness.B2.Polylog.ae_pairing_eq_polarInt
      (P := P) (g := h) (H := H) hh.1 hH isOpen_Ioi (by intro ε hε; exact hε)
      (K := locTestT) hK (w := profile) hprofileCont hprofileBound hKw
  have hTail := LQGMetric.DFGPS.lem2_1PolarDiff_of
      LQGMetric.DFGPS.lem2_1PolarPoint LQGMetric.DFGPS.lem2_1HeatJoint P h H hh.1 hH
  have hScale : ∀ n : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ ζ : ℝ, 0 < ζ →
      ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ z ∈ ball (0 : ℂ) n,
        |H r z ω| ≤ C * max (max (A * Real.log (1 / r))
          (Real.log r ^ (1 / 2 + ζ))) 1 := fun n =>
    LQGMetric.DFGPS.lem2_2 hh.1 hH n
  choose A hA hAb using hScale
  have hGrowth : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ C : ℝ, ∀ r : ℝ, 0 < r →
      ∀ z ∈ ball (0 : ℂ) n,
        |H r z ω| ≤ C * max (max (A n * Real.log (1 / r))
          (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 :=
    ae_all_iff.2 fun n => hAb n (1 / 2) (by norm_num)
  refine ⟨H, hH, ?_⟩
  filter_upwards [hLocal, hTail, hGrowth] with ω hωLocal hωTail hωGrowth
  intro δ hδ z
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hz : z ∈ ball (0 : ℂ) n := by
    rw [mem_ball, dist_zero_right]
    exact hn
  obtain ⟨C, hC⟩ := hωGrowth n
  have hA0 : 0 ≤ A n := (hA n).le
  let tail : ℝ → ℝ → ℝ := fun ε r => 1 - profile ε r
  have hTailBound : ∀ r, |tail δ r| ≤ 1 := by
    intro r
    have hp := LQGMetric.DFGPS.locProf_mem_Icc (Real.log δ) (r : ℂ)
    change |1 - profile δ r| ≤ 1
    rw [abs_le]
    constructor <;> linarith [hp.1, hp.2]
  have hLocalBound : ∀ r, |profile δ r| ≤ 1 := fun r => hprofileBound δ hδ r
  have hHr : ContinuousOn (fun r : ℝ => H r z ω) (Ioi (0 : ℝ)) :=
    (hH.cont ω).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => by simp [hr])
  have hProfileR : Continuous fun r : ℝ => profile δ r := by
    exact LQGMetric.DFGPS.contDiff_locProf.continuous.comp
      (continuous_const.prodMk Complex.continuous_ofReal)
  have hTailR : Continuous fun r : ℝ => tail δ r := continuous_const.sub hProfileR
  have hscalePair : ∀ (u : ℝ → ℝ), Continuous u → (∀ r, |u r| ≤ 1) →
      IntegrableOn (fun r : ℝ => r * H r z ω * u r * Real.exp (-r ^ 2 / δ ^ 2))
        (Ioi (0 : ℝ)) := by
    intro u huCont hu
    have hcont : ContinuousOn
        (fun r : ℝ => r * H r z ω * u r * Real.exp (-r ^ 2 / δ ^ 2)) (Ioi 0) := by
      exact ((continuousOn_id.mul hHr).mul huCont.continuousOn).mul
        (Real.continuous_exp.comp ((continuous_pow 2).neg.div_const (δ ^ 2))).continuousOn
    have hmajor : IntegrableOn
        (fun r : ℝ => |C| * ((A n + r ^ 2 + r) * Real.exp (-(1 / δ ^ 2) * r ^ 2)))
        (Ioi 0) := by
      have hbase := LQGMetric.DFGPS.integrableOn_gaussW (A n)
        (by positivity : 0 < (1 / δ ^ 2 : ℝ))
      exact hbase.const_mul |C|
    refine Integrable.mono' hmajor (hcont.aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_))
    have hr : 0 < r := hr
    have hFr := SupercriticalLQGUniqueness.B2.Polylog.abs_le_of_lem2_2 hA0 hr
      (hC r hr z hz)
    have hExp : Real.exp (-r ^ 2 / δ ^ 2) = Real.exp (-(1 / δ ^ 2) * r ^ 2) := by
      congr 1
      field_simp
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hr,
      abs_of_pos (Real.exp_pos _), hExp]
    calc r * |H r z ω| * |u r| * Real.exp (-(1 / δ ^ 2) * r ^ 2)
        ≤ r * (|C| * (A n / r + r + 1)) * 1 * Real.exp (-(1 / δ ^ 2) * r ^ 2) := by
          gcongr
          · exact hu r
      _ = (A n + r ^ 2 + r) * Real.exp (-(1 / δ ^ 2) * r ^ 2) * |C| := by
          field_simp [ne_of_gt hr]
      _ = |C| * ((A n + r ^ 2 + r) * Real.exp (-(1 / δ ^ 2) * r ^ 2)) := by ring
  have hIlocal := hscalePair (profile δ) hProfileR hLocalBound
  have hItail := hscalePair (tail δ) hTailR hTailBound
  have hTailEq := hωTail δ hδ z
  have hLocalEq := hωLocal δ hδ z
  have hLoc : locMollify δ hδ (h ω) z =
      polarInt profile (fun r z => H r z ω) (δ, z) := by
    simpa only [SupercriticalLQGUniqueness.B2.Polylog.locTestT_of_pos hδ,
      LQGMetric.LFPP.locMollify] using hLocalEq
  have hT : heatMollify δ (h ω) z - locMollify δ hδ (h ω) z =
      polarInt tail (fun r z => H r z ω) (δ, z) := by
    simpa [polarInt, tail, profile, LQGMetric.DFGPS.locBump_eq_locProf hδ] using hTailEq.2
  have hSum : polarInt tail (fun r z => H r z ω) (δ, z) +
        polarInt profile (fun r z => H r z ω) (δ, z) =
      polarInt (fun _ _ => 1) (fun r z => H r z ω) (δ, z) := by
    simp only [polarInt]
    rw [← mul_add, ← integral_add hItail hIlocal]
    apply congrArg (fun x : ℝ => 2 / δ ^ 2 * x)
    exact setIntegral_congr_fun measurableSet_Ioi fun r _ => by
      simp [tail]
      ring
  calc heatMollify δ (h ω) z =
        (heatMollify δ (h ω) z - locMollify δ hδ (h ω) z) +
          locMollify δ hδ (h ω) z := by ring
    _ = polarInt tail (fun r z => H r z ω) (δ, z) +
          polarInt profile (fun r z => H r z ω) (δ, z) := by rw [hT, hLoc]
    _ = polarInt (fun _ _ => 1) (fun r z => H r z ω) (δ, z) := hSum
    _ = 2 / δ ^ 2 * ∫ s in Ioi (0 : ℝ), s * H s z ω * Real.exp (-s ^ 2 / δ ^ 2) := by
      simp [polarInt]

end SupercriticalLFPPAS.Field
