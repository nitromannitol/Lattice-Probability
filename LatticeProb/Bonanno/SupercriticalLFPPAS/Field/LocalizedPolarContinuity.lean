/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLFPPAS.Field.LocalizedPolarContinuity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLFPPAS.Field.LocalizedExponentContinuity
import LatticeProb.Bonanno.SupercriticalLFPPAS.Field.RadialHeatIdentity
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedApprox

/-!
# Continuity of the localized radial integral in its cutoff exponent

For a fixed heat scale and center, the PL polar integral varies continuously with the exponent.
The circle-average growth estimate supplies one integrable majorant on every exponent interval.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.B2.Polylog

namespace SupercriticalLFPPAS.Field

private lemma continuousAt_plProf_exponent {δ t r q₀ : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (ht : 1 < t) (htδ : t = Real.log δ⁻¹) :
    ContinuousAt (fun q => plProf q δ r) q₀ := by
  have heq : (fun q => plProf q δ r) =
      fun q => LQGMetric.DFGPS.locProf
        (2 * (Real.log δ + q * Real.log t)) (r : ℂ) := by
    funext q
    change LQGMetric.DFGPS.locProf (Real.log (plRad q δ ^ 2)) (r : ℂ) = _
    rw [log_plRad_sq_formula hδ ht htδ (q := q)]
  rw [heq]
  have hc : Continuous fun q : ℝ =>
      (2 * (Real.log δ + q * Real.log t), (r : ℂ)) := by fun_prop
  exact (LQGMetric.DFGPS.contDiff_locProf.continuous.comp hc).continuousAt

/-- The unnormalized PL polar integral is continuous in the cutoff exponent. -/
theorem continuousAt_plPolarInt_exponent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {g : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGMetric.DFGPS.IsCircleAvgVersion g P H)
    (ω : Ω) (z : ℂ) {δ t A C : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (ht : 1 < t) (htδ : t = Real.log δ⁻¹) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbound : ∀ r : ℝ, 0 < r → |H r z ω| ≤ C * (A / r + r + 1))
    (q₀ : ℝ) :
    ContinuousAt (fun q => polarInt (plProf q) (fun r z => H r z ω) (δ, z)) q₀ := by
  let F : ℝ → ℝ → ℝ := fun q r =>
    r * H r z ω * plProf q δ r * Real.exp (-r ^ 2 / δ ^ 2)
  let c : ℝ := 1 / δ ^ 2
  let G : ℝ → ℝ := fun r =>
    C * ((A + r ^ 2 + r) * Real.exp (-c * r ^ 2))
  have hc : 0 < c := by
    change 0 < 1 / δ ^ 2
    exact one_div_pos.mpr (pow_pos hδ.1 2)
  have hG : IntegrableOn G (Ioi (0 : ℝ)) := by
    have hbase := LQGMetric.DFGPS.integrableOn_gaussW A hc
    exact hbase.const_mul C
  have hG' : Integrable G (volume.restrict (Ioi (0 : ℝ))) := hG
  have hHr : ContinuousOn (fun r : ℝ => H r z ω) (Ioi (0 : ℝ)) :=
    (hH.cont ω).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr, mem_univ _⟩)
  have hcontR : ∀ q : ℝ, ContinuousOn (F q) (Ioi (0 : ℝ)) := by
    intro q
    have hp : Continuous fun r : ℝ => plProf q δ r := by
      unfold plProf
      exact LQGMetric.DFGPS.contDiff_locProf.continuous.comp
        (continuous_const.prodMk Complex.continuous_ofReal)
    have he : Continuous fun r : ℝ => Real.exp (-r ^ 2 / δ ^ 2) := by fun_prop
    exact ((continuousOn_id.mul hHr).mul hp.continuousOn).mul he.continuousOn
  have hmeas : ∀ᶠ q in 𝓝 q₀,
      AEStronglyMeasurable (F q) (volume.restrict (Ioi (0 : ℝ))) :=
    Eventually.of_forall fun q => (hcontR q).aestronglyMeasurable measurableSet_Ioi
  have hmajor : ∀ᶠ q in 𝓝 q₀, ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖F q r‖ ≤ G r := by
    filter_upwards with q
    apply (ae_restrict_iff' measurableSet_Ioi).2
    filter_upwards with r hr
    have hr : 0 < r := hr
    have hprof := abs_plProf_le q δ r
    have hF := hbound r hr
    change |r * H r z ω * plProf q δ r * Real.exp (-r ^ 2 / δ ^ 2)| ≤ G r
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hr, abs_of_pos (Real.exp_pos _)]
    have hA0 : 0 ≤ A / r := div_nonneg hA hr.le
    have hsum : 0 ≤ A / r + r + 1 := by positivity
    calc r * |H r z ω| * |plProf q δ r| * Real.exp (-r ^ 2 / δ ^ 2)
        ≤ r * (C * (A / r + r + 1)) * 1 * Real.exp (-r ^ 2 / δ ^ 2) := by
          gcongr
      _ = G r := by
        simp only [G, c]
        field_simp [ne_of_gt hr]
  have hq : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ContinuousAt (fun q => F q r) q₀ := by
    apply (ae_restrict_iff' measurableSet_Ioi).2
    filter_upwards with r hr
    have hr : 0 < r := hr
    have hp := continuousAt_plProf_exponent (r := r) (q₀ := q₀) hδ ht htδ
    change ContinuousAt
      (fun q => r * H r z ω * plProf q δ r * Real.exp (-r ^ 2 / δ ^ 2)) q₀
    have hrc : ContinuousAt (fun _ : ℝ => r) q₀ := continuousAt_const
    have hHc : ContinuousAt (fun _ : ℝ => H r z ω) q₀ := continuousAt_const
    have hec : ContinuousAt (fun _ : ℝ => Real.exp (-r ^ 2 / δ ^ 2)) q₀ :=
      continuousAt_const
    change ContinuousAt
      ((fun _ : ℝ => r) * (fun _ => H r z ω) * (fun q => plProf q δ r) *
        (fun _ => Real.exp (-r ^ 2 / δ ^ 2))) q₀
    exact ((hrc.mul hHc).mul hp).mul hec
  have hInt : ContinuousAt (fun q => ∫ r in Ioi (0 : ℝ), F q r) q₀ := by
    exact continuousAt_of_dominated hmeas hmajor hG' hq
  have hfactor : ContinuousAt (fun _ : ℝ => 2 / δ ^ 2) q₀ := continuousAt_const
  have hresult := hfactor.mul hInt
  change ContinuousAt
    ((fun _ : ℝ => 2 / δ ^ 2) *
      (fun q => ∫ r in Ioi (0 : ℝ),
        r * H r z ω * plProf q δ r * Real.exp (-r ^ 2 / δ ^ 2))) q₀
  exact hresult

end SupercriticalLFPPAS.Field
