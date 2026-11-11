import Mathlib
import LatticeProb.LQG.LQGMeasureNonatomicMassLocality
import LatticeProb.LQG.LQGWeylScaling

/-!
# The log singularity of `h = h^ℂ - α₀ log |·|` off the origin

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Lemma 2.4. The singular weight step of Lemma 2.4 is stated as the definition `SingularWeightStepLP` and PROVED here
(`singularWeightStep_lp`). The Weyl scaling of the LQG measure of `h^ℂ` (Fact 2.1 III, Duplantier-Sheffield 2011 and
Berestycki-Powell) is the proved result `lqgMeasureWeylScaling_lp` (module `LatticeProb.LQG.LQGWeylScaling`), used with no
hypothesis.

Argument: for `η > 0`, `f_η = -α₀ log max(|·|, η)` is continuous and equals `-α₀ log |·|` on
circles inside `{|x| > η}`; the circle averages of `h^ℂ + f_η` and of `h` agree on compacts of `{|x| > η}` at small scales, so
the vague limits agree there (`isLQGLimit_restrict_eq`); on `{|x| > η}`, `e^{γ f_η(x)} = |x|^{-γα₀}`. Union over `η = 1/(n+1)`.
-/

universe u

namespace LatticeProb.LQG.LQGMeasureNonatomicMass

open MeasureTheory Filter Topology Set Metric LatticeProb.Gauss LatticeProb.LQG
open LatticeProb.LQG.ProfileDerived (dyadicScale_pos)
open LatticeProb.LQG.LQGWeylScalingDerived (lqgMeasureWeylScaling_lp)

/-- The singular weight step of Lemma 2.4. A definition; proved below. -/
def SingularWeightStepLP : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ μ₀ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    IsLQGMeasureOfField P γ 0 hcirc μ₀ →
    ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((μ₀ ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α₀)))).restrict {0}ᶜ

/-- Per sample: the Weyl-scaling identities for `μ₀` (all continuous `f`) and the defining vague limit of `μ_h` give
`μ_h = |x|^{-γα₀} μ₀` on `ℂ \ {0}`. -/
theorem restrict_compl_zero_eq_withDensity {γ α₀ : ℝ} {hc : ℝ → ℂ → ℝ} {m m₀ : Measure ℂ}
    (hm : IsLQGLimit γ (fieldCircleAverage α₀ hc) m)
    (hW : ∀ f : ℂ → ℝ, Continuous f → IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 hc) f)
        (m₀.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))) :
    m.restrict {0}ᶜ = (m₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α₀)))).restrict {0}ᶜ := by
  have hU : ∀ n : ℕ, m.restrict {x : ℂ | ((n : ℝ) + 1)⁻¹ < ‖x‖} =
      (m₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α₀)))).restrict {x : ℂ | ((n : ℝ) + 1)⁻¹ < ‖x‖} := by
    intro n
    set η : ℝ := ((n : ℝ) + 1)⁻¹ with hη
    have hη0 : 0 < η := by positivity
    have hUo : IsOpen {x : ℂ | η < ‖x‖} := isOpen_lt continuous_const continuous_norm
    have hf : Continuous fun x : ℂ => -α₀ * Real.log (max ‖x‖ η) :=
      continuous_const.mul ((continuous_norm.max continuous_const).log fun x => (lt_max_of_lt_right hη0).ne')
    have hloc : ∀ K : Set ℂ, IsCompact K → K ⊆ {x : ℂ | η < ‖x‖} →
        ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, fieldCircleAverage α₀ hc (dyadicScale k) z =
          addCircleAverage (fieldCircleAverage 0 hc) (fun x => -α₀ * Real.log (max ‖x‖ η)) (dyadicScale k) z := by
      intro K hK hKU
      obtain ⟨η', hη', hK'⟩ : ∃ η' > η, ∀ z ∈ K, η' ≤ ‖z‖ := by
        rcases K.eq_empty_or_nonempty with rfl | hne
        · exact ⟨η + 1, by linarith, fun z hz => absurd hz (Set.notMem_empty z)⟩
        obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
        exact ⟨‖z₀‖, hKU hz₀, fun z hz => hmin hz⟩
      have hd : Tendsto dyadicScale atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      filter_upwards [hd.eventually (gt_mem_nhds (sub_pos.2 hη'))] with k hk z hz
      have hca : Real.circleAverage (fun x : ℂ => -α₀ * Real.log (max ‖x‖ η)) z (dyadicScale k) =
          -α₀ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z (dyadicScale k) := by
        calc Real.circleAverage (fun x : ℂ => -α₀ * Real.log (max ‖x‖ η)) z (dyadicScale k)
            = Real.circleAverage ((-α₀) • fun x : ℂ => Real.log ‖x‖) z (dyadicScale k) := by
              refine Real.circleAverage_congr_sphere fun x hx => ?_
              rw [mem_sphere, abs_of_pos (dyadicScale_pos k), dist_eq_norm] at hx
              have h1 := norm_sub_norm_le z x
              rw [norm_sub_rev] at h1
              have hxη : η < ‖x‖ := by linarith [hK' z hz]
              simp only [Pi.smul_apply, smul_eq_mul, max_eq_left hxη.le]
          _ = -α₀ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z (dyadicScale k) := by
              rw [Real.circleAverage_smul, smul_eq_mul]
      simp only [addCircleAverage, fieldCircleAverage, zero_mul, sub_zero, hca]
      ring
    rw [isLQGLimit_restrict_eq hm (hW _ hf) hUo hloc, restrict_withDensity hUo.measurableSet,
      restrict_withDensity hUo.measurableSet]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hUo.measurableSet] with x hx
    have hx0 : 0 < ‖x‖ := hη0.trans hx
    rw [max_eq_left (le_of_lt hx), Real.rpow_def_of_pos hx0]
    ring_nf
  have hcover : ({0}ᶜ : Set ℂ) = ⋃ n : ℕ, {x : ℂ | ((n : ℝ) + 1)⁻¹ < ‖x‖} := by
    ext x
    simp only [mem_compl_iff, mem_singleton_iff, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 hx)
      exact ⟨n, by simpa [one_div] using hn⟩
    · rintro ⟨n, hn⟩ rfl
      have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      have hn' : ((n : ℝ) + 1)⁻¹ < ‖(0 : ℂ)‖ := hn
      rw [norm_zero] at hn'
      linarith
  rw [hcover]
  exact Measure.restrict_iUnion_congr.2 hU

/-- `SingularWeightStepLP` is proved from the Weyl scaling `lqgMeasureWeylScaling_lp` for the field `h^ℂ` (`α₀ = 0`), with no hypothesis. -/
theorem singularWeightStep_lp : SingularWeightStepLP.{u} := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ μ₀ hGFF hμ hμ₀
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  filter_upwards [h1, lqgMeasureWeylScaling_lp P γ 0 hC hcirc hGFF hγ hγ2 hQ μ₀ hμ₀] with ω hω1 hω2
  exact restrict_compl_zero_eq_withDensity hω1 hω2

end LatticeProb.LQG.LQGMeasureNonatomicMass
