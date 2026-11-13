/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLFPPAS.Field.LocalizedPolarFormula at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLFPPAS.Field.LocalizedPolarContinuity
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_2

/-!
# Polar representation for every localized cutoff radius

The pinned polar-pairing theorem handles each fixed exponent.  Countable rational exponents and
continuity in the exponent give one almost-sure identity for every cutoff radius.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistC)
open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF)
open SupercriticalLQGUniqueness.B2.Polylog

namespace SupercriticalLFPPAS.Field

/-- Almost surely, every normalized localized field is given by the circle-average polar
integral, simultaneously in the heat scale, center, and exponent. -/
theorem ae_plMollify_eq_polarInt_allExponent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ H : ℝ → ℂ → Ω → ℝ, LQGMetric.DFGPS.IsCircleAvgVersion h P H ∧
      ∀ᵐ ω ∂P, ∀ δ : ℝ, ∀ hδ : δ ∈ Ioo (0 : ℝ) 1,
        1 < Real.log δ⁻¹ → ∀ z : ℂ, ∀ q : ℝ,
          plZ q δ hδ * plMollify q δ hδ (h ω) z =
            polarInt (plProf q) (fun r z => H r z ω) (δ, z) := by
  obtain ⟨H, hH⟩ := LQGMetric.DFGPS.exists_isCircleAvgVersion hh.1
  have hFixed : ∀ q : ℚ, ∀ᵐ ω ∂P, ∀ δ : ℝ, ∀ hδ : δ ∈ Ioo (0 : ℝ) 1,
      ∀ z : ℂ, h ω (plTest (q : ℝ) δ hδ z) =
        polarInt (plProf (q : ℝ)) (fun r z => H r z ω) (δ, z) := by
    intro q
    have hpair := ae_pairing_eq_polarInt (P := P) (g := h) hh.1 hH
      (hI := isOpen_Ioo) (hI0 := fun _ hx => hx.1)
      (K := plTestT (q : ℝ)) (hK := continuousOn_plTestT (q : ℝ))
      (w := plProf (q : ℝ)) (hw := continuousOn_plProf (q : ℝ))
      (hw1 := fun δ _ r => abs_plProf_le (q : ℝ) δ r)
      (hKw := fun δ hδ z x => plTestT_apply' (q : ℝ) δ hδ z x)
    filter_upwards [hpair] with ω hω
    intro δ hδ z
    have hω' := hω δ hδ z
    rw [plTestT_of_mem (q : ℝ) hδ z] at hω'
    exact hω'
  have hFixedAll : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ δ : ℝ, ∀ hδ : δ ∈ Ioo (0 : ℝ) 1,
      ∀ z : ℂ, h ω (plTest (q : ℝ) δ hδ z) =
        polarInt (plProf (q : ℝ)) (fun r z => H r z ω) (δ, z) :=
    ae_all_iff.2 hFixed
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
  filter_upwards [hFixedAll, hGrowth] with ω hωFixed hωGrowth
  intro δ hδ hlog z
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hz : z ∈ ball (0 : ℂ) n := by
    rw [mem_ball, dist_zero_right]
    exact hn
  obtain ⟨C, hC⟩ := hωGrowth n
  have hbound : ∀ r : ℝ, 0 < r →
      |H r z ω| ≤ |C| * (A n / r + r + 1) := by
    intro r hr
    exact abs_le_of_lem2_2 (hA n).le hr (hC r hr z hz)
  have hLeft : Continuous fun q : ℝ =>
      plZ q δ hδ * plMollify q δ hδ (h ω) z := by
    rw [continuous_iff_continuousAt]
    intro q
    have hZ := continuousAt_plZ_exponent hδ hlog q
    have hM := continuousAt_plMollify_exponent hδ hlog (h ω) z q
    change ContinuousAt
      ((fun q => plZ q δ hδ) * (fun q => plMollify q δ hδ (h ω) z)) q
    exact hZ.mul hM
  have hRight : Continuous fun q : ℝ =>
      polarInt (plProf q) (fun r z => H r z ω) (δ, z) := by
    rw [continuous_iff_continuousAt]
    intro q
    exact continuousAt_plPolarInt_exponent hH ω z
      (δ := δ) (t := Real.log δ⁻¹) (A := A n) (C := |C|)
      hδ hlog rfl (hA n).le (abs_nonneg C) hbound q
  have hEqOn : EqOn
      (fun q : ℝ => plZ q δ hδ * plMollify q δ hδ (h ω) z)
      (fun q => polarInt (plProf q) (fun r z => H r z ω) (δ, z))
      (Set.range (fun q : ℚ => (q : ℝ))) := by
    rintro q ⟨qrat, rfl⟩
    have hq := hωFixed qrat δ hδ z
    calc plZ (qrat : ℝ) δ hδ * plMollify (qrat : ℝ) δ hδ (h ω) z
        = plZ (qrat : ℝ) δ hδ *
            ((plZ (qrat : ℝ) δ hδ)⁻¹ * h ω
              (plTest (qrat : ℝ) δ hδ z)) := by rw [plMollify]
      _ = h ω (plTest (qrat : ℝ) δ hδ z) := by
        rw [← mul_assoc, mul_inv_cancel₀ (plZ_pos (qrat : ℝ) δ hδ).ne', one_mul]
      _ = polarInt (plProf (qrat : ℝ)) (fun r z => H r z ω) (δ, z) := hq
  have hEq := Continuous.ext_on Rat.denseRange_cast hLeft hRight hEqOn
  intro q
  exact congrFun hEq q

end SupercriticalLFPPAS.Field
