/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicBoxCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicLowBandBoxAbs

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem dg20_non_dyadic_compare_on_box
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (U : Set ℂ) (x₀ : ℂ) (b : ℝ) (hb : 0 < b)
    (hU : U ⊆ ferniqueBox x₀ b)
    (n : ℕ) (s u : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (hu : 0 ≤ u) :
    let r : ℝ := (2 : ℝ) ^ s
    let W' := dg20ScaledNoise r (by positivity : 0 < r) W
    P.real {ω | ∃ z ∈ U,
      ferniqueCF * Real.sqrt ((8 * b) * b) + u <
        |phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 z ω -
          phiMN W P 0 n ((r : ℂ) * z) ω|} ≤
      2 * Real.exp (-u ^ 2 / 2) := by
  dsimp only
  let r : ℝ := (2 : ℝ) ^ s
  have hr : 0 < r := by dsimp [r]; positivity
  let W' := dg20ScaledNoise r hr W
  obtain ⟨hW', hdiff⟩ := dg20_non_dyadic_field_difference_coupled P W hW n s hs.le
  letI := hW'.isProbabilityMeasure
  have hone : (2 : ℝ) ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : -s ≤ 0)
  have hlow := isPhiVersion_phiVer (b := 1) hW'
    (by positivity : 0 < (2 : ℝ) ^ (-s)) hone
  have hevent :
      {ω | ∃ z ∈ U,
        ferniqueCF * Real.sqrt ((8 * b) * b) + u <
          |phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 z ω -
            phiMN W P 0 n ((r : ℂ) * z) ω|} =ᵐ[P]
      {ω | ∃ z ∈ U,
        ferniqueCF * Real.sqrt ((8 * b) * b) + u <
          |phiVer W' P ((2 : ℝ) ^ (-s)) 1 z ω|} := by
    filter_upwards [hdiff] with ω hω
    apply propext
    constructor
    · rintro ⟨z, hz, hbad⟩
      refine ⟨z, hz, ?_⟩
      rwa [hω z] at hbad
    · rintro ⟨z, hz, hbad⟩
      refine ⟨z, hz, ?_⟩
      rwa [hω z]
  have hreal : P.real {ω | ∃ z ∈ U,
        ferniqueCF * Real.sqrt ((8 * b) * b) + u <
          |phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 z ω -
            phiMN W P 0 n ((r : ℂ) * z) ω|} =
      P.real {ω | ∃ z ∈ U,
        ferniqueCF * Real.sqrt ((8 * b) * b) + u <
          |phiVer W' P ((2 : ℝ) ^ (-s)) 1 z ω|} := by
    simpa only [Measure.real] using congrArg ENNReal.toReal (measure_congr hevent)
  have hsubevent :
      {ω | ∃ z ∈ U,
        ferniqueCF * Real.sqrt ((8 * b) * b) + u <
          |phiVer W' P ((2 : ℝ) ^ (-s)) 1 z ω|} ⊆
      {ω | ferniqueCF * Real.sqrt ((8 * b) * b) + u ≤
        ⨆ v : ferniqueBox x₀ b,
          |phiVer W' P ((2 : ℝ) ^ (-s)) 1 v ω|} := by
    rintro ω ⟨z, hz, hbad⟩
    exact hbad.le.trans (le_ciSup
      (bddAbove_abs_of_compact (isCompact_ferniqueBox x₀ b) (hlow.cont ω))
      ⟨z, hU hz⟩)
  have hhalf : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-s) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (-1 : ℝ) ≤ -s by linarith)
    norm_num at h ⊢
    exact h
  rw [hreal]
  exact (measureReal_mono hsubevent (measure_ne_top P _)).trans
    (dg20_low_band_box_abs_tail P W' hW' x₀ b hb _ hhalf hone u hu)

end SupercriticalLQGUniqueness.B2.DG20Pt
