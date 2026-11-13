/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.Uniqueness at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.NV1Evidence
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffSq




 





set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent

open LQGMetric (DistC)

private theorem no_exponent_lt_of_common_bounds
    (ξ : Set.Ioi (0 : ℝ)) (Q Q' : ℝ) (m : ℝ → ℝ≥0∞)
    (hQ : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q + δ)) ≤ m ε ∧
        m ε ≤ ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q - δ)))
    (hQ' : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q' + δ)) ≤ m ε ∧
        m ε ≤ ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q' - δ))) :
    ¬ Q < Q' := by
  intro hlt
  let δ : ℝ := (ξ : ℝ) * (Q' - Q) / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (mul_pos ξ.property (sub_pos.mpr hlt)) (by norm_num)
  have hpow : 1 - (ξ : ℝ) * Q' + δ < 1 - (ξ : ℝ) * Q - δ := by
    have hmul : 0 < (ξ : ℝ) * (Q' - Q) := mul_pos ξ.property (sub_pos.mpr hlt)
    dsimp [δ]
    nlinarith only [hmul]
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q' + δ)) ≤ m ε ∧
      m ε ≤ ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q - δ)) ∧
      0 < ε ∧ ε < 1 := by
    filter_upwards [hQ δ hδ, hQ' δ hδ,
      self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0),
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with ε h₁ h₂ hε hε1
    exact ⟨h₂.1, h₁.2, hε, hε1⟩
  obtain ⟨ε, hlow, hup, hε, hε1⟩ := hevent.exists
  have hstrict : ε ^ (1 - (ξ : ℝ) * Q - δ) < ε ^ (1 - (ξ : ℝ) * Q' + δ) :=
    Real.rpow_lt_rpow_of_exponent_gt hε hε1 hpow
  have hstrict' : ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q - δ)) <
      ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q' + δ)) :=
    (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hε _)).2 hstrict
  exact (not_le_of_gt hstrict') (hlow.trans hup)

 
theorem isLFPPExponent_unique :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q Q' : ℝ,
      IsLFPPExponent ξ Q → IsLFPPExponent ξ Q' → Q = Q' := by
  intro ξ Q Q' hQ hQ'
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := exists_normalizedGFF
  let : MeasurableSpace Ω := mΩ
  have : IsProbabilityMeasure P := hP
  obtain ⟨X, m, hXm⟩ := exists_exponent_witness_family P h hh ξ
  have h₁ := hQ P h hh X m hXm
  have h₂ := hQ' P h hh X m hXm
  exact le_antisymm
    (le_of_not_gt (no_exponent_lt_of_common_bounds ξ Q' Q m h₂ h₁))
    (le_of_not_gt (no_exponent_lt_of_common_bounds ξ Q Q' m h₁ h₂))

 

end SupercriticalLQGUniqueness.Exponent
