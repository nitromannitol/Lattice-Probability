/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Implementation.ExistsUnique_isLFPPNormalizer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPNormalizer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Normalizer.Median

 












set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Implementation

open SupercriticalLQGUniqueness.B2.Normalizer

 


theorem existsUnique_isLFPPNormalizer_impl :
    ∀ ξ ε : Set.Ioi (0 : ℝ), ∃! a : Set.Ioi (0 : ℝ), IsLFPPNormalizer ξ ε a := by
  intro ξ ε
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, h₀, hh₀⟩ := exists_normalizedGFF
  obtain ⟨X₀, -, hX₀⟩ := exists_heatVersion hh₀ (ε : ℝ) ε.2
  obtain ⟨a₀, ha₀, hmed₀⟩ := exists_pos_isMedian hh₀ (ξ : ℝ) ε ε.2 X₀ hX₀
  refine ⟨⟨a₀, ha₀⟩, ?_, ?_⟩
  · 
    intro Ω _ P _ h hh X hX
    exact (Exponent.HeatVersion.isMedian_crossing_iff_of_normalizedGFF hh₀ hh (ξ : ℝ) ε ε.2
      X₀ X hX₀ hX _).1 hmed₀
  · 
    intro b hb
    have hb₀ := hb P₀ h₀ hh₀ X₀ hX₀
    rcases lt_trichotomy (b : ℝ) a₀ with hlt | heq | hgt
    · exact (not_isMedian_ofReal_pair b.2.le hlt
        (measure_lfppCrossingLength_mem_Ioo_pos hh₀ ξ.2 ε.2 X₀ hX₀ b.2 hlt) hb₀ hmed₀).elim
    · exact Subtype.ext heq
    · exact (not_isMedian_ofReal_pair ha₀.le hgt
        (measure_lfppCrossingLength_mem_Ioo_pos hh₀ ξ.2 ε.2 X₀ hX₀ ha₀ hgt) hmed₀ hb₀).elim

end SupercriticalLQGUniqueness.Implementation
