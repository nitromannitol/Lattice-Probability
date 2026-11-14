/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundWitness at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric

theorem laneC_exists_around_witness_of_lt
    (D : ContMetric) (A E F : Set ℂ) {M : ℝ≥0∞}
    (hM : D.aroundDist A E F < M) :
    ∃ a b : ℝ, ∃ P : ℝ → ℂ,
      a ≤ b ∧ ContinuousOn P (Icc a b) ∧
      P '' Icc a b ⊆ A ∧ Disconnects (P '' Icc a b) E F ∧
        D.len P a b < M := by
  unfold ContMetric.aroundDist at hM
  simp only [iInf_lt_iff] at hM
  obtain ⟨a, b, P, hab, hcont, hcar, hsep, hlen⟩ := hM
  exact ⟨a, b, P, hab, hcont, hcar, hsep, hlen⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
