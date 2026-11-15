import LatticeProb.Analysis.LocalMinCountable
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle

/-! # Grid phases avoiding coordinate local minima -/

set_option autoImplicit false

open Set Filter

namespace MatedCRTHarmonic.RouteM

/-- For each mesh, only countably many phases put a grid point at a local
minimum of either coordinate of a Peanosphere path. -/
theorem Peanosphere.countable_gridLocalMin_phases
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η) (ε : ℝ) :
    {c : ℝ | ∃ (i : Fin 2) (x : ℤ),
      IsLocalMin (MatedCRT.lrCoord i · ω) (c + ε * x)}.Countable := by
  have hcount : ∀ i : Fin 2, {t | IsLocalMin (MatedCRT.lrCoord i · ω) t}.Countable := by
    intro i
    exact LatticeProb.countable_localMin_of_distinct_values _ (P.locMinDistinct i)
  apply Set.Countable.mono _ (countable_iUnion fun i : Fin 2 =>
    countable_iUnion fun x : ℤ => (hcount i).image (fun t => t - ε * x))
  intro c hc
  obtain ⟨i, x, hx⟩ := hc
  apply mem_iUnion.mpr
  refine ⟨i, mem_iUnion.mpr ⟨x, ?_⟩⟩
  exact ⟨c + ε * x, hx, by ring⟩

end MatedCRTHarmonic.RouteM
