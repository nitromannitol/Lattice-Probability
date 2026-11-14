/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianExcursionRange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuousExitProperties

/-! Deterministic links between elapsed time and the range of the actual
normalized Brownian excursion. -/

open Set
open scoped NNReal ENNReal unitInterval

namespace BouRabeeGwynne

lemma lt_continuousExitTime_of_mem_Icc {d : ℕ} {U : Set (Euc d)}
    (hU : IsOpen U) {x : Euc d} {ω : BrownianPath d} {T : ℝ≥0}
    (hinside : ∀ t ∈ Icc (0 : ℝ≥0) T, x + ω t ∈ U) :
    (T : ℝ≥0∞) < continuousExitTime U x ω := by
  by_contra h
  have hle := le_of_not_gt h
  have hfinite : continuousExitTime U x ω ≠ ∞ :=
    ne_of_lt (hle.trans_lt ENNReal.coe_lt_top)
  have ht : (continuousExitTime U x ω).toNNReal ≤ T := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_toNNReal hfinite] using hle
  exact continuousExitTime_not_mem hU hfinite (hinside _ ⟨bot_le, ht⟩)

lemma mem_range_stoppedBrownianRepresentative {d : ℕ} (U : Set (Euc d))
    (x : Euc d) (ω : BrownianPath d) {t : ℝ≥0}
    (ht : t ≤ (continuousExitTime U x ω).toNNReal) :
    x + ω t ∈ range (stoppedBrownianRepresentative U x ω) := by
  let τ : ℝ≥0 := (continuousExitTime U x ω).toNNReal
  by_cases hτ : τ = 0
  · have htzero : t = 0 := le_antisymm (ht.trans hτ.le) bot_le
    refine ⟨0, ?_⟩
    change x + ω ⟨(0 : ℝ) * ((continuousExitTime U x ω).toNNReal : ℝ), _⟩ = x + ω t
    rw [htzero]
    apply congrArg (fun s : ℝ≥0 => x + ω s)
    exact Subtype.ext (zero_mul _)
  · have hτpos : 0 < (τ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hτ)
    let u : unitInterval := ⟨(t : ℝ) / (τ : ℝ),
      div_nonneg t.property τ.property,
      (div_le_one hτpos).mpr (by exact_mod_cast ht)⟩
    refine ⟨u, ?_⟩
    change x + ω ⟨((t : ℝ) / (τ : ℝ)) * (τ : ℝ), _⟩ = x + ω t
    apply congrArg (fun s : ℝ≥0 => x + ω s)
    apply Subtype.ext
    exact div_mul_cancel₀ _ hτpos.ne'

lemma stoppedBrownianRepresentative_not_all_mem_of_visit {d : ℕ}
    {U K : Set (Euc d)} (hU : IsOpen U) {x : Euc d} {ω : BrownianPath d}
    {T : ℝ≥0} (hfinite : continuousExitTime U x ω ≠ ∞)
    (hinside : ∀ t ∈ Icc (0 : ℝ≥0) T, x + ω t ∈ U)
    (hvisit : x + ω T ∉ K) :
    ¬ ∀ u : unitInterval, stoppedBrownianRepresentative U x ω u ∈ K := by
  intro hstay
  have ht : T ≤ (continuousExitTime U x ω).toNNReal := by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal hfinite]
    exact (lt_continuousExitTime_of_mem_Icc hU hinside).le
  obtain ⟨u, hu⟩ := mem_range_stoppedBrownianRepresentative U x ω ht
  exact hvisit (hu ▸ hstay u)

end BouRabeeGwynne
