/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianSkeletonTail at commit fdb5cad; the module paths of local imports and lint-related details are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianUniformModulus
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteExit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Uniform bounds on Brownian ball-skeleton counts

The event below contains every construction of a monotone exit skeleton whose
successive displacements have size at least `ε`. Its measure is bounded using
the actual Brownian exit-time tail and the common path modulus. No choice of
ball centers or coupling is assumed, and no measurability of an uncountable
existential event is needed for this outer-measure bound.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace BouRabeeGwynne

lemma pathModulusEvent_forces_short_step {d : ℕ} {ω : BrownianPath d}
    {T : ℝ≥0} {ε : ℝ} (hε : 0 < ε) {m K : ℕ}
    (hmod : ω ∈ pathModulusEvent T (ε / 2) m)
    (hK : (T : ℝ) < (K : ℝ) * (1 / (m + 1 : ℝ)))
    {τ : ℕ → ℝ≥0} (hmono : Monotone τ) (hτT : τ K ≤ T) :
    ∃ k < K, dist (ω (τ k)) (ω (τ (k + 1))) < ε := by
  by_contra hsep
  push Not at hsep
  have hgap (k : ℕ) (hk : k < K) :
      1 / (m + 1 : ℝ) ≤ (τ (k + 1) : ℝ) - (τ k : ℝ) := by
    by_contra hsmall
    have hstep : (τ k : ℝ) ≤ (τ (k + 1) : ℝ) := by
      exact_mod_cast hmono (Nat.le_succ k)
    have htime : dist (τ k) (τ (k + 1)) ≤ 1 / (m + 1 : ℝ) := by
      rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr hstep)]
      linarith
    have hkT : τ k ≤ T := (hmono (Nat.le_of_lt hk)).trans hτT
    have hsuccT : τ (k + 1) ≤ T := (hmono (Nat.succ_le_of_lt hk)).trans hτT
    have hbound := hmod (τ k) ⟨bot_le, hkT⟩ (τ (k + 1)) ⟨bot_le, hsuccT⟩ htime
    have hlower := hsep k hk
    linarith
  have hprogress : ∀ k : ℕ, k ≤ K →
      (k : ℝ) * (1 / (m + 1 : ℝ)) ≤ (τ k : ℝ) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hp := ih (Nat.le_of_succ_le hk)
      have hg := hgap k (Nat.lt_of_succ_le hk)
      push_cast
      linarith
  have hsmall := hprogress K le_rfl
  have hτT' : (τ K : ℝ) ≤ T := by exact_mod_cast hτT
  linarith

/-- All paths admitting at least `K` successive `ε`-moves before their actual
exit. This event is defined directly on the canonical continuous-path space. -/
def ballSkeletonCountEvent {d : ℕ} (U : Set (Euc d)) (z : Euc d)
    (ε : ℝ) (K : ℕ) : Set (BrownianPath d) :=
  {ω | ∃ τ : ℕ → ℝ≥0, Monotone τ ∧
    (τ K : ℝ≥0∞) ≤ continuousExitTime U z ω ∧
    ∀ k < K, ε ≤ dist (ω (τ k)) (ω (τ (k + 1)))}

lemma ballSkeletonCountEvent_subset {d : ℕ} (U : Set (Euc d)) (z : Euc d)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (m K : ℕ)
    (hK : (T : ℝ) < (K : ℝ) * (1 / (m + 1 : ℝ))) :
    ballSkeletonCountEvent U z ε K ⊆
      {ω | (T : ℝ≥0∞) < continuousExitTime U z ω} ∪
        (pathModulusEvent T (ε / 2) m)ᶜ := by
  rintro ω ⟨τ, hmono, htime, hlarge⟩
  by_cases hlate : (T : ℝ≥0∞) < continuousExitTime U z ω
  · exact Or.inl hlate
  · right
    intro hmod
    have hτT : τ K ≤ T := ENNReal.coe_le_coe.mp
      (htime.trans (le_of_not_gt hlate))
    obtain ⟨k, hk, hshort⟩ := pathModulusEvent_forces_short_step hε hmod hK hmono hτT
    exact (not_lt_of_ge (hlarge k hk)) hshort

/-- The skeleton-count tail is uniformly small over every starting point in a
bounded domain. The estimate is valid for the actual standard Brownian law,
and thus for every measurable ball-exit skeleton contained in this event. -/
theorem standardBrownianLaw_uniform_skeletonTail {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ z ∈ U, μ (ballSkeletonCountEvent U z ε K) ≤ ENNReal.ofReal η := by
  let : IsProbabilityMeasure μ := hμ.1
  have hhalf : 0 < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨n, hn⟩ := (standardBrownianLaw_uniform_exitTail hd hμ hU hhalf).exists
  let T : ℝ≥0 := ((n : ℝ≥0) + 1) ^ 2
  have hmodlim := measure_compl_pathModulusEvent_tendsto_zero μ T
    (show 0 < ε / 2 by positivity)
  obtain ⟨m, hm⟩ := (hmodlim.eventually (gt_mem_nhds hhalf)).exists
  obtain ⟨K, hK⟩ := exists_nat_gt ((T : ℝ) / (1 / (m + 1 : ℝ)))
  have hK' : (T : ℝ) < (K : ℝ) * (1 / (m + 1 : ℝ)) :=
    (div_lt_iff₀ (by positivity : 0 < 1 / (m + 1 : ℝ))).mp hK
  refine ⟨K, fun z hz ↦ ?_⟩
  calc
    μ (ballSkeletonCountEvent U z ε K) ≤
        μ ({ω | (T : ℝ≥0∞) < continuousExitTime U z ω} ∪
          (pathModulusEvent T (ε / 2) m)ᶜ) :=
      measure_mono (ballSkeletonCountEvent_subset U z hε T m K hK')
    _ ≤ μ {ω | (T : ℝ≥0∞) < continuousExitTime U z ω} +
        μ (pathModulusEvent T (ε / 2) m)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
      add_le_add (hn z hz) hm.le
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end BouRabeeGwynne
