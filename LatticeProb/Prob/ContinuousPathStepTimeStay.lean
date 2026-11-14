import LatticeProb.Prob.ContinuousPathStepTimeChain
import LatticeProb.Prob.ContinuousPathStepTimeStopped

/-!
# Displacement times of a stopped path: the stay form

Let `f g : ℝ≥0 → E` agree on `[0, T]`. The `K`-th displacement time of size `r` of a continuous path
that is attained at time `≤ T` is also the `K`-th displacement time of the other path
(`stepTime_eq_of_eqOn_of_le`): the displacement is witnessed at a time `≤ T`, where the paths agree
(`stepTime_le_of_eqOn_of_stepTime_eq` treats the borderline case `σ_K = T`).

This gives the stay form of the transfer through a stopped path
(`norm_lt_of_lt_stepTime_of_norm_sub_comp_stopped_le`): if `f` stays in the ball of radius `ρ` before
its `K`-th displacement time of size `s`, and `b`, stopped at a time `T` at which `‖b T‖ ≥ ρ + κ`,
is within `κ` of `f` modulo an increasing time change, then `b` stays in the ball of radius `ρ + κ`
before its `K`-th displacement time of size `r`, whenever `2 r + 2 κ ≤ s`.
-/

open Set
open scoped NNReal ENNReal

namespace LatticeProb

section StepTimeStay

variable {E : Type*} [NormedAddCommGroup E]

/-- **Borderline case of locality.** If `f = g` on `[0, T]`, `f` is continuous and its `K`-th
displacement time of size `r > 0` is exactly `T`, then the `K`-th displacement time of `g` is at most
`T`. -/
theorem stepTime_le_of_eqOn_of_stepTime_eq {f g : ℝ≥0 → E} {r : ℝ} {T : ℝ≥0}
    (hfg : ∀ t ≤ T, f t = g t) (hf : Continuous f) (hr : 0 < r) {K : ℕ}
    (hK : stepTime f r K = T) : stepTime g r K ≤ T := by
  cases K with
  | zero => simp
  | succ j =>
    have hlt : stepTime f r (j + 1) < ⊤ := by rw [hK]; exact ENNReal.coe_lt_top
    obtain ⟨a, t, ha, ht, hat, hrt, -⟩ := stepTime_succ_spec hf hr hlt
    have htT : t = T := ENNReal.coe_inj.1 (ht.symm.trans hK)
    rw [htT] at hat hrt
    have hloc := min_stepTime_eq_of_eqOn (r := r) hfg j
    rw [ha, min_eq_left (ENNReal.coe_le_coe.2 hat.le)] at hloc
    have hgj : stepTime g r j = a := by
      rcases le_total (stepTime g r j) (T : ℝ≥0∞) with h | h
      · rw [min_eq_left h] at hloc
        exact hloc.symm
      · rw [min_eq_right h] at hloc
        exact absurd (ENNReal.coe_inj.1 hloc) hat.ne
    have hne : stepTime g r j ≠ ⊤ := by rw [hgj]; exact ENNReal.coe_ne_top
    rw [stepTime_succ_of_ne_top hne, hgj, ENNReal.toNNReal_coe]
    refine nextStep_le_of_mem ⟨hat.le, ?_⟩
    rw [← hfg T le_rfl, ← hfg a hat.le]
    exact hrt

/-- **Locality of a displacement time attained before `T`.** If `f = g` on `[0, T]`, `f` is continuous
and its `K`-th displacement time of size `r > 0` is at most `T`, then `g` has the same `K`-th
displacement time. -/
theorem stepTime_eq_of_eqOn_of_le {f g : ℝ≥0 → E} {r : ℝ} {T : ℝ≥0}
    (hfg : ∀ t ≤ T, f t = g t) (hf : Continuous f) (hr : 0 < r) {K : ℕ}
    (hK : stepTime f r K ≤ T) : stepTime g r K = stepTime f r K := by
  have hloc := min_stepTime_eq_of_eqOn (r := r) hfg K
  rw [min_eq_left hK] at hloc
  by_cases h : stepTime g r K ≤ (T : ℝ≥0∞)
  · rw [min_eq_left h] at hloc
    exact hloc.symm
  · rw [not_le] at h
    rw [min_eq_right h.le] at hloc
    exact absurd (stepTime_le_of_eqOn_of_stepTime_eq hfg hf hr hloc) (not_le.2 h)

/-- **Stay form of the transfer through a stopped path.** Let `b` be continuous and `f` within `κ` of
`b` stopped at time `T`, modulo an increasing time change `φ`, with `‖b T‖ ≥ ρ + κ`. If `2 r + 2 κ ≤ s`
and `f` stays in the open ball of radius `ρ` about the origin before its `K`-th displacement time of
size `s`, then `b` stays in the open ball of radius `ρ + κ` about the origin before its `K`-th
displacement time of size `r > 0`. -/
theorem norm_lt_of_lt_stepTime_of_norm_sub_comp_stopped_le {f b : ℝ≥0 → E} (hb : Continuous b)
    {T : ℝ≥0} (φ : ℝ≥0 ≃o ℝ≥0) {s r κ ρ : ℝ} (hr0 : 0 < r)
    (hfb : ∀ t, ‖f t - b (min (φ t) T)‖ ≤ κ) (hr : 2 * r + 2 * κ ≤ s) {K : ℕ}
    (hf : ∀ t : ℝ≥0, (t : ℝ≥0∞) < stepTime f s K → ‖f t‖ < ρ) (hT : ρ + κ ≤ ‖b T‖) :
    ∀ u : ℝ≥0, (u : ℝ≥0∞) < stepTime b r K → ‖b u‖ < ρ + κ := by
  intro u hu
  obtain ⟨g, hg⟩ : ∃ g : ℝ≥0 → E, ∀ t, g t = b (min t T) :=
    ⟨fun t => b (min t T), fun _ => rfl⟩
  have hgc : Continuous g := by
    have : g = fun t => b (min t T) := funext hg
    rw [this]
    exact hb.comp (continuous_id.min continuous_const)
  have hstay := norm_lt_of_lt_stepTime_of_norm_sub_comp_le (g := g) φ
    (fun t => by rw [hg]; exact hfb t) hr hf
  have hbg : ∀ t ≤ T, b t = g t := fun t ht => by rw [hg, min_eq_left ht]
  have hloc := min_stepTime_eq_of_eqOn (r := r) hbg K
  by_cases hKT : stepTime b r K ≤ (T : ℝ≥0∞)
  · rw [min_eq_left hKT] at hloc
    have hle : stepTime b r K ≤ stepTime g r K := by
      rw [hloc]
      exact min_le_left _ _
    have huT : u ≤ T := by exact_mod_cast (hu.trans_le hKT).le
    have h1 := hstay u (hu.trans_le hle)
    rwa [hg, min_eq_left huT] at h1
  · exfalso
    rw [not_le] at hKT
    rw [min_eq_right hKT.le] at hloc
    have hTg : (T : ℝ≥0∞) ≤ stepTime g r K := by
      by_contra hcon
      rw [not_le] at hcon
      rw [min_eq_left hcon.le] at hloc
      exact hcon.ne hloc.symm
    have hTg' : stepTime g r K = T := by
      refine le_antisymm ?_ hTg
      by_contra hcon
      rw [not_le] at hcon
      have h1 := hstay T hcon
      rw [hg, min_self] at h1
      linarith
    have h2 := stepTime_le_of_eqOn_of_stepTime_eq (fun t ht => (hbg t ht).symm) hgc hr0 hTg'
    exact absurd hKT (not_lt.2 h2)

end StepTimeStay

end LatticeProb
