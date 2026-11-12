import Mathlib
import LatticeProb.Prob.UpcrossAttempt

/-!
# Renewal equation for the up-crossing piece at a lower level `-δ`

Fix `δ > 0` and `c > 0`.  An attempt starts at `0` and runs until the path exits `(-δ, c)`.  If it
exits at `c` the attempt succeeds.  If it exits at `-δ`, the attempt waits for the next return to
`0`, and then starts afresh.  Since the path stays below `c` throughout a failed attempt, the first
up-crossing piece to `c` of the path is the first up-crossing piece of the restarted path.  The
generic renewal-with-failure lemma therefore gives
`μ₀(success) · ∫ f(piece_c) dμ₀ = ∫_success f(piece_c) dμ₀`,
where success means that the path hits `c` before it hits `-δ`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section Stop

/-- If a time `t` is at least the minimum of two stopping functionals, whether the second is smaller
than the first is decided by the path stopped at `t`. -/
lemma IsStopFun.stopAt_lt_iff_of_min_le {Ψ₁ Ψ₂ : C(ℝ≥0, ℝ) → ℝ≥0∞} (h₁ : IsStopFun Ψ₁)
    (h₂ : IsStopFun Ψ₂) (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) (ht : Min.min (Ψ₁ w) (Ψ₂ w) ≤ t) :
    Ψ₂ (stopAt (t : ℝ≥0∞) w) < Ψ₁ (stopAt (t : ℝ≥0∞) w) ↔ Ψ₂ w < Ψ₁ w := by
  have key : ∀ {Φ : C(ℝ≥0, ℝ) → ℝ≥0∞}, IsStopFun Φ →
      (Φ w ≤ t → Φ (stopAt (t : ℝ≥0∞) w) = Φ w) ∧ (t < Φ w → t < Φ (stopAt (t : ℝ≥0∞) w)) :=
    fun {Φ} hΦ => ⟨(hΦ w t).1, fun h => by
      by_contra hcon
      exact absurd ((hΦ w t).2 (not_lt.1 hcon)) (not_le.2 h)⟩
  obtain ⟨f1, g1⟩ := key h₁
  obtain ⟨f2, g2⟩ := key h₂
  rcases le_or_gt (Ψ₁ w) t with l1 | l1 <;> rcases le_or_gt (Ψ₂ w) t with l2 | l2
  · rw [f1 l1, f2 l2]
  · have h2 := g2 l2
    rw [f1 l1]
    exact ⟨fun h => absurd h (not_lt.2 (l1.trans h2.le)),
      fun h => absurd h (not_lt.2 (l1.trans l2.le))⟩
  · have h1 := g1 l1
    rw [f2 l2]
    exact ⟨fun _ => l2.trans_lt l1, fun _ => l2.trans_lt h1⟩
  · exact absurd ht (not_le.2 (lt_min l1 l2))

end Stop

section Level

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The attempt succeeds: the path hits `c` before it hits `-δ`. -/
def levelSuccess (δ c : ℝ) : Set C(ℝ≥0, ℝ) :=
  {w | hitFrom c 0 (w : ℝ≥0 → ℝ) < hitFrom (-δ) 0 (w : ℝ≥0 → ℝ)}

/-- End of an attempt at the level `-δ`: the first hit of `c`, or, if the path first hits `-δ`,
the next return to `0`. -/
def levelAttemptEnd (δ c : ℝ) (w : C(ℝ≥0, ℝ)) : ℝ≥0∞ :=
  Min.min (hitFrom c 0 (w : ℝ≥0 → ℝ))
    (hitFrom 0 (hitFrom (-δ) 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ))

lemma measurableSet_levelSuccess (δ c : ℝ) : MeasurableSet (levelSuccess δ c) :=
  measurableSet_lt (measurable_hitFrom (r := fun _ => 0) measurable_const c)
    (measurable_hitFrom (r := fun _ => 0) measurable_const (-δ))

/-- **Renewal equation at a lower level.**  For Brownian motion with drift `mu > 0`, `δ > 0`,
`c > 0` and `f ≤ 1` a functional of the first up-crossing piece to `c`:
`μ₀(success) · ∫ f(piece_c) dμ₀ = ∫_success f(piece_c) dμ₀`, where success means that the path
hits `c` before it hits `-δ`. -/
theorem driftLaw_mul_lintegral_piece_eq_setLIntegral_level [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu) {δ c : ℝ} (hδ : 0 < δ)
    (hc : 0 < c) {f : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hf : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)))
    (hf1 : ∀ p, f p ≤ 1) :
    driftLaw P B hcont mu (levelSuccess δ c) *
        ∫⁻ w : C(ℝ≥0, ℝ), f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu)
      = ∫⁻ w in levelSuccess δ c, f (firstUpcrossPiece c (w : ℝ≥0 → ℝ))
          ∂(driftLaw P B hcont mu) := by
  have hAm : Measurable fun w : C(ℝ≥0, ℝ) => hitFrom c 0 (w : ℝ≥0 → ℝ) :=
    measurable_hitFrom (r := fun _ => 0) measurable_const c
  have hBm : Measurable fun w : C(ℝ≥0, ℝ) => hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) :=
    measurable_hitFrom (r := fun _ => 0) measurable_const (-δ)
  have hNm : Measurable fun w : C(ℝ≥0, ℝ) =>
      hitFrom 0 (hitFrom (-δ) 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) := measurable_hitFrom hBm 0
  have hA : IsStopFun fun w : C(ℝ≥0, ℝ) => hitFrom c 0 (w : ℝ≥0 → ℝ) := isStopFun_hitFrom_zero c
  have hBs : IsStopFun fun w : C(ℝ≥0, ℝ) => hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) :=
    isStopFun_hitFrom_zero (-δ)
  have hNs : IsStopFun fun w : C(ℝ≥0, ℝ) =>
      hitFrom 0 (hitFrom (-δ) 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) := hBs.hitFrom 0
  refine driftLaw_mul_lintegral_eq_setLIntegral hB hm hcont mu (ρ := levelAttemptEnd δ c)
    (hAm.min hNm) (hA.min hNs) ?_ (measurableSet_levelSuccess δ c) ?_ hf (fun w => hf1 _) ?_
  · filter_upwards [ae_start_hitFrom_driftLaw hB hm hcont hmu hc.le] with w ⟨_, hfin⟩
    exact ne_top_of_le_ne_top hfin (min_le_left _ _)
  · intro w hw
    obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ≥0∞) = levelAttemptEnd δ c w :=
      ⟨_, ENNReal.coe_toNNReal hw⟩
    rw [← ht]
    refine hBs.stopAt_lt_iff_of_min_le hA w t ?_
    rw [ht]
    exact le_min (min_le_right _ _) ((min_le_left _ _).trans le_hitFrom)
  · intro w hw0 hρ hnS
    have hle : hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) ≤ hitFrom c 0 (w : ℝ≥0 → ℝ) := not_lt.1 hnS
    have hBfin : hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) ≠ ⊤ := by
      intro hBt
      apply hρ
      have hAt : hitFrom c 0 (w : ℝ≥0 → ℝ) = ⊤ := top_le_iff.1 (hBt ▸ hle)
      simp [levelAttemptEnd, hBt, hAt, hitFrom_top]
    obtain ⟨b, hb, -, hwb, -⟩ := exists_hitFrom_eq w.continuous hBfin
    have hNle : hitFrom 0 (hitFrom (-δ) 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) ≤
        hitFrom c 0 (w : ℝ≥0 → ℝ) := by
      by_cases hAt : hitFrom c 0 (w : ℝ≥0 → ℝ) = ⊤
      · rw [hAt]; exact le_top
      obtain ⟨a, ha, -, hwa, -⟩ := exists_hitFrom_eq w.continuous hAt
      have hba : b ≤ a := by
        have := hle
        rw [hb, ha] at this
        exact_mod_cast this
      obtain ⟨s, hs, hws⟩ : ∃ s ∈ Set.Icc b a, w s = 0 :=
        intermediate_value_Icc hba w.continuous.continuousOn
          ⟨by rw [hwb]; linarith, by rw [hwa]; exact hc.le⟩
      calc hitFrom 0 (hitFrom (-δ) 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) ≤ s :=
            hitFrom_le (by rw [hb]; exact_mod_cast hs.1) hws
        _ ≤ hitFrom c 0 (w : ℝ≥0 → ℝ) := by rw [ha]; exact_mod_cast hs.2
    have hρN : levelAttemptEnd δ c w =
        hitFrom 0 (hitFrom (-δ) 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) := min_eq_right hNle
    have hfin : hitFrom 0 (hitFrom (-δ) 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) ≠ ⊤ := hρN ▸ hρ
    obtain ⟨T, hT, -, hwT, -⟩ := exists_hitFrom_eq w.continuous hfin
    have hlt : ∀ s : ℝ≥0, s ≤ T → w s < c := by
      refine forall_lt_of_forall_ne w.continuous (by rw [hw0]; exact hc) fun s hs hwsc => ?_
      have h1 : hitFrom c 0 (w : ℝ≥0 → ℝ) ≤ s := hitFrom_le zero_le hwsc
      have h2 : (T : ℝ≥0∞) ≤ hitFrom c 0 (w : ℝ≥0 → ℝ) := hT ▸ hNle
      have hsT : s = T := le_antisymm hs (by exact_mod_cast h2.trans h1)
      rw [hsT, hwT] at hwsc
      exact hc.ne hwsc
    show f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) = f (firstUpcrossPiece c
      (shiftPath (levelAttemptEnd δ c w).toNNReal w : ℝ≥0 → ℝ))
    rw [hρN, hT, ENNReal.toNNReal_coe]
    exact congrArg f (firstUpcrossPiece_eq_shift_of_zero w.continuous hc hw0 hwT hlt)

end Level

end LatticeProb
