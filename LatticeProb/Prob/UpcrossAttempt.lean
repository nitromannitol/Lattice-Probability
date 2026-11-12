import Mathlib
import LatticeProb.Prob.PathRenewalFailure
import LatticeProb.Prob.UpcrossSplit
import LatticeProb.Prob.BrownianDriftHitFinite

/-!
# The renewal equation for the final up-crossing piece

Let `μ₀` be the law of Brownian motion with drift `mu > 0` on path space, `0 < c' < c`, and `F` a
functional of the first up-crossing piece to the level `c`.  An *attempt* runs the path to the first
hit `τ` of `c'`, and then to the first exit `ρ` of `(0, c)` after `τ`.  It succeeds if the exit is
at `c`.  After a failed attempt the path is at `0` and the first up-crossing piece is that of the
restarted path, so the generic renewal-with-failure lemma gives
`μ₀(success) · ∫ F dμ₀ = ∫_success F dμ₀`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section Stop

/-- Order-theoretic fact about the minimum of two stopping functionals: whether the second is
smaller than the first is decided by the path stopped at the minimum. -/
lemma IsStopFun.stopAt_min_lt_iff {Ψ₁ Ψ₂ : C(ℝ≥0, ℝ) → ℝ≥0∞} (h₁ : IsStopFun Ψ₁)
    (h₂ : IsStopFun Ψ₂) (w : C(ℝ≥0, ℝ)) (hw : Min.min (Ψ₁ w) (Ψ₂ w) ≠ ⊤) :
    Ψ₂ (stopAt (Min.min (Ψ₁ w) (Ψ₂ w)) w) < Ψ₁ (stopAt (Min.min (Ψ₁ w) (Ψ₂ w)) w) ↔
      Ψ₂ w < Ψ₁ w := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ≥0∞) = Min.min (Ψ₁ w) (Ψ₂ w) := ⟨_, ENNReal.coe_toNNReal hw⟩
  rw [← ht]
  have key : ∀ {Φ : C(ℝ≥0, ℝ) → ℝ≥0∞}, IsStopFun Φ →
      (Φ w ≤ t → Φ (stopAt (t : ℝ≥0∞) w) = Φ w) ∧ (t < Φ w → t < Φ (stopAt (t : ℝ≥0∞) w)) :=
    fun {Φ} hΦ => ⟨(hΦ w t).1, fun h => by
      by_contra hcon
      exact absurd ((hΦ w t).2 (not_lt.1 hcon)) (not_le.2 h)⟩
  obtain ⟨f1, g1⟩ := key h₁
  obtain ⟨f2, g2⟩ := key h₂
  have ht1 : (t : ℝ≥0∞) ≤ Ψ₁ w := by rw [ht]; exact min_le_left _ _
  have ht2 : (t : ℝ≥0∞) ≤ Ψ₂ w := by rw [ht]; exact min_le_right _ _
  rcases eq_or_lt_of_le ht1 with e1 | l1 <;> rcases eq_or_lt_of_le ht2 with e2 | l2
  · rw [f1 e1.ge, f2 e2.ge, ← e1, ← e2]
  · have := g2 l2
    rw [f1 e1.ge]
    have hA : ¬ Ψ₂ (stopAt (t : ℝ≥0∞) w) < Ψ₁ w := not_lt.2 (by rw [← e1]; exact this.le)
    have hB : ¬ Ψ₂ w < Ψ₁ w := not_lt.2 (by rw [← e1]; exact l2.le)
    exact ⟨fun h => absurd h hA, fun h => absurd h hB⟩
  · have := g1 l1
    rw [f2 e2.ge, ← e2]
    exact ⟨fun _ => l1, fun _ => this⟩
  · exfalso
    have : (t : ℝ≥0∞) < Min.min (Ψ₁ w) (Ψ₂ w) := lt_min l1 l2
    rw [ht] at this
    exact lt_irrefl _ this

end Stop

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Almost-sure statements for the drifted path law can be checked on the sample space. -/
lemma ae_driftLaw_iff (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (mu : ℝ) {p : C(ℝ≥0, ℝ) → Prop} (hp : MeasurableSet {w | p w}) :
    (∀ᵐ w : C(ℝ≥0, ℝ) ∂(driftLaw P B hcont mu), p w) ↔
      ∀ᵐ ω ∂P, p (driftMap mu (pathMap B hcont ω)) := by
  have hp' : MeasurableSet {x : C(ℝ≥0, ℝ) | p (driftMap mu x)} := (measurable_driftMap mu) hp
  rw [driftLaw, ae_map_iff (measurable_driftMap mu).aemeasurable hp,
    ae_map_iff (measurable_pathMap B hm hcont).aemeasurable hp']

/-- Under Brownian motion with positive drift, the path starts at `0` and hits every level
`c ≥ 0` almost surely. -/
lemma ae_start_hitFrom_driftLaw [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ}
    (hmu : 0 < mu) {c : ℝ} (hc : 0 ≤ c) :
    ∀ᵐ w : C(ℝ≥0, ℝ) ∂(driftLaw P B hcont mu), w 0 = 0 ∧ hitFrom c 0 (w : ℝ≥0 → ℝ) ≠ ⊤ := by
  have hp : MeasurableSet {w : C(ℝ≥0, ℝ) | w 0 = 0 ∧ hitFrom c 0 (w : ℝ≥0 → ℝ) ≠ ⊤} :=
    (measurableSet_eq_fun (continuous_eval_const 0).measurable measurable_const).inter
      ((measurable_hitFrom (r := fun _ => 0) measurable_const c) (measurableSet_singleton ⊤).compl)
  refine (ae_driftLaw_iff hm hcont mu hp).2 ?_
  filter_upwards [ae_hitFrom_ne_top_brownian_drift hB hmu hc,
    hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω h h0
  exact ⟨by simp [driftMap_apply, pathMap_apply, show B 0 ω = 0 from h0], h⟩

end Law

section Attempt

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A continuous path from `0` which is at the level `c > c'` at time `s` has hit `c'` by `s`. -/
lemma hitFrom_mid_le {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {c' c : ℝ} (hc' : 0 < c')
    (hcc : c' < c) {s : ℝ≥0} (hws : w s = c) : hitFrom c' 0 w ≤ s := by
  obtain ⟨s', hs'mem, hws'⟩ : ∃ s' ∈ Set.Icc (0 : ℝ≥0) s, w s' = c' :=
    intermediate_value_Icc zero_le hw.continuousOn
      ⟨by rw [hw0]; exact hc'.le, by rw [hws]; exact hcc.le⟩
  exact (hitFrom_le (r := 0) zero_le hws').trans (by exact_mod_cast hs'mem.2)

/-- The attempt succeeds: after the first hit of `c'`, the path hits `c` before it hits `0`. -/
def attemptSuccess (c' c : ℝ) : Set C(ℝ≥0, ℝ) :=
  {w | hitFrom c (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) <
    hitFrom 0 (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ)}

/-- **Renewal equation for the final up-crossing piece.**  For Brownian motion with drift
`mu > 0`, levels `0 < c' < c` and `f ≤ 1` a functional of the first up-crossing piece to `c`:
`μ₀(success) · ∫ f(piece_c) dμ₀ = ∫_success f(piece_c) dμ₀`, where success means that after the
first hit of `c'` the path hits `c` before `0`. -/
theorem driftLaw_mul_lintegral_piece_eq_setLIntegral [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu) {c' c : ℝ} (hc' : 0 < c')
    (hcc : c' < c) {f : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hf : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)))
    (hf1 : ∀ p, f p ≤ 1) :
    driftLaw P B hcont mu (attemptSuccess c' c) *
        ∫⁻ w : C(ℝ≥0, ℝ), f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu)
      = ∫⁻ w in attemptSuccess c' c, f (firstUpcrossPiece c (w : ℝ≥0 → ℝ))
          ∂(driftLaw P B hcont mu) := by
  have hc : 0 < c := hc'.trans hcc
  have hτm : Measurable fun w : C(ℝ≥0, ℝ) => hitFrom c' 0 (w : ℝ≥0 → ℝ) :=
    measurable_hitFrom (r := fun _ => 0) measurable_const c'
  have hτ : IsStopFun fun w : C(ℝ≥0, ℝ) => hitFrom c' 0 (w : ℝ≥0 → ℝ) := isStopFun_hitFrom_zero c'
  have h0 : IsStopFun fun w : C(ℝ≥0, ℝ) => hitFrom 0 (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) :=
    hτ.hitFrom 0
  have hcs : IsStopFun fun w : C(ℝ≥0, ℝ) => hitFrom c (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) :=
    hτ.hitFrom c
  refine driftLaw_mul_lintegral_eq_setLIntegral hB hm hcont mu
    (ρ := fun w : C(ℝ≥0, ℝ) => exitFrom 0 c (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ))
    (measurable_exitFrom hτm 0 c) (isStopFun_exitFrom hτ 0 c) ?_
    (measurableSet_lt (measurable_hitFrom hτm c) (measurable_hitFrom hτm 0)) ?_ hf
    (fun w => hf1 _) ?_
  · filter_upwards [ae_start_hitFrom_driftLaw hB hm hcont hmu hc.le] with w ⟨hw0, hfin⟩
    have : hitFrom c (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) ≤ hitFrom c 0 (w : ℝ≥0 → ℝ) :=
      le_iInf₂ fun s hs => hitFrom_le (hitFrom_mid_le w.continuous hw0 hc' hcc hs.2) hs.2
    exact ne_top_of_le_ne_top hfin ((min_le_right _ _).trans this)
  · intro w hw
    exact (h0.stopAt_min_lt_iff hcs w hw).symm.symm
  · intro w hw0 hρ hnS
    have hle : hitFrom 0 (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) ≤
        hitFrom c (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) := not_lt.1 hnS
    have hρeq : exitFrom 0 c (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) =
        hitFrom 0 (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) := min_eq_left hle
    have hfin : hitFrom 0 (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) ≠ ⊤ := hρeq ▸ hρ
    show f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) = f (firstUpcrossPiece c
      (shiftPath (exitFrom 0 c (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ)).toNNReal w : ℝ≥0 → ℝ))
    rw [hρeq]
    exact congrArg f (firstUpcrossPiece_eq_shift_of_fail w.continuous hw0 hc' hcc hle hfin)

end Attempt

end LatticeProb
