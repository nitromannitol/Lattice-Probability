import Mathlib
import LatticeProb.Prob.UpcrossRenewal

/-!
# Renewal at the end of the first up-crossing interval

Let `X` be an adapted process with continuous paths whose increments are those of a Brownian
motion `B` plus the drift `mu`, and let `μ₀` be the law of the Brownian path with drift `mu`
(started at `0`) on `C(ℝ≥0, ℝ)`.  The strong Markov property on path space at a stopping time `τ`
that is a measurable functional of the path gives, for functionals `A` of the path up to `τ` and
`R` of the path after `τ`,
`E[A(X) R(X after τ)] = E[A(X)] · ∫ R dμ₀`.

* `LatticeProb.lintegral_mul_shift_restart`: the general statement;
* `LatticeProb.lintegral_expNeg_piece_upcrossEnd₂_restart`: for `q, c ∈ ℝ` and a measurable
  functional `f` of the first up-crossing piece,
  `E[e^{-q d₂} f(piece)] = E[e^{-q d₁} f(piece)] · ∫ e^{-q (return time)} dμ₀`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Restart at a path stopping time, product form.**  For a measurable functional `τ'` of the
path of `X` which is a stopping time, `A` a measurable functional unchanged by stopping at `τ'`
and vanishing on `{τ' = ⊤}`, and `R` measurable:
`E[A(X) R(X after τ')] = E[A(X)] · ∫ R dμ₀`. -/
theorem lintegral_mul_shift_restart [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {X : ℝ≥0 → Ω → ℝ}
    (hXad : StronglyAdapted (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm)) X)
    (hXc : ∀ ω, Continuous fun t => X t ω) {mu : ℝ}
    (hXinc : ∀ ω t s, X (t + s) ω - X t ω = (B (t + s) ω - B t ω) + mu * s)
    {τ' : C(ℝ≥0, ℝ) → ℝ≥0∞} (hτ'm : Measurable τ')
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => τ' (pathMap X hXc ω))
    {A R : C(ℝ≥0, ℝ) → ℝ≥0∞} (hA : Measurable A) (hR : Measurable R)
    (hAstop : ∀ w : C(ℝ≥0, ℝ), τ' w ≠ ⊤ → A (stopAt (τ' w) w) = A w)
    (hAtop : ∀ w : C(ℝ≥0, ℝ), τ' w = ⊤ → A w = 0) :
    ∫⁻ ω, A (pathMap X hXc ω) *
        R (shiftPath (τ' (pathMap X hXc ω)).toNNReal (pathMap X hXc ω)) ∂P
      = (∫⁻ ω, A (pathMap X hXc ω) ∂P) *
        ∫⁻ v, R v ∂((P.map (pathMap B hcont)).map (driftMap mu)) := by
  have hXm : ∀ t, Measurable (X t) := fun t =>
    (hXad t).measurable.mono ((natFiltration (liftOne B) (stronglyMeasurable_liftOne hm)).le t) le_rfl
  have hpm : Measurable (pathMap X hXc) := measurable_pathMap X hXm hXc
  have hτm : Measurable fun ω => τ' (pathMap X hXc ω) := hτ'm.comp hpm
  have hmeas : MeasurableSet {ω | τ' (pathMap X hXc ω) < ⊤} := measurableSet_lt hτm measurable_const
  have hApm : Measurable fun ω => A (pathMap X hXc ω) := hA.comp hpm
  have hΦ : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => A p.1 * R p.2 :=
    (hA.comp measurable_fst).mul (hR.comp measurable_snd)
  have hsupp : Function.support (fun ω => A (pathMap X hXc ω) *
      R (shiftPath (τ' (pathMap X hXc ω)).toNNReal (pathMap X hXc ω))) ⊆
      {ω | τ' (pathMap X hXc ω) < ⊤} := by
    intro ω hω
    by_contra hne
    have h1 : τ' (pathMap X hXc ω) = ⊤ := by simpa using hne
    apply hω
    show A (pathMap X hXc ω) * _ = 0
    rw [hAtop _ h1, zero_mul]
  have hsupp' : Function.support (fun ω => A (pathMap X hXc ω)) ⊆
      {ω | τ' (pathMap X hXc ω) < ⊤} := by
    intro ω hω
    by_contra hne
    have h1 : τ' (pathMap X hXc ω) = ⊤ := by simpa using hne
    exact hω (hAtop _ h1)
  have key := lintegral_restart_path hB hm hcont hXad hXc hXinc hτ hΦ
  rw [← setLIntegral_eq_of_support_subset hsupp, ← setLIntegral_eq_of_support_subset hsupp',
    ← lintegral_mul_const _ hApm]
  refine (setLIntegral_congr_fun hmeas fun ω hω => ?_).trans
    (key.trans (setLIntegral_congr_fun hmeas fun ω hω => ?_))
  · show A (pathMap X hXc ω) * _ = A (stopAt (τ' (pathMap X hXc ω)) (pathMap X hXc ω)) * _
    rw [hAstop _ hω.ne]
  · show ∫⁻ w, A (stopAt (τ' (pathMap X hXc ω)) (pathMap X hXc ω)) * R w
        ∂((P.map (pathMap B hcont)).map (driftMap mu)) = _
    rw [lintegral_const_mul _ hR, hAstop _ hω.ne]

/-- **Renewal at the end of the first up-crossing interval.**  For `X` adapted with continuous paths
and increments those of `B` plus the drift `mu`, `c, q ∈ ℝ` and `f` a measurable functional of the
first up-crossing piece,
`E[e^{-q d₂} f(piece)] = E[e^{-q d₁} f(piece)] · ∫ e^{-q (return time)} dμ₀`. -/
theorem lintegral_expNeg_piece_upcrossEnd₂_restart [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {X : ℝ≥0 → Ω → ℝ}
    (hXad : StronglyAdapted (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm)) X)
    (hXc : ∀ ω, Continuous fun t => X t ω) {mu : ℝ}
    (hXinc : ∀ ω t s, X (t + s) ω - X t ω = (B (t + s) ω - B t ω) + mu * s)
    (c q : ℝ) {f : (ℝ≥0 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, expNeg q (upcrossEnd₂ c (fun t => X t ω)) * f (firstUpcrossPiece c (fun t => X t ω)) ∂P
      = (∫⁻ ω, expNeg q (upcrossEnd₁ c (fun t => X t ω)) *
          f (firstUpcrossPiece c (fun t => X t ω)) ∂P) *
        ∫⁻ v : C(ℝ≥0, ℝ), expNeg q (upcrossReturn c (v : ℝ≥0 → ℝ))
          ∂((P.map (pathMap B hcont)).map (driftMap mu)) := by
  have hA : Measurable fun s : C(ℝ≥0, ℝ) =>
      expNeg q (upcrossEnd₁ c (s : ℝ≥0 → ℝ)) * f (firstUpcrossPiece c (s : ℝ≥0 → ℝ)) :=
    ((measurable_expNeg q).comp (measurable_upcrossEnd₁ c)).mul
      (hf.comp (measurable_firstUpcrossPiece c))
  have hR : Measurable fun v : C(ℝ≥0, ℝ) => expNeg q (upcrossReturn c (v : ℝ≥0 → ℝ)) :=
    (measurable_expNeg q).comp (measurable_upcrossReturn c)
  have hstep : ∀ w : C(ℝ≥0, ℝ),
      expNeg q (upcrossEnd₂ c (w : ℝ≥0 → ℝ)) * f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) =
        (expNeg q (upcrossEnd₁ c (w : ℝ≥0 → ℝ)) * f (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) *
          expNeg q (upcrossReturn c
            (shiftPath (upcrossEnd₁ c (w : ℝ≥0 → ℝ)).toNNReal w : ℝ≥0 → ℝ)) := by
    intro w
    by_cases hd : upcrossEnd₁ c (w : ℝ≥0 → ℝ) = ⊤
    · have h2 : upcrossEnd₂ c (w : ℝ≥0 → ℝ) = ⊤ := upcrossEnd₂_eq_top_of_end₁ c hd
      rw [h2, hd]
      simp
    · rw [expNeg_upcrossEnd₂_mul_piece_eq, expNeg_mul_piece_stopAt c q f hd]
  have key := lintegral_mul_shift_restart hB hm hcont hXad hXc hXinc
    (τ' := fun w : C(ℝ≥0, ℝ) => upcrossEnd₁ c (w : ℝ≥0 → ℝ)) (measurable_upcrossEnd₁ c)
    (isStoppingTime_upcrossEnd₁ hXad hXc c) hA hR
    (fun w hw => expNeg_mul_piece_stopAt c q f hw)
    (fun w hw => by simp [hw])
  exact (lintegral_congr fun ω => hstep (pathMap X hXc ω)).trans key

end LatticeProb
