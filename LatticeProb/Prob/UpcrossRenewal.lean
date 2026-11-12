import Mathlib
import LatticeProb.Prob.UpcrossLaplace
import LatticeProb.Prob.BrownianRestartPath

/-!
# Renewal identities for the Laplace transform of the first up-crossing piece

Let `X` be an adapted process with continuous paths whose increments are those of a Brownian
motion `B` plus the drift `mu`, and let `μ₀` be the law of the Brownian path with drift `mu` (started
at `0`) on `C(ℝ≥0, ℝ)`.  For `f` a measurable functional of the first up-crossing piece of `X`
(from `0` to the level `c > 0`) and `q ∈ ℝ`, the strong Markov property on path space at the first
zero `τ₀` and at the end `d₁` of the first up-crossing interval gives

* `LatticeProb.lintegral_expNeg_piece_upcrossEnd₁_restart`:
  `E[e^{-q d₁} f(piece)] = E[e^{-q τ₀}] · ∫ f(piece v) e^{-q d₁ v} dμ₀`;
* `LatticeProb.expNeg_mul_piece_stopAt`: the weight `e^{-q d₁} f(piece)` is unchanged when the
  path is stopped at `d₁` (used for the renewal at `d₁`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- Stopping a path at its (finite) first zero time keeps the first zero time. -/
lemma hitFrom_zero_stopAt {w : C(ℝ≥0, ℝ)} (h : hitFrom 0 0 (w : ℝ≥0 → ℝ) ≠ ⊤) :
    hitFrom 0 0 (stopAt (hitFrom 0 0 (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ) = hitFrom 0 0 (w : ℝ≥0 → ℝ) := by
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = hitFrom 0 0 (w : ℝ≥0 → ℝ) :=
    ⟨_, ENNReal.coe_toNNReal h⟩
  have h1 := (isStopFun_hitFrom_zero 0 w T).1 (le_of_eq hT.symm)
  rw [← hT]
  exact h1.trans hT.symm

/-- Stopping a path at the finite end `d₁` of its first up-crossing interval keeps `d₁`. -/
lemma upcrossEnd₁_stopAt (c : ℝ) {w : C(ℝ≥0, ℝ)} (h : upcrossEnd₁ c (w : ℝ≥0 → ℝ) ≠ ⊤) :
    upcrossEnd₁ c (stopAt (upcrossEnd₁ c (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ) =
      upcrossEnd₁ c (w : ℝ≥0 → ℝ) := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0, (D : ℝ≥0∞) = upcrossEnd₁ c (w : ℝ≥0 → ℝ) :=
    ⟨_, ENNReal.coe_toNNReal h⟩
  have h1 := (isStopFun_upcrossEnd₁ c w D).1 (le_of_eq hD.symm)
  rw [← hD]
  exact h1.trans hD.symm

lemma upcrossEnd₂_eq_top_of_end₁ (c : ℝ) {w : ℝ≥0 → ℝ} (h : upcrossEnd₁ c w = ⊤) :
    upcrossEnd₂ c w = ⊤ := by
  unfold upcrossEnd₂
  rw [h, hitFrom_top, hitFrom_top]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Renewal at the first zero.** -/
theorem lintegral_expNeg_piece_upcrossEnd₁_restart [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {X : ℝ≥0 → Ω → ℝ}
    (hXad : StronglyAdapted (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm)) X)
    (hXc : ∀ ω, Continuous fun t => X t ω) {mu : ℝ}
    (hXinc : ∀ ω t s, X (t + s) ω - X t ω = (B (t + s) ω - B t ω) + mu * s)
    {c : ℝ} (hc : 0 < c) (q : ℝ) {f : (ℝ≥0 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, expNeg q (upcrossEnd₁ c (fun t => X t ω)) * f (firstUpcrossPiece c (fun t => X t ω)) ∂P
      = (∫⁻ ω, expNeg q (hitFrom 0 0 (fun t => X t ω)) ∂P) *
        ∫⁻ v : C(ℝ≥0, ℝ), f (firstUpcrossPiece c (v : ℝ≥0 → ℝ)) *
          expNeg q (upcrossEnd₁ c (v : ℝ≥0 → ℝ)) ∂((P.map (pathMap B hcont)).map (driftMap mu)) := by
  set F := natFiltration (liftOne B) (stronglyMeasurable_liftOne hm) with hF
  set τ : Ω → ℝ≥0∞ := fun ω => hitFrom 0 0 (fun t => X t ω) with hτdef
  have hτ : IsStoppingTime F τ := isStoppingTime_hitFrom_zero hXad hXc 0
  have hXm : ∀ t, Measurable (X t) := fun t => (hXad t).measurable.mono (F.le t) le_rfl
  have hpm : Measurable (pathMap X hXc) := measurable_pathMap X hXm hXc
  have hτm : Measurable τ := (measurable_hitFrom measurable_const 0).comp hpm
  have hmeas : MeasurableSet {ω | τ ω < ⊤} := measurableSet_lt hτm measurable_const
  set G : C(ℝ≥0, ℝ) → ℝ≥0∞ := fun v =>
    f (firstUpcrossPiece c (v : ℝ≥0 → ℝ)) * expNeg q (upcrossEnd₁ c (v : ℝ≥0 → ℝ)) with hG
  have hGm : Measurable G :=
    (hf.comp (measurable_firstUpcrossPiece c)).mul
      ((measurable_expNeg q).comp (measurable_upcrossEnd₁ c))
  set Φ : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) → ℝ≥0∞ := fun p =>
    expNeg q (hitFrom 0 0 (p.1 : ℝ≥0 → ℝ)) * G p.2 with hΦdef
  have hΦ : Measurable Φ :=
    ((measurable_expNeg q).comp ((measurable_hitFrom measurable_const 0).comp measurable_fst)).mul
      (hGm.comp measurable_snd)
  have hexp : Measurable fun ω => expNeg q (τ ω) := (measurable_expNeg q).comp hτm
  have step1 : ∀ ω, expNeg q (upcrossEnd₁ c (fun t => X t ω)) *
      f (firstUpcrossPiece c (fun t => X t ω)) =
      expNeg q (τ ω) * G (shiftPath (τ ω).toNNReal (pathMap X hXc ω)) := fun ω =>
    expNeg_upcrossEnd₁_mul_piece_eq hc q (pathMap X hXc ω) f
  have hsupp : Function.support (fun ω => expNeg q (τ ω) *
      G (shiftPath (τ ω).toNNReal (pathMap X hXc ω))) ⊆ {ω | τ ω < ⊤} := by
    intro ω hω
    by_contra hne
    have : τ ω = ⊤ := by simpa using hne
    exact hω (by simp [this])
  have hsupp' : Function.support (fun ω => expNeg q (τ ω)) ⊆ {ω | τ ω < ⊤} := by
    intro ω hω
    by_contra hne
    have : τ ω = ⊤ := by simpa using hne
    exact hω (by simp [this])
  calc ∫⁻ ω, expNeg q (upcrossEnd₁ c (fun t => X t ω)) *
        f (firstUpcrossPiece c (fun t => X t ω)) ∂P
      = ∫⁻ ω in {ω | τ ω < ⊤}, expNeg q (τ ω) *
          G (shiftPath (τ ω).toNNReal (pathMap X hXc ω)) ∂P := by
        rw [setLIntegral_eq_of_support_subset hsupp]
        exact lintegral_congr step1
    _ = ∫⁻ ω in {ω | τ ω < ⊤},
          Φ (stopAt (τ ω) (pathMap X hXc ω), shiftPath (τ ω).toNNReal (pathMap X hXc ω)) ∂P := by
        refine setLIntegral_congr_fun hmeas fun ω hω => ?_
        have hne : hitFrom 0 0 ((pathMap X hXc ω : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) ≠ ⊤ := hω.ne
        have hz : hitFrom 0 0 (stopAt (τ ω) (pathMap X hXc ω) : ℝ≥0 → ℝ) = τ ω :=
          hitFrom_zero_stopAt hne
        simp only [hΦdef]
        rw [hz]
    _ = ∫⁻ ω in {ω | τ ω < ⊤}, ∫⁻ w, Φ (stopAt (τ ω) (pathMap X hXc ω), w)
          ∂((P.map (pathMap B hcont)).map (driftMap mu)) ∂P :=
        lintegral_restart_path hB hm hcont hXad hXc hXinc hτ hΦ
    _ = ∫⁻ ω in {ω | τ ω < ⊤}, expNeg q (τ ω) *
          ∫⁻ v, G v ∂((P.map (pathMap B hcont)).map (driftMap mu)) ∂P := by
        refine setLIntegral_congr_fun hmeas fun ω hω => ?_
        have hne : hitFrom 0 0 ((pathMap X hXc ω : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) ≠ ⊤ := hω.ne
        have hz : hitFrom 0 0 (stopAt (τ ω) (pathMap X hXc ω) : ℝ≥0 → ℝ) = τ ω :=
          hitFrom_zero_stopAt hne
        simp only [hΦdef]
        rw [hz, lintegral_const_mul _ hGm]
    _ = (∫⁻ ω, expNeg q (τ ω) ∂P) * ∫⁻ v, G v ∂((P.map (pathMap B hcont)).map (driftMap mu)) := by
        rw [lintegral_mul_const _ hexp, setLIntegral_eq_of_support_subset hsupp']

/-- The Laplace weight of `d₁` times a functional of the first up-crossing piece is unchanged by
stopping the path at `d₁`. -/
lemma expNeg_mul_piece_stopAt (c q : ℝ) (f : (ℝ≥0 → ℝ) → ℝ≥0∞) {w : C(ℝ≥0, ℝ)}
    (h : upcrossEnd₁ c (w : ℝ≥0 → ℝ) ≠ ⊤) :
    expNeg q (upcrossEnd₁ c (stopAt (upcrossEnd₁ c (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ)) *
        f (firstUpcrossPiece c (stopAt (upcrossEnd₁ c (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ)) =
      expNeg q (upcrossEnd₁ c (w : ℝ≥0 → ℝ)) * f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0, upcrossEnd₁ c (w : ℝ≥0 → ℝ) = D :=
    ⟨_, (ENNReal.coe_toNNReal h).symm⟩
  rw [upcrossEnd₁_stopAt c h, hD, firstUpcrossPiece_stopAt c w hD]

end LatticeProb
