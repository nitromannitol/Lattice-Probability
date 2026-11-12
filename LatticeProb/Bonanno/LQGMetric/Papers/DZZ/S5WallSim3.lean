/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5WallSim3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim2

/-!
# P-317K-SIM, part 3: the one-scale window of the target wall on the original space

For `θ = simMap a b`, a coupling `(W₁, W₂)` as in `DZZSimCoupleU` (DZZ lem-scaling-coupling,
l. 611–624) and `A₀, B₀ ⊆ K₀`, the law of `log D^{θK₀}_δ(θA₀, θB₀)` under any white noise is that
under `W₂` (`prob_lgdMinSet_wall_eq`, S5L54I1), and `wsim_window_prob` applies with
`δ₁ = δ e^{λ}/‖a‖`, `δ₂ = δ e^{−λ}/‖a‖` (`wsim_window_target`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- The law of a walled `min D_δ(A, B)` does not depend on the white noise (copy of
`prob_lgdMinSet_wall_eq`, S5L54I1, which is not imported here). -/
theorem wsim_prob_lgdMinSet_wall_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (K : Set ℂ) (δ : ℝ) (A B : Set ℂ) (T : Set ℕ∞) :
    P {ω | lgdMinSet (dzzWall K (dzzMuIn γ W ω)) δ A B ∈ T} =
      P' {ω | lgdMinSet (dzzWall K (dzzMuIn γ W' ω)) δ A B ∈ T} := by
  have hev : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ => m c q :=
    fun c q => (measurable_pi_apply q).comp (measurable_pi_apply c)
  have hmeas : Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ => lgdRat (wallMass K m) δ A B :=
    measurable_lgdRat (m := fun m => wallMass K m) (fun c q => (hev c q).add measurable_const)
      δ A B
  have h := prob_ballMassQ_dzzMuIn_eq hW hW' hγ hγ2 (hmeas (T.to_countable.measurableSet))
  simp only [mem_preimage] at h
  simp_rw [lgdMinSet_eq_lgdRat, ballMassQ_dzzWall]
  exact h

/-- **The one-scale window of the target wall** through one coupling. -/
theorem wsim_window_target {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W₁ W₂ : WNSpace → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW₂ : IsWhiteNoise P' W₂) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {K₀ : Set ℂ} {a b : ℂ} (ha : a ≠ 0) {C lam : ℝ}
    (hcpl : P'.real {ω | ¬ ∀ x ∈ K₀, ∀ y ∈ K₀, ∀ δ : ℝ, 0 < δ →
          lgdDZZ (dzzWall (simMap a b '' K₀) (dzzMuIn γ W₂ ω)) (‖a‖ * δ * Real.exp lam)
              (simMap a b x) (simMap a b y) ≤
            lgdDZZ (dzzWall K₀ (dzzMuIn γ W₁ ω)) δ x y ∧
          lgdDZZ (dzzWall K₀ (dzzMuIn γ W₁ ω)) δ x y ≤
            lgdDZZ (dzzWall (simMap a b '' K₀) (dzzMuIn γ W₂ ω)) (‖a‖ * δ * Real.exp (-lam))
              (simMap a b x) (simMap a b y)} ≤ C * Real.exp (-lam ^ 2 / C))
    {S : Set DyBox} {A₀ B₀ : Set ℂ} (hA : A₀ ⊆ K₀) (hB : B₀ ⊆ K₀) {δ : ℝ} (hδ : 0 < δ)
    (hfin : ∀ᵐ ω ∂P', lgdMinSet (dzzWall K₀ (dzzMuIn γ W₁ ω)) (δ * Real.exp (-lam) / ‖a‖)
      A₀ B₀ < ⊤)
    (hδ₂ : δ * Real.exp (-lam) / ‖a‖ ∈ Ioo (0 : ℝ) 1)
    (hF : 1 ≤ cor39Fac (δ * Real.exp lam / ‖a‖) (δ * Real.exp (-lam) / ‖a‖)) (t w : ℝ) :
    P {ω | ¬ (t - w - Real.log (δ * Real.exp (-lam) / ‖a‖)⁻¹ ^ (0.9 : ℝ) -
          Real.log (cor39Fac (δ * Real.exp lam / ‖a‖) (δ * Real.exp (-lam) / ‖a‖)) ≤
        logMinLGD (dzzWall (simMap a b '' K₀) (dzzMuIn γ W ω)) δ
          (simMap a b '' A₀) (simMap a b '' B₀) ∧
        logMinLGD (dzzWall (simMap a b '' K₀) (dzzMuIn γ W ω)) δ
          (simMap a b '' A₀) (simMap a b '' B₀) ≤
          t + w + Real.log (δ * Real.exp (-lam) / ‖a‖)⁻¹ ^ (0.9 : ℝ))} ≤
      ENNReal.ofReal (C * Real.exp (-lam ^ 2 / C)) +
        P' (prop32EventOn S γ W₁ (fun ω => dzzWall K₀ (dzzMuIn γ W₁ ω))
          (δ * Real.exp (-lam) / ‖a‖) A₀ B₀)ᶜ +
        P' {ω | |logApproxLGDOn S γ W₁ (δ * Real.exp (-lam) / ‖a‖) A₀ B₀ ω - t| ≤ w}ᶜ +
        P' (cor39Event (fun ω => dzzWall K₀ (dzzMuIn γ W₁ ω)) (δ * Real.exp lam / ‖a‖)
          (δ * Real.exp (-lam) / ‖a‖) A₀ B₀)ᶜ := by
  have := hW₂.isProbabilityMeasure
  set δ₁ := δ * Real.exp lam / ‖a‖ with hδ₁
  set δ₂ := δ * Real.exp (-lam) / ‖a‖ with hδ₂d
  set lo := t - w - Real.log δ₂⁻¹ ^ (0.9 : ℝ) - Real.log (cor39Fac δ₁ δ₂)
  set hi := t + w + Real.log δ₂⁻¹ ^ (0.9 : ℝ)
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  -- law transfer to `W₂`
  have e := wsim_prob_lgdMinSet_wall_eq hW hW₂ hγ hγ2 (simMap a b '' K₀) δ (simMap a b '' A₀)
    (simMap a b '' B₀) {n | ¬ (lo ≤ Real.log (n.toNat : ℝ) ∧ Real.log (n.toNat : ℝ) ≤ hi)}
  simp only [mem_ofPred_eq] at e
  simp only [logMinLGD]
  rw [e]
  set E := {ω | ¬ ∀ x ∈ K₀, ∀ y ∈ K₀, ∀ δ : ℝ, 0 < δ →
          lgdDZZ (dzzWall (simMap a b '' K₀) (dzzMuIn γ W₂ ω)) (‖a‖ * δ * Real.exp lam)
              (simMap a b x) (simMap a b y) ≤
            lgdDZZ (dzzWall K₀ (dzzMuIn γ W₁ ω)) δ x y ∧
          lgdDZZ (dzzWall K₀ (dzzMuIn γ W₁ ω)) δ x y ≤
            lgdDZZ (dzzWall (simMap a b '' K₀) (dzzMuIn γ W₂ ω)) (‖a‖ * δ * Real.exp (-lam))
              (simMap a b x) (simMap a b y)} with hEdef
  have hPE : P' E ≤ ENNReal.ofReal (C * Real.exp (-lam ^ 2 / C)) := by
    rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal hcpl
  have h1 : ‖a‖ * δ₁ * Real.exp (-lam) = δ := by
    rw [hδ₁]; field_simp; simp [← Real.exp_add]
  have h2 : ‖a‖ * δ₂ * Real.exp lam = δ := by
    rw [hδ₂d]; field_simp; simp [← Real.exp_add]
  have hE : ∀ ω, ω ∉ E → ∀ x ∈ A₀, ∀ y ∈ B₀,
      lgdDZZ (dzzWall K₀ (dzzMuIn γ W₁ ω)) δ₁ x y ≤
          lgdDZZ (dzzWall (simMap a b '' K₀) (dzzMuIn γ W₂ ω)) δ (simMap a b x) (simMap a b y) ∧
        lgdDZZ (dzzWall (simMap a b '' K₀) (dzzMuIn γ W₂ ω)) δ (simMap a b x) (simMap a b y) ≤
          lgdDZZ (dzzWall K₀ (dzzMuIn γ W₁ ω)) δ₂ x y := by
    intro ω hω x hx y hy
    simp only [hEdef, mem_ofPred_eq, not_not] at hω
    have k1 := (hω x (hA hx) y (hB hy) δ₁ (by positivity)).2
    have k2 := (hω x (hA hx) y (hB hy) δ₂ (by positivity)).1
    rw [h1] at k1; rw [h2] at k2
    exact ⟨k1, k2⟩
  have hw := wsim_window_prob (P' := P') (S := S) (γ := γ) (W₁ := W₁) (E := E) hE hfin hδ₂ hF t w
  refine hw.trans ?_
  gcongr

end DZZ
end LQGMetric
