/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5WallSim2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim1

/-!
# P-317K-SIM, part 2: the window of `log D^{θK₀}_δ` at one scale through the coupling

DZZ lem-scaling-coupling (l. 611–624) gives, outside a small event `E`,
`D^{K₀}_{δ₁}(x, y) ≤ D^{θK₀}_δ(θx, θy) ≤ D^{K₀}_{δ₂}(x, y)` with `δ₁ = δ e^{λ}/‖a‖`,
`δ₂ = δ e^{−λ}/‖a‖` (DEC-123 §3). On the walled P3.2 event at `δ₂` (l. 807–812), the
concentration event of `log D'^{K₀}_{δ₂}` around a number `t` (l. 1528–1530) and the walled
Corollary 3.9 event for `(δ₁, δ₂)` (l. 1235–1244), the target `log D^{θK₀}_δ` lies in
`[t − w − e − log F, t + w + e]`, `e = (log δ₂⁻¹)^{0.9}`, `F` the factor of Cor 3.9
(`wsim_window_prob`). DZZ's own route for the shifted means (DEC-123 §3, last bullet).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The factor of `cor39Event`. -/
def cor39Fac (δ δ' : ℝ) : ℝ :=
  (δ / δ') ^ 3 * Real.exp ((Real.log δ⁻¹) ^ (0.9 : ℝ) +
    (Real.log δ⁻¹) ^ (0.8 : ℝ) + (Real.log δ'⁻¹) ^ (0.9 : ℝ))

lemma one_le_cor39Fac {δ δ' : ℝ} (hδ' : 0 < δ') (hδδ' : δ' ≤ δ) (hδ1 : δ ≤ 1) :
    1 ≤ cor39Fac δ δ' := by
  have hL : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg ((one_le_inv₀ (hδ'.trans_le hδδ')).2 hδ1)
  have hL' : 0 ≤ Real.log δ'⁻¹ := Real.log_nonneg ((one_le_inv₀ hδ').2 (hδδ'.trans hδ1))
  have h1 : 1 ≤ (δ / δ') ^ 3 := one_le_pow₀ ((one_le_div hδ').2 hδδ')
  have h2 : 1 ≤ Real.exp ((Real.log δ⁻¹) ^ (0.9 : ℝ) + (Real.log δ⁻¹) ^ (0.8 : ℝ) +
      (Real.log δ'⁻¹) ^ (0.9 : ℝ)) :=
    Real.one_le_exp (by positivity)
  unfold cor39Fac
  nlinarith

lemma wsim_min_image_le {μ₁ μ₂ : Measure ℂ} {δ₁ δ₂ : ℝ} {f : ℂ → ℂ} {A B : Set ℂ}
    (h : ∀ x ∈ A, ∀ y ∈ B, lgdDZZ μ₂ δ₂ (f x) (f y) ≤ lgdDZZ μ₁ δ₁ x y) :
    lgdMinSet μ₂ δ₂ (f '' A) (f '' B) ≤ lgdMinSet μ₁ δ₁ A B :=
  le_iInf₂ fun x hx => le_iInf₂ fun y hy =>
    (iInf₂_le (f x) (mem_image_of_mem f hx)).trans
      ((iInf₂_le (f y) (mem_image_of_mem f hy)).trans (h x hx y hy))

/-- The deterministic chain of the window. -/
lemma wsim_log_window {Y1 X Y2 Y' : ℕ∞} {F e t w : ℝ} (hF : 1 ≤ F) (he : 0 ≤ e)
    (h1' : 1 ≤ Y1) (h1 : Y1 ≤ X) (h2 : X ≤ Y2) (hfin : Y2 ≠ ⊤)
    (hp32a : (Y' : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-e)) ≤ Y2)
    (hp32b : (Y2 : ℝ≥0∞) ≤ Y' * ENNReal.ofReal (Real.exp e))
    (hconc : |Real.log (Y'.toNat : ℝ) - t| ≤ w)
    (hcor : (Y2 : ℝ≥0∞) ≤ (Y1 : ℝ≥0∞) * ENNReal.ofReal F) :
    t - w - e - Real.log F ≤ Real.log (X.toNat : ℝ) ∧ Real.log (X.toNat : ℝ) ≤ t + w + e := by
  have hXf : X ≠ ⊤ := ne_top_of_le_ne_top hfin h2
  have hY1f : Y1 ≠ ⊤ := ne_top_of_le_ne_top hXf h1
  have hX1 : 1 ≤ X := h1'.trans h1
  have hY21 : 1 ≤ Y2 := hX1.trans h2
  have a1 := abs_log_toNat_sub_le he hp32a hp32b
  have a2 := wsim_log_le_of_le hX1 hfin h2
  have a3 := wsim_log_le_add_log hY21 hY1f hF hcor
  have a4 := wsim_log_le_of_le h1' hXf h1
  rw [abs_le] at a1 hconc
  constructor <;> linarith [a1.1, a1.2, hconc.1, hconc.2]

/-- **The window at one scale** (outside the coupling event `E`, the walled P3.2 event at `δ₂`,
the concentration event of `log D'_{δ₂}` around `t`, the walled Cor 3.9 event, and a null set). -/
theorem wsim_window_prob {P' : Measure Ω} {μ₁ μ₂ : Ω → Measure ℂ} {S : Set DyBox} {γ : ℝ}
    {W₁ : WNSpace → Ω → ℝ} {δ δ₁ δ₂ : ℝ} {f : ℂ → ℂ} {A₀ B₀ : Set ℂ} {E : Set Ω}
    (hE : ∀ ω, ω ∉ E → ∀ x ∈ A₀, ∀ y ∈ B₀,
      lgdDZZ (μ₁ ω) δ₁ x y ≤ lgdDZZ (μ₂ ω) δ (f x) (f y) ∧
        lgdDZZ (μ₂ ω) δ (f x) (f y) ≤ lgdDZZ (μ₁ ω) δ₂ x y)
    (hfin : ∀ᵐ ω ∂P', lgdMinSet (μ₁ ω) δ₂ A₀ B₀ < ⊤) (hδ₂ : δ₂ ∈ Ioo (0 : ℝ) 1)
    (hF : 1 ≤ cor39Fac δ₁ δ₂) (t w : ℝ) :
    P' {ω | ¬ (t - w - Real.log δ₂⁻¹ ^ (0.9 : ℝ) - Real.log (cor39Fac δ₁ δ₂) ≤
        logMinLGD (μ₂ ω) δ (f '' A₀) (f '' B₀) ∧
        logMinLGD (μ₂ ω) δ (f '' A₀) (f '' B₀) ≤ t + w + Real.log δ₂⁻¹ ^ (0.9 : ℝ))} ≤
      P' E + P' (prop32EventOn S γ W₁ μ₁ δ₂ A₀ B₀)ᶜ +
        P' {ω | |logApproxLGDOn S γ W₁ δ₂ A₀ B₀ ω - t| ≤ w}ᶜ +
        P' (cor39Event μ₁ δ₁ δ₂ A₀ B₀)ᶜ := by
  set N := {ω | ¬ lgdMinSet (μ₁ ω) δ₂ A₀ B₀ < ⊤} with hN
  have hN0 : P' N = 0 := by
    have := ae_iff.1 hfin
    simpa [hN] using this
  have he : 0 ≤ Real.log δ₂⁻¹ ^ (0.9 : ℝ) :=
    Real.rpow_nonneg (Real.log_nonneg ((one_le_inv₀ hδ₂.1).2 hδ₂.2.le)) _
  have hsub : {ω | ¬ (t - w - Real.log δ₂⁻¹ ^ (0.9 : ℝ) - Real.log (cor39Fac δ₁ δ₂) ≤
        logMinLGD (μ₂ ω) δ (f '' A₀) (f '' B₀) ∧
        logMinLGD (μ₂ ω) δ (f '' A₀) (f '' B₀) ≤ t + w + Real.log δ₂⁻¹ ^ (0.9 : ℝ))} ⊆
      E ∪ (prop32EventOn S γ W₁ μ₁ δ₂ A₀ B₀)ᶜ ∪
        {ω | |logApproxLGDOn S γ W₁ δ₂ A₀ B₀ ω - t| ≤ w}ᶜ ∪
        (cor39Event μ₁ δ₁ δ₂ A₀ B₀)ᶜ ∪ N := by
    intro ω hω
    by_contra hc
    simp only [mem_union, mem_compl_iff, not_or, not_not, hN, mem_ofPred_eq] at hc
    obtain ⟨⟨⟨⟨hωE, h32⟩, hcc⟩, hcor⟩, hfω⟩ := hc
    have hl := lgdMinSet_le_image (f := f) fun x hx y hy => (hE ω hωE x hx y hy).1
    have hu := wsim_min_image_le (f := f) fun x hx y hy => (hE ω hωE x hx y hy).2
    exact hω (wsim_log_window (Y' := approxLGDSetOn S γ W₁ δ₂ A₀ B₀ ω) hF he
      (one_le_lgdMinSet _ _ _ _) hl hu hfω.ne h32.1 h32.2 hcc hcor)
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  rw [hN0, add_zero]
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  exact measure_union_le _ _

end DZZ
end LQGMetric
