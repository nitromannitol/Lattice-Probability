/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.OneBoxLowerTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.VerticalLower

 

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem perc_field_one_box_lower_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 3 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        P {ω | scaledBoxCrossMin (ξ : ℝ)
            (fun z => phiMN W P 0 n z ω) c ρ r <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T⁻¹ *
              ((2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) * lambdaN ξ W P n))} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  let x₀ := c.re - 3 * ρ
  let x₁ := c.re - ρ
  let x₂ := c.re + ρ
  let x₃ := c.re + 3 * ρ
  let y₀ := c.im - 3 * ρ
  let y₁ := c.im - ρ
  let y₂ := c.im + ρ
  let y₃ := c.im + 3 * ρ
  have hx : x₀ < x₃ := by dsimp [x₀, x₃]; linarith
  have hy : y₀ < y₃ := by dsimp [y₀, y₃]; linarith
  obtain ⟨a₀, b₀, ha₀, hb₀, htop⟩ :=
    perc_field_horizontal_sides_lower_of_inputs hPerc hExp ξ Q hQ ζ hζ
      x₀ x₃ y₀ y₃ y₂ y₃ hx hy
      (by dsimp [y₀, y₂]; linarith) (by dsimp [y₂, y₃]; linarith)
      hy.le le_rfl (by dsimp [y₂, y₃]; linarith)
  obtain ⟨a₁, b₁, ha₁, hb₁, hbot⟩ :=
    perc_field_horizontal_sides_lower_of_inputs hPerc hExp ξ Q hQ ζ hζ
      x₀ x₃ y₀ y₃ y₁ y₀ hx hy
      (by dsimp [y₀, y₁]; linarith) (by dsimp [y₁, y₃]; linarith)
      le_rfl hy.le (by dsimp [y₀, y₁]; linarith)
  obtain ⟨a₂, b₂, ha₂, hb₂, hright⟩ :=
    perc_field_vertical_sides_lower_of_inputs hPerc hExp ξ Q hQ ζ hζ
      x₀ x₃ y₀ y₃ x₂ x₃ hx hy
      (by dsimp [x₀, x₂]; linarith) (by dsimp [x₂, x₃]; linarith)
      hx.le le_rfl (by dsimp [x₂, x₃]; linarith)
  obtain ⟨a₃, b₃, ha₃, hb₃, hleft⟩ :=
    perc_field_vertical_sides_lower_of_inputs hPerc hExp ξ Q hQ ζ hζ
      x₀ x₃ y₀ y₃ x₁ x₀ hx hy
      (by dsimp [x₀, x₁]; linarith) (by dsimp [x₁, x₃]; linarith)
      le_rfl hx.le (by dsimp [x₀, x₁]; linarith)
  let a := a₀ + a₁ + a₂ + a₃
  let b := min (min b₀ b₁) (min b₂ b₃)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; exact lt_min (lt_min hb₀ hb₁) (lt_min hb₂ hb₃)
  refine ⟨a, b, ha, hb, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  let F : ℂ → ℂ := fun z => (r : ℂ) * z
  let K : Set ℂ := Icc x₀ x₃ ×ℂ Icc y₀ y₃
  let threshold : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
      ENNReal.ofReal (T⁻¹ *
        ((2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) * lambdaN ξ W P n))
  let X₀ : Ω → ℝ≥0∞ := fun ω => crossLenIn (ξ : ℝ)
    (fun z => phiMN W P 0 n z ω) (F '' K)
    (F '' (Icc x₀ x₃ ×ℂ ({y₂} : Set ℝ)))
    (F '' (Icc x₀ x₃ ×ℂ ({y₃} : Set ℝ)))
  let X₁ : Ω → ℝ≥0∞ := fun ω => crossLenIn (ξ : ℝ)
    (fun z => phiMN W P 0 n z ω) (F '' K)
    (F '' (Icc x₀ x₃ ×ℂ ({y₁} : Set ℝ)))
    (F '' (Icc x₀ x₃ ×ℂ ({y₀} : Set ℝ)))
  let X₂ : Ω → ℝ≥0∞ := fun ω => crossLenIn (ξ : ℝ)
    (fun z => phiMN W P 0 n z ω) (F '' K)
    (F '' (({x₂} : Set ℝ) ×ℂ Icc y₀ y₃))
    (F '' (({x₃} : Set ℝ) ×ℂ Icc y₀ y₃))
  let X₃ : Ω → ℝ≥0∞ := fun ω => crossLenIn (ξ : ℝ)
    (fun z => phiMN W P 0 n z ω) (F '' K)
    (F '' (({x₁} : Set ℝ) ×ℂ Icc y₀ y₃))
    (F '' (({x₀} : Set ℝ) ×ℂ Icc y₀ y₃))
  have h₀ : P {ω | X₀ ω < threshold ω} ≤
      ENNReal.ofReal (a₀ * Real.exp (-b₀ * (Real.log T) ^ 2)) := by
    simpa only [X₀, threshold, F, K, r] using htop P W hW n k hkn T hT
  have h₁ : P {ω | X₁ ω < threshold ω} ≤
      ENNReal.ofReal (a₁ * Real.exp (-b₁ * (Real.log T) ^ 2)) := by
    simpa only [X₁, threshold, F, K, r] using hbot P W hW n k hkn T hT
  have h₂ : P {ω | X₂ ω < threshold ω} ≤
      ENNReal.ofReal (a₂ * Real.exp (-b₂ * (Real.log T) ^ 2)) := by
    simpa only [X₂, threshold, F, K, r] using hright P W hW n k hkn T hT
  have h₃ : P {ω | X₃ ω < threshold ω} ≤
      ENNReal.ofReal (a₃ * Real.exp (-b₃ * (Real.log T) ^ 2)) := by
    simpa only [X₃, threshold, F, K, r] using hleft P W hW n k hkn T hT
  have hfour := measure_min_four_lt P X₀ X₁ X₂ X₃ threshold _ _ _ _ h₀ h₁ h₂ h₃
  calc
    P {ω | scaledBoxCrossMin (ξ : ℝ)
        (fun z => phiMN W P 0 n z ω) c ρ r < threshold ω} =
        P {ω | min (min (X₀ ω) (X₁ ω)) (min (X₂ ω) (X₃ ω)) < threshold ω} := rfl
    _ ≤ ENNReal.ofReal (a₀ * Real.exp (-b₀ * (Real.log T) ^ 2)) +
        ENNReal.ofReal (a₁ * Real.exp (-b₁ * (Real.log T) ^ 2)) +
        ENNReal.ofReal (a₂ * Real.exp (-b₂ * (Real.log T) ^ 2)) +
        ENNReal.ofReal (a₃ * Real.exp (-b₃ * (Real.log T) ^ 2)) := hfour
    _ ≤ ENNReal.ofReal (a * Real.exp (-b * (Real.log T) ^ 2)) := by
      simpa only [a, b] using gaussian_four_sum_bound
        a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ T ha₀ ha₁ ha₂ ha₃

end SupercriticalLQGUniqueness.B2.DG20Pt

