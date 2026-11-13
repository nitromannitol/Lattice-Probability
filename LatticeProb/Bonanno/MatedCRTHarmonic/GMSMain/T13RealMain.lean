/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T13RealMain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T13RealThm32

/-!
# [18] Theorems 1.3 (repaired), 1.4 and 3.2 at every real mesh `ε ∈ (0, 1)` for every frozen coupling

For a frozen coupling `D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm` on a standard Borel
space and `γ ∈ (0, 2)`, at every real mesh `ε ∈ (0, 1)` the map is the frozen `MatedCRT.graph ε (bm ω) h` with the
cells `η ω([ε(x−1), εx])` (`MatedCRT.cell ε (η ω)`). Inputs: [18] Proposition 2.10 in the source order
(`epsA_prop210Source`) and Lemma 2.7 (`epsA_lemma27Bad_coupling`), both at every real mesh.

* **`t13_theorem13_real`** — repaired Theorem 1.3 (`matedCRT_energy_le_of_matingOfTrees`):
  `∃ α > 0, ∀ ρ ∈ (0,1), ∀ C ≥ 1, ∃ A > 0, ∀ D … ∀ f …, ∃ C_f, ∀ ε ∈ (0,1)`,
  `P[¬ T13RealEnergyGood ε (bm ω) (η ω) D f A 0] ≤ C_f ε^α`;
* **`t13_theorem32_real`** — Theorem 3.2 as printed (`matedCRT_energy_le_add_of_matingOfTrees`):
  `∃ α > 0, ∃ β > 0, ∀ ρ, ∀ C ≥ 1, ∃ A > 0, ∃ C_r, ∀ ε ∈ (0,1), ∀ (D, f) ∈ 𝒞_C(ε^β)`,
  `P[¬ T13RealEnergyGood ε (bm ω) (η ω) D f A ε^α] ≤ C_r ε^α`;
* **`t13_theorem14_green_real`** — Theorem 1.4 (1.8) (`matedCRT_green_and_recurrent_of_matingOfTrees`, part (i)):
  `∃ α > 0, ∀ ρ, ∃ A > 0, ∃ C, ∀ ε ∈ (0,1)`, `P[¬ T13RealGreenGood ε ρ A (bm ω) (η ω)] ≤ C ε^α`;
* recurrence (part (ii)) is `t13_theorem14_recurrent_exists` (every real `ε > 0`, `T13Main`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic GMS3

/-- The Proposition 2.10 rate at a lowered exponent `α ≤ α₂`. -/
theorem t13r_prop210_lower_exponent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {bm : Ω → MatedCRT.Path2} {η : Ω → C(ℝ, ℂ)} {ρP Cb β A α₂ α CP : ℝ} (hαα₂ : α ≤ α₂) (hCP : 0 ≤ CP)
    (h : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (V : Set ℂ) (g : ℂ → ℝ), GMS4.Prop210Admissible ε ρP Cb β V g →
      P (EpsAProp210Bad bm η ε V g A (ε ^ α₂)) ≤ ENNReal.ofReal (CP * ε ^ α₂)) :
    ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (V : Set ℂ) (g : ℂ → ℝ), GMS4.Prop210Admissible ε ρP Cb β V g →
      P (EpsAProp210Bad bm η ε V g A (ε ^ α)) ≤ ENNReal.ofReal (CP * ε ^ α) := by
  intro ε hε V g hadm
  have hpow : ε ^ α₂ ≤ ε ^ α := Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le hαα₂
  exact (measure_mono (t13r_prop210Bad_anti_tol hpow)).trans ((h ε hε V g hadm).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hCP)))

/-- A rate `≤ C ε^{α₁}` is a rate `≤ C ε^{α₀}` for `α₀ ≤ α₁`, `C ≥ 0`, `ε ∈ (0, 1)`. -/
theorem t13r_rate_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S : Set Ω} {C α₀ α₁ ε : ℝ}
    (hC : 0 ≤ C) (hα : α₀ ≤ α₁) (hε : ε ∈ Ioo (0 : ℝ) 1) (h : P S ≤ ENNReal.ofReal (C * ε ^ α₁)) :
    P S ≤ ENNReal.ofReal (C * ε ^ α₀) :=
  h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le hα) hC))

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The window exponent `q = (2+γ)^{-2}` of Lemma 2.7. -/
theorem t13r_q_mem (hγ : γ ∈ Ioo (0 : ℝ) 2) : 0 < 1 / (2 + γ) ^ 2 ∧ 1 / (2 + γ) ^ 2 < 2 / (2 + γ) ^ 2 := by
  have hγ2 : 0 < (2 + γ) ^ 2 := by have := hγ.1; positivity
  exact ⟨by positivity, div_lt_div_of_pos_right (by norm_num) hγ2⟩

/-- **[18] Theorem 3.2 (quantitative Dirichlet energy bound) at every real mesh, for the mated-CRT map of a frozen
coupling**: `∃ α, β > 0` (depending only on the coupling, i.e. on `γ`), `∀ ρ ∈ (0, 1)`, `∀ C ≥ 1`, `∃ A > 0`,
`∃ C_r` (depending only on `C`, `ρ` and the coupling), for every `ε ∈ (0, 1)` and every `(D, f) ∈ 𝒞_C(ε^β)` (with `f`
continuous on `D̄`): `P[Energy(f_ε; G^ε(D)) ≤ A Energy(f; D) + ε^α fails] ≤ C_r ε^α` ((3.10)). -/
theorem t13_theorem32_real (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ C : ℝ, 1 ≤ C →
      ∃ A : ℝ, 0 < A ∧ ∃ Cr : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ →
        (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier Dom)) ≤ ENNReal.ofReal (C * r)) →
        BoundedConvexityWith C Dom →
        ∀ f : ℂ → ℝ, DifferentiableOn ℝ f Dom →
          (∀ z ∈ Dom, ∀ w ∈ Dom, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ ε ^ (-β) * dist z w) →
          (∀ z ∈ Dom, |f z| ≤ ε ^ (-β)) → (∀ z ∈ Dom, ‖fderiv ℝ f z‖ ≤ ε ^ (-β)) →
          ContinuousOn f (closure Dom) →
            P {ω | ¬ T13RealEnergyGood ε (bm ω) (η ω) Dom f A (ε ^ α)} ≤ ENNReal.ofReal (Cr * ε ^ α) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨α₂, hα₂, β₂, hβ₂, h210⟩ := epsA_prop210Source D hstd hγ
  obtain ⟨hq0, hq2⟩ := t13r_q_mem hγ
  set q : ℝ := 1 / (2 + γ) ^ 2 with hqdef
  have hL : 0 < GMSLemma27.lemma27Exponent q γ := GMSLemma27.lemma27Exponent_pos hγ.1 hq0 hq2
  set αr : ℝ := min α₂ (GMSLemma27.lemma27Exponent q γ / 2) with hαrdef
  have hαr : 0 < αr := lt_min hα₂ (by linarith)
  have hαrL : αr < GMSLemma27.lemma27Exponent q γ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set m : ℝ := min αr (min q β₂) with hmdef
  have hm0 : 0 < m := lt_min hαr (lt_min hq0 hβ₂)
  set β : ℝ := min (β₂ / 2) (m / 4) with hβdef
  have hβ : 0 < β := lt_min (by positivity) (by positivity)
  have h2β : 2 * β ≤ β₂ := by have := min_le_left (β₂ / 2) (m / 4); linarith
  have h4β : 4 * β ≤ m := by have := min_le_right (β₂ / 2) (m / 4); linarith
  have hmαr : m ≤ αr := min_le_left _ _
  refine ⟨m / 4, by positivity, β, hβ, fun ρ hρ0 hρ1 C hC1 => ?_⟩
  set ρ₁ : ℝ := (ρ + 1) / 2 with hρ₁def
  have hρρ₁ : ρ < ρ₁ := by rw [hρ₁def]; linarith
  have hρ₁1 : ρ₁ < 1 := by rw [hρ₁def]; linarith
  have hρ₁0 : 0 < ρ₁ := hρ0.trans hρρ₁
  obtain ⟨A, hA, hCA⟩ := h210 ρ₁ hρ₁0 hρ₁1
  set Cb : ℝ := max C (16 * π) with hCbdef
  have hCb16 : 16 * π ≤ Cb := le_max_right _ _
  have hCb1 : 1 < Cb := by nlinarith [Real.pi_gt_three]
  obtain ⟨CP, hCP, h210ρ⟩ := hCA Cb hCb1
  obtain ⟨C27, hC27, h27⟩ := epsA_lemma27Bad_coupling D hstd hγ hq0 hq2 ⟨hρ₁0, hρ₁1⟩ hαrL
  obtain ⟨Cr, hCr, hrate⟩ := t13r_theorem32_of_inputs P bm η (αt := m / 4) hρ0 hρρ₁ hρ₁1 hq0 hβ₂ hαr hA.le
    hCP hC27 hC1 (le_max_left _ _) hCb16 hβ h2β h4β le_rfl h27
    (t13r_prop210_lower_exponent (min_le_left _ _) hCP h210ρ)
  refine ⟨3 * C ^ 2 * A, by positivity, Cr, fun ε hε hε1 Dom hDo hDsub hbdry hbc f hf hLip hfb hGf hfc => ?_⟩
  exact t13r_rate_mono hCr (by linarith) ⟨hε, hε1⟩
    (hrate ε ⟨hε, hε1⟩ Dom f hDo hDsub hbdry hbc hf hLip hfb hGf hfc)

end Coupling

end MatedCRTHarmonic.GMSMain
