/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcC at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcB
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P317A

/-!
# The concentration step of DZZ Proposition 3.17, and the Lipschitz inputs (P2-DZZCONC)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Proposition 3.17, l. 1538–1651.

* **`conc_of_lip`**: `dev_median_le` + `abs_integral_sub_median_le`:
  `P(|Y − E Y| > 2τ + 3V/M + 2Mp) ≤ p`, `p = 2ε + 2 exp(−(ℓ − η − Cσ)²/(2σ²))`
  (DZZ l. 1595–1613).
* `DZZLipData P γ W δ A B σ ℓ τ ε`: the output of DZZ l. 1555–1594 at one `δ`: a centered
  Gaussian process `X` (DZZ's coarse field `𝒳_δ`, `Var ≤ σ²`; DZZ l. 1600 "maximal individual
  variance … is `O_{C_mc}(log δ⁻¹)`"), a good set `𝒜` (DZZ's `𝒜 ⊆ 𝒜_δ`) with
  `P(X ∉ 𝒜) ≤ ε`, `log D'_{γ,δ}(A,B) = F(X)` on `X ∈ 𝒜` (DZZ l. 1567: "`D'_{γ,δ} =
  D'_{γ,δ,𝒳_δ}`"), (eq-distance-Lip) for `‖x − x'‖_∞ ≤ ℓ` with bound `τ` (DZZ l. 1591–1594), and a
  finite `1`-net in the sense of `gauss_far_le` (continuity of `𝒳_δ`, implicit in DZZ).
* `DZZDistLip1` (OPEN): `DZZLipData` with `σ² = K log δ⁻¹`, `ℓ = a ι log δ⁻¹` (DZZ `ℓ_δ =
  ι log δ⁻¹/(2γα)`), `τ = ι log δ⁻¹`, `ε = δ^{aι}` (DZZ: `𝒳_δ ∈ 𝒜` with `c ι`-high probability),
  l. 1572–1594.
* `DZZDistLip2` (OPEN): `ℓ = (log δ⁻¹)^{0.9}`, `τ = (log δ⁻¹)^{0.93}`, `ε = δ^a` (DZZ l. 1631–1645:
  `P(𝒳_δ ∈ 𝒜) ≥ 1 − δ^{1/(2α)}`, `ℓ_δ = (log δ⁻¹)^{0.9}`, the closeness `(log δ⁻¹)^{−0.09}` of
  `𝓔*_{δ,α}` gives `τ = 4(log δ⁻¹)^{0.91} ≤ (log δ⁻¹)^{0.93}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric

namespace LQGMetric
namespace DZZ

open WhiteNoise

universe u v

/-- **Concentration from the Lipschitz property on a good set** (DZZ l. 1595–1613). -/
theorem conc_of_lip : ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {T : Type v} (X : T → Ω → ℝ), IsGaussianProcess X P →
    (∀ t, ∫ ω, X t ω ∂P = 0) → ∀ σ : ℝ, 0 ≤ σ → (∀ t, Var[X t; P] ≤ σ ^ 2) →
    ∀ (Y : Ω → ℝ), MemLp Y 2 P → ∀ V : ℝ, ∫ ω, Y ω ^ 2 ∂P ≤ V →
    ∀ (𝒜 : Set (T → ℝ)) (F : (T → ℝ) → ℝ),
    (∀ᵐ ω ∂P, (fun s => X s ω) ∈ 𝒜 → Y ω = F (fun s => X s ω)) →
    ∀ ε : ℝ, P.real {ω | (fun s => X s ω) ∉ 𝒜} ≤ ε →
    ∀ ℓ τ : ℝ, 0 ≤ τ → (∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, (∀ s, |x s - x' s| ≤ ℓ) → |F x - F x'| ≤ τ) →
    ∀ (η : ℝ) (n : ℕ) (t : Fin n → T),
    (∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, ∀ s, ∃ i, |x s - x' s| ≤ |x (t i) - x' (t i)| + η) →
    ε ≤ 4⁻¹ → C * σ + η ≤ ℓ → ∀ M : ℝ, 0 < M →
    P.real {ω | 2 * τ + 3 * V / M +
        2 * M * (2 * ε + 2 * exp (-(ℓ - η - C * σ) ^ 2 / (2 * σ ^ 2))) <
          |Y ω - ∫ ω', Y ω' ∂P|} ≤
      2 * ε + 2 * exp (-(ℓ - η - C * σ) ^ 2 / (2 * σ ^ 2)) := by
  obtain ⟨C, hC1, hC⟩ := dev_median_le.{u, v}
  refine ⟨C, hC1, ?_⟩
  intro Ω _ P _ T X hX h0 σ hσ hvar Y hY V hV 𝒜 F hYF ε hε ℓ τ hτ hlip η n t hnet hε4 hℓ M hM
  set p := 2 * ε + 2 * exp (-(ℓ - η - C * σ) ^ 2 / (2 * σ ^ 2))
  have hYm : AEMeasurable Y P := hY.aestronglyMeasurable.aemeasurable
  obtain ⟨m, hm⟩ := exists_isMedian (μ := P.map Y)
  rw [isMedian_map_iff hYm] at hm
  have hr : ∀ S : Set Ω, (2 : ENNReal)⁻¹ ≤ P S → 2⁻¹ ≤ P.real S := fun S h => by
    have := ENNReal.toReal_mono (measure_ne_top P S) h
    simpa [measureReal_def] using this
  have hm1 := hr _ hm.1
  have hm2 := hr _ hm.2
  have hdev : P.real {ω | τ < |Y ω - m|} ≤ p :=
    hC P X hX h0 σ hσ hvar Y m hm1 hm2 𝒜 F hYF ε hε ℓ τ hlip η n t hnet hε4 hℓ
  have hmean := abs_integral_sub_median_le hY hV hm1 hm2 hM hτ hdev
  refine (measureReal_mono (fun ω hω => ?_) (measure_ne_top P _)).trans hdev
  simp only [mem_setOf_eq] at hω ⊢
  have := abs_sub_le (Y ω) m (∫ ω', Y ω' ∂P)
  rw [abs_sub_comm m] at this
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The output of DZZ l. 1555–1594 at one `δ` (see the module docstring). -/
def DZZLipData (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (A B : Set ℂ)
    (σ ℓ τ ε : ℝ) : Prop :=
  ∃ (T : Type) (X : T → Ω → ℝ), IsGaussianProcess X P ∧ (∀ t, ∫ ω, X t ω ∂P = 0) ∧
    (∀ t, Var[X t; P] ≤ σ ^ 2) ∧ ∃ (𝒜 : Set (T → ℝ)) (F : (T → ℝ) → ℝ),
      (∀ᵐ ω ∂P, (fun s => X s ω) ∈ 𝒜 → logApproxLGD γ W δ A B ω = F (fun s => X s ω)) ∧
      P.real {ω | (fun s => X s ω) ∉ 𝒜} ≤ ε ∧
      (∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, (∀ s, |x s - x' s| ≤ ℓ) → |F x - F x'| ≤ τ) ∧
      ∃ (n : ℕ) (t : Fin n → T),
        ∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, ∀ s, ∃ i, |x s - x' s| ≤ |x (t i) - x' (t i)| + 1

/-- **DZZ l. 1555–1594** for (eq-concentration-approximate) (OPEN). -/
def DZZDistLip1 (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (ξ : ℝ) : Prop :=
  ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    ∀ ι ∈ Ioo (0 : ℝ) 1, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      DZZLipData P γ W δ (A δ) (B δ) (√(K * Real.log δ⁻¹)) (a * ι * Real.log δ⁻¹)
        (ι * Real.log δ⁻¹) (δ ^ (a * ι))

/-- **DZZ l. 1631–1645** for (eq-concentration-approximate-2) (OPEN). -/
def DZZDistLip2 (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (ξ : ℝ) : Prop :=
  ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ A B : ℝ → Set ℂ, IsXiAdmissible ξ A B →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      DZZLipData P γ W δ (A δ) (B δ) (√(K * Real.log δ⁻¹)) (Real.log δ⁻¹ ^ (0.9 : ℝ))
        (Real.log δ⁻¹ ^ (0.93 : ℝ)) (δ ^ a)

end DZZ
end LQGMetric
