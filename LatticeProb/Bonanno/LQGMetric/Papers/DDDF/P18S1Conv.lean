/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18S1Conv at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P5ULarge
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step3

/-!
# DDDF Prop 18, Step 1: from `ψ` to `φ` (task P2-DDDF18S1)

DDDF (arXiv:1904.08021, `tightness.tex` l. 900–910, proof of Prop 18 = `eq:UpperTailsPhi`,
Step 1). The percolation part (l. 902–905) gives, for `ψ`,
`P(L^{(n)}_{3k,k}(ψ) ≥ C k² ℓ̄_n(ψ,p)) ≤ C e^{-ck}` (`P18Step1Psi`, verbatim the display after
l. 905, with `ψ` for the parameters `psiQ₀` of Cor 17). The display after l. 906 converts it to
`φ` (`p18_step1_of_psi`):
* on `{X_{3k,k} < A√k}`: `L_{3k,k}(φ) ≤ e^{ξA√k} L_{3k,k}(ψ)` (`lenObs_le_of_XAB_le`), with the
  uniform-in-`k` tail of `X_{3k,k}` (`prop5_X3k_tail`, from Prop 5);
* `ℓ̄_n(ψ,p) ≤ C_p ℓ̄_n(φ,p/2)` ((2.27) = `eq:RatiosPsiPhi`, `ellQ_psi_le_of_tail`).
Prop 18 then follows from `P18Step1Psi` via `dddf_prop18_of_step1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}

/-- **DDDF Prop 18, Step 1 for `ψ`** (display after l. 905):
`P(L^{(n)}_{3k,k}(ψ) ≥ C k² ℓ̄_n(ψ,p)) ≤ C e^{-ck}` for `p` small, with `ψ = ψ_{0,n}` for the
parameters `psiQ₀`. -/
def P18Step1Psi (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (n k : ℕ), 1 ≤ k →
    P {ω | C * k ^ 2 * ellBarQ ξ P (psiMN psiQ₀ W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) ≤
        lenObs ξ (psiMN psiQ₀ W P 0 n) (rectAB (3 * k) k) ω} ≤
      ENNReal.ofReal (C * Real.exp (-(c * k)))

/-- **DDDF Prop 18, Step 1** (display after l. 906): the `φ` version from the `ψ` version. -/
theorem p18_step1_of_psi {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hψ : P18Step1Psi ξ W P) : P18Step1 ξ W P := by
  have := hW.isProbabilityMeasure
  set Q := psiQ₀
  obtain ⟨p₀, hp₀, hstep⟩ := hψ
  obtain ⟨A, cA, hA, hcA, hX⟩ := prop5_X3k_tail hW Q
  obtain ⟨C', c', hC', hc', htail⟩ := exists_tail_XAB_unif hW Q 1
  refine ⟨min p₀ (1 / 2), lt_min hp₀ (by norm_num), fun p hp hpp => ?_⟩
  have hp1 : p ≤ 1 / 2 := hpp.trans (min_le_right _ _)
  obtain ⟨Cψ, cψ, hCψ, hcψ, h1⟩ := hstep p hp (hpp.trans (min_le_left _ _))
  set M : ℝ := √(max 1 (Real.log (C' / (p / 2))) / c')
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  set C : ℝ := max (max A (Cψ * Real.exp (ξ * M))) (4 + Cψ)
  have hAC : A ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hψC : Cψ * Real.exp (ξ * M) ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have h4C : 4 + Cψ ≤ C := le_max_right _ _
  refine ⟨C, min cA cψ, by positivity, lt_min hcA hcψ, fun n k hk => ?_⟩
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hψv := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  -- (2.27): `ℓ̄_n(ψ,p) ≤ e^{ξM} ℓ̄_n(φ,p/2)`
  have hlev : (1 - ENNReal.ofReal p) + ENNReal.ofReal (p / 2) = 1 - ENNReal.ofReal (p / 2) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp.le, ← ENNReal.ofReal_sub _ (by positivity),
      ← ENNReal.ofReal_add (by linarith) (by positivity)]
    congr 1; ring
  have hcmp := ellQ_psi_le_of_tail (ξ := ξ) hW Q zero_le_one zero_le_one hM
    (htail 1 1 le_rfl le_rfl (p / 2) (by positivity)) (p := 1 - ENNReal.ofReal p)
    (by rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp.le, ENNReal.ofReal_pos]; linarith)
    (by rw [hlev]; exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
          (ENNReal.ofReal_pos.2 (by positivity)).ne') n
  rw [hlev, abs_of_pos hξ] at hcmp
  set lφ := ellBarN ξ W P n (ENNReal.ofReal (p / 2))
  have hlφ : 0 ≤ lφ := ellQ_nonneg hφ.cont hφ.meas _
    (by rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_pos]
        linarith)
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne')
  have hcmp' : ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) ≤
      Real.exp (ξ * M) * lφ := hcmp
  set E₁ := {ω | ENNReal.ofReal (A * √k) ≤
    XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) (3 * k) k}
  set E₂ := {ω | Cψ * k ^ 2 * ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) ≤
    lenObs ξ (psiMN Q W P 0 n) (rectAB (3 * k) k) ω}
  have hsub : {ω | Real.exp (ξ * C * √k) * C * k ^ 2 * lφ ≤
      lenObs ξ (phiMN W P 0 n) (rectAB (3 * k) k) ω} ⊆ E₁ ∪ E₂ := by
    intro ω hω
    by_cases h1 : ω ∈ E₁
    · exact Or.inl h1
    right
    have hXle : XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) (3 * k) k ≤
        ENNReal.ofReal (A * √k) := (not_le.1 h1).le
    have hL := lenObs_le_of_XAB_le (ξ := ξ) (φ := fun n => phiMN W P 0 n)
      (ψ := fun n => psiMN Q W P 0 n)
      (fun k _ => (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)).cont _) (by positivity)
      hk0 (by positivity) hXle n
    rw [abs_of_pos hξ] at hL
    have hω' : Real.exp (ξ * C * √k) * C * k ^ 2 * lφ ≤ _ := hω
    have hexp : Real.exp (ξ * (A * √k)) ≤ Real.exp (ξ * C * √k) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hAC hξ.le
      nlinarith [Real.sqrt_nonneg (k : ℝ)]
    have hkey : C * k ^ 2 * lφ ≤ lenObs ξ (psiMN Q W P 0 n) (rectAB (3 * k) k) ω := by
      have h0 : 0 ≤ C * k ^ 2 * lφ := by positivity
      have h2 : Real.exp (ξ * (A * √k)) * (C * k ^ 2 * lφ) ≤
          Real.exp (ξ * (A * √k)) * lenObs ξ (psiMN Q W P 0 n) (rectAB (3 * k) k) ω := by
        calc _ ≤ Real.exp (ξ * C * √k) * (C * k ^ 2 * lφ) := mul_le_mul_of_nonneg_right hexp h0
          _ = Real.exp (ξ * C * √k) * C * k ^ 2 * lφ := by ring
          _ ≤ _ := hω'.trans hL
      exact le_of_mul_le_mul_left h2 (Real.exp_pos _)
    show Cψ * k ^ 2 * _ ≤ _
    calc Cψ * k ^ 2 * ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p)
        ≤ Cψ * k ^ 2 * (Real.exp (ξ * M) * lφ) :=
          mul_le_mul_of_nonneg_left hcmp' (by positivity)
      _ = (Cψ * Real.exp (ξ * M)) * k ^ 2 * lφ := by ring
      _ ≤ C * k ^ 2 * lφ := by gcongr
      _ ≤ _ := hkey
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (hX k hk) (h1 n k hk)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : Real.exp (-(cA * k)) ≤ Real.exp (-(min cA cψ * k)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left cA cψ])
  have e2 : Real.exp (-(cψ * k)) ≤ Real.exp (-(min cA cψ * k)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right cA cψ])
  have he := Real.exp_pos (-(min cA cψ * k))
  nlinarith

end DDDF
end LQGMetric
