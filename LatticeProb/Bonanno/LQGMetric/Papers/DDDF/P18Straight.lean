/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Straight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L9Tail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw

/-!
# DDDF Proposition 18, Step 4: the straight-path moment bound (task P2-DDDF16)

DDDF (arXiv:1904.08021, `tightness.tex` l. 930, proof of Prop 18 = `Prop:UpperTail`, Step 4):
"bounding from above the left-right distance by taking a straight path from left to right and
then using a moment method analogous to the one in (3.40) [`eq:MomentEst`], we get
`P(L^{(n)}_{1,1}(φ) ≥ e^{ξ s}) ≤ e^{-s²/(2(n+1) log 2)}`".

Here this is literally DDDF Lemma 9's moment estimate (`lemma9_tail`, proof l. 701–722, which
uses a geodesic of `Γ`, here the straight segment of the zero field `Γ = 0`) applied to
`Ψ = φ_{0,n}` with `Var φ_{0,n}(x) = n log 2` (`variance_phi`; DDDF's `(n+1) log 2` is the
star-scale normalisation of DF, see blueprint row DDDF.P2):
`P(L^{(n)}_{a,b}(φ) > a e^{ξs}) ≤ e^{-s²/(2 n log 2)}` for `n ≥ 1`, `s > ξ n log 2`
(the range where the optimal moment exponent `s/(ξ n log 2)` exceeds `1`).
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

/-- the law of `φ_{0,n}(x)`: centred Gaussian with variance `n log 2` -/
lemma hasLaw_phiMN {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (n : ℕ) (x : ℂ) :
    ∃ v : NNReal, (v : ℝ) = n * Real.log 2 ∧ HasLaw (phiMN W P 0 n x) (gaussianReal 0 v) P := by
  have := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hL := hasLaw_phi hW ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) x
  refine ⟨_, ?_, hL.congr (hφ.ae_eq x)⟩
  have h1 := hL.variance_eq
  rw [variance_id_gaussianReal, variance_phi hW (by positivity)
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le n))] at h1
  rw [← h1]
  simp [Real.log_pow]

/-- **DDDF Prop 18, Step 4 (straight path + moment method)**: for `n ≥ 1` and
`s > ξ n log 2`, `P(L^{(n)}_{a,b}(φ) > a e^{ξ s}) ≤ e^{-s²/(2 n log 2)}`. -/
theorem dddf_p18_straight {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {n : ℕ} (hn : 1 ≤ n) {s : ℝ}
    (hs : ξ * (n * Real.log 2) < s) :
    P {ω | ENNReal.ofReal (a * Real.exp (ξ * s)) <
        rectLen ξ (fun x => phiMN W P 0 n x ω) (rectAB a b)} ≤
      ENNReal.ofReal (Real.exp (-(s ^ 2 / (2 * (n * Real.log 2))))) := by
  have := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  set V : ℝ := n * Real.log 2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hV : 0 < V := by positivity
  set σ := √V
  have hσ : 0 < σ := Real.sqrt_pos.2 hV
  have hσ2 : σ ^ 2 = V := Real.sq_sqrt hV.le
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  set ε := Real.exp (-(s ^ 2 / (2 * V)))
  have hε : ε < Real.exp (-(ξ * σ) ^ 2 / 2) := by
    refine Real.exp_lt_exp.2 ?_
    rw [mul_pow, hσ2]
    have h1 : (ξ * V) ^ 2 < s ^ 2 := pow_lt_pow_left₀ hs (by positivity) two_ne_zero
    have h2 : ξ ^ 2 * V / 2 < s ^ 2 / (2 * V) := by
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    linarith [show -(ξ ^ 2 * V) / 2 = -(ξ ^ 2 * V / 2) by ring]
  have hgauss : ∀ x ∈ (rectAB a b).toSet, ∃ v : NNReal, (v : ℝ) ≤ σ ^ 2 ∧
      HasLaw (phiMN W P 0 n x) (gaussianReal 0 v) P := fun x _ => by
    obtain ⟨v, hv, hL⟩ := hasLaw_phiMN hW n x
    exact ⟨v, by rw [hv, hσ2], hL⟩
  have hcw : (rectAB a b).crossWidth = a := by simp [rectAB, MarkedRect.crossWidth]
  have h9 := lemma9_tail hξ hσ (Real.exp_pos _) hε (rectAB a b) ha.le hb (by rw [hcw]; exact ha)
    (Γ := fun _ _ => 0) (Ψ := phiMN W P 0 n) (fun ω => continuous_const)
    (fun x => measurable_const) hφ.cont hφ.meas (indepFun_const_left _ _) hgauss
  have hlen0 : rectLen ξ (fun _ => (0 : ℝ)) (rectAB a b) = ENNReal.ofReal a := by
    refine le_antisymm ?_ ?_
    · have h := rectLen_le (ξ := ξ) (f := fun _ => (0 : ℝ)) (rectAB a b) ha.le hb (M := 0)
        (fun x _ => by simp)
      simpa [hcw] using h
    · have h := rectLen_ge (ξ := ξ) (f := fun _ => (0 : ℝ)) (rectAB a b) (M := 0)
        (fun x _ => by simp)
      simpa [hcw] using h
  have hsq : √(2 * (ξ * σ) ^ 2 * Real.log ε⁻¹) = ξ * s := by
    rw [Real.log_inv, Real.log_exp, mul_pow, hσ2]
    rw [show 2 * (ξ ^ 2 * V) * -(-(s ^ 2 / (2 * V))) = (ξ * s) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [hsq, hlen0] at h9
  refine le_trans (measure_mono fun ω hω => ?_) h9
  have hω' : ENNReal.ofReal (a * Real.exp (ξ * s)) <
      rectLen ξ (fun x => phiMN W P 0 n x ω) (rectAB a b) := hω
  show ENNReal.ofReal (Real.exp (ξ * s)) * ENNReal.ofReal a <
    rectLen ξ (fun x => (0 : ℝ) + phiMN W P 0 n x ω) (rectAB a b)
  simp only [zero_add]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  exact hω'

end DDDF
end LQGMetric
