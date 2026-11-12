/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Step2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale

/-!
# DDDF Proposition 18, Step 2: decoupling and scaling (the reduction) (task P2-DDDF16)

DDDF (arXiv:1904.08021, `tightness.tex` l. 912–920, proof of Prop 18, Step 2): "Since
`L^{(n)}_{3,1}(φ) ≤ e^{ξ max_{R_{3,1}} φ_{0,m}} L^{(m,n)}_{3,1}(φ)`, the scaling property of the
field `φ`, i.e. `L^{(m,n)}_{3,1}(φ) =ᵈ 2^{-m} L^{(n−m)}_{3·2^m,2^m}(φ)`, gives
`P(L^{(n)}_{3,1}(φ) ≥ e^{ξ s√m} e^{c√(2^m)} ℓ̄_{n−m}(φ,p)) ≤ P(max_{R_{3,1}} φ_{0,m} ≥ Cm + s√m)
 + P(2^{-m} L^{(n−m)}_{3·2^m,2^m}(φ) ≥ e^{c√(2^m)} ℓ̄_{n−m}(φ,p))`."
Here this first inequality (`dddf_p18_step2_split`, for every rectangle `R_{a,b}` and every
threshold): from the a.s. decomposition `φ_{0,n} = φ_{0,m} + φ_{m,n}` (`ae_phiMN_add`,
`phi_add_ae` on a countable dense set, then continuity), the comparison
`crossLenIn_le_of_abs_sub_le` (with `max |φ_{0,m}|`, as Prop 2 bounds `|φ|`), and DDDF (2.30)
(`dddf_eq230`). The two terms on the right are then bounded by Prop 2 and by Step 1
(percolation), which are not in this file.
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

/-- `φ_{0,n} = φ_{0,m} + φ_{m,n}`, almost surely for all `x` (continuous versions) -/
theorem ae_phiMN_add {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {m n : ℕ} (hmn : m ≤ n) :
    ∀ᵐ ω ∂P, ∀ x : ℂ, phiMN W P 0 n x ω = phiMN W P 0 m x ω + phiMN W P m n x ω := by
  have h0n := isPhiVersion_phiMN hW (Nat.zero_le n)
  have h0m := isPhiVersion_phiMN hW (Nat.zero_le m)
  have hmn' := isPhiVersion_phiMN hW hmn
  have hpt : ∀ x : ℂ, ∀ᵐ ω ∂P, phiMN W P 0 n x ω = phiMN W P 0 m x ω + phiMN W P m n x ω := by
    intro x
    have hadd := phi_add_ae hW (a := (2 : ℝ)⁻¹ ^ n) (b := (2 : ℝ)⁻¹ ^ m) (c := (2 : ℝ)⁻¹ ^ 0)
      (by positivity) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le m)) x
    filter_upwards [h0n.ae_eq x, h0m.ae_eq x, hmn'.ae_eq x, hadd] with ω e1 e2 e3 e4
    rw [e1, e2, e3, e4, add_comm]
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable s := hsc.to_subtype
  have h : ∀ᵐ ω ∂P, ∀ x : s,
      phiMN W P 0 n x ω = phiMN W P 0 m x ω + phiMN W P m n x ω := by
    rw [ae_all_iff]; exact fun x => hpt x
  filter_upwards [h] with ω hω
  have hf : Continuous fun x => phiMN W P 0 n x ω := h0n.cont ω
  have hg : Continuous fun x => phiMN W P 0 m x ω + phiMN W P m n x ω :=
    (h0m.cont ω).add (hmn'.cont ω)
  intro x
  exact congrFun (Continuous.ext_on hsd hf hg fun y hy => hω ⟨y, hy⟩) x

/-- **DDDF Prop 18, Step 2, first inequality** (l. 914–917): for `0 ≤ m ≤ n` and all `M`, `x`,
`P(e^{|ξ|M} x ≤ L^{(n)}_{a,b}(φ)) ≤ P(max_{R_{a,b}} |φ_{0,m}| > M)
  + P(x ≤ 2^{-m} L^{(n−m)}_{2^m a, 2^m b}(φ))`. -/
theorem dddf_p18_step2_split {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {m n : ℕ}
    (hmn : m ≤ n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (M x : ℝ) :
    P {ω | Real.exp (|ξ| * M) * x ≤ lenObs ξ (phiMN W P 0 n) (rectAB a b) ω} ≤
      P {ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 m z ω|} +
        P {ω | x ≤ (2 : ℝ)⁻¹ ^ m *
          lenMN ξ W P ((2 : ℝ) ^ m * a) ((2 : ℝ) ^ m * b) 0 (n - m) ω} := by
  have h0m := isPhiVersion_phiMN hW (Nat.zero_le m)
  have hmn' := isPhiVersion_phiMN hW hmn
  have hlaw := dddf_eq230 (ξ := ξ) hW a b hmn (S := Ici x) measurableSet_Ici
  have hE : {ω | Real.exp (|ξ| * M) * x ≤ lenObs ξ (phiMN W P 0 n) (rectAB a b) ω} ≤ᵐ[P]
      ({ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 m z ω|} ∪
        {ω | lenMN ξ W P a b m n ω ∈ Ici x} : Set Ω) := by
    filter_upwards [ae_phiMN_add hW hmn] with ω hω hωE
    by_cases hB : M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 m z ω|
    · exact Or.inl hB
    right
    have hB' := not_lt.1 hB
    have hbd : ∀ z ∈ (rectAB a b).toSet,
        |phiMN W P 0 n z ω - phiMN W P m n z ω| ≤ M := by
      intro z hz
      rw [hω z, add_sub_cancel_right]
      exact (le_ciSup (SupTail.bddAbove_abs_of_compact (MarkedRect.isCompact_toSet _)
        (h0m.cont ω)) (⟨z, hz⟩ : (rectAB a b).toSet)).trans hB'
    have hle := crossLenIn_le_of_abs_sub_le (ξ := ξ) (A := (rectAB a b).side₁)
      (B := (rectAB a b).side₂) hbd
    have hfin := rectLen_ne_top (ξ := ξ) (rectAB a b) ha hb (hmn'.cont ω)
    have hL : lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤
        Real.exp (|ξ| * M) * lenMN ξ W P a b m n ω := by
      unfold lenMN lenObs
      calc (rectLen ξ (fun x => phiMN W P 0 n x ω) (rectAB a b)).toReal
          ≤ (ENNReal.ofReal (Real.exp (|ξ| * M)) *
              rectLen ξ (fun x => phiMN W P m n x ω) (rectAB a b)).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle
        _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    have hωE' : Real.exp (|ξ| * M) * x ≤ lenObs ξ (phiMN W P 0 n) (rectAB a b) ω := hωE
    exact (mul_le_mul_iff_of_pos_left (Real.exp_pos _)).1 (hωE'.trans hL)
  calc _ ≤ P ({ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 m z ω|} ∪
        {ω | lenMN ξ W P a b m n ω ∈ Ici x}) := measure_mono_ae hE
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [hlaw]; rfl

end DDDF
end LQGMetric
