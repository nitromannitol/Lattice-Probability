/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.PsiQuantile at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiProp5

/-!
# Quantile comparison of `φ` and `ψ` through `X_{a,b}` (task P2-DDDFPSI; DDDF (2.26)–(2.28))

DDDF (arXiv:1904.08021, `tightness.tex` l. 482–490): from
`e^{−ξX_{a,b}} L^{(n)}_{a,b}(ψ) ≤ L^{(n)}_{a,b}(φ) ≤ e^{ξX_{a,b}} L^{(n)}_{a,b}(ψ)` (`rectLen_le_XAB`)
and Prop 5 "(and a union bound)" one gets the quantile comparisons (2.27)
`ℓ^{(n)}_{a,b}(φ, p) ≤ e^{ξ C√|log ε/C|} ℓ^{(n)}_{a,b}(ψ, p + ε)` etc.

* `ellQ_phi_le_of_tail`: if `P(X_{a,b} > M) ≤ ε` then `ℓ(φ, p) ≤ e^{|ξ|M} ℓ(ψ, p + ε)`;
  `ellQ_psi_le_of_tail`: the same with `φ`, `ψ` swapped (`X_{a,b}` is symmetric). These are the
  union-bound step of DDDF l. 486; the lower bounds of (2.27) are the same statements read with
  `p − ε` in place of `p`, and the `ℓ̄` bounds are the statements at `1 − p`.
* `exists_ellQ_phi_le`: with Prop 5 (`dddf_prop5_XAB`), for every `ε ∈ (0,1)` the tail
  hypothesis holds with `M = √(log(C/ε)/c)`, i.e. (2.27) with `e^{|ξ|√(log(C/ε)/c)}` in place of
  DDDF's `e^{ξ C √|log ε/C|}` (same form, constants named differently).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The generic union-bound step: if `L_φ ≤ K L_ψ` off an event of probability `≤ ε`, then
`ℓ(φ, p) ≤ K ℓ(ψ, p + ε)`. -/
theorem ellQ_le_of_le_off {ξ : ℝ} {Y Z : ℂ → Ω → ℝ} [IsProbabilityMeasure P]
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (hZc : ∀ ω, Continuous fun x => Z x ω) (hZm : ∀ x, Measurable (Z x)) (R : MarkedRect)
    {K : ℝ} (hK : 0 ≤ K) {E : Set Ω} {ε p : ℝ≥0∞} (hE : P E ≤ ε)
    (hle : ∀ ω ∉ E, lenObs ξ Y R ω ≤ K * lenObs ξ Z R ω) (hp0 : 0 < p) (hp1 : p + ε < 1) :
    ellQ ξ P Y R p ≤ K * ellQ ξ P Z R (p + ε) := by
  have hε : ε ≠ ∞ := ne_top_of_lt (lt_of_le_of_lt le_add_self hp1)
  have hpε0 : 0 < p + ε := lt_of_lt_of_le hp0 le_self_add
  have hp1' : p < 1 := lt_of_le_of_lt le_self_add hp1
  set ℓ := ellQ ξ P Z R (p + ε)
  have hZ := prob_le_ellQ (ξ := ξ) (P := P) hZc hZm R hpε0 hp1
  have hsub : {ω | lenObs ξ Z R ω ≤ ℓ} ⊆ {ω | lenObs ξ Y R ω ≤ K * ℓ} ∪ E := by
    intro ω hω
    by_cases hωE : ω ∈ E
    · exact Or.inr hωE
    · left
      exact (hle ω hωE).trans (mul_le_mul_of_nonneg_left hω hK)
  have h1 : p + ε ≤ P {ω | lenObs ξ Y R ω ≤ K * ℓ} + ε :=
    hZ.trans ((measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add_right hE _)))
  have h2 : p ≤ P {ω | lenObs ξ Y R ω ≤ K * ℓ} := (ENNReal.add_le_add_iff_right hε).mp h1
  refine (le_measure_Iic_iff_lowerQuantile_le hp0 hp1').1 ?_
  rw [Measure.map_apply (measurable_lenObs hYc hYm R) measurableSet_Iic]
  exact h2

omit [MeasurableSpace Ω] in
/-- On `{X_{a,b} ≤ M}`: `L^{(n)}_{a,b}(φ) ≤ e^{|ξ|M} L^{(n)}_{a,b}(ψ)` (DDDF l. 482). -/
theorem lenObs_le_of_XAB_le {ξ : ℝ} {φ ψ : ℕ → ℂ → Ω → ℝ}
    (hψc : ∀ n ω, Continuous fun x => ψ n x ω) {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : 0 ≤ M) {ω : Ω}
    (hX : XAB (fun n y => φ n y ω) (fun n y => ψ n y ω) a b ≤ ENNReal.ofReal M) (n : ℕ) :
    lenObs ξ (φ n) (rectAB a b) ω ≤ exp (|ξ| * M) * lenObs ξ (ψ n) (rectAB a b) ω := by
  have h := rectLen_le_XAB (ξ := ξ) hM hX n
  have hfin := rectLen_ne_top (ξ := ξ) (rectAB a b) ha hb (hψc n ω)
  unfold lenObs
  calc (rectLen ξ (fun x => φ n x ω) (rectAB a b)).toReal
      ≤ (ENNReal.ofReal (exp (|ξ| * M)) * rectLen ξ (fun x => ψ n x ω) (rectAB a b)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h
    _ = exp (|ξ| * M) * (rectLen ξ (fun x => ψ n x ω) (rectAB a b)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le]

variable [IsProbabilityMeasure P]

/-- **(2.27), union-bound form**: `P(X_{a,b} > M) ≤ ε` implies
`ℓ^{(n)}_{a,b}(φ, p) ≤ e^{|ξ|M} ℓ^{(n)}_{a,b}(ψ, p + ε)`. -/
theorem ellQ_phi_le_of_tail (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ a b M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M) {ε p : ℝ≥0∞}
    (hε : P {ω | ENNReal.ofReal M <
      XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b} ≤ ε)
    (hp0 : 0 < p) (hp1 : p + ε < 1) (n : ℕ) :
    ellQ ξ P (phiMN W P 0 n) (rectAB a b) p ≤
      exp (|ξ| * M) * ellQ ξ P (psiMN Q W P 0 n) (rectAB a b) (p + ε) :=
  ellQ_le_of_le_off (isPhiVersion_phiMN hW (Nat.zero_le n)).cont
    (isPhiVersion_phiMN hW (Nat.zero_le n)).meas
    (isPsiVersion_psiMN hW (Nat.zero_le n)).cont (isPsiVersion_psiMN hW (Nat.zero_le n)).meas
    _ (exp_pos _).le hε (fun _ hω => lenObs_le_of_XAB_le
      (φ := fun n => phiMN W P 0 n) (ψ := fun n => psiMN Q W P 0 n)
      (fun n _ => (isPsiVersion_psiMN hW (Nat.zero_le n)).cont _) ha hb hM
      (not_lt.mp hω) n) hp0 hp1

/-- **(2.27), union-bound form, `φ ↔ ψ`**: `ℓ^{(n)}_{a,b}(ψ, p) ≤ e^{|ξ|M} ℓ^{(n)}_{a,b}(φ, p + ε)`. -/
theorem ellQ_psi_le_of_tail (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ a b M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M) {ε p : ℝ≥0∞}
    (hε : P {ω | ENNReal.ofReal M <
      XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b} ≤ ε)
    (hp0 : 0 < p) (hp1 : p + ε < 1) (n : ℕ) :
    ellQ ξ P (psiMN Q W P 0 n) (rectAB a b) p ≤
      exp (|ξ| * M) * ellQ ξ P (phiMN W P 0 n) (rectAB a b) (p + ε) :=
  ellQ_le_of_le_off (isPsiVersion_psiMN hW (Nat.zero_le n)).cont
    (isPsiVersion_psiMN hW (Nat.zero_le n)).meas
    (isPhiVersion_phiMN hW (Nat.zero_le n)).cont (isPhiVersion_phiMN hW (Nat.zero_le n)).meas
    _ (exp_pos _).le hε (fun _ hω => lenObs_le_of_XAB_le
      (φ := fun n => psiMN Q W P 0 n) (ψ := fun n => phiMN W P 0 n)
      (fun n _ => (isPhiVersion_phiMN hW (Nat.zero_le n)).cont _) ha hb hM
      (by rw [XAB_comm]; exact not_lt.mp hω) n) hp0 hp1

end DDDF
end LQGMetric
