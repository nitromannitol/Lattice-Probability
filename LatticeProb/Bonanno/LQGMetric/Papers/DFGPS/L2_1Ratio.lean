/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1Ratio at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.LocalizedCont
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylLower

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.1, last step: uniform closeness of the fields gives `D̂^ε/D^ε → 1`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:697 and T:741: "The relation
(eqn-localized-lfpp-approx) is immediate from (eqn-localized-lfpp) and the definition of LFPP."
(Denominator read as `D^ε_𝗁`, DEV-DFGPS-3.)

`lfppDOn_le_of_abs_sub_le`: if `|φ' − φ| ≤ δ` on `S`, then `D^{φ'}(z, w; S) ≤ e^{|ξ|δ} D^φ(z, w; S)`
(pointwise comparison of the integrands along paths in `S`; own elementary argument, as in
`LFPP/WeylBounds.lean`). `lem2_1_ratio`: if `sup_{U} |h*_ε − ĥ*_ε| → 0` as `ε → 0`, then
`D̂^ε_h(z, w; U)/D^ε_h(z, w; U) → 1` uniformly in `z, w ∈ U`, in the two-sided multiplicative
form `c⁻¹ D^ε ≤ D̂^ε ≤ c D^ε` for every `c > 1` and all small `ε` (this form is meaningful also
where the distances are `0` or `∞`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS

open LFPP

theorem lfppDOn_le_of_abs_sub_le {ξ : ℝ} {φ φ' : ℂ → ℝ} {S : Set ℂ} {δ : ℝ}
    (hδ : ∀ x ∈ S, |φ' x - φ x| ≤ δ) (z w : ℂ) :
    lfppDOn ξ φ' S z w ≤ ENNReal.ofReal (Real.exp (|ξ| * δ)) * lfppDOn ξ φ S z w := by
  unfold lfppDOn
  rw [ENNReal.mul_iInf_of_ne (by simpa using Real.exp_pos _) ENNReal.ofReal_ne_top]
  refine iInf_mono fun P => ?_
  rw [lfppLen_eq, lfppLen_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
  have e : lenDens ξ φ' P.1 s = lenDens ξ (fun x => φ x + (φ' x - φ x)) P.1 s := by
    simp only [add_sub_cancel]
  rw [e, lenDens_add]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl
  calc ξ * (φ' (P.1 s) - φ (P.1 s)) ≤ |ξ * (φ' (P.1 s) - φ (P.1 s))| := le_abs_self _
    _ = |ξ| * |φ' (P.1 s) - φ (P.1 s)| := abs_mul _ _
    _ ≤ |ξ| * δ := mul_le_mul_of_nonneg_left (hδ _ (P.2.2 s hs)) (abs_nonneg _)

/-- **DFGPS Lemma 2.1, (eqn-localized-lfpp-approx) from (eqn-localized-approx)** (T:697, 741),
deterministic form: if `sup_{z ∈ U} |h*_ε(z) − ĥ*_ε(z)| → 0` as `ε → 0`, then for every `c > 1`,
for all small `ε`, `c⁻¹ D^ε_h(z, w; U) ≤ D̂^ε_h(z, w; U) ≤ c D^ε_h(z, w; U)` for all `z, w`. -/
theorem lem2_1_ratio (ξ : ℝ) (h : DistC) (U : Set ℂ)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z ∈ U,
      |heatMollify ε h z - locMollify ε hε h z| ≤ δ)
    {c : ℝ} (hc : 1 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z w : ℂ,
      lfppLocOn ξ ε hε h U z w ≤ ENNReal.ofReal c * lfppDOn ξ (heatMollify ε h) U z w ∧
      lfppDOn ξ (heatMollify ε h) U z w ≤ ENNReal.ofReal c * lfppLocOn ξ ε hε h U z w := by
  have hlc : 0 < Real.log c := Real.log_pos hc
  set δ : ℝ := Real.log c / (|ξ| + 1)
  have hδ : 0 < δ := by positivity
  have hexp : Real.exp (|ξ| * δ) ≤ c := by
    have : |ξ| * δ ≤ Real.log c := by
      simp only [δ]; rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg ξ]
    calc Real.exp (|ξ| * δ) ≤ Real.exp (Real.log c) := Real.exp_le_exp.2 this
      _ = c := Real.exp_log (by linarith)
  filter_upwards [hconv δ hδ] with ε hε0 hε z w
  have h1 := lfppDOn_le_of_abs_sub_le (ξ := ξ) (φ := heatMollify ε h) (φ' := locMollify ε hε h)
    (S := U) (δ := δ) (fun x hx => by rw [abs_sub_comm]; exact hε0 hε x hx) z w
  have h2 := lfppDOn_le_of_abs_sub_le (ξ := ξ) (φ := locMollify ε hε h) (φ' := heatMollify ε h)
    (S := U) (δ := δ) (fun x hx => hε0 hε x hx) z w
  have hm : ENNReal.ofReal (Real.exp (|ξ| * δ)) ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hexp
  exact ⟨h1.trans (mul_le_mul_left hm _), h2.trans (mul_le_mul_left hm _)⟩

end LQGMetric.DFGPS
