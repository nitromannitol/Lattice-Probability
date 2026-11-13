/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.UStarMoments at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Theorem44

/-!
# Moments of the localized density `u^ε_*`

Source: [18] proof of Lemma 4.9 : "The larger range of possible values of
`p` in (4.24) as compared to (4.25) is due to the difference in the range of possible `p` values in Theorem 4.4", and the
last step "apply Theorem 4.4 with `ε̂` in place of `ε` to get `E[X̂^{p′}_{a₁,a₂}] ≲ 1` for each `p′ ∈ (1, 4/γ²)`", where
`X̂ = u^{ε̂}_*(0) 1(…)` and `u_* = DA (deg_in + deg_out)` (4.19).

`theorem44_uStar_holds`: under the hypotheses of Theorem 4.4, for `p ∈ [1, 4/γ²)` the moments
`E[u^ε_*(0)^p]` are bounded uniformly in `ε > 0` (Hölder with exponents `s ∈ (1, (4/γ²)/p)` and `s/(s − 1)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-- **Uniform moments of `u^ε_*(0)`**. Under `CurveScaleInvariant` and `UnitCellMoments`, for every
`p ∈ [1, 4/γ²)` there is a finite `C` with `E[u^ε_*(0)^p] ≤ C` for all `ε > 0` (root time `0`). -/
theorem theorem44_uStar_holds {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : Ω → C(ℝ, ℂ)} {γ : ℝ}
    (hη : Measurable η) (hscale : CurveScaleInvariant P η) (hmom : UnitCellMoments γ P η) :
    ∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, locUStar ε (η ω) 0 ^ p ∂P ≤ C := by
  intro p hp hpK
  set K : ℝ := 4 / γ ^ 2 with hK
  have hp0 : 0 < p := by linarith
  set s : ℝ := (1 + K / p) / 2 with hs
  have hKp : 1 < K / p := by rw [lt_div_iff₀ hp0]; linarith
  have hs1 : 1 < s := by rw [hs]; linarith
  have hps : p * s < K := by
    rw [hs, mul_div_assoc', mul_add, mul_one, mul_div_cancel₀ _ hp0.ne']
    linarith
  set r : ℝ := s.conjExponent with hr
  have hsr : s.HolderConjugate r := Real.HolderConjugate.conjExponent hs1
  have hr1 : 1 < r := hsr.symm.lt
  have hps1 : 1 ≤ p * s := by nlinarith
  have hpr1 : 1 ≤ p * r := by nlinarith
  have hcoe : Measurable fun n : ℕ∞ => (n : ℝ≥0∞) := measurable_of_countable _
  -- the degree sum and the area ratio at mesh `ε`
  set S : ℝ → Ω → ℝ≥0∞ := fun ε ω => ((locDegIn ε (η ω) 0 + locDegOut ε (η ω) 0 : ℕ∞) : ℝ≥0∞) with hS
  set D : ℝ → Ω → ℝ≥0∞ := fun ε ω => locDA ε (η ω) 0 with hD
  have hSm : ∀ ε : ℝ, 0 ≤ ε → Measurable (S ε) := fun ε hε =>
    hcoe.comp ((measurable_of_countable (fun x : ℕ∞ × ℕ∞ => x.1 + x.2)).comp
      (((measurable_locDegIn ε 0).comp hη).prodMk ((measurable_locDegOut hε 0).comp hη)))
  have hDm : ∀ ε : ℝ, Measurable (D ε) := fun ε => (measurable_locDA ε 0).comp hη
  -- transport of the two moments from mesh `ε` to mesh `1`
  have hSeq : ∀ ε : ℝ, 0 < ε → ∫⁻ ω, S ε ω ^ (p * s) ∂P = ∫⁻ ω, S 1 ω ^ (p * s) ∂P := by
    intro ε hε
    exact lintegral_localTriple_eq hη hscale hε
      (F := fun x => ((x.2.1 + x.2.2 : ℕ∞) : ℝ≥0∞) ^ (p * s))
      ((ENNReal.continuous_rpow_const.measurable).comp (hcoe.comp
        ((measurable_of_countable (fun x : ℕ∞ × ℕ∞ => x.1 + x.2)).comp measurable_snd)))
  have hDeq : ∀ ε : ℝ, 0 < ε → ∫⁻ ω, D ε ω ^ (p * r) ∂P = ∫⁻ ω, D 1 ω ^ (p * r) ∂P := by
    intro ε hε
    exact lintegral_localTriple_eq hη hscale hε (F := fun x => x.1 ^ (p * r))
      ((ENNReal.continuous_rpow_const.measurable).comp measurable_fst)
  -- finiteness at mesh `1`
  have hSfin : ∫⁻ ω, S 1 ω ^ (p * s) ∂P < ⊤ := by
    have hle : ∀ ω, S 1 ω ^ (p * s) ≤ (2 : ℝ≥0∞) ^ (p * s - 1) *
        (((locDegIn 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s) + ((locDegOut 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s)) := by
      intro ω
      simp only [hS, ENat.toENNReal_add]
      exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hps1
    have hm1 : Measurable fun ω => ((locDegIn 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s) :=
      (ENNReal.continuous_rpow_const.measurable).comp (hcoe.comp ((measurable_locDegIn 1 0).comp hη))
    have hm2 : Measurable fun ω => ((locDegOut 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s) :=
      (ENNReal.continuous_rpow_const.measurable).comp
        (hcoe.comp ((measurable_locDegOut zero_le_one 0).comp hη))
    refine (lintegral_mono hle).trans_lt ?_
    have hm12 : Measurable fun ω => ((locDegIn 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s) +
        ((locDegOut 1 (η ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s) := hm1.add hm2
    rw [lintegral_const_mul _ hm12, lintegral_add_left hm1]
    refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top) ?_
    exact ENNReal.add_lt_top.mpr ⟨hmom.2.1 _ hps1 hps, hmom.2.2 _ hps1⟩
  have hDfin : ∫⁻ ω, D 1 ω ^ (p * r) ∂P < ⊤ := hmom.1 _ hpr1
  refine ⟨(∫⁻ ω, S 1 ω ^ (p * s) ∂P) ^ (1 / s) * (∫⁻ ω, D 1 ω ^ (p * r) ∂P) ^ (1 / r), ?_, ?_⟩
  · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hSfin.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hDfin.ne)
  · intro ε hε
    have hsplit : ∀ ω, locUStar ε (η ω) 0 ^ p = (fun ω => S ε ω ^ p) ω * (fun ω => D ε ω ^ p) ω := by
      intro ω
      simp only [hS, hD, locUStar]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, mul_comm]
    simp_rw [hsplit]
    have hf : Measurable fun ω => S ε ω ^ p :=
      (ENNReal.continuous_rpow_const.measurable).comp (hSm ε hε.le)
    have hg : Measurable fun ω => D ε ω ^ p := (ENNReal.continuous_rpow_const.measurable).comp (hDm ε)
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P hsr hf.aemeasurable hg.aemeasurable
    refine hH.trans (le_of_eq ?_)
    simp only [← ENNReal.rpow_mul]
    rw [hSeq ε hε, hDeq ε hε]

end MatedCRTHarmonic.GMS4b
