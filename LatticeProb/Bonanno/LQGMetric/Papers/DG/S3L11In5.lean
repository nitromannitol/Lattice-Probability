/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11In5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11In1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The exceptional event `Z` of DG Lemma 3.11 (P2-DG105l)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma 3.11 (DG:1226):
"Combining this with (eqn-gff-compare) (applied with `A = c n^{1/2}` for an appropriate constant
`c > 0`) and taking a union bound of `O_n(n²)` Euclidean balls of radius 1 whose union covers
`ℛ_n'`". In the formalization each grid square carries its own rescaled white noise `W'_x`
(D105, DV-D105g-3), and the comparison event is `max_K |hatMod'_x|, max_K |trMod'_x| ≤ A/2`.

* `sq_mul_exp_le`: `(n+1)² e^{−an} ≤ (8/a²) e^{a/2} e^{−an/2}`;
* **`prob_iUnion_tail_le`**: for `A_n = √(κ n)` and at most `N (n+1)²` squares (any family of
  white noises), `P[Z] ≤ a₂ e^{−a₃ n}`, with constants independent of the family
  (`hatTr_tail_uniform`, S3L11In1).

Own elementary glue (union bound).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the polynomial factor of the union bound is absorbed in the exponential -/
lemma sq_mul_exp_le {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 * Real.exp (-(a * n)) ≤
      (8 / a ^ 2 * Real.exp (a / 2)) * Real.exp (-(a / 2 * n)) := by
  set x := a * ((n : ℝ) + 1) / 2 with hxdef
  have hx : 0 ≤ x := by positivity
  have h1 : x ^ 2 / 2 ≤ Real.exp x :=
    le_trans (by nlinarith) (Real.quadratic_le_exp_of_nonneg hx)
  have h2 : ((n : ℝ) + 1) ^ 2 ≤ 8 / a ^ 2 * Real.exp x := by
    have e : ((n : ℝ) + 1) ^ 2 = 4 * x ^ 2 / a ^ 2 := by
      rw [hxdef]; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have e2 : 8 / a ^ 2 * Real.exp x * a ^ 2 = 8 * Real.exp x := by field_simp
    rw [e2]; linarith
  calc ((n : ℝ) + 1) ^ 2 * Real.exp (-(a * n))
      ≤ 8 / a ^ 2 * Real.exp x * Real.exp (-(a * n)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = _ := by
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
        congr 2
        rw [hxdef]; ring

/-- **`P[Z] ≤ a₂ e^{−a₃ n}`** (DG:1226): the union over at most `N (n+1)²` squares, each with its
own white noise `W' i`, of the comparison events at level `A_n = √(κ n)`. -/
theorem prob_iUnion_tail_le (hW : IsWhiteNoise P W) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) {κ : ℝ} (hκ : 0 < κ)
    {N : ℝ} (hN : 0 ≤ N) :
    ∃ a₂ a₃ : ℝ, 0 ≤ a₂ ∧ 0 < a₃ ∧ ∀ (n : ℕ) {ι : Type} (G : Finset ι)
      (W' : ι → WNSpace → Ω → ℝ) (hW' : ∀ i, IsWhiteNoise P (W' i)),
      (G.card : ℝ) ≤ N * ((n : ℝ) + 1) ^ 2 →
      P (⋃ i ∈ G, {ω | ¬ ∀ z ∈ ferniqueBox y b,
          |hatMod (hW' i) hb hK z ω| ≤ √(κ * n) / 2 ∧ |trMod (hW' i) hb hK z ω| ≤ √(κ * n) / 2})
        ≤ ENNReal.ofReal (a₂ * Real.exp (-(a₃ * n))) := by
  obtain ⟨c₀, c₁, hc₁, ht⟩ := hatTr_tail_uniform hW hb hK
  set a := c₁ * κ with ha
  have ha0 : 0 < a := mul_pos hc₁ hκ
  refine ⟨N * max c₀ 0 * (8 / a ^ 2 * Real.exp (a / 2)), a / 2, by positivity, by positivity,
    fun n ι G W' hW' hG => ?_⟩
  have hsq : √(κ * n) ^ 2 = κ * n := Real.sq_sqrt (by positivity)
  have hone : ∀ i, P {ω | ¬ ∀ z ∈ ferniqueBox y b,
      |hatMod (hW' i) hb hK z ω| ≤ √(κ * n) / 2 ∧ |trMod (hW' i) hb hK z ω| ≤ √(κ * n) / 2} ≤
      ENNReal.ofReal (max c₀ 0 * Real.exp (-(a * n))) := by
    intro i
    refine (ht (W' i) (hW' i) _ (Real.sqrt_nonneg _)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hsq, show -c₁ * (κ * n) = -(a * n) by rw [ha]; ring]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  calc _ ≤ ∑ i ∈ G, P {ω | ¬ ∀ z ∈ ferniqueBox y b,
        |hatMod (hW' i) hb hK z ω| ≤ √(κ * n) / 2 ∧ |trMod (hW' i) hb hK z ω| ≤ √(κ * n) / 2} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ G, ENNReal.ofReal (max c₀ 0 * Real.exp (-(a * n))) :=
        Finset.sum_le_sum fun i _ => hone i
    _ = ENNReal.ofReal (G.card * (max c₀ 0 * Real.exp (-(a * n)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (N * max c₀ 0 * (8 / a ^ 2 * Real.exp (a / 2)) *
          Real.exp (-(a / 2 * n))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hpos : 0 ≤ max c₀ 0 * Real.exp (-(a * n)) := by positivity
        calc (G.card : ℝ) * (max c₀ 0 * Real.exp (-(a * n)))
            ≤ N * ((n : ℝ) + 1) ^ 2 * (max c₀ 0 * Real.exp (-(a * n))) :=
              mul_le_mul_of_nonneg_right hG hpos
          _ = N * max c₀ 0 * (((n : ℝ) + 1) ^ 2 * Real.exp (-(a * n))) := by ring
          _ ≤ N * max c₀ 0 * ((8 / a ^ 2 * Real.exp (a / 2)) * Real.exp (-(a / 2 * n))) :=
              mul_le_mul_of_nonneg_left (sq_mul_exp_le ha0 n) (by positivity)
          _ = _ := by ring

end DG
end LQGMetric
