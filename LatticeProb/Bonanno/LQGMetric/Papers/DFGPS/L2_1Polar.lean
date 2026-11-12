/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1Polar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Tail
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.1: the GFF case from the polar formula

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:711–734: for a whole-plane GFF `g`
with circle-average process `g_r(z)`, since `ψ_ε` and `p_{ε²/2}` are radial about `z`,
`g*_ε(z) − ĝ*_ε(z) = (2/ε²) ∫_0^∞ r g_r(z) (1 − ψ_ε(r)) e^{−r²/ε²} dr` (the difference of the two
polar formulas T:719–722); with Lemma 2.2 (`ζ = 1/2`) the right side is
`≤ C K_A (2/ε²) e^{−1/(8ε)} → 0` uniformly in `z ∈ U` (T:726–733).

* `Lem2_1PolarDiff`: the polar formula for the difference, simultaneously for all `(ε, z)`,
  together with the existence of the limit defining `g*_ε(z)` (open node).
* `lem2_1GffApprox_of_polarDiff : Lem2_1PolarDiff → Lem2_1GffApprox` (the paper's tail argument,
  T:726–734, with `lem2_2`, `abs_polar_tail_le`, `tendsto_polarTailFac`).
* `lem2_1_of_polarDiff`: DFGPS Lemma 2.1 modulo `Lem2_1PolarDiff`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace LQGMetric.DFGPS

open LFPP

/-- **Polar formula for `g*_ε − ĝ*_ε`** (DFGPS T:719–722), for every jointly continuous version
`H` of the circle-average process of a whole-plane GFF, simultaneously in `(ε, z)`, together with
the existence of the limit defining `g*_ε(z)` (implicit in the paper). Open node. -/
def Lem2_1PolarDiff.{u} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (g : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ),
    IsWholePlaneGFF g P → IsCircleAvgVersion g P H →
    ∀ᵐ ω ∂P, ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ z : ℂ,
      (∃ L, Tendsto (fun n : ℕ => g ω (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 L)) ∧
      heatMollify ε (g ω) z - locMollify ε hε (g ω) z =
        2 / ε ^ 2 * ∫ r in Ioi 0, r * H r z ω * (1 - locBump ε hε (r : ℂ)) *
          Real.exp (-r ^ 2 / ε ^ 2)

/-- **The GFF case of (eqn-localized-approx) from the polar formula** (DFGPS T:726–734). -/
theorem lem2_1GffApprox_of_polarDiff.{u} (HP : Lem2_1PolarDiff.{u}) : Lem2_1GffApprox.{u} := by
  intro Ω _ P g hg U hU
  obtain ⟨H, hH⟩ := exists_isCircleAvgVersion hg
  obtain ⟨R, hR⟩ := hU.closure.subset_ball (0 : ℂ)
  set R' := max R 1
  have hR' : closure U ⊆ ball (0 : ℂ) R' := hR.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨A, hA, hAb⟩ := lem2_2 hg hH R'
  filter_upwards [HP P g H hg hH, hAb (1 / 2) (by norm_num)] with ω hω hC δ hδ
  obtain ⟨C, hC⟩ := hC
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R' := mem_ball_self (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hC0 : 0 ≤ C := by
    have := hC 1 one_pos 0 h0
    have hm : (1 : ℝ) ≤ max (max (A * Real.log (1 / 1)) (Real.log 1 ^ (1 / 2 + 1 / 2 : ℝ))) 1 :=
      le_max_right _ _
    by_contra hneg
    push Not at hneg
    have : C * max (max (A * Real.log (1 / 1)) (Real.log 1 ^ (1 / 2 + 1 / 2 : ℝ))) 1 < 0 :=
      mul_neg_of_neg_of_pos hneg (by linarith)
    linarith [abs_nonneg (H 1 0 ω)]
  have hlim : Tendsto (fun ε : ℝ => C * tailK A * (2 / ε ^ 2 * Real.exp (-(1 / (8 * ε)))))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_polarTailFac.const_mul (C * tailK A)
  have hle1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds one_pos)
  filter_upwards [hlim.eventually (ge_mem_nhds hδ), hle1] with ε hεδ hε1 hε z hz
  obtain ⟨hex, heq⟩ := hω ε hε z
  refine ⟨hex, ?_⟩
  rw [heq]
  refine (abs_polar_tail_le hA.le hC0 hε hε1 (F := fun r => H r z ω)
    (w := fun r => 1 - locBump ε hε (r : ℂ)) (fun r hr => hC r hr z (hR' hz))
    (fun r => by linarith [locBump_le_one ε hε (r : ℂ)])
    (fun r => by linarith [locBump_nonneg ε hε (r : ℂ)]) (fun r hr hrs => ?_)).trans hεδ
  rw [locBump_eq_one ε hε (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; exact hrs),
    sub_self]

end LQGMetric.DFGPS
