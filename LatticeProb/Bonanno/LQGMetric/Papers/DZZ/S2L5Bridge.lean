/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L5Bridge at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatRefl2
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSupp
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension

/-!
# DZZ Lemma 2.5, bridge part: `q(t; u, u) − q(t; u, v) = O(|u − v|/√t)` (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang, *Heat kernel for Liouville Brownian motion and Liouville graph distance*
(arXiv:1807.00422, `LBM_LGDarXiv.tex`), proof of Lemma 2.5 (`lem-variance-continuity`),
l. 466–508, following Rhodes–Vargas [RV14, Appendix A]:

* `bridgeStay_sub_le` (l. 476–502): for the open unit square `𝕍`,
  `q(t; u, u) − q(t; u, v) ≤ P(τ' ≤ t, τ > t) ≤ 12 |u − v|/√t`. As in DZZ the event is split
  along the four sides `𝕃_1, …, 𝕃_4` of `𝕍`; for each side the event is contained in
  `{max_{s ≤ t} (B_s − (s/t) B_t)_i ∈ [a, c]}` with `c − a ≤ |u − v|`, whose probability is
  `e^{−2a²/t} − e^{−2c²/t} ≤ 3(c − a)/√t` by the reflection principle
  (`measureReal_bridge_max_mem_Icc_le`, DZZ l. 491–498). The two lower sides use the
  maximum of `−(B_s − (s/t)B_t)`, again a planar bridge (`isPlanarBridge_neg`).
* `pi_killedHeat_sub_le` (l. 469–475): `π(p_𝕍(t; u, u) − p_𝕍(t; u, v)) ≤ 7 |u − v| t^{−3/2}`,
  using `1 − e^{−x} ≤ √x` (DZZ l. 472).

Bookkeeping (own, elementary): DZZ only treat `a > 0` in the reflection bound; for `a ≤ 0 < c`
we bound the band probability by `P(max ≤ c) = 1 − e^{−2c²/t} ≤ √2 c/√t ≤ 3(c − a)/√t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DZZ

open KilledHeat

variable {Ω : Type*} [MeasurableSpace Ω]

lemma coordProc_neg (X : ℝ≥0 → Ω → ℂ) :
    coordProc (fun s ω => -X s ω) = fun p ω => -coordProc X p ω := by
  funext p ω
  unfold coordProc
  split_ifs <;> simp

/-- The negative of a planar bridge is a planar bridge. -/
theorem isPlanarBridge_neg {t : ℝ≥0} {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) : IsPlanarBridge t (fun s ω => -X s ω) P where
  cont := hX.cont.mono fun _ h => h.neg
  gauss := by
    rw [coordProc_neg]
    exact hX.gauss.of_isGaussianProcess fun p => ⟨{p},
      -ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({p} : Finset (Bool × ℝ≥0)) => ℝ)
        ⟨p, by simp⟩, fun ω => rfl⟩
  mean p := by
    rw [coordProc_neg]
    simp only [integral_neg, hX.mean p, neg_zero]
  cov p q hp hq := by
    rw [coordProc_neg]
    show cov[-coordProc X p, -coordProc X q; P] = _
    rw [covariance_neg_left, covariance_neg_right, neg_neg, hX.cov p q hp hq]

omit [MeasurableSpace Ω] in
lemma coordProc_false (X : ℝ≥0 → Ω → ℂ) (s : ℝ≥0) (ω : Ω) :
    coordProc X (false, s) ω = (X s ω).re := by simp [coordProc]

omit [MeasurableSpace Ω] in
lemma coordProc_true (X : ℝ≥0 → Ω → ℂ) (s : ℝ≥0) (ω : Ω) :
    coordProc X (true, s) ω = (X s ω).im := by simp [coordProc]

end DZZ
end LQGMetric
