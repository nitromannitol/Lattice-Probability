/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53UF5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53UF4

/-!
# DZZ Lemma 5.3 part 1, node 4 (`u`, `v` desirable), assembled (P2-DZZ53UF)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2516–2522: on the box chain of
`𝓔*` (S5L53L2), `P(l53UVBadBox ∩ {u, v good}) ≤ e^{−L^{0.22}}/2` for large `k` (`L = k log 2`,
`T = E log D̃_{2^{-l}}(u,v) + L^{0.98}`), from

* the per-point far bound and Markov with the cut-off (`l53uf_hbad`, S5L53UF3);
* the node-4 assembly `l53uf_UVBadBox_le` (S5L53UF2, copy of `l53UVBadBox_le`, S5L53M5);
* the numerics `l53uf_numerics` (S5L53UF4), `N = ⌊k C_mc⌋ + 2 n_{ε*}` (`l53uf_hN`),
  `ε*⁻¹ ≤ 2 e^{α* √L log L}` (`four_pow_epsStarN_le`, S3L12S3).

Explicit hypotheses: the domination event of P-131R (`hdom`, in flight in S5L53Z*) for the
node-4 proxies `l53ufM` with `P(Gᶜ) ≤ e^{−L^{0.23}}`; the scaling coupling of P-131S
(`hcpl = L53SimCoupleX`, the conclusion of `fineChaos_sim_couple`, S5L53X4, in flight); the
inputs `h317`, `hcor` of `l53_uv_far` (S5L53G6) as in P-131F (S5L53Y2).

**Superseded (2026-10-03):** off the route of the main theorem; see FN3 / handoff P2-DZZ53FIN (UF5 numerics copied into the FIN route; AUDIT-2026-10-03-P).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent DyBox

/-- `hN` of node 4 with `N = ⌊k C_mc⌋₊ + 2 n_{ε*}` -/
lemma l53uf_hN (γ αs : ℝ) (k : ℕ) : ∀ C : DyBox, ((2 : ℝ)⁻¹ ^ k) ^ dzzCmc γ ≤ C.side →
    C.n + 2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) ≤
      ⌊(k : ℝ) * dzzCmc γ⌋₊ + 2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) := by
  intro C hC
  have hl := Real.log_le_log (by positivity) hC
  rw [Real.log_rpow (by positivity), DyBox.side, Real.log_pow, Real.log_pow, Real.log_inv] at hl
  have h2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hn : (C.n : ℝ) ≤ (k : ℝ) * dzzCmc γ := by nlinarith
  have := Nat.le_floor hn
  omega

/-- `12 δ^{C_Mc} ≤ |v − u|` for large `k` -/
lemma l53uf_ev_hs (γ : ℝ) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ k : ℕ in atTop, 12 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ ≤ A := by
  have e : ∀ k : ℕ, ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ = ((2 : ℝ)⁻¹ ^ dzzCMc γ) ^ k := fun k => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹ ^ dzzCMc γ) (by positivity)
    (Real.rpow_lt_one (by norm_num) (by norm_num) (dzzCMc_pos γ))
  filter_upwards [(tendsto_order.1 ht).2 (A / 12) (by positivity)] with k hk
  rw [e]; linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

end DZZ
end LQGMetric
