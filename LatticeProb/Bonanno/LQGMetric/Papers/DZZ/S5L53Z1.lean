/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53Z1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3EtaB3

/-!
# DZZ Lemma 5.3 part 1, R2: the domination (eq-M-A-upper-bound-bis), deterministic part
(P2-DZZ53Z, packet P-131R)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, (eq-M-A-upper-bound-bis) l. 2453–2456:
on `𝓔₄`, for every Borel `A ⊆ 𝖡 ∈ 𝓑_i`, `M_γ(A) ≤ δ² s_i^{−2} M_γ^{η̌^𝖡}(A) e^{(log δ⁻¹)^{0.91}}`.
With DV-D131-1 (decision D131 §3) the proxy chaos is DZZ's `M̃_{γ,s',η}` (`etaChaos`), `s' = 2^{-m}`.

This is the proof of (eq-M-tilde-B-bound) (l. 1116–1119) in the library,
`l32TildeMUpper_wickQArea` (S3EtaB3), **generalized** (near-miss reuse, preference (b)): there the
fine scale is `2^{-(n_B + 2 kL37)}` with `2^{2 kL37} ≤ (α L)²` and the field threshold is
`α √L log L`; here the fine scale `2^{-(n_B + j)}` is arbitrary with `2^j ≤ Y`, the threshold is a
free `T` (the event `nbrFineGen W X Y T`, S3L4Fine), and the sets are closed (and then open)
general closed sets (and, in S5L53Z3, rational balls) instead of dyadic boxes. The proof is the same comparison of the approximating
densities (copied from `l32TildeMUpper_wickQArea`, with `dens_compare_real_upper`,
`etaCV_le_of_nbrFine`, `tildeVar_ge_split` of S3EtaB2 reused verbatim):
`h̃_n ≤ η_n + √L` (eq-tilde-h-eta-assump), `η_n = η^{2^{-p}}_n + η_{2^{-p}}`,
`η_{2^{-p}}(z) ≤ η_{s_B}(c_B) + T`, `Var h̃_n ≥ Var η^{2^{-p}}_n + Var η_{s_B}(c_B) − V`, and the
cell mass `s_B² e^{γη_{s_B}(c_B) − γ²/2 Var} ≤ δ²`.

* `l53DomC γ δ T b₁ s := exp(γ(√L + T) + γ²/2 (b₁ + 2√5380 √(log s⁻¹ + 4)))`.
* **`l53_dens_le`**: the density comparison (the part of the proof that is not the limit step).
* `l53_wick_le_closed`: the domination on a closed set within `3 s_B` of `c_B` (limit step as a
  hypothesis, as in `wickGoodU`). The open-ball form through `ae_dzzMuIn_ball_le_proxyMass`
  (S5L53K2) is in S5L53Z3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4 SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the domination constant `exp(γ(√L + T) + γ²/2 (b₁ + 2√5380 √(log s⁻¹ + 4)))` -/
def l53DomC (γ δ T b₁ s : ℝ) : ℝ :=
  Real.exp (γ * (Real.sqrt (Real.log δ⁻¹) + T) +
    γ ^ 2 / 2 * (b₁ + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log s⁻¹ + 4)))

lemma l53DomC_pos (γ δ T b₁ s : ℝ) : 0 < l53DomC γ δ T b₁ s := Real.exp_pos _

/-- **the density comparison of (eq-M-A-upper-bound-bis)** (the pointwise part of the proof of
`l32TildeMUpper_wickQArea`, S3EtaB3, generalized): on `wickGoodU ∩ (eq-tilde-h-eta-assump) ∩
nbrFineGen W X Y T`, for a dyadic box `B` with `2^{n_B} ≤ X` and `M_{γ,s_B}(B) ≤ δ²`, every `j` with
`2^j ≤ Y` and `n ≥ n_B + j`: for a.e. `z ∈ 𝕍` with `|z − c_B| ≤ 5 s_B`,
`e^{γh̃_n(z) − γ²/2 Var} ≤ l53DomC · δ² s_B^{-2} · e^{γη^{2^{-(n_B+j)}}_n(z) − γ²/2 Var}`. -/
theorem l53_dens_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) {b₁ : ℝ}
    (hb₁ : ∀ (n : ℕ) (v : ℂ), |tildeVar ((1 / 2 : ℝ) ^ n) v - etaVar ((1 / 2 : ℝ) ^ n) v| ≤ b₁)
    {δ X Y T : ℝ} {ω : Ω} (hgood : ω ∈ wickGoodU hW γ) (hE27 : ω ∈ tildeEtaEvent hW δ)
    (hnbr : ω ∈ nbrFineGen W X Y T) {B : DyBox} (hX : (2 : ℝ) ^ B.n ≤ X)
    (happ : approxLQG γ W ω B ≤ δ ^ 2) {j : ℕ} (hY : (2 : ℝ) ^ j ≤ Y) {n : ℕ}
    (hn : B.n + j ≤ n) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ dzzV → ‖z - B.center‖ ≤ 5 * B.side →
      wickDensC hW γ n z ω ≤ ENNReal.ofReal (l53DomC γ δ T b₁ B.side * δ ^ 2 / B.side ^ 2) *
        etaDens W γ ((2 : ℝ)⁻¹ ^ (B.n + j)) n z ω := by
  set L := Real.log δ⁻¹ with hLdef
  have hs0 := DyBox.side_pos' B
  filter_upwards [hgood.2.1 (B.n + j) n hn] with z hz hzV hnorm
  have h1 : coarseVer hW n z ω ≤ etaCV hW n z ω + Real.sqrt L := by
    have := (abs_lt.1 (hE27 z hzV n)).2; linarith
  have h3 := etaCV_le_of_nbrFine hW hnbr hgood.1 hX hY hzV (by linarith)
  have h4 := tildeVar_ge_split hW hb₁ B (j := j) hn hnorm
  have h7 : B.side ^ 2 *
      Real.exp (γ * etaInf W B.side B.center ω - γ ^ 2 / 2 * etaVar B.side B.center) ≤ δ ^ 2 :=
    happ
  have hc0 : 0 ≤ l53DomC γ δ T b₁ B.side * δ ^ 2 / B.side ^ 2 := by
    have := l53DomC_pos γ δ T b₁ B.side; positivity
  unfold etaDens wickDensC
  rw [← ENNReal.ofReal_mul hc0]
  refine ENNReal.ofReal_le_ofReal ?_
  exact dens_compare_real_upper hγ h1 hz h3 h4 hs0 h7 le_rfl

end DZZ
end LQGMetric
