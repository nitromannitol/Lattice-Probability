/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7Open at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7Mass

/-!
# DZZ Lemma 3.7: the band field and open boxes (P2-DZZ3D, WP-113)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) proof of Lemma 3.7, l. 973–995.

* `decompEvent W`: the a.s. event on which `η_{s_{B̃}}(c̃) = η_{2^{-N}}(c̃) + η^{2^{-N}}_{s_{B̃}}(c̃)`
  for all dyadic boxes `B̃` and all `N ≤` level of `B̃` (countably many identities);
  `ae_decompEvent`.
* `bandNorm γ W B̃ N ω = γ η^{2^{-N}}_{s_{B̃}}(c̃) − γ²/2 Var η^{2^{-N}}_{s_{B̃}}(c̃)` (the exponent in
  DZZ's display l. 975).
* `tail_bandNorm_finset`: union bound `P(∃ B̃ ∈ S, a ≤ bandNorm) ≤ |S| e^{−a}` (DZZ eq-berlin1,
  normalized form; see S3VarBdry for the DEVIATIONS note).
* `approxLQG_fine_le_of_mem`: DZZ l. 975 on `nbrFineEvent ∩ decompEvent ∩ {M_s(B) ≤ δ²}` and
  (eq-LQG-tilde-B-Phi) once `bandNorm ≤ a`.
* `boxOpen`: DZZ's `𝓔_{B'_i, open}` (l. 994), measurable w.r.t. the band field at the centres of
  `𝓑_∂(B'_i, t/ε)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The decomposition `η_{s_{B̃}} = η_{2^{-N}} + η^{2^{-N}}_{s_{B̃}}` at all dyadic centres. -/
def decompEvent (W : WNSpace → Ω → ℝ) : Set Ω :=
  {ω | ∀ (bt : DyBox) (N : ℕ), N ≤ bt.n → etaInf W bt.side bt.center ω =
    etaInf W ((2 : ℝ)⁻¹ ^ N) bt.center ω + eta W bt.side ((2 : ℝ)⁻¹ ^ N) bt.center ω}

theorem ae_decompEvent (hW : IsWhiteNoise P W) : ∀ᵐ ω ∂P, ω ∈ decompEvent W := by
  simp only [decompEvent, mem_ofPred_eq]
  rw [ae_all_iff]; intro bt
  rw [ae_all_iff]; intro N
  by_cases hN : N ≤ bt.n
  · filter_upwards [etaInf_eq_add_eta_ae hW (DyBox.side_pos' bt) (inv_two_pow_le_side hN)
      bt.center] with ω h _
    exact h
  · exact ae_of_all _ fun ω h => absurd h hN

/-- The normalized band exponent `γ η^{2^{-N}}_{s_{B̃}}(c̃) − γ²/2 Var η^{2^{-N}}_{s_{B̃}}(c̃)`. -/
def bandNorm (γ : ℝ) (W : WNSpace → Ω → ℝ) (bt : DyBox) (N : ℕ) (ω : Ω) : ℝ :=
  γ * eta W bt.side ((2 : ℝ)⁻¹ ^ N) bt.center ω -
    γ ^ 2 / 2 * etaBandVar bt.side ((2 : ℝ)⁻¹ ^ N) bt.center

/-- Union bound (DZZ eq-berlin1, normalized): `P(∃ B̃ ∈ S, a ≤ bandNorm) ≤ |S| e^{−a}`. -/
theorem tail_bandNorm_finset (hW : IsWhiteNoise P W) (S : Finset DyBox) (N : ℕ) (γ a : ℝ) :
    P.real {ω | ∃ bt ∈ S, a ≤ bandNorm γ W bt N ω} ≤ S.card * Real.exp (-a) := by
  have := hW.isProbabilityMeasure
  have hsub : {ω | ∃ bt ∈ S, a ≤ bandNorm γ W bt N ω} ⊆
      ⋃ bt ∈ S, {ω | a ≤ bandNorm γ W bt N ω} := by
    intro ω ⟨bt, hbt, h⟩
    exact mem_biUnion hbt h
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  calc ∑ bt ∈ S, P.real {ω | a ≤ bandNorm γ W bt N ω}
      ≤ ∑ _bt ∈ S, Real.exp (-a) :=
        Finset.sum_le_sum fun bt _ => tail_eta_normalized hW _ _ bt.center γ a
    _ = S.card * Real.exp (-a) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **DZZ l. 975 and (eq-LQG-tilde-B-Phi)**: on `nbrFineEvent ∩ decompEvent ∩ {M_s(B) ≤ δ²}`, a box
`B̃` of level `≥ m + j` (`2^j ≤ (α log δ⁻¹)²`, so `2^{-(m+j)} ≥ ε² s` in DZZ's notation) within
`8 s` of `c_B` with `bandNorm ≤ a` has
`M_{s_{B̃}}(B̃) ≤ δ² (s_{B̃}/s)² e^{γ α √L log L + γ²√8608 √(log s⁻¹ + 4)} e^{a}`. -/
theorem approxLQG_fine_le_of_mem (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    {Cmc α δ : ℝ} {ω : Ω} (hE : ω ∈ nbrFineEvent W Cmc α δ) (hdec : ω ∈ decompEvent W)
    {b bt : DyBox} {j : ℕ} (hm : (2 : ℝ) ^ b.n ≤ δ ^ (-Cmc))
    (hjY : (2 : ℝ) ^ j ≤ (α * Real.log δ⁻¹) ^ 2) (hj : b.n + j ≤ bt.n)
    (hc : ‖b.center - bt.center‖ ≤ 8 * b.side) (hM : approxLQG γ W ω b ≤ δ ^ 2) {a : ℝ}
    (ha : bandNorm γ W bt (b.n + j) ω ≤ a) :
    approxLQG γ W ω bt ≤ δ ^ 2 * (bt.side / b.side) ^ 2 *
      Real.exp (γ * (α * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)) +
        γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log b.side⁻¹ + 4))) * Real.exp a := by
  have hT := hE b.n j hm hjY b bt rfl hj hc
  have h := approxLQG_fine_le hW hγ hj hc hT (hdec bt (b.n + j) hj) hM
  refine h.trans ?_
  gcongr
  exact ha

/-- DZZ's `𝓔_{B', open}` (l. 994): the normalized band exponent is `< a` at every box of
`𝓑_∂(B', 2^{-k'})`; the band is `η^{2^{-N}}_{·}`. -/
def boxOpen (γ : ℝ) (W : WNSpace → Ω → ℝ) (B' : DyBox) (k' N : ℕ) (a : ℝ) : Set Ω :=
  {ω | ∀ bt ∈ boxCollBdry B' k', bandNorm γ W bt N ω < a}

end DZZ
end LQGMetric
