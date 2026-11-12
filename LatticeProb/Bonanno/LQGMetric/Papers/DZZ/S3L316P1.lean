/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L316P1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinCore

/-!
# DZZ Lemma 3.16, (eq-B-percolation): the percolation step (P2-DZZ316)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1381–1404 (proof of Lemma 3.16):
"the percolation argument in Lemma 3.7 yields (eq-B-percolation)", with `t = ε*` and
`{M_s(B) ≤ δ²} ∩ 𝓔_{δ,α} ∩ 𝓔_{B'_i, open} ⊆ {M_{ε* s}(B̃) ≤ δ² : B̃ ∈ 𝓑'_i}`.

* `l316_enc_open`: the Peierls step of `l37_enc_core` (P2-DZZ3F, l. 990–1015) with the good
  predicate `𝓔_{B'_i, open}` itself: outside an event of probability
  `≤ 4 (2N+1) (8θ)^{N-n+1}` there is an enclosure of `B` by open boxes of `𝓑(B, 2^{-k})`.
  (Same proof as `l37_enc_core`, stopping before `psiLe_of_boxOpen`.)
* `approxLQG_lt_of_boxOpen`: the displayed inclusion of DZZ l. 1393–1396 (with `δ' = δ`): on
  `𝓔_{δ,α} ∩ decompEvent ∩ {M_s(B) ≤ δ²}`, every box of `𝓑_∂(B'_i, 2^{-k''})` of an open
  `B'_i` has `M < δ²` (as in `psiLe_of_boxOpen`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ l. 1393–1396** (`δ' = δ`): open boxes have all their boundary boxes of mass `< δ²`. -/
theorem approxLQG_lt_of_boxOpen (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    {Cmc α δ a : ℝ} {ω : Ω} (hE : ω ∈ nbrFineEvent W Cmc α δ) (hdec : ω ∈ decompEvent W)
    {B B' : DyBox} {k k'' j : ℕ} (hm : (2 : ℝ) ^ B.n ≤ δ ^ (-Cmc))
    (hjY : (2 : ℝ) ^ j ≤ (α * Real.log δ⁻¹) ^ 2) (hjk : j ≤ k + k'')
    (hM : approxLQG γ W ω B ≤ δ ^ 2) (hB' : B' ∈ boxColl B k)
    (hopen : ω ∈ boxOpen γ W B' k'' (B.n + j) a)
    (hsmall : δ ^ 2 * ((2 : ℝ)⁻¹ ^ (k + k'')) ^ 2 *
      Real.exp (γ * (α * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)) +
        γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log B.side⁻¹ + 4))) * Real.exp a <
      δ ^ 2) :
    ∀ bt ∈ boxCollBdry B' k'', approxLQG γ W ω bt < δ ^ 2 := by
  intro bt hbt
  have hj : B.n + j ≤ bt.n := by rw [hbt.1, hB'.1]; omega
  refine (approxLQG_fine_le_of_mem hW hγ hE hdec hm hjY hj (center_near_of_boxColl hB' hbt) hM
    (hopen bt hbt).le).trans_lt ?_
  rwa [side_div_of_boxColl hB' hbt]

end DZZ
end LQGMetric
