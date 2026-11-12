/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53G4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G3

/-!
# DZZ Lemma 5.3, part 1, node 2: (eq-z-open) for dyadic sub-boxes (P2-DZZ53G)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2452–2502:
"For each `𝖡 ∈ 𝓑_i`, there is an event `𝓔_{𝖡,open}` which is measurable with respect to the field
`η̌^𝖡` so that `P(𝓔_{𝖡,open} | 𝓕*) ≥ 1 − O(K⁻²)` and `(𝓔_{𝖡,open} ∩ 𝓔₄) ⊆ {𝖡 is open}`."

* `closedBox_eq_sqBox`: `𝖡̄ = 𝕍_{c_𝖡, s_𝖡}`.
* **`l53_zopen_dyBox`**: (eq-z-open) for a family of dyadic boxes `B i` with boundary sets
  `Bd i ⊆ 𝖡̄_i` (DZZ: `∂𝖡_i`), local proxies `νB i` of the field (white noise in `R i`; DZZ:
  `M^{η̌^𝖡}` scaled by `δ² s_i^{-2} e^{(log δ⁻¹)^{0.91}}`), the per-pair far bound `p` (DZZ:
  `O(K⁻⁴)`), an `𝓕*`-type conditioning event `A₀` (white noise in `R₀`), and
  `a = b = K⁻¹𝓛₁(Bd i)`. The event `𝓔_{𝖡_i,open} = (l53ZBad (νB i) …)ᶜ`:
  1. is measurable for `W|_{R i}`;
  2. `P[𝓔_{𝖡_i,open}ᶜ | A₀] ≤ p K²` (DZZ: `O(K⁻²)`);
  3. the `𝓔_{𝖡_i,open}ᶜ` are independent under `P[·|A₀]` for pairwise disjoint regions;
  4. on `𝓔_{𝖡_i,open}` and the domination event (`ν ω ≤ νB i ω` on the balls inside
     `𝖡*_i = 𝕍_{c,5s}`, DZZ (eq-M-A-upper-bound-bis), part of `𝓔₄`), `𝖡_i` is open for
     `D^{K_w}[ν ω]` (any wall `K_w ⊇ 𝖡*_i`, e.g. `𝕍̃_{u,v}`) in the form `hopen` of
     `l53_open_chain` (S5L53E4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent DyBox

/-- The closed dyadic box is the closed square `𝕍_{c_𝖡, s_𝖡}`. -/
lemma closedBox_eq_sqBox (b : DyBox) : b.closedBox = sqBox b.center b.side := by
  ext z
  simp only [closedBox, sqBox, DyBox.center, mem_ofPred_eq, abs_le]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

end DZZ
end LQGMetric
