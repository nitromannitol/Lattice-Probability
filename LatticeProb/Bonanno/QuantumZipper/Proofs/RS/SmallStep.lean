/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.SmallStep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.TwoPoint

/-!
# EXT-RS D3: the small-time step of the reverse flow

For `δ ≥ 0`, `w ∈ H` and continuous `V`:
* `‖revMap V δ w − w‖ ≤ |V δ| + 2δ/Im w`, hence `≤ osc_{[0,δ]} V + 2δ/Im w` when `V 0 = 0`;
* `Im w ≤ Im (revMap V δ w)`;
* `‖(revMap V δ)' w‖ ≤ √(Im w² + 4δ)/Im w`.

Plays the role of Kemppainen, *Schramm–Loewner Evolution*, Lemma 6.7 (p. 110). The proof reads
the bounds off the integral form of the reverse Loewner equation (as in
`RegCont.norm_revMap_sub_self_le`) and the existing `TwoPoint.norm_deriv_revMap_le`,
`TwoPoint.im_revMap_sq_le`, `im_le_im_revMap`.

Note: in this project `revMap V 0 w = w − V 0`, so the oscillation bound needs `V 0 = 0`.
-/

noncomputable section

open Complex Set

namespace QuantumZipper
namespace RS

/-- **D3 (iii).** `‖(revMap V δ)' w‖ ≤ √(Im w² + 4δ)/Im w`. -/
theorem norm_deriv_revMap_le_sqrt {V : ℝ → ℝ} (hV : Continuous V) {δ : ℝ} (hδ : 0 ≤ δ)
    {w : ℂ} (hw : w ∈ H) : ‖deriv (revMap V δ) w‖ ≤ Real.sqrt (w.im ^ 2 + 4 * δ) / w.im := by
  have hw0 : 0 < w.im := hw
  refine (TwoPoint.norm_deriv_revMap_le hV hw hδ).trans ?_
  gcongr
  exact Real.le_sqrt_of_sq_le (TwoPoint.im_revMap_sq_le hV hw hδ)

end RS
end QuantumZipper
