/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13G6 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13G5

/-!
# DZZ Lemma 3.13, cell geometry VI: assembling the box sequence along a good cell sequence (P2-DZZ313G)

DZZ arXiv:1807.00422 `LBM_LGDarXiv.tex` l. 1327–1331: along a good sequence of cells `𝖢_1, …, 𝖢_{d₀}` joining
`u` and `v`, concatenate the corridors of `𝒞_j` from `x_{j−1}` to `x_j` (doors of `exists_door`, corridors of
`exists_corridor`), starting at the box of `u` and ending with an arbitrary path in `𝒞_{d₀}` to the box of `v`.
In the first cell we use `x_0 = u` (the door square at `u` lies in `(𝖢_1)_large°`, controlled by the
goodness of `u`, as in DZZ's "arbitrary sequence of boxes in `𝒞_1`"); in the last cell the goodness of `v`.

`l313_assemble`: every box `B` of the sequence lies in a cell `𝖢` with `n_B = n_𝖢 + 2k` (`s_B = ε² s_𝖢`,
`ε = 2^{-k}`) and every `z ∈ 𝕍` within `ε s_𝖢/10` of `B` has `s_{z,δ} ≥ ε s_𝖢`; the length is
`≤ d₀ · 4^{2k}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma boxAt_mem_self {N : ℕ} {v : ℂ} (hv : v ∈ dzzV) : (boxAt N v).Mem v := ⟨hv, rfl⟩

end DZZ
end LQGMetric
