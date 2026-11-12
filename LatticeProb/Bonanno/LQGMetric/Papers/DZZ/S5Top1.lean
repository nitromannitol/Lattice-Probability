/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Top1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117
import LatticeProb.Bonanno.LQGMetric.Topo.SectorRect

/-!
# D117 P-GLUE (1): the rectangle crossing lemma `DZZCrossLemma`

DZZ = Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2566–2567 and 2605
(Fig. glue: "four short crossings through four rectangles … which altogether form a contour
enclosing `L_δ`"). The deterministic core is the lemma of R. Maehara, *The Jordan curve theorem
via the Brouwer fixed point theorem*, Amer. Math. Monthly 91 (1984), Lemma 1: a left–right and a
bottom–top crossing of a closed rectangle meet.

Reuse: the path version is `RectMeet.rect_crossings_meet` (2-d Poincaré–Miranda via the loop
degree of QuantumZipper), and its continuum version `Sector.lr_tb_meet` (compact preconnected
sets). Here we only pass from path-connected sets to the compact ranges of joining paths.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric
namespace DZZ

open Set

/-- A path-connected set meeting two points contains a compact connected set through both. -/
theorem exists_compact_conn_of_pathConn {S : Set ℂ} (hS : IsPathConnected S) {p q : ℂ}
    (hp : p ∈ S) (hq : q ∈ S) :
    ∃ L : Set ℂ, IsCompact L ∧ IsPreconnected L ∧ L ⊆ S ∧ p ∈ L ∧ q ∈ L := by
  have hj := hS.joinedIn p hp q hq
  refine ⟨range hj.somePath, isCompact_range hj.somePath.continuous,
    (isConnected_range hj.somePath.continuous).isPreconnected, ?_, ⟨0, by simp⟩, ⟨1, by simp⟩⟩
  rintro _ ⟨t, rfl⟩
  exact hj.somePath_mem t

end DZZ
end LQGMetric
