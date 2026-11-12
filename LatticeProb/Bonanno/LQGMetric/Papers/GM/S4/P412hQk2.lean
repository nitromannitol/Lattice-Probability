/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412hQk2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412hQk1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412gCentre

/-!
# The guard centres of GM L4.15 Step 3 (D98 §2, packet P-Qk, part 2)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 3, l. 2155–2183 (the
points `z_y`, `y ∈ 𝒴_k`, with (∗), chosen depending only on `(𝓑^•_{t_k}, h|)`, at most
`#𝒴_k` of them); GM.S4.1 (l. 1648–1654); decision D98 §2 (route (ii)).

With `ε' = ε^κ𝕣`, the grid `g i = (ε'/8)·m_i` (`m_i` an enumeration of `ℤ²`) and
`Q_k = {i | #Conf_k ≤ L, ∃ e ∈ 𝒴_k, gd(𝓑^•_{t_k}, e) = g i}`:
* `{i ∈ Q_k}` is a.s. an event of `σ(𝓑^•_{t_k}, h|)` (`p412h_Xq_aeEventIn`,
  `p412i_confCount_aeEventIn`);
* a.s. `#Q_k ≤ #𝒴_k ≤ 2#Conf_k ≤ 2L` (`gd` is a function of `e`; `p412f_endSet_encard`);
* `p412g_grid_centres` (radius `8ε'`) gives `2L` surely measurable centres on `∂𝓑^•_{t_k}`,
  and by `p412h_goodZ_filled` the centre attached to `gd(𝓑^•_{t_k}, e)` satisfies (∗) for `e`.
**`p412h_centres`**: the conclusion of `P412jCentres` (with `z := x_j`), under the extra
hypothesis that `𝓑^•_{t_k}` is bounded for every `ω` (needed by `p412g_grid_centres` for centres
on `∂𝓑^•_{t_k}` at every `ω`; see the report).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology Bornology
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

theorem p412h_gd_grid (K : Set ℂ) (y : ℂ) (ε : ℝ) : ∃ m, p412hGd K y ε = p412hG ε m := by
  unfold p412hGd
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem p412h_G_inj {ε : ℝ} (hε : ε ≠ 0) : Function.Injective (p412hG ε) := by
  intro m n hmn
  have h8 : ((ε / 8 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast div_ne_zero hε (by norm_num)
  have e := mul_left_cancel₀ h8 hmn
  have h1 := congrArg Complex.re e
  have h2 := congrArg Complex.im e
  simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.intCast_im,
    Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im] at h1 h2
  norm_num at h1 h2
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

end LQGMetric.GM
