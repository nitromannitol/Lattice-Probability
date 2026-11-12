/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8FinSetup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinMed
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinTight
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8Couple
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffZB
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofF
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8, GFF case on `[0,1]²`: the common setup (T:876–891)

For a whole-plane GFF `g` (any additive constant) this file assembles, on one probability space,
the objects of the proof of DFGPS Lemma 2.8 (T:876–891):

* the Markov coupling of `g` with a zero-boundary GFF on `(-1,2)²` (`markov_zb_coupling`, centre
  `0`, radius `4`), DDDF's zero-boundary versions `Y` and their tightness/positivity (`zb_step`,
  with a white noise from `exists_isWhiteNoise` defining `λ_ε`);
* the per-`ε` comparison `sup_{[0,1]²} |g*_ε − Y_{ε²}| ≤ M` with probability `≥ 1 − ζ`
  (`gff_zb_field_prob`);
* the bounds `C⁻¹ λ_ε ≤ 𝔞_ε ≤ C λ_ε` for small `ε` (`aEps_lambda_bounds`, applied to the
  normalized field `g − g_1(0)` and its own coupling: `𝔞_ε`, `λ_ε` are deterministic).

`unitSq_setup` packages these facts; `L2_8FinAsm.lean` derives tightness and positivity.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP HeatSq WhiteNoise DDDF

lemma disjoint_sqOpen_sphere : Disjoint (sqOpen (-1) 3) (sphere (0 : ℂ) 4) := by
  rw [Set.disjoint_left]
  intro z ⟨h1, h2, h3, h4⟩ hz
  rw [mem_sphere, dist_zero_right] at hz
  have := Complex.norm_le_abs_re_add_abs_im z
  have a1 : |z.re| < 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  have a2 : |z.im| < 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  linarith

end LQGMetric.DFGPS
