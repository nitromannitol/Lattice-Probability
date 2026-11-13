/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.VarBounds at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.LogCov

/-!
# Basic variance bounds: Lemma 3.0 and the single-measure bound (3.12′) (packet P-F2, target T4)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1), Lemma 3.4(a) and its uses in Lemma 4.1
("`Var H_root ≤ C_d` by the calculation in Lemma 3.4(a)") and (5.19); planning audit HA2
(`planning/audits/HA2-section-3.md`), findings HA2-12 and HA2-15, Details D1.4 ((F1), (F2)) and
D8(a); HA3 D3(a) (root variance).

* Lemma 3.0 for point masses, at the level of `scaleCov` (`k_{a,b,z}` is `bandVecM` of `δ_z`):
  - (F1) `scaleCov_dirac_zero`: `Cov(H_{a,b}(z), H_{a,b}(w)) = ∫_a^b C((z - w)/t) dt/t`, and
    `scaleCov_dirac_self`: `Var H_{a,b}(z) = log(b/a)`;
  - (F2) `exists_scaleCov_dirac_sub_le`: `E(H_{a,b}(z) - H_{a,b}(w))² ≤ L |z - w|² / a²` (every `b`).
* (3.12′) `single_measure_bound` (HA2-12): for a probability measure with the growth bound (3.4)
  at scale `1` and every measurable `S ⊆ (0, ∞)` of finite length, `⟨H_S, μ⟩` is defined and
  `Var⟨H_S, μ⟩ ≤ C |S|`; and (3.12) for differences, `Var⟨H_S, μ - ν⟩ ≤ 4 C |S|`
  (`pair_measure_bound`).  This covers the root variance `Var⟨H_{ε,1}, ν_{[0,e₁]}⟩ ≤ C` of
  Lemma 4.1 (HA3 D3(a)) and Lemma 3.4(a) (`scaleCov_fine_scales_le`).

Proof of (3.12′) (HA2 D8(a)): `|C| ≤ 1` and `supp C ⊆ B̄(0, 2ρ_κ)` give
`∫∫ C((z - w)/t) dμ dμ / t ≤ t⁻¹ sup_z μ(B̄(z, 2ρ_κ t)) ≤ 2ρ_κ B` at every scale `t > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ}

/-! ### Lemma 3.0: point masses -/

theorem isPairable_dirac_zero (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ) (z : Rd d) :
    IsPairable κ (Ioo a b) (Measure.dirac z) 0 := by
  rw [IsPairable, bandFun_dirac, bandFun_zero_measure, sub_zero]
  exact memLp_bandKernel hκ ha b z

/-! ### The single-measure bound (3.12′) -/

end HigherDimLFPP
