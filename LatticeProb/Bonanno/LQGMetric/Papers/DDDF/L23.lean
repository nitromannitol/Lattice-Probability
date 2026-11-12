/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L23 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L23Gauss
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L23Var
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L23Disc
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.GaussFdd
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePhi

/-!
# DDDF Lemma 23: `Var log L^{(n)}_{1,1}(φ) ≤ ξ² (n+1) log 2`

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1036–1056 (`Lem:VarApriori`; blueprint node DDDF.L23). We follow DDDF's proof:

1. `L^{(n)}_{1,1}(D_k)`, the crossing length for the field that is piecewise constant on the
   dyadic blocks of size `2^{-k}` with the centre values of `φ_{0,n}` (`L23.discLogLen`,
   `L23Disc.lean`), converges to `L^{(n)}_{1,1}(φ)` (l. 1043–1047; `L23.tendsto_logLen_snap`);
2. `log L^{(n)}_{1,1}(D_k)` is a `ξ`-Lipschitz function, for the sup metric, of the `4^k`
   jointly Gaussian centre values `Y` (l. 1050; `L23.lipschitzWith_discLogLen`), so by Gaussian
   concentration "applied as in [DD18, Lemma 5.8]" its variance is at most
   `ξ² max_i Var Y_i = ξ² n log 2` (l. 1050–1055; `GaussConc.variance_le_of_lipschitz_vector`,
   `L23Gauss.lean`);
3. the variance bound passes to the limit (l. 1047–1049; DDDF: dominated convergence; we use
   Fatou, `L23.memLp_variance_le_of_tendsto`, `L23Var.lean`).

`Var φ_{0,n}(x) = log 2^n = n log 2` (`variance_phi_delta`), so we get `ξ² n log 2`
(`dddf_lemma23_sharp`), which implies DDDF's stated `ξ² (n+1) log 2` (`dddf_lemma23`). We also
record `log L^{(n)}_{1,1}(φ) ∈ L²`, which DDDF use implicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

namespace L23

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `GaussConc.variance_le_of_lipschitz_vector` for any finite index type, plus `L²`. -/
theorem memLp_variance_le_fintype {ι : Type*} [Fintype ι] {Y : Ω → ι → ℝ}
    (hY : HasGaussianLaw Y P) (h0 : ∀ i, ∫ ω, Y ω i ∂P = 0) {s : ℝ} (hs : 0 ≤ s)
    (hvar : ∀ i, Var[fun ω => Y ω i; P] ≤ s) {g : (ι → ℝ) → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    MemLp (fun ω => g (Y ω)) 2 P ∧ Var[fun ω => g (Y ω); P] ≤ (K : ℝ) ^ 2 * s := by
  have := hY.isProbabilityMeasure
  constructor
  · have hY2 : MemLp Y 2 P := hY.memLp_two
    have hn : MemLp (fun ω => (K : ℝ) * ‖Y ω‖) 2 P := hY2.norm.const_mul _
    have hb : MemLp (fun ω => |g 0| + (K : ℝ) * ‖Y ω‖) 2 P := (memLp_const (|g 0|)).add hn
    refine hb.of_le (hg.continuous.measurable.comp_aemeasurable hY.aemeasurable).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have hpos : 0 ≤ |g 0| + (K : ℝ) * ‖Y ω‖ := by positivity
    rw [Real.norm_eq_abs (g (Y ω)), Real.norm_of_nonneg hpos]
    have h1 := hg.dist_le_mul (Y ω) 0
    rw [Real.dist_eq, dist_zero_right] at h1
    have := abs_sub_abs_le_abs_sub (g (Y ω)) (g 0)
    linarith
  obtain ⟨N, ⟨e⟩⟩ : ∃ N : ℕ, Nonempty (ι ≃ Fin N) := ⟨_, ⟨Fintype.equivFin ι⟩⟩
  let L : (ι → ℝ) →L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm j)
  let Y' : Ω → Fin N → ℝ := fun ω j => Y ω (e.symm j)
  have hY' : HasGaussianLaw Y' P := hY.map L
  let g' : (Fin N → ℝ) → ℝ := fun z => g fun i => z (e i)
  have hT : LipschitzWith 1 fun (z : Fin N → ℝ) (i : ι) => z (e i) :=
    LipschitzWith.of_dist_le_mul fun z z' => by
      rw [NNReal.coe_one, one_mul]
      exact (dist_pi_le_iff dist_nonneg).2 fun i => dist_le_pi_dist z z' (e i)
  have hg' : LipschitzWith K g' := by
    have h := hg.comp hT; rw [mul_one] at h; exact h
  have hfun : (fun ω => g (Y ω)) = fun ω => g' (Y' ω) := by
    funext ω; simp [g', Y']
  obtain ⟨s', hs'⟩ : ∃ s', s' = ⨆ j, Var[fun ω => Y' ω j; P] := ⟨_, rfl⟩
  have hs'0 : 0 ≤ s' := hs' ▸ Real.iSup_nonneg fun j => variance_nonneg _ _
  have hs's : s' ≤ s := hs' ▸ Real.iSup_le (fun j => hvar (e.symm j)) hs
  have hv := GaussConc.variance_le_of_lipschitz_vector hY' (fun j => h0 (e.symm j))
    (Real.sqrt_nonneg s') (by rw [Real.sq_sqrt hs'0, hs']) hg'
  rw [Real.sq_sqrt hs'0] at hv
  rw [hfun]
  exact hv.trans (mul_le_mul_of_nonneg_left hs's (sq_nonneg _))

variable {W : WNSpace → Ω → ℝ}

/-- the centre values of `φ_{0,n}` are centered with variance `n log 2` -/
lemma integral_variance_phiMN (hW : IsWhiteNoise P W) (n : ℕ) (x : ℂ) :
    ∫ ω, phiMN W P 0 n x ω ∂P = 0 ∧ Var[phiMN W P 0 n x; P] = n * Real.log 2 := by
  have h := (isPhiVersion_phiMN hW (Nat.zero_le n)).ae_eq x
  simp only [pow_zero] at h
  refine ⟨by rw [integral_congr_ae h, integral_phi hW], ?_⟩
  rw [variance_congr h, variance_phi_delta hW (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)) x, inv_pow, inv_inv, Real.log_pow]

end L23

open L23

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace L23

lemma disc_memLp_variance (hW : IsWhiteNoise P W) (ξ : ℝ) (n k : ℕ) :
    MemLp (fun ω => discLogLen ξ k fun c => phiMN W P 0 n c ω) 2 P ∧
      Var[fun ω => discLogLen ξ k fun c => phiMN W P 0 n c ω; P] ≤
        ξ ^ 2 * (n * Real.log 2) := by
  have h := memLp_variance_le_fintype (hasGaussianLaw_phiMN hW (Nat.zero_le n) (grid k))
    (fun c => (integral_variance_phiMN hW n c).1) (by positivity)
    (fun c => (integral_variance_phiMN hW n c).2.le) (lipschitzWith_discLogLen ξ k)
  rwa [coe_nnnorm, Real.norm_eq_abs, sq_abs] at h

lemma disc_measurable (hW : IsWhiteNoise P W) (ξ : ℝ) (n k : ℕ) :
    Measurable fun ω => discLogLen ξ k fun c => phiMN W P 0 n c ω :=
  (lipschitzWith_discLogLen ξ k).continuous.measurable.comp
    (measurable_pi_iff.2 fun c => (isPhiVersion_phiMN hW (Nat.zero_le n)).meas c)

lemma disc_tendsto (hW : IsWhiteNoise P W) (ξ : ℝ) (n : ℕ) (ω : Ω) :
    Tendsto (fun k => discLogLen ξ k fun c => phiMN W P 0 n c ω) atTop
      (𝓝 (logLen ξ (fun x => phiMN W P 0 n x ω))) := by
  have h1 : Continuous fun x => phiMN W P 0 n x ω := (isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω
  have h2 := tendsto_logLen_snap (ξ := ξ) h1
  exact h2

lemma log_lenN_eq (ξ : ℝ) (n : ℕ) :
    (fun ω => Real.log (lenN ξ W P 1 1 n ω)) = fun ω => logLen ξ (fun x => phiMN W P 0 n x ω) :=
  rfl

end L23

/-- **DDDF Lemma 23**, sharp form: `log L^{(n)}_{1,1}(φ) ∈ L²` and
`Var log L^{(n)}_{1,1}(φ) ≤ ξ² n log 2`. -/
theorem dddf_lemma23_sharp (hW : IsWhiteNoise P W) (ξ : ℝ) (n : ℕ) :
    MemLp (fun ω => Real.log (lenN ξ W P 1 1 n ω)) 2 P ∧
      Var[fun ω => Real.log (lenN ξ W P 1 1 n ω); P] ≤ ξ ^ 2 * (n * Real.log 2) := by
  have := hW.isProbabilityMeasure
  rw [log_lenN_eq]
  exact memLp_variance_le_of_tendsto (disc_measurable hW ξ n)
    (fun k => (disc_memLp_variance hW ξ n k).1) (fun k => (disc_memLp_variance hW ξ n k).2)
    (disc_tendsto hW ξ n)

end DDDF
end LQGMetric
