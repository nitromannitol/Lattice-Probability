/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AreaLogSing at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (FinArea). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaP3bSup
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.TwoRadiusTilt
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond

/-!
Discharges `AtomlessUncond.P3bBoundArea` (TASKS.md R14, first theorem; handoff
`handoff/M4-AREA-P3B.md`, "Remaining" item 4).

For the normalized field `Z = aZ X R`, an interior point `z ∈ ℍ` and the dyadic scales
`δ = 4·2^{-n}`, `D = min (Im z) 1 / 2`, `d = D/2`, `S = annIC z n = B̄(z, 2^{-n})`, the
decomposition `mu_{2^{-k}}(S) = e^{γΩ} δ^{γ²/2} W_k(S)` of `AreaP3bInner`
(`ae_areaApprox_eq_omZ_mul`) holds a.s. for all `k ≥ n`, and `Ω = omZ X z δ D` is independent of
the inner field (`indepFun_omZ_innerS`). Hence the `p`-th moment of `sup_{k ≥ n} mu_{2^{-k}}(S)`
factors into the lognormal moment of `e^{γΩ} δ^{γ²/2}` (`lintegral_omZ_factor_rpow`, handoff item
3) times the `p`-th moment of `sup_m W_{n+m}(S)`, which is controlled by
`AreaP3bSup.lintegral_iSup_massFunC_inner_rpow_le`. The two deterministic factors combine into
the single power of `2` required by `P3bBoundArea`:

  `E (sup_{k ≥ n} mu_{2^{-k}}(S))^p ≤ C 2^{n(γ²p²/2 − p(2 + γ²/2))}`.

This mirrors the boundary computation `FracMom.fracMoment_dyadic`; the interior decomposition
`Ω = Z_δ(z) − Z_D(z)` is the own adaptation recorded in DEVIATIONS (L-M4 item 7).

Source: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.3, p. 18 (the circle average process
`h_{e^{-t}}(z)` is a Brownian motion, whence independent increments of the circle averages) and
§3.2, (14)–(15), p. 19 (the LQG area measure `ε^{γ²/2}e^{γh_ε}dz`); the Θ-law form of the no-atom
statement is §3.3, (25), p. 22 (`AreaNoAtom.areaLogSingNoAtom`). (AUDIT10 G10-2 corrects the
earlier "§3.1"; §3.1 of the paper is the smoothness of the circle average field, Prop. 3.1.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaP3b

open GaussTK KernelId

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ### Elementary real lemmas on `radius n = 2^{-n}` -/

/-- `radius n ^ a = 2^{-n a}`. -/
theorem radius_rpow_eq {a : ℝ} (n : ℕ) : radius n ^ a = (2 : ℝ) ^ (-(n : ℝ) * a) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hrn : radius n = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [radius, inv_pow, ← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_neg h2.le]
  rw [hrn, ← Real.rpow_mul h2.le]

/-- `e^{(log D − log δ) t} = D^t δ^{−t}` for `D, δ > 0`. -/
theorem exp_log_sub_mul {D δ t : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    exp ((log D - log δ) * t) = D ^ t * δ ^ (-t) := by
  rw [sub_mul, exp_sub, div_eq_mul_inv, ← Real.rpow_def_of_pos hD, ← Real.rpow_def_of_pos hδ,
    ← Real.rpow_neg hδ.le]

/-- **The `n`-dependence of the `Ω`-factor.** With `δ = 4·2^{-n}`,
`δ^{pγ²/2} e^{(log D − log δ)(pγ)²/2} δ^{2p} = D^{(pγ)²/2} 4^{A} 2^{n(γ²p²/2 − p(2+γ²/2))}`,
`A = pγ²/2 + 2p − (pγ)²/2 = −(γ²p²/2 − p(2+γ²/2))`. -/
theorem u_mul_delta_eq {γ p D : ℝ} (hD : 0 < D) (n : ℕ) :
    (4 * radius n) ^ (p * (γ ^ 2 / 2)) *
        exp ((log D - log (4 * radius n)) * (p * γ) ^ 2 / 2) * (4 * radius n) ^ (2 * p) =
      D ^ ((p * γ) ^ 2 / 2) * (4 : ℝ) ^ (p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2) *
        (2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * p ^ 2 / 2 - p * (2 + γ ^ 2 / 2))) := by
  have hrn : 0 < radius n := radius_pos n
  have hδ : 0 < 4 * radius n := by positivity
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have harg : (log D - log (4 * radius n)) * (p * γ) ^ 2 / 2
      = (log D - log (4 * radius n)) * ((p * γ) ^ 2 / 2) := by ring
  rw [harg, exp_log_sub_mul hD hδ]
  have hrearr : ((4 * radius n) ^ (p * (γ ^ 2 / 2)) *
        (D ^ ((p * γ) ^ 2 / 2) * (4 * radius n) ^ (-((p * γ) ^ 2 / 2)))) *
        (4 * radius n) ^ (2 * p)
      = D ^ ((p * γ) ^ 2 / 2) * ((4 * radius n) ^ (p * (γ ^ 2 / 2)) *
        (4 * radius n) ^ (-((p * γ) ^ 2 / 2)) * (4 * radius n) ^ (2 * p)) := by ring
  rw [hrearr, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
  have hexp : p * (γ ^ 2 / 2) + -((p * γ) ^ 2 / 2) + 2 * p
      = p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2 := by ring
  rw [hexp, Real.mul_rpow h4 hrn.le, radius_rpow_eq]
  have hexp2 : -(n : ℝ) * (p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2)
      = (n : ℝ) * (γ ^ 2 * p ^ 2 / 2 - p * (2 + γ ^ 2 / 2)) := by ring
  rw [hexp2]
  ring

/-- **The real core of the interior area fractional-moment bound**: the `Ω`-factor times the sup
bound's two summands (`|S| = π 2^{-2n} = π δ²/16`), with the constants of the statement. -/
theorem u_mul_factor_eq {γ p D K Cst q : ℝ} (hD : 0 < D) (hCst : 0 ≤ Cst) (n : ℕ) :
    ((4 * radius n) ^ (p * (γ ^ 2 / 2)) *
        exp ((log D - log (4 * radius n)) * (p * γ) ^ 2 / 2)) *
      ((exp (γ ^ 2 / 2 * K) * (π * radius n ^ 2)) ^ p +
        (Cst * (4 * radius n) ^ 2) ^ p * (1 - q)⁻¹) =
      (D ^ ((p * γ) ^ 2 / 2) * (exp (γ ^ 2 / 2 * K) * (π / 16)) ^ p *
          (4 : ℝ) ^ (p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2) +
        D ^ ((p * γ) ^ 2 / 2) * Cst ^ p * (1 - q)⁻¹ *
          (4 : ℝ) ^ (p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2)) *
        (2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * p ^ 2 / 2 - p * (2 + γ ^ 2 / 2))) := by
  have hrn : 0 < radius n := radius_pos n
  have hδ : 0 < 4 * radius n := by positivity
  have h16 : (0 : ℝ) ≤ π / 16 := by positivity
  have hpt : (0 : ℝ) ≤ (4 * radius n) ^ (2 : ℝ) := rpow_nonneg hδ.le 2
  have h2 : (exp (γ ^ 2 / 2 * K) * (π * radius n ^ 2)) ^ p
      = (exp (γ ^ 2 / 2 * K) * (π / 16)) ^ p * (4 * radius n) ^ (2 * p) := by
    have hsq : π * radius n ^ 2 = π / 16 * (4 * radius n) ^ (2 : ℝ) := by
      rw [Real.rpow_two]; ring
    rw [hsq, ← mul_assoc, Real.mul_rpow (mul_nonneg (exp_pos _).le h16) hpt,
      ← Real.rpow_mul hδ.le]
  have h3 : (Cst * (4 * radius n) ^ 2) ^ p = Cst ^ p * (4 * radius n) ^ (2 * p) := by
    rw [← Real.rpow_two (4 * radius n), Real.mul_rpow hCst hpt, ← Real.rpow_mul hδ.le]
  rw [h2, h3,
    show ((4 * radius n) ^ (p * (γ ^ 2 / 2)) *
          exp ((log D - log (4 * radius n)) * (p * γ) ^ 2 / 2)) *
        ((exp (γ ^ 2 / 2 * K) * (π / 16)) ^ p * (4 * radius n) ^ (2 * p) +
          Cst ^ p * (4 * radius n) ^ (2 * p) * (1 - q)⁻¹)
        = ((4 * radius n) ^ (p * (γ ^ 2 / 2)) *
            exp ((log D - log (4 * radius n)) * (p * γ) ^ 2 / 2) *
            (4 * radius n) ^ (2 * p)) *
          ((exp (γ ^ 2 / 2 * K) * (π / 16)) ^ p + Cst ^ p * (1 - q)⁻¹) by ring,
    u_mul_delta_eq (γ := γ) (p := p) (D := D) hD n]
  ring

/-! ### The dyadic ball volume -/

theorem volumeReal_annIC (z : ℂ) (n : ℕ) :
    volume.real (AtomlessUncond.annIC z n) = π * radius n ^ 2 := by
  have hpi : (↑NNReal.pi : ℝ≥0∞).toReal = π := by
    rw [show (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal π by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]]
    exact ENNReal.toReal_ofReal pi_pos.le
  rw [AtomlessUncond.annIC, MeasureTheory.measureReal_def, Complex.volume_closedBall,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (radius_pos n).le, hpi]
  ring

/-! ### The fractional-moment bound -/

end AreaP3b
end QuantumZipper
