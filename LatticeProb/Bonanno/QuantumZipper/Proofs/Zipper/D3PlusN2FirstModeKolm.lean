/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeKolm at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FIRSTMODE, step 2: a quantitative sup tail from the dyadic Kolmogorov chaining

Task N2Z-FIRSTMODE. For a process `Z` on `ℝ^d` (`d ≤ 4`) with continuous paths, the increment
moment bound `MomentBoundG Z P p a K (R+1)` of `KolmG` and pointwise moments `E|Z q|^p ≤ K` on
the box `boxD R`, we prove the tail bound (`kolm_sup_tail`)

`P(∃ q ∈ [-R,R]^d, (d/(1-θ) + 1) λ < |Z q|) ≤ (K/λ^p) ((2R+1)^d + d (2R+1)^d / (1 - ρ))`,

`ρ = 16 (1/2)^a / θ^p < 1`. Proof: apply the chaining of `KolmG` (`telescope_G'`,
`measure_badSetG_le`) to `Z/λ` from level `0`, plus Markov at the `(2R+1)^d` lattice points of
level `0`. This is the quantitative form of the Kolmogorov–Čentsov criterion (Revuz–Yor,
*Continuous Martingales and Brownian Motion*, 3rd ed., Ch. I, Thm (2.1), pp. 26–27, whose proof
bounds the Hölder constant on the complement of the bad events); the bookkeeping is own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace D3Plus

open KolmD KolmG

variable {d : ℕ} {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- On all-good levels, the value at `q` is within `d/(1-θ)` of the level-0 rounding. -/
theorem abs_sub_rndD_zero_le_of_good (hθ0 : 0 < θ) (hθ1 : θ < 1) {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) {R : ℕ} (hg : ∀ j ≥ 0, GoodG θ f R j) {q : Fin d → ℝ}
    (hq : q ∈ boxD R) : |f q - f (rndD 0 q)| ≤ d / (1 - θ) := by
  have ht : Tendsto (fun M => rndD M q) atTop (𝓝 q) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun M => norm_rndD_sub_le M q) ?_
    simp_rw [one_div]
    exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlim : Tendsto (fun M => |f (rndD M q) - f (rndD 0 q)|) atTop
      (𝓝 |f q - f (rndD 0 q)|) :=
    (((hf.tendsto q).comp ht).sub tendsto_const_nhds).abs
  refine le_of_tendsto hlim (Eventually.of_forall fun M => ?_)
  have h := telescope_G' hθ0 hθ1 hq hg le_rfl (Nat.zero_le M)
  simpa using h

/-- Scaling the moment bound. -/
theorem momentBoundG_div {Z : (Fin d → ℝ) → Ω → ℝ} {p : ℕ} {a K : ℝ} {R : ℕ}
    (hmom : MomentBoundG Z P p a K R) {c : ℝ} (hc : 0 < c) (hK : 0 ≤ K) :
    MomentBoundG (fun q ω => Z q ω / c) P p a (K / c ^ p) R := by
  intro q hq q' hq'
  have e : ∀ ω, ENNReal.ofReal (|Z q ω / c - Z q' ω / c| ^ p) =
      ENNReal.ofReal (|Z q ω - Z q' ω| ^ p) * ENNReal.ofReal ((c ^ p)⁻¹) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by positivity), ← sub_div, abs_div, abs_of_pos hc,
      div_pow, div_eq_mul_inv]
  simp_rw [e]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc _ ≤ ENNReal.ofReal (K * ‖q - q'‖ ^ a) * ENNReal.ofReal ((c ^ p)⁻¹) := by
        gcongr; exact hmom q hq q' hq'
    _ = ENNReal.ofReal (K / c ^ p * ‖q - q'‖ ^ a) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

/-- The level-0 lattice of the box `R` has `(2R+1)^d` points. -/
theorem card_lattice0 (R : ℕ) :
    ((Fintype.piFinset fun _ : Fin d => Finset.Icc (-(R : ℤ)) R).card : ℝ) =
      (2 * (R : ℝ) + 1) ^ d := by
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Icc]
  have h1 : (0 : ℤ) ≤ (R : ℤ) + 1 - -(R : ℤ) := by omega
  push_cast
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]; push_cast; ring

end D3Plus
end QuantumZipper
