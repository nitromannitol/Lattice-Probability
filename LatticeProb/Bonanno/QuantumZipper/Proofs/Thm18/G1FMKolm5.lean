/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.G1FMKolm5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeKolm
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE: the quantitative Kolmogorov sup tail in any dimension

Task G1-FM-BLOCK5. `kolm_sup_tail_N` is `D3Plus.kolm_sup_tail` without the restriction `d ≤ 4`:
the only dimension-dependent input, the level-`j` union bound, is taken from
`KolmN.measure_badSetG_le_N` (threshold `2^d (1/2)^a / θ^p < 1` in place of `16 (1/2)^a/θ^p`).
Source: quantitative form of the Kolmogorov–Čentsov criterion (Revuz–Yor, *Continuous
Martingales and Brownian Motion*, 3rd ed., Ch. I, Thm (2.1), pp. 26–27); bookkeeping own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM

open KolmD KolmG D3Plus

variable {d : ℕ} {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Quantitative sup tail** from the dyadic Kolmogorov chaining, any dimension `d`. -/
theorem kolm_sup_tail_N (hθ0 : 0 < θ) (hθ1 : θ < 1) {Z : (Fin d → ℝ) → Ω → ℝ}
    (hZc : ∀ ω, Continuous fun q => Z q ω) (hZ : ∀ q, AEMeasurable (Z q) P) {p : ℕ} {a K : ℝ}
    (ha : 0 ≤ a) (hK : 0 ≤ K) (hρ : (2 : ℝ) ^ d * ((1 / 2 : ℝ) ^ a / θ ^ p) < 1) {R : ℕ}
    (hmom : MomentBoundG Z P p a K (R + 1))
    (hpt : ∀ q ∈ boxD (d := d) R, ∫⁻ ω, ENNReal.ofReal (|Z q ω| ^ p) ∂P ≤ ENNReal.ofReal K)
    {l : ℝ} (hl : 0 < l) :
    P {ω | ∃ q ∈ boxD (d := d) R, (d / (1 - θ) + 1) * l < |Z q ω|} ≤
      ENNReal.ofReal (K / l ^ p * ((2 * R + 1) ^ d +
        d * (2 * R + 1) ^ d / (1 - (2 : ℝ) ^ d * ((1 / 2 : ℝ) ^ a / θ ^ p)))) := by
  classical
  set ρ : ℝ := (2 : ℝ) ^ d * ((1 / 2 : ℝ) ^ a / θ ^ p) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have h1ρ : 0 < 1 - ρ := by linarith
  set Z' : (Fin d → ℝ) → Ω → ℝ := fun q ω => Z q ω / l with hZ'
  set K' : ℝ := K / l ^ p with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hmom' : MomentBoundG Z' P p a K' (R + 1) := momentBoundG_div hmom hl hK
  have hZ'm : ∀ q, AEMeasurable (Z' q) P := fun q => (hZ q).div_const l
  set S : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R with hS
  set B : Set Ω := (⋃ j, badSetG Z' θ R j) ∪
    ⋃ b ∈ S, {ω | 1 < |Z' (lptD 0 b) ω - 0|} with hB
  have hsub : {ω | ∃ q ∈ boxD (d := d) R, (d / (1 - θ) + 1) * l < |Z q ω|} ⊆ B := by
    intro ω hω
    by_contra hnot
    simp only [hB, mem_union, mem_iUnion, not_or, not_exists, badSetG, mem_ofPred_eq,
      not_not, sub_zero, not_lt] at hnot
    obtain ⟨hgood, hlat⟩ := hnot
    obtain ⟨q, hq, hbig⟩ := hω
    have h1 := abs_sub_rndD_zero_le_of_good hθ0 hθ1 ((hZc ω).div_const l)
      (fun j _ => hgood j) hq
    have hmem : flr 0 q ∈ S := Fintype.mem_piFinset.2 fun i =>
      Finset.mem_Icc.2 (abs_le.1 (by simpa using inRange_flr hq 0 i))
    have h2 := hlat _ hmem
    have h3 : |Z' q ω| ≤ d / (1 - θ) + 1 := by
      have := abs_sub_abs_le_abs_sub (Z' q ω) (Z' (rndD 0 q) ω)
      simp only [rndD] at this h1
      simp only [hZ'] at *
      linarith
    have h4 : |Z q ω| ≤ (d / (1 - θ) + 1) * l := by
      simp only [hZ', abs_div, abs_of_pos hl] at h3
      rwa [div_le_iff₀ hl] at h3
    linarith
  have hbad : ∀ j, P (badSetG Z' θ R j) ≤ ENNReal.ofReal (d * (2 * R + 1) ^ d * K' * ρ ^ j) :=
    fun j => KolmN.measure_badSetG_le_N hθ0 hZ'm ha hK'0 hmom' j
  have hlatb : ∀ b ∈ S, P {ω | 1 < |Z' (lptD 0 b) ω - 0|} ≤ ENNReal.ofReal K' := by
    intro b hb
    have hbR : lptD 0 b ∈ boxD (d := d) R := fun i => by
      have := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hb i)
      simp only [lptD, pow_zero, div_one]
      rw [abs_le]; constructor <;> exact_mod_cast (by omega : _)
    have hm : ∫⁻ ω, ENNReal.ofReal (|Z' (lptD 0 b) ω - 0| ^ p) ∂P ≤ ENNReal.ofReal K' := by
      have e : ∀ ω, ENNReal.ofReal (|Z' (lptD 0 b) ω - 0| ^ p) =
          ENNReal.ofReal (|Z (lptD 0 b) ω| ^ p) * ENNReal.ofReal ((l ^ p)⁻¹) := by
        intro ω
        rw [← ENNReal.ofReal_mul (by positivity), sub_zero, hZ', abs_div, abs_of_pos hl,
          div_pow, div_eq_mul_inv]
      simp_rw [e]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hK', div_eq_mul_inv,
        ENNReal.ofReal_mul hK]
      gcongr; exact hpt _ hbR
    simpa using meas_gt_le_of_moment_G (hZ'm _) aemeasurable_const one_pos hm
  have hgeom : ∑' j, ENNReal.ofReal (d * (2 * R + 1) ^ d * K' * ρ ^ j) =
      ENNReal.ofReal (d * (2 * R + 1) ^ d * K' / (1 - ρ)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      ((summable_geometric_of_lt_one hρ0 hρ).mul_left _), tsum_mul_left,
      tsum_geometric_of_lt_one hρ0 hρ, div_eq_mul_inv]
  calc P {ω | ∃ q ∈ boxD (d := d) R, (d / (1 - θ) + 1) * l < |Z q ω|}
      ≤ P B := measure_mono hsub
    _ ≤ P (⋃ j, badSetG Z' θ R j) + P (⋃ b ∈ S, {ω | 1 < |Z' (lptD 0 b) ω - 0|}) :=
        measure_union_le _ _
    _ ≤ ∑' j, ENNReal.ofReal (d * (2 * R + 1) ^ d * K' * ρ ^ j) +
          ∑ b ∈ S, ENNReal.ofReal K' :=
        add_le_add ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hbad))
          ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hlatb))
    _ = ENNReal.ofReal (K / l ^ p * ((2 * R + 1) ^ d +
          d * (2 * R + 1) ^ d / (1 - ρ))) := by
        rw [hgeom, Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_lattice0,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hK']; ring

end G1FM
end Thm18Asm
end QuantumZipper
