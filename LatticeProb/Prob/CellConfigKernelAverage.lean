import LatticeProb.Prob.CellConfigCappedSquareSigma
import LatticeProb.Prob.CellConfigKernelExactCovariance

/-!
# The kernel average of a function of the rooted cell configuration over the capped square

Let `H` be a cell configuration, `D` a dyadic system of the plane with coordinates `q`, and
`K(H, D, w, z) = |Ŝ_m^w|⁻¹ 1(z ∈ Ŝ_m^w)` the uniform-average kernel of the capped square of cell
mass `m` around `w` (`averageKernel`). For a function `G(H, D, z) ≥ 0` of the configuration seen
from the root `z`, the *kernel average*
`A_m G(H, D, w) = ∫ K(H, D, w, z) G(H, D, z) dz`
is the uniform average of `G(H, D, ·)` over the capped square around `w`, defined for every root `w`
in a jointly measurable form. Gwynne, Miller and Sheffield (*An invariance principle for ergodic
scale-free random environments*, arXiv 1807.07515, proof of Lemma 2.7) use the average
`|S_m^0|⁻¹ ∫_{S_m^0} G(H - z, D - z) dz` as the conditional expectation given the σ-algebra `𝓕_m`;
the rooted form `A_m G` is the function whose level sets are witnesses of `𝓕_m`.

## Main results
* `lintegral_comp_smul_add_complex`: the planar change of variables
  `∫ f(s z + b) dz = s⁻² ∫ f(z) dz` for `s > 0`.
* `measurable_kernelAverage`: `A_m G` is measurable for a measurable `G`.
* `kernelAverage_similarity`: `A_m G` is invariant under the joint similarity
  `(H, D, w) ↦ (C(H - u), C(D - u), C(w - u))` at every dyadic system with compatible offset
  sequences, when `G` is.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- **Planar change of variables** for a similarity `z ↦ s z + b` with `s > 0`:
`∫ f(s z + b) dz = s⁻² ∫ f(z) dz` for Lebesgue measure on `ℂ`. -/
theorem lintegral_comp_smul_add_complex {f : ℂ → ℝ≥0∞} (hf : Measurable f) {s : ℝ}
    (hs : 0 < s) (b : ℂ) :
    ∫⁻ z, f (s • z + b) = ENNReal.ofReal ((s ^ 2)⁻¹) * ∫⁻ z, f z := by
  have key := lintegral_map (μ := (volume : Measure ℂ)) (hf.comp (measurable_add_const b))
    (measurable_const_smul s)
  rw [Measure.map_addHaar_smul (μ := (volume : Measure ℂ)) hs.ne', Complex.finrank_real_complex,
    abs_of_pos (by positivity : (0 : ℝ) < (s ^ 2)⁻¹), lintegral_smul_measure] at key
  rw [← lintegral_add_right_eq_self f b]
  exact key.symm

/-- **The kernel average** `A_m G(H, D, w) = ∫ |Ŝ_m^w|⁻¹ 1(z ∈ Ŝ_m^w) G(H, D, z) dz` of a function
of the rooted configuration over the capped square of cell mass `m` around the root `w`; the
argument is `(H, q, w)`. -/
noncomputable def kernelAverage (m : ℝ≥0∞) (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞)
    (p : GMSSpace × DyadicCoord × ℂ) : ℝ≥0∞ :=
  ∫⁻ z, averageKernel m (p.1, (p.2.1, p.2.2), z) * G (p.1, p.2.1, z)

/-- **The kernel average is measurable** in the configuration, the dyadic system and the root, for
a measurable `G`. -/
theorem measurable_kernelAverage (m : ℝ≥0∞) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (hG : Measurable G) : Measurable (kernelAverage m G) := by
  unfold kernelAverage
  exact Measurable.lintegral_prod_right'
    (f := fun x : (GMSSpace × DyadicCoord × ℂ) × ℂ =>
      averageKernel m (x.1.1, (x.1.2.1, x.1.2.2), x.2) * G (x.1.1, x.1.2.1, x.2))
    (((measurable_averageKernel m).comp (measurable_fst.fst.prodMk
      ((measurable_fst.snd.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd))).mul
      (hG.comp (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd))))

/-- **Similarity invariance of the kernel average**: if `H'` is `C(H - u)`, the dyadic system `q`
has compatible offset sequences and `G` is invariant under the joint similarity at `q`, then
`A_m G(H', C(D - u), C(w - u)) = A_m G(H, D, w)`: the kernel scales by `s⁻²`
(`averageKernel_similarity`) and Lebesgue measure by `s²`. -/
theorem kernelAverage_similarity (m : ℝ≥0∞) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (hGm : Measurable G) {s : ℝ} {u : Plane} {hs : 0 < s} {H H' : GMSSpace}
    (hHH' : IsSimilar s u hs H H') {q : DyadicCoord} (h₁ : IsCompatible q.2.1)
    (h₂ : IsCompatible q.2.2)
    (hG : ∀ z : ℂ, G (H', similarityCoord s u q, s • z + similarityOffset s u) = G (H, q, z))
    (w : ℂ) :
    kernelAverage m G (H', similarityCoord s u q, s • w + similarityOffset s u) =
      kernelAverage m G (H, q, w) := by
  have hc : (0 : ℝ) ≤ s ^ 2 := by positivity
  have hF : Measurable fun z : ℂ =>
      averageKernel m (H', (similarityCoord s u q, s • w + similarityOffset s u), z) *
        G (H', similarityCoord s u q, z) :=
    ((measurable_averageKernel m).comp (measurable_const.prodMk
      (measurable_const.prodMk measurable_id))).mul
      (hGm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  have hFH : Measurable fun z : ℂ => averageKernel m (H, (q, w), z) * G (H, q, z) :=
    ((measurable_averageKernel m).comp (measurable_const.prodMk
      (measurable_const.prodMk measurable_id))).mul
      (hGm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  have key : ENNReal.ofReal ((s ^ 2)⁻¹) *
        kernelAverage m G (H', similarityCoord s u q, s • w + similarityOffset s u) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * kernelAverage m G (H, q, w) := by
    dsimp only [kernelAverage]
    rw [← lintegral_comp_smul_add_complex hF hs
      (similarityOffset s u), ← lintegral_const_mul _ hFH]
    refine lintegral_congr fun z => ?_
    rw [averageKernel_similarity hHH' q h₁ h₂ m w z, hG z, mul_assoc]
  have hinv : ENNReal.ofReal (s ^ 2) * ENNReal.ofReal ((s ^ 2)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hc, mul_inv_cancel₀ (pow_pos hs 2).ne', ENNReal.ofReal_one]
  calc kernelAverage m G (H', similarityCoord s u q, s • w + similarityOffset s u)
      = ENNReal.ofReal (s ^ 2) * (ENNReal.ofReal ((s ^ 2)⁻¹) *
          kernelAverage m G (H', similarityCoord s u q, s • w + similarityOffset s u)) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = ENNReal.ofReal (s ^ 2) * (ENNReal.ofReal ((s ^ 2)⁻¹) * kernelAverage m G (H, q, w)) := by
        rw [key]
    _ = kernelAverage m G (H, q, w) := by rw [← mul_assoc, hinv, one_mul]

end LatticeProb.CellConfigCappedSquare
