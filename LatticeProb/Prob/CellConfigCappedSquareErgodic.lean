import LatticeProb.Prob.CellConfigKernelAverage
import LatticeProb.Prob.ReverseMartingaleTrivialTail

/-!
# Ergodic averages over the capped squares: the conditional form of the ergodic lemma

Let `H` be a random cell configuration with law `μ` satisfying the mass-transport principle, `D` an
independent uniform dyadic system with coordinates `q`, and `S_m^0 = S_m^0(H, D)` the capped square
of cell mass `m` around the origin. Gwynne, Miller and Sheffield (*An invariance principle for
ergodic scale-free random environments*, arXiv 1807.07515, Lemma 2.7 and its proof) obtain the
convergence of the uniform averages `|S_m^0|⁻¹ ∫_{S_m^0} F(H - z, D - z) dz` as `m → ∞` from the
identity `|S_m^0|⁻¹ ∫_{S_m^0} F(H - z, D - z) dz = E[F | 𝓕_m]` (Definition 2.5 and Lemma 2.3) and the
backward martingale convergence theorem, the σ-algebras `𝓕_m` decreasing in `m`. Without any
ergodicity input the limit is the conditional expectation given the tail σ-algebra
`𝓘 = ⋂_{m > 0} 𝓕_m`; this file proves that conditional form along the integer cell masses.

## Main results
* `cappedSquareTailSigma`: the tail σ-algebra `𝓘 = ⋂_k 𝓕_{k+1}`, and `iInf_cappedSquareSigma_eq`:
  it is the intersection of all `𝓕_m`, `0 < m < ∞`.
* `ae_tendsto_kernelAverage_origin_condExp`: almost surely under `μ ⊗ P` (with `P` the law of the
  uniform dyadic system), the kernel average `A_{k+1} G(H, D, 0)` tends to `E[G(H, D, 0) | 𝓘]` as
  `k → ∞`, for every measurable `G ≥ 0` invariant under the joint similarity with
  `E[G(H, D, 0)] < ∞`.
* `ae_ae_tendsto_cappedSquareAverage`: the same for the uniform average
  `|S_{k+1}^0|⁻¹ ∫_{S_{k+1}^0} G(H, D, z) dz`, for almost every `H` and almost every `D`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- **The tail σ-algebra** `𝓘 = ⋂_k 𝓕_{k+1}` of the capped-square σ-algebras
(arXiv 1807.07515, Lemma 2.6: the σ-algebra `⋂_{m > 0} 𝓕_m`; see `iInf_cappedSquareSigma_eq`). -/
@[instance_reducible]
def cappedSquareTailSigma : MeasurableSpace (GMSSpace × DyadicCoord) :=
  ⨅ k : ℕ, cappedSquareSigma ((k : ℝ≥0∞) + 1)

/-- `𝓘` is a sub-σ-algebra of the product σ-algebra. -/
theorem cappedSquareTailSigma_le :
    cappedSquareTailSigma ≤ (inferInstance : MeasurableSpace (GMSSpace × DyadicCoord)) :=
  (iInf_le _ 0).trans (cappedSquareSigma_le _)

/-- `𝓘 ≤ 𝓕_m` for every cell mass `m ∈ (0, ∞)`. -/
theorem cappedSquareTailSigma_le_cappedSquareSigma {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞) :
    cappedSquareTailSigma ≤ cappedSquareSigma m := by
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hmtop
  exact (iInf_le _ k).trans (cappedSquareSigma_anti hm0 (hk.le.trans le_self_add) (by simp))

/-- **`𝓘` is the intersection of all the σ-algebras `𝓕_m`, `0 < m < ∞`.** -/
theorem iInf_cappedSquareSigma_eq :
    (⨅ (m : ℝ≥0∞) (_ : m ≠ 0) (_ : m ≠ ∞), cappedSquareSigma m) = cappedSquareTailSigma :=
  le_antisymm
    (le_iInf fun k => iInf_le_of_le ((k : ℝ≥0∞) + 1)
      (iInf_le_of_le (by simp) (iInf_le_of_le (by simp) le_rfl)))
    (le_iInf fun _ => le_iInf fun hm0 => le_iInf fun hmtop =>
      cappedSquareTailSigma_le_cappedSquareSigma hm0 hmtop)

section Limit

variable {μ : Measure GMSSpace}

/-- **Conditional ergodic lemma for the kernel average** (arXiv 1807.07515, Lemma 2.7, conditional
form): under the mass-transport principle, for a finite law `μ` of the configuration and every
measurable `G ≥ 0` invariant under the joint similarity with `E[G(H, D, 0)] < ∞`, almost surely
under `μ ⊗ P` the kernel averages `A_{k+1} G(H, D, 0)` converge to `E[G(H, D, 0) | 𝓘]` as `k → ∞`.
Proof: `A_m G(·, ·, 0)` is a version of `E[G(H, D, 0) | 𝓕_m]`, and the backward martingale
convergence theorem along the decreasing sequence `𝓕_{k+1}`. -/
theorem ae_tendsto_kernelAverage_origin_condExp [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (hfin : ∫⁻ p, G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞) :
    ∀ᵐ p ∂μ.prod dyadicLaw,
      Tendsto (fun k : ℕ => (kernelAverage ((k : ℝ≥0∞) + 1) G (p.1, p.2, 0)).toReal) atTop
        (𝓝 ((μ.prod dyadicLaw)[fun p => (G (p.1, p.2, 0)).toReal | cappedSquareTailSigma] p)) := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hG0 : Measurable fun p : GMSSpace × DyadicCoord => G (p.1, p.2, 0) :=
    hG.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hk : ∀ᵐ p ∂μ.prod dyadicLaw, ∀ k : ℕ,
      (kernelAverage ((k : ℝ≥0∞) + 1) G (p.1, p.2, 0)).toReal =
        (μ.prod dyadicLaw)[fun p => (G (p.1, p.2, 0)).toReal |
          cappedSquareSigma ((k : ℝ≥0∞) + 1)] p :=
    ae_all_iff.2 fun k => kernelAverage_origin_ae_eq_condExp hMT (by simp) (by simp) hG hinv hfin
  filter_upwards [hk, ReverseMartingale.tendsto_condExp_iInf_ae (P := μ.prod dyadicLaw)
    (ℱ := fun k : ℕ => cappedSquareSigma ((k : ℝ≥0∞) + 1)) (fun _ => cappedSquareSigma_le _)
    antitone_cappedSquareSigma_natCast_add_one
    (integrable_toReal_of_lintegral_ne_top hG0.aemeasurable hfin)] with p hp hlim
  exact hlim.congr fun k => (hp k).symm

/-- **Conditional ergodic lemma for the uniform capped-square averages** (arXiv 1807.07515,
Lemma 2.7, conditional form): under the hypotheses of `ae_tendsto_kernelAverage_origin_condExp`, for
`μ`-almost every configuration `H` and almost every dyadic system `D`,
`|S_{k+1}^0|⁻¹ ∫_{S_{k+1}^0} G(H, D, z) dz → E[G(H, D, 0) | 𝓘](H, D)` as `k → ∞`. -/
theorem ae_ae_tendsto_cappedSquareAverage [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (hfin : ∫⁻ p, G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      Tendsto (fun k : ℕ => (cappedSquareAverage ((k : ℝ≥0∞) + 1) G H q).toReal) atTop
        (𝓝 ((μ.prod dyadicLaw)[fun p => (G (p.1, p.2, 0)).toReal | cappedSquareTailSigma]
          (H, q))) := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  filter_upwards [Measure.ae_ae_of_ae_prod
    (ae_tendsto_kernelAverage_origin_condExp hMT hG hinv hfin)] with H hH
  filter_upwards [hH, ae_all_iff.2 fun k : ℕ =>
    ae_kernelAverage_origin_eq (m := (k : ℝ≥0∞) + 1) (by simp) (by simp) G H] with q hq hkq
  exact hq.congr fun k => congrArg ENNReal.toReal (hkq k)

end Limit

end LatticeProb.CellConfigCappedSquare
