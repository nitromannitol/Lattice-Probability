import LatticeProb.Prob.CellConfigCappedSquareErgodic

/-!
# The rooted tail supremum at the origin and the conditional expectations given the tail σ-algebra

Let `H` be a random cell configuration with law `μ` satisfying the mass-transport principle, `D` an
independent uniform dyadic system with coordinates `q`, `𝓕_m` the σ-algebra of arXiv 1807.07515,
Definition 2.5, and `𝓘 = ⋂_k 𝓕_{k+1}` its tail σ-algebra (`cappedSquareTailSigma`). For a measurable
`G ≥ 0` invariant under the joint similarity, the conditional expectation `E[G(H, D, 0) | 𝓘]` need
not exist as an integrable object; Lemma 2.7 of arXiv 1807.07515 for a non-integrable `G ≥ 0` is
proved through the truncations `G ∧ N` and the supremum `J = sup_N E[G ∧ N | 𝓘]`. This file
identifies the rooted tail supremum `J̃ G(H, D, 0) = sup_N limsup_k A_{k+1}(G ∧ N)(H, D, 0)`
(`rootedTailSup`) at the origin with `J`, almost surely.

## Main results
* `measurable_rootedTailSup_origin_tail`: `(H, D) ↦ J̃ G(H, D, 0)` is `𝓘`-measurable.
* `lintegral_min_origin_ne_top`: the truncation `G ∧ N` at the origin has a finite integral under a
  finite law.
* `ae_tendsto_kernelAverage_min_origin`, `ae_limsup_kernelAverage_min_origin`: almost surely the
  kernel averages `A_{k+1}(G ∧ N)(H, D, 0)` converge in `[0, ∞]` to `E[G(H, D, 0) ∧ N | 𝓘]`, so
  their upper limit is that conditional expectation.
* `ae_rootedTailSup_origin_eq_iSup_condExp`: almost surely
  `J̃ G(H, D, 0) = sup_N E[G(H, D, 0) ∧ N | 𝓘]`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- **The rooted tail supremum at the origin is measurable with respect to the tail σ-algebra**
`𝓘 = ⋂_k 𝓕_{k+1}`, for a measurable `G ≥ 0` invariant under the joint similarity: it is
`𝓕_{k+1}`-measurable for every `k`. -/
theorem measurable_rootedTailSup_origin_tail {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w)) :
    Measurable[cappedSquareTailSigma] fun p : GMSSpace × DyadicCoord =>
      rootedTailSup G (p.1, p.2, 0) := by
  intro t ht
  refine MeasurableSpace.measurableSet_iInf.2 fun k => ?_
  exact measurable_rootedTailSup_origin (m := (k : ℝ≥0∞) + 1) (by simp) (by simp) hG hinv ht

section TailSup

variable {μ : Measure GMSSpace}

/-- Under a finite law of the configuration, the truncation `G ∧ N` at the origin has a finite
integral under `μ ⊗ P`, with `P` the law of the uniform dyadic system. -/
theorem lintegral_min_origin_ne_top [IsFiniteMeasure μ] (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞)
    (N : ℕ) : ∫⁻ p, min (G (p.1, p.2, 0)) (N : ℝ≥0∞) ∂μ.prod dyadicLaw ≠ ∞ := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have h : ∫⁻ p, min (G (p.1, p.2, 0)) (N : ℝ≥0∞) ∂μ.prod dyadicLaw ≤
      ∫⁻ _, (N : ℝ≥0∞) ∂μ.prod dyadicLaw :=
    lintegral_mono fun _ => min_le_right _ _
  rw [lintegral_const] at h
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) (measure_ne_top _ _)) h

/-- **Convergence of the truncated kernel averages in `[0, ∞]`** (arXiv 1807.07515, Lemma 2.7,
conditional form, for the truncation `G ∧ N`): under the mass-transport principle, for a finite law
`μ` of the configuration and every measurable `G ≥ 0` invariant under the joint similarity, almost
surely under `μ ⊗ P` the kernel averages `A_{k+1}(G ∧ N)(H, D, 0)` converge to
`E[G(H, D, 0) ∧ N | 𝓘]` as `k → ∞`. The averages are almost surely finite, their integrals being the
finite integral of `G ∧ N` at the origin. -/
theorem ae_tendsto_kernelAverage_min_origin [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (N : ℕ) :
    ∀ᵐ p ∂μ.prod dyadicLaw,
      Tendsto (fun k : ℕ =>
          kernelAverage ((k : ℝ≥0∞) + 1) (fun y => min (G y) (N : ℝ≥0∞)) (p.1, p.2, 0)) atTop
        (𝓝 (ENNReal.ofReal ((μ.prod dyadicLaw)[fun p => (min (G (p.1, p.2, 0)) (N : ℝ≥0∞)).toReal |
          cappedSquareTailSigma] p))) := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hGN : Measurable fun y => min (G y) (N : ℝ≥0∞) := hG.min measurable_const
  have hinvN : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        min (G (H', similarityCoord s u q, s • w + similarityOffset s u)) (N : ℝ≥0∞) =
          min (G (H, q, w)) (N : ℝ≥0∞) :=
    fun s u hs H H' h q h₁ h₂ w => by rw [hinv s u hs H H' h q h₁ h₂ w]
  have hfin := lintegral_min_origin_ne_top (μ := μ) G N
  have hK : ∀ k : ℕ, ∀ᵐ p ∂μ.prod dyadicLaw,
      kernelAverage ((k : ℝ≥0∞) + 1) (fun y => min (G y) (N : ℝ≥0∞)) (p.1, p.2, 0) < ∞ := by
    intro k
    have h := setLIntegral_kernelAverage_origin hMT (m := (k : ℝ≥0∞) + 1) (by simp) (by simp)
      hGN hinvN (@MeasurableSet.univ _ (cappedSquareSigma ((k : ℝ≥0∞) + 1)))
    simp only [Measure.restrict_univ] at h
    refine ae_lt_top ((measurable_kernelAverage _ hGN).comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))) ?_
    rw [h]
    exact hfin
  filter_upwards [ae_tendsto_kernelAverage_origin_condExp hMT hGN hinvN hfin, ae_all_iff.2 hK]
    with p hp hpK
  exact ((ENNReal.continuous_ofReal.tendsto _).comp hp).congr fun k =>
    ENNReal.ofReal_toReal (hpK k).ne

/-- **The upper limit of the truncated kernel averages is the conditional expectation given the
tail σ-algebra**: under the hypotheses of `ae_tendsto_kernelAverage_min_origin`, almost surely
`limsup_k A_{k+1}(G ∧ N)(H, D, 0) = E[G(H, D, 0) ∧ N | 𝓘]`. -/
theorem ae_limsup_kernelAverage_min_origin [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (N : ℕ) :
    ∀ᵐ p ∂μ.prod dyadicLaw,
      limsup (fun k : ℕ =>
          kernelAverage ((k : ℝ≥0∞) + 1) (fun y => min (G y) (N : ℝ≥0∞)) (p.1, p.2, 0)) atTop =
        ENNReal.ofReal ((μ.prod dyadicLaw)[fun p => (min (G (p.1, p.2, 0)) (N : ℝ≥0∞)).toReal |
          cappedSquareTailSigma] p) :=
  (ae_tendsto_kernelAverage_min_origin hMT hG hinv N).mono fun _ hp => hp.limsup_eq

/-- **The rooted tail supremum at the origin is the supremum of the truncated conditional
expectations given the tail σ-algebra** (arXiv 1807.07515, Lemma 2.7 for a non-integrable `G ≥ 0`:
the object `J = sup_N E[G ∧ N | 𝓘]`): under the mass-transport principle, for a finite law `μ` of
the configuration and every measurable `G ≥ 0` invariant under the joint similarity, almost surely
under `μ ⊗ P`, `J̃ G(H, D, 0) = sup_N E[G(H, D, 0) ∧ N | 𝓘]`. No integrability of `G` is assumed. -/
theorem ae_rootedTailSup_origin_eq_iSup_condExp [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w)) :
    ∀ᵐ p ∂μ.prod dyadicLaw,
      rootedTailSup G (p.1, p.2, 0) =
        ⨆ N : ℕ, ENNReal.ofReal ((μ.prod dyadicLaw)[fun p =>
          (min (G (p.1, p.2, 0)) (N : ℝ≥0∞)).toReal | cappedSquareTailSigma] p) := by
  filter_upwards [ae_all_iff.2 fun N : ℕ => ae_limsup_kernelAverage_min_origin hMT hG hinv N]
    with p hp
  exact iSup_congr hp

end TailSup

end LatticeProb.CellConfigCappedSquare
