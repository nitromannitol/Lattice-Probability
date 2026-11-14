import LatticeProb.Prob.CellConfigKernelCovariance
import LatticeProb.Prob.CellConfigKernelReverse
import LatticeProb.Bonanno.ReflectedGMS.GMS.HypothesisTransfer

/-!
# Mass transport for the capped squares of the uniform dyadic system

Let `μ` be the law of a random cell configuration `H` satisfying the mass-transport principle
(Gwynne, Miller and Sheffield, *An invariance principle for ergodic scale-free random
environments*, arXiv 1807.07515, Definition 1.2(4)), let `S_m^w` be the capped square of cell
mass `m ∈ (0, ∞)` around `w` for the uniform dyadic system of the plane, and let `G(H, w) ≥ 0` be
measurable and invariant under the positive similarities, `G(C(H - u), C(w - u)) = G(H, w)`.

The transport kernel `F(H, w₀, w₁) = E[|S_m^{w₀}|⁻¹ 1(w₁ ∈ S_m^{w₀})] G(H, w₁)` is covariant of
degree `-2`, so the mass-transport principle gives `E ∫ F(H, 0, w) dw = E ∫ F(H, w, 0) dw`. The
left side is the expected uniform average of `G(H, ·)` over `S_m^0`, and the right side is
`E[G(H, 0)]`, because the kernel integrates to one in its centre. This is (B.6) of arXiv
1807.07515:

`E[|S_m^0|⁻¹ ∫_{S_m^0} G(H, z) dz] = E[G(H, 0)]`.

## Main results

* `lintegral_cappedTransportKernel_zero_right`: `∫ F(H, w, 0) dw = G(H, 0)`.
* `lintegral_cappedSquare_average_eq`: the identity (B.6).
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- **Right side of the transport identity**: the integral of the transport kernel into the
origin is `G(H, 0)`, since `∫ |S_m^w|⁻¹ 1(0 ∈ S_m^w) dw = 1` almost surely in the dyadic
system. -/
theorem lintegral_cappedTransportKernel_zero_right {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞)
    (G : GMSSpace × ℂ → ℝ≥0∞) (H : GMSSpace) :
    ∫⁻ w, cappedTransportKernel m G (H, w, 0) ∂volume = G (H, 0) := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hK : Measurable fun x : ℂ × DyadicCoord => averageKernel m (H, (x.2, x.1), 0) :=
    (measurable_averageKernel m).comp (measurable_const.prodMk
      ((measurable_snd.prodMk measurable_fst).prodMk measurable_const))
  have h1 : ∫⁻ q, ∫⁻ z : ℂ, averageKernel m (H, (q, z), 0) ∂volume
        ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) =
      ∫⁻ _q, 1 ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) :=
    lintegral_congr_ae ((ae_lintegral_averageKernel_reverse H 0).mono
      fun q hq => hq m hm0 hmtop)
  calc ∫⁻ w, cappedTransportKernel m G (H, w, 0) ∂volume
      = ∫⁻ z : ℂ, (∫⁻ q, averageKernel m (H, (q, z), 0)
          ∂(unifIco 1).prod (offsetLaw.prod offsetLaw)) * G (H, 0) ∂volume := by
        rw [← (MeasurePreserving.symm _ measurePreserving_planeCoordMeas).lintegral_comp_emb
          planeCoordMeas.symm.measurableEmbedding
          (fun z : ℂ => (∫⁻ q, averageKernel m (H, (q, z), 0)
            ∂(unifIco 1).prod (offsetLaw.prod offsetLaw)) * G (H, 0))]
        refine lintegral_congr fun w => ?_
        simp only [cappedTransportKernel, map_zero]
        rfl
    _ = (∫⁻ z : ℂ, ∫⁻ q, averageKernel m (H, (q, z), 0)
          ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) ∂volume) * G (H, 0) :=
        lintegral_mul_const _ hK.lintegral_prod_right'
    _ = (∫⁻ q, ∫⁻ z : ℂ, averageKernel m (H, (q, z), 0) ∂volume
          ∂(unifIco 1).prod (offsetLaw.prod offsetLaw)) * G (H, 0) := by
        rw [lintegral_lintegral_swap (f := fun z q => averageKernel m (H, (q, z), 0))
          hK.aemeasurable]
    _ = G (H, 0) := by
        rw [h1, lintegral_const, measure_univ, one_mul, one_mul]

/-- **Mass transport for the capped squares** ((B.6) of arXiv 1807.07515): under the
mass-transport principle, for every cell mass `m ∈ (0, ∞)` and every measurable `G ≥ 0`
invariant under the positive similarities, `G(C(H - u), C(w - u)) = G(H, w)`,
`E[|S_m^0|⁻¹ ∫ 1(z ∈ S_m^0) G(H, z) dz] = E[G(H, 0)]`, the expectation on the left taken over the
configuration and the uniform dyadic system. -/
theorem lintegral_cappedSquare_average_eq {μ : Measure GMSSpace} (hMT : MassTransport μ)
    {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞) {G : GMSSpace × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ w : ℂ, G (H', s • w + similarityOffset s u) = G (H, w)) :
    ∫⁻ H, ∫⁻ q, ∫⁻ z, (volume (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2)
          (cellMass volume (complexCells H.1)) m 0))⁻¹ *
        (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2)
          (cellMass volume (complexCells H.1)) m 0).indicator (fun _ => (1 : ℝ≥0∞)) z *
        G (H, z) ∂volume ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) ∂μ =
      ∫⁻ H, G (H, 0) ∂μ := by
  have h := massTransport_ennreal (cappedTransportKernel m G) hMT
    (measurable_cappedTransportKernel m hG)
    (fun s u hs H H' hHH' w₀ w₁ =>
      cappedTransportKernel_similarity hm0 hmtop hHH' (hinv s u hs H H' hHH') w₀ w₁)
  simp only [lintegral_cappedTransportKernel_zero_left hm0 hmtop hG,
    lintegral_cappedTransportKernel_zero_right hm0 hmtop G] at h
  exact h

end LatticeProb.CellConfigCappedSquare
