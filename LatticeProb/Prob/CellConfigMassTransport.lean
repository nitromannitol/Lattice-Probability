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
* `lintegral_cappedSquare_average_eq_joint`: the joint form, for `G(H, D, w)` depending also on
  the dyadic system `D` and invariant under the joint similarity of `(H, D, w)`:
  `E[|S_m^0|⁻¹ ∫_{S_m^0} G(H, D, z) dz] = E[G(H, D, 0)]` (the re-sampling property of
  Lemma 2.3 of arXiv 1807.07515 in test-function form).
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

/-! ### The joint form: functions of the configuration and the dyadic system -/

/-- **The joint transport kernel of the capped squares**: for `G(H, D, w)` depending on the
configuration, the dyadic coordinates and a point,
`F(H, w₀, w₁) = E[|S_m^{w₀}|⁻¹ 1(w₁ ∈ S_m^{w₀}) G(H, D, w₁)]`, the expectation over the uniform
dyadic system `D`, for points of `Plane` read in the coordinates `ℂ`. -/
noncomputable def jointTransportKernel (m : ℝ≥0∞) (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞)
    (p : GMSSpace × Plane × Plane) : ℝ≥0∞ :=
  ∫⁻ q, averageKernel m (p.1, (q, planeCoord.symm p.2.1), planeCoord.symm p.2.2) *
      G (p.1, q, planeCoord.symm p.2.2) ∂(unifIco 1).prod (offsetLaw.prod offsetLaw)

/-- **Covariance of the joint transport kernel**: if `H'` is `C(H - u)` and `G` is invariant under
the joint similarity of the configuration, the dyadic system and the point,
`G(H', C(D - u), T w) = G(H, D, w)` for every dyadic system with compatible offset sequences (a set
of full measure), then `F(H', C(w₀ - u), C(w₁ - u)) = s⁻² F(H, w₀, w₁)`. -/
theorem jointTransportKernel_similarity {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hGm : Measurable G) {s : ℝ} {u : Plane}
    {hs : 0 < s} {H H' : GMSSpace} (hHH' : IsSimilar s u hs H H')
    (hG : ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
      G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (w₀ w₁ : Plane) :
    jointTransportKernel m G (H', positiveSimilarity s u w₀, positiveSimilarity s u w₁) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * jointTransportKernel m G (H, w₀, w₁) := by
  simp only [jointTransportKernel, planeCoord_symm_positiveSimilarity]
  have hmeas : ∀ (K : GMSSpace) (a b : ℂ),
      Measurable fun q : DyadicCoord => averageKernel m (K, (q, a), b) * G (K, q, b) :=
    fun K a b => (measurable_averageKernel_dyadic m K a b).mul
      (hGm.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  calc ∫⁻ q, averageKernel m (H', (q, s • planeCoord.symm w₀ + similarityOffset s u),
          s • planeCoord.symm w₁ + similarityOffset s u) *
        G (H', q, s • planeCoord.symm w₁ + similarityOffset s u)
        ∂(unifIco 1).prod (offsetLaw.prod offsetLaw)
      = ∫⁻ q, averageKernel m (H', (similarityCoord s u q,
          s • planeCoord.symm w₀ + similarityOffset s u),
          s • planeCoord.symm w₁ + similarityOffset s u) *
        G (H', similarityCoord s u q, s • planeCoord.symm w₁ + similarityOffset s u)
        ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) :=
        ((measurePreserving_similarityCoord s u).lintegral_comp (hmeas H' _ _)).symm
    _ = ∫⁻ q, ENNReal.ofReal ((s ^ 2)⁻¹) *
          (averageKernel m (H, (q, planeCoord.symm w₀), planeCoord.symm w₁) *
            G (H, q, planeCoord.symm w₁)) ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) :=
        lintegral_congr_ae (((ae_averageKernel_similarity hHH' (planeCoord.symm w₀)).and
          ae_isCompatible_system).mono fun q hq => by
            beta_reduce
            rw [hq.1 m hm0 hmtop (planeCoord.symm w₁), hG q hq.2.1 hq.2.2, mul_assoc])
    _ = _ := lintegral_const_mul _ (hmeas H _ _)

/-- **The joint transport kernel is measurable** in the configuration and the two points, for a
measurable `G`. -/
theorem measurable_jointTransportKernel (m : ℝ≥0∞) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (hG : Measurable G) : Measurable (jointTransportKernel m G) := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hc : Measurable fun z : Plane => planeCoord.symm z := planeCoord.symm.continuous.measurable
  unfold jointTransportKernel
  exact Measurable.lintegral_prod_right'
    (f := fun x : (GMSSpace × Plane × Plane) × DyadicCoord =>
      averageKernel m (x.1.1, (x.2, planeCoord.symm x.1.2.1), planeCoord.symm x.1.2.2) *
        G (x.1.1, x.2, planeCoord.symm x.1.2.2))
    (((measurable_averageKernel m).comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.prodMk (hc.comp ((measurable_fst.comp measurable_snd).comp
        measurable_fst))).prodMk (hc.comp ((measurable_snd.comp measurable_snd).comp
          measurable_fst))))).mul
      (hG.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.prodMk
        (hc.comp ((measurable_snd.comp measurable_snd).comp measurable_fst))))))

/-- **Left side of the joint transport identity**: the integral of the joint transport kernel from
the origin is the expected uniform average of `G(H, D, ·)` over the capped square `S_m^0`. -/
theorem lintegral_jointTransportKernel_zero_left {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G) (H : GMSSpace) :
    ∫⁻ w, jointTransportKernel m G (H, 0, w) ∂volume =
      ∫⁻ q, ∫⁻ z, (volume (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2)
          (cellMass volume (complexCells H.1)) m 0))⁻¹ *
        (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2)
          (cellMass volume (complexCells H.1)) m 0).indicator (fun _ => (1 : ℝ≥0∞)) z *
        G (H, q, z) ∂volume ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hK : Measurable fun x : ℂ × DyadicCoord =>
      averageKernel m (H, (x.2, 0), x.1) * G (H, x.2, x.1) :=
    ((measurable_averageKernel m).comp (measurable_const.prodMk
      ((measurable_snd.prodMk measurable_const).prodMk measurable_fst))).mul
      (hG.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst)))
  calc ∫⁻ w, jointTransportKernel m G (H, 0, w) ∂volume
      = ∫⁻ z : ℂ, ∫⁻ q, averageKernel m (H, (q, 0), z) * G (H, q, z)
          ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) ∂volume := by
        rw [← (MeasurePreserving.symm _ measurePreserving_planeCoordMeas).lintegral_comp_emb
          planeCoordMeas.symm.measurableEmbedding
          (fun z : ℂ => ∫⁻ q, averageKernel m (H, (q, 0), z) * G (H, q, z)
            ∂(unifIco 1).prod (offsetLaw.prod offsetLaw))]
        refine lintegral_congr fun w => ?_
        simp only [jointTransportKernel, map_zero]
        rfl
    _ = ∫⁻ q, ∫⁻ z : ℂ, averageKernel m (H, (q, 0), z) * G (H, q, z) ∂volume
          ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) :=
        lintegral_lintegral_swap (f := fun z q => averageKernel m (H, (q, 0), z) * G (H, q, z))
          hK.aemeasurable
    _ = _ := by
        refine lintegral_congr_ae ((ae_averageKernel_eq H 0).mono fun q hq => ?_)
        exact lintegral_congr fun z => by rw [hq m hm0 hmtop z]

/-- **Right side of the joint transport identity**: the integral of the joint transport kernel
into the origin is `E[G(H, D, 0)]`, the expectation over the dyadic system. -/
theorem lintegral_jointTransportKernel_zero_right {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G) (H : GMSSpace) :
    ∫⁻ w, jointTransportKernel m G (H, w, 0) ∂volume =
      ∫⁻ q, G (H, q, 0) ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hK : Measurable fun x : ℂ × DyadicCoord =>
      averageKernel m (H, (x.2, x.1), 0) * G (H, x.2, 0) :=
    ((measurable_averageKernel m).comp (measurable_const.prodMk
      ((measurable_snd.prodMk measurable_fst).prodMk measurable_const))).mul
      (hG.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_const)))
  calc ∫⁻ w, jointTransportKernel m G (H, w, 0) ∂volume
      = ∫⁻ z : ℂ, ∫⁻ q, averageKernel m (H, (q, z), 0) * G (H, q, 0)
          ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) ∂volume := by
        rw [← (MeasurePreserving.symm _ measurePreserving_planeCoordMeas).lintegral_comp_emb
          planeCoordMeas.symm.measurableEmbedding
          (fun z : ℂ => ∫⁻ q, averageKernel m (H, (q, z), 0) * G (H, q, 0)
            ∂(unifIco 1).prod (offsetLaw.prod offsetLaw))]
        refine lintegral_congr fun w => ?_
        simp only [jointTransportKernel, map_zero]
        rfl
    _ = ∫⁻ q, ∫⁻ z : ℂ, averageKernel m (H, (q, z), 0) * G (H, q, 0) ∂volume
          ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) :=
        lintegral_lintegral_swap (f := fun z q => averageKernel m (H, (q, z), 0) * G (H, q, 0))
          hK.aemeasurable
    _ = ∫⁻ q, (∫⁻ z : ℂ, averageKernel m (H, (q, z), 0) ∂volume) * G (H, q, 0)
          ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) :=
        lintegral_congr fun q => lintegral_mul_const _ ((measurable_averageKernel m).comp
          (measurable_const.prodMk ((measurable_const.prodMk measurable_id).prodMk
            measurable_const)))
    _ = _ := lintegral_congr_ae ((ae_lintegral_averageKernel_reverse H 0).mono
          fun q hq => by beta_reduce; rw [hq m hm0 hmtop, one_mul])

/-- **Joint mass transport for the capped squares** ((B.6) of arXiv 1807.07515, joint form): under
the mass-transport principle, for every cell mass `m ∈ (0, ∞)` and every measurable
`G(H, D, w) ≥ 0` invariant under the joint similarity, `G(C(H - u), C(D - u), C(w - u)) =
G(H, D, w)` for every dyadic system `D` with compatible offset sequences, `E[|S_m^0|⁻¹ ∫ 1(z ∈ S_m^0) G(H, D, z) dz] = E[G(H, D, 0)]`, both expectations taken
over the configuration and the independent uniform dyadic system `D`. -/
theorem lintegral_cappedSquare_average_eq_joint {μ : Measure GMSSpace} (hMT : MassTransport μ)
    {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w)) :
    ∫⁻ H, ∫⁻ q, ∫⁻ z, (volume (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2)
          (cellMass volume (complexCells H.1)) m 0))⁻¹ *
        (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2)
          (cellMass volume (complexCells H.1)) m 0).indicator (fun _ => (1 : ℝ≥0∞)) z *
        G (H, q, z) ∂volume ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) ∂μ =
      ∫⁻ H, ∫⁻ q, G (H, q, 0) ∂(unifIco 1).prod (offsetLaw.prod offsetLaw) ∂μ := by
  have h := massTransport_ennreal (jointTransportKernel m G) hMT
    (measurable_jointTransportKernel m hG)
    (fun s u hs H H' hHH' w₀ w₁ =>
      jointTransportKernel_similarity hm0 hmtop hG hHH' (hinv s u hs H H' hHH') w₀ w₁)
  simp only [lintegral_jointTransportKernel_zero_left hm0 hmtop hG,
    lintegral_jointTransportKernel_zero_right hm0 hmtop hG] at h
  exact h

end LatticeProb.CellConfigCappedSquare
