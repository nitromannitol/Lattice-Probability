import LatticeProb.Prob.CellConfigOriginSquares

/-!
# Ergodic averages of a signed integrable function over the squares around the origin

Let `H` be a random cell configuration with law `μ` satisfying the mass-transport principle, `D` an
independent uniform dyadic system with coordinates `q`, `S_m^0` the capped square of cell mass `m`
around the origin and `S_k` the square of generation `k` of `D` containing the origin. For a
measurable similarity-invariant `F(H, D, w) ≥ 0` with `E[F(H, D, 0)] < ∞`, the uniform averages of
`F` over `S_m^0` (as `m → ∞`) and over `S_k` (as `k → ∞`) converge to `E[F(H, D, 0) | 𝓘]`
(Gwynne, Miller and Sheffield, *An invariance principle for ergodic scale-free random
environments*, arXiv 1807.07515, Lemma 2.7, (2.3)). Here the same is shown for a signed `F` with
`E[|F(H, D, 0)|] < ∞`, by splitting `F = F⁺ - F⁻` and using the linearity of the conditional
expectation.

Since `E[|F|(H, D, 0)] = E[|S_m^0|⁻¹ ∫_{S_m^0} |F|(H, D, z) dz] < ∞` for every cell mass
`m ∈ (0, ∞)`, almost surely `F(H, D, ·)` is integrable on every `S_m^0` and on every `S_k`, so that
the averages are Bochner set averages `⨍_{S} F(H, D, z) dz`.

## Main results
* `ae_ae_integrableOn_originCappedSquare`, `ae_ae_integrableOn_squareAt`: almost surely
  `F(H, D, ·)` is integrable on every capped square `S_m^0`, `m ∈ (0, ∞)`, and on every square
  `S_k` around the origin.
* `ae_ae_tendsto_setAverage_originCappedSquare_condExp`: `⨍_{S_m^0} F(H, D, z) dz → E[F(H, D, 0) | 𝓘]`
  as the cell mass `m → ∞` through `ℝ`.
* `ae_ae_tendsto_setAverage_squareAt_condExp`: `⨍_{S_k} F(H, D, z) dz → E[F(H, D, 0) | 𝓘]` as
  `k → ∞`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-! ### Uniform averages over a set -/

/-- The extended uniform average `∫ |S|⁻¹ 1_S g` of `g ≥ 0` over a measurable set `S` is
`|S|⁻¹ ∫_S g`. -/
theorem lintegral_inv_volume_mul_indicator_mul {S : Set ℂ} (hS : MeasurableSet S)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, (volume S)⁻¹ * S.indicator (fun _ => (1 : ℝ≥0∞)) z * g z =
      (volume S)⁻¹ * ∫⁻ z in S, g z := by
  rw [← lintegral_indicator hS, ← lintegral_const_mul _ (hg.indicator hS)]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz, indicator_of_mem hz, mul_one]
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, mul_zero, zero_mul]

/-- A measurable `g` whose extended uniform average of `‖g‖` over a measurable set `S` of finite
volume is finite is integrable on `S`. -/
theorem integrableOn_of_average_enorm_ne_top {S : Set ℂ} (hS : MeasurableSet S)
    (hSfin : volume S ≠ ∞) {g : ℂ → ℝ} (hg : Measurable g)
    (h : ∫⁻ z, (volume S)⁻¹ * S.indicator (fun _ => (1 : ℝ≥0∞)) z * ‖g z‖ₑ ≠ ∞) :
    IntegrableOn g S := by
  rw [lintegral_inv_volume_mul_indicator_mul hS hg.enorm] at h
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  show ∫⁻ z in S, ‖g z‖ₑ < ∞
  refine lt_top_iff_ne_top.2 fun htop => h ?_
  rw [htop]
  exact ENNReal.mul_top (ENNReal.inv_ne_zero.2 hSfin)

/-- For `g` integrable on a measurable set `S`, the difference of the extended uniform averages of
`g⁺` and `g⁻` over `S` is the set average `⨍_S g`. -/
theorem toReal_average_ofReal_sub_eq_setAverage {S : Set ℂ} (hS : MeasurableSet S) {g : ℂ → ℝ}
    (hg : Measurable g) (hint : IntegrableOn g S) :
    (∫⁻ z, (volume S)⁻¹ * S.indicator (fun _ => (1 : ℝ≥0∞)) z * ENNReal.ofReal (g z)).toReal -
        (∫⁻ z, (volume S)⁻¹ * S.indicator (fun _ => (1 : ℝ≥0∞)) z *
          ENNReal.ofReal (-g z)).toReal =
      ⨍ z in S, g z := by
  have hN : Measurable fun z => ENNReal.ofReal (-g z) := hg.neg.ennreal_ofReal
  rw [lintegral_inv_volume_mul_indicator_mul hS hg.ennreal_ofReal,
    lintegral_inv_volume_mul_indicator_mul hS hN, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ← mul_sub, ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
    setAverage_eq, smul_eq_mul, measureReal_def, ENNReal.toReal_inv]

/-! ### Almost sure integrability on the capped squares -/

/-- A function of a similarity-invariant `F` is similarity-invariant. -/
theorem similarity_invariant_comp {β : Type*} {F : GMSSpace × DyadicCoord × ℂ → ℝ}
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        F (H', similarityCoord s u q, s • w + similarityOffset s u) = F (H, q, w))
    (φ : ℝ → β) :
    ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        φ (F (H', similarityCoord s u q, s • w + similarityOffset s u)) = φ (F (H, q, w)) :=
  fun s u hs H H' h q h₁ h₂ w => by rw [hinv s u hs H H' h q h₁ h₂ w]

/-- For every configuration and almost every dyadic system, every capped square `S_m^0` with
`m ∈ (0, ∞)` is a square of the dyadic system containing the origin (arXiv 1807.07515, (2.1) and
Lemma 2.2). -/
theorem ae_exists_originCappedSquare_eq_squareAt (H : GMSSpace) :
    ∀ᵐ q ∂dyadicLaw, ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      ∃ j : ℤ, originCappedSquare m H q = squareAt q.1 q.2.1 q.2.2 j 0 := by
  have := countable_cells H.2
  filter_upwards [ae_exists_isCappedSquare_squareAt_cellMass 0 (locallyFinite_complexCells H.2)
      (iUnion_complexCells H.2) isCompact_complexCells (volume_complexCells_ne_zero H.2)]
    with q hex m hm0 hmtop
  obtain ⟨j, -, -, hj⟩ := hex m hm0 hmtop
  exact ⟨j, hj.cappedSquare_eq⟩

section Signed

variable {μ : Measure GMSSpace}

/-- Under the mass-transport principle, for a cell mass `m ∈ (0, ∞)` and a measurable
similarity-invariant `G ≥ 0` with `E[G(H, D, 0)] < ∞`, the uniform average
`|S_m^0|⁻¹ ∫_{S_m^0} G(H, D, z) dz` is finite almost surely: its expectation is `E[G(H, D, 0)]`. -/
theorem ae_ae_cappedSquareAverage_ne_top (hMT : MassTransport μ) {m : ℝ≥0∞} (hm0 : m ≠ 0)
    (hmtop : m ≠ ∞) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (hfin : ∫⁻ p, G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, cappedSquareAverage m G H q ≠ ∞ := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hK : Measurable fun p : GMSSpace × DyadicCoord => kernelAverage m G (p.1, p.2, 0) :=
    (measurable_kernelAverage m hG).comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hKfin : ∫⁻ p, kernelAverage m G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞ := by
    have h := setLIntegral_kernelAverage_origin hMT hm0 hmtop hG hinv
      (@MeasurableSet.univ _ (cappedSquareSigma m))
    simp only [Measure.restrict_univ] at h
    rw [h]
    exact hfin
  filter_upwards [Measure.ae_ae_of_ae_prod (ae_lt_top hK hKfin)] with H hH
  filter_upwards [hH, ae_kernelAverage_origin_eq hm0 hmtop G H] with q hq heq
  rw [← heq]
  exact hq.ne

/-- **Almost sure integrability on the capped squares**: under the mass-transport principle, for
a measurable similarity-invariant `F` with `E[|F(H, D, 0)|] < ∞`, for `μ`-almost every
configuration `H` and almost every dyadic system `D`, `F(H, D, ·)` is integrable on every capped
square `S_m^0` with `m ∈ (0, ∞)`. -/
theorem ae_ae_integrableOn_originCappedSquare (hMT : MassTransport μ)
    {F : GMSSpace × DyadicCoord × ℂ → ℝ} (hF : Measurable F)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        F (H', similarityCoord s u q, s • w + similarityOffset s u) = F (H, q, w))
    (hint : Integrable (fun p : GMSSpace × DyadicCoord => F (p.1, p.2, 0)) (μ.prod dyadicLaw)) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      IntegrableOn (fun z => F (H, q, z)) (originCappedSquare m H q) := by
  have hfin : ∫⁻ p, ‖F (p.1, p.2, 0)‖ₑ ∂μ.prod dyadicLaw ≠ ∞ :=
    (show ∫⁻ p, ‖F (p.1, p.2, 0)‖ₑ ∂μ.prod dyadicLaw < ∞ from hint.2).ne
  have hr : ∀ r : ℚ, ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, (0 : ℝ) < r →
      cappedSquareAverage (ENNReal.ofReal r) (fun p => ‖F p‖ₑ) H q ≠ ∞ := by
    intro r
    by_cases hr0 : (0 : ℝ) < r
    · filter_upwards [ae_ae_cappedSquareAverage_ne_top hMT (ENNReal.ofReal_pos.2 hr0).ne'
        ENNReal.ofReal_ne_top hF.enorm (similarity_invariant_comp hinv _) hfin] with H hH
      filter_upwards [hH] with q hq _
      exact hq
    · exact Eventually.of_forall fun H => Eventually.of_forall fun q h => absurd h hr0
  filter_upwards [ae_all_iff.2 hr] with H hH
  filter_upwards [ae_all_iff.2 hH, ae_exists_lt_forall_originCappedSquare_eq H,
    ae_exists_originCappedSquare_eq_squareAt H] with q hq hstep hsq m hm0 hmtop
  obtain ⟨m₂, hm₂, hconst⟩ := hstep m hm0 hmtop
  obtain ⟨r, -, hmr, hr2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hm₂
  have hr0 : (0 : ℝ) < r := ENNReal.ofReal_pos.1 ((pos_iff_ne_zero.2 hm0).trans hmr)
  have havg := hq r hr0
  rw [cappedSquareAverage, hconst (ENNReal.ofReal r) hmr.le hr2] at havg
  obtain ⟨j, hj⟩ := hsq m hm0 hmtop
  rw [hj] at havg ⊢
  exact integrableOn_of_average_enorm_ne_top (isCompact_squareAt j 0).isClosed.measurableSet
    (isCompact_squareAt j 0).measure_lt_top.ne (g := fun z => F (H, q, z))
    (hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))) havg

/-- **Almost sure integrability on the squares around the origin**: under the hypotheses of
`ae_ae_integrableOn_originCappedSquare`, for `μ`-almost every configuration and almost every dyadic
system, `F(H, D, ·)` is integrable on the square `S_k` of every generation `k ∈ ℤ` containing the
origin. -/
theorem ae_ae_integrableOn_squareAt (hMT : MassTransport μ)
    {F : GMSSpace × DyadicCoord × ℂ → ℝ} (hF : Measurable F)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        F (H', similarityCoord s u q, s • w + similarityOffset s u) = F (H, q, w))
    (hint : Integrable (fun p : GMSSpace × DyadicCoord => F (p.1, p.2, 0)) (μ.prod dyadicLaw)) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ j : ℤ,
      IntegrableOn (fun z => F (H, q, z)) (squareAt q.1 q.2.1 q.2.2 j 0) := by
  filter_upwards [ae_ae_integrableOn_originCappedSquare hMT hF hinv hint] with H hH
  filter_upwards [hH, ae_strictMono_cellMass_squareAt_origin H,
    ae_originCappedSquare_cellMass_squareAt_eq H] with q hq hmono hsq j
  have h0 : cellMass volume (complexCells H.1) (squareAt q.1 q.2.1 q.2.2 j 0) ≠ 0 := fun h => by
    simpa [h] using hmono (sub_one_lt j)
  have hI := hq _ h0 (cellMass_squareAt_ne_top H q j)
  rwa [hsq j] at hI

/-- **Conditional ergodic lemma along real cell masses, signed form** (arXiv 1807.07515,
Lemma 2.7, (2.3)): under the mass-transport principle, for a finite law `μ` and every measurable
similarity-invariant `F` with `E[|F(H, D, 0)|] < ∞`, for `μ`-almost every configuration `H` and
almost every dyadic system `D`, `⨍_{S_m^0} F(H, D, z) dz → E[F(H, D, 0) | 𝓘](H, D)` as the cell
mass `m → ∞` through `ℝ`. -/
theorem ae_ae_tendsto_setAverage_originCappedSquare_condExp [IsFiniteMeasure μ]
    (hMT : MassTransport μ) {F : GMSSpace × DyadicCoord × ℂ → ℝ} (hF : Measurable F)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        F (H', similarityCoord s u q, s • w + similarityOffset s u) = F (H, q, w))
    (hint : Integrable (fun p : GMSSpace × DyadicCoord => F (p.1, p.2, 0)) (μ.prod dyadicLaw)) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      Tendsto (fun x : ℝ => ⨍ z in originCappedSquare (ENNReal.ofReal x) H q, F (H, q, z))
        atTop
        (𝓝 ((μ.prod dyadicLaw)[fun p => F (p.1, p.2, 0) | cappedSquareTailSigma] (H, q))) := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have h0 : Measurable fun p : GMSSpace × DyadicCoord => F (p.1, p.2, 0) :=
    hF.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hPfin : ∫⁻ p, ENNReal.ofReal (F (p.1, p.2, 0)) ∂μ.prod dyadicLaw ≠ ∞ :=
    hint.lintegral_lt_top.ne
  have hNfin : ∫⁻ p, ENNReal.ofReal (-F (p.1, p.2, 0)) ∂μ.prod dyadicLaw ≠ ∞ :=
    hint.neg.lintegral_lt_top.ne
  have hsub : (μ.prod dyadicLaw)[fun p => F (p.1, p.2, 0) | cappedSquareTailSigma]
      =ᵐ[μ.prod dyadicLaw]
        (μ.prod dyadicLaw)[fun p => (ENNReal.ofReal (F (p.1, p.2, 0))).toReal |
          cappedSquareTailSigma] -
        (μ.prod dyadicLaw)[fun p => (ENNReal.ofReal (-F (p.1, p.2, 0))).toReal |
          cappedSquareTailSigma] := by
    have e : (fun p : GMSSpace × DyadicCoord => F (p.1, p.2, 0)) =
        (fun p => (ENNReal.ofReal (F (p.1, p.2, 0))).toReal) -
          fun p => (ENNReal.ofReal (-F (p.1, p.2, 0))).toReal := by
      funext p
      simp only [Pi.sub_apply, ENNReal.toReal_ofReal', max_zero_sub_max_neg_zero_eq_self]
    rw [e]
    exact condExp_sub (m := cappedSquareTailSigma)
      (integrable_toReal_of_lintegral_ne_top h0.ennreal_ofReal.aemeasurable hPfin)
      (integrable_toReal_of_lintegral_ne_top h0.neg.ennreal_ofReal.aemeasurable hNfin)
  filter_upwards [ae_ae_tendsto_cappedSquareAverage_ofReal hMT (G := fun p => ENNReal.ofReal (F p))
      hF.ennreal_ofReal (similarity_invariant_comp hinv _) hPfin,
    ae_ae_tendsto_cappedSquareAverage_ofReal hMT (G := fun p => ENNReal.ofReal (-F p))
      hF.neg.ennreal_ofReal (similarity_invariant_comp hinv fun t => ENNReal.ofReal (-t)) hNfin,
    Measure.ae_ae_of_ae_prod hsub, ae_ae_integrableOn_originCappedSquare hMT hF hinv hint]
    with H hHP hHN hHsub hHint
  filter_upwards [hHP, hHN, hHsub, hHint, ae_exists_originCappedSquare_eq_squareAt H]
    with q hqP hqN hqsub hqint hqsq
  rw [hqsub]
  refine (hqP.sub hqN).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : ENNReal.ofReal x ≠ 0 := (ENNReal.ofReal_pos.2 hx).ne'
  have hI := hqint _ hx0 ENNReal.ofReal_ne_top
  obtain ⟨j, hj⟩ := hqsq _ hx0 ENNReal.ofReal_ne_top
  rw [hj] at hI
  rw [cappedSquareAverage, cappedSquareAverage, hj]
  exact toReal_average_ofReal_sub_eq_setAverage (isCompact_squareAt j 0).isClosed.measurableSet
    (g := fun z => F (H, q, z))
    (hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))) hI

/-- **Conditional ergodic lemma along the squares around the origin, signed form**
(arXiv 1807.07515, Lemma 2.7, (2.3)): under the mass-transport principle, for a finite law `μ` and
every measurable similarity-invariant `F` with `E[|F(H, D, 0)|] < ∞`, for `μ`-almost every
configuration `H` and almost every dyadic system `D`, the set averages `⨍_{S_k} F(H, D, z) dz` over
the squares `S_k` of generation `k` containing the origin converge to `E[F(H, D, 0) | 𝓘](H, D)` as
`k → ∞`. -/
theorem ae_ae_tendsto_setAverage_squareAt_condExp [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {F : GMSSpace × DyadicCoord × ℂ → ℝ} (hF : Measurable F)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        F (H', similarityCoord s u q, s • w + similarityOffset s u) = F (H, q, w))
    (hint : Integrable (fun p : GMSSpace × DyadicCoord => F (p.1, p.2, 0)) (μ.prod dyadicLaw)) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      Tendsto (fun j : ℤ => ⨍ z in squareAt q.1 q.2.1 q.2.2 j 0, F (H, q, z)) atTop
        (𝓝 ((μ.prod dyadicLaw)[fun p => F (p.1, p.2, 0) | cappedSquareTailSigma] (H, q))) := by
  filter_upwards [ae_ae_tendsto_setAverage_originCappedSquare_condExp hMT hF hinv hint]
    with H hH
  filter_upwards [hH, ae_tendsto_cellMass_squareAt_origin_atTop H,
    ae_originCappedSquare_cellMass_squareAt_eq H] with q hq htop hsq
  have hreal := tendsto_toReal_atTop_of_tendsto_top htop fun j => cellMass_squareAt_ne_top H q j
  refine (hq.comp hreal).congr fun j => ?_
  simp only [Function.comp_apply, ENNReal.ofReal_toReal (cellMass_squareAt_ne_top H q j), hsq j]

end Signed

end LatticeProb.CellConfigCappedSquare
