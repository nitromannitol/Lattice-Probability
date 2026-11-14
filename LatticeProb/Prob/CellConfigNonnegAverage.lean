import LatticeProb.Prob.CellConfigCappedSquareTailSup
import LatticeProb.Prob.CellConfigOriginSquares

/-!
# Averages of a nonnegative function over the squares around the origin

Let `H` be a random cell configuration with law `μ` satisfying the mass-transport principle, `D` an
independent uniform dyadic system with coordinates `q`, and `𝓘 = ⋂_k 𝓕_{k+1}` the tail σ-algebra
(`cappedSquareTailSigma`). For a measurable `G ≥ 0` invariant under the joint similarity, with no
integrability assumption, the conditional expectation `E[G(H, D, 0) | 𝓘]` is replaced by the
supremum of the truncated conditional expectations
`J = sup_N E[G(H, D, 0) ∧ N | 𝓘]` (`truncCondExpSup`). This file proves (2.3) of arXiv 1807.07515
(Lemma 2.7) for such `G`: almost surely the uniform averages of `G(H, D, ·)` over the capped squares
`S_m^0` (as `m → ∞` through `ℝ`) and over the squares `S_k` of generation `k` containing the origin
converge in `[0, ∞]` to `J`.

The lower bound follows from the integrable case applied to the truncations `G ∧ N`. For the upper
bound on `{J < ∞}` the integrable case is applied to `G · 1{J̃ G ≤ R}`, where `J̃ G` is the rooted tail
supremum (`rootedTailSup`): an invariant version of `J` whose level sets are block constant, so that
the averages of `G` and of `G · 1{J̃ G ≤ R}` agree on `{J̃ G(H, D, 0) ≤ R}`; the limit
`E[G(H, D, 0) 1{J ≤ R} | 𝓘]` is identified with `J` on `{J ≤ R}` by comparing integrals over `𝓘`-sets.

## Main results
* `ae_ae_tendsto_cappedSquareAverage_ofReal_iSup_condExp`: the averages over `S_m^0`, `m → ∞`
  through `ℝ`, converge to `J`.
* `ae_ae_tendsto_squareAt_average_iSup_condExp`: the averages over the squares `S_k` of generation
  `k ∈ ℤ` containing the origin converge to `J` as `k → ∞`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-! ### Capped squares of real and rational mass; averages -/

/-- For every configuration and almost every dyadic system, every capped square around the origin
of real mass `x ≥ 1` is the capped square of a rational mass `max(r, 1)`. -/
theorem ae_exists_rat_originCappedSquare_eq (H : GMSSpace) :
    ∀ᵐ q ∂dyadicLaw, ∀ x : ℝ, 1 ≤ x → ∃ r : ℚ,
      originCappedSquare (ENNReal.ofReal x) H q = originCappedSquare (ratMass r) H q := by
  filter_upwards [ae_exists_lt_forall_originCappedSquare_eq H] with q hstep
  intro x hx
  have hx0 : ENNReal.ofReal x ≠ 0 := (ENNReal.ofReal_pos.2 (zero_lt_one.trans_le hx)).ne'
  obtain ⟨m₂, hm₂, hconst⟩ := hstep _ hx0 ENNReal.ofReal_ne_top
  obtain ⟨r, -, hxr, hr2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hm₂
  have hxr' : x ≤ r := (ENNReal.ofReal_lt_ofReal_iff'.1 hxr).1.le
  have hmr : ratMass r = ENNReal.ofReal r := by rw [ratMass, max_eq_left (hx.trans hxr')]
  refine ⟨r, ?_⟩
  rw [hmr]
  exact (hconst _ (ENNReal.ofReal_le_ofReal hxr') hr2).symm

/-- Two functions that agree almost everywhere on the capped square `S_m^0(H, D)` have the same
capped-square average. -/
theorem cappedSquareAverage_congr_ae {m : ℝ≥0∞} {G G' : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    {H : GMSSpace} {q : DyadicCoord}
    (h : ∀ᵐ z ∂volume, z ∈ originCappedSquare m H q → G (H, q, z) = G' (H, q, z)) :
    cappedSquareAverage m G H q = cappedSquareAverage m G' H q := by
  unfold cappedSquareAverage
  refine lintegral_congr_ae ?_
  filter_upwards [h] with z hz
  by_cases hzS : z ∈ originCappedSquare m H q
  · rw [hz hzS]
  · simp only [indicator_of_notMem hzS, mul_zero, zero_mul]

/-- Monotonicity of the capped-square average in the function. -/
theorem cappedSquareAverage_mono {m : ℝ≥0∞} {G G' : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (h : ∀ p, G p ≤ G' p) (H : GMSSpace) (q : DyadicCoord) :
    cappedSquareAverage m G H q ≤ cappedSquareAverage m G' H q :=
  lintegral_mono fun z => by gcongr; exact h _

/-! ### The integrable case in `[0, ∞]` -/

section Integrable

variable {μ : Measure GMSSpace}

/-- Under the hypotheses of `ae_ae_tendsto_cappedSquareAverage_ofReal` (in particular
`E[G(H, D, 0)] < ∞`), for `μ`-almost every configuration and almost every dyadic system, the
capped-square averages of `G` of every real mass `x ≥ 1` are finite. -/
theorem ae_ae_cappedSquareAverage_ofReal_ne_top [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (hfin : ∫⁻ p, G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ x : ℝ, 1 ≤ x →
      cappedSquareAverage (ENNReal.ofReal x) G H q ≠ ∞ := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hK : ∀ r : ℚ, ∀ᵐ p ∂μ.prod dyadicLaw,
      kernelAverage (ratMass r) G (p.1, p.2, 0) < ∞ := by
    intro r
    have h := setLIntegral_kernelAverage_origin hMT (ratMass_ne_zero r) (ratMass_ne_top r) hG hinv
      (@MeasurableSet.univ _ (cappedSquareSigma (ratMass r)))
    simp only [Measure.restrict_univ] at h
    refine ae_lt_top ((measurable_kernelAverage _ hG).comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))) ?_
    rw [h]
    exact hfin
  filter_upwards [Measure.ae_ae_of_ae_prod (ae_all_iff.2 hK)] with H hH
  filter_upwards [hH, ae_all_iff.2 fun r : ℚ =>
      ae_kernelAverage_origin_eq (ratMass_ne_zero r) (ratMass_ne_top r) G H,
    ae_exists_rat_originCappedSquare_eq H] with q hq hkq hrat
  intro x hx
  obtain ⟨r, hr⟩ := hrat x hx
  have hxr : cappedSquareAverage (ENNReal.ofReal x) G H q = cappedSquareAverage (ratMass r) G H q := by
    simp only [cappedSquareAverage, hr]
  rw [hxr, ← hkq r]
  exact (hq r).ne

/-- **Conditional ergodic lemma along real masses in `[0, ∞]`**: under the hypotheses of
`ae_ae_tendsto_cappedSquareAverage_ofReal`, for `μ`-almost every configuration and almost every
dyadic system, the capped-square averages `|S_x^0|⁻¹ ∫_{S_x^0} G(H, D, z) dz` converge in `[0, ∞]`
to `E[G(H, D, 0) | 𝓘](H, D)` as the mass `x → ∞` through `ℝ`. -/
theorem ae_ae_tendsto_cappedSquareAverage_ofReal_condExp [IsFiniteMeasure μ]
    (hMT : MassTransport μ) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (hfin : ∫⁻ p, G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      Tendsto (fun x : ℝ => cappedSquareAverage (ENNReal.ofReal x) G H q) atTop
        (𝓝 (ENNReal.ofReal ((μ.prod dyadicLaw)[fun p => (G (p.1, p.2, 0)).toReal |
          cappedSquareTailSigma] (H, q)))) := by
  filter_upwards [ae_ae_tendsto_cappedSquareAverage_ofReal hMT hG hinv hfin,
    ae_ae_cappedSquareAverage_ofReal_ne_top hMT hG hinv hfin] with H hH hHfin
  filter_upwards [hH, hHfin] with q hq hqfin
  refine ((ENNReal.continuous_ofReal.tendsto _).comp hq).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact ENNReal.ofReal_toReal (hqfin x hx)

end Integrable

/-! ### The supremum of the truncated conditional expectations -/

/-- **The supremum of the truncated conditional expectations given the tail σ-algebra**
`J(H, D) = sup_N E[G(H, D, 0) ∧ N | 𝓘](H, D)` under `μ ⊗ P` (arXiv 1807.07515, Lemma 2.7 for a
non-integrable `G ≥ 0`). For an integrable `G` it is a version of `E[G(H, D, 0) | 𝓘]`; in general it
replaces this conditional expectation, which is not defined. -/
noncomputable def truncCondExpSup (μ : Measure GMSSpace) (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞)
    (p : GMSSpace × DyadicCoord) : ℝ≥0∞ :=
  ⨆ N : ℕ, ENNReal.ofReal ((μ.prod dyadicLaw)[fun p =>
    (min (G (p.1, p.2, 0)) (N : ℝ≥0∞)).toReal | cappedSquareTailSigma] p)

section TailSup

variable {μ : Measure GMSSpace}

/-- For a measurable `g ≥ 0` of finite integral under `μ ⊗ P` and every event `A ∈ 𝓘`,
`∫_A g = ∫_A E[g | 𝓘]`. -/
theorem setLIntegral_eq_setLIntegral_ofReal_condExp [IsFiniteMeasure μ]
    {g : GMSSpace × DyadicCoord → ℝ≥0∞} (hg : Measurable g)
    (hfin : ∫⁻ p, g p ∂μ.prod dyadicLaw ≠ ∞) {A : Set (GMSSpace × DyadicCoord)}
    (hA : MeasurableSet[cappedSquareTailSigma] A) :
    ∫⁻ p in A, g p ∂μ.prod dyadicLaw =
      ∫⁻ p in A, ENNReal.ofReal ((μ.prod dyadicLaw)[fun p => (g p).toReal |
        cappedSquareTailSigma] p) ∂μ.prod dyadicLaw := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have : IsFiniteMeasure ((μ.prod dyadicLaw).trim cappedSquareTailSigma_le) :=
    isFiniteMeasure_trim _
  have hint : Integrable (fun p => (g p).toReal) (μ.prod dyadicLaw) :=
    integrable_toReal_of_lintegral_ne_top hg.aemeasurable hfin
  have hc : Integrable ((μ.prod dyadicLaw)[fun p => (g p).toReal | cappedSquareTailSigma])
      (μ.prod dyadicLaw) := integrable_condExp
  have hc0 : 0 ≤ᵐ[μ.prod dyadicLaw]
      (μ.prod dyadicLaw)[fun p => (g p).toReal | cappedSquareTailSigma] :=
    condExp_nonneg (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  have h1 : ∫⁻ p in A, g p ∂μ.prod dyadicLaw =
      ∫⁻ p in A, ENNReal.ofReal (g p).toReal ∂μ.prod dyadicLaw :=
    lintegral_congr_ae (ae_restrict_of_ae ((ae_lt_top hg hfin).mono fun p hp =>
      (ENNReal.ofReal_toReal hp.ne).symm))
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg),
    ← setIntegral_condExp cappedSquareTailSigma_le hint hA,
    ofReal_integral_eq_lintegral_ofReal hc.integrableOn (ae_restrict_of_ae hc0)]

/-- Every `x ∈ [0, ∞]` is the supremum of its truncations `x ∧ N`, `N ∈ ℕ`. -/
theorem eq_iSup_min_natCast (x : ℝ≥0∞) : x = ⨆ N : ℕ, min x (N : ℝ≥0∞) := by
  refine le_antisymm ?_ (iSup_le fun N => min_le_left _ _)
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hc.ne_top
  exact lt_of_lt_of_le (lt_min hc hN) (le_iSup (fun N : ℕ => min x (N : ℝ≥0∞)) N)

/-- **Conditional monotone convergence, integrated form**: for a measurable `G ≥ 0` and every event
`A ∈ 𝓘`, `∫_A G(H, D, 0) ≤ ∫_A J` with `J = sup_N E[G(H, D, 0) ∧ N | 𝓘]`. -/
theorem setLIntegral_origin_le_truncCondExpSup [IsFiniteMeasure μ]
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    {A : Set (GMSSpace × DyadicCoord)} (hA : MeasurableSet[cappedSquareTailSigma] A) :
    ∫⁻ p in A, G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≤
      ∫⁻ p in A, truncCondExpSup μ G p ∂μ.prod dyadicLaw := by
  have hG0 : Measurable fun p : GMSSpace × DyadicCoord => G (p.1, p.2, 0) :=
    hG.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  calc ∫⁻ p in A, G (p.1, p.2, 0) ∂μ.prod dyadicLaw
      = ∫⁻ p in A, ⨆ N : ℕ, min (G (p.1, p.2, 0)) (N : ℝ≥0∞) ∂μ.prod dyadicLaw :=
        lintegral_congr fun p => eq_iSup_min_natCast _
    _ = ⨆ N : ℕ, ∫⁻ p in A, min (G (p.1, p.2, 0)) (N : ℝ≥0∞) ∂μ.prod dyadicLaw :=
        lintegral_iSup (f := fun (N : ℕ) (p : GMSSpace × DyadicCoord) =>
            min (G (p.1, p.2, 0)) (N : ℝ≥0∞))
          (fun _ => hG0.min measurable_const)
          (fun N N' h p => min_le_min_left _ (Nat.cast_le.2 h))
    _ ≤ ∫⁻ p in A, truncCondExpSup μ G p ∂μ.prod dyadicLaw := iSup_le fun N => by
        rw [setLIntegral_eq_setLIntegral_ofReal_condExp
          (g := fun p : GMSSpace × DyadicCoord => min (G (p.1, p.2, 0)) (N : ℝ≥0∞))
          (hG0.min measurable_const) (lintegral_min_origin_ne_top G N) hA]
        exact lintegral_mono fun p => le_iSup_of_le N le_rfl

/-- If `J ≤ R < ∞` almost everywhere on an event `A ∈ 𝓘`, then `G(H, D, 0) 1_A` has a finite
integral under `μ ⊗ P`. -/
theorem lintegral_indicator_origin_ne_top [IsFiniteMeasure μ]
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    {A : Set (GMSSpace × DyadicCoord)} (hA : MeasurableSet[cappedSquareTailSigma] A)
    {R : ℝ≥0∞} (hR : R ≠ ∞)
    (hJR : ∀ᵐ p ∂μ.prod dyadicLaw, p ∈ A → truncCondExpSup μ G p ≤ R) :
    ∫⁻ p, A.indicator (fun p => G (p.1, p.2, 0)) p ∂μ.prod dyadicLaw ≠ ∞ := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hAm : MeasurableSet A := cappedSquareTailSigma_le A hA
  rw [lintegral_indicator hAm]
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hR (measure_ne_top (μ.prod dyadicLaw) A)) ?_
  calc ∫⁻ p in A, G (p.1, p.2, 0) ∂μ.prod dyadicLaw
      ≤ ∫⁻ p in A, truncCondExpSup μ G p ∂μ.prod dyadicLaw :=
        setLIntegral_origin_le_truncCondExpSup hG hA
    _ ≤ ∫⁻ _ in A, R ∂μ.prod dyadicLaw := lintegral_mono_ae ((ae_restrict_iff' hAm).2 hJR)
    _ = R * (μ.prod dyadicLaw) A := setLIntegral_const A R

/-- **Localisation of the conditional expectation**: if `J ≤ R < ∞` almost everywhere on an event
`A ∈ 𝓘`, then almost everywhere on `A`, `E[G(H, D, 0) 1_A | 𝓘] = J`. Proof: `E[(G ∧ N) 1_A | 𝓘] =
1_A E[G ∧ N | 𝓘]` gives `J ≤ E[G 1_A | 𝓘]` on `A`, and both sides have the same integral over `A`,
finite. -/
theorem ae_ofReal_condExp_indicator_origin_eq [IsFiniteMeasure μ]
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    {A : Set (GMSSpace × DyadicCoord)} (hA : MeasurableSet[cappedSquareTailSigma] A)
    {R : ℝ≥0∞} (hR : R ≠ ∞)
    (hJR : ∀ᵐ p ∂μ.prod dyadicLaw, p ∈ A → truncCondExpSup μ G p ≤ R) :
    ∀ᵐ p ∂μ.prod dyadicLaw, p ∈ A →
      ENNReal.ofReal ((μ.prod dyadicLaw)[fun p =>
          (A.indicator (fun p => G (p.1, p.2, 0)) p).toReal | cappedSquareTailSigma] p) =
        truncCondExpSup μ G p := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have : IsFiniteMeasure ((μ.prod dyadicLaw).trim cappedSquareTailSigma_le) :=
    isFiniteMeasure_trim _
  have hAm : MeasurableSet A := cappedSquareTailSigma_le A hA
  have hG0 : Measurable fun p : GMSSpace × DyadicCoord => G (p.1, p.2, 0) :=
    hG.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hg : Measurable (A.indicator fun p : GMSSpace × DyadicCoord => G (p.1, p.2, 0)) :=
    hG0.indicator hAm
  have hgfin := lintegral_indicator_origin_ne_top hG hA hR hJR
  have hgint : Integrable (fun p =>
      (A.indicator (fun p : GMSSpace × DyadicCoord => G (p.1, p.2, 0)) p).toReal)
      (μ.prod dyadicLaw) :=
    integrable_toReal_of_lintegral_ne_top hg.aemeasurable hgfin
  have hle : ∀ᵐ p ∂(μ.prod dyadicLaw).restrict A, truncCondExpSup μ G p ≤
      ENNReal.ofReal ((μ.prod dyadicLaw)[fun p =>
        (A.indicator (fun p => G (p.1, p.2, 0)) p).toReal | cappedSquareTailSigma] p) := by
    have hN : ∀ N : ℕ, ∀ᵐ p ∂μ.prod dyadicLaw, p ∈ A →
        (μ.prod dyadicLaw)[fun p => (min (G (p.1, p.2, 0)) (N : ℝ≥0∞)).toReal |
            cappedSquareTailSigma] p ≤
          (μ.prod dyadicLaw)[fun p => (A.indicator (fun p => G (p.1, p.2, 0)) p).toReal |
            cappedSquareTailSigma] p := by
      intro N
      have hfN : Integrable (fun p : GMSSpace × DyadicCoord =>
          (min (G (p.1, p.2, 0)) (N : ℝ≥0∞)).toReal) (μ.prod dyadicLaw) :=
        integrable_toReal_of_lintegral_ne_top (hG0.min measurable_const).aemeasurable
          (lintegral_min_origin_ne_top G N)
      have hmono : (μ.prod dyadicLaw)[A.indicator (fun p : GMSSpace × DyadicCoord =>
            (min (G (p.1, p.2, 0)) (N : ℝ≥0∞)).toReal) | cappedSquareTailSigma]
          ≤ᵐ[μ.prod dyadicLaw]
          (μ.prod dyadicLaw)[fun p => (A.indicator (fun p => G (p.1, p.2, 0)) p).toReal |
            cappedSquareTailSigma] := by
        refine condExp_mono (hfN.indicator hAm) hgint ?_
        filter_upwards [ae_lt_top hg hgfin] with p hp
        by_cases hpA : p ∈ A
        · simp only [indicator_of_mem hpA] at hp ⊢
          exact ENNReal.toReal_mono hp.ne (min_le_left _ _)
        · simp only [indicator_of_notMem hpA, ENNReal.toReal_zero, le_refl]
      filter_upwards [condExp_indicator hfN hA, hmono] with p hp1 hp2 hpA
      rw [hp1, indicator_of_mem hpA] at hp2
      exact hp2
    refine (ae_restrict_iff' hAm).2 ?_
    filter_upwards [ae_all_iff.2 hN] with p hp hpA
    exact iSup_le fun N => ENNReal.ofReal_le_ofReal (hp N hpA)
  have hint_le : ∫⁻ p in A, ENNReal.ofReal ((μ.prod dyadicLaw)[fun p =>
        (A.indicator (fun p => G (p.1, p.2, 0)) p).toReal | cappedSquareTailSigma] p)
        ∂μ.prod dyadicLaw ≤
      ∫⁻ p in A, truncCondExpSup μ G p ∂μ.prod dyadicLaw := by
    rw [← setLIntegral_eq_setLIntegral_ofReal_condExp hg hgfin hA]
    calc ∫⁻ p in A, A.indicator (fun p => G (p.1, p.2, 0)) p ∂μ.prod dyadicLaw
        ≤ ∫⁻ p in A, G (p.1, p.2, 0) ∂μ.prod dyadicLaw :=
          lintegral_mono fun p => indicator_le_self A _ p
      _ ≤ _ := setLIntegral_origin_le_truncCondExpSup hG hA
  have hfinJ : ∫⁻ p in A, truncCondExpSup μ G p ∂μ.prod dyadicLaw ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hR (measure_ne_top (μ.prod dyadicLaw) A)) ?_
    calc ∫⁻ p in A, truncCondExpSup μ G p ∂μ.prod dyadicLaw
        ≤ ∫⁻ _ in A, R ∂μ.prod dyadicLaw := lintegral_mono_ae ((ae_restrict_iff' hAm).2 hJR)
      _ = R * (μ.prod dyadicLaw) A := setLIntegral_const A R
  have hmeas : AEMeasurable (fun p => ENNReal.ofReal ((μ.prod dyadicLaw)[fun p =>
      (A.indicator (fun p => G (p.1, p.2, 0)) p).toReal | cappedSquareTailSigma] p))
      ((μ.prod dyadicLaw).restrict A) :=
    (stronglyMeasurable_condExp.mono cappedSquareTailSigma_le).measurable.ennreal_ofReal.aemeasurable
  filter_upwards [(ae_restrict_iff' hAm).1
    (ae_eq_of_ae_le_of_lintegral_le hle hfinJ hmeas hint_le)] with p hp hpA
  exact (hp hpA).symm

/-! ### The localisation `G · 1{J̃ G ≤ R}` -/

/-- At the origin, `G · 1{J̃ G ≤ R}` is `G(H, D, 0)` times the indicator of the event
`{J̃ G(H, D, 0) ≤ R}`. -/
theorem indicator_rootedTailSup_origin (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞) (R : ℝ≥0∞)
    (p : GMSSpace × DyadicCoord) :
    (rootedTailSup G ⁻¹' Iic R).indicator G (p.1, p.2, 0) =
      {p : GMSSpace × DyadicCoord | rootedTailSup G (p.1, p.2, 0) ≤ R}.indicator
        (fun p => G (p.1, p.2, 0)) p := by
  by_cases hp : rootedTailSup G (p.1, p.2, 0) ≤ R
  · rw [indicator_of_mem (show (p.1, p.2, (0 : ℂ)) ∈ rootedTailSup G ⁻¹' Iic R from hp),
      indicator_of_mem
        (show p ∈ {p : GMSSpace × DyadicCoord | rootedTailSup G (p.1, p.2, 0) ≤ R} from hp)]
  · rw [indicator_of_notMem (show (p.1, p.2, (0 : ℂ)) ∉ rootedTailSup G ⁻¹' Iic R from hp),
      indicator_of_notMem
        (show p ∉ {p : GMSSpace × DyadicCoord | rootedTailSup G (p.1, p.2, 0) ≤ R} from hp)]

/-- **Similarity invariance of `G · 1{J̃ G ≤ R}`**, for a measurable invariant `G ≥ 0`. -/
theorem indicator_rootedTailSup_similarity {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (R : ℝ≥0∞) :
    ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        (rootedTailSup G ⁻¹' Iic R).indicator G
            (H', similarityCoord s u q, s • w + similarityOffset s u) =
          (rootedTailSup G ⁻¹' Iic R).indicator G (H, q, w) := by
  intro s u hs H H' h q h₁ h₂ w
  have hJ := rootedTailSup_similarity hG h h₁ h₂ (hinv s u hs H H' h q h₁ h₂) w
  by_cases hc : rootedTailSup G (H, q, w) ≤ R
  · rw [indicator_of_mem (show (H', similarityCoord s u q, s • w + similarityOffset s u) ∈
        rootedTailSup G ⁻¹' Iic R from hJ.trans_le hc),
      indicator_of_mem (show (H, q, w) ∈ rootedTailSup G ⁻¹' Iic R from hc),
      hinv s u hs H H' h q h₁ h₂ w]
  · rw [indicator_of_notMem (show (H', similarityCoord s u q, s • w + similarityOffset s u) ∉
        rootedTailSup G ⁻¹' Iic R from fun h' => hc (hJ.symm.trans_le h')),
      indicator_of_notMem (show (H, q, w) ∉ rootedTailSup G ⁻¹' Iic R from hc)]

/-- The event `{J̃ G(H, D, 0) ≤ R}` belongs to the tail σ-algebra `𝓘`. -/
theorem measurableSet_rootedTailSup_origin_le {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (R : ℝ≥0∞) :
    MeasurableSet[cappedSquareTailSigma]
      {p : GMSSpace × DyadicCoord | rootedTailSup G (p.1, p.2, 0) ≤ R} :=
  measurable_rootedTailSup_origin_tail hG hinv measurableSet_Iic

/-- Almost surely, `J ≤ R` on the event `{J̃ G(H, D, 0) ≤ R}`. -/
theorem ae_truncCondExpSup_le_of_rootedTailSup_le [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (R : ℝ≥0∞) :
    ∀ᵐ p ∂μ.prod dyadicLaw,
      p ∈ {p : GMSSpace × DyadicCoord | rootedTailSup G (p.1, p.2, 0) ≤ R} →
        truncCondExpSup μ G p ≤ R :=
  (ae_rootedTailSup_origin_eq_iSup_condExp hMT hG hinv).mono fun p hp hpR =>
    (show truncCondExpSup μ G p = rootedTailSup G (p.1, p.2, 0) from hp.symm).trans_le hpR

/-- For `R < ∞`, `G · 1{J̃ G ≤ R}` has a finite integral at the origin under `μ ⊗ P`. -/
theorem lintegral_indicator_rootedTailSup_ne_top [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    {R : ℝ≥0∞} (hR : R ≠ ∞) :
    ∫⁻ p, (rootedTailSup G ⁻¹' Iic R).indicator G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞ := by
  rw [lintegral_congr (indicator_rootedTailSup_origin G R)]
  exact lintegral_indicator_origin_ne_top hG (measurableSet_rootedTailSup_origin_le hG hinv R) hR
    (ae_truncCondExpSup_le_of_rootedTailSup_le hMT hG hinv R)

/-- Almost surely on `{J̃ G(H, D, 0) ≤ R}`, `R < ∞`,
`E[(G · 1{J̃ G ≤ R})(H, D, 0) | 𝓘] = J`. -/
theorem ae_ofReal_condExp_indicator_rootedTailSup_eq [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    {R : ℝ≥0∞} (hR : R ≠ ∞) :
    ∀ᵐ p ∂μ.prod dyadicLaw, rootedTailSup G (p.1, p.2, 0) ≤ R →
      ENNReal.ofReal ((μ.prod dyadicLaw)[fun p =>
          ((rootedTailSup G ⁻¹' Iic R).indicator G (p.1, p.2, 0)).toReal |
            cappedSquareTailSigma] p) =
        truncCondExpSup μ G p := by
  have hfun : (fun p : GMSSpace × DyadicCoord =>
      ((rootedTailSup G ⁻¹' Iic R).indicator G (p.1, p.2, 0)).toReal) = fun p =>
      ({p : GMSSpace × DyadicCoord | rootedTailSup G (p.1, p.2, 0) ≤ R}.indicator
        (fun p => G (p.1, p.2, 0)) p).toReal :=
    funext fun p => by rw [indicator_rootedTailSup_origin]
  rw [hfun]
  exact ae_ofReal_condExp_indicator_origin_eq hG (measurableSet_rootedTailSup_origin_le hG hinv R)
    hR (ae_truncCondExpSup_le_of_rootedTailSup_le hMT hG hinv R)

/-- **Block constancy of the localisation**: for every configuration and almost every dyadic system
with `J̃ G(H, D, 0) ≤ R`, the capped-square averages of `G` and of `G · 1{J̃ G ≤ R}` of every real
mass `x ≥ 1` coincide. -/
theorem ae_cappedSquareAverage_indicator_rootedTailSup_eq
    (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞) (R : ℝ≥0∞) (H : GMSSpace) :
    ∀ᵐ q ∂dyadicLaw, rootedTailSup G (H, q, 0) ≤ R → ∀ x : ℝ, 1 ≤ x →
      cappedSquareAverage (ENNReal.ofReal x) ((rootedTailSup G ⁻¹' Iic R).indicator G) H q =
        cappedSquareAverage (ENNReal.ofReal x) G H q := by
  filter_upwards [ae_exists_rat_originCappedSquare_eq H, ae_all_iff.2 fun r : ℚ =>
    ae_rootedTailSup_eq_origin (ratMass_ne_zero r) (ratMass_ne_top r) G H] with q hrat hblock
  intro hR x hx
  obtain ⟨r, hr⟩ := hrat x hx
  refine cappedSquareAverage_congr_ae ?_
  filter_upwards [hblock r] with z hz hzS
  rw [hr] at hzS
  exact indicator_of_mem (show (H, q, z) ∈ rootedTailSup G ⁻¹' Iic R from (hz hzS).trans_le hR) G

/-! ### Convergence to `J` -/

/-- **Lower bound by truncation**: for `μ`-almost every configuration and almost every dyadic system,
`J ≤ liminf_{x → ∞} |S_x^0|⁻¹ ∫_{S_x^0} G(H, D, z) dz`. -/
theorem ae_ae_truncCondExpSup_le_liminf_cappedSquareAverage [IsFiniteMeasure μ]
    (hMT : MassTransport μ) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w)) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, truncCondExpSup μ G (H, q) ≤
      liminf (fun x : ℝ => cappedSquareAverage (ENNReal.ofReal x) G H q) atTop := by
  have hinvN : ∀ N : ℕ, ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace),
      IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        min (G (H', similarityCoord s u q, s • w + similarityOffset s u)) (N : ℝ≥0∞) =
          min (G (H, q, w)) (N : ℝ≥0∞) :=
    fun N s u hs H H' h q h₁ h₂ w => by rw [hinv s u hs H H' h q h₁ h₂ w]
  have h := fun N : ℕ => ae_ae_tendsto_cappedSquareAverage_ofReal hMT
    (hG.min measurable_const) (hinvN N) (lintegral_min_origin_ne_top G N)
  filter_upwards [ae_all_iff.2 h] with H hH
  filter_upwards [ae_all_iff.2 hH] with q hq
  refine iSup_le fun N => ?_
  have hlim := (ENNReal.continuous_ofReal.tendsto _).comp (hq N)
  refine hlim.liminf_eq.symm.trans_le (liminf_le_liminf (Eventually.of_forall fun x => ?_))
  exact ENNReal.ofReal_toReal_le.trans
    (cappedSquareAverage_mono (fun y => min_le_left _ _) H q)

/-- **Convergence to `J` along real masses**, stated with `truncCondExpSup`. -/
theorem ae_ae_tendsto_cappedSquareAverage_ofReal_truncCondExpSup [IsFiniteMeasure μ]
    (hMT : MassTransport μ) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w)) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      Tendsto (fun x : ℝ => cappedSquareAverage (ENNReal.ofReal x) G H q) atTop
        (𝓝 (truncCondExpSup μ G (H, q))) := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hE := fun R : ℕ => ae_ae_tendsto_cappedSquareAverage_ofReal_condExp hMT
    (hG.indicator (measurable_rootedTailSup hG measurableSet_Iic))
    (indicator_rootedTailSup_similarity hG hinv (R : ℝ≥0∞))
    (lintegral_indicator_rootedTailSup_ne_top hMT hG hinv (ENNReal.natCast_ne_top R))
  have hEq := fun R : ℕ => Measure.ae_ae_of_ae_prod
    (ae_ofReal_condExp_indicator_rootedTailSup_eq hMT hG hinv (μ := μ) (ENNReal.natCast_ne_top R))
  have hJ := Measure.ae_ae_of_ae_prod (ae_rootedTailSup_origin_eq_iSup_condExp hMT hG hinv)
  filter_upwards [ae_all_iff.2 hE, ae_all_iff.2 hEq, hJ,
    ae_ae_truncCondExpSup_le_liminf_cappedSquareAverage hMT hG hinv] with H hHE hHEq hHJ hHlow
  filter_upwards [ae_all_iff.2 hHE, ae_all_iff.2 hHEq, hHJ, hHlow, ae_all_iff.2 fun R : ℕ =>
    ae_cappedSquareAverage_indicator_rootedTailSup_eq G (R : ℝ≥0∞) H]
    with q hqE hqEq hqJ hqlow hqloc
  refine tendsto_of_le_liminf_of_limsup_le hqlow ?_
  rcases eq_top_or_lt_top (truncCondExpSup μ G (H, q)) with htop | hlt
  · exact le_top.trans_eq htop.symm
  · obtain ⟨R, hR⟩ := ENNReal.exists_nat_gt hlt.ne
    have hRle : rootedTailSup G (H, q, 0) ≤ (R : ℝ≥0∞) :=
      (show rootedTailSup G (H, q, 0) = truncCondExpSup μ G (H, q) from hqJ).trans_le hR.le
    refine le_of_eq ?_
    calc limsup (fun x : ℝ => cappedSquareAverage (ENNReal.ofReal x) G H q) atTop
        = limsup (fun x : ℝ => cappedSquareAverage (ENNReal.ofReal x)
            ((rootedTailSup G ⁻¹' Iic (R : ℝ≥0∞)).indicator G) H q) atTop := by
          refine limsup_congr ?_
          filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
          exact (hqloc R hRle x hx).symm
      _ = truncCondExpSup μ G (H, q) := (hqE R).limsup_eq.trans (hqEq R hRle)

/-- **Ergodic lemma for a nonnegative function along real masses** (arXiv 1807.07515, Lemma 2.7,
(2.3), for `G ≥ 0` without integrability): under the mass-transport principle, for a finite law `μ`
of the configuration and every measurable `G ≥ 0` invariant under the joint similarity, for
`μ`-almost every configuration `H` and almost every dyadic system `D`, the capped-square averages
`|S_x^0|⁻¹ ∫_{S_x^0} G(H, D, z) dz` converge in `[0, ∞]`, as the mass `x → ∞` through `ℝ`, to
`J(H, D) = sup_N E[G(H, D, 0) ∧ N | 𝓘](H, D)`. -/
theorem ae_ae_tendsto_cappedSquareAverage_ofReal_iSup_condExp [IsFiniteMeasure μ]
    (hMT : MassTransport μ) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w)) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      Tendsto (fun x : ℝ => cappedSquareAverage (ENNReal.ofReal x) G H q) atTop
        (𝓝 (⨆ N : ℕ, ENNReal.ofReal ((μ.prod dyadicLaw)[fun p =>
          (min (G (p.1, p.2, 0)) (N : ℝ≥0∞)).toReal | cappedSquareTailSigma] (H, q)))) :=
  ae_ae_tendsto_cappedSquareAverage_ofReal_truncCondExpSup hMT hG hinv

/-- **Ergodic lemma for a nonnegative function along the squares around the origin**
(arXiv 1807.07515, Lemma 2.7, (2.3), for `G ≥ 0` without integrability): under the mass-transport
principle, for a finite law `μ` of the configuration and every measurable `G ≥ 0` invariant under
the joint similarity, for `μ`-almost every configuration `H` and almost every dyadic system `D`, the
uniform averages `|S_k|⁻¹ ∫_{S_k} G(H, D, z) dz` over the squares `S_k` of generation `k` containing
the origin converge in `[0, ∞]`, as `k → ∞`, to `J(H, D) = sup_N E[G(H, D, 0) ∧ N | 𝓘](H, D)`. -/
theorem ae_ae_tendsto_squareAt_average_iSup_condExp [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w)) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      Tendsto (fun j : ℤ => ∫⁻ z, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
          (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z * G (H, q, z))
        atTop
        (𝓝 (⨆ N : ℕ, ENNReal.ofReal ((μ.prod dyadicLaw)[fun p =>
          (min (G (p.1, p.2, 0)) (N : ℝ≥0∞)).toReal | cappedSquareTailSigma] (H, q)))) := by
  filter_upwards [ae_ae_tendsto_cappedSquareAverage_ofReal_truncCondExpSup hMT hG hinv] with H hH
  filter_upwards [hH, ae_tendsto_cellMass_squareAt_origin_atTop H,
    ae_cappedSquareAverage_cellMass_squareAt_eq H G] with q hq htop havg
  have hreal := tendsto_toReal_atTop_of_tendsto_top htop fun j => cellMass_squareAt_ne_top H q j
  refine (hq.comp hreal).congr fun j => ?_
  simp only [Function.comp_apply, ENNReal.ofReal_toReal (cellMass_squareAt_ne_top H q j), havg j]

end TailSup

end LatticeProb.CellConfigCappedSquare
