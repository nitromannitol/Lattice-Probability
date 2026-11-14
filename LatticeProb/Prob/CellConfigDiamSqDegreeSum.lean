import LatticeProb.Prob.CellConfigOriginSquares
import LatticeProb.Prob.CellConfigCovariantDyadicRelatives
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds

/-!
# Diameter squared times degree of the cells meeting the dyadic squares around the origin

Gwynne, Miller and Sheffield (*An invariance principle for ergodic scale-free random
environments*, arXiv 1807.07515, Lemma 2.10) show that for the squares `S_k` of the uniform dyadic
system containing the origin there is a deterministic constant `C > 0` such that almost surely
`limsup_{k → ∞} |S_k|⁻² Σ_{H ∈ H(S_k)} diam(H)² (π(H) + π*(H)) ≤ C`.

The proof applies the ergodic lemma along the squares `S_k` to the function `F` of (2.4),
`F(H, D) = diam(H₀)² / Area(H₀) · (π(H₀) + π*(H₀))` with `H₀` the cell containing the origin. At a
point `z` we take, for each of the two summands, the infimum over the cells containing `z`. This
is exactly covariant under the similarities `H ↦ C(H - u)`, measurable (the cells of a configuration
are its label slots), equal at almost every point of a cell to its value at that cell (two cells
meet in a null set), and bounded at the origin by its value at any choice `H₀` of a cell containing
the origin, so that the finite expectation hypothesis (1.5) bounds its mean.

The ergodic lemma gives the limit `E[F | 𝓘]` with `𝓘 = ⋂_m 𝓕_m`. Since `F` is a function of the
configuration alone, `E[F | 𝓘] = E[F]`: every event of `𝓘` agrees almost surely with the event that
its rooted witness holds at almost every root, which is exactly invariant under the joint
similarity of the configuration and the dyadic system; the section measure of such an event is a
similarity invariant function of the configuration, hence almost surely constant by ergodicity
modulo scaling.

Splitting the integral of `F` over a square into the cells gives (2.10) for the cells contained in
the square. The cells meeting `S_k` without being contained in it are handled as in the printed
proof: by Lemma 2.9 they have diameter at most `|S_k| / 2`, hence lie in the dyadic ancestor of side
`4 |S_k|` centred on `S_k`, and Lemma 2.8, for the similarity covariant event "the cells inside `S`
have total weight at most `c |S|²`", transfers (2.10) to that ancestor. These two inputs are the
hypothesis `h29` of the final theorem and the measurable ancestor transfer.

## Main results
* `condExp_fst_cappedSquareTailSigma`: `E[G(H) | 𝓘] = E[G]` for integrable `G` of the configuration,
  under ergodicity modulo scaling.
* `measurable_rootedDiamSqDegree`, `rootedDiamSqDegree_similarity`,
  `lintegral_rootedDiamSqDegreeAt_zero_lt_top`: the function `F` of (2.4) is measurable, similarity
  invariant and has finite mean.
* `innerDiamSqDegreeSum_le_setLIntegral`: the cells contained in `S` carry at most `∫_S F`.
* `ae_ae_limsup_innerDiamSqDegreeSum_squareAt_le`: (2.10) with `C₀ = E[F]`.
* `exists_limsup_inv_volume_mul_diamSqDegreeSum_le_of_boundary`: the bound
  conditional on the boundary estimate.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-! ### Invariant observables are almost surely constant -/

/-- A real observable all of whose sublevel sets have probability `0` or `1` is almost surely
constant. -/
theorem exists_ae_eq_const_of_measure_le_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (h01 : ∀ r : ℝ, μ {x | f x ≤ r} = 0 ∨ μ {x | f x ≤ r} = 1) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  have hmeas : ∀ r : ℝ, MeasurableSet {x | f x ≤ r} := fun r =>
    measurableSet_le hf measurable_const
  have hae1 : ∀ r : ℝ, μ {x | f x ≤ r} = 1 → ∀ᵐ x ∂μ, f x ≤ r := fun r hr =>
    ae_iff.2 ((prob_compl_eq_zero_iff (hmeas r)).2 hr)
  have hae0 : ∀ r : ℝ, μ {x | f x ≤ r} = 0 → ∀ᵐ x ∂μ, r < f x := fun r hr =>
    ae_iff.2 (by simpa only [not_lt] using hr)
  have hnull : ¬ ∀ᵐ _ ∂μ, False := fun h => by
    have h0 : μ Set.univ = 0 := measure_mono_null (fun _ _ => not_false) (ae_iff.1 h)
    exact one_ne_zero (measure_univ.symm.trans h0)
  have hne : ({r : ℝ | μ {x | f x ≤ r} = 1}).Nonempty := by
    by_contra hcon
    have h0 : ∀ n : ℕ, μ {x | f x ≤ (n : ℝ)} = 0 := fun n =>
      (h01 n).resolve_right fun h => hcon ⟨(n : ℝ), h⟩
    refine hnull ((ae_all_iff.2 fun n : ℕ => hae0 _ (h0 n)).mono fun x hx => ?_)
    obtain ⟨n, hn⟩ := exists_nat_ge (f x)
    exact absurd (hx n) (not_lt.2 hn)
  have hbdd : BddBelow {r : ℝ | μ {x | f x ≤ r} = 1} := by
    by_contra hcon
    have h1 : ∀ n : ℕ, μ {x | f x ≤ -(n : ℝ)} = 1 := fun n =>
      (h01 _).resolve_left fun h0 => hcon ⟨-(n : ℝ), fun r hr => by
        by_contra hlt
        have hle : μ {x | f x ≤ r} ≤ μ {x | f x ≤ -(n : ℝ)} :=
          measure_mono fun x hx => le_trans hx (le_of_lt (not_le.1 hlt))
        rw [show μ {x | f x ≤ r} = 1 from hr, h0] at hle
        exact absurd hle (not_le.2 zero_lt_one)⟩
    refine hnull ((ae_all_iff.2 fun n : ℕ => hae1 _ (h1 n)).mono fun x hx => ?_)
    obtain ⟨n, hn⟩ := exists_nat_gt (-f x)
    linarith [hx n]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = sInf {r : ℝ | μ {x | f x ≤ r} = 1} := ⟨_, rfl⟩
  refine ⟨c, ?_⟩
  have hle : ∀ᵐ x ∂μ, f x ≤ c := by
    have h : ∀ n : ℕ, ∀ᵐ x ∂μ, f x ≤ c + 1 / ((n : ℝ) + 1) := fun n => by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨r, hr, hrlt⟩ := exists_lt_of_csInf_lt hne
        (show sInf {r : ℝ | μ {x | f x ≤ r} = 1} < c + 1 / ((n : ℝ) + 1) by rw [← hc]; linarith)
      exact (hae1 r hr).mono fun x hx => hx.trans hrlt.le
    filter_upwards [ae_all_iff.2 h] with x hx
    by_contra hcon
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (not_le.1 hcon))
    linarith [hx n]
  have hge : ∀ᵐ x ∂μ, c ≤ f x := by
    have h : ∀ n : ℕ, ∀ᵐ x ∂μ, c - 1 / ((n : ℝ) + 1) < f x := fun n => by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      refine hae0 _ ((h01 _).resolve_right fun hmem => ?_)
      have h' := csInf_le hbdd
        (show c - 1 / ((n : ℝ) + 1) ∈ {r : ℝ | μ {x | f x ≤ r} = 1} from hmem)
      rw [← hc] at h'
      linarith
    filter_upwards [ae_all_iff.2 h] with x hx
    by_contra hcon
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (not_le.1 hcon))
    linarith [hx n]
  filter_upwards [hle, hge] with x h1 h2
  exact le_antisymm h1 h2

/-- **Ergodicity modulo scaling for observables**: a measurable real function of the configuration
invariant under every similarity `H ↦ C(H - u)` is almost surely constant. -/
theorem exists_ae_eq_const_of_ergodicModuloScaling {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (herg : ErgodicModuloScaling μ) {f : GMSSpace → ℝ} (hf : Measurable f)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      f H' = f H) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c :=
  exists_ae_eq_const_of_measure_le_zero_or_one hf fun r =>
    herg _ (measurableSet_le hf measurable_const) fun s u hs H H' h => by
      show f H ≤ r ↔ f H' ≤ r
      rw [hinv s u hs H H' h]

/-! ### Exactly invariant representatives of the tail events -/

/-- The affine maps `z ↦ s • z + b` of `ℂ` with `s > 0` preserve Lebesgue null sets. -/
theorem volume_preimage_smul_add_eq_zero_iff {s : ℝ} (hs : 0 < s) {u : Plane} {E : Set ℂ} :
    volume ((fun z : ℂ => s • z + similarityOffset s u) ⁻¹' E) = 0 ↔ volume E = 0 := by
  have hsurj : Function.Surjective fun z : ℂ => s • z + similarityOffset s u := fun w =>
    ⟨s⁻¹ • (w - similarityOffset s u), by
      simp only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, sub_add_cancel]⟩
  have h := volume_image_smul_add_similarityOffset s u
    ((fun z : ℂ => s • z + similarityOffset s u) ⁻¹' E)
  rw [Set.image_preimage_eq E hsurj] at h
  rw [h, mul_eq_zero, or_iff_right (ENNReal.ofReal_pos.2 (pow_pos hs 2)).ne']

/-- **Invariant representatives of the events of `𝓘`**: every event of the tail σ-algebra
`𝓘 = ⋂_m 𝓕_m` (arXiv 1807.07515, Definition 2.5) agrees almost surely with a measurable event
exactly invariant under the joint similarity of the configuration and the dyadic system, namely
the event that the rooted witness of mass `1` holds at almost every root. -/
theorem exists_jointInvariant_ae_eq_of_measurableSet_cappedSquareTailSigma
    {μ : Measure GMSSpace} {A : Set (GMSSpace × DyadicCoord)}
    (hA : MeasurableSet[cappedSquareTailSigma] A) :
    ∃ T : Set (GMSSpace × DyadicCoord), MeasurableSet T ∧
      (∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
        ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 →
          ((H', similarityCoord s u q) ∈ T ↔ (H, q) ∈ T)) ∧
      A =ᵐ[μ.prod dyadicLaw] T := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hA' : MeasurableSet[⨅ k : ℕ, cappedSquareSigma ((k : ℝ≥0∞) + 1)] A := hA
  have hk : ∀ k : ℕ, ∃ B, IsCappedSquareWitness ((k : ℝ≥0∞) + 1) B ∧
      A = {p | (p.1, p.2, (0 : ℂ)) ∈ B} := MeasurableSpace.measurableSet_iInf.1 hA'
  choose B hB hAB using hk
  obtain ⟨T, hT⟩ : ∃ T : Set (GMSSpace × DyadicCoord),
      T = {p | ∀ᵐ z ∂(volume : Measure ℂ), (p.1, p.2, z) ∈ B 0} := ⟨_, rfl⟩
  have hmemT : ∀ p : GMSSpace × DyadicCoord,
      p ∈ T ↔ ∀ᵐ z ∂(volume : Measure ℂ), (p.1, p.2, z) ∈ B 0 := by
    subst hT
    exact fun p => Iff.rfl
  have hφ : Measurable fun x : (GMSSpace × DyadicCoord) × ℂ => (x.1.1, x.1.2, x.2) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  have ht : MeasurableSet T := by
    have hm := measurable_measure_prodMk_left (ν := (volume : Measure ℂ))
      ((hB 0).1.compl.preimage hφ)
    have heq : T = (fun p => (volume : Measure ℂ) (Prod.mk p ⁻¹'
        ((fun x : (GMSSpace × DyadicCoord) × ℂ => (x.1.1, x.1.2, x.2)) ⁻¹' (B 0)ᶜ))) ⁻¹' {0} := by
      ext p
      exact (hmemT p).trans ae_iff
    rw [heq]
    exact hm (measurableSet_singleton 0)
  refine ⟨T, ht, ?_, ?_⟩
  · intro s u hs H H' hHH' q hq₁ hq₂
    have hTz : ∀ z : ℂ, ((H', similarityCoord s u q, s • z + similarityOffset s u) ∈ B 0 ↔
        (H, q, z) ∈ B 0) := (hB 0).2.1 s u hs H H' hHH' q hq₁ hq₂
    refine (hmemT _).trans (Iff.trans ?_ (hmemT _).symm)
    show (∀ᵐ w ∂(volume : Measure ℂ), (H', similarityCoord s u q, w) ∈ B 0) ↔
      ∀ᵐ z ∂(volume : Measure ℂ), (H, q, z) ∈ B 0
    have hpre : {z : ℂ | ¬ (H, q, z) ∈ B 0} = (fun z : ℂ => s • z + similarityOffset s u) ⁻¹'
        {w : ℂ | ¬ (H', similarityCoord s u q, w) ∈ B 0} := by
      ext z
      exact not_congr (hTz z).symm
    rw [ae_iff, ae_iff, hpre, volume_preimage_smul_add_eq_zero_iff hs]
  · have key : ∀ H : GMSSpace, ∀ᵐ q ∂dyadicLaw, ((H, q) ∈ A ↔ (H, q) ∈ T) := by
      intro H
      filter_upwards [ae_isCompatible_system, ae_iUnion_squareAt_eq_univ,
        ae_all_iff.2 fun k => (hB k).2.2 H] with q hq hexh hwit
      have htr : ∀ (k : ℕ) (z : ℂ), ((H, q, z) ∈ B k ↔ (H, q, z) ∈ B 0) := by
        intro k z
        obtain ⟨H', hsim⟩ : ∃ H' : GMSSpace, IsSimilar 1 (planeCoord z) one_pos H H' :=
          ⟨⟨_, CellConfig.isCellConfiguration_similarity 1 (planeCoord z) one_pos H.2⟩, rfl⟩
        have h0 : (1 : ℝ) • z + similarityOffset 1 (planeCoord z) = 0 := by
          rw [similarityOffset, one_smul, one_smul, LinearIsometryEquiv.symm_apply_apply,
            add_neg_cancel]
        have e1 := (hB k).2.1 1 (planeCoord z) one_pos H H' hsim q hq.1 hq.2 z
        have e0 := (hB 0).2.1 1 (planeCoord z) one_pos H H' hsim q hq.1 hq.2 z
        rw [h0] at e1 e0
        have hk' : (H', similarityCoord 1 (planeCoord z) q) ∈ A ↔
            (H', similarityCoord 1 (planeCoord z) q, (0 : ℂ)) ∈ B k :=
          Iff.of_eq (congrArg (fun S => (H', similarityCoord 1 (planeCoord z) q) ∈ S) (hAB k))
        have h0' : (H', similarityCoord 1 (planeCoord z) q) ∈ A ↔
            (H', similarityCoord 1 (planeCoord z) q, (0 : ℂ)) ∈ B 0 :=
          Iff.of_eq (congrArg (fun S => (H', similarityCoord 1 (planeCoord z) q) ∈ S) (hAB 0))
        exact e1.symm.trans (hk'.symm.trans (h0'.trans e0))
      have hz : ∀ᵐ z ∂(volume : Measure ℂ), ((H, q, z) ∈ B 0 ↔ (H, q) ∈ A) := by
        filter_upwards [ae_all_iff.2 hwit] with z hz
        have hzU : z ∈ ⋃ j : ℤ, squareAt q.1 q.2.1 q.2.2 j 0 := by
          rw [hexh 0]
          exact Set.mem_univ z
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hzU
        obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (cellMass_squareAt_ne_top H q j)
        have hsub : squareAt q.1 q.2.1 q.2.2 j 0 ⊆ originCappedSquare ((k : ℝ≥0∞) + 1) H q :=
          Set.subset_sUnion_of_mem (CappedSquare.mem_candidates.2
            ⟨squareAt_mem_dyadicSquares j 0, mem_squareAt j 0, hk.le.trans le_self_add⟩)
        have h1 := hz k (hsub hj)
        rw [← htr k z]
        exact h1.trans (Iff.of_eq (congrArg (fun S => (H, q) ∈ S) (hAB k))).symm
      refine Iff.trans ?_ (hmemT (H, q)).symm
      constructor
      · intro hmem
        exact hz.mono fun z hz' => hz'.2 hmem
      · intro hB0
        by_contra hnA
        have hfalse : ∀ᵐ _ ∂(volume : Measure ℂ), False :=
          (hz.and hB0).mono fun z h => hnA (h.1.1 h.2)
        have hvol : (volume : Measure ℂ) Set.univ = 0 :=
          measure_mono_null (fun _ _ => not_false) (ae_iff.1 hfalse)
        exact (isOpen_univ.measure_pos (volume : Measure ℂ) Set.univ_nonempty).ne' hvol
    have hmeasA : MeasurableSet A := cappedSquareTailSigma_le A hA
    have hset : MeasurableSet {p : GMSSpace × DyadicCoord | p ∈ A ↔ p ∈ T} := by
      have heq : {p : GMSSpace × DyadicCoord | p ∈ A ↔ p ∈ T} = (A ∩ T) ∪ (Aᶜ ∩ Tᶜ) := by
        ext p
        show (p ∈ A ↔ p ∈ T) ↔ p ∈ (A ∩ T) ∪ (Aᶜ ∩ Tᶜ)
        rw [Set.mem_union, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_compl_iff,
          Set.mem_compl_iff]
        tauto
      rw [heq]
      exact (hmeasA.inter ht).union (hmeasA.compl.inter ht.compl)
    exact ((Measure.ae_prod_iff_ae_ae hset).2 (Filter.Eventually.of_forall key)).mono
      fun p hp => propext hp

/-- Fubini for an observable of the configuration on a measurable set of pairs: the integral over
`t` is the integral of `G` weighted by the section measure. -/
theorem setIntegral_fst_eq_integral_dyadicLaw_mul {μ : Measure GMSSpace} [IsFiniteMeasure μ]
    {t : Set (GMSSpace × DyadicCoord)} (ht : MeasurableSet t) {G : GMSSpace → ℝ}
    (hG : Integrable G μ) :
    ∫ p in t, G p.1 ∂(μ.prod dyadicLaw) = ∫ x, dyadicLaw.real (Prod.mk x ⁻¹' t) * G x ∂μ := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hGf : Integrable (fun p : GMSSpace × DyadicCoord => G p.1) (μ.prod dyadicLaw) :=
    hG.comp_fst dyadicLaw
  rw [← integral_indicator ht, integral_prod _ (hGf.indicator ht)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hsec : (fun y => t.indicator (fun p : GMSSpace × DyadicCoord => G p.1) (x, y)) =
      (Prod.mk x ⁻¹' t).indicator (fun _ => G x) := by
    ext y
    by_cases hy : (x, y) ∈ t
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ Prod.mk x ⁻¹' t from hy)]
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (show y ∉ Prod.mk x ⁻¹' t from hy)]
  simp only [hsec, integral_indicator (measurable_prodMk_left ht), setIntegral_const, smul_eq_mul]

/-- **Observables of the configuration are deterministic given `𝓘`** (arXiv 1807.07515, Lemma 2.7,
in the conditional form for functions of `H` alone): under ergodicity modulo scaling, for every
integrable `G`, `E[G(H) | 𝓘] = E[G]` almost surely, where `𝓘 = ⋂_m 𝓕_m`. -/
theorem condExp_fst_cappedSquareTailSigma {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (herg : ErgodicModuloScaling μ) {g : GMSSpace → ℝ} (hg : Integrable g μ) :
    (μ.prod dyadicLaw)[fun p => g p.1 | cappedSquareTailSigma] =ᵐ[μ.prod dyadicLaw]
      fun _ => ∫ H, g H ∂μ := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hGf : Integrable (fun p : GMSSpace × DyadicCoord => g p.1) (μ.prod dyadicLaw) :=
    hg.comp_fst dyadicLaw
  refine (ae_eq_condExp_of_forall_setIntegral_eq cappedSquareTailSigma_le hGf
    (fun A _ _ => (integrable_const _).integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_const.aestronglyMeasurable).symm
  obtain ⟨t, ht, htinv, hst⟩ :=
    exists_jointInvariant_ae_eq_of_measurableSet_cappedSquareTailSigma (μ := μ) hA
  have hfm : Measurable fun H : GMSSpace => dyadicLaw.real (Prod.mk H ⁻¹' t) :=
    (measurable_measure_prodMk_left ht).ennreal_toReal
  have hfinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      dyadicLaw.real (Prod.mk H' ⁻¹' t) = dyadicLaw.real (Prod.mk H ⁻¹' t) := by
    intro s u hs H H' h
    have h1 : dyadicLaw (similarityCoord s u ⁻¹' (Prod.mk H' ⁻¹' t)) =
        dyadicLaw (Prod.mk H' ⁻¹' t) :=
      (measurePreserving_similarityCoord s u).measure_preimage
        (measurable_prodMk_left ht).nullMeasurableSet
    have h2 : similarityCoord s u ⁻¹' (Prod.mk H' ⁻¹' t) =ᵐ[dyadicLaw] Prod.mk H ⁻¹' t := by
      filter_upwards [ae_isCompatible_system] with q hq
      exact propext (htinv s u hs H H' h q hq.1 hq.2)
    show (dyadicLaw (Prod.mk H' ⁻¹' t)).toReal = (dyadicLaw (Prod.mk H ⁻¹' t)).toReal
    rw [← h1, measure_congr h2]
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_ergodicModuloScaling herg hfm hfinv
  have key : ∀ G : GMSSpace → ℝ, Integrable G μ →
      ∫ p in t, G p.1 ∂(μ.prod dyadicLaw) = c * ∫ H, G H ∂μ := by
    intro G hG
    rw [setIntegral_fst_eq_integral_dyadicLaw_mul ht hG, ← integral_const_mul]
    exact integral_congr_ae (hc.mono fun x (hx : dyadicLaw.real (Prod.mk x ⁻¹' t) = c) => by
      simp only [hx])
  have hct : (μ.prod dyadicLaw).real t = c := by
    have h1 := key (fun _ => 1) (integrable_const 1)
    simpa only [setIntegral_const, smul_eq_mul, mul_one, integral_const, probReal_univ,
      measureReal_restrict_apply_univ] using h1
  show ∫ _ in A, (∫ x, g x ∂μ) ∂(μ.prod dyadicLaw) = ∫ p in A, g p.1 ∂(μ.prod dyadicLaw)
  rw [setIntegral_congr_set hst, setIntegral_congr_set hst, setIntegral_const, key g hg, hct,
    smul_eq_mul]

/-! ### The function `F` of (2.4) -/

/-- `diam(H)² π(H) / Area(H)` for a cell `H` of a configuration. -/
noncomputable def cellPiDensity (H : CellConfig) (K : Cell) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K * H.pi K)

/-- `diam(H)² π*(H) / Area(H)` for a cell `H` of a configuration. -/
noncomputable def cellPiStarDensity (H : CellConfig) (K : Cell) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K * H.piStar K)

/-- A cell functional evaluated at a point: the infimum over the cells containing the point. -/
noncomputable def rootedCellInf (φ : CellConfig → Cell → ℝ≥0∞) (H : GMSSpace) (z : ℂ) : ℝ≥0∞ :=
  ⨅ (K : H.1.cells) (_ : z ∈ complexCells H.1 K), φ H.1 K

/-- The function `F` of (2.4) of arXiv 1807.07515 for the configuration rooted at `z`:
`diam(H_z)² (π(H_z) + π*(H_z)) / Area(H_z)` for the cell `H_z` containing `z`. -/
noncomputable def rootedDiamSqDegreeAt (H : GMSSpace) (z : ℂ) : ℝ≥0∞ :=
  rootedCellInf cellPiDensity H z + rootedCellInf cellPiStarDensity H z

/-- The function `F` of (2.4) as a function of the rooted configuration and dyadic system. -/
noncomputable def rootedDiamSqDegree (p : GMSSpace × DyadicCoord × ℂ) : ℝ≥0∞ :=
  rootedDiamSqDegreeAt p.1 p.2.2

/-- `diam(H)² (π(H) + π*(H))` for a cell `H` of a configuration. -/
noncomputable def diamSqDegree (H : CellConfig) (K : Cell) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 * (H.pi K + H.piStar K))

/-- `Σ_{H ∈ H(S)} diam(H)² (π(H) + π*(H))`: the sum over the cells meeting `S`. -/
noncomputable def diamSqDegreeSum (H : CellConfig) (S : Set ℂ) : ℝ≥0∞ :=
  ∑' K : H.cells, {K : H.cells | (complexCells H K ∩ S).Nonempty}.indicator
    (fun K => diamSqDegree H K) K

/-- The sum of `diam(H)² (π(H) + π*(H))` over the cells contained in `S`. -/
noncomputable def innerDiamSqDegreeSum (H : CellConfig) (S : Set ℂ) : ℝ≥0∞ :=
  ∑' K : H.cells, {K : H.cells | complexCells H K ⊆ S}.indicator (fun K => diamSqDegree H K) K

/-- The dyadic ancestor of side `4 |S_j|` of the square `S_j` around the origin in which `S_j`
occupies the second row and column. -/
noncomputable def originAncestorSquare (q : DyadicCoord) (j : ℤ) : Set ℂ :=
  cornerSquare (gridFloor q.1 q.2.1 j (0 : ℂ).re - (2 : ℝ) ^ (q.1 + (j : ℝ)))
    (gridFloor q.1 q.2.2 j (0 : ℂ).im - (2 : ℝ) ^ (q.1 + (j : ℝ))) (4 * (2 : ℝ) ^ (q.1 + (j : ℝ)))

theorem area_nonneg (K : Cell) : 0 ≤ CellConfig.area K := ENNReal.toReal_nonneg

theorem pi_nonneg {H : CellConfig} (hH : H.IsCellConfiguration) (K : Cell) : 0 ≤ H.pi K :=
  tsum_nonneg fun K' => hH.c_nonneg K K'

theorem piStar_nonneg {H : CellConfig} (hH : H.IsCellConfiguration) (K : Cell) :
    0 ≤ H.piStar K :=
  tsum_nonneg fun K' => inv_nonneg.2 (hH.c_nonneg K K')

/-! #### Measurability through the label slots -/

/-- A sum over the cells is the sum over the label slots. -/
theorem tsum_cells_eq_tsum_slot {H : CellConfig} (hH : H.IsCellConfiguration)
    (F : Cell → ℝ≥0∞) : ∑' K : H.cells, F K = ∑' n, (H.slot n).elim 0 F := by
  have hinj : Function.Injective (CellConfig.label hH) := by
    intro K K' h
    have h1 := CellConfig.slot_label hH K
    have h2 := CellConfig.slot_label hH K'
    rw [h] at h1
    exact Subtype.ext (Option.some_inj.mp (h1.symm.trans h2))
  have hsupp : Function.support (fun n => (H.slot n).elim 0 F) ⊆
      Set.range (CellConfig.label hH) := by
    intro n hn
    cases hs : H.slot n with
    | none => exact absurd (by simp only [hs, Option.elim]) hn
    | some K =>
      obtain ⟨hK, hl⟩ := (CellConfig.slot_eq_some_iff hH).1 hs
      exact ⟨⟨K, hK⟩, leastInteriorLabel_unique
        (CellConfig.leastInteriorLabel_label hH ⟨K, hK⟩) hl⟩
  rw [← hinj.tsum_eq hsupp]
  exact tsum_congr fun K => by simp only [CellConfig.slot_label hH K, Option.elim]

theorem slot_elim_ofReal_c {H : CellConfig} {n : ℕ} {K : Cell} (hn : H.slot n = some K)
    (m : ℕ) :
    (H.slot m).elim 0 (fun K' => ENNReal.ofReal (H.c K K')) = ENNReal.ofReal (H.codeCond n m) := by
  cases hm : H.slot m with
  | none => simp only [Option.elim, CellConfig.codeCond_of_none_right hm, ENNReal.ofReal_zero]
  | some K' => simp only [Option.elim, CellConfig.codeCond_of_some hn hm]

theorem slot_elim_ofReal_inv_c {H : CellConfig} {n : ℕ} {K : Cell} (hn : H.slot n = some K)
    (m : ℕ) :
    (H.slot m).elim 0 (fun K' => ENNReal.ofReal (H.c K K')⁻¹) =
      ENNReal.ofReal (H.codeCond n m)⁻¹ := by
  cases hm : H.slot m with
  | none =>
    simp only [Option.elim, CellConfig.codeCond_of_none_right hm, inv_zero, ENNReal.ofReal_zero]
  | some K' => simp only [Option.elim, CellConfig.codeCond_of_some hn hm]

/-- A function on the cells vanishing off the neighbours of a cell is summable: only finitely
many cells meet a compact set. -/
theorem summable_of_adj {H : CellConfig} (hH : H.IsCellConfiguration) (K : Cell)
    {f : H.cells → ℝ} (hf : ∀ K' : H.cells, f K' ≠ 0 → H.Adj K K') : Summable f := by
  have hfin : (Subtype.val ⁻¹' H.restrict (K : Set Plane) : Set H.cells).Finite :=
    (CellConfig.finite_restrict_of_isCompact hH K.isCompact).preimage
      Subtype.val_injective.injOn
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun K' hK' => ?_
  by_contra hne
  apply hK'
  rw [Set.Finite.mem_toFinset]
  obtain ⟨x, hx⟩ := hH.adj_inter K K' (hf K' hne)
  exact ⟨K'.2, x, hx.2, hx.1⟩

theorem ofReal_pi_eq_tsum {H : CellConfig} (hH : H.IsCellConfiguration) (K : Cell) :
    ENNReal.ofReal (H.pi K) = ∑' K' : H.cells, ENNReal.ofReal (H.c K K') :=
  ENNReal.ofReal_tsum_of_nonneg (fun K' => hH.c_nonneg K K')
    (summable_of_adj hH K fun K' hne => lt_of_le_of_ne (hH.c_nonneg K K') (Ne.symm hne))

theorem ofReal_piStar_eq_tsum {H : CellConfig} (hH : H.IsCellConfiguration) (K : Cell) :
    ENNReal.ofReal (H.piStar K) = ∑' K' : H.cells, ENNReal.ofReal (H.c K K')⁻¹ :=
  ENNReal.ofReal_tsum_of_nonneg (fun K' => inv_nonneg.2 (hH.c_nonneg K K'))
    (summable_of_adj hH K fun K' hne => lt_of_le_of_ne (hH.c_nonneg K K') fun h =>
      hne (by simp only [← h, inv_zero]))

/-- The density `diam(H)² π(H) / Area(H)` at the cell of label slot `n`. -/
noncomputable def slotPiDensity (n : ℕ) (H : GMSSpace) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (interiorCell (Code.rationalPoint n) H : Set Plane) ^ 2 /
      CellConfig.area (interiorCell (Code.rationalPoint n) H)) *
    ∑' m, ENNReal.ofReal (H.1.codeCond n m)

/-- The density `diam(H)² π*(H) / Area(H)` at the cell of label slot `n`. -/
noncomputable def slotPiStarDensity (n : ℕ) (H : GMSSpace) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (interiorCell (Code.rationalPoint n) H : Set Plane) ^ 2 /
      CellConfig.area (interiorCell (Code.rationalPoint n) H)) *
    ∑' m, ENNReal.ofReal (H.1.codeCond n m)⁻¹

theorem measurable_slotPiDensity (n : ℕ) : Measurable (slotPiDensity n) := by
  have hd : Measurable fun H : GMSSpace =>
      Metric.diam (interiorCell (Code.rationalPoint n) H : Set Plane) :=
    Spatial.measurable_cellDiam.comp (measurable_interiorCell (Code.rationalPoint n))
  have ha : Measurable fun H : GMSSpace => CellConfig.area (interiorCell (Code.rationalPoint n) H) :=
    (Spatial.measurable_cellVolume.comp (measurable_interiorCell (Code.rationalPoint n))).ennreal_toReal
  exact (ENNReal.measurable_ofReal.comp ((hd.pow_const 2).div ha)).mul
    (Measurable.tsum fun m => ENNReal.measurable_ofReal.comp (measurable_codeCond n m))

theorem measurable_slotPiStarDensity (n : ℕ) : Measurable (slotPiStarDensity n) := by
  have hd : Measurable fun H : GMSSpace =>
      Metric.diam (interiorCell (Code.rationalPoint n) H : Set Plane) :=
    Spatial.measurable_cellDiam.comp (measurable_interiorCell (Code.rationalPoint n))
  have ha : Measurable fun H : GMSSpace => CellConfig.area (interiorCell (Code.rationalPoint n) H) :=
    (Spatial.measurable_cellVolume.comp (measurable_interiorCell (Code.rationalPoint n))).ennreal_toReal
  exact (ENNReal.measurable_ofReal.comp ((hd.pow_const 2).div ha)).mul
    (Measurable.tsum fun m => ENNReal.measurable_ofReal.comp (measurable_codeCond n m).inv)

theorem slotPiDensity_eq {n : ℕ} {H : GMSSpace} (h : H ∈ labelSet n) :
    slotPiDensity n H = cellPiDensity H.1 (interiorCell (Code.rationalPoint n) H) := by
  have hslot : H.1.slot n = some (interiorCell (Code.rationalPoint n) H) := by
    simp only [slot_eq, h, ↓reduceIte]
  rw [slotPiDensity, cellPiDensity, ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (area_nonneg _)),
    ofReal_pi_eq_tsum H.2, tsum_cells_eq_tsum_slot H.2
      (fun K' => ENNReal.ofReal (H.1.c (interiorCell (Code.rationalPoint n) H) K'))]
  congr 1
  exact tsum_congr fun m => (slot_elim_ofReal_c hslot m).symm

theorem slotPiStarDensity_eq {n : ℕ} {H : GMSSpace} (h : H ∈ labelSet n) :
    slotPiStarDensity n H = cellPiStarDensity H.1 (interiorCell (Code.rationalPoint n) H) := by
  have hslot : H.1.slot n = some (interiorCell (Code.rationalPoint n) H) := by
    simp only [slot_eq, h, ↓reduceIte]
  rw [slotPiStarDensity, cellPiStarDensity,
    ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (area_nonneg _)),
    ofReal_piStar_eq_tsum H.2, tsum_cells_eq_tsum_slot H.2
      (fun K' => ENNReal.ofReal (H.1.c (interiorCell (Code.rationalPoint n) H) K')⁻¹)]
  congr 1
  exact tsum_congr fun m => (slot_elim_ofReal_inv_c hslot m).symm

/-- The configurations and points for which the point lies in the cell of label slot `n`. -/
def rootedCellSet (n : ℕ) : Set (GMSSpace × ℂ) :=
  {p | p.1 ∈ labelSet n ∧ planeCoord p.2 ∈ (interiorCell (Code.rationalPoint n) p.1 : Set Plane)}

theorem mem_rootedCellSet {n : ℕ} {p : GMSSpace × ℂ} :
    p ∈ rootedCellSet n ↔
      p.1 ∈ labelSet n ∧ planeCoord p.2 ∈ (interiorCell (Code.rationalPoint n) p.1 : Set Plane) :=
  Iff.rfl

theorem measurableSet_rootedCellSet (n : ℕ) : MeasurableSet (rootedCellSet n) :=
  (measurable_fst (measurableSet_labelSet n)).inter
    ((((measurable_interiorCell (Code.rationalPoint n)).comp measurable_fst).prodMk
      (planeCoord.continuous.measurable.comp measurable_snd)) Spatial.measurableSet_cellMem)

/-- **Measurability of a cell functional evaluated at a point**, given its measurability at the
cells of the label slots. -/
theorem measurable_rootedCellInf {φ : CellConfig → Cell → ℝ≥0∞} {ψ : ℕ → GMSSpace → ℝ≥0∞}
    (hψ : ∀ n, Measurable (ψ n))
    (hψφ : ∀ n H, H ∈ labelSet n → ψ n H = φ H.1 (interiorCell (Code.rationalPoint n) H)) :
    Measurable fun p : GMSSpace × ℂ => rootedCellInf φ p.1 p.2 := by
  classical
  have heq : (fun p : GMSSpace × ℂ => rootedCellInf φ p.1 p.2) =
      fun p => ⨅ n, (rootedCellSet n).piecewise (fun p => ψ n p.1) (fun _ => ⊤) p := by
    funext p
    obtain ⟨H, z⟩ := p
    show rootedCellInf φ H z =
      ⨅ n, (rootedCellSet n).piecewise (fun p => ψ n p.1) (fun _ => ⊤) (H, z)
    refine le_antisymm (le_iInf fun n => ?_) (le_iInf₂ fun K hK => ?_)
    · by_cases hn : (H, z) ∈ rootedCellSet n
      · have hmem := (interiorCell_spec (labelSet_subset n (mem_rootedCellSet.1 hn).1)).1
        have hle1 : rootedCellInf φ H z ≤ φ H.1 (interiorCell (Code.rationalPoint n) H) :=
          iInf₂_le (⟨interiorCell (Code.rationalPoint n) H, hmem⟩ : H.1.cells)
            (mem_rootedCellSet.1 hn).2
        rw [Set.piecewise_eq_of_mem _ _ _ hn]
        exact hle1.trans_eq (hψφ n H (mem_rootedCellSet.1 hn).1).symm
      · rw [Set.piecewise_eq_of_notMem _ _ _ hn]
        exact le_top
    · have hlab : H ∈ labelSet (CellConfig.label H.2 K) :=
        (⟨K.1, K.2, CellConfig.leastInteriorLabel_label H.2 K⟩ :
          ∃ K' ∈ H.1.cells, Code.LeastInteriorLabel K' (CellConfig.label H.2 K))
      have hK' : interiorCell (Code.rationalPoint (CellConfig.label H.2 K)) H = K := by
        have h1 := slot_eq H (CellConfig.label H.2 K)
        rw [CellConfig.slot_label H.2 K] at h1
        simp only [hlab, ↓reduceIte, Option.some_inj] at h1
        exact h1.symm
      have hn : (H, z) ∈ rootedCellSet (CellConfig.label H.2 K) :=
        mem_rootedCellSet.2 ⟨hlab, (show planeCoord z ∈
          (interiorCell (Code.rationalPoint (CellConfig.label H.2 K)) H : Set Plane) by
            rw [hK']; exact hK)⟩
      exact (iInf_le _ (CellConfig.label H.2 K)).trans (le_of_eq
        ((Set.piecewise_eq_of_mem _ _ _ hn).trans
          ((hψφ _ H hlab).trans (congrArg (φ H.1) hK'))))
  rw [heq]
  exact Measurable.iInf fun n => Measurable.piecewise (measurableSet_rootedCellSet n)
    ((hψ n).comp measurable_fst) measurable_const

theorem measurable_rootedCellInf_cellPiDensity :
    Measurable fun p : GMSSpace × ℂ => rootedCellInf cellPiDensity p.1 p.2 :=
  measurable_rootedCellInf (φ := cellPiDensity) measurable_slotPiDensity
    fun _ _ h => slotPiDensity_eq h

theorem measurable_rootedCellInf_cellPiStarDensity :
    Measurable fun p : GMSSpace × ℂ => rootedCellInf cellPiStarDensity p.1 p.2 :=
  measurable_rootedCellInf (φ := cellPiStarDensity) measurable_slotPiStarDensity
    fun _ _ h => slotPiStarDensity_eq h

theorem measurable_rootedDiamSqDegreeAt :
    Measurable fun p : GMSSpace × ℂ => rootedDiamSqDegreeAt p.1 p.2 :=
  measurable_rootedCellInf_cellPiDensity.add measurable_rootedCellInf_cellPiStarDensity

/-- **The function `F` of (2.4) is measurable.** -/
theorem measurable_rootedDiamSqDegree : Measurable rootedDiamSqDegree :=
  measurable_rootedDiamSqDegreeAt.comp (measurable_fst.prodMk measurable_snd.snd)

/-! #### Invariance under the similarities -/

theorem pi_similarity_transformCell (H : CellConfig) (s : ℝ) (u : Plane) (hs : 0 < s)
    (K : Cell) : (H.similarity s u hs).pi (transformCell s u hs K) = H.pi K := by
  unfold CellConfig.pi
  rw [← (CellConfig.similarityCellEquiv s u hs).tsum_eq]
  exact tsum_congr fun K' => CellConfig.similarity_c_transformCell s u hs K K'

theorem piStar_similarity_transformCell (H : CellConfig) (s : ℝ) (u : Plane) (hs : 0 < s)
    (K : Cell) : (H.similarity s u hs).piStar (transformCell s u hs K) = H.piStar K := by
  unfold CellConfig.piStar
  rw [← (CellConfig.similarityCellEquiv s u hs).tsum_eq]
  exact tsum_congr fun K' => congrArg Inv.inv (CellConfig.similarity_c_transformCell s u hs K K')

theorem area_transformCell (s : ℝ) (u : Plane) (hs : 0 < s) (K : Cell) :
    CellConfig.area (transformCell s u hs K) = s ^ 2 * CellConfig.area K := by
  unfold CellConfig.area
  rw [coe_transformCell, Spatial.volume_image_positiveSimilarity, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg s)]

theorem cellPiDensity_similarity (H : CellConfig) (s : ℝ) (u : Plane) (hs : 0 < s) (K : Cell) :
    cellPiDensity (H.similarity s u hs) (transformCell s u hs K) = cellPiDensity H K := by
  unfold cellPiDensity
  rw [pi_similarity_transformCell, area_transformCell, coe_transformCell,
    Spatial.diam_image_positiveSimilarity s u hs, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero 2 hs.ne')]

theorem cellPiStarDensity_similarity (H : CellConfig) (s : ℝ) (u : Plane) (hs : 0 < s)
    (K : Cell) :
    cellPiStarDensity (H.similarity s u hs) (transformCell s u hs K) = cellPiStarDensity H K := by
  unfold cellPiStarDensity
  rw [piStar_similarity_transformCell, area_transformCell, coe_transformCell,
    Spatial.diam_image_positiveSimilarity s u hs, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero 2 hs.ne')]

/-- A covariant cell functional evaluated at a point is invariant under the similarities. -/
theorem rootedCellInf_similarity {φ : CellConfig → Cell → ℝ≥0∞}
    (hφ : ∀ (H : CellConfig) (s : ℝ) (u : Plane) (hs : 0 < s) (K : Cell),
      φ (H.similarity s u hs) (transformCell s u hs K) = φ H K)
    {s : ℝ} {u : Plane} {hs : 0 < s} {H H' : GMSSpace} (h : IsSimilar s u hs H H') {z : ℂ} :
    rootedCellInf φ H' (s • z + similarityOffset s u) = rootedCellInf φ H z := by
  obtain ⟨H'c, hH'c⟩ := H'
  have h' : H'c = H.1.similarity s u hs := h
  subst h'
  have hinj : Function.Injective fun z : ℂ => s • z + similarityOffset s u := fun a b hab =>
    smul_right_injective ℂ hs.ne' (add_right_cancel hab)
  show ⨅ (K : (H.1.similarity s u hs).cells)
      (_ : s • z + similarityOffset s u ∈ complexCells (H.1.similarity s u hs) K),
      φ (H.1.similarity s u hs) K = ⨅ (K : H.1.cells) (_ : z ∈ complexCells H.1 K), φ H.1 K
  rw [← (CellConfig.similarityCellEquiv s u hs).iInf_comp]
  refine iInf_congr fun K => iInf_congr_Prop ?_ fun _ => hφ H.1 s u hs K.1
  rw [complexCells_similarity s u hs K]
  exact hinj.mem_set_image

/-- **The function `F` of (2.4) is invariant under the joint similarities.** -/
theorem rootedDiamSqDegree_similarity (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace)
    (h : IsSimilar s u hs H H') (q : DyadicCoord) (_ : IsCompatible q.2.1)
    (_ : IsCompatible q.2.2) (w : ℂ) :
    rootedDiamSqDegree (H', similarityCoord s u q, s • w + similarityOffset s u) =
      rootedDiamSqDegree (H, q, w) := by
  show rootedCellInf cellPiDensity H' (s • w + similarityOffset s u) +
      rootedCellInf cellPiStarDensity H' (s • w + similarityOffset s u) =
    rootedCellInf cellPiDensity H w + rootedCellInf cellPiStarDensity H w
  rw [rootedCellInf_similarity cellPiDensity_similarity h,
    rootedCellInf_similarity cellPiStarDensity_similarity h]

/-! #### Finite mean -/

/-- **The function `F` of (2.4) has finite mean** under GMS's finite expectation hypothesis
(1.5), for any choice of the cell containing the origin. -/
theorem lintegral_rootedDiamSqDegreeAt_zero_lt_top {μ : Measure GMSSpace}
    (hFE : FiniteExpectation μ) : ∫⁻ H, rootedDiamSqDegreeAt H 0 ∂μ < ∞ := by
  obtain ⟨H₀, hH₀, hπ, hπs⟩ := hFE
  have hle : ∀ (φ : CellConfig → Cell → ℝ≥0∞) (H : GMSSpace),
      rootedCellInf φ H 0 ≤ φ H.1 (H₀ H) := fun φ H =>
    iInf₂_le (⟨H₀ H, (hH₀ H).1⟩ : H.1.cells)
      (show planeCoord (0 : ℂ) ∈ (H₀ H : Set Plane) by rw [map_zero]; exact (hH₀ H).2)
  have hm : Measurable fun H : GMSSpace => rootedCellInf cellPiDensity H 0 :=
    measurable_rootedCellInf_cellPiDensity.comp (measurable_id.prodMk measurable_const)
  calc ∫⁻ H, rootedDiamSqDegreeAt H 0 ∂μ
      = (∫⁻ H, rootedCellInf cellPiDensity H 0 ∂μ) +
          ∫⁻ H, rootedCellInf cellPiStarDensity H 0 ∂μ :=
        lintegral_add_left hm _
    _ ≤ (∫⁻ H, cellPiDensity H.1 (H₀ H) ∂μ) + ∫⁻ H, cellPiStarDensity H.1 (H₀ H) ∂μ :=
        add_le_add (lintegral_mono fun H => hle _ H) (lintegral_mono fun H => hle _ H)
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hπ, hπs⟩

/-! ### Splitting an integral of `F` into the cells -/

/-- Almost every point of the plane lies in at most one cell. -/
theorem ae_unique_cell (H : GMSSpace) : ∀ᵐ z ∂(volume : Measure ℂ), ∀ K K' : H.1.cells,
    z ∈ complexCells H.1 K → z ∈ complexCells H.1 K' → K = K' := by
  have := countable_cells H.2
  have hnull : volume (⋃ (K : H.1.cells) (K' : H.1.cells) (_ : K ≠ K'),
      complexCells H.1 K ∩ complexCells H.1 K') = 0 :=
    measure_iUnion_null fun K => measure_iUnion_null fun K' => measure_iUnion_null fun hne =>
      calc volume (complexCells H.1 K ∩ complexCells H.1 K')
          = volume (planeCoordMeas ⁻¹' ((K.1 : Set Plane) ∩ K'.1)) := rfl
        _ = volume ((K.1 : Set Plane) ∩ K'.1) :=
          measurePreserving_planeCoordMeas.measure_preimage_equiv _
        _ = 0 := H.2.volume_inter K.1 K.2 K'.1 K'.2 fun h => hne (Subtype.ext h)
  refine ae_iff.2 (measure_mono_null (fun z hz => ?_) hnull)
  have hz' : ¬ ∀ K K' : H.1.cells, z ∈ complexCells H.1 K → z ∈ complexCells H.1 K' → K = K' :=
    hz
  simp only [not_forall] at hz'
  obtain ⟨K, K', hK, hK', hne⟩ := hz'
  exact Set.mem_iUnion.2 ⟨K, Set.mem_iUnion.2 ⟨K', Set.mem_iUnion.2 ⟨hne, hK, hK'⟩⟩⟩

theorem rootedCellInf_eq_of_unique {φ : CellConfig → Cell → ℝ≥0∞} {H : GMSSpace} {z : ℂ}
    {K₀ : H.1.cells} (hz : z ∈ complexCells H.1 K₀)
    (hu : ∀ K K' : H.1.cells, z ∈ complexCells H.1 K → z ∈ complexCells H.1 K' → K = K') :
    rootedCellInf φ H z = φ H.1 K₀ :=
  le_antisymm (iInf₂_le K₀ hz) (le_iInf₂ fun K hK => by rw [hu K K₀ hK hz])

/-- **The integral of `F` over a cell** is `diam(H)² (π(H) + π*(H))`. -/
theorem setLIntegral_rootedDiamSqDegreeAt_cell (H : GMSSpace) (K : H.1.cells) :
    ∫⁻ z in complexCells H.1 K, rootedDiamSqDegreeAt H z = diamSqDegree H.1 K := by
  have hKm : MeasurableSet (complexCells H.1 K) :=
    (isCompact_complexCells K).isClosed.measurableSet
  have hvoltop : volume (K.1 : Set Plane) ≠ ∞ := K.1.isCompact.measure_lt_top.ne
  have hvol0 : volume (K.1 : Set Plane) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior _ (H.2.interior_nonempty K.1 K.2)).ne'
  have hA : 0 < CellConfig.area K.1 := ENNReal.toReal_pos hvol0 hvoltop
  have hvol : volume (complexCells H.1 K) = ENNReal.ofReal (CellConfig.area K.1) := by
    rw [volume_complexCells, CellConfig.area, ENNReal.ofReal_toReal hvoltop]
  have hconst : ∫⁻ z in complexCells H.1 K, rootedDiamSqDegreeAt H z =
      ∫⁻ _ in complexCells H.1 K, (cellPiDensity H.1 K + cellPiStarDensity H.1 K) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem hKm, ae_restrict_of_ae (ae_unique_cell H)] with z hz hu
    simp only [rootedDiamSqDegreeAt, rootedCellInf_eq_of_unique hz hu]
  have e : ∀ x : ℝ, Metric.diam (K.1 : Set Plane) ^ 2 / CellConfig.area K.1 * x *
      CellConfig.area K.1 = Metric.diam (K.1 : Set Plane) ^ 2 * x := fun x => by
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hA.ne']
  have h1 := mul_nonneg (div_nonneg (sq_nonneg (Metric.diam (K.1 : Set Plane)))
    (area_nonneg K.1)) (pi_nonneg H.2 K.1)
  have h2 := mul_nonneg (div_nonneg (sq_nonneg (Metric.diam (K.1 : Set Plane)))
    (area_nonneg K.1)) (piStar_nonneg H.2 K.1)
  rw [hconst, setLIntegral_const, hvol]
  unfold cellPiDensity cellPiStarDensity diamSqDegree
  rw [add_mul, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2,
    ← ENNReal.ofReal_add (mul_nonneg h1 (area_nonneg K.1)) (mul_nonneg h2 (area_nonneg K.1)),
    e, e, mul_add]

/-- **The cells contained in `S` carry at most `∫_S F`.** -/
theorem innerDiamSqDegreeSum_le_setLIntegral (H : GMSSpace) {S : Set ℂ} (hS : MeasurableSet S) :
    innerDiamSqDegreeSum H.1 S ≤ ∫⁻ z in S, rootedDiamSqDegreeAt H z := by
  have := countable_cells H.2
  have hGm : Measurable fun z => rootedDiamSqDegreeAt H z :=
    measurable_rootedDiamSqDegreeAt.comp measurable_prodMk_left
  have hpart : ∀ K : H.1.cells,
      {K' : H.1.cells | complexCells H.1 K' ⊆ S}.indicator (fun K' => diamSqDegree H.1 K') K =
        ∫⁻ z, {K' : H.1.cells | complexCells H.1 K' ⊆ S}.indicator
          (fun K' => (complexCells H.1 K').indicator (fun z => rootedDiamSqDegreeAt H z) z) K := by
    intro K
    by_cases hK : K ∈ {K' : H.1.cells | complexCells H.1 K' ⊆ S}
    · simp only [Set.indicator_of_mem hK]
      rw [lintegral_indicator (hs := (isCompact_complexCells K).isClosed.measurableSet),
        setLIntegral_rootedDiamSqDegreeAt_cell]
    · simp only [Set.indicator_of_notMem hK, lintegral_zero]
  have hmeas : ∀ K : H.1.cells, Measurable fun z =>
      {K' : H.1.cells | complexCells H.1 K' ⊆ S}.indicator
        (fun K' => (complexCells H.1 K').indicator (fun z => rootedDiamSqDegreeAt H z) z) K := by
    intro K
    by_cases hK : K ∈ {K' : H.1.cells | complexCells H.1 K' ⊆ S}
    · simp only [Set.indicator_of_mem hK]
      exact hGm.indicator (isCompact_complexCells K).isClosed.measurableSet
    · simp only [Set.indicator_of_notMem hK]
      exact measurable_const
  have hpt : ∀ᵐ z ∂(volume : Measure ℂ),
      (∑' K : H.1.cells, {K' : H.1.cells | complexCells H.1 K' ⊆ S}.indicator
        (fun K' => (complexCells H.1 K').indicator (fun z => rootedDiamSqDegreeAt H z) z) K) ≤
        S.indicator (fun z => rootedDiamSqDegreeAt H z) z := by
    filter_upwards [ae_unique_cell H] with z hu
    have hzU : z ∈ ⋃ K, complexCells H.1 K := by
      rw [iUnion_complexCells H.2]
      exact Set.mem_univ z
    obtain ⟨K₀, hK₀⟩ := Set.mem_iUnion.1 hzU
    have hzero : ∀ K ≠ K₀, {K' : H.1.cells | complexCells H.1 K' ⊆ S}.indicator
        (fun K' => (complexCells H.1 K').indicator (fun z => rootedDiamSqDegreeAt H z) z) K =
          0 := by
      intro K hK
      by_cases hKS : K ∈ {K' : H.1.cells | complexCells H.1 K' ⊆ S}
      · simp only [Set.indicator_of_mem hKS,
          Set.indicator_of_notMem (fun hzK => hK (hu K K₀ hzK hK₀) : z ∉ complexCells H.1 K)]
      · simp only [Set.indicator_of_notMem hKS]
    rw [tsum_eq_single K₀ hzero]
    by_cases hKS : K₀ ∈ {K' : H.1.cells | complexCells H.1 K' ⊆ S}
    · simp only [Set.indicator_of_mem hKS, Set.indicator_of_mem hK₀,
        Set.indicator_of_mem ((hKS : complexCells H.1 K₀ ⊆ S) hK₀), le_refl]
    · simp only [Set.indicator_of_notMem hKS, zero_le]
  calc innerDiamSqDegreeSum H.1 S
      = ∑' K : H.1.cells, ∫⁻ z, {K' : H.1.cells | complexCells H.1 K' ⊆ S}.indicator
          (fun K' => (complexCells H.1 K').indicator (fun z => rootedDiamSqDegreeAt H z) z) K :=
        tsum_congr hpart
    _ = ∫⁻ z, ∑' K : H.1.cells, {K' : H.1.cells | complexCells H.1 K' ⊆ S}.indicator
          (fun K' => (complexCells H.1 K').indicator (fun z => rootedDiamSqDegreeAt H z) z) K :=
        (lintegral_tsum fun K => (hmeas K).aemeasurable).symm
    _ ≤ ∫⁻ z, S.indicator (fun z => rootedDiamSqDegreeAt H z) z := lintegral_mono_ae hpt
    _ = ∫⁻ z in S, rootedDiamSqDegreeAt H z := lintegral_indicator (hs := hS) _

/-- The integral of `F` over a compact set is finite: only finitely many cells meet it. -/
theorem setLIntegral_rootedDiamSqDegreeAt_lt_top (H : GMSSpace) {S : Set ℂ} (hS : IsCompact S) :
    ∫⁻ z in S, rootedDiamSqDegreeAt H z < ∞ := by
  have hfin := (locallyFinite_complexCells H.2).finite_nonempty_inter_compact hS
  have hbound : ∀ z ∈ S, rootedDiamSqDegreeAt H z ≤
      ∑ K ∈ hfin.toFinset, (cellPiDensity H.1 K + cellPiStarDensity H.1 K) := by
    intro z hz
    have hzU : z ∈ ⋃ K, complexCells H.1 K := by
      rw [iUnion_complexCells H.2]
      exact Set.mem_univ z
    obtain ⟨K, hK⟩ := Set.mem_iUnion.1 hzU
    have hKmem : K ∈ hfin.toFinset :=
      (Set.Finite.mem_toFinset hfin).2 (show (complexCells H.1 K ∩ S).Nonempty from ⟨z, hK, hz⟩)
    have h1 : rootedCellInf cellPiDensity H z ≤ cellPiDensity H.1 K := iInf₂_le K hK
    have h2 : rootedCellInf cellPiStarDensity H z ≤ cellPiStarDensity H.1 K := iInf₂_le K hK
    exact (add_le_add h1 h2).trans (Finset.single_le_sum
      (f := fun K : H.1.cells => cellPiDensity H.1 K + cellPiStarDensity H.1 K)
      (fun _ _ => zero_le) hKmem)
  calc ∫⁻ z in S, rootedDiamSqDegreeAt H z
      ≤ ∫⁻ _ in S, ∑ K ∈ hfin.toFinset, (cellPiDensity H.1 K + cellPiStarDensity H.1 K) :=
        setLIntegral_mono' hS.measurableSet hbound
    _ = (∑ K ∈ hfin.toFinset, (cellPiDensity H.1 K + cellPiStarDensity H.1 K)) * volume S :=
        setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (ENNReal.sum_ne_top.2 fun _ _ =>
        ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)) hS.measure_lt_top

theorem lintegral_mul_indicator_one_mul {S : Set ℂ} (hS : MeasurableSet S) (c : ℝ≥0∞)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, c * S.indicator (fun _ => (1 : ℝ≥0∞)) z * f z = c * ∫⁻ z in S, f z := by
  have h : (fun z => c * S.indicator (fun _ => (1 : ℝ≥0∞)) z * f z) =
      fun z => c * S.indicator f z := by
    funext z
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz, mul_one]
    · simp only [Set.indicator_of_notMem hz, mul_zero, zero_mul]
  rw [h, lintegral_const_mul c (hf.indicator hS), lintegral_indicator (hs := hS)]

theorem volume_squareAt_ne_zero (q : DyadicCoord) (j : ℤ) :
    volume (squareAt q.1 q.2.1 q.2.2 j 0) ≠ 0 := by
  have hℓ : (0 : ℝ) < (2 : ℝ) ^ (q.1 + (j : ℝ)) := Real.rpow_pos_of_pos two_pos _
  rw [volume_squareAt]
  exact mul_ne_zero (ENNReal.ofReal_pos.2 hℓ).ne' (ENNReal.ofReal_pos.2 hℓ).ne'

theorem volume_squareAt_ne_top (q : DyadicCoord) (j : ℤ) :
    volume (squareAt q.1 q.2.1 q.2.2 j 0) ≠ ∞ :=
  (isCompact_squareAt j 0).measure_lt_top.ne

/-! ### (2.10): the cells contained in `S_k` -/

/-- **arXiv 1807.07515, (2.10)**, for the cells contained in the squares `S_k` around the origin:
almost surely `limsup_k |S_k|⁻² Σ_{H ⊆ S_k} diam(H)² (π(H) + π*(H)) ≤ C₀` with the deterministic
constant `C₀ = E[F]`, `F` as in (2.4). -/
theorem ae_ae_limsup_innerDiamSqDegreeSum_squareAt_le {μ : Measure GMSSpace}
    [IsProbabilityMeasure μ] (hMT : MassTransport μ) (herg : ErgodicModuloScaling μ)
    (hFE : FiniteExpectation μ) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      limsup (fun j : ℤ => (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
          innerDiamSqDegreeSum H.1 (squareAt q.1 q.2.1 q.2.2 j 0)) atTop ≤
        ENNReal.ofReal (∫ H, (rootedDiamSqDegreeAt H 0).toReal ∂μ) := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hm0 : Measurable fun H : GMSSpace => rootedDiamSqDegreeAt H 0 :=
    measurable_rootedDiamSqDegreeAt.comp (measurable_id.prodMk measurable_const)
  have hfin' : ∫⁻ H, rootedDiamSqDegreeAt H 0 ∂μ ≠ ∞ :=
    (lintegral_rootedDiamSqDegreeAt_zero_lt_top hFE).ne
  have hmeas2 : Measurable fun p : GMSSpace × DyadicCoord => rootedDiamSqDegree (p.1, p.2, 0) :=
    measurable_rootedDiamSqDegree.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hfin : ∫⁻ p, rootedDiamSqDegree (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞ := by
    rw [lintegral_prod _ hmeas2.aemeasurable]
    simpa only [rootedDiamSqDegree, lintegral_const, measure_univ, mul_one] using hfin'
  have hint : Integrable (fun H : GMSSpace => (rootedDiamSqDegreeAt H 0).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hm0.aemeasurable hfin'
  have hcond := Measure.ae_ae_of_ae_prod (condExp_fst_cappedSquareTailSigma herg hint)
  filter_upwards [ae_ae_tendsto_squareAt_average_condExp hMT measurable_rootedDiamSqDegree
    rootedDiamSqDegree_similarity hfin, hcond] with H hH hc
  filter_upwards [hH, hc] with q hq hcq
  have hq' : Tendsto (fun j : ℤ => (∫⁻ z, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
      (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z *
        rootedDiamSqDegree (H, q, z)).toReal) atTop
      (𝓝 (∫ H, (rootedDiamSqDegreeAt H 0).toReal ∂μ)) := by
    convert hq using 2
    exact hcq.symm
  have hf : Measurable fun z : ℂ => rootedDiamSqDegree (H, q, z) :=
    measurable_rootedDiamSqDegree.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hne : ∀ j : ℤ, (∫⁻ z, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
      (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z *
        rootedDiamSqDegree (H, q, z)) ≠ ∞ := fun j => by
    rw [lintegral_mul_indicator_one_mul (isCompact_squareAt j 0).isClosed.measurableSet _ hf]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (volume_squareAt_ne_zero q j))
      (setLIntegral_rootedDiamSqDegreeAt_lt_top H (isCompact_squareAt j 0)).ne
  have htend : Tendsto (fun j : ℤ => ∫⁻ z, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
      (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z *
        rootedDiamSqDegree (H, q, z)) atTop
      (𝓝 (ENNReal.ofReal (∫ H, (rootedDiamSqDegreeAt H 0).toReal ∂μ))) :=
    (ENNReal.tendsto_ofReal hq').congr fun j => ENNReal.ofReal_toReal (hne j)
  have hle : ∀ j : ℤ, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
      innerDiamSqDegreeSum H.1 (squareAt q.1 q.2.1 q.2.2 j 0) ≤
        ∫⁻ z, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
          (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z *
            rootedDiamSqDegree (H, q, z) := fun j => by
    have hSm : MeasurableSet (squareAt q.1 q.2.1 q.2.2 j 0) :=
      (isCompact_squareAt j 0).isClosed.measurableSet
    rw [lintegral_mul_indicator_one_mul hSm _ hf]
    exact mul_le_mul' le_rfl (innerDiamSqDegreeSum_le_setLIntegral H hSm)
  exact (Filter.limsup_le_limsup (Filter.Eventually.of_forall hle)).trans htend.limsup_eq.le

/-! ### Measurability of the square event -/

/-- Containment of a fixed set in a closed square is closed in its parameters. -/
theorem isClosed_setOf_subset_cornerSquare (A : Set ℂ) :
    IsClosed {p : ℝ × ℝ × ℝ | A ⊆ cornerSquare p.1 p.2.1 p.2.2} := by
  have heq : {p : ℝ × ℝ × ℝ | A ⊆ cornerSquare p.1 p.2.1 p.2.2} =
      ⋂ z ∈ A, {p : ℝ × ℝ × ℝ | z ∈ cornerSquare p.1 p.2.1 p.2.2} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, Set.subset_def]
  rw [heq]
  refine isClosed_iInter fun z => isClosed_iInter fun _ => ?_
  simp only [mem_cornerSquare, Set.ofPred_and]
  exact (isClosed_le continuous_fst continuous_const).inter
    ((isClosed_le continuous_const (continuous_fst.add continuous_snd.snd)).inter
      ((isClosed_le continuous_snd.fst continuous_const).inter
        (isClosed_le continuous_const (continuous_snd.fst.add continuous_snd.snd))))

/-- The total weight of cells contained in a square is measurable in the square parameters. -/
theorem measurable_innerDiamSqDegreeSum_cornerSquare (H : GMSSpace) :
    Measurable fun p : ℝ × ℝ × ℝ =>
      innerDiamSqDegreeSum H.1 (cornerSquare p.1 p.2.1 p.2.2) := by
  have := countable_cells H.2
  unfold innerDiamSqDegreeSum
  apply Measurable.tsum
  intro K
  have hm := (isClosed_setOf_subset_cornerSquare (complexCells H.1 K)).measurableSet
  convert (measurable_const.indicator hm : Measurable
    ({p : ℝ × ℝ × ℝ | complexCells H.1 K ⊆ cornerSquare p.1 p.2.1 p.2.2}.indicator
      (fun _ => diamSqDegree H.1 K))) using 1
  ext p
  by_cases h : complexCells H.1 K ⊆ cornerSquare p.1 p.2.1 p.2.2 <;>
    simp [Set.indicator, h]

/-- The bounded interior-weight event is measurable in the square parameters. -/
theorem measurableSet_innerDiamSqDegreeSum_cornerSquare_le (H : GMSSpace) (c : ℝ≥0∞) :
    MeasurableSet {p : ℝ × ℝ × ℝ |
      innerDiamSqDegreeSum H.1 (cornerSquare p.1 p.2.1 p.2.2) ≤
        c * volume (cornerSquare p.1 p.2.1 p.2.2)} := by
  apply measurableSet_le (measurable_innerDiamSqDegreeSum_cornerSquare H)
  have hm : Measurable fun p : ℝ × ℝ × ℝ => volume (cornerSquare p.1 p.2.1 p.2.2) := by
    simp_rw [volume_cornerSquare]
    exact (ENNReal.measurable_ofReal.comp measurable_snd.snd).mul
      (ENNReal.measurable_ofReal.comp measurable_snd.snd)
  exact measurable_const.mul hm

/-! ### Lemma 2.10 -/

/-- A cell meeting the square `[a, a + ℓ] × [b, b + ℓ]` with diameter at most `ℓ / 2` lies in
the square `[a - ℓ, a + 3ℓ] × [b - ℓ, b + 3ℓ]`. -/
theorem complexCells_subset_cornerSquare {H : CellConfig} {K : H.cells} {a b ℓ : ℝ}
    (hmeet : (complexCells H K ∩ cornerSquare a b ℓ).Nonempty)
    (hdiam : Metric.diam (K.1 : Set Plane) ≤ ℓ / 2) :
    complexCells H K ⊆ cornerSquare (a - ℓ) (b - ℓ) (4 * ℓ) := by
  obtain ⟨z, hzK, hzS⟩ := hmeet
  intro w hw
  have hd : dist w z ≤ ℓ / 2 := by
    have h := Metric.dist_le_diam_of_mem K.1.isCompact.isBounded
      (show planeCoord w ∈ (K.1 : Set Plane) from hw)
      (show planeCoord z ∈ (K.1 : Set Plane) from hzK)
    rw [LinearIsometryEquiv.dist_map] at h
    exact h.trans hdiam
  have hre : |w.re - z.re| ≤ ℓ / 2 := by
    have h := Complex.abs_re_le_norm (w - z)
    rw [Complex.sub_re] at h
    rw [dist_eq_norm] at hd
    exact h.trans hd
  have him : |w.im - z.im| ≤ ℓ / 2 := by
    have h := Complex.abs_im_le_norm (w - z)
    rw [Complex.sub_im] at h
    rw [dist_eq_norm] at hd
    exact h.trans hd
  obtain ⟨h1, h2, h3, h4⟩ := mem_cornerSquare.1 hzS
  rw [abs_le] at hre him
  have hℓ : 0 ≤ ℓ := by linarith [hre.1, hre.2]
  exact mem_cornerSquare.2 ⟨by linarith [hre.1], by linarith [hre.2], by linarith [him.1],
    by linarith [him.2]⟩

/-- A conditional form of arXiv 1807.07515, Lemma 2.10, (2.9). Let `μ` be the law of a cell configuration satisfying
the mass-transport principle, ergodicity modulo scaling and the finite expectation hypothesis
(1.5), and `S_k` the square of generation `k` of an independent uniform dyadic system containing
the origin. There is a deterministic constant `C > 0` such that almost surely
`limsup_{k → ∞} |S_k|⁻² Σ_{H ∈ H(S_k)} diam(H)² (π(H) + π*(H)) ≤ C`.

The proof assumes IP Lemma 2.9 with `ε = 1/2` (`h29`: almost surely, for large `k`, every cell
meeting `S_k` has diameter at most `|S_k| / 2`). -/
theorem exists_limsup_inv_volume_mul_diamSqDegreeSum_le_of_boundary {μ : Measure GMSSpace}
    [IsProbabilityMeasure μ] (hMT : MassTransport μ) (herg : ErgodicModuloScaling μ)
    (hFE : FiniteExpectation μ)
    (h29 : ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ᶠ j in atTop, ∀ K : H.1.cells,
      (complexCells H.1 K ∩ squareAt q.1 q.2.1 q.2.2 j 0).Nonempty →
        Metric.diam (K.1 : Set Plane) ≤ (2 : ℝ) ^ (q.1 + (j : ℝ)) / 2)
    :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      limsup (fun j : ℤ => (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
        diamSqDegreeSum H.1 (squareAt q.1 q.2.1 q.2.2 j 0)) atTop ≤ ENNReal.ofReal C := by
  have h28 : ∀ c : ℝ≥0∞, (∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ᶠ j in atTop,
        innerDiamSqDegreeSum H.1 (squareAt q.1 q.2.1 q.2.2 j 0) ≤
          c * volume (squareAt q.1 q.2.1 q.2.2 j 0)) →
      ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ᶠ j in atTop,
        innerDiamSqDegreeSum H.1 (originAncestorSquare q j) ≤
          c * volume (originAncestorSquare q j) := by
    intro c hc
    simpa only [originAncestorSquare] using
      (ae_ae_eventually_dyadicAncestor_side_four
        (E := fun S H => innerDiamSqDegreeSum H.1 S ≤ c * volume S)
        (Filter.Eventually.of_forall fun H => measurableSet_innerDiamSqDegreeSum_cornerSquare_le H c)
        hc)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = ∫ H, (rootedDiamSqDegreeAt H 0).toReal ∂μ := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := by
    rw [hC₀]
    exact integral_nonneg fun H => ENNReal.toReal_nonneg
  refine ⟨16 * (C₀ + 1), by positivity, ?_⟩
  have hev : ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw, ∀ᶠ j in atTop,
      innerDiamSqDegreeSum H.1 (squareAt q.1 q.2.1 q.2.2 j 0) ≤
        ENNReal.ofReal (C₀ + 1) * volume (squareAt q.1 q.2.1 q.2.2 j 0) := by
    filter_upwards [ae_ae_limsup_innerDiamSqDegreeSum_squareAt_le hMT herg hFE] with H hH
    filter_upwards [hH] with q hq
    rw [← hC₀] at hq
    have hlt : limsup (fun j : ℤ => (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
        innerDiamSqDegreeSum H.1 (squareAt q.1 q.2.1 q.2.2 j 0)) atTop <
          ENNReal.ofReal (C₀ + 1) :=
      hq.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
    filter_upwards [Filter.eventually_lt_of_limsup_lt hlt] with j hj
    have hv0 := volume_squareAt_ne_zero q j
    have hvt := volume_squareAt_ne_top q j
    calc innerDiamSqDegreeSum H.1 (squareAt q.1 q.2.1 q.2.2 j 0)
        = volume (squareAt q.1 q.2.1 q.2.2 j 0) * ((volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
            innerDiamSqDegreeSum H.1 (squareAt q.1 q.2.1 q.2.2 j 0)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hv0 hvt, one_mul]
      _ ≤ volume (squareAt q.1 q.2.1 q.2.2 j 0) * ENNReal.ofReal (C₀ + 1) :=
          mul_le_mul' le_rfl hj.le
      _ = ENNReal.ofReal (C₀ + 1) * volume (squareAt q.1 q.2.1 q.2.2 j 0) := mul_comm _ _
  have hanc := h28 (ENNReal.ofReal (C₀ + 1)) hev
  filter_upwards [hanc, h29] with H hH1 hH2
  filter_upwards [hH1, hH2] with q hq1 hq2
  have hbound : ∀ᶠ j in atTop, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
      diamSqDegreeSum H.1 (squareAt q.1 q.2.1 q.2.2 j 0) ≤ ENNReal.ofReal (16 * (C₀ + 1)) := by
    filter_upwards [hq1, hq2] with j hj1 hj2
    have hsub : diamSqDegreeSum H.1 (squareAt q.1 q.2.1 q.2.2 j 0) ≤
        innerDiamSqDegreeSum H.1 (originAncestorSquare q j) := by
      refine ENNReal.tsum_le_tsum fun K => ?_
      by_cases hK : K ∈
          {K : H.1.cells | (complexCells H.1 K ∩ squareAt q.1 q.2.1 q.2.2 j 0).Nonempty}
      · have hKA : K ∈ {K : H.1.cells | complexCells H.1 K ⊆ originAncestorSquare q j} :=
          complexCells_subset_cornerSquare (a := gridFloor q.1 q.2.1 j (0 : ℂ).re)
            (b := gridFloor q.1 q.2.2 j (0 : ℂ).im) (ℓ := (2 : ℝ) ^ (q.1 + (j : ℝ))) hK
            (hj2 K hK)
        simp only [Set.indicator_of_mem hK, Set.indicator_of_mem hKA, le_refl]
      · simp only [Set.indicator_of_notMem hK, zero_le]
    have hvolA : volume (originAncestorSquare q j) =
        16 * volume (squareAt q.1 q.2.1 q.2.2 j 0) := by
      rw [originAncestorSquare, volume_cornerSquare, volume_squareAt,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
      ring
    have hv0 := volume_squareAt_ne_zero q j
    have hvt := volume_squareAt_ne_top q j
    calc (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
          diamSqDegreeSum H.1 (squareAt q.1 q.2.1 q.2.2 j 0)
        ≤ (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
            (ENNReal.ofReal (C₀ + 1) * (16 * volume (squareAt q.1 q.2.1 q.2.2 j 0))) :=
          mul_le_mul' le_rfl (hsub.trans (hj1.trans_eq (by rw [hvolA])))
      _ = ((volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ * volume (squareAt q.1 q.2.1 q.2.2 j 0)) *
            (16 * ENNReal.ofReal (C₀ + 1)) := by ring
      _ = ENNReal.ofReal (16 * (C₀ + 1)) := by
          rw [ENNReal.inv_mul_cancel hv0 hvt, one_mul,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16), ENNReal.ofReal_ofNat]
  exact Filter.limsup_le_of_le (h := hbound)

end LatticeProb.CellConfigCappedSquare
