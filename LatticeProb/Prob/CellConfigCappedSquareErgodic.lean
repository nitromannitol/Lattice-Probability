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
* `ae_exists_lt_forall_originCappedSquare_eq`: almost surely `m ↦ S_m^0` is a step function that is
  constant on an interval `[m, m₂)` with `m < m₂` to the right of every mass `m ∈ (0, ∞)`.
* `ae_ae_tendsto_cappedSquareAverage_ofReal`: the uniform averages over `S_m^0` converge to
  `E[G(H, D, 0) | 𝓘]` as the real mass `m → ∞`, for almost every `H` and almost every `D`.
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

/-! ### Rational and real cell masses -/

/-- The cell mass `max r 1` attached to a rational parameter `r`. -/
noncomputable def ratMass (r : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (max (r : ℝ) 1)

theorem ratMass_ne_zero (r : ℚ) : ratMass r ≠ 0 :=
  (ENNReal.ofReal_pos.2 (lt_max_of_lt_right one_pos)).ne'

theorem ratMass_ne_top (r : ℚ) : ratMass r ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem ratMass_mono : Monotone ratMass := fun _ _ h =>
  ENNReal.ofReal_le_ofReal (max_le_max (by exact_mod_cast h) le_rfl)

/-- The σ-algebras `𝓕_{max(r, 1)}`, `r ∈ ℚ`, decrease. -/
theorem antitone_cappedSquareSigma_ratMass :
    Antitone fun r : ℚ => cappedSquareSigma (ratMass r) := fun r r' h =>
  cappedSquareSigma_anti (ratMass_ne_zero r) (ratMass_mono h) (ratMass_ne_top r')

/-- The tail of the rational family `𝓕_{max(r, 1)}` is `𝓘`. -/
theorem iInf_cappedSquareSigma_ratMass_eq :
    (⨅ r : ℚ, cappedSquareSigma (ratMass r)) = cappedSquareTailSigma := by
  refine le_antisymm (le_iInf fun k => iInf_le_of_le ((k : ℚ) + 1) ?_)
    (le_iInf fun r =>
      cappedSquareTailSigma_le_cappedSquareSigma (ratMass_ne_zero r) (ratMass_ne_top r))
  refine cappedSquareSigma_anti (by simp) ?_ (ratMass_ne_top _)
  have hk : ((k : ℝ≥0∞) + 1) = ENNReal.ofReal ((k : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg k) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  rw [hk, ratMass]
  exact ENNReal.ofReal_le_ofReal (le_max_of_le_left (by simp))

/-- A function of a real parameter that eventually takes values of a convergent rational family
at larger parameters converges to the same limit. -/
theorem tendsto_of_eventually_exists_rat {β : Type*} [TopologicalSpace β] {f : ℚ → β}
    {g : ℝ → β} {L : β} (hf : Tendsto f atTop (𝓝 L))
    (hg : ∀ᶠ x : ℝ in atTop, ∃ r : ℚ, x ≤ (r : ℝ) ∧ g x = f r) : Tendsto g atTop (𝓝 L) := by
  rw [tendsto_def] at hf ⊢
  intro U hU
  obtain ⟨N, hN⟩ := mem_atTop_sets.1 (hf U hU)
  filter_upwards [hg, eventually_ge_atTop (N : ℝ)] with x ⟨r, hxr, hgr⟩ hx
  rw [mem_preimage, hgr]
  exact hN r (by exact_mod_cast hx.trans hxr)

/-- **The capped square is a right step function of the mass**: for every configuration and
almost every dyadic system, to the right of every mass `m ∈ (0, ∞)` there is `m₂ > m` with
`S_{m'}^0 = S_m^0` for all `m' ∈ [m, m₂)` (arXiv 1807.07515, (2.1): `m₂` is the cell mass of the
next larger square containing the origin). -/
theorem ae_exists_lt_forall_originCappedSquare_eq (H : GMSSpace) :
    ∀ᵐ q ∂dyadicLaw, ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ → ∃ m₂, m < m₂ ∧
      ∀ m', m ≤ m' → m' < m₂ → originCappedSquare m' H q = originCappedSquare m H q := by
  have := countable_cells H.2
  filter_upwards [ae_exists_isCappedSquare_squareAt_cellMass 0 (locallyFinite_complexCells H.2)
      (iUnion_complexCells H.2) isCompact_complexCells (volume_complexCells_ne_zero H.2),
    ae_isCompatible_isOffGrid_system 0] with q hex hq
  intro m hm0 hmtop
  obtain ⟨j, -, hj2, hcap⟩ := hex m hm0 hmtop
  refine ⟨_, hj2, fun m' hm' hm'2 => ?_⟩
  have hm'0 : m' ≠ 0 := ((pos_iff_ne_zero.2 hm0).trans_le hm').ne'
  have hm'top : m' ≠ ∞ := (hm'2.trans_le le_top).ne
  obtain ⟨j', hj'1, -, hcap'⟩ := hex m' hm'0 hm'top
  refine hcap'.cappedSquare_eq.trans (Eq.trans ?_ hcap.cappedSquare_eq.symm)
  have hsub := hcap'.subset hcap.mem_family hcap.mem (hcap.mass_le.trans hm')
  rcases le_or_gt j' j with h | h
  · exact (squareAt_mono hq.1 hq.2.1 hq.2.2 h).antisymm hsub
  · exact absurd (hj'1.trans_lt hm'2)
      (not_lt.2 (cellMass_mono _ _ (squareAt_mono hq.1 hq.2.1 hq.2.2 (Int.add_one_le_of_lt h))))

section RealLimit

variable {μ : Measure GMSSpace}

/-- **Conditional ergodic lemma along rational masses**: under the hypotheses of
`ae_tendsto_kernelAverage_origin_condExp`, almost surely under `μ ⊗ P`, the kernel averages
`A_{max(r, 1)} G(H, D, 0)` converge to `E[G(H, D, 0) | 𝓘]` as `r → ∞` through `ℚ`. -/
theorem ae_tendsto_kernelAverage_origin_condExp_rat [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (hfin : ∫⁻ p, G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞) :
    ∀ᵐ p ∂μ.prod dyadicLaw,
      Tendsto (fun r : ℚ => (kernelAverage (ratMass r) G (p.1, p.2, 0)).toReal) atTop
        (𝓝 ((μ.prod dyadicLaw)[fun p => (G (p.1, p.2, 0)).toReal | cappedSquareTailSigma] p)) := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hG0 : Measurable fun p : GMSSpace × DyadicCoord => G (p.1, p.2, 0) :=
    hG.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hk : ∀ᵐ p ∂μ.prod dyadicLaw, ∀ r : ℚ,
      (kernelAverage (ratMass r) G (p.1, p.2, 0)).toReal =
        (μ.prod dyadicLaw)[fun p => (G (p.1, p.2, 0)).toReal | cappedSquareSigma (ratMass r)] p :=
    ae_all_iff.2 fun r =>
      kernelAverage_origin_ae_eq_condExp hMT (ratMass_ne_zero r) (ratMass_ne_top r) hG hinv hfin
  have h := ReflectedGMS.ReverseRationalAE.tendsto_condExp_iInf_rat_ae (P := μ.prod dyadicLaw)
    (ms := fun r : ℚ => cappedSquareSigma (ratMass r)) (fun _ => cappedSquareSigma_le _)
    antitone_cappedSquareSigma_ratMass
    (integrable_toReal_of_lintegral_ne_top hG0.aemeasurable hfin)
  rw [iInf_cappedSquareSigma_ratMass_eq] at h
  filter_upwards [hk, h] with p hp hlim
  exact hlim.congr fun r => (hp r).symm

/-- **Conditional ergodic lemma for the capped-square averages along real masses**
(arXiv 1807.07515, Lemma 2.7, conditional form): under the hypotheses of
`ae_tendsto_kernelAverage_origin_condExp`, for `μ`-almost every configuration `H` and almost every
dyadic system `D`, `|S_m^0|⁻¹ ∫_{S_m^0} G(H, D, z) dz → E[G(H, D, 0) | 𝓘](H, D)` as the mass
`m → ∞` through `ℝ`. -/
theorem ae_ae_tendsto_cappedSquareAverage_ofReal [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (hfin : ∫⁻ p, G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      Tendsto (fun x : ℝ => (cappedSquareAverage (ENNReal.ofReal x) G H q).toReal) atTop
        (𝓝 ((μ.prod dyadicLaw)[fun p => (G (p.1, p.2, 0)).toReal | cappedSquareTailSigma]
          (H, q))) := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  filter_upwards [Measure.ae_ae_of_ae_prod
    (ae_tendsto_kernelAverage_origin_condExp_rat hMT hG hinv hfin)] with H hH
  filter_upwards [hH, ae_all_iff.2 fun r : ℚ =>
      ae_kernelAverage_origin_eq (ratMass_ne_zero r) (ratMass_ne_top r) G H,
    ae_exists_lt_forall_originCappedSquare_eq H] with q hq hkq hstep
  have hrat : Tendsto (fun r : ℚ => (cappedSquareAverage (ratMass r) G H q).toReal) atTop _ :=
    hq.congr fun r => congrArg ENNReal.toReal (hkq r)
  refine tendsto_of_eventually_exists_rat hrat ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : ENNReal.ofReal x ≠ 0 := (ENNReal.ofReal_pos.2 (zero_lt_one.trans_le hx)).ne'
  obtain ⟨m₂, hm₂, hconst⟩ := hstep _ hx0 ENNReal.ofReal_ne_top
  obtain ⟨r, -, hxr, hr2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hm₂
  have hxr' : x ≤ r := (ENNReal.ofReal_lt_ofReal_iff'.1 hxr).1.le
  refine ⟨r, hxr', ?_⟩
  have hS := hconst _ (ENNReal.ofReal_le_ofReal hxr') hr2
  have hmr : ratMass r = ENNReal.ofReal r := by rw [ratMass, max_eq_left (hx.trans hxr')]
  rw [hmr]
  simp only [cappedSquareAverage, hS]

end RealLimit

end LatticeProb.CellConfigCappedSquare
