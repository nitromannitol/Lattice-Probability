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
* `ae_kernelAverage_eq_origin`: block constancy; almost surely `A_m G` is constant on the capped square
  `S_m^0` around the origin, and `ae_kernelAverage_origin_eq`: there it is the uniform average.
* `measurable_kernelAverage_origin`: `(H, D) ↦ A_m G(H, D, 0)` is `𝓕_m`-measurable.
* `cappedSquareSigma_anti`: `𝓕_{m'} ≤ 𝓕_m` for `0 < m ≤ m' < ∞`, and
  `antitone_cappedSquareSigma_natCast_add_one`: `k ↦ 𝓕_{k+1}` is antitone.
* `kernelAverage_origin_ae_eq_condExp`: under the mass-transport principle, `A_m G(·, ·, 0)` is a version
  of `E[G(H, D, 0) | 𝓕_m]`.
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

/-! ### Block constancy and the witnesses of `𝓕_m` -/

/-- **The kernel is constant on the selected square**: for a dyadic system with compatible offset
sequences, an off-grid root `w` whose selected generation is `j` and an off-grid point `z` of the
square of generation `j` at `w`, the kernel rooted at `z` is the kernel rooted at `w` (the squares of
generations `j` and `j + 1` at `z` are those at `w`, so `j` is also selected at `z`). -/
theorem averageKernel_eq_of_mem_squareAt {m : ℝ≥0∞} {H : GMSSpace} {q : DyadicCoord}
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) {w z : ℂ}
    (hw : IsOffGrid q.1 q.2.1 q.2.2 w) (hz : IsOffGrid q.1 q.2.1 q.2.2 z) {j : ℤ}
    (hj : j ∈ selectionSet (complexCells H.1) m q w) (hzj : z ∈ squareAt q.1 q.2.1 q.2.2 j w)
    (w₁ : ℂ) : averageKernel m (H, (q, z), w₁) = averageKernel m (H, (q, w), w₁) := by
  have e0 : squareAt q.1 q.2.1 q.2.2 j w = squareAt q.1 q.2.1 q.2.2 j z :=
    squareAt_eq_of_mem hz hzj
  have e1 : squareAt q.1 q.2.1 q.2.2 (j + 1) w = squareAt q.1 q.2.1 q.2.2 (j + 1) z :=
    squareAt_eq_of_mem hz (squareAt_mono_of_isCompatible h₁ h₂ w (Int.le_add_one le_rfl) hzj)
  have hjz : j ∈ selectionSet (complexCells H.1) m q z :=
    ⟨by rw [← e0]; exact hj.1, by rw [← e1]; exact hj.2⟩
  dsimp only [averageKernel]
  rw [selectedSum_eq_of_mem (monotone_cellMass_squareAt h₁ h₂ hz) hjz,
    selectedSum_eq_of_mem (monotone_cellMass_squareAt h₁ h₂ hw) hj, e0]

/-- **The kernel average is constant on the selected square** (deterministic form). -/
theorem kernelAverage_eq_of_mem_squareAt (m : ℝ≥0∞) (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞)
    {H : GMSSpace} {q : DyadicCoord} (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2)
    {w z : ℂ} (hw : IsOffGrid q.1 q.2.1 q.2.2 w) (hz : IsOffGrid q.1 q.2.1 q.2.2 z) {j : ℤ}
    (hj : j ∈ selectionSet (complexCells H.1) m q w) (hzj : z ∈ squareAt q.1 q.2.1 q.2.2 j w) :
    kernelAverage m G (H, q, z) = kernelAverage m G (H, q, w) := by
  dsimp only [kernelAverage]
  exact lintegral_congr fun w₁ => by
    rw [averageKernel_eq_of_mem_squareAt h₁ h₂ hw hz hj hzj w₁]

/-- **Block constancy of the kernel average**: for every configuration `H`, every cell mass
`m ∈ (0, ∞)` and almost every dyadic system, the kernel average rooted at almost every point of the
capped square `S_m^0(H, D)` around the origin is the kernel average rooted at the origin. -/
theorem ae_kernelAverage_eq_origin {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞)
    (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞) (H : GMSSpace) :
    ∀ᵐ q ∂dyadicLaw, ∀ᵐ z ∂volume, z ∈ originCappedSquare m H q →
      kernelAverage m G (H, q, z) = kernelAverage m G (H, q, 0) := by
  have := countable_cells H.2
  filter_upwards [ae_isCompatible_isOffGrid_system 0,
    ae_exists_isCappedSquare_squareAt_cellMass 0 (locallyFinite_complexCells H.2)
      (iUnion_complexCells H.2) isCompact_complexCells (volume_complexCells_ne_zero H.2)]
    with q hq hex
  obtain ⟨j, hj1, hj2, hcap⟩ := hex m hm0 hmtop
  filter_upwards [ae_isOffGrid_volume q.1 q.2.1 q.2.2] with z hz hzS
  have hzj : z ∈ squareAt q.1 q.2.1 q.2.2 j 0 := by
    rw [← hcap.cappedSquare_eq]
    exact hzS
  exact kernelAverage_eq_of_mem_squareAt m G hq.1 hq.2.1 hq.2.2 hz ⟨hj1, hj2⟩ hzj

/-- **At the origin the kernel average is the uniform average over the capped square**: for every
configuration and every cell mass `m ∈ (0, ∞)`, almost surely in the dyadic system,
`A_m G(H, D, 0) = |S_m^0|⁻¹ ∫_{S_m^0} G(H, D, z) dz`. -/
theorem ae_kernelAverage_origin_eq {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞)
    (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞) (H : GMSSpace) :
    ∀ᵐ q ∂dyadicLaw, kernelAverage m G (H, q, 0) = cappedSquareAverage m G H q := by
  filter_upwards [ae_averageKernel_eq H 0] with q hq
  dsimp only [kernelAverage, cappedSquareAverage]
  exact lintegral_congr fun z => by rw [hq m hm0 hmtop z]

/-- **The strict upper level sets of the kernel average are witnesses of `𝓕_m`**, for a measurable
`G ≥ 0` invariant under the joint similarity at every dyadic system with compatible offset
sequences. -/
theorem isCappedSquareWitness_kernelAverage {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (t : ℝ≥0∞) : IsCappedSquareWitness m (kernelAverage m G ⁻¹' Ioi t) := by
  refine ⟨measurable_kernelAverage m hG measurableSet_Ioi,
    fun s u hs H H' h q h₁ h₂ w => ?_, fun H => ?_⟩
  · have e := kernelAverage_similarity m hG h h₁ h₂ (hinv s u hs H H' h q h₁ h₂) w
    simp only [mem_preimage, e]
  · filter_upwards [ae_kernelAverage_eq_origin hm0 hmtop G H] with q hq
    filter_upwards [hq] with z hz hzS
    simp only [mem_preimage, hz hzS]

/-- **The kernel average at the origin is `𝓕_m`-measurable**: `(H, D) ↦ A_m G(H, D, 0)` is
measurable for the σ-algebra `𝓕_m` (`cappedSquareSigma`), for a measurable invariant `G ≥ 0`. -/
theorem measurable_kernelAverage_origin {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w)) :
    Measurable[cappedSquareSigma m] fun p : GMSSpace × DyadicCoord =>
      kernelAverage m G (p.1, p.2, 0) :=
  measurable_of_Ioi (mδ := cappedSquareSigma m) fun t =>
    ⟨_, isCappedSquareWitness_kernelAverage hm0 hmtop hG hinv t, rfl⟩

/-! ### `𝓕_m` decreases in the cell mass -/

/-- **The capped squares increase with the cell mass**: for every configuration `H`, cell masses
`0 < m ≤ m' < ∞` and almost every dyadic system, `S_m^0(H, D) ⊆ S_{m'}^0(H, D)`. -/
theorem ae_originCappedSquare_subset {m m' : ℝ≥0∞} (hm0 : m ≠ 0) (hmm' : m ≤ m')
    (hm'top : m' ≠ ∞) (H : GMSSpace) :
    ∀ᵐ q ∂dyadicLaw, originCappedSquare m H q ⊆ originCappedSquare m' H q := by
  have := countable_cells H.2
  filter_upwards [ae_exists_isCappedSquare_squareAt_cellMass 0 (locallyFinite_complexCells H.2)
      (iUnion_complexCells H.2) isCompact_complexCells (volume_complexCells_ne_zero H.2)]
    with q hex z hz
  obtain ⟨j, -, -, hcap⟩ := hex m hm0 (ne_top_of_le_ne_top hm'top hmm')
  obtain ⟨j', -, -, hcap'⟩ := hex m' ((pos_iff_ne_zero.2 hm0).trans_le hmm').ne' hm'top
  have h1 : z ∈ squareAt q.1 q.2.1 q.2.2 j 0 := by
    rw [← hcap.cappedSquare_eq]
    exact hz
  have h2 := hcap'.subset hcap.mem_family hcap.mem (hcap.mass_le.trans hmm') h1
  rw [← hcap'.cappedSquare_eq] at h2
  exact h2

/-- **`𝓕_m` decreases in the cell mass** (arXiv 1807.07515, Definition 2.5): for cell masses
`0 < m ≤ m' < ∞`, every event of `𝓕_{m'}` is an event of `𝓕_m`, since almost surely
`S_m^0 ⊆ S_{m'}^0`, so a witness of `𝓕_{m'}` is a witness of `𝓕_m`. -/
theorem cappedSquareSigma_anti {m m' : ℝ≥0∞} (hm0 : m ≠ 0) (hmm' : m ≤ m') (hm'top : m' ≠ ∞) :
    cappedSquareSigma m' ≤ cappedSquareSigma m := by
  rintro A ⟨B, hB, rfl⟩
  refine ⟨B, ⟨hB.1, hB.2.1, fun H => ?_⟩, rfl⟩
  filter_upwards [hB.2.2 H, ae_originCappedSquare_subset hm0 hmm' hm'top H] with q hq hsub
  filter_upwards [hq] with z hz hzS
  exact hz (hsub hzS)

/-- The σ-algebras `𝓕_{k+1}`, `k ∈ ℕ`, form a decreasing sequence. -/
theorem antitone_cappedSquareSigma_natCast_add_one :
    Antitone fun k : ℕ => cappedSquareSigma ((k : ℝ≥0∞) + 1) := fun k l hkl =>
  cappedSquareSigma_anti (by simp) (by exact_mod_cast Nat.add_le_add_right hkl 1) (by simp)

/-! ### The conditional expectation given `𝓕_m` -/

section CondExp

variable {μ : Measure GMSSpace}

/-- **Set-integral identity on the product space**: under the mass-transport principle, for every
cell mass `m ∈ (0, ∞)`, every measurable invariant `G ≥ 0` and every event `A ∈ 𝓕_m`,
`∫_A A_m G(H, D, 0) d(μ ⊗ P) = ∫_A G(H, D, 0) d(μ ⊗ P)`, with `P` the law of the uniform dyadic
system. -/
theorem setLIntegral_kernelAverage_origin (hMT : MassTransport μ) {m : ℝ≥0∞} (hm0 : m ≠ 0)
    (hmtop : m ≠ ∞) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    {A : Set (GMSSpace × DyadicCoord)} (hA : MeasurableSet[cappedSquareSigma m] A) :
    ∫⁻ p in A, kernelAverage m G (p.1, p.2, 0) ∂μ.prod dyadicLaw =
      ∫⁻ p in A, G (p.1, p.2, 0) ∂μ.prod dyadicLaw := by
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  have hAm : MeasurableSet A := cappedSquareSigma_le m A hA
  have hK : Measurable fun p : GMSSpace × DyadicCoord => kernelAverage m G (p.1, p.2, 0) :=
    (measurable_kernelAverage m hG).comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hG0 : Measurable fun p : GMSSpace × DyadicCoord => G (p.1, p.2, 0) :=
    hG.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hind : ∀ f : GMSSpace × DyadicCoord → ℝ≥0∞, ∀ p,
      A.indicator f p = A.indicator (fun _ => (1 : ℝ≥0∞)) p * f p := by
    intro f p
    by_cases hp : p ∈ A
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, one_mul]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, zero_mul]
  have e1 : ∫⁻ p in A, kernelAverage m G (p.1, p.2, 0) ∂μ.prod dyadicLaw =
      ∫⁻ H, ∫⁻ q, A.indicator (fun _ => (1 : ℝ≥0∞)) (H, q) * cappedSquareAverage m G H q
        ∂dyadicLaw ∂μ := by
    rw [← lintegral_indicator hAm, lintegral_congr (hind _),
      lintegral_prod (fun p => A.indicator (fun _ => (1 : ℝ≥0∞)) p *
        kernelAverage m G (p.1, p.2, 0)) ((measurable_const.indicator hAm).mul hK).aemeasurable]
    refine lintegral_congr fun H => lintegral_congr_ae ?_
    filter_upwards [ae_kernelAverage_origin_eq hm0 hmtop G H] with q hq
    rw [hq]
  have e2 : ∫⁻ p in A, G (p.1, p.2, 0) ∂μ.prod dyadicLaw =
      ∫⁻ H, ∫⁻ q, A.indicator (fun _ => (1 : ℝ≥0∞)) (H, q) * G (H, q, 0) ∂dyadicLaw ∂μ := by
    rw [← lintegral_indicator hAm, lintegral_congr (hind _),
      lintegral_prod (fun p => A.indicator (fun _ => (1 : ℝ≥0∞)) p * G (p.1, p.2, 0))
        ((measurable_const.indicator hAm).mul hG0).aemeasurable]
  rw [e1, e2, lintegral_indicator_mul_cappedSquareAverage hMT hm0 hmtop hG hinv hA]

/-- **`avg_m G = E[G | 𝓕_m]`** (arXiv 1807.07515, proof of Lemma 2.7): under the mass-transport
principle, for a finite law `μ` of the configuration, every cell mass `m ∈ (0, ∞)` and every
measurable `G ≥ 0` invariant under the joint similarity with `E[G(H, D, 0)] < ∞`, the kernel average
at the origin, i.e. almost surely the uniform average `|S_m^0|⁻¹ ∫_{S_m^0} G(H, D, z) dz`, is a
version of the conditional expectation of `G(H, D, 0)` given `𝓕_m` under `μ ⊗ P`. -/
theorem kernelAverage_origin_ae_eq_condExp [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞) {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞}
    (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (hfin : ∫⁻ p, G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞) :
    (fun p : GMSSpace × DyadicCoord => (kernelAverage m G (p.1, p.2, 0)).toReal)
      =ᵐ[μ.prod dyadicLaw]
        (μ.prod dyadicLaw)[fun p => (G (p.1, p.2, 0)).toReal | cappedSquareSigma m] := by
  have hK : Measurable fun p : GMSSpace × DyadicCoord => kernelAverage m G (p.1, p.2, 0) :=
    (measurable_kernelAverage m hG).comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hG0 : Measurable fun p : GMSSpace × DyadicCoord => G (p.1, p.2, 0) :=
    hG.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hKfin : ∫⁻ p, kernelAverage m G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞ := by
    have h := setLIntegral_kernelAverage_origin hMT hm0 hmtop hG hinv
      (@MeasurableSet.univ _ (cappedSquareSigma m))
    simp only [Measure.restrict_univ] at h
    rw [h]
    exact hfin
  have hKm := measurable_kernelAverage_origin hm0 hmtop hG hinv
  have : IsProbabilityMeasure (unifIco 1) := isProbabilityMeasure_unifIco one_pos
  refine ae_eq_condExp_of_forall_setIntegral_eq (cappedSquareSigma_le m)
    (integrable_toReal_of_lintegral_ne_top hG0.aemeasurable hfin)
    (fun s _ _ => (integrable_toReal_of_lintegral_ne_top hK.aemeasurable hKfin).integrableOn)
    (fun s hs _ => ?_) hKm.ennreal_toReal.stronglyMeasurable.aestronglyMeasurable
  rw [integral_toReal hK.aemeasurable (ae_restrict_of_ae (ae_lt_top hK hKfin)),
    integral_toReal hG0.aemeasurable (ae_restrict_of_ae (ae_lt_top hG0 hfin)),
    setLIntegral_kernelAverage_origin hMT hm0 hmtop hG hinv hs]

end CondExp

end LatticeProb.CellConfigCappedSquare
