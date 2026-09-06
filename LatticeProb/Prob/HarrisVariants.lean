/-
Adapted from https://github.com/anthropics/formal-math, percolation subdirectory,
commit 795efb86, file percolation/Percolation/Literature/LocallyMonotoneFKG.lean,
used under the Apache License 2.0.  Only the general product-measure section is
taken; namespaces have been changed to `LatticeProb`.  The statements are
unchanged.

Three consequences of `LatticeProb.infinitePi_harris`: the same inequality for
decreasing events, the reverse inequality for one increasing and one decreasing
event, and the independence of two events that depend on disjoint sets of
coordinates.  The last of these is the locally monotone form: an event which is
increasing in one block of coordinates and decreasing in another is still
positively correlated with a product of events in the two blocks.
-/
import Mathlib.Probability.ConditionalProbability
import LatticeProb.Prob.Harris

namespace LatticeProb

open MeasureTheory Measure ProbabilityTheory Set

section Product

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

/-! ### Harris' inequality for decreasing events -/

/-- **Harris' inequality for two decreasing events** (Grimmett 1999, Thm. (2.4)(b) applied to
the complements): under a product probability measure on a product of linearly ordered spaces,
decreasing measurable events are positively correlated, `μ∞ A * μ∞ B ≤ μ∞ (A ∩ B)`. [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem infinitePi_harris_lower [∀ i, LinearOrder (X i)] {A B : Set (Π i, X i)}
    (hA : IsLowerSet A) (hB : IsLowerSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (infinitePi μ).real A * (infinitePi μ).real B ≤ (infinitePi μ).real (A ∩ B) := by
  have h := infinitePi_harris μ hA.compl hB.compl hAm.compl hBm.compl
  rw [← Set.compl_union, measureReal_compl hAm, measureReal_compl hBm,
    measureReal_compl (hAm.union hBm), probReal_univ] at h
  have hu := measureReal_union_add_inter hBm (μ := infinitePi μ) (s := A)
  have e : (1 - (infinitePi μ).real A) * (1 - (infinitePi μ).real B) =
      1 - (infinitePi μ).real A - (infinitePi μ).real B +
        (infinitePi μ).real A * (infinitePi μ).real B := by ring
  linarith

/-- **Harris' inequality for an increasing and a decreasing event** (Grimmett 1999,
Thm. (2.4)(b) applied to `A` and `Bᶜ`): they are negatively correlated,
`μ∞ (A ∩ B) ≤ μ∞ A * μ∞ B`. [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem infinitePi_harris_upper_lower [∀ i, LinearOrder (X i)] {A B : Set (Π i, X i)}
    (hA : IsUpperSet A) (hB : IsLowerSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (infinitePi μ).real (A ∩ B) ≤ (infinitePi μ).real A * (infinitePi μ).real B := by
  have h := infinitePi_harris μ hA hB.compl hAm hBm.compl
  rw [measureReal_compl hBm, probReal_univ] at h
  have hs : (infinitePi μ).real (A ∩ Bᶜ) + (infinitePi μ).real (A ∩ B) =
      (infinitePi μ).real A := by
    rw [← Set.sdiff_eq, add_comm]
    exact measureReal_inter_add_sdiff hBm
  linarith

/-! ### Independence of events depending on disjoint sets of coordinates -/

/-- Under a product measure, an event depending only on the coordinates in a finite set `s` and an
event depending only on the coordinates outside `s` are independent:
`μ∞ (A ∩ B) = μ∞ A * μ∞ B`. (Grimmett 1999, §2.2; the gluing map `(ω, η) ↦ s.piecewise ω η`
transports `μ∞ ⊗ μ∞` to `μ∞` and pulls `A ∩ B` back to `A ×ˢ B`.) [cite: GrimmettPercolation1999, §2.2] -/
theorem infinitePi_real_inter_of_dependsOn [DecidableEq ι] (s : Finset ι) {A B : Set (Π i, X i)}
    (hA : DependsOn (· ∈ A) ↑s) (hB : DependsOn (· ∈ B) (↑s)ᶜ) (hAm : MeasurableSet A)
    (hBm : MeasurableSet B) :
    (infinitePi μ).real (A ∩ B) = (infinitePi μ).real A * (infinitePi μ).real B := by
  have hpre : (fun p : (Π i, X i) × (Π i, X i) => s.piecewise p.1 p.2) ⁻¹' (A ∩ B) = A ×ˢ B := by
    ext p
    have h1 : (s.piecewise p.1 p.2 ∈ A) = (p.1 ∈ A) :=
      hA fun i hi => Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_coe.1 hi)
    have h2 : (s.piecewise p.1 p.2 ∈ B) = (p.2 ∈ B) :=
      hB fun i hi => Finset.piecewise_eq_of_notMem _ _ _ fun h => hi (Finset.mem_coe.2 h)
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod]
    rw [h1, h2]
  have h : ((infinitePi μ).prod (infinitePi μ)).map (fun p => s.piecewise p.1 p.2) (A ∩ B) =
      infinitePi μ (A ∩ B) := by
    rw [infinitePi_prod_map_piecewise]
  rw [Measure.map_apply (measurable_finsetPiecewise s) (hAm.inter hBm), hpre,
    Measure.prod_prod] at h
  simp only [measureReal_def, ← h, ENNReal.toReal_mul]

/-- Variant of `infinitePi_real_inter_of_dependsOn` for two disjoint finite sets of
coordinates. [cite: GrimmettPercolation1999, §2.2] -/
theorem infinitePi_real_inter_of_dependsOn_disjoint {s t : Finset ι} (hst : Disjoint s t)
    {A B : Set (Π i, X i)} (hA : DependsOn (· ∈ A) ↑s) (hB : DependsOn (· ∈ B) ↑t)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (infinitePi μ).real (A ∩ B) = (infinitePi μ).real A * (infinitePi μ).real B := by
  classical
  refine infinitePi_real_inter_of_dependsOn μ s hA (hB.mono fun i hi his => ?_) hAm hBm
  exact Finset.disjoint_left.1 hst (Finset.mem_coe.1 his) (Finset.mem_coe.1 hi)

/-! ### Sections along the gluing map -/

/-- Fubini for the gluing map, event form: `μ∞ E = ∫ μ∞ {η | s.piecewise ω η ∈ E} dμ∞(ω)`.
[cite: GrimmettPercolation1999, Thm. 2.4 (proof, (2.9))] -/
theorem infinitePi_real_eq_integral_piecewise [DecidableEq ι] (s : Finset ι) {E : Set (Π i, X i)}
    (hE : MeasurableSet E) :
    (infinitePi μ).real E =
      ∫ ω, (infinitePi μ).real ((fun η => s.piecewise ω η) ⁻¹' E) ∂infinitePi μ := by
  have hint : Integrable (E.indicator (1 : (Π i, X i) → ℝ)) (infinitePi μ) :=
    (integrable_const 1).indicator hE
  rw [← integral_indicator_one hE, ← integral_integral_piecewise μ (s := s) hint]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only
  rw [← integral_indicator_one ((measurable_finsetPiecewise_right s ω) hE)]
  rfl

/-! ### Nolin's generalised FKG inequality -/

/-- **Generalised FKG inequality for locally monotone events** (Nolin 2008, §4.3, EJP Lemma 13 =
arXiv Lemma 12): "Consider `A⁺, Ã⁺` two increasing events, and `A⁻, Ã⁻` two decreasing
events. Assume that there exist three disjoint finite sets of vertices `𝒜, 𝒜⁺` and `𝒜⁻` such
that `A⁺, A⁻, Ã⁺` and `Ã⁻` depend only on the sites in, respectively, `𝒜 ∪ 𝒜⁺`, `𝒜 ∪ 𝒜⁻`,
`𝒜⁺` and `𝒜⁻`. Then we have `P(Ã⁺ ∩ Ã⁻ | A⁺ ∩ A⁻) ≥ P(Ã⁺) P(Ã⁻)` for any product measure
`P`." Product form (no positivity proviso): `P(A⁺ ∩ A⁻) P(Ã⁺) P(Ã⁻) ≤ P((A⁺ ∩ A⁻) ∩ (Ã⁺ ∩ Ã⁻))`,
for the product `μ∞` of arbitrary probability measures on linearly ordered measurable spaces
(here `S = 𝒜`, `P = 𝒜⁺`, `M = 𝒜⁻`, `Ap = A⁺`, `Am = A⁻`, `Bp = Ã⁺`, `Bm = Ã⁻`). [cite: Nolin2008, §4.3, Lemma 13 (arXiv 0711.4948: Lemma 12)] -/
theorem infinitePi_locallyMonotone_fkg [∀ i, LinearOrder (X i)] {S P M : Finset ι}
    (hSP : Disjoint S P) (hSM : Disjoint S M) (hPM : Disjoint P M)
    {Ap Am Bp Bm : Set (Π i, X i)}
    (hAp : IsUpperSet Ap) (hAm : IsLowerSet Am) (hBp : IsUpperSet Bp) (hBm : IsLowerSet Bm)
    (mAp : MeasurableSet Ap) (mAm : MeasurableSet Am) (mBp : MeasurableSet Bp)
    (mBm : MeasurableSet Bm)
    (dAp : DependsOn (· ∈ Ap) (↑S ∪ ↑P)) (dAm : DependsOn (· ∈ Am) (↑S ∪ ↑M))
    (dBp : DependsOn (· ∈ Bp) ↑P) (dBm : DependsOn (· ∈ Bm) ↑M) :
    (infinitePi μ).real (Ap ∩ Am) * ((infinitePi μ).real Bp * (infinitePi μ).real Bm) ≤
      (infinitePi μ).real (Ap ∩ Am ∩ (Bp ∩ Bm)) := by
  classical
  -- notation: `Φ ω = S.piecewise ω ·` glues `ω` on `S` to an independent sample off `S`
  have mΦ : ∀ ω : Π i, X i, Measurable fun η => S.piecewise ω η :=
    fun ω => measurable_finsetPiecewise_right S ω
  -- coordinates of `P` and `M` lie outside `S`
  have hPS : ∀ {i}, i ∈ P → i ∉ S := fun hi h => Finset.disjoint_left.1 hSP h hi
  have hMS : ∀ {i}, i ∈ M → i ∉ S := fun hi h => Finset.disjoint_left.1 hSM h hi
  -- the `B`-events do not see the glued coordinates
  have ΦBp : ∀ ω η : Π i, X i, (S.piecewise ω η ∈ Bp) = (η ∈ Bp) := fun ω η =>
    dBp fun i hi => Finset.piecewise_eq_of_notMem _ _ _ (hPS (Finset.mem_coe.1 hi))
  have ΦBm : ∀ ω η : Π i, X i, (S.piecewise ω η ∈ Bm) = (η ∈ Bm) := fun ω η =>
    dBm fun i hi => Finset.piecewise_eq_of_notMem _ _ _ (hMS (Finset.mem_coe.1 hi))
  -- sections of the `A`-events: monotone, measurable, depending on `P` (resp. `M`) only
  set secP : (Π i, X i) → Set (Π i, X i) := fun ω => {η | S.piecewise ω η ∈ Ap} with hsecP
  set secM : (Π i, X i) → Set (Π i, X i) := fun ω => {η | S.piecewise ω η ∈ Am} with hsecM
  have secP_upper : ∀ ω, IsUpperSet (secP ω) := fun ω η η' hle hη =>
    hAp (Finset.piecewise_le_piecewise S le_rfl hle) hη
  have secM_lower : ∀ ω, IsLowerSet (secM ω) := fun ω η η' hle hη =>
    hAm (Finset.piecewise_le_piecewise S le_rfl hle) hη
  have secP_meas : ∀ ω, MeasurableSet (secP ω) := fun ω => (mΦ ω) mAp
  have secM_meas : ∀ ω, MeasurableSet (secM ω) := fun ω => (mΦ ω) mAm
  have agree : ∀ (T : Finset ι) (ω η η' : Π i, X i), (∀ i ∈ (↑T : Set ι), η i = η' i) →
      ∀ i ∈ (↑S ∪ ↑T : Set ι), S.piecewise ω η i = S.piecewise ω η' i := by
    intro T ω η η' h i hi
    by_cases hiS : i ∈ S
    · simp only [Finset.piecewise_eq_of_mem _ _ _ hiS]
    · simp only [Finset.piecewise_eq_of_notMem _ _ _ hiS]
      rcases hi with hi | hi
      · exact absurd (Finset.mem_coe.1 hi) hiS
      · exact h i hi
  have secP_dep : ∀ ω, DependsOn (· ∈ secP ω) ↑P := fun ω η η' h =>
    show (S.piecewise ω η ∈ Ap) = (S.piecewise ω η' ∈ Ap) from dAp (agree P ω η η' h)
  have secM_dep : ∀ ω, DependsOn (· ∈ secM ω) ↑M := fun ω η η' h =>
    show (S.piecewise ω η ∈ Am) = (S.piecewise ω η' ∈ Am) from dAm (agree M ω η η' h)
  have inter_dep : ∀ {C D : Set (Π i, X i)} {T : Set ι}, DependsOn (· ∈ C) T →
      DependsOn (· ∈ D) T → DependsOn (· ∈ C ∩ D) T := by
    intro C D T hC hD η η' h
    exact congrArg₂ (· ∧ ·) (hC h) (hD h)
  -- the pointwise (conditional) inequality
  have key : ∀ ω, (infinitePi μ).real ((fun η => S.piecewise ω η) ⁻¹' (Ap ∩ Am)) *
      ((infinitePi μ).real Bp * (infinitePi μ).real Bm) ≤
      (infinitePi μ).real ((fun η => S.piecewise ω η) ⁻¹' (Ap ∩ Am ∩ (Bp ∩ Bm))) := by
    intro ω
    have e1 : (fun η => S.piecewise ω η) ⁻¹' (Ap ∩ Am ∩ (Bp ∩ Bm)) =
        (secP ω ∩ Bp) ∩ (secM ω ∩ Bm) := by
      ext η
      simp only [Set.mem_preimage, Set.mem_inter_iff, hsecP, hsecM, Set.mem_setOf_eq]
      rw [ΦBp, ΦBm]
      tauto
    have e2 : (fun η => S.piecewise ω η) ⁻¹' (Ap ∩ Am) = secP ω ∩ secM ω := by
      ext η
      simp only [Set.mem_preimage, Set.mem_inter_iff, hsecP, hsecM, Set.mem_setOf_eq]
    rw [e1, e2,
      infinitePi_real_inter_of_dependsOn_disjoint μ hPM (inter_dep (secP_dep ω) dBp)
        (inter_dep (secM_dep ω) dBm) ((secP_meas ω).inter mBp) ((secM_meas ω).inter mBm),
      infinitePi_real_inter_of_dependsOn_disjoint μ hPM (secP_dep ω) (secM_dep ω) (secP_meas ω)
        (secM_meas ω)]
    have hP := infinitePi_harris μ (secP_upper ω) hBp (secP_meas ω) mBp
    have hM := infinitePi_harris_lower μ (secM_lower ω) hBm (secM_meas ω) mBm
    calc (infinitePi μ).real (secP ω) * (infinitePi μ).real (secM ω) *
          ((infinitePi μ).real Bp * (infinitePi μ).real Bm)
        = ((infinitePi μ).real (secP ω) * (infinitePi μ).real Bp) *
            ((infinitePi μ).real (secM ω) * (infinitePi μ).real Bm) := by ring
      _ ≤ (infinitePi μ).real (secP ω ∩ Bp) * (infinitePi μ).real (secM ω ∩ Bm) :=
          mul_le_mul hP hM (mul_nonneg measureReal_nonneg measureReal_nonneg) measureReal_nonneg
  -- integrate over `ω`
  have mD : MeasurableSet (Ap ∩ Am) := mAp.inter mAm
  have mE : MeasurableSet (Ap ∩ Am ∩ (Bp ∩ Bm)) := mD.inter (mBp.inter mBm)
  rw [infinitePi_real_eq_integral_piecewise μ S mD, infinitePi_real_eq_integral_piecewise μ S mE,
    ← integral_mul_const]
  have hmeasI : ∀ {E : Set (Π i, X i)}, MeasurableSet E →
      Measurable fun ω : Π i, X i => (infinitePi μ).real ((fun η => S.piecewise ω η) ⁻¹' E) := by
    intro E hE
    have heq : (fun ω : Π i, X i => (infinitePi μ).real ((fun η => S.piecewise ω η) ⁻¹' E)) =
        fun ω => ∫ η, E.indicator (1 : (Π i, X i) → ℝ) (S.piecewise ω η) ∂infinitePi μ := by
      funext ω
      rw [← integral_indicator_one ((mΦ ω) hE)]
      rfl
    rw [heq]
    exact measurable_integral_piecewise μ (measurable_const.indicator hE)
  have hbdI : ∀ (E : Set (Π i, X i)) (ω : Π i, X i),
      ‖(infinitePi μ).real ((fun η => S.piecewise ω η) ⁻¹' E)‖ ≤ 1 := fun E ω => by
    rw [Real.norm_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  refine integral_mono ?_ ?_ key
  · refine Integrable.of_bound ((hmeasI mD).mul_const _).aestronglyMeasurable (1 * 1)
      (ae_of_all _ fun ω => ?_)
    rw [norm_mul]
    refine mul_le_mul (hbdI _ ω) ?_ (norm_nonneg _) zero_le_one
    rw [Real.norm_of_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)]
    exact mul_le_one₀ measureReal_le_one measureReal_nonneg measureReal_le_one
  · exact .of_bound (hmeasI mE).aestronglyMeasurable 1 (ae_of_all _ (hbdI _))

end Product

end LatticeProb
