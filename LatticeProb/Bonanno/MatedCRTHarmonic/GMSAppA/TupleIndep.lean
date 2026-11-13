/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.TupleIndep at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.FieldData

/-!
# Independence bookkeeping for `N`-tuples of independent fields

For [18] Lemma A.3 with `N` independent whole-plane GFFs :

* `GMSAppA.indep_iSup_iSup_of_iIndep` — if the σ-algebras `𝒜_k` are independent and `B_k, D_k ≤ 𝒜_k` with `B_k`
  independent of `D_k` for each `k`, then `⨆ B_k` is independent of `⨆ D_k`;
* `GMSAppA.indep_comap_congr` — independence of `𝒢` from `σ(f)` passes to an a.e.-equal `f'`;
* `GMSAppA.IsZeroBoundaryGFF.congr_ae` — the zero-boundary GFF property passes to an a.e.-equal measurable version;
* `GMSAppA.exists_diskMarkov_meas` — a Markov decomposition whose zero-boundary part is `h − G`, hence
  `σ(h)`-measurable (so that all the data of one field are `σ(h)`-measurable).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric LQGMetric.GM LQGMetric.Blueprint
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

section Sups

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- the π-system of full intersections `⋂_k b_k`, `b_k ∈ B_k` -/
def fullInter (B : ι → MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ b : ι → Set Ω, (∀ k, MeasurableSet[B k] (b k)) ∧ s = ⋂ k, b k}

lemma isPiSystem_fullInter (B : ι → MeasurableSpace Ω) : IsPiSystem (fullInter B) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩ -
  exact ⟨fun k => b k ∩ b' k, fun k => (hb k).inter (hb' k), (iInter_inter_distrib _ _).symm⟩

lemma generateFrom_fullInter [Fintype ι] [DecidableEq ι] (B : ι → MeasurableSpace Ω) :
    MeasurableSpace.generateFrom (fullInter B) = ⨆ k, B k := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (iSup_le fun k => ?_)
  · rintro _ ⟨b, hb, rfl⟩
    exact MeasurableSet.iInter fun k => (le_iSup B k) _ (hb k)
  · intro s hs
    refine MeasurableSpace.measurableSet_generateFrom ⟨fun j => if j = k then s else univ, ?_, ?_⟩
    · intro j
      by_cases hj : j = k
      · subst hj; simpa using hs
      · simp [hj]
    · ext x
      simp only [mem_iInter]
      constructor
      · intro hx j; by_cases hj : j = k <;> simp [hj, hx]
      · intro hx; simpa using hx k

/-- **Independence of the suprema of independent pairs**. -/
theorem indep_iSup_iSup_of_iIndep [Fintype ι] [IsProbabilityMeasure P] {𝒜 B D : ι → MeasurableSpace Ω} (h𝒜 : iIndep 𝒜 P)
    (hB : ∀ k, B k ≤ 𝒜 k) (hD : ∀ k, D k ≤ 𝒜 k) (h𝒜le : ∀ k, 𝒜 k ≤ m0)
    (hBD : ∀ k, Indep (B k) (D k) P) : Indep (⨆ k, B k) (⨆ k, D k) P := by
  classical
  rw [← generateFrom_fullInter B, ← generateFrom_fullInter D]
  refine IndepSets.indep (generateFrom_fullInter B ▸ iSup_le fun k => (hB k).trans (h𝒜le k))
    (generateFrom_fullInter D ▸ iSup_le fun k => (hD k).trans (h𝒜le k))
    (isPiSystem_fullInter B) (isPiSystem_fullInter D) rfl rfl ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨b, hb, rfl⟩ ⟨d, hd, rfl⟩
  have hbd : ∀ k, P (b k ∩ d k) = P (b k) * P (d k) := fun k =>
    (Indep_iff _ _ P).1 (hBD k) _ _ (hb k) (hd k)
  rw [← iInter_inter_distrib, h𝒜.meas_iInter fun k => ((hB k) _ (hb k)).inter ((hD k) _ (hd k)),
    h𝒜.meas_iInter fun k => (hB k) _ (hb k), h𝒜.meas_iInter fun k => (hD k) _ (hd k)]
  simp_rw [hbd]
  exact Finset.prod_mul_distrib

end Sups

/-- Independence of `𝒢` from `σ(f)` passes to an a.e.-equal `f'`. -/
theorem indep_comap_congr {Ω β : Type*} {m0 : MeasurableSpace Ω} [MeasurableSpace β]
    {P : Measure Ω} {𝒢 : MeasurableSpace Ω} {f f' : Ω → β} (hff : f =ᵐ[P] f')
    (h : Indep 𝒢 (MeasurableSpace.comap f inferInstance) P) :
    Indep 𝒢 (MeasurableSpace.comap f' inferInstance) P := by
  rw [Indep_iff] at h ⊢
  intro s t hs ht
  obtain ⟨B, hB, rfl⟩ := ht
  have heq : f' ⁻¹' B =ᵐ[P] f ⁻¹' B := by
    filter_upwards [hff] with ω hω
    simp only [mem_preimage, hω]
  have h1 : s ∩ f' ⁻¹' B =ᵐ[P] s ∩ f ⁻¹' B :=
    Filter.EventuallyEqSet.inter (EventuallyEq.refl _ s) heq
  rw [measure_congr h1, measure_congr heq]
  exact h s _ hs ⟨B, hB, rfl⟩

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- The zero-boundary GFF property passes to an a.e.-equal measurable version. -/
theorem IsZeroBoundaryGFF.congr_ae {U : TopologicalSpace.Opens ℂ} {g g' : Ω → DistOn U}
    (hg : IsZeroBoundaryGFF U g P) (hg' : Measurable g') (hgg : g =ᵐ[P] g') :
    IsZeroBoundaryGFF U g' P := by
  have hpair : ∀ φ : TestOn U, (fun ω => g ω φ) =ᵐ[P] fun ω => g' ω φ := fun φ => by
    filter_upwards [hgg] with ω hω; rw [hω]
  refine ⟨hg', ⟨fun φ => (measurable_distOn_apply φ).comp hg', ?_, fun φ => ?_, fun φ ψ => ?_⟩⟩
  · exact hg.process.gaussian.congr fun φ => hpair φ
  · rw [← integral_congr_ae (hpair φ)]; exact hg.process.centered φ
  · rw [← LQGMetric.MarkovNorm.cov_congr_ae (hpair φ) (hpair ψ)]
    exact hg.process.covariance_eq φ ψ

omit [MeasurableSpace Ω] in
/-- `σ(h|_{ℂ∖𝔻}) ≤ σ(h)` -/
lemma extSigma_le_comap (h : Ω → DistC) : extSigma h ≤ MeasurableSpace.comap h inferInstance := by
  unfold extSigma fieldSigmaClosed
  refine (iInf₂_le (1 : ℝ) one_pos).trans ?_
  show MeasurableSpace.comap (restrictTo _ ∘ h) inferInstance ≤ _
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_restrictTo _).comap_le

/-- **A Markov decomposition with `σ(h)`-measurable zero-boundary part** `h̊ = h − G`. -/
theorem exists_diskMarkov_meas [IsProbabilityMeasure P] (hh : IsWholePlaneGFF h P)
    {r : ℝ} {w : ℂ} (hr : 0 < r) (hn : ∀ᵐ ω ∂P, circleAvg (h ω) r w = 0)
    (hV : Disjoint (ball (0 : ℂ) 1) (sphere w r)) :
    ∃ M : DiskMarkov P h, Measurable[MeasurableSpace.comap h inferInstance] M.hz := by
  obtain ⟨M⟩ := exists_diskMarkov hh hr hn hV
  have hGm : Measurable[MeasurableSpace.comap h inferInstance] M.G :=
    M.G_meas.mono (extSigma_le_comap h) le_rfl
  have hhm : Measurable[MeasurableSpace.comap h inferInstance] h := comap_measurable h
  have hsub : Measurable[MeasurableSpace.comap h inferInstance] fun ω => h ω - M.G ω :=
    GFFInv.measurable_distC_iff.2 fun φ => ((GFFInv.measurable_pair φ).comp hhm).sub
      ((GFFInv.measurable_pair φ).comp hGm)
  have hsub' : Measurable fun ω => h ω - M.G ω := hsub.mono hh.measurable.comap_le le_rfl
  have hae : M.hz =ᵐ[P] fun ω => h ω - M.G ω := by
    filter_upwards [M.dec] with ω hω
    rw [hω, add_sub_cancel_left]
  refine ⟨⟨M.G, fun ω => h ω - M.G ω, M.G_meas, ae_of_all _ fun ω => (add_sub_cancel _ _).symm,
    M.harm, ?_, ?_⟩, hsub⟩
  · refine IsZeroBoundaryGFF.congr_ae M.zb ((measurable_restrictTo _).comp hsub') ?_
    filter_upwards [hae] with ω hω
    rw [hω]
  · exact (indep_comap_congr hae M.indep.symm).symm

namespace DiskMarkov

lemma measurable_Ed_comap {M : DiskMarkov P h} :
    Measurable[MeasurableSpace.comap h inferInstance] M.Ed :=
  M.measurable_Ed_ext.mono (extSigma_le_comap h) le_rfl

lemma measurable_cAvg_comap : Measurable[MeasurableSpace.comap h inferInstance] (cAvg h) :=
  (measurable_cAvg_ext h).mono (extSigma_le_comap h) le_rfl

lemma measurable_Zd_comap {M : DiskMarkov P h}
    (hM : Measurable[MeasurableSpace.comap h inferInstance] M.hz) :
    Measurable[MeasurableSpace.comap h inferInstance] M.Zd :=
  (measurable_restrictTo _).comp hM

end DiskMarkov

end MatedCRTHarmonic.GMSAppA
