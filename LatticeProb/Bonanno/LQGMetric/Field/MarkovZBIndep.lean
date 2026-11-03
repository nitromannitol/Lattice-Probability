/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovZBIndep at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGerm

/-!
# The zero-boundary part is independent of the germ `σ(h|_{ℂ∖U})` (task P2-MARKOV, part 5)

For a whole-plane GFF `h` normalized by `h_1(0) = 0` and an open set `U` disjoint from `∂𝔻`, the
projection `zbProc` of `h` onto `H₀¹(U)` (a zero-boundary GFF on `U`, `isZBGFFProcess_zbProc`) is
independent of the germ σ-algebra

  `σ(h|_{ℂ∖U}) = ⋂_{ε>0} σ(h|_{B_ε(ℂ∖U)})` (`Blueprint.fieldSigmaClosed`, LM l. 164 footnote).

(`indep_zbProc_fieldSigmaClosed`). This is the independence half of LM Lemma 2.1 (`V ∩ ∂𝔻 = ∅`
case; GMSh arXiv:1807.07511 Lemma 2.2; Miller–Sheffield IG4 arXiv:1302.4738 Prop. 2.8;
Berestycki–Powell arXiv:2404.16642 Thm 1.52). Proof: `zbVec φ` is the `L²` limit of Dirichlet
pairings `(h, fₖ)_∇`, `fₖ ∈ C_c^∞(U)`; for each `k` the supports of the `fₖ` stay at a positive
distance `ε` from `ℂ ∖ U`, so `(h, fₖ)_∇` is orthogonal to every mean-zero pairing supported in
`B_ε(ℂ∖U)` and hence independent of `σ(h|_{B_ε(ℂ∖U)}) ⊇` germ (`indep_fieldSigma_of_orth`);
independence passes to the limit in probability (`indep_comap_of_tendstoInMeasure`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovZBIndep

open MarkovGauss MarkovIndep MarkovZB MarkovGerm Blueprint QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

omit [IsProbabilityMeasure P] in
lemma comap_pi_eq_iSup {T : Type*} (Y : T → Ω → ℝ) :
    MeasurableSpace.comap (fun ω t => Y t ω) MeasurableSpace.pi =
      ⨆ I : Finset T, MeasurableSpace.comap (fun ω (t : I) => Y t ω) inferInstance := by
  refine le_antisymm ?_ (iSup_le fun I => ?_)
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun t => ?_
    rw [MeasurableSpace.comap_comp]
    have : (fun ω => Y t ω) = (fun v : ({t} : Finset T) → ℝ =>
        v ⟨t, Finset.mem_singleton_self t⟩) ∘ fun ω (s : ({t} : Finset T)) => Y s ω := rfl
    refine le_trans ?_ (le_iSup (fun I : Finset T =>
      MeasurableSpace.comap (fun ω (t : I) => Y t ω) inferInstance) {t})
    change MeasurableSpace.comap (fun ω => Y t ω) _ ≤ _
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  · have : (fun ω (t : I) => Y t ω) = (fun (v : T → ℝ) (t : I) => v t) ∘ fun ω t => Y t ω := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_iff.2 fun t => measurable_pi_apply _).comap_le

omit [IsProbabilityMeasure P] in
lemma fieldSigmaClosed_le (hh : IsWholePlaneGFF h P) (K : Set ℂ) :
    fieldSigmaClosed h K ≤ ‹MeasurableSpace Ω› := by
  refine (iInf₂_le (1 : ℝ) one_pos).trans ?_
  refine Measurable.comap_le ?_
  have h2 : Measurable fun g : DistC => restrictTo (nbhdO 1 K) g := by
    refine Measurable.of_comap_le ?_
    rw [DistOn.measurableSpace, MeasurableSpace.comap_comp]
    exact (measurable_pi_iff.2 fun φ => measurable_evalDist _).comap_le
  exact h2.comp hh.measurable

/-- compact sets inside `U` avoid a thickening of `ℂ ∖ U` -/
lemma exists_thickening_disjoint {U : Opens ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∃ ε > 0, Disjoint K (thickening ε (U : Set ℂ)ᶜ) := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open U.isOpen hKU
  refine ⟨δ, hδ, Set.disjoint_left.2 fun x hx hx' => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx'
  exact hy (hsub (mem_cthickening_of_dist_le y x δ K hx (by rw [dist_comm]; exact hxy.le)))

/-- one approximant: the Dirichlet pairings of finitely many `f ∈ C_c^∞(U)` are independent of
the germ of `h` on `ℂ ∖ U` -/
theorem indep_cmLin_fieldSigmaClosed (hh : IsNormalizedWPGFF h P) {U : Opens ℂ}
    (hU : Disjoint (U : Set ℂ) (sphere 0 1)) {S : Type*} [Fintype S] (f : S → zsSub U) :
    Indep (MeasurableSpace.comap (fun ω s => pairProc h (cmTest0 (zsTest (f s).2)) ω)
      inferInstance) (fieldSigmaClosed h (U : Set ℂ)ᶜ) P := by
  have hK : IsCompact (⋃ s, tsupport ((f s : ℂ → ℝ))) := isCompact_iUnion fun s => (f s).2.2.1
  obtain ⟨ε, hε, hdisj⟩ := exists_thickening_disjoint hK
    (iUnion_subset fun s => (f s).2.2.2)
  have hO : sphere (0 : ℂ) 1 ⊆ nbhdO ε (U : Set ℂ)ᶜ := fun x hx =>
    self_subset_thickening hε _ (fun hxU => Set.disjoint_left.1 hU hxU hx)
  have hind := indep_fieldSigma_of_orth hh (nbhdO ε (U : Set ℂ)ᶜ) hO
    (fun s => cmLin hh.1 U (f s)) (fun s => toLp_mem_gaussSpace (memLp_pair hh.1) _)
    (fun s χ hχ => ?_) (Wm := fun ω s => pairProc h (cmTest0 (zsTest (f s).2)) ω)
    (measurable_pi_iff.2 fun s => measurable_eval hh.1 _)
    (fun s => ((memLp_pair hh.1 _).coeFn_toLp).symm)
  · exact indep_of_indep_of_le_right hind.symm (iInf₂_le ε hε) |>.symm.symm
  · rw [← cmIso_gradLin, inner_cmIso_gradLin]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : (f s : ℂ → ℝ) x = 0
    · simp [hx]
    · have hxK : x ∈ ⋃ s, tsupport ((f s : ℂ → ℝ)) :=
        mem_iUnion.2 ⟨s, subset_tsupport _ hx⟩
      have : χ.1 x = 0 := image_eq_zero_of_notMem_tsupport fun h' =>
        Set.disjoint_left.1 hdisj hxK (hχ h')
      simp [this]

omit [IsProbabilityMeasure P] in
lemma comap_finset_mono {T : Type*} (Y : T → Ω → ℝ) {I₁ I₂ : Finset T} (hI : I₁ ⊆ I₂) :
    MeasurableSpace.comap (fun ω (t : I₁) => Y t ω) inferInstance ≤
      MeasurableSpace.comap (fun ω (t : I₂) => Y t ω) inferInstance := by
  have : (fun ω (t : I₁) => Y t ω) =
      (fun (v : I₂ → ℝ) (t : I₁) => v ⟨t, hI t.2⟩) ∘ fun ω (t : I₂) => Y t ω := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_iff.2 fun t => measurable_pi_apply _).comap_le

/-- **Independence from the germ.** For any family `v` in `H₀¹(U)` and measurable versions `Zm`
of `cmIso v`, the process `Zm` is independent of the germ `σ(h|_{ℂ∖U})` (`U ∩ ∂𝔻 = ∅`). -/
theorem indep_cmIso_fieldSigmaClosed (hh : IsNormalizedWPGFF h P) {U : Opens ℂ}
    (hU : Disjoint (U : Set ℂ) (sphere 0 1)) {T : Type*}
    (v : T → gradClosure (U : Set ℂ) (zeroSpace U)) (Zm : T → Ω → ℝ)
    (hZm : ∀ t, Measurable (Zm t)) (hae : ∀ t, Zm t =ᵐ[P] cmIso hh.1 U (v t)) :
    Indep (MeasurableSpace.comap (fun ω t => Zm t ω) MeasurableSpace.pi)
      (fieldSigmaClosed h (U : Set ℂ)ᶜ) P := by
  rw [comap_pi_eq_iSup]
  refine indep_iSup_of_directed_le (fun I => ?_)
    (fun I => Measurable.comap_le (measurable_pi_iff.2 fun t => hZm _))
    (fieldSigmaClosed_le hh.1 _) ?_
  · have hseq : ∀ t : I, ∃ f : ℕ → zsSub U, Tendsto (fun k => gradLin U (f k)) atTop
        (𝓝 (v t)) := by
      intro t
      obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.1 (denseRange_gradLin U (v t))
      choose f hf using hw
      exact ⟨f, by simpa [hf] using hlim⟩
    choose f hf using hseq
    refine indep_comap_of_tendstoInMeasure
      (Zn := fun k ω (t : I) => pairProc h (cmTest0 (zsTest (f t k).2)) ω)
      (measurable_pi_iff.2 fun t => hZm _)
      (fun k => measurable_pi_iff.2 fun t => measurable_eval hh.1 _)
      (fieldSigmaClosed_le hh.1 _) (tendstoInMeasure_pi fun t => ?_)
      fun k => indep_cmLin_fieldSigmaClosed hh hU (fun t => f t k)
    have hL : Tendsto (fun k => cmLin hh.1 U (f t k)) atTop (𝓝 (cmIso hh.1 U (v t))) := by
      have := ((cmIso hh.1 U).continuous.tendsto _).comp (hf t)
      simp only [Function.comp_def, cmIso_gradLin] at this
      exact this
    exact ((tendstoInMeasure_of_tendsto_Lp hL).congr_left fun k =>
      (memLp_pair hh.1 _).coeFn_toLp).congr_right (hae t).symm
  · intro I₁ I₂
    classical
    exact ⟨I₁ ∪ I₂, comap_finset_mono _ Finset.subset_union_left,
      comap_finset_mono _ Finset.subset_union_right⟩

end MarkovZBIndep
end LQGMetric
