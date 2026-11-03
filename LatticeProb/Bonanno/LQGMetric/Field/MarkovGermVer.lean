/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovNorm
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc

/-!
# Germ measurability of the harmonic part: the Hilbert-space reduction (task P2-MKD, part 1)

Leaf (D) of `handoff/P2-MARKOV.md`: the harmonic part `𝔥(φ) = ⟨h, φ⟩ − ⟨h̊, φ 1_V⟩` of a
normalized whole-plane GFF is determined by the germ `σ(h|_{ℂ∖V}) = ⋂_ε σ(h|_{B_ε(ℂ∖V)})`.

* `germSpan hh O`: the closed span `S(O)` of the mean-zero pairings `[⟨h, χ⟩]`,
  `χ ∈ 𝓓₀(ℂ)`, `supp χ ⊆ O`; every element has a `σ(h|_O)`-measurable version
  (`exists_version_of_mem_germSpan`: `S(O) ⊆ L²(σ(h|_O))`, which is closed).
* `exists_germ_version_of_mem`: a variable lying in `S(B_ε(K))` for every `ε > 0` has a
  `fieldSigmaClosed h K`-measurable version (one version for the decreasing family, as in
  QuantumZipper `F1Germ.exists_iInf_version`, here for real-valued variables).
* `harm_mem_germSpan_of_orth`: if every element of the Gaussian space orthogonal to `S(O)` is a
  Dirichlet pairing on `V` (i.e. lies in the range of `cmIso hh V`, `H₀¹(V)`), then the harmonic
  part lies in `S(O)` (it is orthogonal to `H₀¹(V)` by `inner_pairVec_cmIso`).
* `exists_germ_version_harm_of_orth`: leaf (D) for bounded `V`, from that orthogonality
  statement for `O = B_ε(ℂ ∖ V)`, all `ε > 0`.

This is the Hilbert-space form of the Markov property: Sheffield, *Gaussian free fields for
mathematicians* (math/0312099), §2.6, Thm 2.17 and the paragraph after it (`F^⊥_U` is generated
by `(h, f)_∇` with `Δf` vanishing on `U`, "it allows us to measure the values of `h` outside of
`U`", tex l. 690–725); Miller–Sheffield IG4 (arXiv:1302.4738) Prop. 2.8 proof (tex l. 1120–1127);
Berestycki–Powell (arXiv:2404.16642) Thm 1.52 and Lemma 1.53 (`H₀¹(D) = Supp(U) ⊕ Harm(U)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovGermVer

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm Blueprint QuantumZipper
  QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- `S(O)`: the closed span of the mean-zero pairings `[⟨h, χ⟩]` with `supp χ ⊆ O` -/
def germSpan (hh : IsWholePlaneGFF h P) (O : Set ℂ) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ ((fun χ : TestC0 => (memLp_pair hh χ).toLp (pairProc h χ)) ''
    {χ : TestC0 | tsupport (χ.1 : ℂ → ℝ) ⊆ O})).topologicalClosure

lemma toLp_mem_germSpan (hh : IsWholePlaneGFF h P) {O : Set ℂ} (χ : TestC0)
    (hχ : tsupport (χ.1 : ℂ → ℝ) ⊆ O) : (memLp_pair hh χ).toLp (pairProc h χ) ∈ germSpan hh O :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨χ, hχ, rfl⟩)

lemma germSpan_le_gaussSpace (hh : IsWholePlaneGFF h P) (O : Set ℂ) :
    germSpan hh O ≤ gaussSpace (pairProc h) (memLp_pair hh) := by
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
    (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨χ, -, rfl⟩
  exact toLp_mem_gaussSpace (memLp_pair hh) χ

lemma germSpan_mono (hh : IsWholePlaneGFF h P) {O O' : Set ℂ} (hO : O ⊆ O') :
    germSpan hh O ≤ germSpan hh O' :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (image_mono fun _ hχ => hχ.trans hO))

omit [IsProbabilityMeasure P] in
lemma fieldSigma_le (hh : IsWholePlaneGFF h P) (O : Opens ℂ) :
    fieldSigma h O ≤ ‹MeasurableSpace Ω› := by
  refine Measurable.comap_le ?_
  have h2 : Measurable fun g : DistC => restrictTo O g := by
    refine Measurable.of_comap_le ?_
    rw [DistOn.measurableSpace, MeasurableSpace.comap_comp]
    exact (measurable_pi_iff.2 fun φ => measurable_evalDist _).comap_le
  exact h2.comp hh.measurable

/-- `S(O) ⊆ L²(σ(h|_O))` -/
theorem germSpan_le_lpMeas (hh : IsWholePlaneGFF h P) (O : Opens ℂ) :
    germSpan hh O ≤ lpMeas ℝ ℝ (fieldSigma h O) 2 P := by
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
    (isClosed_aestronglyMeasurable (fieldSigma_le hh O))
  rintro _ ⟨χ, hχ, rfl⟩
  rw [SetLike.mem_coe, mem_lpMeas_iff_aestronglyMeasurable]
  exact ⟨pairProc h χ, (GM.measurable_pair_fieldSigma h χ.1 hχ).stronglyMeasurable,
    (memLp_pair hh χ).coeFn_toLp⟩

/-- every element of `S(O)` has a `σ(h|_O)`-measurable version -/
theorem exists_version_of_mem_germSpan (hh : IsWholePlaneGFF h P) (O : Opens ℂ)
    {v : Lp ℝ 2 P} (hv : v ∈ germSpan hh O) :
    ∃ G : Ω → ℝ, Measurable[fieldSigma h O] G ∧ (v : Ω → ℝ) =ᵐ[P] G := by
  obtain ⟨g, hg, hfg⟩ := mem_lpMeas_iff_aestronglyMeasurable.1 (germSpan_le_lpMeas hh O hv)
  exact ⟨g, hg.measurable, hfg⟩

omit [IsProbabilityMeasure P] in
/-- one version for a decreasing family of σ-algebras (real-valued form of QuantumZipper
`F1Germ.exists_iInf_version`) -/
theorem exists_iInf_version_real {𝒢 : ℕ → MeasurableSpace Ω} (h𝒢 : Antitone 𝒢) {f : Ω → ℝ}
    (hloc : ∀ n, ∃ g : Ω → ℝ, Measurable[𝒢 n] g ∧ f =ᵐ[P] g) :
    ∃ g : Ω → ℝ, Measurable[⨅ n, 𝒢 n] g ∧ f =ᵐ[P] g := by
  choose G hGm hGe using hloc
  refine ⟨fun ω => limsup (fun m => G m ω) atTop, ?_, ?_⟩
  · refine measurable_iff_comap_le.2 (le_iInf fun n => ?_)
    have e : (fun ω => limsup (fun m => G m ω) atTop) =
        fun ω => limsup (fun m => G (m + n) ω) atTop := by
      funext ω; exact (limsup_nat_add (fun m => G m ω) n).symm
    rw [e]
    exact measurable_iff_comap_le.1 (Measurable.limsup (mδ := 𝒢 n) fun m =>
      (hGm (m + n)).mono (h𝒢 (Nat.le_add_left n m)) le_rfl)
  · filter_upwards [ae_all_iff.2 hGe] with ω hω
    have : (fun m => G m ω) = fun _ => f ω := funext fun m => (hω m).symm
    rw [this, limsup_const]

/-- a variable lying in `S(B_ε(K))` for every `ε > 0` is `σ(h|_K)`-measurable up to a null set -/
theorem exists_germ_version_of_mem (hh : IsWholePlaneGFF h P) (K : Set ℂ) {f : Ω → ℝ}
    (hloc : ∀ ε > 0, ∃ v ∈ germSpan hh (nbhdO ε K), f =ᵐ[P] (v : Ω → ℝ)) :
    ∃ G : Ω → ℝ, Measurable[fieldSigmaClosed h K] G ∧ f =ᵐ[P] G := by
  set r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hr
  have hr0 : ∀ n, 0 < r n := fun n => Nat.one_div_pos_of_nat
  have hanti : Antitone fun n => fieldSigma h (nbhdO (r n) K) := fun m n hmn =>
    GM.fieldSigma_mono h (thickening_mono (Nat.one_div_le_one_div hmn) K)
  obtain ⟨g, hg, hfg⟩ := exists_iInf_version_real (P := P) hanti fun n => by
    obtain ⟨v, hv, hfv⟩ := hloc (r n) (hr0 n)
    obtain ⟨G, hG, hvG⟩ := exists_version_of_mem_germSpan hh _ hv
    exact ⟨G, hG, hfv.trans hvG⟩
  refine ⟨g, hg.mono (le_iInf₂ fun ε hε => ?_) le_rfl, hfg⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact iInf_le_of_le n (GM.fieldSigma_mono h (thickening_mono hn.le K))

/-- **The harmonic part lies in `S(O)`** as soon as the part of the Gaussian space orthogonal to
`S(O)` consists of Dirichlet pairings on `V` (bounded `V`, `V ∩ ∂𝔻 = ∅`). -/
theorem harm_mem_germSpan_of_orth (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) (hVb : Bornology.IsBounded (V : Set ℂ))
    {O : Set ℂ}
    (horth : ∀ w ∈ gaussSpace (pairProc h) (memLp_pair hh.1),
      (∀ u ∈ germSpan hh.1 O, ⟪u, w⟫ = 0) → w ∈ Set.range (cmIso hh.1 V))
    (φ : TestC) :
    pairVec hh φ - extVec hh.1 V ((V : Set ℂ).indicator φ) ∈ germSpan hh.1 O := by
  set S := germSpan hh.1 O
  have : CompleteSpace S := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set X := pairVec hh φ - extVec hh.1 V ((V : Set ℂ).indicator φ)
  have hX : X ∈ gaussSpace (pairProc h) (memLp_pair hh.1) :=
    sub_mem (pairVec_mem_gaussSpace hh φ) (extVec_mem_gaussSpace hh.1 V _)
  set w := X - S.starProjection X
  have hwS : w ∈ Sᗮ := S.sub_starProjection_mem_orthogonal X
  have hwG : w ∈ gaussSpace (pairProc h) (memLp_pair hh.1) :=
    sub_mem hX (germSpan_le_gaussSpace hh.1 O (S.starProjection_apply_mem X))
  obtain ⟨v, hv⟩ := horth w hwG fun u hu => (Submodule.mem_orthogonal S w).1 hwS u hu
  have hXw : ⟪X, w⟫ = 0 := by
    rw [← hv]
    change ⟪pairVec hh φ - cmIso hh.1 V ⟨rieszFun V _, rieszFun_mem V _⟩, cmIso hh.1 V v⟫ = 0
    rw [inner_sub_left, inner_pairVec_cmIso hh hV hVb, LinearIsometry.inner_map_map,
      Submodule.coe_inner, sub_self]
  have hPw : ⟪S.starProjection X, w⟫ = 0 :=
    (Submodule.mem_orthogonal S w).1 hwS _ (S.starProjection_apply_mem X)
  have hw0 : w = 0 := by
    have : ⟪w, w⟫ = 0 := by
      change ⟪X - S.starProjection X, w⟫ = 0
      rw [inner_sub_left, hXw, hPw, sub_zero]
    exact inner_self_eq_zero.1 this
  have : X = S.starProjection X := sub_eq_zero.1 hw0
  rw [this]
  exact S.starProjection_apply_mem X

/-- **Leaf (D) for bounded `V`, from the orthogonality statement**: the harmonic part has a
version measurable for the germ `σ(h|_{ℂ∖V})`. -/
theorem exists_germ_version_harm_of_orth (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) (hVb : Bornology.IsBounded (V : Set ℂ))
    (horth : ∀ ε > 0, ∀ w ∈ gaussSpace (pairProc h) (memLp_pair hh.1),
      (∀ u ∈ germSpan hh.1 (nbhdO ε (V : Set ℂ)ᶜ), ⟪u, w⟫ = 0) →
        w ∈ Set.range (cmIso hh.1 V))
    (φ : TestC) :
    ∃ G : Ω → ℝ, Measurable[fieldSigmaClosed h (V : Set ℂ)ᶜ] G ∧
      (fun ω => h ω φ - zbExt hh.1 V φ ω) =ᵐ[P] G := by
  refine exists_germ_version_of_mem hh.1 _ fun ε hε => ⟨_,
    harm_mem_germSpan_of_orth hh hV hVb (horth ε hε) φ, ?_⟩
  filter_upwards [Lp.coeFn_sub (pairVec hh φ) (extVec hh.1 V ((V : Set ℂ).indicator φ)),
    pairVec_ae hh φ, zbExt_ae hh.1 V φ] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]

/-- if every mean-zero pairing is a whole-plane Dirichlet pairing, so is the whole Gaussian space
(the range of an isometry on a complete space is closed) -/
theorem gaussSpace_le_range_cmIso_top (hh : IsWholePlaneGFF h P)
    (ha : ∀ ψ : TestC0, (memLp_pair hh ψ).toLp (pairProc h ψ) ∈ Set.range (cmIso hh ⊤))
    {w : Lp ℝ 2 P} (hw : w ∈ gaussSpace (pairProc h) (memLp_pair hh)) :
    w ∈ Set.range (cmIso hh ⊤) := by
  have hcl : IsClosed (LinearMap.range (cmIso hh ⊤).toLinearMap : Set (Lp ℝ 2 P)) := by
    rw [LinearMap.coe_range]
    exact (cmIso hh ⊤).isometry.isClosedEmbedding.isClosed_range
  have hle : gaussSpace (pairProc h) (memLp_pair hh) ≤ LinearMap.range (cmIso hh ⊤).toLinearMap :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 (by
      rintro _ ⟨ψ, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_range]
      exact ha ψ)) hcl
  obtain ⟨v, hv⟩ := LinearMap.mem_range.1 (hle hw)
  exact ⟨v, hv⟩

/-- **Leaf (D) for bounded `V`, from the two Dirichlet-space statements**:
(a) every mean-zero pairing `[⟨h, ψ⟩]` is a whole-plane Dirichlet pairing `(h, u_ψ)_∇`;
(b) a whole-plane Dirichlet pairing orthogonal to `S(B_ε(ℂ∖V))` is a Dirichlet pairing on `V`
(its Cameron–Martin function is constant on `B_ε(ℂ∖V)`). -/
theorem exists_germ_version_harm_of_dirichlet (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) (hVb : Bornology.IsBounded (V : Set ℂ))
    (ha : ∀ ψ : TestC0, (memLp_pair hh.1 ψ).toLp (pairProc h ψ) ∈ Set.range (cmIso hh.1 ⊤))
    (hb : ∀ ε > 0, ∀ v : gradClosure ((⊤ : Opens ℂ) : Set ℂ) (zeroSpace ((⊤ : Opens ℂ) : Set ℂ)),
      (∀ u ∈ germSpan hh.1 (nbhdO ε (V : Set ℂ)ᶜ), ⟪u, cmIso hh.1 ⊤ v⟫ = 0) →
        cmIso hh.1 ⊤ v ∈ Set.range (cmIso hh.1 V))
    (φ : TestC) :
    ∃ G : Ω → ℝ, Measurable[fieldSigmaClosed h (V : Set ℂ)ᶜ] G ∧
      (fun ω => h ω φ - zbExt hh.1 V φ ω) =ᵐ[P] G := by
  refine exists_germ_version_harm_of_orth hh hV hVb (fun ε hε w hw hwS => ?_) φ
  obtain ⟨v, rfl⟩ := gaussSpace_le_range_cmIso_top hh.1 ha hw
  exact hb ε hε v hwS

end MarkovGermVer
end LQGMetric
