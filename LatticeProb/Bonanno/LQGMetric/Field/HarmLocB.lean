/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HarmLocB at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HarmLocA
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2D
import LatticeProb.Bonanno.LQGMetric.Field.MarkovHarm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.MarkovNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Locality of the harmonic part: the Hilbert-space step (task P2-HARMLOC, part B)

For a whole-plane GFF `h` with an **arbitrary** additive constant and a bounded open `U`, write
`𝒢 = σ(h|_{ℂ∖U})` (`fieldSigmaClosed h Uᶜ`) and `R = range (cmIso U) = H₀¹(U) ⊆ L²(P)` (the
Dirichlet pairings `(h, f)_∇`, `f ∈ C_c^∞(U)`). If `R ⊥ L²(𝒢)` in the weak form
`∫_s (h, f)_∇ = 0` for `s ∈ 𝒢` (this is what `IsHarmPart` gives for `φ = −Δf/2π`, see
`HarmLocC`), then for every mean-zero test function `χ`,

  `E[⟨h, χ⟩ | 𝒢] = ⟨h, χ⟩ − Π_R ⟨h, χ⟩`  a.s. (`condExp_pair_eq`),

and the right-hand side lies in `S(B_ε(ℂ∖U))` for all `ε` (germ step, `mem_range_cmIso_of_orth`)
and in `S(W)` for every open `W ⊇ U ∪ supp χ` (`R ⊆ S(U)`), hence has a `σ(h|_W)`-measurable
version (`exists_version_of_mem_germSpan`).

This is the Hilbert-space form of the Markov property: Sheffield, *Gaussian free fields for
mathematicians* (math/0312099), §2.6, Thm 2.17 (tex l. 690–725): `H(D) = Supp(U) ⊕ Harm(U)`,
the projection onto `Harm(U)` is the conditional expectation given the field outside `U`;
Berestycki–Powell (arXiv:2404.16642) Thm 1.52, Lemma 1.53. The germ step is the project's
`MarkovGermVer.mem_range_cmIso_of_orth`, applied to the recentred field `h − h_1(0)` (which has
the same mean-zero pairings, `DFGPS.isNormalizedAt_recenter`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace HarmLoc

open MarkovGauss MarkovZB MarkovGermVer MarkovHarm Blueprint QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the recentred field `h − h_1(0)` -/
def recF (h : Ω → DistC) : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) 1 0)

omit [MeasurableSpace Ω] in
lemma recF_pair (h : Ω → DistC) (ω : Ω) (χ : TestC0) : recF h ω χ.1 = h ω χ.1 := by
  rw [recF, GFFInv.addConst_apply, χ.2, zero_mul, add_zero]

omit [MeasurableSpace Ω] in
lemma pairProc_recF (h : Ω → DistC) : pairProc (recF h) = pairProc h :=
  funext fun χ => funext fun ω => recF_pair h ω χ

omit [IsProbabilityMeasure P] in
lemma isNormalized_recF (hh : IsWholePlaneGFF h P) : IsNormalizedWPGFF (recF h) P :=
  DFGPS.isNormalizedAt_recenter hh one_pos 0

/-- the germ spans of `h` and of `h − h_1(0)` agree -/
lemma germSpan_recF (hh : IsWholePlaneGFF h P) (O : Set ℂ) :
    germSpan (isNormalized_recF hh).1 O = germSpan hh O := by
  have e : (fun χ : TestC0 => (memLp_pair (isNormalized_recF hh).1 χ).toLp
      (pairProc (recF h) χ)) = fun χ => (memLp_pair hh χ).toLp (pairProc h χ) :=
    funext fun χ => MemLp.toLp_congr _ _ (Eventually.of_forall fun ω => recF_pair h ω χ)
  unfold germSpan
  rw [e]

omit [IsProbabilityMeasure P] in
lemma fieldSigmaClosed_le (hh : IsWholePlaneGFF h P) (K : Set ℂ) :
    fieldSigmaClosed h K ≤ ‹MeasurableSpace Ω› :=
  (iInf₂_le 1 one_pos).trans (fieldSigma_le hh _)

section Hilbert

variable (hh : IsWholePlaneGFF h P) (U : Opens ℂ)

/-- `H₀¹(U)` inside `L²(P)` (for the recentred field) -/
def rangeR : Submodule ℝ (Lp ℝ 2 P) :=
  LinearMap.range (cmIso (isNormalized_recF hh).1 U).toLinearMap

lemma isClosed_rangeR : IsClosed (rangeR hh U : Set (Lp ℝ 2 P)) := by
  rw [rangeR, LinearMap.coe_range]
  exact (cmIso (isNormalized_recF hh).1 U).isometry.isClosedEmbedding.isClosed_range

instance : CompleteSpace (rangeR hh U) := (isClosed_rangeR hh U).completeSpace_coe

lemma rangeR_le_germSpan : rangeR hh U ≤ germSpan hh (U : Set ℂ) := by
  rintro _ ⟨v, rfl⟩
  rw [← germSpan_recF hh]
  refine (denseRange_gradLin U).induction_on v ?_ fun f => ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage
      (cmIso (isNormalized_recF hh).1 U).continuous
  · show cmIso _ U (gradLin U f) ∈ _
    rw [cmIso_gradLin]
    exact toLp_mem_germSpan _ (cmTest0 (zsTest f.2))
      ((tsupport_cmTest_subset f.2).trans f.2.2.2)

lemma rangeR_le_gaussSpace :
    rangeR hh U ≤ gaussSpace (pairProc (recF h)) (memLp_pair (isNormalized_recF hh).1) := by
  rintro _ ⟨v, rfl⟩
  exact cmIso_mem_gaussSpace _ U v

variable {U} in
/-- `R ⊥ 𝟙_s` for `s ∈ 𝒢`, from the generators -/
lemma inner_indicator_rangeR
    (hperp : ∀ f : zsSub (U : Set ℂ), ∀ s, MeasurableSet[fieldSigmaClosed h (U : Set ℂ)ᶜ] s →
      ∫ ω in s, h ω (cmTest (zsTest f.2)) ∂P = 0)
    {s : Set Ω} (hs : MeasurableSet[fieldSigmaClosed h (U : Set ℂ)ᶜ] s) {r : Lp ℝ 2 P}
    (hr : r ∈ rangeR hh U) :
    ⟪indicatorConstLp 2 (fieldSigmaClosed_le hh _ s hs) (measure_ne_top P s) (1 : ℝ), r⟫ = 0 := by
  obtain ⟨v, rfl⟩ := hr
  refine (denseRange_gradLin U).induction_on v ?_ fun f => ?_
  · exact isClosed_eq ((continuous_const.inner continuous_id).comp
      (cmIso (isNormalized_recF hh).1 U).continuous) continuous_const
  · show ⟪_, cmIso _ U (gradLin U f)⟫ = 0
    rw [cmIso_gradLin, L2.inner_indicatorConstLp_one]
    simp only [cmLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [setIntegral_congr_ae (fieldSigmaClosed_le hh _ s hs)
      (((memLp_pair (isNormalized_recF hh).1 _).coeFn_toLp).mono fun ω hω _ => hω)]
    simp only [pairProc_recF]
    exact hperp f s hs

variable {U} in
/-- **germ step** (arbitrary additive constant): `X − Π_R X ∈ S(B_ε(ℂ∖U))` -/
lemma sub_proj_mem_germSpan (hUb : Bornology.IsBounded (U : Set ℂ)) {ε : ℝ} (hε : 0 < ε)
    (χ : TestC0) :
    (memLp_pair (isNormalized_recF hh).1 χ).toLp (pairProc (recF h) χ) -
      (rangeR hh U).starProjection
        ((memLp_pair (isNormalized_recF hh).1 χ).toLp (pairProc (recF h) χ)) ∈
      germSpan hh (nbhdO ε (U : Set ℂ)ᶜ : Set ℂ) := by
  set hN := isNormalized_recF hh
  set R := rangeR hh U
  rw [← germSpan_recF hh]
  set S := germSpan hN.1 (nbhdO ε (U : Set ℂ)ᶜ : Set ℂ)
  have : CompleteSpace S := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set X := (memLp_pair hN.1 χ).toLp (pairProc (recF h) χ)
  set A := X - R.starProjection X
  have hAG : A ∈ gaussSpace (pairProc (recF h)) (memLp_pair hN.1) :=
    sub_mem (toLp_mem_gaussSpace _ χ) (rangeR_le_gaussSpace hh U (R.starProjection_apply_mem X))
  set w := A - S.starProjection A
  have hwS : w ∈ Sᗮ := S.sub_starProjection_mem_orthogonal A
  have hwG : w ∈ gaussSpace (pairProc (recF h)) (memLp_pair hN.1) :=
    sub_mem hAG (germSpan_le_gaussSpace hN.1 _ (S.starProjection_apply_mem A))
  obtain ⟨v, hv⟩ := gaussSpace_le_range_cmIso_top hN.1 (pair_mem_range_cmIso_top hN.1) hwG
  have hwR : w ∈ R := by
    obtain ⟨v', hv'⟩ := mem_range_cmIso_of_orth hN hUb hε v (by
      rw [hv]; exact fun u hu => (Submodule.mem_orthogonal S w).1 hwS u hu)
    exact ⟨v', hv'.trans hv⟩
  have hAw : ⟪A, w⟫ = 0 :=
    (Submodule.mem_orthogonal' R A).1 (R.sub_starProjection_mem_orthogonal X) w hwR
  have hPw : ⟪S.starProjection A, w⟫ = 0 :=
    (Submodule.mem_orthogonal S w).1 hwS _ (S.starProjection_apply_mem A)
  have hw0 : w = 0 := by
    have : ⟪w, w⟫ = 0 := by
      change ⟪A - S.starProjection A, w⟫ = 0
      rw [inner_sub_left, hAw, hPw, sub_zero]
    exact inner_self_eq_zero.1 this
  have : A = S.starProjection A := sub_eq_zero.1 hw0
  rw [this]
  exact S.starProjection_apply_mem A

end Hilbert

end HarmLoc
end LQGMetric
