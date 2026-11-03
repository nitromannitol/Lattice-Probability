/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer2E at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2D
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAdmCov

/-!
# Germ measurability of the harmonic part: the reduction for unbounded `V` (task P2-MKD2)

With leaf (A) (`inner_pairVec_cmIso_of_disjoint`, admissibility of every `V` with
`V ∩ ∂𝔻 = ∅`), the Hilbert-space reduction of `MarkovGermVer.lean` holds without boundedness:
`exists_germ_version_harm_of_range` reduces leaf (D) for arbitrary open `V` (`V ∩ ∂𝔻 = ∅`) to the
germ step (node (b)) for that `V`. For bounded `V` the germ step is `mem_range_cmIso_of_orth`.

Sources: as in `MarkovGermVer.lean` (Sheffield math/0312099 §2.6, Thm 2.17; IG4 Prop. 2.8;
Berestycki–Powell arXiv:2404.16642 Thm 1.52 / Lemma 1.53).
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

/-- `harm_mem_germSpan_of_orth` without boundedness of `V` (uses leaf (A)) -/
theorem harm_mem_germSpan_of_orth' (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) {O : Set ℂ}
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
    rw [inner_sub_left, MarkovAdm.inner_pairVec_cmIso_of_disjoint hh hV, LinearIsometry.inner_map_map,
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

/-- **Leaf (D) for arbitrary open `V` (`V ∩ ∂𝔻 = ∅`), from the germ step for `V`**. -/
theorem exists_germ_version_harm_of_range (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1))
    (hb : ∀ ε > 0, ∀ v : gradClosure ((⊤ : Opens ℂ) : Set ℂ) (zeroSpace ((⊤ : Opens ℂ) : Set ℂ)),
      (∀ u ∈ germSpan hh.1 (nbhdO ε (V : Set ℂ)ᶜ), ⟪u, cmIso hh.1 ⊤ v⟫ = 0) →
        cmIso hh.1 ⊤ v ∈ Set.range (cmIso hh.1 V))
    (φ : TestC) :
    ∃ G : Ω → ℝ, Measurable[fieldSigmaClosed h (V : Set ℂ)ᶜ] G ∧
      (fun ω => h ω φ - zbExt hh.1 V φ ω) =ᵐ[P] G := by
  refine exists_germ_version_of_mem hh.1 _ fun ε hε => ⟨_,
    harm_mem_germSpan_of_orth' hh hV (fun w hw hwS => ?_) φ, ?_⟩
  · obtain ⟨v, rfl⟩ := gaussSpace_le_range_cmIso_top hh.1 (pair_mem_range_cmIso_top hh.1) hw
    exact hb ε hε v hwS
  · filter_upwards [Lp.coeFn_sub (pairVec hh φ) (extVec hh.1 V ((V : Set ℂ).indicator φ)),
      pairVec_ae hh φ, zbExt_ae hh.1 V φ] with ω h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]

end MarkovGermVer
end LQGMetric
