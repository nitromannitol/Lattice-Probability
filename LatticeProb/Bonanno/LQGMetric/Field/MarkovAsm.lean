/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovAsm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAsmB
import LatticeProb.Bonanno.LQGMetric.Field.MarkovVer2Fub
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2E

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Assembly of LM Lemma 2.1 (task P2-LMASM)

LM Lemma 2.1 (`lem-whole-plane-markov`, l. 425–429; proved in GMSh = arXiv:1807.07511,
Lemma 2.2), case `V ∩ ∂𝔻 = ∅`, assembled from the proved leaves of `handoff/P2-MARKOV.md`:
`hz` is the distribution-valued version of the extension by zero of the zero-boundary part
(`MarkovVer2.exists_dist_version_zbExt`, leaf (V)), `𝔥 := h − hz`. Clauses: sum (definition),
harmonic (`MarkovAsm.ae_harmonic_sub`: Weyl's lemma, leaf (H)), determined
(`exists_germ_dist_version` from the pairing-level germ versions, leaf (D)), `𝔥 ⫫ hz`
(`indepFun_sub_dist`), zero-boundary GFF (`isZeroBoundaryGFF_restrict`), vanishing off `cl V`
(leaf (V)), `hz ⫫ σ(h|_{ℂ∖V})` (`indep_dist_fieldSigmaClosed`).

**Gap to `Blueprint.LMLem2_1` (reported, not bridged).** `LMLem2_1` asks for the harmonic clause
for *every* `ω` together with `h ω = 𝔥 ω + h̊ ω` for every `ω`, `h̊ ω` vanishing off `cl V` for
every `ω` and `h̊` measurable. The proof gives the harmonic clause for a.e. `ω` (as in the paper,
where all statements about the random distributions are almost sure). Upgrading to every `ω`
would require, on the null set where it fails, a *measurable* decomposition `T = A + S` of an
arbitrary distribution `T ∈ 𝒟'(ℂ)` with `A|_V` harmonic and `S` supported in `cl V` (true by the
structure theorem for distributions, but not a step of LM/GMSh). Hence the results here:

* `markov_decomp_ae` : the decomposition for one `V`, given the germ versions of the harmonic
  pairings (leaf (D) for that `V`);
* `lmLem2_1AE_of_germ` : `LMLem2_1AE` (= `LMLem2_1` with the harmonic clause a.s.) from the germ
  step `mem_range_cmIso_of_orth_unbdd` (hypothesis, being proved by P2-MKD3);
* `lmLem2_1AE_bdd` : `LMLem2_1AEBdd` (bounded `V`), unconditional.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace InnerProductSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovAsm

open MarkovZB MarkovExt MarkovVer2 MarkovGermVer Blueprint QuantumZipper QuantumZipper.K3

/-- **LM Lemma 2.1 with the harmonic clause almost sure**: `LMLem2_1` with
`∀ ω, ∃ g harmonic …` replaced by `∀ᵐ ω, ∃ g harmonic …`; all other clauses verbatim. -/
def LMLem2_1AE : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWPGFF h P → ∀ V : TopologicalSpace.Opens ℂ,
      Disjoint (V : Set ℂ) (Metric.sphere (0 : ℂ) 1) →
    ∃ hh hz : Ω → DistC, (∀ ω, h ω = hh ω + hz ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (V : Set ℂ) ∧
        ∀ φ : TestOn V, restrictTo V (hh ω) φ = ∫ x, g x * φ x) ∧
      (∃ G : Ω → DistC, @Measurable Ω DistC (fieldSigmaClosed h (V : Set ℂ)ᶜ) _ G ∧
        hh =ᵐ[P] G) ∧
      IndepFun hh hz P ∧
      IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P ∧
      (∀ ω, restrictTo (toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0) ∧
      Indep (MeasurableSpace.comap hz inferInstance) (fieldSigmaClosed h (V : Set ℂ)ᶜ) P

/-- `LMLem2_1AE` for bounded `V` -/
def LMLem2_1AEBdd : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWPGFF h P → ∀ V : TopologicalSpace.Opens ℂ,
      Disjoint (V : Set ℂ) (Metric.sphere (0 : ℂ) 1) → Bornology.IsBounded (V : Set ℂ) →
    ∃ hh hz : Ω → DistC, (∀ ω, h ω = hh ω + hz ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (V : Set ℂ) ∧
        ∀ φ : TestOn V, restrictTo V (hh ω) φ = ∫ x, g x * φ x) ∧
      (∃ G : Ω → DistC, @Measurable Ω DistC (fieldSigmaClosed h (V : Set ℂ)ᶜ) _ G ∧
        hh =ᵐ[P] G) ∧
      IndepFun hh hz P ∧
      IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P ∧
      (∀ ω, restrictTo (toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0) ∧
      Indep (MeasurableSpace.comap hz inferInstance) (fieldSigmaClosed h (V : Set ℂ)ᶜ) P

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- **The Markov decomposition for one `V`**, given germ versions of the harmonic pairings. -/
theorem markov_decomp_ae (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1))
    (hG : ∀ φ : TestC, ∃ G : Ω → ℝ, Measurable[fieldSigmaClosed h (V : Set ℂ)ᶜ] G ∧
      (fun ω => h ω φ - zbExt hh.1 V φ ω) =ᵐ[P] G) :
    ∃ hh' hz : Ω → DistC, (∀ ω, h ω = hh' ω + hz ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (V : Set ℂ) ∧
        ∀ φ : TestOn V, restrictTo V (hh' ω) φ = ∫ x, g x * φ x) ∧
      (∃ G : Ω → DistC, @Measurable Ω DistC (fieldSigmaClosed h (V : Set ℂ)ᶜ) _ G ∧
        hh' =ᵐ[P] G) ∧
      IndepFun hh' hz P ∧
      IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P ∧
      (∀ ω, restrictTo (toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0) ∧
      Indep (MeasurableSpace.comap hz inferInstance) (fieldSigmaClosed h (V : Set ℂ)ᶜ) P := by
  obtain ⟨hz, hzm, hzae, hzv⟩ := exists_dist_version_zbExt hh hV
  exact ⟨fun ω => h ω - hz ω, hz, fun ω => (sub_add_cancel _ _).symm,
    ae_harmonic_sub hh hV hz hzae, exists_germ_dist_version hh hzae hG,
    indepFun_sub_dist hh hV hzae, isZeroBoundaryGFF_restrict hh hV hzm hzae, hzv,
    indep_dist_fieldSigmaClosed hh hV hzae⟩

/-- **LM Lemma 2.1 (harmonic clause a.s.) from the germ step for unbounded `V`**
(`mem_range_cmIso_of_orth_unbdd`, `handoff/P2-MKD2.md`). -/
theorem lmLem2_1AE_of_germ
    (hD : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {V : Opens ℂ},
      Disjoint (V : Set ℂ) (sphere 0 1) → ∀ {ε : ℝ}, 0 < ε →
      ∀ v : gradClosure ((⊤ : Opens ℂ) : Set ℂ) (zeroSpace ((⊤ : Opens ℂ) : Set ℂ)),
      (∀ u ∈ germSpan hh.1 (Blueprint.nbhdO ε (V : Set ℂ)ᶜ), ⟪u, cmIso hh.1 ⊤ v⟫ = 0) →
        cmIso hh.1 ⊤ v ∈ Set.range (cmIso hh.1 V)) :
    LMLem2_1AE := by
  intro Ω _ P _ h hh V hV
  exact markov_decomp_ae hh hV
    (exists_germ_version_harm_of_range hh hV fun ε hε v hv => hD hh hV hε v hv)

/-- **LM Lemma 2.1 (harmonic clause a.s.) for bounded `V`**, unconditional. -/
theorem lmLem2_1AE_bdd : LMLem2_1AEBdd := by
  intro Ω _ P _ h hh V hV hVb
  exact markov_decomp_ae hh hV (exists_germ_version_harm_of_bdd hh hV hVb)

end MarkovAsm
end LQGMetric
