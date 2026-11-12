/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.GermSplitA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2D
import LatticeProb.Bonanno.LQGMetric.Field.MarkovHarm
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.MarkovNorm
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.BilipLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `σ(h) ⊆ σ(h|_V) ∨ σ(h|_{ℂ∖V})` for bounded `V` (task P2-GERM)

LM (arXiv:1905.00379, `local-metrics-final.tex`) l. 534: "`h` is determined by `h|_V` and
`h|_{U∖V}`". For a whole-plane GFF `h` (arbitrary additive constant) and a **bounded** open `V`:

  `σ(h) ⊆ σ(h|_V) ∨ σ(h|_{ℂ∖V})` modulo `P`-null events (`locGermSplitBdd`),

with `σ(h|_{ℂ∖V}) = ⋂_ε σ(h|_{B_ε(ℂ∖V)})` (LM footnote l. 164).

Proof (Gaussian Hilbert space; Sheffield, *Gaussian free fields for mathematicians*
(math/0312099) §2.6, Thm 2.17 and the paragraph after it, tex l. 690–725: `H = Supp(V) ⊕ Harm(V)`;
Berestycki–Powell arXiv:2404.16642 Thm 1.52, Lemma 1.53), following `handoff/P2-LMLOC.md`:
1. `S(O)` = closed span of the mean-zero pairings supported in `O` (`MarkovGermVer.germSpan`).
   Germ step (project, `MarkovGermVer.mem_range_cmIso_of_orth`, applied to the recentred field
   `h − h_1(0)`, which has the same mean-zero pairings): an element of the Gaussian space
   orthogonal to `S(B_ε(ℂ∖V))` is a Dirichlet pairing on `V`, hence lies in `S(V)`
   (`mem_germSpan_of_orth`).
2. Hence `S(V)^⊥ ∩ H ⊆ S(B_ε(ℂ∖V))` for every `ε` (`mem_germSpan_nbhd_of_orthV`).
3. For mean-zero `χ`: `⟨h, χ⟩ = Π_{S(V)}⟨h, χ⟩ + w`, the first summand `σ(h|_V)`-measurable, `w`
   `σ(h|_{ℂ∖V})`-measurable (`exists_germ_version_of_mem`).
4. A general test function `φ = χ + (∫φ) ψ`, `ψ ∈ C_c^∞(V)`, `∫ψ = 1`; `⟨h, ψ⟩` is
   `σ(h|_V)`-measurable. For `V = ∅` every pairing is germ-measurable directly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace GermSplit

open MarkovGauss MarkovZB MarkovGermVer MarkovHarm Blueprint QuantumZipper QuantumZipper.K3
  GM.Bilip

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the recentred field `h − h_1(0)` -/
def gsRec (h : Ω → DistC) : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) 1 0)

omit [MeasurableSpace Ω] in
lemma gsRec_pair (h : Ω → DistC) (ω : Ω) (χ : TestC0) : gsRec h ω χ.1 = h ω χ.1 := by
  rw [gsRec, GFFInv.addConst_apply, χ.2, zero_mul, add_zero]

omit [IsProbabilityMeasure P] in
lemma isNormalized_gsRec (hh : IsWholePlaneGFF h P) : IsNormalizedWPGFF (gsRec h) P :=
  DFGPS.isNormalizedAt_recenter hh one_pos 0

lemma toLp_gsRec (hh : IsWholePlaneGFF h P) :
    (fun χ : TestC0 => (memLp_pair (isNormalized_gsRec hh).1 χ).toLp
      (pairProc (gsRec h) χ)) = fun χ => (memLp_pair hh χ).toLp (pairProc h χ) :=
  funext fun χ => MemLp.toLp_congr _ _ (Eventually.of_forall fun ω => gsRec_pair h ω χ)

lemma germSpan_gsRec (hh : IsWholePlaneGFF h P) (O : Set ℂ) :
    germSpan (isNormalized_gsRec hh).1 O = germSpan hh O := by
  unfold germSpan
  rw [toLp_gsRec hh]

lemma gaussSpace_gsRec (hh : IsWholePlaneGFF h P) :
    gaussSpace (pairProc (gsRec h)) (memLp_pair (isNormalized_gsRec hh).1) =
      gaussSpace (pairProc h) (memLp_pair hh) := by
  unfold gaussSpace
  rw [toLp_gsRec hh]

/-- `H₀¹(U) ⊆ S(U)`: Dirichlet pairings on `U` are pairings supported in `U` -/
lemma cmIso_mem_germSpan (hh : IsWholePlaneGFF h P) (U : Opens ℂ)
    (v : gradClosure (U : Set ℂ) (zeroSpace (U : Set ℂ))) :
    cmIso hh U v ∈ germSpan hh (U : Set ℂ) := by
  refine (denseRange_gradLin U).induction_on v
    ((Submodule.isClosed_topologicalClosure _).preimage (cmIso hh U).continuous) fun f => ?_
  show cmIso hh U (gradLin U f) ∈ _
  rw [cmIso_gradLin]
  exact toLp_mem_germSpan hh (cmTest0 (zsTest f.2)) ((tsupport_cmTest_subset f.2).trans f.2.2.2)

/-- **germ step**: an element of the Gaussian space orthogonal to `S(B_ε(ℂ∖V))` lies in `S(V)`
(bounded `V`, arbitrary additive constant) -/
theorem mem_germSpan_of_orth (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hVb : Bornology.IsBounded (V : Set ℂ)) {ε : ℝ} (hε : 0 < ε) {w : Lp ℝ 2 P}
    (hw : w ∈ gaussSpace (pairProc h) (memLp_pair hh))
    (hwO : ∀ u ∈ germSpan hh (nbhdO ε (V : Set ℂ)ᶜ), ⟪u, w⟫ = 0) :
    w ∈ germSpan hh (V : Set ℂ) := by
  have hn := isNormalized_gsRec hh
  rw [← gaussSpace_gsRec hh] at hw
  obtain ⟨v, rfl⟩ := gaussSpace_le_range_cmIso_top hn.1 (pair_mem_range_cmIso_top hn.1) hw
  obtain ⟨v', hv'⟩ := mem_range_cmIso_of_orth hn hVb hε v (by rw [germSpan_gsRec hh]; exact hwO)
  rw [← hv', ← germSpan_gsRec hh]
  exact cmIso_mem_germSpan hn.1 V v'

/-- `S(V)^⊥ ∩ H ⊆ S(B_ε(ℂ∖V))` -/
theorem mem_germSpan_nbhd_of_orthV (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hVb : Bornology.IsBounded (V : Set ℂ)) {w : Lp ℝ 2 P}
    (hw : w ∈ gaussSpace (pairProc h) (memLp_pair hh)) (hwV : w ∈ (germSpan hh (V : Set ℂ))ᗮ)
    {ε : ℝ} (hε : 0 < ε) : w ∈ germSpan hh (nbhdO ε (V : Set ℂ)ᶜ) := by
  set T := germSpan hh (nbhdO ε (V : Set ℂ)ᶜ)
  have : CompleteSpace T := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set z := w - T.starProjection w with hz
  have hzT : z ∈ Tᗮ := T.sub_starProjection_mem_orthogonal w
  have hzG : z ∈ gaussSpace (pairProc h) (memLp_pair hh) :=
    sub_mem hw (germSpan_le_gaussSpace hh _ (T.starProjection_apply_mem w))
  have hzV : z ∈ germSpan hh (V : Set ℂ) :=
    mem_germSpan_of_orth hh hVb hε hzG fun u hu => (Submodule.mem_orthogonal T z).1 hzT u hu
  have h1 : ⟪z, w⟫ = 0 := (Submodule.mem_orthogonal _ w).1 hwV z hzV
  have h2 : ⟪T.starProjection w, z⟫ = 0 :=
    (Submodule.mem_orthogonal T z).1 hzT _ (T.starProjection_apply_mem w)
  have hz0 : z = 0 := by
    have : ⟪z, z⟫ = 0 := by
      conv_lhs => arg 2; rw [hz]
      rw [inner_sub_right, h1, real_inner_comm, h2, sub_zero]
    exact inner_self_eq_zero.1 this
  have : w = T.starProjection w := sub_eq_zero.1 hz0
  rw [this]
  exact T.starProjection_apply_mem w

/-- a mean-zero pairing splits as a `σ(h|_V)`-measurable plus a `σ(h|_{ℂ∖V})`-measurable
variable, a.s. -/
theorem exists_split_pair0 (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hVb : Bornology.IsBounded (V : Set ℂ)) (χ : TestC0) :
    ∃ G₁ G₂ : Ω → ℝ, Measurable[fieldSigma h V] G₁ ∧
      Measurable[fieldSigmaClosed h (V : Set ℂ)ᶜ] G₂ ∧ pairProc h χ =ᵐ[P] G₁ + G₂ := by
  set S := germSpan hh (V : Set ℂ)
  have : CompleteSpace S := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set X := (memLp_pair hh χ).toLp (pairProc h χ)
  have hX : X ∈ gaussSpace (pairProc h) (memLp_pair hh) := toLp_mem_gaussSpace (memLp_pair hh) χ
  set w := X - S.starProjection X with hw
  have hwS : w ∈ Sᗮ := S.sub_starProjection_mem_orthogonal X
  have hwG : w ∈ gaussSpace (pairProc h) (memLp_pair hh) :=
    sub_mem hX (germSpan_le_gaussSpace hh _ (S.starProjection_apply_mem X))
  obtain ⟨G₁, hG₁, hG₁e⟩ := exists_version_of_mem_germSpan hh V (S.starProjection_apply_mem X)
  obtain ⟨G₂, hG₂, hG₂e⟩ := exists_germ_version_of_mem hh (V : Set ℂ)ᶜ (f := (w : Ω → ℝ))
    fun ε hε => ⟨w, mem_germSpan_nbhd_of_orthV hh hVb hwG hwS hε, EventuallyEq.rfl⟩
  refine ⟨G₁, G₂, hG₁, hG₂, ?_⟩
  have e1 : X = S.starProjection X + w := (add_sub_cancel _ _).symm
  filter_upwards [(memLp_pair hh χ).coeFn_toLp, Lp.coeFn_add (S.starProjection X) w, hG₁e, hG₂e]
    with ω h1 h2 h3 h4
  calc pairProc h χ ω = (X : Ω → ℝ) ω := h1.symm
    _ = ((S.starProjection X + w : Lp ℝ 2 P) : Ω → ℝ) ω := by rw [← e1]
    _ = (G₁ + G₂) ω := by rw [h2, Pi.add_apply, Pi.add_apply, h3, h4]

omit [MeasurableSpace Ω] in
/-- a test function in `V` with integral one -/
lemma exists_test_unit {V : Opens ℂ} (hV : (V : Set ℂ).Nonempty) :
    ∃ ψ : TestC, tsupport (ψ : ℂ → ℝ) ⊆ V ∧ ∫ x, ψ x = 1 := by
  obtain ⟨c, hc⟩ := hV
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 V.2 c hc
  let b : ContDiffBump c := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨⟨b.normed volume, b.contDiff_normed (n := ⊤), b.hasCompactSupport_normed,
    subset_univ _⟩, ?_, b.integral_normed⟩
  change tsupport (b.normed volume) ⊆ V
  rw [b.tsupport_normed_eq]
  exact (closedBall_subset_ball (by change r / 2 < r; linarith)).trans hrV

/-- every pairing `⟨h, φ⟩` is a.s. equal to a `σ(h|_V) ∨ σ(h|_{ℂ∖V})`-measurable variable -/
theorem exists_split_pair (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hVb : Bornology.IsBounded (V : Set ℂ)) (φ : TestC) :
    ∃ G : Ω → ℝ, Measurable[fieldSigma h V ⊔ fieldSigmaClosed h (V : Set ℂ)ᶜ] G ∧
      (fun ω => h ω φ) =ᵐ[P] G := by
  rcases (V : Set ℂ).eq_empty_or_nonempty with hV | hV
  · refine ⟨fun ω => h ω φ, ?_, EventuallyEq.rfl⟩
    refine Measurable.mono ?_ le_sup_right le_rfl
    refine measurable_iff_comap_le.2 (le_iInf₂ fun ε hε => measurable_iff_comap_le.1
      (GM.measurable_pair_fieldSigma h φ fun x _ => ?_))
    change x ∈ thickening ε (V : Set ℂ)ᶜ
    rw [hV, compl_empty]
    exact self_subset_thickening hε _ (mem_univ x)
  · obtain ⟨ψ, hψV, hψ1⟩ := exists_test_unit hV
    set a := ∫ x, φ x
    let χ : TestC0 := ⟨φ - a • ψ, GFFLaw.integral_sub_smul hψ1 φ⟩
    obtain ⟨G₁, G₂, hG₁, hG₂, he⟩ := exists_split_pair0 hh hVb χ
    have hψm := GM.measurable_pair_fieldSigma h ψ hψV
    refine ⟨fun ω => G₁ ω + G₂ ω + a * h ω ψ, ?_, ?_⟩
    · exact ((hG₁.mono le_sup_left le_rfl).add (hG₂.mono le_sup_right le_rfl)).add
        ((hψm.mono le_sup_left le_rfl).const_mul a)
    · filter_upwards [he] with ω hω
      have e : h ω φ = h ω χ.1 + a * h ω ψ := by
        change h ω φ = h ω (φ - a • ψ) + a * h ω ψ
        rw [map_sub, map_smul, smul_eq_mul]; ring
      rw [e]
      change pairProc h χ ω + _ = _
      rw [hω, Pi.add_apply]

omit [IsProbabilityMeasure P] in
lemma measurable_aeClosure_of_ae_eq {G : MeasurableSpace Ω} {f g : Ω → ℝ}
    (hg : Measurable[G] g) (hfg : f =ᵐ[P] g) : Measurable[aeClosure P G] f :=
  fun _ hs => ⟨_, hg hs, hfg.preimage _⟩

/-- **LM l. 534 for bounded `V`**: `σ(h) ⊆ σ(h|_V) ∨ σ(h|_{ℂ∖V})` modulo null events -/
def LocGermSplitBdd : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ V : TopologicalSpace.Opens ℂ, Bornology.IsBounded (V : Set ℂ) →
      MeasurableSpace.comap h inferInstance ≤
        aeClosure P (fieldSigma h V ⊔ fieldSigmaClosed h (V : Set ℂ)ᶜ)

theorem locGermSplitBdd : LocGermSplitBdd := by
  intro Ω _ P _ h hh V hVb
  have hm : Measurable[aeClosure P (fieldSigma h V ⊔ fieldSigmaClosed h (V : Set ℂ)ᶜ)] h :=
    (@GFFInv.measurable_distC_iff Ω (aeClosure P _) h).2 fun φ => by
      obtain ⟨G, hG, hGe⟩ := exists_split_pair hh hVb φ
      exact measurable_aeClosure_of_ae_eq hG hGe
  exact measurable_iff_comap_le.1 hm

end GermSplit
end LQGMetric
