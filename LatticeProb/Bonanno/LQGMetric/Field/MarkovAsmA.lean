/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovAsmA at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeyl3
import LatticeProb.Bonanno.LQGMetric.Field.MarkovExt
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAdm
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Assembly of LM Lemma 2.1, part A: the harmonic part is a.s. harmonic on `V` (task P2-LMASM)

For `hz` a version of the extension by zero (`MarkovExt.zbExt`) of the zero-boundary part, the
harmonic part `h − hz` is, for a.e. `ω`, given on `V` by a harmonic function
(`ae_harmonic_sub`). Proof: `⟨h − hz, −Δψ/2π⟩ = 0` a.s. for each `ψ ∈ 𝓓(V)`
(`MarkovHarm.zbProc_cmTestOn_ae`, the pairing-level weak harmonicity); for the countable
generating family `distGen V j` of `𝒟'(V)` (`injective_distOn_pairings`) this holds
simultaneously a.s., hence the distribution `(h − hz)|_V ∘ (−Δ/2π)` vanishes; then Weyl's lemma
(`MarkovWeyl3.exists_harmonic_of_laplacian_eq_zero`). This is the statement "`𝔥` is harmonic on
`V`" of LM Lemma 2.1 (`lem-whole-plane-markov`, l. 425–429; GMSh Lemma 2.2), whose proof
(GMSh §2.2; Sheffield math/0312099 §2.6) obtains it from the orthogonal decomposition
`H(ℂ) = H₀(V) ⊕ Harm(V)`. `−Δ/2π` as a continuous linear map of `𝓓(V)`: mathlib
`TestFunction.lineDerivCLM`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace Laplacian
open InnerProductSpace

namespace LQGMetric
namespace MarkovAsm

open MarkovZB MarkovHarm MarkovExt MarkovAdm MarkovWeyl3 MarkovGerm

/-- `ψ ↦ −Δψ/(2π)` on `𝓓(V)` -/
def lapV (V : Opens ℂ) : TestOn V →L[ℝ] TestOn V :=
  (-(2 * Real.pi)⁻¹ : ℝ) •
    ((TestFunction.lineDerivCLM ℝ (1 : ℂ) : TestOn V →L[ℝ] TestOn V).comp
        (TestFunction.lineDerivCLM ℝ (1 : ℂ) : TestOn V →L[ℝ] TestOn V) +
      (TestFunction.lineDerivCLM ℝ Complex.I : TestOn V →L[ℝ] TestOn V).comp
        (TestFunction.lineDerivCLM ℝ Complex.I : TestOn V →L[ℝ] TestOn V))

lemma lineDerivCLM_testOn_apply {V : Opens ℂ} (ψ : TestOn V) (v x : ℂ) :
    (TestFunction.lineDerivCLM ℝ v : TestOn V →L[ℝ] TestOn V) ψ x = fderiv ℝ ψ x v := by
  rw [TestFunction.lineDerivCLM_apply_of_le le_top,
    ((ψ.contDiff.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv]

lemma lapV_apply {V : Opens ℂ} (ψ : TestOn V) (x : ℂ) :
    lapV V ψ x = -(2 * Real.pi)⁻¹ * Δ (⇑ψ) x := by
  have e : ∀ v : ℂ, (TestFunction.lineDerivCLM ℝ v : TestOn V →L[ℝ] TestOn V)
      ((TestFunction.lineDerivCLM ℝ v : TestOn V →L[ℝ] TestOn V) ψ) x =
        fderiv ℝ (fun y => fderiv ℝ ψ y v) x v := fun v => by
    rw [lineDerivCLM_testOn_apply]
    congr 1
  rw [QuantumZipper.K3.laplacian_eq_fderiv_fderiv (ψ.contDiff.of_le (by simp)) x, ← e, ← e]
  simp [lapV]; ring

/-- `ψ ∈ 𝓓(V)` as an element of `C_c^∞(V)` -/
def toZs {V : Opens ℂ} (ψ : TestOn V) : zsSub (V : Set ℂ) :=
  ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset⟩

/-- an element of `C_c^∞(V)` as a test function on `V` -/
def ofZs {V : Opens ℂ} (f : zsSub (V : Set ℂ)) : TestOn V :=
  have hf : f.1 ∈ QuantumZipper.zeroSpace (V : Set ℂ) := f.2
  ⟨f.1, hf.1, hf.2.1, hf.2.2⟩

lemma toZs_ofZs {V : Opens ℂ} (f : zsSub (V : Set ℂ)) : toZs (ofZs f) = f := rfl

lemma cmTestOn_toZs {V : Opens ℂ} (ψ : TestOn V) : cmTestOn (toZs ψ) = lapV V ψ := by
  ext x
  rw [cmTestOn_apply, cmTest_apply, lapV_apply]
  rfl

lemma extC_cmTestOn {V : Opens ℂ} (f : zsSub (V : Set ℂ)) :
    extC V (cmTestOn f) = cmTest (zsTest f.2) := by
  ext x
  rw [coe_extC]
  rfl

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- **The harmonic part is a.s. harmonic on `V`.** -/
theorem ae_harmonic_sub (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) (hz : Ω → DistC)
    (hzae : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh.1 V φ) :
    ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (V : Set ℂ) ∧
      ∀ φ : TestOn V, restrictTo V (h ω - hz ω) φ = ∫ x, g x * φ x := by
  have hadm := zbAdmissible_of_disjoint_sphere hV
  have key : ∀ f : zsSub (V : Set ℂ),
      ∀ᵐ ω ∂P, restrictTo V (h ω - hz ω) (cmTestOn f) = 0 := fun f => by
    filter_upwards [hzae (extC V (cmTestOn f)), zbExt_ae_eq_zbProc hh.1 (cmTestOn f),
      zbProc_cmTestOn_ae hh.1 hadm f] with ω h1 h2 h3
    change (h ω - hz ω) (extC V (cmTestOn f)) = 0
    rw [sub_apply, h1, h2, h3, extC_cmTestOn, sub_self]
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ × ℕ,
      restrictTo V (h ω - hz ω) (cmTestOn (toZs (distGen V j))) = 0 :=
    ae_all_iff.2 fun j => key _
  filter_upwards [hall] with ω hω
  set T := restrictTo V (h ω - hz ω)
  have hT0 : T.comp (lapV V) = 0 := by
    apply injective_distOn_pairings V
    funext j
    show T (lapV V (distGen V j)) = 0
    rw [← cmTestOn_toZs]
    exact hω j
  refine exists_harmonic_of_laplacian_eq_zero T fun f => ?_
  rw [← toZs_ofZs f, cmTestOn_toZs]
  exact congrArg (fun S : DistOn V => S (ofZs f)) hT0

end MarkovAsm
end LQGMetric
