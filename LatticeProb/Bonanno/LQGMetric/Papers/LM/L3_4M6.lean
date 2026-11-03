/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4M6 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M5
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4N6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LM Lemma 3.1: the canonical nesting `LMNestCanonLeaf`, and LM Lemma 3.1 (task P2-LM34c)

Source: MQ arXiv:1812.03913 `lqg_geodesics.tex`, proof of Prop 4.3 (l. 693–700): nested Markov
decompositions of `h` on `B_{r_0} ⊃ B_{r_1} ⊃ …`; LM arXiv:1905.00379 Lemma 3.1 (`N = 0`),
whose proof (LM l. 696–706) uses MQ Prop 4.3 via Lemma 3.4.

`lmNestCanonLeaf`: with the canonical decompositions `exists_lmRep_zbExt`, the increments
`D = nestIncr r G λ` (`L3_4M2`), `𝓕_j = σ(D_0, …, D_j)` (`nestF`), the independence and
centring clauses (`L3_4M5`) and the telescoping identity (`sum_nestFun`) with
`d_j = nestFun r g λ j`. Hence `lmLem3_1a`, `lmLem3_1b` (via `lmLem3_1a_of_canon'`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric.LM

open Blueprint MarkovGauss MarkovNorm

lemma integrable_harm_mul_test {g : ℂ → ℝ} (hg : HarmonicOnNhd g (ball (0 : ℂ) 1))
    (φ : TestOn (ballO (0 : ℂ) 1)) : Integrable (fun x => g x * φ x) := by
  have hsub : tsupport (φ : ℂ → ℝ) ⊆ ball (0 : ℂ) 1 := fun x hx => φ.tsupport_subset hx
  have hc : ContinuousOn (fun x => g x * φ x) (tsupport (φ : ℂ → ℝ)) :=
    (hg.contDiffOn.continuousOn.mono hsub).mul φ.continuous.continuousOn
  rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport (φ : ℂ → ℝ))
    fun x hx => subset_tsupport _ fun h0 => hx (by simp [h0])]
  exact hc.integrableOn_compact φ.hasCompactSupport

/-- the representation of `D_{j+1}` on `B_1` -/
lemma restrictTo_nestIncr_succ {Ω : Type} (r : ℕ → ℝ) (G : ℕ → Ω → DistC) (lam : ℕ → Ω → ℝ)
    (j : ℕ) (ω : Ω) {g g' : ℂ → ℝ} (hg : HarmonicOnNhd g (ball (0 : ℂ) 1))
    (hgrep : ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (G j ω) φ = ∫ x, g x * φ x)
    (hg' : HarmonicOnNhd g' (ball (0 : ℂ) 1))
    (hg'rep : ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (G (j + 1) ω) φ = ∫ x, g' x * φ x)
    (hρ0 : 0 < r (j + 1) / r j) (hρ1 : r (j + 1) / r j ≤ 1) (φ : TestOn (ballO 0 1)) :
    restrictTo (ballO 0 1) (nestIncr r G lam (j + 1) ω) φ =
      ∫ x, (g' x - g ((r (j + 1) / r j) • x) + lam j ω) * φ x := by
  have hI1 := integrable_harm_mul_test hg' φ
  have hI2 := integrable_harm_mul_test (harmonicOnNhd_comp_smul hg hρ0 hρ1) φ
  have hI3 : Integrable (fun x => lam j ω * φ x) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).const_mul _
  have e : ∀ x, (g' x - g ((r (j + 1) / r j) • x) + lam j ω) * φ x =
      g' x * φ x - g ((r (j + 1) / r j) • x) * φ x + lam j ω * φ x := fun x => by ring
  simp_rw [e]
  rw [integral_add (f := fun x => g' x * φ x - g ((r (j + 1) / r j) • x) * φ x)
    (g := fun x => lam j ω * φ x) (hI1.sub hI2) hI3, integral_sub hI1 hI2, integral_const_mul,
    ← hg'rep, ← restrictTo_affineComp_rep hgrep hρ0 hρ1, restrictTo_apply_eq, restrictTo_apply_eq,
    restrictTo_apply_eq]
  simp only [nestIncr]
  rw [GFFInv.addConst_apply]
  have e2 : ∫ x, (TestFunction.monoCLM ℝ φ : TestC) x = ∫ x, φ x :=
    integral_congr_ae (Eventually.of_forall fun x => monoCLM_apply_eq φ x)
  rw [e2, mul_comm (∫ x, φ x)]
  rfl

/-- **The canonical nesting** (MQ l. 693–700) -/
theorem lmNestCanonLeaf (s₁ : ℝ) : LMNestCanonLeaf s₁ := by
  intro Ω mΩ P _ h hh r hr0 hrA _
  choose hh0 hz G hrep hzm hzae hzv using fun k => exists_lmRep_zbExt hh.1 (hr0 k)
  set lamv : ℕ → Lp ℝ 2 P := fun j => nKappa hh hr0 j - nProj hh hr0 j (nKappa hh hr0 j)
  set lam : ℕ → Ω → ℝ := fun j => (Lp.aestronglyMeasurable (lamv j)).aemeasurable.mk _
  have hlm : ∀ j, Measurable (lam j) := fun j =>
    (Lp.aestronglyMeasurable _).aemeasurable.measurable_mk
  have hlam : ∀ j, lam j =ᵐ[P] (lamv j : Ω → ℝ) := fun j =>
    ((Lp.aestronglyMeasurable _).aemeasurable.ae_eq_mk).symm
  set D := nestIncr r G lam
  have hDm : ∀ j, Measurable (D j) := measurable_nestIncr r (measurable_G hh hr0 hrep) hlm
  refine ⟨nestF D, D, nestF_mono D, nestF_le hDm, measurable_nestF D,
    fun j => indep_nestIncr_succ hh hr0 hrA hrep hzae hlam j,
    fun j => indepFun_nestIncr_compl hh hr0 hrA hrep hzae hlam j,
    fun j φ => integral_nestIncr_compl hh hr0 hrep hzae hlam j φ, hh0, hz, G, hrep, fun k => ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ j, (∃ g : ℂ → ℝ, HarmonicOnNhd g (ball (0 : ℂ) 1) ∧
      ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) (hh0 j ω) φ = ∫ x, g x * φ x) ∧
      hh0 j ω = G j ω :=
    ae_all_iff.2 fun j => (hrep j).2.2.2.1.and (hrep j).2.1
  filter_upwards [hall] with ω hω
  choose g hg hgrep using fun j => (hω j).1
  have hgrep' : ∀ j (φ : TestOn (ballO 0 1)),
      restrictTo (ballO 0 1) (G j ω) φ = ∫ x, g j x * φ x := fun j φ => by
    rw [← (hω j).2]; exact hgrep j φ
  refine ⟨g k, hg k, hgrep' k, nestFun r g (fun j => lam j ω), fun j _ => ?_,
    fun u _ => sum_nestFun hr0 g _ k u⟩
  cases j with
  | zero => exact ⟨hg 0, hgrep' 0⟩
  | succ j =>
    have hρ0 := ratio_pos hr0 j
    have hρ1 : r (j + 1) / r j ≤ 1 := (div_le_one (hr0 j)).2 (hrA (Nat.le_succ j))
    exact ⟨((hg (j + 1)).sub (harmonicOnNhd_comp_smul (hg j) hρ0 hρ1)).add
      (harmonicOnNhd_const _), fun φ => restrictTo_nestIncr_succ r G lam j ω (hg j) (hgrep' j)
      (hg (j + 1)) (hgrep' (j + 1)) hρ0 hρ1 φ⟩

/-- **LM Lemma 3.1 (1)** (`N = 0`) -/
theorem lmLem3_1a : LMLem3_1a :=
  lmLem3_1a_of_canon' fun s₁ _ _ => lmNestCanonLeaf s₁

end LQGMetric.LM
