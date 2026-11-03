/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer2B at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2S

/-!
# The germ step: cutoffs and Dirichlet-pairing identities (task P2-MKD2)

Tools for node (b) of `handoff/P2-MKD.md` (`mem_range_cmIso_of_orth`):

* cutoffs in the distance `d(x) = dist(x, ℂ ∖ V)` (`exists_dcut`): smooth `θ` with values in
  `[0, 1]`, `θ ≠ 0 ⇒ a < d`, `θ = 1` where `d ≥ b`; for bounded `V` it lies in `C_c^∞(V)`
  (`dcut_mem_zeroSpace`), and `∇θ(x) ≠ 0 ⇒ a ≤ d(x) ≤ b` (`dcut_fderiv_ne_zero`);
* the inner products of whole-plane Dirichlet pairings: `norm_cmLin_sq`
  (`‖(h, f)_∇‖² = (f, f)_∇`), `inner_cmLin_top` (`⟪(h, f)_∇, (h, g)_∇⟫ = (2π)⁻¹ ∫ ∇f·∇g`),
  `inner_cmLin_pair` (`⟪(h, f)_∇, ⟨h, ψ⟩⟫ = ∫ ψ f`), `norm_pair_sq` (`‖⟨h, ψ⟩‖² = logCov ψ ψ`).

Sources: Sheffield math/0312099 §2.6 (Thm 2.17 and the paragraph after it); Berestycki–Powell
arXiv:2404.16642 Thm 1.52 / Lemma 1.53 (`H₀¹(D) = Supp(U) ⊕ Harm(U)`, proof by cutoff).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace Laplacian
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovGermVer

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm Blueprint QuantumZipper
  QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-! ## Cutoffs in the distance to the complement -/

/-- `d(x) = dist(x, ℂ ∖ V)` -/
abbrev dV (V : Set ℂ) (x : ℂ) : ℝ := infDist x Vᶜ

lemma continuous_dV (V : Set ℂ) : Continuous (dV V) := continuous_infDist_pt _

lemma compl_nonempty_of_bdd {V : Set ℂ} (hVb : Bornology.IsBounded V) : (Vᶜ).Nonempty := by
  obtain ⟨R, hR⟩ := hVb.subset_closedBall (0 : ℂ)
  refine ⟨((|R| + 1 : ℝ) : ℂ), fun hx => ?_⟩
  have := mem_closedBall_zero_iff.1 (hR hx)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
  linarith [le_abs_self R]

lemma mem_of_dV_pos {V : Set ℂ} {x : ℂ} (hx : 0 < dV V x) : x ∈ V := by
  by_contra hxV
  rw [dV, infDist_zero_of_mem (show x ∈ Vᶜ from hxV)] at hx
  exact lt_irrefl _ hx

/-- a function vanishing where `d ≤ a` (`a > 0`) has compact support in `V` (bounded `V`) -/
lemma tsupport_sub_of_dV {V : Set ℂ} (hVb : Bornology.IsBounded V) {a : ℝ} (ha : 0 < a)
    {θ : ℂ → ℝ} (hθ : ∀ x, θ x ≠ 0 → a < dV V x) :
    HasCompactSupport θ ∧ tsupport θ ⊆ {x | a ≤ dV V x} ∧ tsupport θ ⊆ V := by
  have hcl : IsClosed {x | a ≤ dV V x} := isClosed_le continuous_const (continuous_dV V)
  have hsub : tsupport θ ⊆ {x | a ≤ dV V x} :=
    closure_minimal (fun x hx => (hθ x hx).le) hcl
  have hV : {x | a ≤ dV V x} ⊆ V := fun x hx => mem_of_dV_pos (ha.trans_le hx)
  exact ⟨(isCompact_of_isClosed_isBounded hcl (hVb.subset hV)).of_isClosed_subset
    isClosed_closure hsub, hsub, hsub.trans hV⟩

/-- smooth cutoffs in `d` -/
lemma exists_dcut (V : Set ℂ) {a b : ℝ} (hab : a < b) :
    ∃ θ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧ (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
      (∀ x, θ x ≠ 0 → a < dV V x) ∧ (∀ x, b ≤ dV V x → θ x = 1) := by
  obtain ⟨θ, hs, hr, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (isOpen_lt continuous_const (continuous_dV V))
    (isClosed_le continuous_const (continuous_dV V))
    (fun x (hx : b ≤ dV V x) => show a < dV V x from hab.trans_le hx)
  refine ⟨θ, hs, fun x => hr (mem_range_self x), fun x hx => ?_, fun x hx => (h1 x).1 hx⟩
  have : x ∈ Function.support θ := hx
  rw [hsupp] at this; exact this

/-- `∇θ(x) ≠ 0 ⇒ a ≤ d(x) ≤ b` -/
lemma dcut_fderiv_ne_zero {V : Set ℂ} {a b : ℝ} {θ : ℂ → ℝ}
    (hθ0 : ∀ x, θ x ≠ 0 → a < dV V x) (hθ1 : ∀ x, b ≤ dV V x → θ x = 1) {x : ℂ}
    (hx : fderiv ℝ θ x ≠ 0) : a ≤ dV V x ∧ dV V x ≤ b := by
  constructor
  · by_contra hlt
    push Not at hlt
    apply hx
    have hev : θ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt (continuous_dV V) continuous_const).mem_nhds hlt] with y hy
      by_contra hne
      exact absurd (hθ0 y hne) (not_lt.2 (le_of_lt hy))
    rw [hev.fderiv_eq]; exact fderiv_const_apply _
  · by_contra hlt
    push Not at hlt
    apply hx
    have hev : θ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const (continuous_dV V)).mem_nhds hlt] with y hy
      exact hθ1 y (le_of_lt hy)
    rw [hev.fderiv_eq]; exact fderiv_const_apply _

/-- `d(x) < ε ⇒ x ∈ B_ε(ℂ ∖ V)` -/
lemma mem_nbhdO_of_dV {V : Set ℂ} (hVb : Bornology.IsBounded V) {ε : ℝ} {x : ℂ}
    (hx : dV V x < ε) : x ∈ (nbhdO ε Vᶜ : Set ℂ) :=
  (mem_thickening_iff_infDist_lt (compl_nonempty_of_bdd hVb)).2 hx

/-! ## Inner products of whole-plane Dirichlet pairings -/

lemma norm_cmLin_sq (hh : IsWholePlaneGFF h P) (U : Opens ℂ) (f : zsSub U) :
    ‖cmLin hh U f‖ ^ 2 = gradEnergy f.1 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [cmLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_toLp_eq_cov _ _ (centered_pairProc hh _)]
  exact (hh.covariance_eq _ _).trans (logCov_cmTest_cmTest _)

lemma inner_cmLin_pair (hh : IsWholePlaneGFF h P) (U : Opens ℂ) (f : zsSub U) (ψ : TestC0) :
    ⟪cmLin hh U f, (memLp_pair hh ψ).toLp (pairProc h ψ)⟫ = ∫ x, ψ.1 x * f.1 x := by
  rw [← cmIso_gradLin, inner_cmIso_gradLin]

lemma norm_pair_sq (hh : IsWholePlaneGFF h P) (ψ : TestC0) :
    ‖(memLp_pair hh ψ).toLp (pairProc h ψ)‖ ^ 2 = logCov ψ.1 ψ.1 := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_eq_cov _ _ (centered_pairProc hh _)]
  exact hh.covariance_eq ψ ψ

lemma inner_cmLin_top (hh : IsWholePlaneGFF h P) (f g : zsSub ((⊤ : Opens ℂ) : Set ℂ)) :
    ⟪cmLin hh ⊤ f, cmLin hh ⊤ g⟫ = (2 * Real.pi)⁻¹ * ∫ z, gradInner f.1 g.1 z := by
  have e : cmLin hh ⊤ g = (memLp_pair hh (cmTest0 (zsTest g.2))).toLp
      (pairProc h (cmTest0 (zsTest g.2))) := rfl
  rw [e, inner_cmLin_pair,
    integral_gradInner_eq_neg_integral_mul_laplacian (smooth_le f.2.1 1) (smooth_le g.2.1 2)
      g.2.2.1]
  have e2 : ∀ x, (cmTest0 (zsTest g.2)).1 x * f.1 x = -(2 * Real.pi)⁻¹ * (f.1 x * Δ g.1 x) :=
    fun x => by
      change cmTest (zsTest g.2) x * f.1 x = _
      rw [cmTest_apply]
      have : (⇑(zsTest g.2) : ℂ → ℝ) = g.1 := rfl
      rw [this]; ring
  simp_rw [e2]
  rw [integral_const_mul]; ring

end MarkovGermVer
end LQGMetric
