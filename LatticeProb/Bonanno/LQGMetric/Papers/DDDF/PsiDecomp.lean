/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.PsiDecomp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField

/-!
# Scale decomposition `φ_{0,n} − ψ_{0,n} = Σ_{k ≤ n} D_k` (task P2-DDDFPSI; DDDF Prop 5)

DDDF (arXiv:1904.08021, `tightness.tex` l. 431) and DZZ (arXiv:1807.00422, l. 570–573, the
display before "Combined with (2.40) and (2.41)"): `φ_{0,n} − ψ_{0,n} = Σ_{k=1}^n D_k`, hence
`sup_n ‖φ_{0,n} − ψ_{0,n}‖_{[0,1]²} ≤ Σ_k ‖D_k‖_{[0,1]²}`.

* `ae_phiMN_sub_psiMN_eq_sum`: almost surely, for all `n` and all `x`,
  `φ_{0,n}(x) − ψ_{0,n}(x) = Σ_{m<n} D_{m+1}(x)` (continuous versions; a.s. identity on a
  countable dense set by `phi_add_ae`, `psi_add_ae`, `phi_sub_psi_self_ae`, then continuity).
* `ae_XAB_le_tsum`: a.s. `X_{a,b} ≤ Σ_m sup_{R_{a,b}} |D_{m+1}|` (in `[0, ∞]`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- Pointwise a.s. form of the decomposition, for fixed `n` and `x`. -/
theorem phiMN_sub_psiMN_ae_eq_sum (hW : IsWhiteNoise P W) (Q : PsiParams) (n : ℕ) (x : ℂ) :
    (fun ω => phiMN W P 0 n x ω - psiMN Q W P 0 n x ω) =ᵐ[P]
      fun ω => ∑ m ∈ Finset.range n, deltaM Q W P m x ω := by
  induction n with
  | zero =>
    have h1 := (isPhiVersion_phiMN hW (le_refl 0)).ae_eq x
    have h2 := (isPsiVersion_psiMN (Q := Q) hW (le_refl 0)).ae_eq x
    have h3 := phi_sub_psi_self_ae hW Q (a := (2 : ℝ)⁻¹ ^ 0) (by positivity) x
    filter_upwards [h1, h2, h3] with ω e1 e2 e3
    simp only [Pi.zero_apply] at e3
    simp only [Finset.range_zero, Finset.sum_empty]
    rw [e1, e2]; exact e3
  | succ n ih =>
    have hn : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (n + 1) := by positivity
    have hab : (2 : ℝ)⁻¹ ^ (n + 1) ≤ (2 : ℝ)⁻¹ ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
    have hbc : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 0 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.zero_le n)
    have a1 := (isPhiVersion_phiMN hW (Nat.zero_le (n + 1))).ae_eq x
    have a2 := (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le (n + 1))).ae_eq x
    have b1 := (isPhiVersion_phiMN hW (Nat.zero_le n)).ae_eq x
    have b2 := (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).ae_eq x
    have c1 := (isPhiVersion_phiMN hW (Nat.le_succ n)).ae_eq x
    have c2 := (isPsiVersion_psiMN (Q := Q) hW (Nat.le_succ n)).ae_eq x
    have d1 := phi_add_ae hW hn hab hbc x
    have d2 := psi_add_ae hW Q hn hab hbc x
    filter_upwards [ih, a1, a2, b1, b2, c1, c2, d1, d2] with ω h a1 a2 b1 b2 c1 c2 d1 d2
    rw [Finset.sum_range_succ, ← h]
    simp only [deltaM]
    rw [a1, a2, b1, b2, c1, c2, d1, d2]
    ring

/-- **The decomposition, almost surely for all `n` and `x`.** -/
theorem ae_phiMN_sub_psiMN_eq_sum (hW : IsWhiteNoise P W) (Q : PsiParams) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ x : ℂ,
      phiMN W P 0 n x ω - psiMN Q W P 0 n x ω = ∑ m ∈ Finset.range n, deltaM Q W P m x ω := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable s := hsc.to_subtype
  have h : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ x : s,
      phiMN W P 0 n x ω - psiMN Q W P 0 n x ω = ∑ m ∈ Finset.range n, deltaM Q W P m x ω := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro x
    exact phiMN_sub_psiMN_ae_eq_sum hW Q n x
  filter_upwards [h] with ω hω n
  have hf : Continuous fun x => phiMN W P 0 n x ω - psiMN Q W P 0 n x ω :=
    ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω).sub
      ((isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).cont ω)
  have hg : Continuous fun x => ∑ m ∈ Finset.range n, deltaM Q W P m x ω :=
    continuous_finset_sum _ fun m _ => continuous_deltaM hW Q m ω
  intro x
  exact congrFun (Continuous.ext_on hsd hf hg fun y hy => hω n ⟨y, hy⟩) x

/-- `sup_S |D_{m+1}|` in `[0, ∞]`. -/
def supDelta (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (S : Set ℂ) (m : ℕ)
    (ω : Ω) : ℝ≥0∞ :=
  ⨆ x ∈ S, ENNReal.ofReal |deltaM Q W P m x ω|

/-- **`X_{a,b} ≤ Σ_k ‖D_k‖_{R_{a,b}}` almost surely.** -/
theorem ae_XAB_le_tsum (hW : IsWhiteNoise P W) (Q : PsiParams) (a b : ℝ) :
    ∀ᵐ ω ∂P, XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b ≤
      ∑' m, supDelta Q W P (rectAB a b).toSet m ω := by
  filter_upwards [ae_phiMN_sub_psiMN_eq_sum hW Q] with ω hω
  refine iSup_le fun n => iSup₂_le fun x hx => ?_
  rw [hω n x]
  calc ENNReal.ofReal |∑ m ∈ Finset.range n, deltaM Q W P m x ω|
      ≤ ENNReal.ofReal (∑ m ∈ Finset.range n, |deltaM Q W P m x ω|) :=
        ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ m ∈ Finset.range n, ENNReal.ofReal |deltaM Q W P m x ω| :=
        ENNReal.ofReal_sum_of_nonneg fun m _ => abs_nonneg _
    _ ≤ ∑ m ∈ Finset.range n, supDelta Q W P (rectAB a b).toSet m ω :=
        Finset.sum_le_sum fun m _ => le_iSup₂_of_le (f := fun x (_ : x ∈ (rectAB a b).toSet) =>
          ENNReal.ofReal |deltaM Q W P m x ω|) x hx le_rfl
    _ ≤ ∑' m, supDelta Q W P (rectAB a b).toSet m ω := ENNReal.sum_le_tsum _

end DDDF
end LQGMetric
