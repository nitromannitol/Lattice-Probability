/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.PathPiece at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Topology.Piecewise

/-!
# Piecewise C¹ paths: breakpoint form, affine reparametrization, reversal, concatenation

Task P2-LFPP (WP-45 / DFGPS.S5 groundwork). The paths of GM (1.4)
(`literature/src/1905.00383/uniqueness-final.tex` l. 216–220, "piecewise continuously
differentiable paths") are `IsPiecewiseC1Path` (Statement/LFPP.lean, FROZEN). To build new paths
(sub-paths, reversed paths, concatenations, segments) we use an equivalent *breakpoint* form
`PcwC1 P F`: `P` is C¹ on every closed subinterval of `[0,1]` whose interior misses the finite
set `F`. Own elementary arguments (standard facts used implicitly by GM and DFGPS §2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

/-- breakpoint form of "piecewise C¹ on `[0,1]`" -/
def PcwC1 (P : ℝ → ℂ) (F : Finset ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → (∀ x ∈ F, x ∉ Ioo a b) → ContDiffOn ℝ 1 P (Icc a b)

theorem pcwC1_of_partition {P : ℝ → ℂ} {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1)
    (hC : ∀ i : Fin k, ContDiffOn ℝ 1 P (Icc (t i.castSucc) (t i.succ))) :
    PcwC1 P (Finset.univ.image t) := by
  classical
  intro a b ha hab hb hF
  set S := Finset.univ.filter fun j => t j ≤ a
  have hne : S.Nonempty := ⟨0, by simp [S, ht0, ha]⟩
  have hj : t (S.max' hne) ≤ a := (Finset.mem_filter.1 (S.max'_mem hne)).2
  have hjl : S.max' hne ≠ Fin.last k := by
    intro h; rw [h, htk] at hj; linarith
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hjl
  have hsucc : a < t i.succ := by
    by_contra hcon
    rw [not_lt] at hcon
    have : i.succ ≤ S.max' hne := S.le_max' _ (by simp [S, hcon])
    rw [← hi] at this
    exact absurd this (not_le.2 Fin.castSucc_lt_succ)
  have hb' : b ≤ t i.succ := by
    by_contra hcon
    rw [not_le] at hcon
    exact hF _ (Finset.mem_image_of_mem t (Finset.mem_univ _)) ⟨hsucc, hcon⟩
  exact (hC i).mono (Icc_subset_Icc (by rw [hi]; exact hj) hb')

theorem partition_of_pcwC1 {P : ℝ → ℂ} {F : Finset ℝ} (hP : PcwC1 P F) :
    ∃ (k : ℕ) (t : Fin (k + 1) → ℝ), StrictMono t ∧ t 0 = 0 ∧
      t (Fin.last k) = 1 ∧ ∀ i : Fin k, ContDiffOn ℝ 1 P (Icc (t i.castSucc) (t i.succ)) := by
  classical
  set G : Finset ℝ := insert 0 (insert 1 (F.filter fun x => x ∈ Ioo (0 : ℝ) 1))
  have h0 : (0 : ℝ) ∈ G := by simp [G]
  have h1 : (1 : ℝ) ∈ G := by simp [G]
  have hsub : ∀ x ∈ G, x ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    simp only [G, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨_, h⟩
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact Ioo_subset_Icc_self h
  have hcard : 2 ≤ G.card := by
    have hs : ({0, 1} : Finset ℝ) ⊆ G := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have := Finset.card_le_card hs
    rwa [Finset.card_pair zero_ne_one] at this
  obtain ⟨k, hk⟩ : ∃ k, G.card = k + 1 := ⟨G.card - 1, by omega⟩
  set t := G.orderEmbOfFin hk
  have htm : ∀ i, t i ∈ G := fun i => G.orderEmbOfFin_mem hk i
  refine ⟨k, t, t.strictMono, ?_, ?_, ?_⟩
  · have := Finset.orderEmbOfFin_zero hk (Nat.succ_pos k)
    rw [show (0 : Fin (k + 1)) = ⟨0, Nat.succ_pos k⟩ from rfl, this]
    exact le_antisymm (G.min'_le 0 h0) (hsub _ (G.min'_mem _)).1
  · have := Finset.orderEmbOfFin_last hk (Nat.succ_pos k)
    rw [show (Fin.last k) = ⟨k + 1 - 1, Nat.sub_lt (Nat.succ_pos k) (Nat.succ_pos 0)⟩ from
      Fin.ext (by simp), this]
    exact le_antisymm (hsub _ (G.max'_mem _)).2 (G.le_max' 1 h1)
  · intro i
    have ha := hsub _ (htm i.castSucc)
    have hb := hsub _ (htm i.succ)
    refine hP _ _ ha.1 (t.strictMono Fin.castSucc_lt_succ) hb.2 fun x hxF hx => ?_
    have hxG : x ∈ G := by
      simp only [G, Finset.mem_insert, Finset.mem_filter]
      exact Or.inr (Or.inr ⟨hxF, ha.1.trans_lt hx.1, hx.2.trans_le hb.2⟩)
    have hr : x ∈ Set.range t := by rw [Finset.range_orderEmbOfFin]; exact hxG
    obtain ⟨j, rfl⟩ := hr
    have hj1 : i.castSucc < j := t.lt_iff_lt.1 hx.1
    have hj2 : j < i.succ := t.lt_iff_lt.1 hx.2
    exact absurd hj2 (not_lt.2 (Fin.castSucc_lt_iff_succ_le.1 hj1))

theorem _root_.LQGMetric.IsPiecewiseC1Path.exists_pcwC1 {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w) :
    ∃ F, PcwC1 P F := by
  classical
  obtain ⟨k, t, _, ht0, htk, hC⟩ := hP.piecewise
  exact ⟨_, pcwC1_of_partition ht0 htk hC⟩

theorem _root_.LQGMetric.IsPiecewiseC1Path.of_pcwC1 {P : ℝ → ℂ} {z w : ℂ} {F : Finset ℝ} (h0 : P 0 = z)
    (h1 : P 1 = w) (hc : ContinuousOn P (Icc 0 1)) (hP : PcwC1 P F) :
    IsPiecewiseC1Path P z w :=
  ⟨h0, h1, hc, partition_of_pcwC1 hP⟩

/-! ### Affine reparametrizations -/

theorem contDiffOn_comp_affine {P : ℝ → ℂ} {a' b' c s : ℝ} {S : Set ℝ}
    (hP : ContDiffOn ℝ 1 P (Icc a' b')) (hS : MapsTo (fun u => c * u + s) S (Icc a' b')) :
    ContDiffOn ℝ 1 (fun u => P (c * u + s)) S :=
  hP.comp ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffOn hS

theorem deriv_comp_affine (P : ℝ → ℂ) (c s u : ℝ) :
    deriv (fun u => P (c * u + s)) u = c • deriv P (c * u + s) := by
  have := deriv_comp_mul_left (f := fun v => P (v + s)) (c := c) (x := u)
  simp only [deriv_comp_add_const] at this
  exact this

/-- **Change of variables for the LFPP integrand under an affine reparametrization.** -/
theorem setLIntegral_comp_affine (g : ℝ → ℝ≥0∞) {S : Set ℝ} (hS : MeasurableSet S) {c : ℝ}
    (hc : c ≠ 0) (s : ℝ) :
    ∫⁻ u in S, ENNReal.ofReal |c| * g (c * u + s) = ∫⁻ x in (fun u => c * u + s) '' S, g x := by
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hS (f' := fun _ => c)
    (fun u _ => by simpa using (((hasDerivAt_id u).const_mul c).add_const s).hasDerivWithinAt)]
  intro u _ v _ h
  simpa [hc] using h

/-- the LFPP integrand `e^{ξ φ(P t)} |P'(t)|` -/
def lenDens (ξ : ℝ) (φ : ℂ → ℝ) (P : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (ξ * φ (P t)) * ‖deriv P t‖)

theorem lfppLen_eq (ξ : ℝ) (φ : ℂ → ℝ) (P : ℝ → ℂ) :
    lfppLen ξ φ P = ∫⁻ t in Icc (0 : ℝ) 1, lenDens ξ φ P t := rfl

theorem lenDens_comp_affine (ξ : ℝ) (φ : ℂ → ℝ) (P : ℝ → ℂ) (c s u : ℝ) :
    lenDens ξ φ (fun u => P (c * u + s)) u =
      ENNReal.ofReal |c| * lenDens ξ φ P (c * u + s) := by
  unfold lenDens
  rw [deriv_comp_affine, norm_smul, Real.norm_eq_abs, ← ENNReal.ofReal_mul (abs_nonneg c)]
  congr 1
  ring

/-- LFPP length of `u ↦ P(c u + s)` on `[0,1]`. -/
theorem lfppLen_comp_affine (ξ : ℝ) (φ : ℂ → ℝ) (P : ℝ → ℂ) {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    lfppLen ξ φ (fun u => P (c * u + s)) =
      ∫⁻ x in (fun u => c * u + s) '' Icc 0 1, lenDens ξ φ P x := by
  rw [lfppLen_eq, ← setLIntegral_comp_affine _ measurableSet_Icc hc]
  exact setLIntegral_congr_fun measurableSet_Icc fun u _ => lenDens_comp_affine ξ φ P c s u

end LFPP
end LQGMetric
