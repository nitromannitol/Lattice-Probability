/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Var.Subadditive at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Var.Blocks
import LatticeProb.Bonanno.HigherDimLFPP.Var.SubadditiveAux

/-!
# Subadditivity (2.6)

`Ag E (n + r) ≤ Ag E n + Ag E r` in `EReal`, for all `n, r` (HA1 D5, HA1-F6/F7).  For a finite
family `F ⊆ V_{n+r}(E)`, each `f` splits into its coarse interpolant `g ∈ V_n(E)` and the `2ⁿ`
rescaled fine pieces in `V_r(E)`; the canonical distances satisfy
`∫‖f - f'‖ ≤ ∫‖g - g'‖ + ∑ₖ 2⁻²ⁿ ∫‖uₖ - u'ₖ‖` and the energy splits exactly.  Sudakov–Fernique
compares the family with the independent sum of the coarse process and the `2ⁿ` fine processes
scaled by `2⁻ⁿ` (`gEM_le_sum_blocks`); the fine part contributes `2ⁿ · 2⁻ⁿ A_r = A_r`.

Ported from `LQGDimension/Section2/Subadditive.lean` (`Subadd.main_bound`, `aSubadditiveE_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Var

open LQGDimension (gaussianExpectedMax)

section Dist

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical distance (2.2) in kernel form:
`gCov f f + gCov g g - 2 gCov f g = 2π ∫₀¹ ‖f - g‖`. -/
lemma gCov_dist_formula {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) :
    gCov f f + gCov g g - 2 * gCov f g = 2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖f x - g x‖ := by
  have ia : IntervalIntegrable (fun x => ‖f x‖) volume 0 1 := hf.norm.intervalIntegrable 0 1
  have ib : IntervalIntegrable (fun x => ‖g x‖) volume 0 1 := hg.norm.intervalIntegrable 0 1
  have iab : IntervalIntegrable (fun x => ‖f x - g x‖) volume 0 1 :=
    (hf.sub hg).norm.intervalIntegrable 0 1
  have e2 : gCov f g = Real.pi * ((∫ x in (0 : ℝ)..1, ‖f x‖) + (∫ x in (0 : ℝ)..1, ‖g x‖) -
      ∫ x in (0 : ℝ)..1, ‖f x - g x‖) := by
    unfold gCov
    rw [intervalIntegral.integral_sub (ia.add ib) iab, intervalIntegral.integral_add ia ib]
  rw [gCov_self, gCov_self, e2]
  ring

end Dist

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The main estimate of (2.6)** on one finite family (port of `Subadd.main_bound`). -/
theorem gEM_subadd_bound {n r : ℕ} (F : Finset (Vg E (n + r))) (A B : ℝ)
    (hA : ∀ G : Finset (Vg E n), gaussianExpectedMax G (fun f g => gCov (f : ℝ → E) g)
      (fun f => -energy (f : ℝ → E)) ≤ A)
    (hB : ∀ G : Finset (Vg E r), gaussianExpectedMax G (fun f g => gCov (f : ℝ → E) g)
      (fun f => -energy (f : ℝ → E)) ≤ B) :
    gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g) (fun f => -energy (f : ℝ → E)) ≤
      A + B := by
  classical
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  let p : Option (Fin (2 ^ n)) → ℕ := fun o => Option.elim o n (fun _ => r)
  let P : Option (Fin (2 ^ n)) → Vg E (n + r) → ℝ → E := fun o f =>
    Option.elim o (coarse n (f : ℝ → E)) (fun k => fine n (f : ℝ → E) k)
  let s : Option (Fin (2 ^ n)) → ℝ := fun o => Option.elim o 1 (fun _ => 1 / (2 : ℝ) ^ n)
  let Bk : Option (Fin (2 ^ n)) → ℝ := fun o => Option.elim o A (fun _ => B)
  have hP : ∀ o f, P o f ∈ Vg E (p o) := by
    intro o f
    cases o with
    | none => exact coarse_mem n f.2.1 f.2.2.1 f.2.2.2.1
    | some k => exact fine_mem f.2 k.2
  have hs : ∀ o, 0 ≤ s o := by
    intro o
    cases o with
    | none => exact zero_le_one
    | some k => exact div_nonneg zero_le_one hN.le
  have hb : ∀ f ∈ F, -energy (f : ℝ → E) = ∑ o, s o * -energy (P o f) := by
    intro f _
    rw [Fintype.sum_option]
    simp only [s, P, Option.elim]
    rw [Fin.sum_univ_eq_sum_range (fun k => 1 / (2 : ℝ) ^ n * -energy (fine n (f : ℝ → E) k))
      (2 ^ n), energy_decomp f.2]
    simp only [mul_neg, Finset.sum_neg_distrib]
    ring
  have hdist : ∀ f ∈ F, ∀ g ∈ F, gCov (f : ℝ → E) f + gCov (g : ℝ → E) g -
      2 * gCov (f : ℝ → E) g ≤
      ∑ o, s o ^ 2 * (2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖P o f x - P o g x‖) := by
    intro f _ g _
    rw [gCov_dist_formula (Vg_continuous f.2) (Vg_continuous g.2), Fintype.sum_option]
    simp only [s, P, Option.elim]
    rw [Fin.sum_univ_eq_sum_range (fun k => (1 / (2 : ℝ) ^ n) ^ 2 * (2 * Real.pi *
      ∫ x in (0 : ℝ)..1, ‖fine n (f : ℝ → E) k x - fine n (g : ℝ → E) k x‖)) (2 ^ n)]
    have hl1 := l1_decomp (n := n) (m := r) f.2 g.2
    have := mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    refine this.trans (le_of_eq ?_)
    rw [mul_add, Finset.mul_sum, one_pow, one_mul]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hBk : ∀ o (G : Finset (Vg E (p o))), gaussianExpectedMax G
      (fun f g => gCov (f : ℝ → E) g) (fun f => -energy (f : ℝ → E)) ≤ Bk o := by
    intro o G
    cases o with
    | none => exact hA G
    | some k => exact hB G
  have key := gEM_le_sum_blocks F (fun f g => gCov (f : ℝ → E) g) (gCov_psdOn_Vg (n + r) F)
    (fun f => -energy (f : ℝ → E)) p P hP s hs hb hdist Bk hBk
  refine key.trans (le_of_eq ?_)
  rw [Fintype.sum_option]
  simp only [s, Bk, Option.elim, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  field_simp

/-- **Subadditivity (2.6)** in `[0, ∞]`, for all `n, r ≥ 0`. -/
theorem Ag_subadditive (n r : ℕ) : Ag E (n + r) ≤ Ag E n + Ag E r := by
  have hnb := Ag_ne_bot (E := E) n
  have hrb := Ag_ne_bot (E := E) r
  by_cases hn : Ag E n = ⊤
  · rw [hn, EReal.top_add_of_ne_bot hrb]; exact le_top
  by_cases hr : Ag E r = ⊤
  · rw [hr, EReal.add_top_of_ne_bot hnb]; exact le_top
  rw [← Ag_eq_coe_toReal hn, ← Ag_eq_coe_toReal hr, ← EReal.coe_add]
  refine Ag_le_of_forall fun F => ?_
  exact EReal.coe_le_coe_iff.2 (gEM_subadd_bound F _ _ (gEM_le_toReal hn) (gEM_le_toReal hr))

end HigherDimLFPP.Var
