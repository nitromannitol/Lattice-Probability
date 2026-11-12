/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.PathConcat at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps

/-!
# Concatenation of piecewise C¹ paths and additivity of the LFPP length

Task P2-LFPP. Used for the triangle inequality of `D^ε_h` (GM (1.4),
`uniqueness-final.tex` l. 216–220). Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

variable {ξ : ℝ} {φ : ℂ → ℝ}

/-- concatenation: `P(2u)` on `[0, 1/2]`, `R(2u - 1)` on `[1/2, 1]` -/
def concatPath (P R : ℝ → ℂ) (u : ℝ) : ℂ := if u ≤ 1 / 2 then P (2 * u + 0) else R (2 * u + -1)

theorem concatPath_eqOn_left (P R : ℝ → ℂ) :
    EqOn (concatPath P R) (fun u => P (2 * u + 0)) (Iic (1 / 2)) := fun _ hu => by
  simp only [concatPath, mem_Iic.1 hu, ite_true]

theorem concatPath_eqOn_right {P R : ℝ → ℂ} (h : P 1 = R 0) :
    EqOn (concatPath P R) (fun u => R (2 * u + -1)) (Ici (1 / 2)) := by
  intro u hu
  simp only [concatPath]
  split_ifs with h1
  · have : u = 1 / 2 := le_antisymm h1 hu
    subst this
    norm_num [h]
  · rfl

theorem isPiecewiseC1Path_concatPath {P R : ℝ → ℂ} {x y z : ℂ} (hP : IsPiecewiseC1Path P x y)
    (hR : IsPiecewiseC1Path R y z) : IsPiecewiseC1Path (concatPath P R) x z := by
  classical
  have hPR : P 1 = R 0 := hP.target.trans hR.source.symm
  obtain ⟨F, hF⟩ := hP.exists_pcwC1
  obtain ⟨G, hG⟩ := hR.exists_pcwC1
  have hL := concatPath_eqOn_left P R
  have hRt := concatPath_eqOn_right hPR
  refine IsPiecewiseC1Path.of_pcwC1
    (F := insert (1 / 2) (F.image (fun x => x / 2) ∪ G.image (fun x => (x + 1) / 2)))
    (by rw [hL (by norm_num : (0 : ℝ) ∈ Iic (1 / 2))]; simpa using hP.source)
    (by rw [hRt (by norm_num : (1 : ℝ) ∈ Ici (1 / 2))]; norm_num [hR.target]) ?_ ?_
  · have h1 : ContinuousOn (concatPath P R) (Icc 0 (1 / 2)) := by
      refine (hP.continuousOn.comp (by fun_prop) fun u hu => ?_).congr fun u hu => hL hu.2
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h2 : ContinuousOn (concatPath P R) (Icc (1 / 2) 1) := by
      refine (hR.continuousOn.comp (by fun_prop) fun u hu => ?_).congr fun u hu => hRt hu.1
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at this
  · intro a b ha hab hb hFa
    by_cases hb2 : b ≤ 1 / 2
    · refine (contDiffOn_comp_affine (c := 2) (s := 0) (hF (2 * a) (2 * b) (by linarith) (by linarith)
        (by linarith) fun x hx hxI => hFa (x / 2) (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)))
          ⟨by linarith [hxI.1], by linarith [hxI.2]⟩)
        fun u hu => by simp only [mem_Icc]; constructor <;> linarith [hu.1, hu.2]).congr
          fun u hu => ?_
      exact hL (hu.2.trans hb2)
    · have ha2 : 1 / 2 ≤ a := by
        by_contra h
        exact hFa _ (Finset.mem_insert_self _ _) ⟨by linarith, by linarith⟩
      refine (contDiffOn_comp_affine (c := 2) (s := -1) (hG (2 * a - 1) (2 * b - 1) (by linarith) (by linarith)
        (by linarith) fun x hx hxI => hFa ((x + 1) / 2) (Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)))
          ⟨by linarith [hxI.1], by linarith [hxI.2]⟩)
        fun u hu => by simp only [mem_Icc]; constructor <;> linarith [hu.1, hu.2]).congr
          fun u hu => ?_
      exact hRt (ha2.trans hu.1)

theorem image_two_mul_Ioo (s c d : ℝ) :
    (fun u : ℝ => 2 * u + s) '' Ioo c d = Ioo (2 * c + s) (2 * d + s) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · intro hx
    exact ⟨(x - s) / 2, ⟨by linarith [hx.1], by linarith [hx.2]⟩, by ring⟩

/-- **Additivity of the LFPP length under concatenation.** -/
theorem lfppLen_concatPath {P R : ℝ → ℂ} (hPR : P 1 = R 0) :
    lfppLen ξ φ (concatPath P R) = lfppLen ξ φ P + lfppLen ξ φ R := by
  have hL : ∫⁻ u in Ioo (0 : ℝ) (1 / 2), lenDens ξ φ (concatPath P R) u = lfppLen ξ φ P := by
    rw [setLIntegral_congr_fun measurableSet_Ioo fun u hu => lenDens_congr_nhds
      (Filter.eventuallyEq_of_mem (Iio_mem_nhds hu.2)
        fun v hv => concatPath_eqOn_left P R (mem_Iic.2 (le_of_lt hv))),
      setLIntegral_congr_fun measurableSet_Ioo fun u _ => lenDens_comp_affine ξ φ P 2 0 u]
    have := setLIntegral_comp_affine (lenDens ξ φ P) measurableSet_Ioo (by norm_num : (2 : ℝ) ≠ 0)
      0 (S := Ioo 0 (1 / 2))
    rw [this, image_two_mul_Ioo, lfppLen_eq]
    norm_num
    exact setLIntegral_congr Ioo_ae_eq_Icc
  have hR : ∫⁻ u in Ioo (1 / 2 : ℝ) 1, lenDens ξ φ (concatPath P R) u = lfppLen ξ φ R := by
    rw [setLIntegral_congr_fun measurableSet_Ioo fun u hu => lenDens_congr_nhds
      (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hu.1)
        fun v hv => concatPath_eqOn_right hPR (mem_Ici.2 (le_of_lt hv))),
      setLIntegral_congr_fun measurableSet_Ioo fun u _ => lenDens_comp_affine ξ φ R 2 (-1) u]
    have := setLIntegral_comp_affine (lenDens ξ φ R) measurableSet_Ioo (by norm_num : (2 : ℝ) ≠ 0)
      (-1) (S := Ioo (1 / 2) 1)
    rw [this, image_two_mul_Ioo, lfppLen_eq]
    norm_num
    exact setLIntegral_congr Ioo_ae_eq_Icc
  rw [lfppLen_eq, ← Icc_union_Ioc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num),
    lintegral_union measurableSet_Ioc ((Iic_disjoint_Ioi le_rfl).mono Icc_subset_Iic_self Ioc_subset_Ioi_self),
    ← setLIntegral_congr (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1 / 2)),
    ← setLIntegral_congr (Ioo_ae_eq_Ioc (a := (1 / 2 : ℝ)) (b := 1)), hL, hR]

end LFPP
end LQGMetric
