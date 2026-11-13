/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P8Lattice at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P8Charge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P7Compare2D
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFDistance
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.AnnulusGeometry
import Mathlib.Combinatorics.SimpleGraph.Paths

 













set_option autoImplicit false
noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.QPos.P8

open P7

 

 
def rnd (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

lemma abs_rnd_sub (x : ℝ) : |(rnd x : ℝ) - x| ≤ 1 / 2 := by
  have h1 := Int.floor_le (x + 1 / 2)
  have h2 := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]; constructor <;> simp only [rnd] <;> linarith

lemma abs_rnd_sub_rnd {x y : ℝ} (h : |x - y| < 1) : |rnd x - rnd y| ≤ 1 := by
  have hx := abs_rnd_sub x
  have hy := abs_rnd_sub y
  have hr : |((rnd x - rnd y : ℤ) : ℝ)| < 2 := by
    push_cast
    calc |(rnd x : ℝ) - rnd y| = |((rnd x : ℝ) - x) - ((rnd y : ℝ) - y) + (x - y)| := by ring_nf
      _ ≤ |(rnd x : ℝ) - x| + |(rnd y : ℝ) - y| + |x - y| := by
          refine (abs_add_le _ _).trans ?_
          gcongr; exact abs_sub _ _
      _ < 2 := by linarith
  have : |rnd x - rnd y| < 2 := by
    rw [← Int.cast_abs] at hr; exact_mod_cast hr
  omega

 
def latPt (N : ℕ) (z : ℂ) : ℤ × ℤ := (rnd (N * z.re), rnd (N * z.im))

lemma abs_re_cpt_latPt {N : ℕ} (hN : 0 < N) (z : ℂ) :
    |(cpt N (latPt N z)).re - z.re| ≤ 1 / (2 * N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [cpt, latPt]
  rw [show ((rnd (N * z.re) : ℝ)) / N - z.re = (((rnd (N * z.re) : ℝ)) - N * z.re) / N by
    field_simp, abs_div, abs_of_pos hNp, div_le_div_iff₀ hNp (by positivity)]
  nlinarith [abs_rnd_sub (N * z.re)]

lemma abs_im_cpt_latPt {N : ℕ} (hN : 0 < N) (z : ℂ) :
    |(cpt N (latPt N z)).im - z.im| ≤ 1 / (2 * N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [cpt, latPt]
  rw [show ((rnd (N * z.im) : ℝ)) / N - z.im = (((rnd (N * z.im) : ℝ)) - N * z.im) / N by
    field_simp, abs_div, abs_of_pos hNp, div_le_div_iff₀ hNp (by positivity)]
  nlinarith [abs_rnd_sub (N * z.im)]

lemma norm_le_abs_re_add_abs_im' (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| :=
  Complex.norm_le_abs_re_add_abs_im z

lemma squareRadius_le_norm_add (a b : ℂ) : squareRadius a ≤ squareRadius b + ‖a - b‖ := by
  unfold squareRadius
  have h1 : |a.re| ≤ |b.re| + ‖a - b‖ := by
    have := Complex.abs_re_le_norm (a - b)
    rw [Complex.sub_re] at this
    have := abs_sub_abs_le_abs_sub a.re b.re
    linarith
  have h2 : |a.im| ≤ |b.im| + ‖a - b‖ := by
    have := Complex.abs_im_le_norm (a - b)
    rw [Complex.sub_im] at this
    have := abs_sub_abs_le_abs_sub a.im b.im
    linarith
  refine max_le (h1.trans ?_) (h2.trans ?_)
  · gcongr; exact le_max_left _ _
  · gcongr; exact le_max_right _ _

 

 
def latGraph (n : ℕ) : SimpleGraph (DGFFSite n) where
  Adj u v := latticeAdjacent u.1 v.1
  symm := ⟨fun _ _ h => latticeAdjacent_symm h⟩
  loopless := ⟨fun u h => not_latticeAdjacent_self u.1 h⟩

end SupercriticalLQGUniqueness.B2.QPos.P8
