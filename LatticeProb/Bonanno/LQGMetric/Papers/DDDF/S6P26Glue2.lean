/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P26Glue2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Glue
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Sub
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Path
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S2Site
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale

/-!
# DDDF Prop 26, Step 1: scaling tools for the gluing (task P2-DDDF6b)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1289–1294. The unit-scale gluing `rectLen_le_glue` (S6P26Glue.lean) is applied to the field
`(f + g)(2^{-k} ·)` on `[0, 2^k]²`; here the dictionary between the unit-scale site rectangles
`sB z, sT z, sL z, sR z` and the rectangles `u 2^{-k} R_{3,1} + c` of `T20B.mrectLen`
(`rectLen_site_eq`), and the weight comparison `lfppLen_add_le`. Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open LFPP

namespace S6U

variable {ξ : ℝ}

/-- the `(f+g)`-length of a path is at most `W` times its `g`-length when `e^{ξ f} ≤ W` on it -/
lemma lfppLen_add_le {f g : ℂ → ℝ} {P : ℝ → ℂ} {W : ℝ}
    (hW : ∀ t ∈ Icc (0 : ℝ) 1, Real.exp (ξ * f (P t)) ≤ W) :
    lfppLen ξ (fun x => f x + g x) P ≤ ENNReal.ofReal W * lfppLen ξ g P := by
  rw [lfppLen_eq, lfppLen_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  simp only [lenDens]
  have hW0 : 0 ≤ W := (Real.exp_pos _).le.trans (hW t ht)
  rw [← ENNReal.ofReal_mul hW0]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_add, Real.exp_add, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hW t ht) (Real.exp_pos _).le)
    (norm_nonneg _)

/-- `2^{-k} (u R_{3,1} + c') = mot k u (2^{-k} c') R_{3,1}`: the unit-scale rigid image of
`R_{3,1}` and the `T20B.mrectLen` rectangle -/
lemma rectLen_imLen_eq {g : ℂ → ℝ} (hg : Continuous g) (k : ℕ) (u : Circle) (c' : ℂ) :
    s2ImLen ξ (fun x => g ((((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * x)) u c' =
      ENNReal.ofReal ((2 : ℝ) ^ k) *
        ENNReal.ofReal (T20B.mrectLen ξ g k u ((((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * c') 3 1) := by
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have himg : ∀ X : Set ℂ, T20B.mot k u ((((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * c') '' X =
      (fun z => ((((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ)) * z) '' (s2Mot u c' '' X) := by
    intro X
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    simp only [T20B.mot, s2Mot]; ring
  have htop := T20D.crossLenIn_mot_ne_top (ξ := ξ) k u ((((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * c')
    (a := 3) (b := 1) (by norm_num) zero_le_one hg
  have e : ENNReal.ofReal (T20B.mrectLen ξ g k u ((((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * c') 3 1) =
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) *
        s2ImLen ξ (fun x => g ((((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * x)) u c' := by
    unfold T20B.mrectLen
    rw [ENNReal.ofReal_toReal htop, himg, himg, himg, crossLenIn_image_mul _ _ _ _ _ hr]
    rfl
  rw [e, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  norm_num

/-- the four site rectangles of the unit-scale site `z`, as `(u, c)` of `T20B.mrectLen` at scale
`k` (`sB z, sT z, sL z, sR z` scaled by `2^{-k}`) -/
def siteJ (k : ℕ) (z : ℤ × ℤ) : Fin 4 → Circle × ℂ := fun i =>
  match i with
  | 0 => (1, (((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * ((((z.1 : ℝ) - 1 : ℝ) : ℂ) + (((z.2 : ℝ) - 1 : ℝ) : ℂ) * Complex.I))
  | 1 => (1, (((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * ((((z.1 : ℝ) - 1 : ℝ) : ℂ) + (((z.2 : ℝ) + 1 : ℝ) : ℂ) * Complex.I))
  | 2 => (circI, (((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * ((((z.1 : ℝ) : ℝ) : ℂ) + (((z.2 : ℝ) - 1 : ℝ) : ℂ) * Complex.I))
  | 3 => (circI, (((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * ((((z.1 : ℝ) + 2 : ℝ) : ℂ) + (((z.2 : ℝ) - 1 : ℝ) : ℂ) * Complex.I))

/-- the site rectangle `i` of `z` -/
def siteR (z : ℤ × ℤ) : Fin 4 → MarkedRect := fun i =>
  match i with
  | 0 => sB z
  | 1 => sT z
  | 2 => sL z
  | 3 => sR z

lemma rectLen_siteR {g : ℂ → ℝ} (hg : Continuous g) (k : ℕ) (z : ℤ × ℤ) (i : Fin 4) :
    rectLen ξ (fun x => g ((((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * x)) (siteR z i) =
      ENNReal.ofReal ((2 : ℝ) ^ k) *
        ENNReal.ofReal (T20B.mrectLen ξ g k (siteJ k z i).1 (siteJ k z i).2 3 1) := by
  fin_cases i
  · simp only [siteR, siteJ]; rw [rectLen_sB_eq]; exact rectLen_imLen_eq hg k _ _
  · simp only [siteR, siteJ]; rw [rectLen_sT_eq]; exact rectLen_imLen_eq hg k _ _
  · simp only [siteR, siteJ]; rw [rectLen_sL_eq]; exact rectLen_imLen_eq hg k _ _
  · simp only [siteR, siteJ]; rw [rectLen_sR_eq]; exact rectLen_imLen_eq hg k _ _

lemma siteR_wh (z : ℤ × ℤ) (i : Fin 4) : 0 ≤ (siteR z i).w ∧ 0 ≤ (siteR z i).h := by
  fin_cases i <;> simp [siteR, sB, sT, sL, sR]

/-- the site rectangles of `z` lie in `[z₁-1, z₁+2] × [z₂-1, z₂+2]` -/
lemma siteR_sub (z : ℤ × ℤ) (i : Fin 4) {y : ℂ} (hy : y ∈ (siteR z i).toSet) :
    (z.1 : ℝ) - 1 ≤ y.re ∧ y.re ≤ (z.1 : ℝ) + 2 ∧ (z.2 : ℝ) - 1 ≤ y.im ∧ y.im ≤ (z.2 : ℝ) + 2 := by
  rw [mem_toSet_iff] at hy
  fin_cases i <;> simp only [siteR, sB, sT, sL, sR, mem_Icc] at hy <;>
    exact ⟨by linarith [hy.1.1], by linarith [hy.1.2], by linarith [hy.2.1], by linarith [hy.2.2]⟩

lemma clampZ_near_self {N x : ℤ} (hN : 3 ≤ N) (h1 : -1 ≤ x) (h2 : x ≤ N) :
    x - 2 ≤ clampZ 1 (N - 2) x ∧ clampZ 1 (N - 2) x ≤ x + 2 := by
  unfold clampZ; omega

/-- points of the site rectangles of `clampB 1 (N-2) x`, scaled by `2^{-k}`, lie in `glueBox k x` -/
lemma scaled_mem_glueBox {k : ℕ} (hk : 2 ≤ k) {x : ℤ × ℤ} (hx : x ∈ T20.blkIdx k) (i : Fin 4)
    {y : ℂ} (hy : y ∈ (siteR (clampB 1 (((2 ^ k : ℕ) : ℤ) - 2) x) i).toSet) :
    (((2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) * y ∈ glueBox k x := by
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have hN : (4 : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) := by
    have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    exact_mod_cast this
  simp only [T20.blkIdx, Finset.mem_product, Finset.mem_Icc] at hx
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hx
  have e2 : ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) := by push_cast; ring
  rw [e2] at a2 a4
  obtain ⟨c1, c2⟩ := clampZ_near_self (by omega : (3 : ℤ) ≤ ((2 ^ k : ℕ) : ℤ)) a1 a2
  obtain ⟨c3, c4⟩ := clampZ_near_self (by omega : (3 : ℤ) ≤ ((2 ^ k : ℕ) : ℤ)) a3 a4
  obtain ⟨y1, y2, y3, y4⟩ := siteR_sub _ i hy
  simp only [clampB] at y1 y2 y3 y4
  have d1 : (x.1 : ℝ) - 2 ≤ (clampZ 1 (((2 ^ k : ℕ) : ℤ) - 2) x.1 : ℝ) := by exact_mod_cast c1
  have d2 : (clampZ 1 (((2 ^ k : ℕ) : ℤ) - 2) x.1 : ℝ) ≤ (x.1 : ℝ) + 2 := by exact_mod_cast c2
  have d3 : (x.2 : ℝ) - 2 ≤ (clampZ 1 (((2 ^ k : ℕ) : ℤ) - 2) x.2 : ℝ) := by exact_mod_cast c3
  have d4 : (clampZ 1 (((2 ^ k : ℕ) : ℤ) - 2) x.2 : ℝ) ≤ (x.2 : ℝ) + 2 := by exact_mod_cast c4
  simp only [glueBox, Complex.mem_reProdIm, mem_Icc, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by linarith) hp.le
  · rw [mul_comm ((x.1 : ℝ) + 4)]; exact mul_le_mul_of_nonneg_left (by linarith) hp.le
  · rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by linarith) hp.le
  · rw [mul_comm ((x.2 : ℝ) + 4)]; exact mul_le_mul_of_nonneg_left (by linarith) hp.le

end S6U

end DDDF
end LQGMetric
