/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18C
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105B

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.22 in the coordinates of `𝕊(1) = [−1, 2]²`

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, Prop 3.22
(`prop-lfpp-upper0`, DG:1722–1727): "`max_{z,w∈𝕊} D^δ_{h^{𝕊(1)}}(z, w; 𝕊(1/2)) ≤ δ^{λ−ζ}` with
polynomially high probability". D105 item 1: the proof is done at `𝕍`-scale through
`T(z) = (z + 1 + i)/3` (`T(𝕊(1)) = [0,1]²`, `T(𝕊(1/2)) = [1/6,5/6]²`, `T(𝕊) = [1/3,2/3]²`);
this file transports `dg_prop322_V` back. For a process `hc` (the circle averages of
`h^{𝕊(1)}`), `p18Vfield hc δ y = hc (3δ) (T⁻¹ y)` is the circle-average process of the
transported field `h^{𝕊(1)} ∘ T⁻¹` (a zero-boundary GFF on `𝕍` by conformal invariance; this
identification is not used here: the L3.7 hypothesis is stated for `p18Vfield hc` directly).

* `p18_dgLFPP_scale` — `D^δ_{hc}(z, w; 𝕊(1/2)) ≤ 3 D^{δ/3}_{p18Vfield hc}(Tz, Tw; T𝕊(1/2))`
  (affine change of variables, `DFGPS.L36.lfppLength_affine`).
* `dg_prop322_sqOne` — DG Prop 3.22 for `hc` in the `𝕊(1)` coordinates.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open WhiteNoise SupTail

variable {Ω : Type} [MeasurableSpace Ω]

/-- DG's `𝕊(1/2) = [−1/2, 3/2]²` (closed) -/
def p18Half : Set ℂ := Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-1 / 2 : ℝ) (3 / 2)

/-- `T⁻¹ y = 3 y − (1 + i)` -/
def p18Tinv (y : ℂ) : ℂ := (3 : ℝ) * y + -(1 + Complex.I)

/-- `T z = (z + 1 + i)/3` -/
def p18T (z : ℂ) : ℂ := ((1 / 3 : ℝ) : ℂ) * z + p18c0

lemma p18_Tinv_T (z : ℂ) : p18Tinv (p18T z) = z := by
  apply Complex.ext <;> simp [p18Tinv, p18T, p18c0] <;> ring

/-- the field at `𝕍`-scale: `hV δ y = hc (3δ) (T⁻¹ y)` -/
def p18Vfield (hc : ℝ → ℂ → Ω → ℝ) (δ : ℝ) (y : ℂ) (ω : Ω) : ℝ := hc (3 * δ) (p18Tinv y) ω

lemma p18_box_convex : Convex ℝ (p39Box p18c0 (1 / 3) (1 / 6)) :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

lemma p18_Tinv_mem {y : ℂ} (hy : y ∈ p39Box p18c0 (1 / 3) (1 / 6)) : p18Tinv y ∈ p18Half := by
  simp only [p39Box, p18Half, Complex.mem_reProdIm, mem_Icc, p18Tinv, p18c0] at hy ⊢
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  norm_num at hy ⊢
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hy.1.1, hy.1.2, hy.2.1, hy.2.2]

lemma p18_T_mem_sq {z : ℂ} (hz : z ∈ Blueprint.closedUnitSquare) :
    p18T z ∈ p39Sq p18c0 (1 / 3) := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  simp only [p39Sq, Complex.mem_reProdIm, mem_Icc, p18T, p18c0, Complex.add_re, Complex.add_im,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- **change of scale** `𝕊(1) → 𝕍` for the restricted LFPP distance -/
lemma p18_sq_sub_box : p39Sq p18c0 (1 / 3) ⊆ p39Box p18c0 (1 / 3) (1 / 6) := by
  intro x hx
  simp only [p39Sq, p39Box, Complex.mem_reProdIm, mem_Icc] at hx ⊢
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2]

lemma p18_dgLFPP_scale (ξ : ℝ) (hc : ℝ → ℂ → Ω → ℝ) (δ : ℝ) (ω : Ω) {z w : ℂ}
    (hz : z ∈ Blueprint.closedUnitSquare) (hw : w ∈ Blueprint.closedUnitSquare) :
    dgLFPP ξ (fun x => hc δ x ω) p18Half z w ≤
      3 * dgLFPP ξ (fun y => p18Vfield hc (δ / 3) y ω) (p39Box p18c0 (1 / 3) (1 / 6))
        (p18T z) (p18T w) := by
  set B := p39Box p18c0 (1 / 3) (1 / 6)
  have hne : Nonempty {q : ℝ → ℂ // IsDGPath B (p18T z) (p18T w) q} :=
    ⟨⟨_, t18_isDGPath_segment p18_box_convex (p18_sq_sub_box (p18_T_mem_sq hz))
      (p18_sq_sub_box (p18_T_mem_sq hw))⟩⟩
  · rw [← div_le_iff₀' (by norm_num : (0 : ℝ) < 3)]
    refine le_ciInf fun q => ?_
    rw [div_le_iff₀' (by norm_num : (0 : ℝ) < 3)]
    have hp := DFGPS.L36.isDGPath_affine q.2 3 (-(1 + Complex.I))
    have hS : (fun x => ((3 : ℝ) : ℂ) * x + -(1 + Complex.I)) '' B ⊆ p18Half := by
      rintro _ ⟨y, hy, rfl⟩; exact p18_Tinv_mem hy
    have hp' : IsDGPath p18Half z w (fun t => ((3 : ℝ) : ℂ) * q.1 t + -(1 + Complex.I)) := by
      refine ⟨?_, ?_, hp.mapsTo.mono_right hS, hp.continuousOn, hp.piecewise_contDiff⟩
      · exact hp.source.trans (p18_Tinv_T z)
      · exact hp.target.trans (p18_Tinv_T w)
    have hlen := DFGPS.L36.lfppLength_affine (r := 3) (by norm_num) (-(1 + Complex.I)) ξ 0
      (Φ := fun x => hc δ x ω) (φ := fun y => p18Vfield hc (δ / 3) y ω)
      (fun x => by simp [p18Vfield, p18Tinv]; ring_nf) q.1
    rw [mul_zero, Real.exp_zero, mul_one] at hlen
    calc dgLFPP ξ (fun x => hc δ x ω) p18Half z w
        ≤ LQGDimension.lfppLength ξ (fun x => hc δ x ω)
            (fun t => ((3 : ℝ) : ℂ) * q.1 t + -(1 + Complex.I)) :=
          ciInf_le (bddBelow_dg _ _ _ _ _) ⟨_, hp'⟩
      _ = _ := hlen

lemma p18_ball_sub_K0 {u : ℂ} (hu : u ∈ p18Pts) :
    closedBall u (2 * (1 / 30)) ⊆ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5) := by
  intro x hx
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨hi, hj⟩ := Finset.mem_product.1 hij
  have hi' : (ij.1 : ℝ) ≤ 20 := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' : (ij.2 : ℝ) ≤ 20 := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hi0 : (0 : ℝ) ≤ ij.1 := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ ij.2 := Nat.cast_nonneg _
  rw [mem_closedBall, dist_eq_norm] at hx
  have hr := (Complex.abs_re_le_norm _).trans hx
  have hm := (Complex.abs_im_le_norm _).trans hx
  simp only [Complex.sub_re, Complex.sub_im] at hr hm
  rw [abs_le] at hr hm
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> norm_num <;> linarith [hr.1, hr.2, hm.1, hm.2]

/-- `K₀ = [1/10, 9/10]²` satisfies the hypothesis of `muHat` -/
lemma p18_hK0 : ∀ z ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5), ball z (1 / 10) ⊆ openSquare := by
  intro z hz x hx
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc] at hz
  norm_num at hz
  rw [mem_ball, dist_eq_norm] at hx
  have hr := (Complex.abs_re_le_norm _).trans_lt hx
  have hm := (Complex.abs_im_le_norm _).trans_lt hx
  simp only [Complex.sub_re, Complex.sub_im] at hr hm
  rw [abs_lt] at hr hm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hr.1, hr.2, hm.1, hm.2, hz.1.1, hz.1.2, hz.2.1, hz.2.2]

/-- **DG L3.8, lower half, for `μ_ĥ` on `T(𝕊(1/2)) = [1/6, 5/6]²`** (`K₀ = [1/10, 9/10]²`;
fixed finite cover by `441` balls of radius `1/30` and a union bound) -/
theorem p18_dgL38Lower_box_muHat {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ z ∈ ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5), ball z (1 / 10) ⊆ openSquare)
    {β : ℝ} (hβ : 0 < β) (hβγ : β < 2 / (2 + γ) ^ 2) :
    DGL38Lower P (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) hK)
      (p39Box p18c0 (1 / 3) (1 / 6)) β := by
  obtain ⟨-, h2⟩ := p18_box_cover
  obtain ⟨p, C, ε₀, hp, hε₀, hb⟩ := p18_dgL38Lower_biUnion p18Pts (fun u => closedBall u (1 / 30))
    (fun u hu => dgL38Lower_muHat hW hγ hγ2 (by norm_num) hK (by norm_num) (p18_ball_sub_K0 hu)
      β hβ hβγ)
  refine ⟨p, C, ε₀, hp, hε₀, fun ε hε hεε => (measure_mono fun ω hω => ?_).trans (hb ε hε hεε)⟩
  simp only [mem_ofPred_eq] at hω ⊢
  exact fun h => hω fun z hz => h z (h2 hz)

end LQGMetric.DG
