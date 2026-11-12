/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20DField at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CGather
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiProp5

/-!
# DDDF Theorem 20, Step 4: field comparisons on the boxes `\hat P` (task P2-DDDFT20d)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1135–1146 ((5.67)): on `\hat P`,
`e^{ξψ_{0,n}} ≥ e^{-2ξX} e^{ξψ_{0,K}(P)} e^{-ξ osc_{\hat P}(φ_{0,K})} e^{ξφ_{K,n}}`.

* `T20D.ae_XAB_shift_ne_top`: `X_{a,b}` on a translated box is a.s. finite (DDDF Prop 5, (2.25),
  moved by the motion invariance of white noise, as `T20C.expMoment_XAB_shift`);
* `T20D.abs_sub_le_Xbig`: `|φ_{0,m} − ψ_{0,m}| ≤ X` on `[-2,3]²`;
* `T20D.osc_hatBox_le`: `|φ_{0,K}(x) − φ_{0,K}(c_P)| ≤ 3 O` for `x ∈ \hat P`, `O = Obig`
  (mean value inequality; `\hat P ⊆ [-2,3]²`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace T20D

/-- `X_{a,b}` on the translated box `c₁ + [0,a]×[0,b]` is a.s. finite (DDDF Prop 5) -/
theorem ae_XAB_shift_ne_top (hW : IsWhiteNoise P W) (Q : PsiParams) (c₁ : ℂ) (a b : ℝ) :
    ∀ᵐ ω ∂P, XAB (fun n y => phiMN W P 0 n (y + c₁) ω)
      (fun n y => psiMN Q W P 0 n (y + c₁) ω) a b ≠ ⊤ := by
  set W' : WNSpace → Ω → ℝ := fun f => W (motionL2 1 c₁ f)
  have hW' : IsWhiteNoise P W' := isWhiteNoise_isometry hW _
  have hφ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ y, phiMN W P 0 n (y + c₁) ω = phiMN W' P 0 n y ω := by
    refine ae_all_iff.2 fun n => ?_
    have h1 := isPhiVersion_phiMN hW (Nat.zero_le n)
    have h2 := isPhiVersion_phiMN hW' (Nat.zero_le n)
    refine T20C.ae_forall_eq_of_cont
      (fun ω => (h1.cont ω).comp (continuous_id.add continuous_const)) h2.cont fun x => ?_
    have e := phi_motion W (a := (2 : ℝ)⁻¹ ^ n) (by positivity) ((2 : ℝ)⁻¹ ^ 0) 1 x c₁
    simp only [Circle.coe_one, one_mul] at e
    exact (h1.ae_eq (x + c₁)).trans (by rw [e]; exact (h2.ae_eq x).symm)
  have hψ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ y, psiMN Q W P 0 n (y + c₁) ω = psiMN Q W' P 0 n y ω := by
    refine ae_all_iff.2 fun n => ?_
    have h1 := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
    have h2 := isPsiVersion_psiMN (Q := Q) hW' (Nat.zero_le n)
    refine T20C.ae_forall_eq_of_cont
      (fun ω => (h1.cont ω).comp (continuous_id.add continuous_const)) h2.cont fun x => ?_
    have e : psi Q W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (x + c₁) =
        psi Q W' ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) x := by
      have e1 := psiKernelL2_motion Q (a := (2 : ℝ)⁻¹ ^ n) (by positivity) ((2 : ℝ)⁻¹ ^ 0) 1 x c₁
      simp only [Circle.coe_one, one_mul] at e1
      funext ω; simp only [psi, e1, W']
    exact (h1.ae_eq (x + c₁)).trans (by rw [e]; exact (h2.ae_eq x).symm)
  obtain ⟨C, c, hC, hc, htail⟩ := dddf_prop5_XAB hW' Q a b
  have htop : P {ω | XAB (fun n y => phiMN W' P 0 n y ω) (fun n y => psiMN Q W' P 0 n y ω) a b
      = ⊤} = 0 := by
    have hT : Tendsto (fun x : ℝ => ENNReal.ofReal (C * Real.exp (-(c * x ^ 2)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => C * Real.exp (-(c * x ^ 2))) atTop (𝓝 0) := by
        have h2 : Tendsto (fun x : ℝ => -(c * x ^ 2)) atTop atBot :=
          tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hc)
        simpa using (Real.tendsto_exp_atBot.comp h2).const_mul C
      have := (ENNReal.continuous_ofReal.tendsto 0).comp h1
      rw [ENNReal.ofReal_zero] at this; exact this
    refine le_antisymm (ge_of_tendsto hT ?_) bot_le
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    refine le_trans (measure_mono fun ω hω => ?_) (htail x hx)
    simp only [mem_setOf_eq] at hω ⊢
    rw [hω]; exact le_top
  have hae : ∀ᵐ ω ∂P, XAB (fun n y => phiMN W' P 0 n y ω) (fun n y => psiMN Q W' P 0 n y ω) a b
      ≠ ⊤ := by
    rw [ae_iff]; simpa using htop
  filter_upwards [hφ, hψ, hae] with ω h1 h2 h3
  simp only [h1, h2]; exact h3

/-- `[-2,3]²` -/
def bigBox : Set ℂ := Icc (-2 : ℝ) 3 ×ℂ Icc (-2 : ℝ) 3

/-- `|φ_{0,m} − ψ_{0,m}| ≤ X` on `[-2,3]²` when `X < ∞` -/
lemma abs_sub_le_Xbig (Q : PsiParams) {ω : Ω}
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤) (m : ℕ) {x : ℂ} (hx : x ∈ bigBox) :
    |phiMN W P 0 m x ω - psiMN Q W P 0 m x ω| ≤ T20C.Xbig Q W P ω := by
  unfold T20C.Xbig
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
  have hy : x - T20C.cBig ∈ (rectAB 5 5).toSet := by
    simp only [bigBox, Complex.mem_reProdIm, mem_Icc] at hx
    simp only [MarkedRect.toSet, rectAB, T20C.cBig, Complex.mem_reProdIm, mem_Icc,
      Complex.sub_re, Complex.sub_im, zero_add]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have e : x - T20C.cBig + T20C.cBig = x := sub_add_cancel _ _
  refine le_trans (le_of_eq ?_) (le_iSup_of_le m (le_iSup₂_of_le (x - T20C.cBig) hy le_rfl))
  simp only [e]

/-- `\hat P ⊆ [-2, 3]²` and the centre of `P` is in `[-2,3]²`, for `b ∈ blkIdx K`, `K ≥ 2` -/
lemma center_near {K : ℕ} (hK : 2 ≤ K) {b : ℤ × ℤ} (hb : b ∈ T20.blkIdx K) :
    -1 / 2 * (2 : ℝ)⁻¹ ^ K ≤ (T20.dyCenter K b).re ∧ (T20.dyCenter K b).re ≤ 1 + 1 / 2 * (2 : ℝ)⁻¹ ^ K ∧
    -1 / 2 * (2 : ℝ)⁻¹ ^ K ≤ (T20.dyCenter K b).im ∧ (T20.dyCenter K b).im ≤ 1 + 1 / 2 * (2 : ℝ)⁻¹ ^ K := by
  have hp := h_pos K
  have e1 : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by rw [inv_pow, mul_inv_cancel₀ (by positivity)]
  simp only [T20.blkIdx, Finset.mem_product, Finset.mem_Icc] at hb
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hb
  have b1 : (-1 : ℝ) ≤ b.1 := by exact_mod_cast a1
  have b2 : (b.1 : ℝ) ≤ 2 ^ K := by exact_mod_cast a2
  have b3 : (-1 : ℝ) ≤ b.2 := by exact_mod_cast a3
  have b4 : (b.2 : ℝ) ≤ 2 ^ K := by exact_mod_cast a4
  simp only [T20.dyCenter]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

lemma h_le_quarter {K : ℕ} (hK : 2 ≤ K) : (2 : ℝ)⁻¹ ^ K ≤ 1 / 4 := by
  have : (2 : ℝ)⁻¹ ^ K ≤ (2 : ℝ)⁻¹ ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hK
  norm_num at this ⊢; linarith

/-- the oscillation bound: `‖∇Y‖ ≤ 2^K O` on `[-2,3]²` -/
lemma norm_fderiv_le_Obig (K : ℕ) {Y : ℂ → Ω → ℝ} {ω : Ω} (hY : ContDiff ℝ 1 fun x => Y x ω)
    {z : ℂ} (hz : z ∈ bigBox) :
    ‖fderiv ℝ (fun x => Y x ω) z‖ ≤ (2 : ℝ) ^ K * T20C.Obig K Y ω := by
  simp only [bigBox] at hz
  rw [Complex.mem_reProdIm] at hz
  obtain ⟨⟨r1, r2⟩, i1, i2⟩ := hz
  set c' : ℂ := ⟨(min ⌊z.re⌋ 2 : ℤ), (min ⌊z.im⌋ 2 : ℤ)⟩
  have hfl : ∀ t : ℝ, -2 ≤ t → t ≤ 3 → (-2 : ℤ) ≤ min ⌊t⌋ 2 ∧ min ⌊t⌋ 2 ≤ (2 : ℤ) ∧
      0 ≤ t - (min ⌊t⌋ 2 : ℤ) ∧ t - (min ⌊t⌋ 2 : ℤ) ≤ 1 := by
    intro t h1 h2
    have f1 := Int.floor_le t
    have f2 := Int.lt_floor_add_one t
    have g1 : (-2 : ℤ) ≤ ⌊t⌋ := Int.le_floor.2 (by push_cast; linarith)
    rcases le_total ⌊t⌋ 2 with h | h
    · rw [min_eq_left h]; exact ⟨by omega, by omega, by linarith, by linarith⟩
    · rw [min_eq_right h]
      have h' : (2 : ℝ) ≤ ⌊t⌋ := by exact_mod_cast h
      refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> push_cast <;> linarith
  obtain ⟨p1, p2, p3, p4⟩ := hfl _ r1 r2
  obtain ⟨q1, q2, q3, q4⟩ := hfl _ i1 i2
  have hc' : c' ∈ T20C.offs := by
    simp only [T20C.offs, Finset.mem_image, Finset.mem_product, Finset.mem_Icc]
    exact ⟨(min ⌊z.re⌋ 2, min ⌊z.im⌋ 2), ⟨⟨p1, p2⟩, q1, q2⟩, rfl⟩
  have hw : z - c' ∈ ferniqueBox 0 1 := by
    simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc, Complex.sub_re, Complex.sub_im,
      Complex.zero_re, Complex.zero_im, zero_add, c']
    exact ⟨⟨p3, p4⟩, q3, q4⟩
  set g : ℂ → ℝ := fun x => ‖fderiv ℝ (fun y => Y (y + c') ω) x‖
  have hg : Continuous g := by
    have : ContDiff ℝ 1 fun y => Y (y + c') ω := hY.comp (contDiff_id.add contDiff_const)
    exact (this.continuous_fderiv (by norm_num)).norm
  have hcpt : IsCompact (ferniqueBox 0 1) := by
    rw [← rectAB_one_toSet]; exact (rectAB 1 1).isCompact_toSet
  have hbdd : BddAbove (range fun x : ferniqueBox 0 1 => g x) := by
    rw [← image_eq_range]; exact (hcpt.image hg).bddAbove
  have h1 : ‖fderiv ℝ (fun x => Y x ω) z‖ ≤ ⨆ x : ferniqueBox 0 1, g x := by
    have e : ‖fderiv ℝ (fun x => Y x ω) z‖ = g (z - c') := by
      simp only [g]; rw [fderiv_comp_add_right (f := fun x => Y x ω), sub_add_cancel]
    rw [e]; exact le_ciSup hbdd ⟨_, hw⟩
  have h2 : ((2 : ℝ) ^ K)⁻¹ * ⨆ x : ferniqueBox 0 1, g x ≤ T20C.Obig K Y ω :=
    Finset.le_sup' (fun c => ((2 : ℝ) ^ K)⁻¹ *
      ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c) ω) z‖) hc'
  have hp : (0 : ℝ) < 2 ^ K := by positivity
  calc _ ≤ ⨆ x : ferniqueBox 0 1, g x := h1
    _ = (2 : ℝ) ^ K * (((2 : ℝ) ^ K)⁻¹ * ⨆ x : ferniqueBox 0 1, g x) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hp.le

/-- **Oscillation on `\hat P`** (DDDF l. 1136): `|φ_{0,K}(x) − φ_{0,K}(c_P)| ≤ 3 O` -/
lemma osc_hatBox_le {K : ℕ} (hK : 2 ≤ K) {Y : ℂ → Ω → ℝ} {ω : Ω}
    (hY : ContDiff ℝ 1 fun x => Y x ω) {b : ℤ × ℤ} (hb : b ∈ T20.blkIdx K) {x : ℂ}
    (hx : x ∈ hatBox K b) :
    |Y x ω - Y (T20.dyCenter K b) ω| ≤ 3 * T20C.Obig K Y ω := by
  have hp := h_pos K
  have hq := h_le_quarter hK
  obtain ⟨c1, c2, c3, c4⟩ := center_near hK hb
  obtain ⟨a1, a2, a3, a4⟩ := mem_hatBox hx
  set c := T20.dyCenter K b
  have hcre : c.re = ((b.1 : ℝ) + 1 / 2) * (2 : ℝ)⁻¹ ^ K := rfl
  have hcim : c.im = ((b.2 : ℝ) + 1 / 2) * (2 : ℝ)⁻¹ ^ K := rfl
  set S := Metric.closedBall c (3 * (2 : ℝ)⁻¹ ^ K)
  have hxS : x ∈ S := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have r1 : |(x - c).re| ≤ 3 / 2 * (2 : ℝ)⁻¹ ^ K := by
      rw [Complex.sub_re, abs_le]; constructor <;> linarith
    have r2 : |(x - c).im| ≤ 3 / 2 * (2 : ℝ)⁻¹ ^ K := by
      rw [Complex.sub_im, abs_le]; constructor <;> linarith
    linarith
  have hS : ∀ z ∈ S, z ∈ bigBox := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have r1 := (Complex.abs_re_le_norm (z - c)).trans hz
    have r2 := (Complex.abs_im_le_norm (z - c)).trans hz
    rw [Complex.sub_re, abs_le] at r1
    rw [Complex.sub_im, abs_le] at r2
    simp only [bigBox]; rw [Complex.mem_reProdIm]
    exact ⟨⟨by linarith [r1.1], by linarith [r1.2]⟩, by linarith [r2.1], by linarith [r2.2]⟩
  have hd : ∀ z ∈ S, DifferentiableAt ℝ (fun x => Y x ω) z := fun z _ =>
    (hY.differentiable (by norm_num)) z
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le hd
    (fun z hz => norm_fderiv_le_Obig K hY (hS z hz)) (convex_closedBall c _)
    (Metric.mem_closedBall_self (by positivity)) hxS
  rw [Real.norm_eq_abs] at h
  have hxc : ‖x - c‖ ≤ 3 * (2 : ℝ)⁻¹ ^ K := by
    rw [← dist_eq_norm]; exact hxS
  have hO := T20C.Obig_nonneg K Y ω
  have e : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by rw [inv_pow, mul_inv_cancel₀ (by positivity)]
  calc _ ≤ (2 : ℝ) ^ K * T20C.Obig K Y ω * ‖x - c‖ := h
    _ ≤ (2 : ℝ) ^ K * T20C.Obig K Y ω * (3 * (2 : ℝ)⁻¹ ^ K) :=
        mul_le_mul_of_nonneg_left hxc (by positivity)
    _ = 3 * T20C.Obig K Y ω * ((2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K) := by ring
    _ = _ := by rw [e, mul_one]

/-- the oscillation over a convex piece of `[-2,3]²`: `|Y x − Y y| ≤ 2^K O ‖x − y‖` -/
lemma osc_bigBox_le (K : ℕ) {Y : ℂ → Ω → ℝ} {ω : Ω} (hY : ContDiff ℝ 1 fun x => Y x ω)
    {x y : ℂ} (hx : x ∈ bigBox) (hy : y ∈ bigBox) :
    |Y x ω - Y y ω| ≤ (2 : ℝ) ^ K * T20C.Obig K Y ω * ‖x - y‖ := by
  have hconv : Convex ℝ bigBox :=
    ((convex_Icc (-2 : ℝ) 3).linear_preimage Complex.reLm).inter
      ((convex_Icc (-2 : ℝ) 3).linear_preimage Complex.imLm)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun x => Y x ω)
    (fun z _ => (hY.differentiable (by norm_num)) z)
    (fun z hz => norm_fderiv_le_Obig K hY hz) hconv hy hx
  rwa [Real.norm_eq_abs] at h

end T20D

end DDDF
end LQGMetric
