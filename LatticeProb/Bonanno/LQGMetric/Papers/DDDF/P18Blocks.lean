/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Blocks at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Strip
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step2

/-!
# DDDF Prop 18, Step 3: laws of the block crossings (task P2-DDDF16c)

DDDF (arXiv:1904.08021, `tightness.tex` l. 918–927) compare the crossings of the rectangles
`R_i^S(P)` of size `2^{-k}(1,3)` around the blocks `P` with `2^{-k} L^{(n−k)}_{1,3}(φ)` (scaling
(2.30) and the invariance of the law of `φ` under translations and the rotation by `i`). Here:
the block rectangles `p18V`, `p18H` (P18Strip.lean) are images of `R_{δ,3δ}` under
`x ↦ x + c` resp. `x ↦ i x + c` (`rectLen_p18V_eq`, `rectLen_p18H_eq`), so
`L^{(k,n)}(p18V/H)` has the law of `2^{-k} L^{(n−k)}_{1,3}(φ)` (`prob_lenObs_p18V`,
`prob_lenObs_p18H`), via `measure_crossLenIn_phiMN_motion` and `dddf_eq230`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}

/-- the rotation by `i` -/
def circI : Circle := Circle.exp (Real.pi / 2)

lemma coe_circI : (circI : ℂ) = Complex.I := by
  rw [circI, Circle.coe_exp]; push_cast; exact Complex.exp_pi_div_two_mul_I

lemma mem_image_motion {u : Circle} {c z : ℂ} {S : Set ℂ} :
    z ∈ (fun x => (u : ℂ) * x + c) '' S ↔ (u : ℂ)⁻¹ * (z - c) ∈ S := by
  have hu := Circle.coe_ne_zero u
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [add_sub_cancel_right, inv_mul_cancel_left₀ hu]
  · intro h
    refine ⟨_, h, ?_⟩
    show (u : ℂ) * ((u : ℂ)⁻¹ * (z - c)) + c = z
    rw [mul_inv_cancel_left₀ hu, sub_add_cancel]

/-- `p18V a y δ` is the translate of `R_{δ,3δ}` by `a + iy` -/
theorem rectLen_p18V_eq (g : ℂ → ℝ) (a y δ : ℝ) :
    rectLen ξ g (p18V a y δ) =
      crossLenIn ξ g ((fun x => ((1 : Circle) : ℂ) * x + (a + y * Complex.I)) ''
          (rectAB δ (3 * δ)).toSet)
        ((fun x => ((1 : Circle) : ℂ) * x + (a + y * Complex.I)) '' (rectAB δ (3 * δ)).side₁)
        ((fun x => ((1 : Circle) : ℂ) * x + (a + y * Complex.I)) ''
          (rectAB δ (3 * δ)).side₂) := by
  unfold rectLen
  congr 1 <;> ext z <;> rw [mem_image_motion] <;>
    simp only [Circle.coe_one, inv_one, one_mul, MarkedRect.toSet, MarkedRect.side₁,
      MarkedRect.side₂, p18V, rectAB, ↓reduceIte, Complex.mem_reProdIm, mem_Icc,
      mem_singleton_iff, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero] <;>
    constructor <;> intro h <;> refine ⟨?_, ?_⟩ <;> (try constructor) <;> linarith [h.1, h.2]

/-- `p18H a y δ` is the image of `R_{δ,3δ}` under `x ↦ i x + (a + 2δ + iy)` (marked sides go to
the bottom and top sides) -/
theorem rectLen_p18H_eq (g : ℂ → ℝ) (a y δ : ℝ) :
    rectLen ξ g (p18H a y δ) =
      crossLenIn ξ g ((fun x => (circI : ℂ) * x + ((a + 2 * δ) + y * Complex.I)) ''
          (rectAB δ (3 * δ)).toSet)
        ((fun x => (circI : ℂ) * x + ((a + 2 * δ) + y * Complex.I)) ''
          (rectAB δ (3 * δ)).side₁)
        ((fun x => (circI : ℂ) * x + ((a + 2 * δ) + y * Complex.I)) ''
          (rectAB δ (3 * δ)).side₂) := by
  unfold rectLen
  congr 1 <;> ext z <;> rw [mem_image_motion] <;>
    simp only [coe_circI, Complex.inv_I, MarkedRect.toSet, MarkedRect.side₁,
      MarkedRect.side₂, p18H, rectAB, ↓reduceIte, Bool.false_eq_true, Complex.mem_reProdIm,
      mem_Icc, mem_singleton_iff, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, mul_zero, mul_one, zero_mul,
      sub_zero, zero_add, add_zero, zero_sub, neg_mul, one_mul, neg_neg,
      Complex.re_ofNat, Complex.im_ofNat] <;>
    constructor <;> intro h <;> refine ⟨?_, ?_⟩ <;> (try constructor) <;>
      linarith [h.1, h.2]

lemma two_pow_mul_inv_pow (k : ℕ) : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by
  rw [inv_pow, mul_inv_cancel₀ (by positivity)]

/-- **Law of a vertical block crossing**: `L^{(k,n)}(p18V a y 2^{-k}) =ᵈ 2^{-k} L^{(n−k)}_{1,3}(φ)` -/
theorem prob_lenObs_p18V {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {k n : ℕ} (hkn : k ≤ n)
    (a y : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | lenObs ξ (phiMN W P k n) (p18V a y ((2 : ℝ)⁻¹ ^ k)) ω ∈ S} =
      P {ω | (2 : ℝ)⁻¹ ^ k * lenObs ξ (phiMN W P 0 (n - k)) (rectAB 1 3) ω ∈ S} := by
  have hS' : MeasurableSet (ENNReal.toReal ⁻¹' S) := ENNReal.measurable_toReal hS
  have e1 : {ω | lenObs ξ (phiMN W P k n) (p18V a y ((2 : ℝ)⁻¹ ^ k)) ω ∈ S} =
      {ω | crossLenIn ξ (fun x => phiMN W P k n x ω)
        ((fun x => ((1 : Circle) : ℂ) * x + (a + y * Complex.I)) ''
          (rectAB ((2 : ℝ)⁻¹ ^ k) (3 * (2 : ℝ)⁻¹ ^ k)).toSet)
        ((fun x => ((1 : Circle) : ℂ) * x + (a + y * Complex.I)) ''
          (rectAB ((2 : ℝ)⁻¹ ^ k) (3 * (2 : ℝ)⁻¹ ^ k)).side₁)
        ((fun x => ((1 : Circle) : ℂ) * x + (a + y * Complex.I)) ''
          (rectAB ((2 : ℝ)⁻¹ ^ k) (3 * (2 : ℝ)⁻¹ ^ k)).side₂) ∈ ENNReal.toReal ⁻¹' S} := by
    ext ω; simp only [lenObs, rectLen_p18V_eq, mem_preimage, mem_ofPred_eq]
  rw [e1, measure_crossLenIn_phiMN_motion hW hkn _ _ (MarkedRect.isCompact_toSet _) hS']
  have e2 := dddf_eq230 (ξ := ξ) hW ((2 : ℝ)⁻¹ ^ k) (3 * (2 : ℝ)⁻¹ ^ k) hkn hS
  rw [show (2 : ℝ) ^ k * (3 * (2 : ℝ)⁻¹ ^ k) = 3 by
    rw [mul_left_comm, two_pow_mul_inv_pow, mul_one], two_pow_mul_inv_pow] at e2
  exact e2

/-- **Law of a horizontal block crossing**: `L^{(k,n)}(p18H a y 2^{-k}) =ᵈ 2^{-k} L^{(n−k)}_{1,3}(φ)` -/
theorem prob_lenObs_p18H {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {k n : ℕ} (hkn : k ≤ n)
    (a y : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | lenObs ξ (phiMN W P k n) (p18H a y ((2 : ℝ)⁻¹ ^ k)) ω ∈ S} =
      P {ω | (2 : ℝ)⁻¹ ^ k * lenObs ξ (phiMN W P 0 (n - k)) (rectAB 1 3) ω ∈ S} := by
  have hS' : MeasurableSet (ENNReal.toReal ⁻¹' S) := ENNReal.measurable_toReal hS
  set c : ℂ := (a + 2 * ((2 : ℝ)⁻¹ ^ k : ℝ)) + y * Complex.I
  have e1 : {ω | lenObs ξ (phiMN W P k n) (p18H a y ((2 : ℝ)⁻¹ ^ k)) ω ∈ S} =
      {ω | crossLenIn ξ (fun x => phiMN W P k n x ω)
        ((fun x => (circI : ℂ) * x + c) '' (rectAB ((2 : ℝ)⁻¹ ^ k) (3 * (2 : ℝ)⁻¹ ^ k)).toSet)
        ((fun x => (circI : ℂ) * x + c) '' (rectAB ((2 : ℝ)⁻¹ ^ k) (3 * (2 : ℝ)⁻¹ ^ k)).side₁)
        ((fun x => (circI : ℂ) * x + c) '' (rectAB ((2 : ℝ)⁻¹ ^ k) (3 * (2 : ℝ)⁻¹ ^ k)).side₂)
          ∈ ENNReal.toReal ⁻¹' S} := by
    ext ω; simp only [lenObs, rectLen_p18H_eq, mem_preimage, mem_ofPred_eq, c]
  rw [e1, measure_crossLenIn_phiMN_motion hW hkn _ _ (MarkedRect.isCompact_toSet _) hS']
  have e2 := dddf_eq230 (ξ := ξ) hW ((2 : ℝ)⁻¹ ^ k) (3 * (2 : ℝ)⁻¹ ^ k) hkn hS
  rw [show (2 : ℝ) ^ k * (3 * (2 : ℝ)⁻¹ ^ k) = 3 by
    rw [mul_left_comm, two_pow_mul_inv_pow, mul_one], two_pow_mul_inv_pow] at e2
  exact e2

/-- the block rectangles of DDDF Step 3 at scale `δ = 2^{-k}`, indexed by
`(j, i, t) ∈ [0, 2^k) × [0, 2^k] × Fin 3` (`t = 0`: `p18V`, `t = 1, 2`: the two `p18H`) -/
def p18Blk (k : ℕ) (b : ℕ × ℤ × Fin 3) : MarkedRect :=
  if b.2.2 = 0 then p18V (b.1 * (2 : ℝ)⁻¹ ^ k) ((b.2.1 - 1) * (2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k)
  else if b.2.2 = 1 then p18H (b.1 * (2 : ℝ)⁻¹ ^ k) ((b.2.1 + 1) * (2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k)
  else p18H (b.1 * (2 : ℝ)⁻¹ ^ k) ((b.2.1 - 1) * (2 : ℝ)⁻¹ ^ k) ((2 : ℝ)⁻¹ ^ k)

/-- the index set of the block rectangles -/
def p18Idx (k : ℕ) : Finset (ℕ × ℤ × Fin 3) :=
  Finset.range (2 ^ k) ×ˢ Finset.Icc (0 : ℤ) (2 ^ k) ×ˢ Finset.univ

/-- **DDDF Prop 18, Step 3, the pathwise bound** (l. 916–918): almost surely, if
`|φ_{0,k}| ≤ M` on `[0,1]²` and every block rectangle has `L^{(k,n)} ≥ x ≥ 0`, then
`⌊2^k/2⌋ x ≤ e^{|ξ|M} L^{(n)}_{1,1}(φ)`. -/
theorem p18_step3_pathwise {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {k n : ℕ}
    (hkn : k ≤ n) :
    ∀ᵐ ω ∂P, ∀ M x : ℝ, 0 ≤ x → (∀ z ∈ (rectAB 1 1).toSet, |phiMN W P 0 k z ω| ≤ M) →
      (∀ b ∈ p18Idx k, ENNReal.ofReal x ≤ rectLen ξ (fun z => phiMN W P k n z ω) (p18Blk k b)) →
      ((2 ^ k / 2 : ℕ) : ℝ) * x ≤
        Real.exp (|ξ| * M) * lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω := by
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  filter_upwards [ae_phiMN_add hW hkn] with ω hω M x hx hM hR
  have hgeom := p18_geom (ξ := ξ) (g := fun z => phiMN W P k n z ω) k
    (m := ENNReal.ofReal x) (fun j i hj hi0 hik => by
      have hmem : ∀ t : Fin 3, (j, i, t) ∈ p18Idx k := fun t => by
        simp only [p18Idx, Finset.mem_product, Finset.mem_range, Finset.mem_Icc,
          Finset.mem_univ, and_true]
        exact ⟨hj, hi0, by exact_mod_cast hik⟩
      refine ⟨?_, ?_, ?_⟩
      · have := hR _ (hmem 0); simpa [p18Blk] using this
      · have := hR _ (hmem 1); simpa [p18Blk] using this
      · have := hR _ (hmem 2); simpa [p18Blk] using this)
  have hcmp := crossLenIn_le_of_abs_sub_le (ξ := ξ) (U := (rectAB 1 1).toSet)
    (A := (rectAB 1 1).side₁) (B := (rectAB 1 1).side₂)
    (f := fun z => phiMN W P k n z ω) (g := fun z => phiMN W P 0 n z ω) (c := M)
    (fun z hz => by rw [hω z, abs_sub_comm, add_sub_cancel_right]; exact hM z hz)
  have hfin := rectLen_ne_top (ξ := ξ) (rectAB 1 1) (by norm_num [rectAB])
    (by norm_num [rectAB]) (hφ.cont ω)
  have h1 : ENNReal.ofReal (((2 ^ k / 2 : ℕ) : ℝ) * x) ≤
      ENNReal.ofReal (Real.exp (|ξ| * M) * lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_mul (Real.exp_pos _).le, lenObs, ENNReal.ofReal_toReal hfin]
    exact hgeom.trans hcmp
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)).1 h1

end DDDF
end LQGMetric
