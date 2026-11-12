/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareCK1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Chapman–Kolmogorov for the image-series interval kernel (task P2-DDDFP29, WP-110)

`HeatSq.integral_intervalDirKernel_mul`: for `s, r > 0` and all `u, v`,
`∫_a^{a+L} q_s(u,w) q_r(w,v) dw = q_{s+r}(u,v)` — the semigroup property of the Dirichlet heat
kernel of `(a, a+L)` given by the method of images (Feller II §X.5). It is the input of DDDF's
covariance computation for `η_t` (`tightness.tex:1517–1523`, the step
`∫_0^∞∫_D p^D_{s/2}(y',y) p^D_{s/2}(y,y'') dy ds`) on `D = (a, a+L)²` (D19, D-DDDF-11).

Proof (own elementary argument following the images picture): write `q = A − B` with the
nonnegative image sums `A_s(u,w) = S_s(u − w)`, `B_s(u,w) = S_s(u + w − 2a)`,
`S_s(c) = ∑ₙ g_s(c + 2nL)`; then `∫_I (A_s A_r + B_s B_r) = S_{s+r}(u − v)` and
`∫_I (A_s B_r + B_s A_r) = S_{s+r}(u + v − 2a)` by unfolding the sums over `I` onto the line
(`lintegral_fold`) and the Gaussian semigroup `integral_gauss1_mul_gauss1`. All interchanges are
done for `ℝ≥0∞`-valued integrands (`lintegral_tsum`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace HeatSq

/-- The `ℝ≥0∞`-valued image sum `S_s(c) = ∑ₙ g_s(c + 2nL)`. -/
def imgSum (L s c : ℝ) : ℝ≥0∞ := ∑' n : ℤ, ENNReal.ofReal (gauss1 s (c + 2 * n * L))

lemma imgSum_eq_ofReal {L s : ℝ} (hs : 0 < s) (hL : 0 < L) (c : ℝ) :
    imgSum L s c = ENNReal.ofReal (∑' n : ℤ, gauss1 s (c + 2 * n * L)) :=
  (ENNReal.ofReal_tsum_of_nonneg (fun _ => gauss1_nonneg _ _) (summable_gauss1_shift hs hL c)).symm

lemma imgSum_ne_top {L s : ℝ} (hs : 0 < s) (hL : 0 < L) (c : ℝ) : imgSum L s c ≠ ∞ := by
  rw [imgSum_eq_ofReal hs hL]; exact ENNReal.ofReal_ne_top

lemma imgSum_toReal {L s : ℝ} (hs : 0 < s) (hL : 0 < L) (c : ℝ) :
    (imgSum L s c).toReal = ∑' n : ℤ, gauss1 s (c + 2 * n * L) := by
  rw [imgSum_eq_ofReal hs hL, ENNReal.toReal_ofReal (tsum_nonneg fun _ => gauss1_nonneg _ _)]

lemma imgSum_add_period (L s c : ℝ) (m : ℤ) : imgSum L s (c + 2 * m * L) = imgSum L s c := by
  unfold imgSum
  rw [← (Equiv.addRight m).tsum_eq (fun n : ℤ => ENNReal.ofReal (gauss1 s (c + 2 * n * L)))]
  congr 1; funext n; simp only [Equiv.coe_addRight]; push_cast; ring_nf

lemma imgSum_neg (L s c : ℝ) : imgSum L s (-c) = imgSum L s c := by
  unfold imgSum
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ENNReal.ofReal (gauss1 s (c + 2 * n * L)))]
  congr 1; funext n; rw [← gauss1_neg]; simp only [Equiv.neg_apply]; push_cast; ring_nf

lemma measurable_imgSum_comp (L s : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun w => imgSum L s (f w)) :=
  Measurable.ennreal_tsum fun _ => ENNReal.measurable_ofReal.comp
    ((continuous_gauss1 s).measurable.comp (hf.add_const _))

lemma intervalDirKernel_eq_imgSum {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) (u v : ℝ) :
    intervalDirKernel a L s u v =
      (imgSum L s (u - v)).toReal - (imgSum L s (u + v - 2 * a)).toReal := by
  rw [intervalDirKernel_eq_sub hs hL, imgSum_toReal hs hL, imgSum_toReal hs hL]

/-- The line convolution `∫ g_s(u − w) S_r(w − e) dw = S_{s+r}(u − e)`. -/
lemma lintegral_gauss1_mul_imgSum {L s r : ℝ} (hs : 0 < s) (hr : 0 < r) (u e : ℝ) :
    ∫⁻ w, ENNReal.ofReal (gauss1 s (u - w)) * imgSum L r (w - e) = imgSum L (s + r) (u - e) := by
  have hmeas : ∀ n : ℤ, AEMeasurable (fun w => ENNReal.ofReal (gauss1 s (u - w)) *
      ENNReal.ofReal (gauss1 r (w - e + 2 * n * L))) := fun n =>
    ((ENNReal.measurable_ofReal.comp ((continuous_gauss1 s).comp
      (continuous_const.sub continuous_id)).measurable).mul
      (ENNReal.measurable_ofReal.comp ((continuous_gauss1 r).comp
        ((continuous_id.sub continuous_const).add continuous_const)).measurable)).aemeasurable
  unfold imgSum
  simp_rw [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum hmeas]
  congr 1; funext n
  have e1 : (fun w => ENNReal.ofReal (gauss1 s (u - w)) *
      ENNReal.ofReal (gauss1 r (w - e + 2 * n * L))) =
      fun w => ENNReal.ofReal (gauss1 s (u - w) * gauss1 r (w - (e - 2 * n * L))) := by
    funext w; rw [ENNReal.ofReal_mul (gauss1_nonneg _ _),
      show w - (e - 2 * n * L) = w - e + 2 * n * L by ring]
  rw [e1, ← ofReal_integral_eq_lintegral_ofReal (integrable_gauss1_mul_gauss1 s r hs hr u _)
    (Filter.Eventually.of_forall fun w => mul_nonneg (gauss1_nonneg _ _) (gauss1_nonneg _ _)),
    integral_gauss1_mul_gauss1 s r hs hr, show u - (e - 2 * n * L) = u - e + 2 * n * L by ring]

/-- Folded convolution: the sums over the images of `I` recombine to the line integral. -/
lemma fold_conv {a L s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hL : 0 < L) (u e : ℝ) :
    (∑' n : ℤ, ∫⁻ w in Ioc a (a + L),
        ENNReal.ofReal (gauss1 s (u - w + 2 * n * L)) * imgSum L r (w - e)) +
      ∑' n : ℤ, ∫⁻ w in Ioc a (a + L),
        ENNReal.ofReal (gauss1 s (u + w - 2 * a + 2 * n * L)) * imgSum L r (w + e - 2 * a) =
      imgSum L (s + r) (u - e) := by
  rw [← lintegral_gauss1_mul_imgSum (L := L) hs hr u e,
    ← lintegral_fold hL (fun w => ENNReal.ofReal (gauss1 s (u - w)) * imgSum L r (w - e))]
  congr 1
  · rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ∫⁻ w in Ioc a (a + L),
        ENNReal.ofReal (gauss1 s (u - w + 2 * n * L)) * imgSum L r (w - e))]
    congr 1; funext n; congr 1; funext w
    rw [show w + 2 * (n : ℝ) * L - e = (w - e) + 2 * n * L by ring, imgSum_add_period]
    rw [show ((Equiv.neg ℤ) n : ℤ) = -n from rfl]; congr 2; push_cast; ring
  · rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ∫⁻ w in Ioc a (a + L),
        ENNReal.ofReal (gauss1 s (u + w - 2 * a + 2 * n * L)) * imgSum L r (w + e - 2 * a))]
    congr 1; funext n; congr 1; funext w
    rw [show 2 * a - w + 2 * (n : ℝ) * L - e = -(w + e - 2 * a) + 2 * n * L by ring,
      imgSum_add_period, imgSum_neg]
    rw [show ((Equiv.neg ℤ) n : ℤ) = -n from rfl]; congr 2; push_cast; ring

/-- Expanding the first factor of a product with an image sum. -/
lemma setLIntegral_imgSum_mul (L s : ℝ) {c : ℝ → ℝ} (hc : Measurable c) {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) (S : Set ℝ) :
    ∫⁻ w in S, imgSum L s (c w) * F w =
      ∑' n : ℤ, ∫⁻ w in S, ENNReal.ofReal (gauss1 s (c w + 2 * n * L)) * F w := by
  unfold imgSum
  simp_rw [← ENNReal.tsum_mul_right]
  exact lintegral_tsum fun n => ((ENNReal.measurable_ofReal.comp
    ((continuous_gauss1 s).measurable.comp (hc.add_const _))).mul hF).aemeasurable

/-- **Chapman–Kolmogorov for the interval kernel**:
`∫_{(a, a+L]} q_s(u,w) q_r(w,v) dw = q_{s+r}(u,v)`. -/
theorem integral_intervalDirKernel_mul {a L s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hL : 0 < L)
    (u v : ℝ) :
    ∫ w in Ioc a (a + L), intervalDirKernel a L s u w * intervalDirKernel a L r w v =
      intervalDirKernel a L (s + r) u v := by
  set I := Ioc a (a + L)
  have hm : ∀ t : ℝ, ∀ f : ℝ → ℝ, Measurable f → Measurable (fun w => imgSum L t (f w)) :=
    fun t f hf => measurable_imgSum_comp L t hf
  set P : ℝ → ℝ≥0∞ := fun w => imgSum L s (u - w) * imgSum L r (w - v) +
    imgSum L s (u + w - 2 * a) * imgSum L r (w + v - 2 * a)
  set Q : ℝ → ℝ≥0∞ := fun w => imgSum L s (u - w) * imgSum L r (w - (2 * a - v)) +
    imgSum L s (u + w - 2 * a) * imgSum L r (w + (2 * a - v) - 2 * a)
  have hPm : Measurable P := by
    refine ((hm s _ ?_).mul (hm r _ ?_)).add ((hm s _ ?_).mul (hm r _ ?_)) <;> fun_prop
  have hQm : Measurable Q := by
    refine ((hm s _ ?_).mul (hm r _ ?_)).add ((hm s _ ?_).mul (hm r _ ?_)) <;> fun_prop
  have hA : ∀ t : ℝ, ∀ x : ℝ, Measurable (fun w => imgSum L t (x - w)) := fun t x =>
    hm t (fun w => x - w) (by fun_prop)
  have hB : ∀ t : ℝ, ∀ x : ℝ, Measurable (fun w => imgSum L t (w + x)) := fun t x =>
    hm t (fun w => w + x) (by fun_prop)
  have hB' : ∀ t : ℝ, ∀ x : ℝ, Measurable (fun w => imgSum L t (w - x)) := fun t x =>
    hm t (fun w => w - x) (by fun_prop)
  have hC : ∀ t : ℝ, ∀ x y : ℝ, Measurable (fun w => imgSum L t (x + w - y)) := fun t x y =>
    hm t (fun w => x + w - y) (by fun_prop)
  have hD : ∀ t : ℝ, ∀ x y : ℝ, Measurable (fun w => imgSum L t (w + x - y)) := fun t x y =>
    hm t (fun w => w + x - y) (by fun_prop)
  have hP : ∫⁻ w in I, P w = imgSum L (s + r) (u - v) := by
    simp only [P]
    have hm1 : Measurable (fun w => imgSum L s (u - w) * imgSum L r (w - v)) :=
      (hA s u).mul (hB' r v)
    rw [lintegral_add_left hm1,
      setLIntegral_imgSum_mul L s (c := fun w => u - w) (by fun_prop) (hB' r v),
      setLIntegral_imgSum_mul L s (c := fun w => u + w - 2 * a) (by fun_prop) (hD r v (2 * a))]
    exact fold_conv hs hr hL u v
  have hQ : ∫⁻ w in I, Q w = imgSum L (s + r) (u + v - 2 * a) := by
    simp only [Q]
    have hm1 : Measurable (fun w => imgSum L s (u - w) * imgSum L r (w - (2 * a - v))) :=
      (hA s u).mul (hB' r (2 * a - v))
    rw [lintegral_add_left hm1,
      setLIntegral_imgSum_mul L s (c := fun w => u - w) (by fun_prop) (hB' r (2 * a - v)),
      setLIntegral_imgSum_mul L s (c := fun w => u + w - 2 * a) (by fun_prop)
        (hD r (2 * a - v) (2 * a)), fold_conv hs hr hL u (2 * a - v)]
    congr 1; ring
  have hfin : ∀ w, P w ≠ ∞ ∧ Q w ≠ ∞ := fun w => by
    constructor <;> exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (imgSum_ne_top hs hL _)
      (imgSum_ne_top hr hL _), ENNReal.mul_ne_top (imgSum_ne_top hs hL _) (imgSum_ne_top hr hL _)⟩
  have hpt : ∀ w, intervalDirKernel a L s u w * intervalDirKernel a L r w v =
      (P w).toReal - (Q w).toReal := by
    intro w
    rw [intervalDirKernel_eq_imgSum hs hL, intervalDirKernel_eq_imgSum hr hL]
    simp only [P, Q, ENNReal.toReal_add (ENNReal.mul_ne_top (imgSum_ne_top hs hL _)
        (imgSum_ne_top hr hL _)) (ENNReal.mul_ne_top (imgSum_ne_top hs hL _)
        (imgSum_ne_top hr hL _)), ENNReal.toReal_mul]
    rw [show w - (2 * a - v) = w + v - 2 * a by ring, show w + (2 * a - v) - 2 * a = w - v by ring]
    ring
  have hsr : 0 < s + r := by positivity
  have hPf : ∫⁻ w in I, P w ≠ ∞ := by rw [hP]; exact imgSum_ne_top hsr hL _
  have hQf : ∫⁻ w in I, Q w ≠ ∞ := by rw [hQ]; exact imgSum_ne_top hsr hL _
  have hPi : Integrable (fun w => (P w).toReal) (volume.restrict I) :=
    integrable_toReal_of_lintegral_ne_top hPm.aemeasurable hPf
  have hQi : Integrable (fun w => (Q w).toReal) (volume.restrict I) :=
    integrable_toReal_of_lintegral_ne_top hQm.aemeasurable hQf
  simp_rw [hpt]
  rw [integral_sub hPi hQi, integral_toReal hPm.aemeasurable
    (Filter.Eventually.of_forall fun w => (hfin w).1.lt_top), integral_toReal hQm.aemeasurable
    (Filter.Eventually.of_forall fun w => (hfin w).2.lt_top), hP, hQ,
    intervalDirKernel_eq_imgSum (by positivity) hL]

end HeatSq
end LQGMetric
