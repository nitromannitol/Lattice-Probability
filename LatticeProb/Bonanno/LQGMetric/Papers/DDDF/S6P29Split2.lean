/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29Split2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Split

/-!
# DDDF Proposition 29 on `(−1,2)²` modulo the first-term increments (R3)

DDDF arXiv:1904.08021, `tightness.tex` DD:1555–1596: by `dKer_cases` the `L²` norms of the
kernel `dKer` split into the first, second and third terms of (6.97). The second
(`HeatSq.lintegral_secondTerm_incr_le`, `_var_le`, DD:1580–1587) and third
(`HeatSq.lintegral_thirdTerm_incr_le`, `_var_le`, DD:1590–1596) terms and the first-term
variance (`HeatSq.lintegral_firstTerm_var_le`, DD:1566–1570) are proved; the first-term
increments (DD:1571–1576, "By splitting the integral at `√|x−x'|` … gradient estimates") are the
hypothesis `P29FirstIncr`. Result: `dddfProp29Sq_of_firstIncr : P29FirstIncr → DDDFProp29Sq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace P29WN

open HeatSq WhiteNoise Blueprint

/-- **First term, increments** (DDDF DD:1571–1576), uniformly in `t ∈ (0,1/2)`:
`∫_0^1 ∫_D (firstKer t s x y − firstKer t s x' y)² dy ds ≤ C |x − x'|` on `[−1+d, 2−d]²`. -/
def P29FirstIncr : Prop :=
  ∀ d > 0, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioo (0 : ℝ) (1 / 2), ∀ x x' : ℂ,
    x.re ∈ Icc (-1 + d) (-1 + 3 - d) → x.im ∈ Icc (-1 + d) (-1 + 3 - d) →
    x'.re ∈ Icc (-1 + d) (-1 + 3 - d) → x'.im ∈ Icc (-1 + d) (-1 + 3 - d) →
    ∫⁻ s in Ioc 0 1, ∫⁻ y in sqOpen (-1) 3,
        ENNReal.ofReal ((firstKer (-1) 3 t s x y - firstKer (-1) 3 t s x' y) ^ 2) ≤
      ENNReal.ofReal (C * ‖x - x'‖)

/-- the measurable version of `1_{s>0} 1_D(y) thirdKer t s x y` -/
def tkM (t : ℝ) (x : ℂ) : ℝ × ℂ → ℝ := zbKerFun (-1) 3 (heatBdd (sqOpen (-1) 3) (t / 2) x).1

lemma measurable_tkM (t : ℝ) (x : ℂ) : Measurable (tkM t x) :=
  measurable_zbKerFun (by norm_num) (heatBdd (sqOpen (-1) 3) (t / 2) x).2.1

lemma tkM_eq {t : ℝ} (ht : 0 < t) (x : ℂ) {q : ℝ × ℂ} (hq : 0 < q.1) (hy : q.2 ∈ sqOpen (-1) 3) :
    tkM t x q = thirdKer (-1) 3 t q.1 x q.2 := by
  rw [tkM, zbKerFun_heatBdd ht, indicator_of_mem (show q ∈ Ioi 0 ×ˢ sqOpen (-1) 3 from ⟨hq, hy⟩)]

lemma measurable_hkM (t : ℝ) (x : ℂ) :
    Measurable fun q : ℝ × ℂ => heatKernel ((t + q.1) / 2) x q.2 := by
  unfold heatKernel; fun_prop

lemma setLIntegral_prod_le (I : Set ℝ) (J : Set ℂ) (f : ℝ × ℂ → ℝ≥0∞) :
    ∫⁻ q in I ×ˢ J, f q ≤ ∫⁻ s in I, ∫⁻ y in J, f (s, y) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact lintegral_prod_le _

/-- the regions of the three terms -/
abbrev S1 : Set (ℝ × ℂ) := Ioc 0 1 ×ˢ sqOpen (-1) 3
abbrev S2 : Set (ℝ × ℂ) := Ioc 0 1 ×ˢ (sqOpen (-1) 3)ᶜ
abbrev S3 : Set (ℝ × ℂ) := Ioi (1 / 2) ×ˢ sqOpen (-1) 3

lemma mS1 : MeasurableSet S1 := measurableSet_Ioc.prod (measurableSet_sqOpen _ _)
lemma mS2 : MeasurableSet S2 := measurableSet_Ioc.prod (measurableSet_sqOpen _ _).compl
lemma mS3 : MeasurableSet S3 := measurableSet_Ioi.prod (measurableSet_sqOpen _ _)

/-- **Splitting** a quadratic functional of `dKer` into the three terms: if `Φ` is a function
of the values at `v` and `u` (here `(a − b)²` or `a²`) with `Φ (−a) (−b) = Φ a b`, `Φ 0 0 = 0`,
then `∫⁻ Φ(dKer t v, dKer t u) ≤ ∫_{S1} Φ(firstKer) + ∫_{S2} Φ(p) + ∫_{S3} Φ(thirdKer)`. -/
theorem lintegral_dKer_le {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) (Φ : ℝ → ℝ → ℝ≥0∞)
    (hΦm : Measurable fun p : ℝ × ℝ => Φ p.1 p.2) (hΦn : ∀ a b, Φ (-a) (-b) = Φ a b)
    (hΦ0 : Φ 0 0 = 0) (u v : ℂ) :
    ∫⁻ q, Φ (dKer t v q) (dKer t u q) ≤
      (∫⁻ s in Ioc 0 1, ∫⁻ y in sqOpen (-1) 3,
          Φ (firstKer (-1) 3 t s v y) (firstKer (-1) 3 t s u y)) +
        (∫⁻ s in Ioc 0 1, ∫⁻ y in (sqOpen (-1) 3)ᶜ,
          Φ (heatKernel ((t + s) / 2) v y) (heatKernel ((t + s) / 2) u y)) +
        (∫⁻ s in Ioi (1 / 2), ∫⁻ y in sqOpen (-1) 3,
          Φ (thirdKer (-1) 3 t s v y) (thirdKer (-1) 3 t s u y)) := by
  set g1 : ℝ × ℂ → ℝ≥0∞ := fun q =>
    Φ (tkM t v q - heatKernel ((t + q.1) / 2) v q.2) (tkM t u q - heatKernel ((t + q.1) / 2) u q.2)
  set g2 : ℝ × ℂ → ℝ≥0∞ := fun q => Φ (heatKernel ((t + q.1) / 2) v q.2)
    (heatKernel ((t + q.1) / 2) u q.2)
  set g3 : ℝ × ℂ → ℝ≥0∞ := fun q => Φ (tkM t v q) (tkM t u q)
  have hg1 : Measurable g1 := hΦm.comp
    (((measurable_tkM t v).sub (measurable_hkM t v)).prodMk
      ((measurable_tkM t u).sub (measurable_hkM t u)))
  have hg2 : Measurable g2 := hΦm.comp ((measurable_hkM t v).prodMk (measurable_hkM t u))
  have hg3 : Measurable g3 := hΦm.comp ((measurable_tkM t v).prodMk (measurable_tkM t u))
  have hpt : ∀ᵐ q ∂(volume : Measure (ℝ × ℂ)), Φ (dKer t v q) (dKer t u q) ≤
      S1.indicator g1 q + S2.indicator g2 q + S3.indicator g3 q := by
    filter_upwards [ae_fst_ne_zero] with q hq
    rcases dKer_cases ht q hq with ⟨hS, he⟩ | ⟨hS, he⟩ | ⟨hS, he⟩ | he
    · rw [he, he, hΦn, indicator_of_mem hS]
      simp only [g1, firstKer, tkM_eq ht.1 _ hS.1.1 hS.2]
      exact le_self_add.trans le_self_add
    · rw [he, he, indicator_of_mem hS]
      exact (le_add_left le_rfl).trans le_self_add
    · rw [he, he, hΦn, indicator_of_mem hS]
      simp only [g3, tkM_eq ht.1 _ (lt_trans (by norm_num) hS.1) hS.2]
      exact le_add_left le_rfl
    · rw [he, he, hΦ0]; exact bot_le
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_add_left (f := fun q => S1.indicator g1 q + S2.indicator g2 q)
      ((hg1.indicator mS1).add (hg2.indicator mS2)),
    lintegral_add_left (hg1.indicator mS1), lintegral_indicator mS1, lintegral_indicator mS2,
    lintegral_indicator mS3]
  have e1 : ∫⁻ q in S1, g1 q = ∫⁻ q in S1, Φ (firstKer (-1) 3 t q.1 v q.2)
      (firstKer (-1) 3 t q.1 u q.2) := by
    refine setLIntegral_congr_fun mS1 fun q hq => ?_
    simp only [g1, firstKer, tkM_eq ht.1 _ hq.1.1 hq.2]
  have e3 : ∫⁻ q in S3, g3 q = ∫⁻ q in S3, Φ (thirdKer (-1) 3 t q.1 v q.2)
      (thirdKer (-1) 3 t q.1 u q.2) := by
    refine setLIntegral_congr_fun mS3 fun q hq => ?_
    simp only [g3, tkM_eq ht.1 _ (lt_trans (by norm_num) hq.1) hq.2]
  rw [e1, e3]
  gcongr
  · exact setLIntegral_prod_le _ _ (fun q => Φ (firstKer (-1) 3 t q.1 v q.2)
      (firstKer (-1) 3 t q.1 u q.2))
  · exact setLIntegral_prod_le _ _ g2
  · exact setLIntegral_prod_le _ _ (fun q => Φ (thirdKer (-1) 3 t q.1 v q.2)
      (thirdKer (-1) 3 t q.1 u q.2))

end P29WN
end DDDF
end LQGMetric
