/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29Split at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29KerFn
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P29First

/-!
# DDDF Proposition 29: splitting the kernel `dKer` into DDDF's three terms (R4 bookkeeping)

DDDF arXiv:1904.08021, `tightness.tex` (6.97) (DD:1555): for `s ≠ 0` the kernel
`dKer t x (s, y)` of `φ_t − p_{t/2} * h` is
* `−firstKer t s x y = p_{(t+s)/2}(x,y) − (p_{t/2} * p^D_{s/2})(x,y)` for `0 < s ≤ 1 − t`, `y ∈ D`
  (the first term `φ¹_t − η¹_t`);
* `p_{(t+s)/2}(x, y)` for `0 < s ≤ 1 − t`, `y ∉ D` (the second term `φ²_t`);
* `−(p_{t/2} * p^D_{s/2})(x, y)` for `s > 1 − t`, `y ∈ D` (the third term `η²_t`);
* `0` otherwise (`dKer_cases`).
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

/-- the four regions of `dKer` (DD:1529–1541) -/
theorem dKer_cases {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) (q : ℝ × ℂ) (hq : q.1 ≠ 0) :
    (q ∈ Ioc 0 1 ×ˢ sqOpen (-1) 3 ∧
        ∀ x, dKer t x q = -firstKer (-1) 3 t q.1 x q.2) ∨
      (q ∈ Ioc 0 1 ×ˢ (sqOpen (-1) 3)ᶜ ∧ ∀ x, dKer t x q = heatKernel ((t + q.1) / 2) x q.2) ∨
      (q ∈ Ioi (1 / 2) ×ˢ sqOpen (-1) 3 ∧ ∀ x, dKer t x q = -thirdKer (-1) 3 t q.1 x q.2) ∨
      (∀ x, dKer t x q = 0) := by
  obtain ⟨ht0, ht1⟩ := ht
  rcases lt_or_gt_of_ne hq with hs | hs
  · right; right; right
    intro x
    have h1 : q ∉ Icc 0 (1 - t) ×ˢ (univ : Set ℂ) := fun h => by linarith [h.1.1]
    have h2 : q ∉ Ioi 0 ×ˢ sqOpen (-1) 3 := fun h => by linarith [mem_Ioi.1 h.1]
    rw [dKer, indicator_of_notMem h1, indicator_of_notMem h2, sub_zero]
  by_cases hy : q.2 ∈ sqOpen (-1) 3
  · have h2 : q ∈ Ioi 0 ×ˢ sqOpen (-1) 3 := ⟨hs, hy⟩
    by_cases hs1 : q.1 ≤ 1 - t
    · left
      have h1 : q ∈ Icc 0 (1 - t) ×ˢ (univ : Set ℂ) := ⟨⟨hs.le, hs1⟩, trivial⟩
      refine ⟨⟨⟨hs, by linarith⟩, hy⟩, fun x => ?_⟩
      rw [dKer, indicator_of_mem h1, indicator_of_mem h2, firstKer]; ring
    · right; right; left
      have h1 : q ∉ Icc 0 (1 - t) ×ˢ (univ : Set ℂ) := fun h => hs1 h.1.2
      refine ⟨⟨show (1 / 2 : ℝ) < q.1 by linarith, hy⟩, fun x => ?_⟩
      rw [dKer, indicator_of_notMem h1, indicator_of_mem h2, zero_sub]
  · have h2 : q ∉ Ioi 0 ×ˢ sqOpen (-1) 3 := fun h => hy h.2
    by_cases hs1 : q.1 ≤ 1 - t
    · right; left
      have h1 : q ∈ Icc 0 (1 - t) ×ˢ (univ : Set ℂ) := ⟨⟨hs.le, hs1⟩, trivial⟩
      refine ⟨⟨⟨hs, by linarith⟩, hy⟩, fun x => ?_⟩
      rw [dKer, indicator_of_mem h1, indicator_of_notMem h2, sub_zero]
    · right; right; right
      intro x
      have h1 : q ∉ Icc 0 (1 - t) ×ˢ (univ : Set ℂ) := fun h => hs1 h.1.2
      rw [dKer, indicator_of_notMem h1, indicator_of_notMem h2, sub_zero]

/-- `{q | q.1 = 0}` is null, so `q.1 ≠ 0` a.e. on `ℝ × ℂ` -/
lemma ae_fst_ne_zero : ∀ᵐ q ∂(volume : Measure (ℝ × ℂ)), q.1 ≠ 0 := by
  rw [Measure.volume_eq_prod, ae_iff]
  have e : {a : ℝ × ℂ | ¬a.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (univ : Set ℂ) := by
    ext q; simp
  rw [e, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- the integral of `G((t+s)/2)` over `s > 0` is at most `2 ∫_{r>0} G(r) dr` -/
lemma lintegral_comp_half_le (G : ℝ → ℝ≥0∞) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Ioi 0, G ((t + s) / 2) ≤ 2 * ∫⁻ r in Ioi 0, G r := by
  have h1 : ∫⁻ s in Ioi 0, G ((t + s) / 2) ≤
      ∫⁻ s, (Ioi (0 : ℝ)).indicator G ((t + s) / 2) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_mono fun s => ?_
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hs, indicator_of_mem (show (t + s) / 2 ∈ Ioi (0 : ℝ) from by
        have := mem_Ioi.1 hs; rw [mem_Ioi]; linarith)]
    · rw [indicator_of_notMem hs]; exact bot_le
  have h2 : ∫⁻ s, (Ioi (0 : ℝ)).indicator G ((t + s) / 2) =
      ∫⁻ s, (Ioi (0 : ℝ)).indicator G (2⁻¹ * s) := by
    have := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun s => (Ioi (0 : ℝ)).indicator G (2⁻¹ * s)) t
    rw [← this]
    congr 1; funext s; congr 1; ring
  have h3 : ∫⁻ s, (Ioi (0 : ℝ)).indicator G (2⁻¹ * s) =
      2 * ∫⁻ r in Ioi 0, G r := by
    have e := lintegral_map_equiv (μ := (volume : Measure ℝ)) ((Ioi (0 : ℝ)).indicator G)
      (Homeomorph.mulLeft₀ (2⁻¹ : ℝ) (by norm_num)).toMeasurableEquiv
    have hm : Measure.map (Homeomorph.mulLeft₀ (2⁻¹ : ℝ) (by norm_num)).toMeasurableEquiv
        volume = ENNReal.ofReal |(2⁻¹ : ℝ)⁻¹| • volume :=
      Real.map_volume_mul_left (by norm_num)
    rw [hm] at e
    simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.coe_mulLeft₀] at e
    rw [← e, lintegral_smul_measure, lintegral_indicator measurableSet_Ioi]
    norm_num
  rw [h2, h3] at h1
  exact h1

end P29WN
end DDDF
end LQGMetric
