/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28U1Aux at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Mean
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Link

/-!
# DDDF Prop 28 Part 1 Step 1 for the family: elementary helpers (task P2-DDDF28U)

Own elementary facts used in the assembly (`S6P28U1Fin`): the splitting `δ = 2^{-(N+r)}` with
`r ∈ (0,1]`, real powers of ratios, the Markov step for the annuli, and the four-piece split of a
long segment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28U

open LFPP Blueprint

/-- `δ ∈ (0,1)` is `2^{-(N+r)}` with `r ∈ (0,1]` -/
lemma exists_split' {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    ∃ (N : ℕ) (r : ℝ), 0 < r ∧ r ≤ 1 ∧ δ = (2 : ℝ) ^ (-((N : ℝ) + r)) := by
  obtain ⟨n, r, hr0, hr1, hδ⟩ := S6.exists_split h0 h1
  rcases hr0.lt_or_eq with h | h
  · exact ⟨n, r, h, hr1, hδ⟩
  · subst h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at hδ; linarith
    · refine ⟨n - 1, 1, one_pos, le_rfl, ?_⟩
      rw [hδ, Nat.cast_sub hn]; congr 1; push_cast; ring

/-- `δ^{β−1} t ≤ 64^{|1−β|} t^β` for `δ ≤ t ≤ 64 δ` -/
lemma rpow_ratio {δ t β : ℝ} (hδ : 0 < δ) (h1 : δ ≤ t) (h2 : t ≤ 64 * δ) :
    δ ^ (β - 1) * t ≤ (64 : ℝ) ^ |1 - β| * t ^ β := by
  have ht : 0 < t := hδ.trans_le h1
  have e : δ ^ (β - 1) * t = (t / δ) ^ (1 - β) * t ^ β := by
    rw [Real.div_rpow ht.le hδ.le, show β - 1 = -(1 - β) by ring, Real.rpow_neg hδ.le]
    have : t = t ^ (1 - β) * t ^ β := by rw [← Real.rpow_add ht]; simp
    calc (δ ^ (1 - β))⁻¹ * t = (δ ^ (1 - β))⁻¹ * (t ^ (1 - β) * t ^ β) := by rw [← this]
      _ = t ^ (1 - β) / δ ^ (1 - β) * t ^ β := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht.le _)
  have hρ1 : 1 ≤ t / δ := by rw [le_div_iff₀ hδ]; linarith
  have hρ2 : t / δ ≤ 64 := by rw [div_le_iff₀ hδ]; linarith
  rcases le_total 0 (1 - β) with h | h
  · rw [abs_of_nonneg h]; exact Real.rpow_le_rpow (by linarith) hρ2 h
  · calc (t / δ) ^ (1 - β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hρ1 h
      _ ≤ (64 : ℝ) ^ |1 - β| := Real.one_le_rpow (by norm_num) (abs_nonneg _)

/-- `lenMetricOn` from a bound on `lfppDOn` -/
lemma lenMetricOn_le_of {ξ : ℝ} {f : ℂ → ℝ} {x y : ℂ} {v : ℝ} (hv : 0 ≤ v)
    (h : lfppDOn ξ f closedUnitSquare x y ≤ ENNReal.ofReal v) :
    lenMetricOn ξ f closedUnitSquare x y ≤ v := by
  simp only [lenMetricOn, DFGPS.crossLenIn_singleton]
  exact ENNReal.toReal_le_of_le_ofReal hv h

/-- **four pieces**: a segment of `[0,1]²` is cut into four pieces whose coordinates differ by
at most a quarter -/
lemma four_pieces {d : ℂ → ℂ → ℝ≥0∞} (htri : ∀ a b c, d a c ≤ d a b + d b c) {x y : ℂ}
    (hx : x ∈ closedUnitSquare) (hy : y ∈ closedUnitSquare) {B : ℝ≥0∞}
    (hB : ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare, |z.re - w.re| < 2⁻¹ →
      |z.im - w.im| < 2⁻¹ → d z w ≤ B) : d x y ≤ 4 * B := by
  set p : ℕ → ℂ := fun i => x + ((i : ℝ) / 4 : ℝ) • (y - x)
  have hp : ∀ i : ℕ, i ≤ 4 → p i ∈ closedUnitSquare := fun i hi =>
    DFGPS.convex_closedUnitSquare.add_smul_sub_mem hx hy
      ⟨by positivity, by rw [div_le_one (by norm_num)]; exact_mod_cast hi⟩
  have hre : |(x - y).re| ≤ 1 := by
    obtain ⟨a1, a2, -, -⟩ := hx
    obtain ⟨b1, b2, -, -⟩ := hy
    rw [Complex.sub_re, abs_le]; constructor <;> linarith
  have him : |(x - y).im| ≤ 1 := by
    obtain ⟨-, -, a1, a2⟩ := hx
    obtain ⟨-, -, b1, b2⟩ := hy
    rw [Complex.sub_im, abs_le]; constructor <;> linarith
  have hstep : ∀ i : ℕ, i < 4 → d (p i) (p (i + 1)) ≤ B := by
    intro i hi
    have e : p i - p (i + 1) = (((1 : ℝ) / 4 : ℝ) : ℂ) * (x - y) := by
      simp only [p, Complex.real_smul]; push_cast; ring
    refine hB _ (hp i hi.le) _ (hp (i + 1) hi) ?_ ?_
    · rw [← Complex.sub_re, e, Complex.re_ofReal_mul, abs_mul]
      have : |(1 : ℝ) / 4| = 1 / 4 := by norm_num
      rw [this]; linarith
    · rw [← Complex.sub_im, e, Complex.im_ofReal_mul, abs_mul]
      have : |(1 : ℝ) / 4| = 1 / 4 := by norm_num
      rw [this]; linarith
  have h0 : p 0 = x := by simp [p]
  have h4 : p 4 = y := by simp [p]
  calc d x y = d (p 0) (p 4) := by rw [h0, h4]
    _ ≤ d (p 0) (p 3) + d (p 3) (p 4) := htri _ _ _
    _ ≤ d (p 0) (p 2) + d (p 2) (p 3) + d (p 3) (p 4) := by gcongr; exact htri _ _ _
    _ ≤ d (p 0) (p 1) + d (p 1) (p 2) + d (p 2) (p 3) + d (p 3) (p 4) := by
        gcongr; exact htri _ _ _
    _ ≤ B + B + B + B := by
        gcongr
        exacts [hstep 0 (by norm_num), hstep 1 (by norm_num), hstep 2 (by norm_num),
          hstep 3 (by norm_num)]
    _ = 4 * B := by ring

end S6P28U
end DDDF
end LQGMetric
