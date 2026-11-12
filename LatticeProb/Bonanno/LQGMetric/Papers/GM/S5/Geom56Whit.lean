/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56Whit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56Step
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# GM Lemma 5.6, condition 3: the Whitney chain to the centre of a square (task P2-M2L56)

See `Geom56Step.lean`. `geom56_whitney`: for a closed grid square `S` of side `s` with `int S ⊆ V`
and `p ∈ S` with a ball `B_ρ(p) ⊆ V`, `d(p, c_S; V) ≤ (2 + 32/(1 − 2^{-χ})) t` when every dyadic
square of side `2^{-j} s` meeting `S` has internal diameter `≤ 2^{-jχ} t`.
Own elementary argument (Whitney chain; GM l. 2991–2994 leave it implicit).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the centre of the grid square `gridSquare s m` -/
def sqCenter (s : ℝ) (m : ℤ × ℤ) : ℂ := ⟨(m.1 + 1 / 2) * s, (m.2 + 1 / 2) * s⟩

/-- the point `p + λ (c − p)` -/
def whitPt (c p : ℂ) (l : ℝ) : ℂ := p + (l : ℂ) * (c - p)

lemma whitPt_re (c p : ℂ) (l : ℝ) : (whitPt c p l).re = p.re + l * (c.re - p.re) := by
  simp [whitPt]

lemma whitPt_im (c p : ℂ) (l : ℝ) : (whitPt c p l).im = p.im + l * (c.im - p.im) := by
  simp [whitPt]

lemma whitPt_sub (c p : ℂ) (l l' : ℝ) :
    whitPt c p l - whitPt c p l' = ((l - l' : ℝ) : ℂ) * (c - p) := by
  simp only [whitPt]; push_cast; ring

lemma norm_center_sub_le {s : ℝ} {m : ℤ × ℤ} {p : ℂ} (hp : p ∈ gridSquare s m) :
    ‖sqCenter s m - p‖ ≤ s := by
  obtain ⟨a1, a2, a3, a4⟩ := hp
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [sqCenter, Complex.sub_re, Complex.sub_im]
  have h1 : |(m.1 + 1 / 2) * s - p.re| ≤ s / 2 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have h2 : |(m.2 + 1 / 2) * s - p.im| ≤ s / 2 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  linarith

/-- the open box is in the interior of the closed square -/
lemma openBox_subset_interior (s : ℝ) (m : ℤ × ℤ) :
    {x : ℂ | m.1 * s < x.re ∧ x.re < (m.1 + 1) * s ∧ m.2 * s < x.im ∧ x.im < (m.2 + 1) * s} ⊆
      interior (gridSquare s m) := by
  refine interior_maximal (fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le⟩) ?_
  exact ((isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const))))

/-- `B_{λ s/2}(p + λ(c − p)) ⊆ int S` (homothety from `p`) -/
lemma ball_whitPt_subset {s : ℝ} {m : ℤ × ℤ} {p : ℂ} (hp : p ∈ gridSquare s m) {l : ℝ}
    (_hl : 0 < l) (hl1 : l ≤ 1) :
    ball (whitPt (sqCenter s m) p l) (l * s / 2) ⊆ interior (gridSquare s m) := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  have hre : |w.re - (whitPt (sqCenter s m) p l).re| < l * s / 2 := by
    rw [← Complex.sub_re]; exact lt_of_le_of_lt (Complex.abs_re_le_norm _) hw
  have him : |w.im - (whitPt (sqCenter s m) p l).im| < l * s / 2 := by
    rw [← Complex.sub_im]; exact lt_of_le_of_lt (Complex.abs_im_le_norm _) hw
  rw [whitPt_re, abs_lt] at hre
  rw [whitPt_im, abs_lt] at him
  obtain ⟨a1, a2, a3, a4⟩ := hp
  simp only [sqCenter] at hre him
  have hl' : 0 ≤ 1 - l := by linarith
  apply openBox_subset_interior
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg hl' (sub_nonneg.2 a1),
    mul_nonneg hl' (sub_nonneg.2 a2), mul_nonneg hl' (sub_nonneg.2 a3),
    mul_nonneg hl' (sub_nonneg.2 a4)]

lemma whitPt_mem {s : ℝ} (hs : 0 < s) {m : ℤ × ℤ} {p : ℂ} (hp : p ∈ gridSquare s m) {l : ℝ}
    (hl : 0 < l) (hl1 : l ≤ 1) : whitPt (sqCenter s m) p l ∈ gridSquare s m :=
  interior_subset (ball_whitPt_subset hp hl hl1 (mem_ball_self (by positivity)))

lemma inv_two_pow_rpow (χ : ℝ) (n : ℕ) : ((2 : ℝ)⁻¹ ^ n) ^ χ = ((2 : ℝ)⁻¹ ^ χ) ^ n :=
  (Real.rpow_pow_comm (by norm_num) χ n).symm

lemma norm_whitPt_sub (c p : ℂ) (l l' : ℝ) :
    ‖whitPt c p l - whitPt c p l'‖ = |l - l'| * ‖c - p‖ := by
  rw [whitPt_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- one level of the Whitney chain: from `λ = 2^{-k}` to `λ = 2^{-k-1}`, in 16 steps through
squares of side `2^{-k-4} s` -/
lemma geom56_level (d : ContMetric) {V : Set ℂ} {s : ℝ} (hs : 0 < s) {m : ℤ × ℤ}
    (hSV : interior (gridSquare s m) ⊆ V) {p : ℂ} (hp : p ∈ gridSquare s m) {χ t : ℝ}
    (hB : ∀ (j : ℕ) (m' : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m' ∩ gridSquare s m).Nonempty →
      internalDiam d (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m') (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m') ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ * t)) (k : ℕ) :
    d.internal V (whitPt (sqCenter s m) p ((2 : ℝ)⁻¹ ^ k))
      (whitPt (sqCenter s m) p ((2 : ℝ)⁻¹ ^ (k + 1))) ≤
      32 * ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (k + 4)) ^ χ * t) := by
  set a : ℝ := (2 : ℝ)⁻¹ ^ k with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set c := sqCenter s m
  set B := ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (k + 4)) ^ χ * t)
  set f : ℕ → ℂ := fun i => whitPt c p (a * (1 - i / 32)) with hf
  have hf0 : f 0 = whitPt c p a := by simp [f]
  have hf16 : f 16 = whitPt c p ((2 : ℝ)⁻¹ ^ (k + 1)) := by
    simp only [f, ha, pow_succ]; norm_num
  have hσ : (2 : ℝ)⁻¹ ^ (k + 4) * s = a * s / 16 := by
    rw [ha, pow_add]; ring
  have hcp := norm_center_sub_le hp
  have hstep : ∀ i < 16, d.internal V (f i) (f (i + 1)) ≤ 2 * B := by
    intro i hi
    have hi' : (i : ℝ) ≤ 15 := by exact_mod_cast Nat.lt_succ_iff.1 hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hl : ∀ l : ℝ, 0 ≤ l → l ≤ 16 → 0 < a * (1 - l / 32) ∧ a * (1 - l / 32) ≤ 1 ∧
        ball (whitPt c p (a * (1 - l / 32))) (3 * ((2 : ℝ)⁻¹ ^ (k + 4) * s)) ⊆ V := by
      intro l hl0 hl16
      have h1 : 0 < a * (1 - l / 32) := mul_pos ha0 (by linarith)
      have h2 : a * (1 - l / 32) ≤ 1 := by nlinarith
      refine ⟨h1, h2, ?_⟩
      refine (ball_subset_ball ?_).trans ((ball_whitPt_subset hp h1 h2).trans hSV)
      rw [hσ]; nlinarith [mul_nonneg (mul_nonneg ha0.le hs.le) (by linarith : (0 : ℝ) ≤ 20 - l)]
    obtain ⟨x1, x2, x3⟩ := hl i hi0 (by linarith)
    obtain ⟨y1, y2, y3⟩ := hl ((i : ℝ) + 1) (by linarith) (by linarith)
    have hx : f i ∈ gridSquare s m := whitPt_mem hs hp x1 x2
    have hy : f (i + 1) ∈ gridSquare s m := by
      simp only [f]; push_cast; exact whitPt_mem hs hp y1 y2
    refine geom56_step d (by positivity) ?_ x3 ?_ ?_
    · simp only [f]; push_cast
      rw [norm_whitPt_sub, hσ]
      have : |a * (1 - i / 32) - a * (1 - (i + 1) / 32)| = a / 32 := by
        rw [show a * (1 - i / 32) - a * (1 - (i + 1) / 32) = a / 32 by ring]
        exact abs_of_pos (by positivity)
      rw [this]; nlinarith
    · simpa [f] using y3
    · rintro m' (h | h)
      · exact hB (k + 4) m' ⟨f i, h, hx⟩
      · exact hB (k + 4) m' ⟨f (i + 1), h, hy⟩
  rw [← hf0, ← hf16]
  calc d.internal V (f 0) (f (15 + 1))
      ≤ ∑ i ∈ Finset.range (15 + 1), d.internal V (f i) (f (i + 1)) := internal_le_sum_seq d V f 15
    _ ≤ ∑ _i ∈ Finset.range (15 + 1), 2 * B :=
        Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.1 hi)
    _ = 32 * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]; norm_num

/-- **the Whitney chain** (GM l. 2991–2994, made explicit): a point `p` of a closed grid square
`S = gridSquare s m` with `int S ⊆ V` and `B_ρ(p) ⊆ V` is at `d(·,·;V)`-distance
`≤ (2 + 32/(1 − 2^{-χ})) t` from the centre of `S`, when every square of side `2^{-j} s` meeting `S`
has internal diameter `≤ 2^{-jχ} t` -/
lemma geom56_whitney (d : ContMetric) {V : Set ℂ} {s : ℝ} (hs : 0 < s) {m : ℤ × ℤ}
    (hSV : interior (gridSquare s m) ⊆ V) {p : ℂ} (hp : p ∈ gridSquare s m) {ρ : ℝ} (hρ : 0 < ρ)
    (hpV : ball p ρ ⊆ V) {χ t : ℝ} (hχ : 0 < χ) (ht : 0 ≤ t)
    (hB : ∀ (j : ℕ) (m' : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m' ∩ gridSquare s m).Nonempty →
      internalDiam d (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m') (gridSquare ((2 : ℝ)⁻¹ ^ j * s) m') ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ χ * t)) :
    d.internal V p (sqCenter s m) ≤ ENNReal.ofReal ((2 + 32 / (1 - (2 : ℝ)⁻¹ ^ χ)) * t) := by
  set q : ℝ := (2 : ℝ)⁻¹ ^ χ with hqdef
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hχ
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ρ / (4 * s) by positivity)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  set c := sqCenter s m
  set g : ℕ → ℂ := fun k => whitPt c p ((2 : ℝ)⁻¹ ^ k) with hg
  have hg0 : g 0 = c := by simp [g, whitPt]
  have hcp := norm_center_sub_le hp
  have hlev : d.internal V c (g (K + 1)) ≤ ENNReal.ofReal (32 / (1 - q) * t) := by
    rw [← hg0]
    refine (internal_le_sum_seq d V g K).trans ?_
    calc ∑ k ∈ Finset.range (K + 1), d.internal V (g k) (g (k + 1))
        ≤ ∑ k ∈ Finset.range (K + 1), ENNReal.ofReal (32 * (q ^ k * t)) := by
          refine Finset.sum_le_sum fun k _ => (geom56_level d hs hSV hp hB k).trans ?_
          rw [inv_two_pow_rpow, ← hqdef, ← ENNReal.ofReal_ofNat 32, ← ENNReal.ofReal_mul (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one hq0.le hq1.le (by omega)) ht) (by norm_num))
      _ = ENNReal.ofReal (∑ k ∈ Finset.range (K + 1), 32 * (q ^ k * t)) :=
          (ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity).symm
      _ ≤ ENNReal.ofReal (32 / (1 - q) * t) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show ∑ k ∈ Finset.range (K + 1), 32 * (q ^ k * t) =
            (32 * t) * ∑ k ∈ Finset.range (K + 1), q ^ k by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring,
            show 32 / (1 - q) * t = (32 * t) * (1 - q)⁻¹ by ring]
          have hgs := geom_sum_Ico_le_of_lt_one (m := 0) (n := K + 1) hq0.le hq1
          rw [← Finset.range_eq_Ico, pow_zero, one_div] at hgs
          exact mul_le_mul_of_nonneg_left hgs (by positivity)
  have hfin : d.internal V (g (K + 1)) p ≤ ENNReal.ofReal (2 * t) := by
    have hσ0 : 0 < (2 : ℝ)⁻¹ ^ K * s := by positivity
    have hK' : 4 * ((2 : ℝ)⁻¹ ^ K * s) < ρ := by
      rw [lt_div_iff₀ (by positivity)] at hK; linarith
    have hgp : ‖g (K + 1) - p‖ < (2 : ℝ)⁻¹ ^ K * s := by
      have : g (K + 1) - p = (((2 : ℝ)⁻¹ ^ (K + 1) : ℝ) : ℂ) * (c - p) := by
        simp only [g, whitPt]; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        pow_succ]
      have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
      nlinarith
    have hgS : g (K + 1) ∈ gridSquare s m := whitPt_mem hs hp (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
    refine (geom56_step d (B := ENNReal.ofReal (((2 : ℝ)⁻¹ ^ K) ^ χ * t)) hσ0 hgp ?_ ?_ ?_).trans ?_
    · refine (ball_subset_ball' ?_).trans hpV
      rw [dist_eq_norm]; linarith
    · exact (ball_subset_ball (by linarith)).trans hpV
    · rintro m' (h | h)
      · exact hB K m' ⟨_, h, hgS⟩
      · exact hB K m' ⟨_, h, hp⟩
    · rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left ht
        (Real.rpow_le_one (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) hχ.le))
        (by norm_num))
  calc d.internal V p c = d.internal V c p := MetricGeometry.internalEDist_comm _ _ _
    _ ≤ d.internal V c (g (K + 1)) + d.internal V (g (K + 1)) p := DFGPS.internal_triangle d V _ _ _
    _ ≤ ENNReal.ofReal (32 / (1 - q) * t) + ENNReal.ofReal (2 * t) := add_le_add hlev hfin
    _ = ENNReal.ofReal ((2 + 32 / (1 - q)) * t) := by
        have h1q : 0 < 1 - q := by linarith
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end LQGMetric.GM
