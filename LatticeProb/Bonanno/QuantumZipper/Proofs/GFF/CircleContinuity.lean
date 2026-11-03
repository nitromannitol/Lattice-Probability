/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.CircleContinuity at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Data.Int.Interval
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Kolmogorov continuity of circle averages of the free GFF

Dyadic-chaining version of the Kolmogorov–Chentsov theorem on the closed upper half-plane,
for a process `Z : ℂ → Ω → ℝ` with an eighth-moment bound
`E|Z z − Z w|⁸ ≤ K ‖z − w‖⁴` on `Hbar` (Section 1–2), and its application to the
folded-circle averages of a free-boundary GFF (Section 3).

Chaining: on the box `boxR R = [−R,R] × [0,R]`, call level `j` good when all increments
between horizontally or vertically adjacent points of the level-`j` dyadic lattice are
`≤ θ^j`, `θ = 7/8`. By Markov and a union bound, level `j` is bad with probability
`≤ C_R q^j`, `q = (8/7)⁸/4 < 1`; Borel–Cantelli makes all large levels good, and then the
dyadic roundings `dyadicRoundC M z` form a Cauchy sequence with a uniform modulus.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace QuantumZipper
namespace CircleCont

/-! ## 1. Dyadic lattice and deterministic chaining -/

/-- The level-`j` dyadic lattice point with integer coordinates `(a, b)`. -/
def lpt (j : ℕ) (a b : ℤ) : ℂ := ⟨(a : ℝ) / 2 ^ j, (b : ℝ) / 2 ^ j⟩

theorem dyadicRoundC_eq_lpt (j : ℕ) (z : ℂ) :
    dyadicRoundC j z = lpt j ⌊(2 : ℝ) ^ j * z.re⌋ ⌊(2 : ℝ) ^ j * z.im⌋ := rfl

/-- The chaining ratio. -/
def θc : ℝ := 7 / 8

theorem θc_pos : 0 < θc := by norm_num [θc]

theorem θc_lt_one : θc < 1 := by norm_num [θc]

/-- The box `[−R, R] × [0, R]`. -/
def boxR (R : ℕ) : Set ℂ := {z | |z.re| ≤ R ∧ 0 ≤ z.im ∧ z.im ≤ R}

/-- Lattice indices of level `j` inside `boxR R`. -/
def InRange (R j : ℕ) (a b : ℤ) : Prop :=
  -((R : ℤ) * 2 ^ j) ≤ a ∧ a ≤ (R : ℤ) * 2 ^ j ∧ 0 ≤ b ∧ b ≤ (R : ℤ) * 2 ^ j

/-- All adjacent increments of `f` at level `j` based in `boxR R` are at most `θ^j`. -/
def GoodLevel (f : ℂ → ℝ) (R j : ℕ) : Prop :=
  ∀ a b : ℤ, InRange R j a b →
    |f (lpt j (a + 1) b) - f (lpt j a b)| ≤ θc ^ j ∧
      |f (lpt j a (b + 1)) - f (lpt j a b)| ≤ θc ^ j

variable {f : ℂ → ℝ} {R : ℕ}

theorem step_re {j : ℕ} (hg : GoodLevel f R j) {a a' b : ℤ} (ha : InRange R j a b)
    (ha' : InRange R j a' b) (h1 : |a - a'| ≤ 1) :
    |f (lpt j a' b) - f (lpt j a b)| ≤ θc ^ j := by
  rw [abs_le] at h1
  rcases (show a' = a + 1 ∨ a' = a ∨ a = a' + 1 by omega) with h | h | h
  · subst h; exact (hg a b ha).1
  · subst h; simp [pow_nonneg θc_pos.le]
  · subst h; rw [abs_sub_comm]; exact (hg a' b ha').1

theorem step_im {j : ℕ} (hg : GoodLevel f R j) {a b b' : ℤ} (hb : InRange R j a b)
    (hb' : InRange R j a b') (h1 : |b - b'| ≤ 1) :
    |f (lpt j a b') - f (lpt j a b)| ≤ θc ^ j := by
  rw [abs_le] at h1
  rcases (show b' = b + 1 ∨ b' = b ∨ b = b' + 1 by omega) with h | h | h
  · subst h; exact (hg a b hb).2
  · subst h; simp [pow_nonneg θc_pos.le]
  · subst h; rw [abs_sub_comm]; exact (hg a b' hb').2

theorem near {j : ℕ} (hg : GoodLevel f R j) {a b a' b' : ℤ} (h : InRange R j a b)
    (h' : InRange R j a' b') (ha : |a - a'| ≤ 1) (hb : |b - b'| ≤ 1) :
    |f (lpt j a' b') - f (lpt j a b)| ≤ 2 * θc ^ j := by
  have hm : InRange R j a' b := ⟨h'.1, h'.2.1, h.2.2.1, h.2.2.2⟩
  have e1 := step_re hg h hm ha
  have e2 := step_im hg hm h' hb
  calc |f (lpt j a' b') - f (lpt j a b)|
      = |(f (lpt j a' b') - f (lpt j a' b)) + (f (lpt j a' b) - f (lpt j a b))| := by
        congr 1; ring
    _ ≤ |f (lpt j a' b') - f (lpt j a' b)| + |f (lpt j a' b) - f (lpt j a b)| :=
        abs_add_le _ _
    _ ≤ 2 * θc ^ j := by linarith

theorem inRange_floor {z : ℂ} (hz : z ∈ boxR R) (j : ℕ) :
    InRange R j ⌊(2 : ℝ) ^ j * z.re⌋ ⌊(2 : ℝ) ^ j * z.im⌋ := by
  obtain ⟨hre, him0, him⟩ := hz
  rw [abs_le] at hre
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  refine ⟨Int.le_floor.2 ?_, ?_, Int.le_floor.2 ?_, ?_⟩
  · push_cast; nlinarith
  · have : ⌊(2 : ℝ) ^ j * z.re⌋ ≤ ⌊(((R : ℤ) * 2 ^ j : ℤ) : ℝ)⌋ :=
      Int.floor_mono (by push_cast; nlinarith)
    rwa [Int.floor_intCast] at this
  · push_cast; exact mul_nonneg hp.le him0
  · have : ⌊(2 : ℝ) ^ j * z.im⌋ ≤ ⌊(((R : ℤ) * 2 ^ j : ℤ) : ℝ)⌋ :=
      Int.floor_mono (by push_cast; nlinarith)
    rwa [Int.floor_intCast] at this

theorem lpt_succ (j : ℕ) (a b : ℤ) : lpt j a b = lpt (j + 1) (2 * a) (2 * b) := by
  rw [Complex.ext_iff]
  simp only [lpt]
  push_cast
  rw [pow_succ, mul_comm ((2 : ℝ) ^ j) 2, mul_div_mul_left _ _ two_ne_zero,
    mul_div_mul_left _ _ two_ne_zero]
  exact ⟨rfl, rfl⟩

theorem floor_succ_bounds (j : ℕ) (x : ℝ) :
    2 * ⌊(2 : ℝ) ^ j * x⌋ ≤ ⌊(2 : ℝ) ^ (j + 1) * x⌋ ∧
      ⌊(2 : ℝ) ^ (j + 1) * x⌋ ≤ 2 * ⌊(2 : ℝ) ^ j * x⌋ + 1 := by
  have e : (2 : ℝ) ^ (j + 1) * x = 2 * ((2 : ℝ) ^ j * x) := by ring
  rw [e]
  set y := (2 : ℝ) ^ j * x
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  constructor
  · apply Int.le_floor.2; push_cast; linarith
  · have : ⌊2 * y⌋ < 2 * ⌊y⌋ + 2 := by
      apply Int.floor_lt.2; push_cast; linarith
    omega

theorem abs_floor_sub_le_one {x y : ℝ} (h : |x - y| < 1) : |⌊x⌋ - ⌊y⌋| ≤ 1 := by
  rw [abs_lt] at h
  have h1 : ⌊x⌋ < ⌊y⌋ + 2 :=
    Int.floor_lt.2 (by push_cast; linarith [Int.lt_floor_add_one y])
  have h2 : ⌊y⌋ < ⌊x⌋ + 2 :=
    Int.floor_lt.2 (by push_cast; linarith [Int.lt_floor_add_one x])
  rw [abs_le]; constructor <;> omega

theorem consec {z : ℂ} (hz : z ∈ boxR R) {j : ℕ} (hg : GoodLevel f R (j + 1)) :
    |f (dyadicRoundC (j + 1) z) - f (dyadicRoundC j z)| ≤ 2 * θc ^ (j + 1) := by
  rw [dyadicRoundC_eq_lpt, dyadicRoundC_eq_lpt j, lpt_succ j]
  have h0 := inRange_floor hz j
  have h1 := inRange_floor hz (j + 1)
  obtain ⟨a1, a2⟩ := floor_succ_bounds j z.re
  obtain ⟨b1, b2⟩ := floor_succ_bounds j z.im
  refine near hg ?_ h1 ?_ ?_
  · have e : ((R : ℤ) * 2 ^ (j + 1)) = 2 * ((R : ℤ) * 2 ^ j) := by ring
    unfold InRange at h0 ⊢
    rw [e]
    generalize (R : ℤ) * 2 ^ j = A at h0 ⊢
    obtain ⟨c1, c2, c3, c4⟩ := h0
    exact ⟨by omega, by omega, by omega, by omega⟩
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega

theorem telescope {z : ℂ} (hz : z ∈ boxR R) {N : ℕ} (hg : ∀ j ≥ N, GoodLevel f R j)
    {n : ℕ} (hn : N ≤ n) (i : ℕ) :
    |f (dyadicRoundC (n + i) z) - f (dyadicRoundC n z)| ≤ 16 * θc ^ n * (1 - θc ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hc := consec (f := f) hz (j := n + i) (hg _ (by omega))
    have hθ : 0 ≤ θc ^ n * θc ^ i := mul_nonneg (pow_nonneg θc_pos.le _) (pow_nonneg θc_pos.le _)
    have h18 : 0 ≤ 16 - 18 * θc := by norm_num [θc]
    calc |f (dyadicRoundC (n + (i + 1)) z) - f (dyadicRoundC n z)|
        ≤ |f (dyadicRoundC (n + i + 1) z) - f (dyadicRoundC (n + i) z)| +
          |f (dyadicRoundC (n + i) z) - f (dyadicRoundC n z)| := by
          rw [← add_assoc]; exact abs_sub_le _ _ _
      _ ≤ 2 * θc ^ (n + i + 1) + 16 * θc ^ n * (1 - θc ^ i) := add_le_add hc ih
      _ ≤ 16 * θc ^ n * (1 - θc ^ (i + 1)) := by
          rw [show θc ^ (n + i + 1) = θc ^ n * θc ^ i * θc by ring,
            show θc ^ (i + 1) = θc ^ i * θc by ring]
          nlinarith [mul_nonneg hθ h18]

theorem telescope' {z : ℂ} (hz : z ∈ boxR R) {N : ℕ} (hg : ∀ j ≥ N, GoodLevel f R j)
    {n M : ℕ} (hn : N ≤ n) (hM : n ≤ M) :
    |f (dyadicRoundC M z) - f (dyadicRoundC n z)| ≤ 16 * θc ^ n := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hM
  have h := telescope hz hg hn i
  have : 0 ≤ θc ^ n * θc ^ i := mul_nonneg (pow_nonneg θc_pos.le _) (pow_nonneg θc_pos.le _)
  nlinarith

theorem abs_floor_sub_of_lt {x y : ℝ} {n : ℕ} (h : |x - y| < 1 / 2 ^ n) :
    |⌊(2 : ℝ) ^ n * x⌋ - ⌊(2 : ℝ) ^ n * y⌋| ≤ 1 := by
  apply abs_floor_sub_le_one
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  rw [← mul_sub, abs_mul, abs_of_pos hp]
  calc (2 : ℝ) ^ n * |x - y| < 2 ^ n * (1 / 2 ^ n) := mul_lt_mul_of_pos_left h hp
    _ = 1 := by field_simp

theorem level_mod {z w : ℂ} (hz : z ∈ boxR R) (hw : w ∈ boxR R) {N : ℕ}
    (hg : ∀ j ≥ N, GoodLevel f R j) {n : ℕ} (hn : N ≤ n)
    (hre : |z.re - w.re| < 1 / 2 ^ n) (him : |z.im - w.im| < 1 / 2 ^ n) {M : ℕ}
    (hM : n ≤ M) :
    |f (dyadicRoundC M z) - f (dyadicRoundC M w)| ≤ 34 * θc ^ n := by
  have h1 := telescope' hz hg hn hM
  have h2 := telescope' hw hg hn hM
  have h3 : |f (dyadicRoundC n w) - f (dyadicRoundC n z)| ≤ 2 * θc ^ n := by
    rw [dyadicRoundC_eq_lpt, dyadicRoundC_eq_lpt]
    exact near (hg n hn) (inRange_floor hz n) (inRange_floor hw n)
      (abs_floor_sub_of_lt hre) (abs_floor_sub_of_lt him)
  rw [abs_sub_comm] at h2 h3
  have h4 := abs_add_three (f (dyadicRoundC M z) - f (dyadicRoundC n z))
    (f (dyadicRoundC n z) - f (dyadicRoundC n w)) (f (dyadicRoundC n w) - f (dyadicRoundC M w))
  have e : f (dyadicRoundC M z) - f (dyadicRoundC n z) +
      (f (dyadicRoundC n z) - f (dyadicRoundC n w)) +
      (f (dyadicRoundC n w) - f (dyadicRoundC M w)) =
      f (dyadicRoundC M z) - f (dyadicRoundC M w) := by ring
  rw [e] at h4
  linarith

theorem tendsto_of_good {z : ℂ} (hz : z ∈ boxR R) {N : ℕ} (hg : ∀ j ≥ N, GoodLevel f R j) :
    Tendsto (fun M => f (dyadicRoundC M z)) atTop
      (𝓝 (limUnder atTop fun M => f (dyadicRoundC M z))) := by
  apply CauchySeq.tendsto_limUnder
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨n, hn1, hn2⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one θc_pos.le θc_lt_one).eventually
    (gt_mem_nhds (show 0 < ε / 32 by positivity))).and (eventually_ge_atTop N)).exists
  refine ⟨n, fun M hM => ?_⟩
  rw [Real.dist_eq]
  have := telescope' hz hg hn2 hM
  linarith

theorem exists_boxR {z : ℂ} (hz : z ∈ Hbar) : ∃ R : ℕ, z ∈ boxR R := by
  obtain ⟨R, hR⟩ := exists_nat_ge (max |z.re| z.im)
  exact ⟨R, (le_max_left _ _).trans hR, hz, (le_max_right _ _).trans hR⟩

theorem continuousOn_of_good (hg : ∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodLevel f R j) :
    ContinuousOn (fun z => limUnder atTop fun M => f (dyadicRoundC M z)) Hbar := by
  intro z hz
  obtain ⟨R, hR⟩ := exists_nat_ge (max (|z.re| + 1) (z.im + 1))
  have hR1 : |z.re| + 1 ≤ R := (le_max_left _ _).trans hR
  have hR2 : z.im + 1 ≤ R := (le_max_right _ _).trans hR
  obtain ⟨N, hN⟩ := hg R
  have hzb : z ∈ boxR R := ⟨by linarith, hz, by linarith⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨n, hn1, hn2⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one θc_pos.le θc_lt_one).eventually
    (gt_mem_nhds (show 0 < ε / 34 by positivity))).and (eventually_ge_atTop N)).exists
  refine ⟨min 1 (1 / 2 ^ n), by positivity, fun {w} hw hwz => ?_⟩
  rw [dist_eq_norm] at hwz
  have hre : |w.re - z.re| < 1 / 2 ^ n := lt_of_le_of_lt
    (by simpa using Complex.abs_re_le_norm (w - z)) (lt_of_lt_of_le hwz (min_le_right _ _))
  have him : |w.im - z.im| < 1 / 2 ^ n := lt_of_le_of_lt
    (by simpa using Complex.abs_im_le_norm (w - z)) (lt_of_lt_of_le hwz (min_le_right _ _))
  have hre1 : |w.re - z.re| < 1 := lt_of_le_of_lt
    (by simpa using Complex.abs_re_le_norm (w - z)) (lt_of_lt_of_le hwz (min_le_left _ _))
  have him1 : |w.im - z.im| < 1 := lt_of_le_of_lt
    (by simpa using Complex.abs_im_le_norm (w - z)) (lt_of_lt_of_le hwz (min_le_left _ _))
  have hwb : w ∈ boxR R := by
    refine ⟨?_, hw, ?_⟩
    · have := abs_sub_abs_le_abs_sub w.re z.re; linarith
    · rw [abs_lt] at him1; linarith
  have htz := tendsto_of_good hzb hN
  have htw := tendsto_of_good hwb hN
  have hle : |(limUnder atTop fun M => f (dyadicRoundC M w)) -
      limUnder atTop fun M => f (dyadicRoundC M z)| ≤ 34 * θc ^ n :=
    le_of_tendsto ((htw.sub htz).abs)
      (eventually_atTop.2 ⟨n, fun M hM => level_mod hwb hzb hN hn2 hre him hM⟩)
  rw [Real.dist_eq]
  linarith

/-! ## 2. Probabilistic part: Markov, union bound, Borel–Cantelli -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem meas_gt_le_of_moment {U V : Ω → ℝ} (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    {B t : ℝ} (ht : 0 < t)
    (hmom : ∫⁻ ω, ENNReal.ofReal (|U ω - V ω| ^ 8) ∂P ≤ ENNReal.ofReal B) :
    P {ω | t < |U ω - V ω|} ≤ ENNReal.ofReal (B / t ^ 8) := by
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (|U ω - V ω| ^ 8)) P :=
    ((continuous_abs.measurable.comp_aemeasurable (hU.sub hV)).pow_const 8).ennreal_ofReal
  have hm := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal (t ^ 8))
  have hsub : {ω | t < |U ω - V ω|} ⊆
      {ω | ENNReal.ofReal (t ^ 8) ≤ ENNReal.ofReal (|U ω - V ω| ^ 8)} := fun ω hω =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht.le (le_of_lt hω) 8)
  have hpos : ENNReal.ofReal (t ^ 8) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  calc P {ω | t < |U ω - V ω|}
      ≤ P {ω | ENNReal.ofReal (t ^ 8) ≤ ENNReal.ofReal (|U ω - V ω| ^ 8)} := measure_mono hsub
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal (t ^ 8) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact hm.trans hmom
    _ = ENNReal.ofReal (B / t ^ 8) := (ENNReal.ofReal_div_of_pos (by positivity)).symm

/-- Per-level ratio `(1/2)⁴ / θ⁸`. -/
def r1 : ℝ := (1 / 2) ^ 4 / θc ^ 8

/-- Geometric ratio of the level-`j` failure probabilities. -/
def qc : ℝ := 4 * r1

theorem r1_pos : 0 < r1 := by norm_num [r1, θc]

theorem qc_pos : 0 < qc := by norm_num [qc, r1, θc]

theorem qc_lt_one : qc < 1 := by norm_num [qc, r1, θc]

theorem r1_le_qc : r1 ≤ qc := by norm_num [qc, r1, θc]

theorem pow_ratio_eq (j : ℕ) : (1 / 2 ^ j : ℝ) ^ 4 / (θc ^ j) ^ 8 = r1 ^ j := by
  rw [r1, ← one_div_pow, ← pow_mul, ← pow_mul, mul_comm j 4, mul_comm j 8, pow_mul, pow_mul,
    ← div_pow]

theorem norm_lpt_sub_re (j : ℕ) (a b : ℤ) : ‖lpt j (a + 1) b - lpt j a b‖ = 1 / 2 ^ j := by
  have : lpt j (a + 1) b - lpt j a b = ((1 / 2 ^ j : ℝ) : ℂ) := by
    apply Complex.ext <;> simp only [lpt, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      push_cast <;> ring
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem norm_lpt_sub_im (j : ℕ) (a b : ℤ) : ‖lpt j a (b + 1) - lpt j a b‖ = 1 / 2 ^ j := by
  have : lpt j a (b + 1) - lpt j a b = ((1 / 2 ^ j : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp only [lpt, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
      push_cast <;> ring
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

theorem lpt_mem_Hbar {j : ℕ} {a b : ℤ} (hb : 0 ≤ b) : lpt j a b ∈ Hbar :=
  show 0 ≤ (b : ℝ) / 2 ^ j from div_nonneg (by exact_mod_cast hb) (by positivity)

variable (Z : ℂ → Ω → ℝ)

/-- The eighth-moment Kolmogorov hypothesis on `Hbar`. -/
def MomentBound (P : Measure Ω) (K : ℝ) : Prop :=
  ∀ z ∈ Hbar, ∀ w ∈ Hbar,
    ∫⁻ ω, ENNReal.ofReal (|Z z ω - Z w ω| ^ 8) ∂P ≤ ENNReal.ofReal (K * ‖z - w‖ ^ 4)

/-- The event that level `j` is bad on `boxR R`. -/
def badSet (R j : ℕ) : Set Ω := {ω | ¬ GoodLevel (fun z => Z z ω) R j}

variable {Z}

theorem meas_adjacent_le (hZ : ∀ z, AEMeasurable (Z z) P) {K : ℝ} (hmom : MomentBound Z P K)
    {z w : ℂ} (hz : z ∈ Hbar) (hw : w ∈ Hbar) {j : ℕ} (hzw : ‖z - w‖ = 1 / 2 ^ j) :
    P {ω | θc ^ j < |Z z ω - Z w ω|} ≤ ENNReal.ofReal (K * r1 ^ j) := by
  refine (meas_gt_le_of_moment (hZ z) (hZ w) (pow_pos θc_pos j) (hmom z hz w hw)).trans ?_
  rw [hzw, mul_div_assoc, pow_ratio_eq]

theorem measure_badSet_le (hZ : ∀ z, AEMeasurable (Z z) P) {K : ℝ} (hK : 0 ≤ K)
    (hmom : MomentBound Z P K) (R j : ℕ) :
    P (badSet Z R j) ≤ ENNReal.ofReal (2 * ((2 * R + 1) * (R + 1)) * K * qc ^ j) := by
  set A : ℤ := (R : ℤ) * 2 ^ j with hA
  have hA0 : 0 ≤ A := by positivity
  set S := Finset.Icc (-A) A ×ˢ Finset.Icc 0 A with hS
  set E : ℤ × ℤ → Set Ω := fun p =>
    {ω | θc ^ j < |Z (lpt j (p.1 + 1) p.2) ω - Z (lpt j p.1 p.2) ω|} ∪
      {ω | θc ^ j < |Z (lpt j p.1 (p.2 + 1)) ω - Z (lpt j p.1 p.2) ω|} with hE
  have hsub : badSet Z R j ⊆ ⋃ p ∈ S, E p := by
    intro ω hω
    simp only [badSet, GoodLevel, not_forall, Set.mem_ofPred_eq] at hω
    obtain ⟨a, b, hab, hnot⟩ := hω
    rw [Set.mem_iUnion₂]
    refine ⟨(a, b), Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hab.1, hab.2.1⟩,
      Finset.mem_Icc.2 ⟨hab.2.2.1, hab.2.2.2⟩⟩, ?_⟩
    by_cases h1 : |Z (lpt j (a + 1) b) ω - Z (lpt j a b) ω| ≤ θc ^ j
    · right; exact lt_of_not_ge fun h2 => hnot ⟨h1, h2⟩
    · left; exact lt_of_not_ge h1
  have hE : ∀ p ∈ S, P (E p) ≤ ENNReal.ofReal (2 * (K * r1 ^ j)) := by
    intro p hp
    have hb : 0 ≤ p.2 := (Finset.mem_Icc.1 (Finset.mem_product.1 hp).2).1
    have hb1 : 0 ≤ p.2 + 1 := by omega
    calc P (E p) ≤ P {ω | θc ^ j < |Z (lpt j (p.1 + 1) p.2) ω - Z (lpt j p.1 p.2) ω|} +
          P {ω | θc ^ j < |Z (lpt j p.1 (p.2 + 1)) ω - Z (lpt j p.1 p.2) ω|} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (K * r1 ^ j) + ENNReal.ofReal (K * r1 ^ j) :=
          add_le_add (meas_adjacent_le hZ hmom (lpt_mem_Hbar hb) (lpt_mem_Hbar hb)
            (norm_lpt_sub_re j p.1 p.2))
            (meas_adjacent_le hZ hmom (lpt_mem_Hbar hb1) (lpt_mem_Hbar hb)
              (norm_lpt_sub_im j p.1 p.2))
      _ = ENNReal.ofReal (2 * (K * r1 ^ j)) := by
          rw [two_mul, ENNReal.ofReal_add (mul_nonneg hK (pow_nonneg r1_pos.le _))
            (mul_nonneg hK (pow_nonneg r1_pos.le _))]
  have hcard : (S.card : ℝ) = (2 * R * 2 ^ j + 1) * (R * 2 ^ j + 1) := by
    rw [hS, Finset.card_product, Int.card_Icc, Int.card_Icc, Nat.cast_mul]
    have h1 : (0 : ℤ) ≤ A + 1 - -A := by omega
    have h2 : (0 : ℤ) ≤ A + 1 - 0 := by omega
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h1, ← Int.cast_natCast (A + 1 - 0).toNat,
      Int.toNat_of_nonneg h2, hA]
    push_cast; ring
  calc P (badSet Z R j) ≤ P (⋃ p ∈ S, E p) := measure_mono hsub
    _ ≤ ∑ p ∈ S, P (E p) := measure_biUnion_finset_le _ _
    _ ≤ ∑ p ∈ S, ENNReal.ofReal (2 * (K * r1 ^ j)) := Finset.sum_le_sum hE
    _ = ENNReal.ofReal ((S.card : ℝ) * (2 * (K * r1 ^ j))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 * ((2 * R + 1) * (R + 1)) * K * qc ^ j) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hcard]
        have ht : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        have h4 : qc ^ j = ((2 : ℝ) ^ j) ^ 2 * r1 ^ j := by
          rw [qc, mul_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
        rw [h4]
        have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
        have hx : (2 * (R : ℝ) * 2 ^ j + 1) * ((R : ℝ) * 2 ^ j + 1) ≤
            ((2 * (R : ℝ) + 1) * ((R : ℝ) + 1)) * ((2 : ℝ) ^ j) ^ 2 := by
          have e1 : (2 * (R : ℝ) * 2 ^ j + 1 : ℝ) ≤ (2 * (R : ℝ) + 1) * 2 ^ j := by nlinarith
          have e2 : ((R : ℝ) * 2 ^ j + 1 : ℝ) ≤ ((R : ℝ) + 1) * 2 ^ j := by nlinarith
          calc (2 * (R : ℝ) * 2 ^ j + 1) * ((R : ℝ) * 2 ^ j + 1)
              ≤ ((2 * (R : ℝ) + 1) * 2 ^ j) * (((R : ℝ) + 1) * 2 ^ j) :=
                mul_le_mul e1 e2 (by positivity) (by positivity)
            _ = ((2 * (R : ℝ) + 1) * ((R : ℝ) + 1)) * ((2 : ℝ) ^ j) ^ 2 := by ring
        have hKr : 0 ≤ 2 * (K * r1 ^ j) := by
          have := pow_nonneg r1_pos.le j; positivity
        calc (2 * (R : ℝ) * 2 ^ j + 1) * ((R : ℝ) * 2 ^ j + 1) * (2 * (K * r1 ^ j))
            ≤ ((2 * (R : ℝ) + 1) * ((R : ℝ) + 1)) * ((2 : ℝ) ^ j) ^ 2 * (2 * (K * r1 ^ j)) :=
              mul_le_mul_of_nonneg_right hx hKr
          _ = 2 * ((2 * R + 1) * (R + 1)) * K * (((2 : ℝ) ^ j) ^ 2 * r1 ^ j) := by ring

theorem tsum_geom_ne_top {c : ℝ} (hc : 0 ≤ c) {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) :
    ∑' j : ℕ, ENNReal.ofReal (c * q ^ j) ≠ ∞ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg hc (pow_nonneg hq0 j))
    ((summable_geometric_of_lt_one hq0 hq).mul_left c)]
  exact ENNReal.ofReal_ne_top

theorem ae_good (hZ : ∀ z, AEMeasurable (Z z) P) {K : ℝ} (hK : 0 ≤ K)
    (hmom : MomentBound Z P K) :
    ∀ᵐ ω ∂P, ∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodLevel (fun z => Z z ω) R j := by
  rw [ae_all_iff]
  intro R
  have hsum : ∑' j, P (badSet Z R j) ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_geom_ne_top (by positivity) qc_pos.le qc_lt_one)
      (ENNReal.tsum_le_tsum fun j => measure_badSet_le hZ hK hmom R j)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  exact ⟨N, fun j hj => not_not.1 (hN j hj)⟩

theorem abs_dyadicRound_sub_le (n : ℕ) (x : ℝ) : |dyadicRound n x - x| ≤ 1 / 2 ^ n := by
  unfold dyadicRound
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have h1 := Int.floor_le ((2 : ℝ) ^ n * x)
  have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ n * x)
  rw [abs_sub_comm, abs_of_nonneg]
  · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hp]; linarith
  · rw [sub_nonneg, div_le_iff₀ hp]; linarith

theorem dyadicRoundC_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) (n : ℕ) : dyadicRoundC n z ∈ Hbar := by
  rw [dyadicRoundC_eq_lpt]
  exact lpt_mem_Hbar (Int.floor_nonneg.2 (mul_nonneg (by positivity) hz))

theorem norm_dyadicRoundC_sub_le (n : ℕ) (z : ℂ) : ‖dyadicRoundC n z - z‖ ≤ 2 * (1 / 2 ^ n) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h1 := abs_dyadicRound_sub_le n z.re
  have h2 := abs_dyadicRound_sub_le n z.im
  simp only [Complex.sub_re, Complex.sub_im]
  exact (add_le_add h1 h2).trans (le_of_eq (by ring))

theorem ae_tendsto_at (hZ : ∀ z, AEMeasurable (Z z) P) {K : ℝ} (hK : 0 ≤ K)
    (hmom : MomentBound Z P K) {z : ℂ} (hz : z ∈ Hbar) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Z (dyadicRoundC n z) ω) atTop (𝓝 (Z z ω)) := by
  have hev : ∀ n : ℕ, P {ω | θc ^ n < |Z (dyadicRoundC n z) ω - Z z ω|} ≤
      ENNReal.ofReal ((16 * K) * r1 ^ n) := by
    intro n
    have hn : ‖dyadicRoundC n z - z‖ ^ 4 ≤ (2 * (1 / 2 ^ n)) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_dyadicRoundC_sub_le n z) 4
    have hm : ∫⁻ ω, ENNReal.ofReal (|Z (dyadicRoundC n z) ω - Z z ω| ^ 8) ∂P ≤
        ENNReal.ofReal (K * (2 * (1 / 2 ^ n)) ^ 4) :=
      (hmom _ (dyadicRoundC_mem_Hbar hz n) z hz).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hn hK))
    refine (meas_gt_le_of_moment (hZ _) (hZ z) (pow_pos θc_pos n) hm).trans
      (le_of_eq (congrArg ENNReal.ofReal ?_))
    rw [← pow_ratio_eq]; ring
  have hsum : ∑' n, P {ω | θc ^ n < |Z (dyadicRoundC n z) ω - Z z ω|} ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_geom_ne_top (by positivity) r1_pos.le
      (r1_le_qc.trans_lt qc_lt_one)) (ENNReal.tsum_le_tsum hev)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one θc_pos.le θc_lt_one)
  filter_upwards [hω] with n hn
  simpa [Real.norm_eq_abs] using hn

/-- **Kolmogorov continuity on `Hbar` (dyadic version).** A real process on `ℂ` whose
increments on `Hbar` satisfy `E|Z z − Z w|⁸ ≤ K ‖z − w‖⁴` has a modification that is
continuous on `Hbar` for every `ω`, and almost surely the values along the dyadic
roundings `dyadicRoundC n z` converge to it at every point of `Hbar`. -/
theorem exists_continuous_modification (hZ : ∀ z, AEMeasurable (Z z) P) {K : ℝ} (hK : 0 ≤ K)
    (hmom : MomentBound Z P K) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, ContinuousOn (fun z => Y z ω) Hbar) ∧
      (∀ z ∈ Hbar, (fun ω => Y z ω) =ᵐ[P] Z z) ∧
      (∀ᵐ ω ∂P, ∀ z ∈ Hbar,
        Tendsto (fun n => Z (dyadicRoundC n z) ω) atTop (𝓝 (Y z ω))) := by
  classical
  refine ⟨fun z ω => if (∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodLevel (fun z => Z z ω) R j) then
    limUnder atTop (fun n => Z (dyadicRoundC n z) ω) else 0, ?_, ?_, ?_⟩
  · intro ω
    by_cases h : ∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodLevel (fun z => Z z ω) R j
    · simp only [if_pos h]; exact continuousOn_of_good h
    · simp only [if_neg h]; exact continuousOn_const
  · intro z hz
    filter_upwards [ae_good hZ hK hmom, ae_tendsto_at hZ hK hmom hz] with ω hG ht
    simp only [if_pos hG]
    exact ht.limUnder_eq
  · filter_upwards [ae_good hZ hK hmom] with ω hG z hz
    simp only [if_pos hG]
    obtain ⟨R, hR⟩ := exists_boxR hz
    obtain ⟨N, hN⟩ := hG R
    exact tendsto_of_good (f := fun z => Z z ω) hR hN

/-! ## 3. Eighth moments of centered real Gaussians -/

theorem integrable_abs_pow8_gaussianReal (v : NNReal) :
    Integrable (fun x : ℝ => |x| ^ 8) (gaussianReal 0 v) := by
  have hmem : MemLp (fun x : ℝ => x) ((8 : ℕ) : NNReal) (gaussianReal 0 v) :=
    memLp_id_gaussianReal 8
  have hint : Integrable (fun x : ℝ => ‖x‖ ^ 8) (gaussianReal 0 v) := hmem.integrable_norm_pow'
  simpa [Real.norm_eq_abs] using hint

theorem integral_abs_pow8_gaussianReal (v : NNReal) :
    ∫ x, |x| ^ 8 ∂(gaussianReal 0 v) = (v : ℝ) ^ 4 * gaussianAbsMoment 8 := by
  have hv0 : (0 : ℝ) ≤ v := v.coe_nonneg
  have hcsq : Real.sqrt (v : ℝ) ^ 2 = v := Real.sq_sqrt hv0
  have hmap : gaussianReal (0 : ℝ) v =
      (gaussianReal (0 : ℝ) 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      push_cast
      rw [hcsq]
      ring
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ x : ℝ, |Real.sqrt v * x| ^ 8 = (v : ℝ) ^ 4 * |x| ^ 8 := by
    intro x
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      show Real.sqrt (v : ℝ) ^ 8 = (Real.sqrt (v : ℝ) ^ 2) ^ 4 by ring, hcsq]
  simp_rw [hpt]
  rw [integral_const_mul]
  rfl

theorem lintegral_pow8_of_map_eq {U : Ω → ℝ} (hU : Measurable U) {v : NNReal}
    (hlaw : P.map U = gaussianReal 0 v) :
    ∫⁻ ω, ENNReal.ofReal (|U ω| ^ 8) ∂P =
      ENNReal.ofReal ((v : ℝ) ^ 4 * gaussianAbsMoment 8) := by
  have hi := integrable_abs_pow8_gaussianReal v
  rw [← hlaw] at hi
  rw [← integral_abs_pow8_gaussianReal, ← hlaw,
    ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity)]
  exact (lintegral_map (f := fun x : ℝ => ENNReal.ofReal (|x| ^ 8))
    (Measurable.ennreal_ofReal (by fun_prop)) hU).symm

/-! ## 4. Circle averages of the free GFF -/

/-- The circle potential `x ↦ ∫ neumannH x y d(foldedCircle a r)(y)`, in closed form. -/
def circPot (r : ℝ) (a x : ℂ) : ℝ :=
  -Real.log (max r ‖a - x‖) - Real.log (max r ‖a - (starRingEnd ℂ) x‖)

theorem integral_neumannH_foldedCircle_right (a x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ y, neumannH x y ∂(foldedCircle a r) = circPot r a x := by
  simp_rw [neumannH_symm x]
  exact integral_neumannH_foldedCircle a x hr

theorem continuous_circPot {r : ℝ} (hr : 0 < r) (a : ℂ) : Continuous (circPot r a) := by
  unfold circPot
  refine ((continuous_const.max ?_).log fun x => (lt_of_lt_of_le hr (le_max_left _ _)).ne').neg.sub
    ((continuous_const.max ?_).log fun x => (lt_of_lt_of_le hr (le_max_left _ _)).ne')
  · exact (continuous_const.sub continuous_id).norm
  · exact (continuous_const.sub Complex.continuous_conj).norm

theorem integrable_circPot {r : ℝ} (hr : 0 < r) (a : ℂ) {b : ℂ} (hb : b ∈ Hbar) :
    Integrable (circPot r a) (foldedCircle b r) := by
  obtain ⟨-, ⟨K, hK, -, hK0⟩, -⟩ := isAdmissibleH_foldedCircle hb hr
  have h := (continuous_circPot hr a).continuousOn.integrableOn_compact
    (μ := foldedCircle b r) hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hK0)] at h

theorem abs_circPot_sub_le {r : ℝ} (hr : 0 < r) (z w x : ℂ) :
    |circPot r z x - circPot r w x| ≤ 2 * ‖z - w‖ / r := by
  have h := abs_integral_neumannH_foldedCircle_sub_le z w x hr
  rw [integral_neumannH_foldedCircle z x hr, integral_neumannH_foldedCircle w x hr] at h
  exact h

/-- **Increment variance bound**: `E|h_r(z) − h_r(w)|² ≤ (4/r) ‖z − w‖` for folded-circle
averages at radius `r`. -/
theorem kernelCov2_foldedCircle_le {r : ℝ} (hr : 0 < r) {z w : ℂ} (hz : z ∈ Hbar)
    (hw : w ∈ Hbar) :
    kernelCov2 neumannH (foldedCircle z r, foldedCircle w r)
      (foldedCircle z r, foldedCircle w r) ≤ 4 * ‖z - w‖ / r := by
  have hkc : ∀ (μ : Measure ℂ) (a : ℂ),
      kernelCov neumannH μ (foldedCircle a r) = ∫ x, circPot r a x ∂μ := by
    intro μ a
    unfold kernelCov
    simp_rw [integral_neumannH_foldedCircle_right a _ hr]
  simp only [kernelCov2, hkc]
  have hb : ∀ b ∈ Hbar, |∫ x, circPot r z x ∂(foldedCircle b r) -
      ∫ x, circPot r w x ∂(foldedCircle b r)| ≤ 2 * ‖z - w‖ / r := by
    intro b hb
    rw [← integral_sub (integrable_circPot hr z hb) (integrable_circPot hr w hb)]
    have := norm_integral_le_of_norm_le_const (μ := foldedCircle b r)
      (f := fun x => circPot r z x - circPot r w x) (C := 2 * ‖z - w‖ / r)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_circPot_sub_le hr z w x)
    simpa [Real.norm_eq_abs] using this
  have h1 := hb z hz
  have h2 := hb w hw
  rw [abs_le] at h1 h2
  have e : 4 * ‖z - w‖ / r = 2 * ‖z - w‖ / r + 2 * ‖z - w‖ / r := by ring
  rw [e]
  linarith [h1.2, h2.1]

variable {X : Ω → FieldSample}

/-- The increment of folded-circle averages is a centered Gaussian with variance
`kernelCov2 neumannH`. -/
theorem map_circleDiff_eq_gaussianReal (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r)
    {z w : ℂ} (hz : z ∈ Hbar) (hw : w ∈ Hbar) :
    P.map (fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r)) =
      gaussianReal 0 (kernelCov2 neumannH (foldedCircle z r, foldedCircle w r)
        (foldedCircle z r, foldedCircle w r)).toNNReal := by
  have hadz := isAdmissibleH_foldedCircle hz hr
  have hadw := isAdmissibleH_foldedCircle hw hr
  have hmass : (foldedCircle z r) Set.univ = (foldedCircle w r) Set.univ := by
    simp [measure_univ]
  have hG : HasGaussianLaw (fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r)) P :=
    hX.gaussian.hasGaussianLaw_eval ⟨(foldedCircle z r, foldedCircle w r), hadz, hadw, hmass⟩
  have hm : AEMeasurable (fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r)) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hc : P[fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r)] = 0 :=
    hX.centered _ _ hadz hadw hmass
  have hcov : cov[fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r),
      fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r); P] =
      kernelCov2 neumannH (foldedCircle z r, foldedCircle w r)
        (foldedCircle z r, foldedCircle w r) :=
    hX.covariance_eq (foldedCircle z r, foldedCircle w r) (foldedCircle z r, foldedCircle w r)
      hadz hadw hmass hadz hadw hmass
  rw [hG.map_eq_gaussianReal, hc, ← covariance_self hm, hcov]

/-- **Eighth-moment Kolmogorov bound** for folded-circle averages at radius `r`. -/
theorem momentBound_circleDiff (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r) (z₀ : ℂ) :
    MomentBound (fun z ω => X ω (foldedCircle z r) - X ω (foldedCircle z₀ r)) P
      ((4 / r) ^ 4 * gaussianAbsMoment 8) := by
  intro z hz w hw
  have e : ∀ ω, X ω (foldedCircle z r) - X ω (foldedCircle z₀ r) -
      (X ω (foldedCircle w r) - X ω (foldedCircle z₀ r)) =
      X ω (foldedCircle z r) - X ω (foldedCircle w r) := fun ω => by ring
  simp only [e]
  rw [lintegral_pow8_of_map_eq (U := fun ω => X ω (foldedCircle z r) - X ω (foldedCircle w r))
    ((hX.measurable_coord _).sub (hX.measurable_coord _))
    (map_circleDiff_eq_gaussianReal hX hr hz hw)]
  apply ENNReal.ofReal_le_ofReal
  have hkb := kernelCov2_foldedCircle_le hr hz hw
  rw [mul_div_right_comm] at hkb
  have hnn : 0 ≤ 4 / r * ‖z - w‖ := mul_nonneg (div_nonneg (by norm_num) hr.le) (norm_nonneg _)
  have hv : ((kernelCov2 neumannH (foldedCircle z r, foldedCircle w r)
      (foldedCircle z r, foldedCircle w r)).toNNReal : ℝ) ≤ 4 / r * ‖z - w‖ := by
    rw [Real.coe_toNNReal']; exact max_le hkb hnn
  have h4 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 4
  calc _ ≤ (4 / r * ‖z - w‖) ^ 4 * gaussianAbsMoment 8 :=
        mul_le_mul_of_nonneg_right h4 (gaussianAbsMoment_nonneg 8)
    _ = (4 / r) ^ 4 * gaussianAbsMoment 8 * ‖z - w‖ ^ 4 := by ring

/-- **Kolmogorov continuity of circle averages of the free GFF.** At radius `radius k`, the
increments `z ↦ X(foldedCircle z) − X(foldedCircle z₀)` have a modification `Y` continuous on
`Hbar` for every `ω`, and almost surely the regularized circle average `avgReg` equals
`Y z + X(foldedCircle z₀)` at every point of `Hbar`. -/
theorem _root_.QuantumZipper.exists_continuous_circleAvg (hX : IsFreeGFFModConstH X P) (k : ℕ) (z₀ : ℂ)
    (hz₀ : z₀ ∈ Hbar) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, ContinuousOn (fun z => Y z ω) Hbar) ∧
      (∀ z ∈ Hbar, (fun ω => Y z ω) =ᵐ[P]
        fun ω => X ω (foldedCircle z (radius k)) - X ω (foldedCircle z₀ (radius k))) ∧
      (∀ᵐ ω ∂P, ∀ z ∈ Hbar,
        avgReg (X ω) k z = Y z ω + X ω (foldedCircle z₀ (radius k))) := by
  have hr := radius_pos k
  obtain ⟨Y, hc, hae, hlim⟩ := exists_continuous_modification
    (Z := fun z ω => X ω (foldedCircle z (radius k)) - X ω (foldedCircle z₀ (radius k)))
    (fun z => ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable)
    (mul_nonneg (pow_nonneg (div_nonneg (by norm_num) hr.le) 4) (gaussianAbsMoment_nonneg 8))
    (momentBound_circleDiff hX hr z₀)
  refine ⟨Y, hc, hae, ?_⟩
  filter_upwards [hlim] with ω hω z hz
  have ht := (hω z hz).add_const (X ω (foldedCircle z₀ (radius k)))
  simp only [sub_add_cancel] at ht
  unfold avgReg
  exact ht.limUnder_eq

end CircleCont
end QuantumZipper
