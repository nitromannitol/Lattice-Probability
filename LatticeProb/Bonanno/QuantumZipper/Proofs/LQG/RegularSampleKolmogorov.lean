/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.RegularSampleKolmogorov at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity

/-!
# Dyadic Kolmogorov continuity in `d ≤ 4` real parameters (helper for M4-R3)

The `d`-dimensional version of `CircleCont.exists_continuous_modification`: a real process
`Z` indexed by `Fin d → ℝ` (sup norm) whose increments satisfy, on every box `[-R,R]^d`,
`E|Z q − Z q'|¹⁶ ≤ K_R ‖q − q'‖⁸`, has a modification that is continuous for every `ω`;
almost surely, along the coordinatewise dyadic floor roundings `rndD n q`, the values of `Z`
converge to it at **every** `q`.

Chaining: level `j` is good on the box `R` when all increments of `Z` between lattice points
of mesh `2^{-j}` that differ by one step in one coordinate are `≤ θ^j`, `θ = 7/8`. A bad level
has probability `≤ C_R q^j` with `q = 2⁴ (1/2)⁸ / θ¹⁶ < 1`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace QuantumZipper
namespace KolmD

open CircleCont (θc θc_pos θc_lt_one floor_succ_bounds abs_floor_sub_le_one
  abs_floor_sub_of_lt meas_gt_le_of_moment tsum_geom_ne_top)

variable {d : ℕ}

/-! ## 1. Lattices and deterministic chaining -/

/-- Level-`j` lattice point with integer coordinates `a`. -/
def lptD (j : ℕ) (a : Fin d → ℤ) : Fin d → ℝ := fun i => (a i : ℝ) / 2 ^ j

/-- Coordinatewise floor at level `j`. -/
def flr (j : ℕ) (q : Fin d → ℝ) : Fin d → ℤ := fun i => ⌊(2 : ℝ) ^ j * q i⌋

/-- Coordinatewise dyadic floor rounding. -/
def rndD (j : ℕ) (q : Fin d → ℝ) : Fin d → ℝ := lptD j (flr j q)

/-- The box `[-R, R]^d`. -/
def boxD (R : ℕ) : Set (Fin d → ℝ) := {q | ∀ i, |q i| ≤ R}

/-- Lattice indices of level `j` in the box `R`. -/
def InRangeD (R j : ℕ) (a : Fin d → ℤ) : Prop := ∀ i, |a i| ≤ (R : ℤ) * 2 ^ j

/-- All one-step increments at level `j` based in the box `R` are at most `θ^j`. -/
def GoodD (f : (Fin d → ℝ) → ℝ) (R j : ℕ) : Prop :=
  ∀ a, InRangeD R j a → ∀ i, |f (lptD j (a + Pi.single i 1)) - f (lptD j a)| ≤ θc ^ j

variable {f : (Fin d → ℝ) → ℝ} {R : ℕ}

theorem near_D {j : ℕ} (hg : GoodD f R j) {a a' : Fin d → ℤ} (ha : InRangeD R j a)
    (ha' : InRangeD R j a') (h1 : ∀ i, |a i - a' i| ≤ 1) :
    |f (lptD j a') - f (lptD j a)| ≤ d * θc ^ j := by
  set b : ℕ → Fin d → ℤ := fun m i => if (i : ℕ) < m then a' i else a i with hb
  have hb0 : b 0 = a := by funext i; simp [hb]
  have hbd : b d = a' := by funext i; simp [hb, i.isLt]
  have hbR : ∀ m, InRangeD R j (b m) := fun m i => by
    simp only [hb]; split_ifs
    · exact ha' i
    · exact ha i
  have hθ : 0 ≤ θc ^ j := pow_nonneg θc_pos.le j
  have step : ∀ m (hm : m < d), |f (lptD j (b (m + 1))) - f (lptD j (b m))| ≤ θc ^ j := by
    intro m hm
    set i₀ : Fin d := ⟨m, hm⟩
    have key : ∀ i : Fin d, b (m + 1) i = b m i + (if (i : ℕ) = m then a' i - a i else 0) := by
      intro i; simp only [hb]; split_ifs <;> omega
    have hbi : ∀ c : ℤ, a' i₀ - a i₀ = c → b (m + 1) = b m + c • Pi.single i₀ 1 := by
      intro c hc
      funext i
      rw [key]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases hi : (i : ℕ) = m
      · have : i = i₀ := Fin.ext hi
        subst this; rw [if_pos hi, if_pos rfl, hc, mul_one]
      · have : i ≠ i₀ := fun h => hi (by rw [h])
        simp [hi, this]
    have hc := h1 i₀
    rw [abs_le] at hc
    rcases (show a' i₀ - a i₀ = 1 ∨ a' i₀ - a i₀ = 0 ∨ a' i₀ - a i₀ = -1 by omega) with
      h | h | h
    · rw [hbi 1 h, one_smul]; exact hg _ (hbR m) i₀
    · rw [hbi 0 h, zero_smul, add_zero, sub_self, abs_zero]; exact hθ
    · have e : b m = b (m + 1) + (1 : ℤ) • Pi.single i₀ 1 := by
        rw [hbi (-1) h, add_assoc, ← add_smul]; simp
      rw [e, one_smul, abs_sub_comm]; exact hg _ (hbR _) i₀
  have ind : ∀ m ≤ d, |f (lptD j (b m)) - f (lptD j a)| ≤ m * θc ^ j := by
    intro m
    induction m with
    | zero => intro _; simp [hb0]
    | succ m ih =>
      intro hm
      calc |f (lptD j (b (m + 1))) - f (lptD j a)|
          ≤ |f (lptD j (b (m + 1))) - f (lptD j (b m))| + |f (lptD j (b m)) - f (lptD j a)| :=
            abs_sub_le _ _ _
        _ ≤ θc ^ j + m * θc ^ j := add_le_add (step m (by omega)) (ih (by omega))
        _ = ((m + 1 : ℕ) : ℝ) * θc ^ j := by push_cast; ring
  simpa [hbd] using ind d le_rfl

theorem inRange_flr {q : Fin d → ℝ} (hq : q ∈ boxD R) (j : ℕ) : InRangeD R j (flr j q) := by
  intro i
  have h := abs_le.1 (hq i)
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  rw [abs_le]
  refine ⟨Int.le_floor.2 ?_, ?_⟩
  · push_cast; nlinarith
  · have : ⌊(2 : ℝ) ^ j * q i⌋ ≤ ⌊(((R : ℤ) * 2 ^ j : ℤ) : ℝ)⌋ :=
      Int.floor_mono (by push_cast; nlinarith)
    rwa [Int.floor_intCast] at this

theorem lptD_succ (j : ℕ) (a : Fin d → ℤ) :
    lptD j a = lptD (j + 1) (fun i => 2 * a i) := by
  funext i
  simp only [lptD]
  push_cast
  rw [pow_succ, mul_comm ((2 : ℝ) ^ j) 2, mul_div_mul_left _ _ two_ne_zero]

theorem consec_D {q : Fin d → ℝ} (hq : q ∈ boxD R) {j : ℕ} (hg : GoodD f R (j + 1)) :
    |f (rndD (j + 1) q) - f (rndD j q)| ≤ d * θc ^ (j + 1) := by
  unfold rndD
  rw [lptD_succ j]
  refine near_D hg ?_ (inRange_flr hq (j + 1)) ?_
  · intro i
    show |2 * flr j q i| ≤ _
    have h0 := inRange_flr hq j i
    have e : ((R : ℤ) * 2 ^ (j + 1)) = 2 * ((R : ℤ) * 2 ^ j) := by ring
    rw [e]
    rw [abs_le] at h0 ⊢
    constructor <;> omega
  · intro i
    obtain ⟨a1, a2⟩ := floor_succ_bounds j (q i)
    simp only [flr]
    rw [abs_le]; constructor <;> omega

theorem telescope_D {q : Fin d → ℝ} (hq : q ∈ boxD R) {N : ℕ} (hg : ∀ j ≥ N, GoodD f R j)
    {n : ℕ} (hn : N ≤ n) (i : ℕ) :
    |f (rndD (n + i) q) - f (rndD n q)| ≤ 8 * d * θc ^ n * (1 - θc ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hc := consec_D (f := f) hq (j := n + i) (hg _ (by omega))
    have hθ : 0 ≤ θc ^ n * θc ^ i := mul_nonneg (pow_nonneg θc_pos.le _) (pow_nonneg θc_pos.le _)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h8 : 0 ≤ 8 - 9 * θc := by norm_num [CircleCont.θc]
    calc |f (rndD (n + (i + 1)) q) - f (rndD n q)|
        ≤ |f (rndD (n + i + 1) q) - f (rndD (n + i) q)| +
          |f (rndD (n + i) q) - f (rndD n q)| := by
          rw [← add_assoc]; exact abs_sub_le _ _ _
      _ ≤ d * θc ^ (n + i + 1) + 8 * d * θc ^ n * (1 - θc ^ i) := add_le_add hc ih
      _ ≤ 8 * d * θc ^ n * (1 - θc ^ (i + 1)) := by
          rw [show θc ^ (n + i + 1) = θc ^ n * θc ^ i * θc by ring,
            show θc ^ (i + 1) = θc ^ i * θc by ring]
          nlinarith [mul_nonneg (mul_nonneg hθ h8) hd0]

theorem telescope_D' {q : Fin d → ℝ} (hq : q ∈ boxD R) {N : ℕ} (hg : ∀ j ≥ N, GoodD f R j)
    {n M : ℕ} (hn : N ≤ n) (hM : n ≤ M) :
    |f (rndD M q) - f (rndD n q)| ≤ 8 * d * θc ^ n := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hM
  have h := telescope_D hq hg hn i
  have : 0 ≤ θc ^ n * θc ^ i := mul_nonneg (pow_nonneg θc_pos.le _) (pow_nonneg θc_pos.le _)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_nonneg this hd0]

theorem level_mod_D {q q' : Fin d → ℝ} (hq : q ∈ boxD R) (hq' : q' ∈ boxD R) {N : ℕ}
    (hg : ∀ j ≥ N, GoodD f R j) {n : ℕ} (hn : N ≤ n)
    (hqq : ∀ i, |q i - q' i| < 1 / 2 ^ n) {M : ℕ} (hM : n ≤ M) :
    |f (rndD M q) - f (rndD M q')| ≤ 17 * d * θc ^ n := by
  have h1 := telescope_D' hq hg hn hM
  have h2 := telescope_D' hq' hg hn hM
  have h3 : |f (rndD n q') - f (rndD n q)| ≤ d * θc ^ n :=
    near_D (hg n hn) (inRange_flr hq n) (inRange_flr hq' n) fun i => abs_floor_sub_of_lt (hqq i)
  rw [abs_sub_comm] at h2 h3
  have h4 := abs_add_three (f (rndD M q) - f (rndD n q))
    (f (rndD n q) - f (rndD n q')) (f (rndD n q') - f (rndD M q'))
  have e : f (rndD M q) - f (rndD n q) + (f (rndD n q) - f (rndD n q')) +
      (f (rndD n q') - f (rndD M q')) = f (rndD M q) - f (rndD M q') := by ring
  rw [e] at h4
  linarith

theorem tendsto_of_good_D {q : Fin d → ℝ} (hq : q ∈ boxD R) {N : ℕ}
    (hg : ∀ j ≥ N, GoodD f R j) :
    Tendsto (fun M => f (rndD M q)) atTop (𝓝 (limUnder atTop fun M => f (rndD M q))) := by
  apply CauchySeq.tendsto_limUnder
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨n, hn1, hn2⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one θc_pos.le θc_lt_one).eventually
    (gt_mem_nhds (show 0 < ε / (8 * d + 1) by positivity))).and (eventually_ge_atTop N)).exists
  refine ⟨n, fun M hM => ?_⟩
  rw [Real.dist_eq]
  have := telescope_D' hq hg hn2 hM
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : 8 * d * θc ^ n < ε := by
    rw [lt_div_iff₀ (by positivity)] at hn1
    nlinarith [pow_nonneg θc_pos.le n]
  linarith

theorem mem_boxD_of_norm {q : Fin d → ℝ} (h : ‖q‖ ≤ R) : q ∈ boxD R := fun i =>
  (norm_le_pi_norm q i).trans h

theorem continuous_of_good_D (hg : ∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodD f R j) :
    Continuous (fun q => limUnder atTop fun M => f (rndD M q)) := by
  rw [Metric.continuous_iff]
  intro q ε hε
  obtain ⟨R, hR⟩ := exists_nat_ge (‖q‖ + 1)
  obtain ⟨N, hN⟩ := hg R
  obtain ⟨n, hn1, hn2⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one θc_pos.le θc_lt_one).eventually
    (gt_mem_nhds (show 0 < ε / (17 * d + 1) by positivity))).and (eventually_ge_atTop N)).exists
  refine ⟨min 1 (1 / 2 ^ n), by positivity, fun {q'} hq' => ?_⟩
  rw [dist_eq_norm] at hq'
  have hqb : q ∈ boxD R := mem_boxD_of_norm (by linarith)
  have hq'b : q' ∈ boxD R := mem_boxD_of_norm (by
    have := norm_le_insert' q' q
    have h1 : ‖q' - q‖ < 1 := lt_of_lt_of_le hq' (min_le_left _ _)
    linarith [norm_sub_norm_le q' q])
  have hi : ∀ i, |q' i - q i| < 1 / 2 ^ n := fun i =>
    lt_of_le_of_lt (by simpa using norm_le_pi_norm (q' - q) i)
      (lt_of_lt_of_le hq' (min_le_right _ _))
  have hle : |(limUnder atTop fun M => f (rndD M q')) -
      limUnder atTop fun M => f (rndD M q)| ≤ 17 * d * θc ^ n :=
    le_of_tendsto (((tendsto_of_good_D hq'b hN).sub (tendsto_of_good_D hqb hN)).abs)
      (eventually_atTop.2 ⟨n, fun M hM => level_mod_D hq'b hqb hN hn2 hi hM⟩)
  rw [Real.dist_eq]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : 17 * d * θc ^ n < ε := by
    rw [lt_div_iff₀ (by positivity)] at hn1
    nlinarith [pow_nonneg θc_pos.le n]
  linarith

/-! ## 2. Probabilistic part -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem meas_gt_le_of_moment16 {U V : Ω → ℝ} (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    {B t : ℝ} (ht : 0 < t)
    (hmom : ∫⁻ ω, ENNReal.ofReal (|U ω - V ω| ^ 16) ∂P ≤ ENNReal.ofReal B) :
    P {ω | t < |U ω - V ω|} ≤ ENNReal.ofReal (B / t ^ 16) := by
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (|U ω - V ω| ^ 16)) P :=
    ((continuous_abs.measurable.comp_aemeasurable (hU.sub hV)).pow_const 16).ennreal_ofReal
  have hm := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal (t ^ 16))
  have hsub : {ω | t < |U ω - V ω|} ⊆
      {ω | ENNReal.ofReal (t ^ 16) ≤ ENNReal.ofReal (|U ω - V ω| ^ 16)} := fun ω hω =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht.le (le_of_lt hω) 16)
  have hpos : ENNReal.ofReal (t ^ 16) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  calc P {ω | t < |U ω - V ω|}
      ≤ P {ω | ENNReal.ofReal (t ^ 16) ≤ ENNReal.ofReal (|U ω - V ω| ^ 16)} := measure_mono hsub
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal (t ^ 16) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact hm.trans hmom
    _ = ENNReal.ofReal (B / t ^ 16) := (ENNReal.ofReal_div_of_pos (by positivity)).symm

/-- Per-level ratio `(1/2)⁸ / θ¹⁶`. -/
def r16 : ℝ := (1 / 2) ^ 8 / θc ^ 16

/-- Geometric ratio of the failure probabilities in dimension `≤ 4`. -/
def q16 : ℝ := 16 * r16

theorem r16_pos : 0 < r16 := by norm_num [r16, CircleCont.θc]

theorem q16_lt_one : q16 < 1 := by norm_num [q16, r16, CircleCont.θc]

theorem r16_le_q16 : r16 ≤ q16 := by norm_num [q16, r16, CircleCont.θc]

theorem pow_ratio16 (j : ℕ) : (1 / 2 ^ j : ℝ) ^ 8 / (θc ^ j) ^ 16 = r16 ^ j := by
  rw [r16, ← one_div_pow, ← pow_mul, ← pow_mul, mul_comm j 8, mul_comm j 16, pow_mul, pow_mul,
    ← div_pow]

variable (Z : (Fin d → ℝ) → Ω → ℝ)

/-- The sixteenth-moment Kolmogorov hypothesis on the box `R`. -/
def MomentBoundD (P : Measure Ω) (K : ℝ) (R : ℕ) : Prop :=
  ∀ q ∈ boxD (d := d) R, ∀ q' ∈ boxD R,
    ∫⁻ ω, ENNReal.ofReal (|Z q ω - Z q' ω| ^ 16) ∂P ≤ ENNReal.ofReal (K * ‖q - q'‖ ^ 8)

/-- The event that level `j` is bad on the box `R`. -/
def badSetD (R j : ℕ) : Set Ω := {ω | ¬ GoodD (fun q => Z q ω) R j}

variable {Z}

theorem lptD_mem_boxD {R j : ℕ} {a : Fin d → ℤ} (ha : InRangeD R j a) (i : Fin d) :
    lptD j (a + Pi.single i 1) ∈ boxD (R + 1) ∧ lptD j a ∈ boxD (R + 1) := by
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have key : ∀ c : ℤ, |c| ≤ (R : ℤ) * 2 ^ j + 1 → |(c : ℝ) / 2 ^ j| ≤ ((R + 1 : ℕ) : ℝ) := by
    intro c hc
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have : (|c| : ℝ) ≤ (R : ℝ) * 2 ^ j + 1 := by exact_mod_cast hc
    rw [← Int.cast_abs]; push_cast; nlinarith
  refine ⟨fun i' => key _ ?_, fun i' => key _ ?_⟩
  · have := ha i'
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> [skip; skip] <;> rw [abs_le] at this ⊢ <;> constructor <;> omega
  · have := ha i'; omega

theorem norm_lptD_step_le (j : ℕ) (a : Fin d → ℤ) (i : Fin d) :
    ‖lptD j (a + Pi.single i 1) - lptD j a‖ ≤ 1 / 2 ^ j := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i' => ?_
  simp only [Pi.sub_apply, lptD, Pi.add_apply, Pi.single_apply, Real.norm_eq_abs]
  split_ifs
  · rw [← sub_div]; push_cast; rw [add_sub_cancel_left, abs_div, abs_one, abs_of_pos (by positivity)]
  · rw [add_zero, sub_self, abs_zero]; positivity

theorem measure_badSetD_le (hd : d ≤ 4) (hZ : ∀ q, AEMeasurable (Z q) P) {K : ℝ} (hK : 0 ≤ K)
    {R : ℕ} (hmom : MomentBoundD Z P K (R + 1)) (j : ℕ) :
    P (badSetD Z R j) ≤ ENNReal.ofReal (d * (2 * R + 1) ^ d * K * q16 ^ j) := by
  classical
  set A : ℤ := (R : ℤ) * 2 ^ j with hA
  have hA0 : 0 ≤ A := by positivity
  set S : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-A) A with hS
  set E : (Fin d → ℤ) → Fin d → Set Ω := fun a i =>
    {ω | θc ^ j < |Z (lptD j (a + Pi.single i 1)) ω - Z (lptD j a) ω|} with hE
  have hsub : badSetD Z R j ⊆ ⋃ a ∈ S, ⋃ i, E a i := by
    intro ω hω
    simp only [badSetD, GoodD, not_forall, Set.mem_ofPred_eq, not_le] at hω
    obtain ⟨a, ha, i, hi⟩ := hω
    simp only [Set.mem_iUnion]
    exact ⟨a, Fintype.mem_piFinset.2 fun i' => Finset.mem_Icc.2 (abs_le.1 (ha i')), i, hi⟩
  have hEb : ∀ a ∈ S, ∀ i, P (E a i) ≤ ENNReal.ofReal (K * r16 ^ j) := by
    intro a haS i
    have ha : InRangeD R j a := fun i' =>
      abs_le.2 (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 haS i'))
    obtain ⟨h1, h2⟩ := lptD_mem_boxD ha i
    have hm := hmom _ h1 _ h2
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_lptD_step_le j a i) 8
    refine (meas_gt_le_of_moment16 (hZ _) (hZ _) (pow_pos θc_pos j)
      (hm.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hn hK)))).trans ?_
    rw [mul_div_assoc, pow_ratio16]
  have hcard : (S.card : ℝ) = (2 * A + 1 : ℤ) ^ d := by
    rw [hS, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Int.card_Icc]
    have h1 : (0 : ℤ) ≤ A + 1 - -A := by omega
    push_cast
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]; push_cast; ring
  have hq : (0 : ℝ) ≤ K * r16 ^ j := mul_nonneg hK (pow_nonneg r16_pos.le _)
  calc P (badSetD Z R j) ≤ P (⋃ a ∈ S, ⋃ i, E a i) := measure_mono hsub
    _ ≤ ∑ a ∈ S, P (⋃ i, E a i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ a ∈ S, ∑ i, P (E a i) := Finset.sum_le_sum fun a _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ a ∈ S, ∑ _i : Fin d, ENNReal.ofReal (K * r16 ^ j) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun i _ => hEb a ha i
    _ = ENNReal.ofReal ((S.card : ℝ) * (d * (K * r16 ^ j))) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (d * (2 * R + 1) ^ d * K * q16 ^ j) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hcard, hA]
        push_cast
        have ht : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
        have e1 : (2 * ((R : ℝ) * 2 ^ j) + 1) ^ d ≤ (2 * R + 1) ^ d * ((2 : ℝ) ^ j) ^ d := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (by nlinarith) d
        have e2 : ((2 : ℝ) ^ j) ^ d ≤ ((2 : ℝ) ^ j) ^ 4 := pow_le_pow_right₀ ht hd
        have e3 : q16 ^ j = ((2 : ℝ) ^ j) ^ 4 * r16 ^ j := by
          rw [q16, mul_pow, ← pow_mul, mul_comm j 4, pow_mul]; norm_num
        rw [e3]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        calc (2 * ((R : ℝ) * 2 ^ j) + 1) ^ d * (d * (K * r16 ^ j))
            ≤ ((2 * R + 1) ^ d * ((2 : ℝ) ^ j) ^ 4) * (d * (K * r16 ^ j)) :=
              mul_le_mul_of_nonneg_right (e1.trans (mul_le_mul_of_nonneg_left e2
                (by positivity))) (by positivity)
          _ = d * (2 * R + 1) ^ d * K * (((2 : ℝ) ^ j) ^ 4 * r16 ^ j) := by ring

theorem ae_good_D (hd : d ≤ 4) (hZ : ∀ q, AEMeasurable (Z q) P)
    (hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundD Z P K R) :
    ∀ᵐ ω ∂P, ∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodD (fun q => Z q ω) R j := by
  rw [ae_all_iff]
  intro R
  obtain ⟨K, hK, hm⟩ := hmom (R + 1)
  have hsum : ∑' j, P (badSetD Z R j) ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_geom_ne_top (by positivity) (r16_pos.le.trans r16_le_q16) q16_lt_one)
      (ENNReal.tsum_le_tsum fun j => measure_badSetD_le hd hZ hK hm j)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  exact ⟨N, fun j hj => not_not.1 (hN j hj)⟩

theorem abs_rndD_sub_le (n : ℕ) (q : Fin d → ℝ) (i : Fin d) : |rndD n q i - q i| ≤ 1 / 2 ^ n :=
  CircleCont.abs_dyadicRound_sub_le n (q i)

theorem norm_rndD_sub_le (n : ℕ) (q : Fin d → ℝ) : ‖rndD n q - q‖ ≤ 1 / 2 ^ n :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
    rw [Pi.sub_apply, Real.norm_eq_abs]; exact abs_rndD_sub_le n q i

theorem ae_tendsto_at_D (hZ : ∀ q, AEMeasurable (Z q) P)
    (hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundD Z P K R) (q : Fin d → ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Z (rndD n q) ω) atTop (𝓝 (Z q ω)) := by
  obtain ⟨R, hR⟩ := exists_nat_ge (‖q‖ + 1)
  obtain ⟨K, hK, hm⟩ := hmom R
  have hqR : q ∈ boxD R := mem_boxD_of_norm (by linarith)
  have hrR : ∀ n, rndD n q ∈ boxD R := fun n => mem_boxD_of_norm (by
    have h1 := norm_rndD_sub_le n q
    have h2 : (1 : ℝ) / 2 ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have := norm_sub_norm_le (rndD n q) q
    linarith)
  have hev : ∀ n : ℕ, P {ω | θc ^ n < |Z (rndD n q) ω - Z q ω|} ≤
      ENNReal.ofReal (K * r16 ^ n) := by
    intro n
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_rndD_sub_le n q) 8
    refine (meas_gt_le_of_moment16 (hZ _) (hZ q) (pow_pos θc_pos n)
      ((hm _ (hrR n) _ hqR).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hn hK)))).trans (le_of_eq ?_)
    rw [mul_div_assoc, pow_ratio16]
  have hsum : ∑' n, P {ω | θc ^ n < |Z (rndD n q) ω - Z q ω|} ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_geom_ne_top hK r16_pos.le
      (r16_le_q16.trans_lt q16_lt_one)) (ENNReal.tsum_le_tsum hev)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one θc_pos.le θc_lt_one)
  filter_upwards [hω] with n hn
  simpa [Real.norm_eq_abs] using hn

/-- **Kolmogorov continuity in `d ≤ 4` parameters (dyadic version).** -/
theorem exists_continuous_modification_D (hd : d ≤ 4) (hZ : ∀ q, AEMeasurable (Z q) P)
    (hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundD Z P K R) :
    ∃ Y : (Fin d → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧
      (∀ q, (fun ω => Y q ω) =ᵐ[P] Z q) ∧
      (∀ᵐ ω ∂P, ∀ q, Tendsto (fun n => Z (rndD n q) ω) atTop (𝓝 (Y q ω))) := by
  classical
  refine ⟨fun q ω => if (∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodD (fun q => Z q ω) R j) then
    limUnder atTop (fun n => Z (rndD n q) ω) else 0, ?_, ?_, ?_⟩
  · intro ω
    by_cases h : ∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodD (fun q => Z q ω) R j
    · simp only [if_pos h]; exact continuous_of_good_D h
    · simp only [if_neg h]; exact continuous_const
  · intro q
    filter_upwards [ae_good_D hd hZ hmom, ae_tendsto_at_D hZ hmom q] with ω hG ht
    simp only [if_pos hG]
    exact ht.limUnder_eq
  · filter_upwards [ae_good_D hd hZ hmom] with ω hG q
    simp only [if_pos hG]
    obtain ⟨R, hR⟩ := exists_nat_ge ‖q‖
    obtain ⟨N, hN⟩ := hG R
    exact tendsto_of_good_D (f := fun q => Z q ω) (mem_boxD_of_norm hR) hN

end KolmD
end QuantumZipper
