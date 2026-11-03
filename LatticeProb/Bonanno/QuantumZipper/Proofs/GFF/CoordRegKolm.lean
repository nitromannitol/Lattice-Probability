/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.CoordRegKolm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample

/-!
# Dyadic Kolmogorov continuity with a general Hölder exponent (helper for RC2)

`RegularSampleKolmogorov` (namespace `KolmD`) fixes the level threshold `θ = 7/8` and the
moment hypothesis `E|Z q − Z q'|¹⁶ ≤ K ‖q − q'‖⁸`. The energy modulus (E) of the unzip maps only
gives `Var(Z q − Z q') ≤ L ‖q − q'‖^{1/12}`, which needs a threshold `θ` close to `1` and a high
moment. This file redoes the chaining with a general `θ ∈ (0,1)`, a general moment `p` and a
general exponent `a` with `16 · 2^{-a} / θ^p < 1` (dimension `d ≤ 4`), reusing the lattice
bookkeeping of `KolmD`. It also records the absolute moments of centred Gaussians.

Source: Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. I, Thm (2.1),
pp. 26–27 (the multiparameter Kolmogorov–Čentsov criterion). `exists_continuous_modification_G`
is a correct **special case** of it, with these differences (AUDIT8 G3): the dimension is
restricted to `d ≤ 4`, the moment to an integer `p`, the constants to one per box `R`, and the
threshold condition `16 · 2^{−a}/θ^p < 1` forces `a > 4` in every dimension (RY ask for `a > d`,
weaker when `d < 4`); the conclusion gives continuity only, not a Hölder order. This suffices for
RC2 (`d = 4`, `a = mβ > 8`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace QuantumZipper
namespace KolmG

open KolmD
open CircleCont (floor_succ_bounds abs_floor_sub_of_lt tsum_geom_ne_top)

variable {d : ℕ} {θ : ℝ}

/-- All one-step increments at level `j` based in the box `R` are at most `θ^j`. -/
def GoodG (θ : ℝ) (f : (Fin d → ℝ) → ℝ) (R j : ℕ) : Prop :=
  ∀ a, InRangeD R j a → ∀ i, |f (lptD j (a + Pi.single i 1)) - f (lptD j a)| ≤ θ ^ j

variable {f : (Fin d → ℝ) → ℝ} {R : ℕ}

theorem near_G (hθ0 : 0 < θ) {j : ℕ} (hg : GoodG θ f R j) {a a' : Fin d → ℤ}
    (ha : InRangeD R j a) (ha' : InRangeD R j a') (h1 : ∀ i, |a i - a' i| ≤ 1) :
    |f (lptD j a') - f (lptD j a)| ≤ d * θ ^ j := by
  set b : ℕ → Fin d → ℤ := fun m i => if (i : ℕ) < m then a' i else a i with hb
  have hb0 : b 0 = a := by funext i; simp [hb]
  have hbd : b d = a' := by funext i; simp [hb, i.isLt]
  have hbR : ∀ m, InRangeD R j (b m) := fun m i => by
    simp only [hb]; split_ifs
    · exact ha' i
    · exact ha i
  have hθ : 0 ≤ θ ^ j := pow_nonneg hθ0.le j
  have step : ∀ m (hm : m < d), |f (lptD j (b (m + 1))) - f (lptD j (b m))| ≤ θ ^ j := by
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
  have ind : ∀ m ≤ d, |f (lptD j (b m)) - f (lptD j a)| ≤ m * θ ^ j := by
    intro m
    induction m with
    | zero => intro _; simp [hb0]
    | succ m ih =>
      intro hm
      calc |f (lptD j (b (m + 1))) - f (lptD j a)|
          ≤ |f (lptD j (b (m + 1))) - f (lptD j (b m))| + |f (lptD j (b m)) - f (lptD j a)| :=
            abs_sub_le _ _ _
        _ ≤ θ ^ j + m * θ ^ j := add_le_add (step m (by omega)) (ih (by omega))
        _ = ((m + 1 : ℕ) : ℝ) * θ ^ j := by push_cast; ring
  simpa [hbd] using ind d le_rfl

theorem consec_G (hθ0 : 0 < θ) {q : Fin d → ℝ} (hq : q ∈ boxD R) {j : ℕ}
    (hg : GoodG θ f R (j + 1)) :
    |f (rndD (j + 1) q) - f (rndD j q)| ≤ d * θ ^ (j + 1) := by
  unfold rndD
  rw [lptD_succ j]
  refine near_G hθ0 hg ?_ (inRange_flr hq (j + 1)) ?_
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

theorem telescope_G (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : Fin d → ℝ} (hq : q ∈ boxD R) {N : ℕ}
    (hg : ∀ j ≥ N, GoodG θ f R j) {n : ℕ} (hn : N ≤ n) (i : ℕ) :
    |f (rndD (n + i) q) - f (rndD n q)| ≤ d / (1 - θ) * θ ^ n * (1 - θ ^ i) := by
  have h1θ : 0 < 1 - θ := by linarith
  induction i with
  | zero => simp
  | succ i ih =>
    have hc := consec_G (f := f) hθ0 hq (j := n + i) (hg _ (by omega))
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have e : (d : ℝ) / (1 - θ) * θ ^ n * (1 - θ ^ (i + 1)) =
        d / (1 - θ) * θ ^ n * (1 - θ ^ i) + d * θ ^ (n + i) := by
      field_simp
      ring
    calc |f (rndD (n + (i + 1)) q) - f (rndD n q)|
        ≤ |f (rndD (n + i + 1) q) - f (rndD (n + i) q)| +
          |f (rndD (n + i) q) - f (rndD n q)| := by
          rw [← add_assoc]; exact abs_sub_le _ _ _
      _ ≤ d * θ ^ (n + i + 1) + d / (1 - θ) * θ ^ n * (1 - θ ^ i) := add_le_add hc ih
      _ ≤ _ := by
          rw [e]
          have : θ ^ (n + i + 1) ≤ θ ^ (n + i) :=
            pow_le_pow_of_le_one hθ0.le hθ1.le (by omega)
          nlinarith

theorem telescope_G' (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : Fin d → ℝ} (hq : q ∈ boxD R) {N : ℕ}
    (hg : ∀ j ≥ N, GoodG θ f R j) {n M : ℕ} (hn : N ≤ n) (hM : n ≤ M) :
    |f (rndD M q) - f (rndD n q)| ≤ d / (1 - θ) * θ ^ n := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hM
  have h := telescope_G hθ0 hθ1 hq hg hn i
  have h1θ : 0 < 1 - θ := by linarith
  have : 0 ≤ (d : ℝ) / (1 - θ) * θ ^ n := by positivity
  have : 0 ≤ θ ^ i := pow_nonneg hθ0.le i
  nlinarith

theorem level_mod_G (hθ0 : 0 < θ) (hθ1 : θ < 1) {q q' : Fin d → ℝ} (hq : q ∈ boxD R)
    (hq' : q' ∈ boxD R) {N : ℕ} (hg : ∀ j ≥ N, GoodG θ f R j) {n : ℕ} (hn : N ≤ n)
    (hqq : ∀ i, |q i - q' i| < 1 / 2 ^ n) {M : ℕ} (hM : n ≤ M) :
    |f (rndD M q) - f (rndD M q')| ≤ (2 * (d / (1 - θ)) + d) * θ ^ n := by
  have h1 := telescope_G' hθ0 hθ1 hq hg hn hM
  have h2 := telescope_G' hθ0 hθ1 hq' hg hn hM
  have h3 : |f (rndD n q') - f (rndD n q)| ≤ d * θ ^ n :=
    near_G hθ0 (hg n hn) (inRange_flr hq n) (inRange_flr hq' n) fun i =>
      abs_floor_sub_of_lt (hqq i)
  rw [abs_sub_comm] at h2 h3
  have h4 := abs_add_three (f (rndD M q) - f (rndD n q))
    (f (rndD n q) - f (rndD n q')) (f (rndD n q') - f (rndD M q'))
  have e : f (rndD M q) - f (rndD n q) + (f (rndD n q) - f (rndD n q')) +
      (f (rndD n q') - f (rndD M q')) = f (rndD M q) - f (rndD M q') := by ring
  rw [e] at h4
  nlinarith

theorem tendsto_of_good_G (hθ0 : 0 < θ) (hθ1 : θ < 1) {q : Fin d → ℝ} (hq : q ∈ boxD R)
    {N : ℕ} (hg : ∀ j ≥ N, GoodG θ f R j) :
    Tendsto (fun M => f (rndD M q)) atTop (𝓝 (limUnder atTop fun M => f (rndD M q))) := by
  apply CauchySeq.tendsto_limUnder
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have h1θ : 0 < 1 - θ := by linarith
  set c : ℝ := d / (1 - θ) with hc
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨n, hn1, hn2⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).eventually
    (gt_mem_nhds (show 0 < ε / (c + 1) by positivity))).and (eventually_ge_atTop N)).exists
  refine ⟨n, fun M hM => ?_⟩
  rw [Real.dist_eq]
  have := telescope_G' hθ0 hθ1 hq hg hn2 hM
  have : c * θ ^ n < ε := by
    rw [lt_div_iff₀ (by positivity)] at hn1
    nlinarith [pow_nonneg hθ0.le n]
  linarith

theorem continuous_of_good_G (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hg : ∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodG θ f R j) :
    Continuous (fun q => limUnder atTop fun M => f (rndD M q)) := by
  rw [Metric.continuous_iff]
  intro q ε hε
  have h1θ : 0 < 1 - θ := by linarith
  set c : ℝ := 2 * (d / (1 - θ)) + d with hc
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨R, hR⟩ := exists_nat_ge (‖q‖ + 1)
  obtain ⟨N, hN⟩ := hg R
  obtain ⟨n, hn1, hn2⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).eventually
    (gt_mem_nhds (show 0 < ε / (c + 1) by positivity))).and (eventually_ge_atTop N)).exists
  refine ⟨min 1 (1 / 2 ^ n), by positivity, fun {q'} hq' => ?_⟩
  rw [dist_eq_norm] at hq'
  have hqb : q ∈ boxD R := mem_boxD_of_norm (by linarith)
  have hq'b : q' ∈ boxD R := mem_boxD_of_norm (by
    have h1 : ‖q' - q‖ < 1 := lt_of_lt_of_le hq' (min_le_left _ _)
    linarith [norm_sub_norm_le q' q])
  have hi : ∀ i, |q' i - q i| < 1 / 2 ^ n := fun i =>
    lt_of_le_of_lt (by simpa using norm_le_pi_norm (q' - q) i)
      (lt_of_lt_of_le hq' (min_le_right _ _))
  have hle : |(limUnder atTop fun M => f (rndD M q')) -
      limUnder atTop fun M => f (rndD M q)| ≤ c * θ ^ n :=
    le_of_tendsto (((tendsto_of_good_G hθ0 hθ1 hq'b hN).sub
      (tendsto_of_good_G hθ0 hθ1 hqb hN)).abs)
      (eventually_atTop.2 ⟨n, fun M hM => level_mod_G hθ0 hθ1 hq'b hqb hN hn2 hi hM⟩)
  rw [Real.dist_eq]
  have : c * θ ^ n < ε := by
    rw [lt_div_iff₀ (by positivity)] at hn1
    nlinarith [pow_nonneg hθ0.le n]
  linarith

/-! ## Probabilistic part -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem meas_gt_le_of_moment_G {p : ℕ} {U V : Ω → ℝ} (hU : AEMeasurable U P)
    (hV : AEMeasurable V P) {B t : ℝ} (ht : 0 < t)
    (hmom : ∫⁻ ω, ENNReal.ofReal (|U ω - V ω| ^ p) ∂P ≤ ENNReal.ofReal B) :
    P {ω | t < |U ω - V ω|} ≤ ENNReal.ofReal (B / t ^ p) := by
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (|U ω - V ω| ^ p)) P :=
    ((continuous_abs.measurable.comp_aemeasurable (hU.sub hV)).pow_const p).ennreal_ofReal
  have hm := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal (t ^ p))
  have hsub : {ω | t < |U ω - V ω|} ⊆
      {ω | ENNReal.ofReal (t ^ p) ≤ ENNReal.ofReal (|U ω - V ω| ^ p)} := fun ω hω =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht.le (le_of_lt hω) p)
  have hpos : ENNReal.ofReal (t ^ p) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  calc P {ω | t < |U ω - V ω|}
      ≤ P {ω | ENNReal.ofReal (t ^ p) ≤ ENNReal.ofReal (|U ω - V ω| ^ p)} := measure_mono hsub
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal (t ^ p) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact hm.trans hmom
    _ = ENNReal.ofReal (B / t ^ p) := (ENNReal.ofReal_div_of_pos (by positivity)).symm

variable (Z : (Fin d → ℝ) → Ω → ℝ)

/-- The moment hypothesis `E|Z q − Z q'|^p ≤ K ‖q − q'‖^a` on the box `R`. -/
def MomentBoundG (P : Measure Ω) (p : ℕ) (a K : ℝ) (R : ℕ) : Prop :=
  ∀ q ∈ boxD (d := d) R, ∀ q' ∈ boxD R,
    ∫⁻ ω, ENNReal.ofReal (|Z q ω - Z q' ω| ^ p) ∂P ≤ ENNReal.ofReal (K * ‖q - q'‖ ^ a)

/-- The event that level `j` is bad on the box `R`. -/
def badSetG (θ : ℝ) (R j : ℕ) : Set Ω := {ω | ¬ GoodG θ (fun q => Z q ω) R j}

variable {Z}

theorem pow_ratio_G {a : ℝ} (ha : 0 ≤ a) (p j : ℕ) :
    (1 / 2 ^ j : ℝ) ^ a / (θ ^ j) ^ p = ((1 / 2 : ℝ) ^ a / θ ^ p) ^ j := by
  have e1 : (1 / 2 ^ j : ℝ) ^ a = ((1 / 2 : ℝ) ^ a) ^ j := by
    rw [one_div, ← inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast, one_div]
  have e2 : (θ ^ j) ^ p = (θ ^ p) ^ j := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [e1, e2, div_pow]

theorem measure_badSetG_le (hd : d ≤ 4) (hθ0 : 0 < θ) (hZ : ∀ q, AEMeasurable (Z q) P)
    {p : ℕ} {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K) {R : ℕ} (hmom : MomentBoundG Z P p a K (R + 1))
    (j : ℕ) :
    P (badSetG Z θ R j) ≤
      ENNReal.ofReal (d * (2 * R + 1) ^ d * K * (16 * ((1 / 2 : ℝ) ^ a / θ ^ p)) ^ j) := by
  classical
  set r : ℝ := (1 / 2 : ℝ) ^ a / θ ^ p with hr
  have hr0 : 0 ≤ r := by positivity
  set A : ℤ := (R : ℤ) * 2 ^ j with hA
  have hA0 : 0 ≤ A := by positivity
  set S : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-A) A with hS
  set E : (Fin d → ℤ) → Fin d → Set Ω := fun a i =>
    {ω | θ ^ j < |Z (lptD j (a + Pi.single i 1)) ω - Z (lptD j a) ω|} with hE
  have hsub : badSetG Z θ R j ⊆ ⋃ a ∈ S, ⋃ i, E a i := by
    intro ω hω
    simp only [badSetG, GoodG, not_forall, Set.mem_ofPred_eq, not_le] at hω
    obtain ⟨a, ha, i, hi⟩ := hω
    simp only [Set.mem_iUnion]
    exact ⟨a, Fintype.mem_piFinset.2 fun i' => Finset.mem_Icc.2 (abs_le.1 (ha i')), i, hi⟩
  have hEb : ∀ a ∈ S, ∀ i, P (E a i) ≤ ENNReal.ofReal (K * r ^ j) := by
    intro a haS i
    have ha' : InRangeD R j a := fun i' =>
      abs_le.2 (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 haS i'))
    obtain ⟨h1, h2⟩ := lptD_mem_boxD ha' i
    have hm := hmom _ h1 _ h2
    have hn := Real.rpow_le_rpow (norm_nonneg _) (norm_lptD_step_le j a i) ha
    refine (meas_gt_le_of_moment_G (hZ _) (hZ _) (pow_pos hθ0 j)
      (hm.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hn hK)))).trans ?_
    rw [mul_div_assoc, pow_ratio_G ha]
  have hcard : (S.card : ℝ) = (2 * A + 1 : ℤ) ^ d := by
    rw [hS, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Int.card_Icc]
    have h1 : (0 : ℤ) ≤ A + 1 - -A := by omega
    push_cast
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]; push_cast; ring
  calc P (badSetG Z θ R j) ≤ P (⋃ a ∈ S, ⋃ i, E a i) := measure_mono hsub
    _ ≤ ∑ a ∈ S, P (⋃ i, E a i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ a ∈ S, ∑ i, P (E a i) := Finset.sum_le_sum fun a _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ a ∈ S, ∑ _i : Fin d, ENNReal.ofReal (K * r ^ j) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun i _ => hEb a ha i
    _ = ENNReal.ofReal ((S.card : ℝ) * (d * (K * r ^ j))) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (d * (2 * R + 1) ^ d * K * (16 * r) ^ j) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hcard, hA]
        push_cast
        have ht : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
        have e1 : (2 * ((R : ℝ) * 2 ^ j) + 1) ^ d ≤ (2 * R + 1) ^ d * ((2 : ℝ) ^ j) ^ d := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (by nlinarith) d
        have e2 : ((2 : ℝ) ^ j) ^ d ≤ ((2 : ℝ) ^ j) ^ 4 := pow_le_pow_right₀ ht hd
        have e3 : (16 * r) ^ j = ((2 : ℝ) ^ j) ^ 4 * r ^ j := by
          rw [mul_pow, ← pow_mul, mul_comm j 4, pow_mul]; norm_num
        rw [e3]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        calc (2 * ((R : ℝ) * 2 ^ j) + 1) ^ d * (d * (K * r ^ j))
            ≤ ((2 * R + 1) ^ d * ((2 : ℝ) ^ j) ^ 4) * (d * (K * r ^ j)) :=
              mul_le_mul_of_nonneg_right (e1.trans (mul_le_mul_of_nonneg_left e2
                (by positivity))) (by positivity)
          _ = d * (2 * R + 1) ^ d * K * (((2 : ℝ) ^ j) ^ 4 * r ^ j) := by ring

theorem ae_good_G (hd : d ≤ 4) (hθ0 : 0 < θ) (hZ : ∀ q, AEMeasurable (Z q) P) {p : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (hρ : 16 * ((1 / 2 : ℝ) ^ a / θ ^ p) < 1)
    (hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundG Z P p a K R) :
    ∀ᵐ ω ∂P, ∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodG θ (fun q => Z q ω) R j := by
  rw [ae_all_iff]
  intro R
  obtain ⟨K, hK, hm⟩ := hmom (R + 1)
  have hsum : ∑' j, P (badSetG Z θ R j) ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_geom_ne_top (by positivity) (by positivity) hρ)
      (ENNReal.tsum_le_tsum fun j => measure_badSetG_le hd hθ0 hZ ha hK hm j)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  exact ⟨N, fun j hj => not_not.1 (hN j hj)⟩

theorem ae_tendsto_at_G (hθ0 : 0 < θ) (hθ1 : θ < 1) (hZ : ∀ q, AEMeasurable (Z q) P) {p : ℕ}
    {a : ℝ} (ha : 0 ≤ a) (hρ : 16 * ((1 / 2 : ℝ) ^ a / θ ^ p) < 1)
    (hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundG Z P p a K R) (q : Fin d → ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Z (rndD n q) ω) atTop (𝓝 (Z q ω)) := by
  set r : ℝ := (1 / 2 : ℝ) ^ a / θ ^ p with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by linarith
  obtain ⟨R, hR⟩ := exists_nat_ge (‖q‖ + 1)
  obtain ⟨K, hK, hm⟩ := hmom R
  have hqR : q ∈ boxD R := mem_boxD_of_norm (by linarith)
  have hrR : ∀ n, rndD n q ∈ boxD R := fun n => mem_boxD_of_norm (by
    have h1 := norm_rndD_sub_le n q
    have h2 : (1 : ℝ) / 2 ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have := norm_sub_norm_le (rndD n q) q
    linarith)
  have hev : ∀ n : ℕ, P {ω | θ ^ n < |Z (rndD n q) ω - Z q ω|} ≤ ENNReal.ofReal (K * r ^ n) := by
    intro n
    have hn := Real.rpow_le_rpow (norm_nonneg _) (norm_rndD_sub_le n q) ha
    refine (meas_gt_le_of_moment_G (hZ _) (hZ q) (pow_pos hθ0 n)
      ((hm _ (hrR n) _ hqR).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hn hK)))).trans (le_of_eq ?_)
    rw [mul_div_assoc, pow_ratio_G ha]
  have hsum : ∑' n, P {ω | θ ^ n < |Z (rndD n q) ω - Z q ω|} ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_geom_ne_top hK hr0 hr1) (ENNReal.tsum_le_tsum hev)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1)
  filter_upwards [hω] with n hn
  simpa [Real.norm_eq_abs] using hn

/-- **Kolmogorov continuity in `d ≤ 4` parameters, general exponents (dyadic version).** -/
theorem exists_continuous_modification_G (hd : d ≤ 4) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hZ : ∀ q, AEMeasurable (Z q) P) {p : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hρ : 16 * ((1 / 2 : ℝ) ^ a / θ ^ p) < 1)
    (hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundG Z P p a K R) :
    ∃ Y : (Fin d → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧
      (∀ q, (fun ω => Y q ω) =ᵐ[P] Z q) ∧
      (∀ᵐ ω ∂P, ∀ q, Tendsto (fun n => Z (rndD n q) ω) atTop (𝓝 (Y q ω))) := by
  classical
  refine ⟨fun q ω => if (∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodG θ (fun q => Z q ω) R j) then
    limUnder atTop (fun n => Z (rndD n q) ω) else 0, ?_, ?_, ?_⟩
  · intro ω
    by_cases h : ∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodG θ (fun q => Z q ω) R j
    · simp only [if_pos h]; exact continuous_of_good_G hθ0 hθ1 h
    · simp only [if_neg h]; exact continuous_const
  · intro q
    filter_upwards [ae_good_G hd hθ0 hZ ha hρ hmom,
      ae_tendsto_at_G hθ0 hθ1 hZ ha hρ hmom q] with ω hG ht
    simp only [if_pos hG]
    exact ht.limUnder_eq
  · filter_upwards [ae_good_G hd hθ0 hZ ha hρ hmom] with ω hG q
    simp only [if_pos hG]
    obtain ⟨R, hR⟩ := exists_nat_ge ‖q‖
    obtain ⟨N, hN⟩ := hG R
    exact tendsto_of_good_G hθ0 hθ1 (mem_boxD_of_norm hR) hN

/-! ## Absolute moments of centred Gaussians -/

theorem integrable_abs_pow_gaussianReal (n : ℕ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => |x| ^ n) (gaussianReal 0 v) := by
  have hmem : MemLp (fun x : ℝ => x) ((n : ℕ) : ℝ≥0) (gaussianReal 0 v) :=
    memLp_id_gaussianReal n
  have hint : Integrable (fun x : ℝ => ‖x‖ ^ n) (gaussianReal 0 v) := hmem.integrable_norm_pow'
  simpa [Real.norm_eq_abs] using hint

theorem integral_abs_pow_two_mul_gaussianReal (m : ℕ) (v : ℝ≥0) :
    ∫ x, |x| ^ (2 * m) ∂(gaussianReal 0 v) = (v : ℝ) ^ m * gaussianAbsMoment (2 * m) := by
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
  have hpt : ∀ x : ℝ, |Real.sqrt v * x| ^ (2 * m) = (v : ℝ) ^ m * |x| ^ (2 * m) := by
    intro x
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, pow_mul, hcsq]
  simp_rw [hpt]
  rw [integral_const_mul]
  rfl

/-- `E|U|^{2m} = v^m · E|N(0,1)|^{2m}` for a centred Gaussian `U` of variance `v`. -/
theorem lintegral_pow_two_mul_of_map_eq {U : Ω → ℝ} (hU : Measurable U) {v : ℝ≥0} (m : ℕ)
    (hlaw : P.map U = gaussianReal 0 v) :
    ∫⁻ ω, ENNReal.ofReal (|U ω| ^ (2 * m)) ∂P =
      ENNReal.ofReal ((v : ℝ) ^ m * gaussianAbsMoment (2 * m)) := by
  have hi := integrable_abs_pow_gaussianReal (2 * m) v
  rw [← hlaw] at hi
  rw [← integral_abs_pow_two_mul_gaussianReal, ← hlaw,
    ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity)]
  exact (lintegral_map (f := fun x : ℝ => ENNReal.ofReal (|x| ^ (2 * m)))
    (Measurable.ennreal_ofReal (by fun_prop)) hU).symm

end KolmG
end QuantumZipper
