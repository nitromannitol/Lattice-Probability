/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.KolmN at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegKolm

/-!
# Kolmogorov–Čentsov continuity in any finite number of parameters

`KolmG.exists_continuous_modification_G` (`Proofs/GFF/CoordRegKolm.lean`) is the dyadic
Kolmogorov continuity criterion restricted to `d ≤ 4` parameters: the restriction enters only
through the union bound over the `(2R 2^j + 1)^d` lattice points of level `j` (it bounds
`2^{jd}` by `2^{4j}`). This file removes the restriction:

* `KolmN.measure_badSetG_le_N`: the union bound with the factor `2^{jd}` (any `d`);
* `KolmN.exists_continuous_modification_N'`: the criterion under the threshold condition
  `2^d · 2^{-a} / θ^p < 1` (for `d = 4` this is the condition of `KolmG`);
* **`KolmN.exists_continuous_modification_N`**: the Revuz–Yor form. If
  `E|Z_q − Z_{q'}|^p ≤ K_R ‖q − q'‖^a` on every box `[-R, R]^d`, with an integer `p ≥ 1` and
  `a > d`, then `Z` has a modification `Y` that is continuous for every `ω`, and a.s.
  `Z(q_n) → Y(q)` along the dyadic approximations `q_n = rndD n q`.

Source: Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. I, Thm (2.1),
pp. 26–27 (the multiparameter Kolmogorov–Čentsov criterion: `E|X_s − X_t|^γ ≤ c|s − t|^{d+ε}`
on `[0,1]^d` gives a continuous (Hölder) modification); the chaining is that of
`CoordRegKolm.lean` (which follows RY's proof), with the lattice count in dimension `d`.
Differences from RY: the moment exponent is an integer `p ≥ 1`; the constant may depend on the
box (a local hypothesis, slightly more general); the conclusion states continuity and dyadic
convergence, not the Hölder order. The choice of the level threshold `θ` from `a > d` is an own
elementary step (Bernoulli's inequality).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace QuantumZipper
namespace KolmN

open KolmD KolmG
open CircleCont (tsum_geom_ne_top)

variable {d : ℕ} {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {Z : (Fin d → ℝ) → Ω → ℝ}

/-- **The union bound of level `j`, in dimension `d`.** -/
theorem measure_badSetG_le_N (hθ0 : 0 < θ) (hZ : ∀ q, AEMeasurable (Z q) P)
    {p : ℕ} {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K) {R : ℕ} (hmom : MomentBoundG Z P p a K (R + 1))
    (j : ℕ) :
    P (badSetG Z θ R j) ≤
      ENNReal.ofReal (d * (2 * R + 1) ^ d * K * ((2 : ℝ) ^ d * ((1 / 2 : ℝ) ^ a / θ ^ p)) ^ j) := by
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
    _ ≤ ENNReal.ofReal (d * (2 * R + 1) ^ d * K * ((2 : ℝ) ^ d * r) ^ j) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hcard, hA]
        push_cast
        have ht : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
        have e1 : (2 * ((R : ℝ) * 2 ^ j) + 1) ^ d ≤ (2 * R + 1) ^ d * ((2 : ℝ) ^ j) ^ d := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (by nlinarith) d
        have e3 : ((2 : ℝ) ^ d * r) ^ j = ((2 : ℝ) ^ j) ^ d * r ^ j := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j d]
        rw [e3]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        calc (2 * ((R : ℝ) * 2 ^ j) + 1) ^ d * (d * (K * r ^ j))
            ≤ ((2 * R + 1) ^ d * ((2 : ℝ) ^ j) ^ d) * (d * (K * r ^ j)) :=
              mul_le_mul_of_nonneg_right e1 (by positivity)
          _ = d * (2 * R + 1) ^ d * K * (((2 : ℝ) ^ j) ^ d * r ^ j) := by ring

/-- Almost surely every box is good from some level on (dimension `d`). -/
theorem ae_good_N (hθ0 : 0 < θ) (hZ : ∀ q, AEMeasurable (Z q) P) {p : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (hρ : (2 : ℝ) ^ d * ((1 / 2 : ℝ) ^ a / θ ^ p) < 1)
    (hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundG Z P p a K R) :
    ∀ᵐ ω ∂P, ∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodG θ (fun q => Z q ω) R j := by
  rw [ae_all_iff]
  intro R
  obtain ⟨K, hK, hm⟩ := hmom (R + 1)
  have hsum : ∑' j, P (badSetG Z θ R j) ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_geom_ne_top (by positivity) (by positivity) hρ)
      (ENNReal.tsum_le_tsum fun j => measure_badSetG_le_N hθ0 hZ ha hK hm j)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  exact ⟨N, fun j hj => not_not.1 (hN j hj)⟩

/-- Convergence along the dyadic approximations at a fixed point (dimension-free). -/
theorem ae_tendsto_at_N (hθ0 : 0 < θ) (hθ1 : θ < 1) (hZ : ∀ q, AEMeasurable (Z q) P) {p : ℕ}
    {a : ℝ} (ha : 0 ≤ a) (hr1 : (1 / 2 : ℝ) ^ a / θ ^ p < 1)
    (hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundG Z P p a K R) (q : Fin d → ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Z (rndD n q) ω) atTop (𝓝 (Z q ω)) := by
  set r : ℝ := (1 / 2 : ℝ) ^ a / θ ^ p with hr
  have hr0 : 0 ≤ r := by positivity
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

/-- **Kolmogorov continuity in `d` parameters, general exponents (dyadic version).** -/
theorem exists_continuous_modification_N' (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hZ : ∀ q, AEMeasurable (Z q) P) {p : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hρ : (2 : ℝ) ^ d * ((1 / 2 : ℝ) ^ a / θ ^ p) < 1)
    (hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundG Z P p a K R) :
    ∃ Y : (Fin d → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧
      (∀ q, (fun ω => Y q ω) =ᵐ[P] Z q) ∧
      (∀ᵐ ω ∂P, ∀ q, Tendsto (fun n => Z (rndD n q) ω) atTop (𝓝 (Y q ω))) := by
  classical
  have hr1 : (1 / 2 : ℝ) ^ a / θ ^ p < 1 := by
    have h1 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    have h0 : 0 ≤ (1 / 2 : ℝ) ^ a / θ ^ p := by positivity
    nlinarith
  refine ⟨fun q ω => if (∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodG θ (fun q => Z q ω) R j) then
    limUnder atTop (fun n => Z (rndD n q) ω) else 0, ?_, ?_, ?_⟩
  · intro ω
    by_cases h : ∀ R : ℕ, ∃ N, ∀ j ≥ N, GoodG θ (fun q => Z q ω) R j
    · simp only [if_pos h]; exact continuous_of_good_G hθ0 hθ1 h
    · simp only [if_neg h]; exact continuous_const
  · intro q
    filter_upwards [ae_good_N hθ0 hZ ha hρ hmom,
      ae_tendsto_at_N hθ0 hθ1 hZ ha hr1 hmom q] with ω hG ht
    simp only [if_pos hG]
    exact ht.limUnder_eq
  · filter_upwards [ae_good_N hθ0 hZ ha hρ hmom] with ω hG q
    simp only [if_pos hG]
    obtain ⟨R, hR⟩ := exists_nat_ge ‖q‖
    obtain ⟨N, hN⟩ := hG R
    exact tendsto_of_good_G hθ0 hθ1 (mem_boxD_of_norm hR) hN

/-- A level threshold `θ ∈ (0,1)` with `2^d 2^{-a} < θ^p`, for `a > d` and `p ≥ 1`
(own elementary step: Bernoulli's inequality). -/
theorem exists_theta_N {p : ℕ} (hp : 0 < p) {a : ℝ} (ha : (d : ℝ) < a) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ (2 : ℝ) ^ d * ((1 / 2 : ℝ) ^ a / θ ^ p) < 1 := by
  set c : ℝ := (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ a with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := by
    have h1 : (1 / 2 : ℝ) ^ a < (1 / 2 : ℝ) ^ (d : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) ha
    rw [Real.rpow_natCast] at h1
    have h2 : (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d = 1 := by rw [← mul_pow]; norm_num
    have h3 : (0 : ℝ) < 2 ^ d := by positivity
    calc c < (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d := mul_lt_mul_of_pos_left h1 h3
      _ = 1 := h2
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  set ε : ℝ := (1 - c) / (2 * p) with hε
  have hε0 : 0 < ε := by rw [hε]; apply div_pos <;> linarith
  have hεp : p * ε = (1 - c) / 2 := by rw [hε]; field_simp
  have hε1 : ε < 1 := by
    have h1p : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have : ε ≤ (1 - c) / 2 := by
      rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  refine ⟨1 - ε, by linarith, by linarith, ?_⟩
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -ε by linarith) p
  have hθp : c < (1 - ε) ^ p := by
    have : (1 : ℝ) + p * -ε = 1 - (1 - c) / 2 := by rw [← hεp]; ring
    rw [show (1 : ℝ) - ε = 1 + -ε by ring]
    linarith
  have hpos : 0 < (1 - ε) ^ p := lt_trans hc0 hθp
  rw [← mul_div_assoc, div_lt_one hpos]
  exact hθp

/-- **Kolmogorov–Čentsov criterion in `d` parameters** (Revuz–Yor, Ch. I, Thm (2.1)): if
`E|Z_q − Z_{q'}|^p ≤ K_R ‖q − q'‖^a` on each box `[-R, R]^d`, with an integer `p ≥ 1` and
`a > d`, then `Z` has a modification continuous for every `ω`, which is almost surely the limit
of `Z` along the dyadic approximations of every point. -/
theorem exists_continuous_modification_N (hZ : ∀ q, AEMeasurable (Z q) P) {p : ℕ} (hp : 0 < p)
    {a : ℝ} (ha : (d : ℝ) < a) (hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundG Z P p a K R) :
    ∃ Y : (Fin d → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧
      (∀ q, (fun ω => Y q ω) =ᵐ[P] Z q) ∧
      (∀ᵐ ω ∂P, ∀ q, Tendsto (fun n => Z (rndD n q) ω) atTop (𝓝 (Y q ω))) := by
  obtain ⟨θ, hθ0, hθ1, hρ⟩ := exists_theta_N (d := d) hp ha
  exact exists_continuous_modification_N' hθ0 hθ1 hZ
    ((Nat.cast_nonneg d).trans ha.le) hρ hmom

end KolmN
end QuantumZipper
