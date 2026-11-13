/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.BMModulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Oscillation
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# RS P2: modulus of continuity of Brownian motion

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §2, node P2.

* `RS.bm_modulus`: for a Brownian motion `B`, almost surely, for every `N` there is `C` with
  `|B (t+s) − B t| ≤ C √(s log(1/s))` for `t ≤ N`, `s ∈ (0, 1/2]`. This is the form used in
  Kemppainen, *Schramm–Loewner Evolution* (2017), eq. (6.17), p. 111 (proof of Thm 5.2); it is
  the non-sharp half of Lévy's modulus of continuity (Revuz–Yor, *Continuous Martingales and
  Brownian Motion*, 3rd ed., Ch. I, Thm (2.7), p. 30).
* `RS.bm_holder`: the Hölder-`a` consequence, `a < 1/2`.

Proof route (non-sharp; our simplification of the textbook proof). For each level `n`, the
dyadic blocks `[k 2^{-n}, (k+2) 2^{-n}]`, `k ≤ N 2^n`, have oscillation at most
`a_n = √(8 (n+1) 2^{-n})` except with probability `≤ (N 2^n + 1) · 2 e^{-2(n+1)}`
(`bmOsc_tail`, Doob's exponential maximal inequality). This is summable, so by Borel–Cantelli
the bound holds for all large `n`. A pair `t, t+s` with `2^{-n-1} < s ≤ 2^{-n}` lies in one block
of level `n`, which gives `|B(t+s) − B t| ≤ 2 a_n ≤ 16 √(s log(1/s))`. Because the blocks
overlap, no chaining is needed (the maximal inequality replaces it). The finitely many small
levels are handled by the bound of `|B|` on `[0, N+1]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped ENNReal NNReal

namespace QuantumZipper
namespace RS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- An increment inside the window is bounded by the oscillation (continuous path). -/
theorem abs_sub_le_bmOsc {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (X · ω)) {t δ r : ℝ≥0}
    (hr : r ∈ Icc t (t + δ)) : |X r ω - X t ω| ≤ bmOsc X t δ ω := by
  rw [bmOsc_eq_iSup_subtype hc]
  have hbdd : BddAbove (Set.range fun x : Set.Icc t (t + δ) => |X x ω - X t ω|) := by
    obtain ⟨C, hC⟩ := ((isCompact_Icc (a := t) (b := t + δ)).image
      (f := fun r => |X r ω - X t ω|) (by fun_prop)).bddAbove
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC ⟨x, x.2, rfl⟩⟩
  exact le_ciSup (f := fun x : Set.Icc t (t + δ) => |X x ω - X t ω|) hbdd ⟨r, hr⟩

/-- The modulus bound for a pre-Brownian process with all paths continuous, fixed `N`. -/
theorem modulus_of_continuous {X : ℝ≥0 → Ω → ℝ} (hX : IsPreBrownianReal X P)
    (hXm : ∀ r, Measurable (X r)) (hXc : ∀ ω, Continuous (X · ω)) (N : ℕ) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ t : ℝ≥0, t ≤ N → ∀ s : ℝ≥0, 0 < s → s ≤ 1 / 2 →
      |X (t + s) ω - X t ω| ≤ C * √((s : ℝ) * log (1 / (s : ℝ))) := by
  set g : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) / 2 ^ n with hg
  set w : ℕ → ℝ≥0 := fun n => 2 / 2 ^ n with hw
  set a : ℕ → ℝ := fun n => √(8 * (n + 1) / 2 ^ n) with ha
  have ha0 : ∀ n, 0 < a n := fun n => Real.sqrt_pos.2 (by positivity)
  set A : ℕ → Set Ω := fun n =>
    ⋃ k ∈ Finset.range (N * 2 ^ n + 1), {ω | a n < bmOsc X (g n k) (w n) ω} with hA
  set f : ℕ → ℝ := fun n => 2 * (N + 1) * (2 * rexp (-2)) ^ n with hf
  have hr0 : 0 ≤ 2 * rexp (-2) := by positivity
  have hr1 : 2 * rexp (-2) < 1 := by
    have h3 : (3 : ℝ) < rexp 2 := by linarith [Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)]
    rw [Real.exp_neg]
    have hp := exp_pos 2
    rw [← div_eq_mul_inv, div_lt_one hp]
    linarith
  have hfs : Summable f := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hPA : ∀ n, P (A n) ≤ ENNReal.ofReal (f n) := by
    intro n
    have hwpos : (0 : ℝ≥0) < w n := by simp only [hw]; positivity
    have hone : ∀ k, P {ω | a n < bmOsc X (g n k) (w n) ω} ≤
        ENNReal.ofReal (2 * rexp (-(2 * ((n : ℝ) + 1)))) := by
      intro k
      refine (BMOsc.bmOsc_tail hX hXm hXc (g n k) (w n) hwpos (ha0 n)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hsq : a n ^ 2 = 8 * (n + 1) / 2 ^ n := Real.sq_sqrt (by positivity)
      have hwr : ((w n : ℝ≥0) : ℝ) = 2 / 2 ^ n := by simp [hw]
      rw [hsq, hwr]
      have : -(8 * ((n : ℝ) + 1) / 2 ^ n) / (2 * (2 / 2 ^ n)) = -(2 * ((n : ℝ) + 1)) := by
        field_simp; ring
      rw [this]
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hone k).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpow : (2 * rexp (-2)) ^ n = 2 ^ n * rexp (-(2 * (n : ℝ))) := by
      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    have he : rexp (-(2 * ((n : ℝ) + 1))) ≤ rexp (-(2 * (n : ℝ))) :=
      exp_le_exp.2 (by linarith)
    have hN : ((N * 2 ^ n + 1 : ℕ) : ℝ) ≤ (N + 1) * 2 ^ n := by
      push_cast
      have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith
    simp only [hf, hpow]
    have hE0 := exp_pos (-(2 * ((n : ℝ) + 1)))
    calc ((N * 2 ^ n + 1 : ℕ) : ℝ) * (2 * rexp (-(2 * ((n : ℝ) + 1))))
        ≤ ((N + 1) * 2 ^ n) * (2 * rexp (-(2 * (n : ℝ)))) := by gcongr
      _ = 2 * (N + 1) * (2 ^ n * rexp (-(2 * (n : ℝ)))) := by ring
  have hsum : (∑' n, P (A n)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n, f n)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hf0 hfs]
    exact ENNReal.tsum_le_tsum hPA
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hω
  obtain ⟨Mb, hMb⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (N : ℝ≥0) + 1)).exists_bound_of_continuousOn
    (hXc ω).continuousOn
  set m : ℝ := √((1 / 2 ^ n0) * log 2) with hm
  have hl2 : (1 / 2 : ℝ) < log 2 := by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hm0 : 0 < m := Real.sqrt_pos.2 (by positivity)
  refine ⟨max 16 (2 * Mb / m), fun t ht s hs0 hs1 => ?_⟩
  have hs0' : (0 : ℝ) < s := hs0
  have hs1' : (s : ℝ) ≤ 1 / 2 := by exact_mod_cast hs1
  set L := log (1 / (s : ℝ)) with hL
  have h2s : (2 : ℝ) ≤ 1 / s := by rw [le_div_iff₀ hs0']; linarith
  have hL2 : log 2 ≤ L := Real.log_le_log (by norm_num) h2s
  have hsL : 0 ≤ (s : ℝ) * L := mul_nonneg hs0'.le (by linarith)
  have hC16 : (16 : ℝ) ≤ max 16 (2 * Mb / m) := le_max_left _ _
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ 1 / s)
    (by norm_num : (1 : ℝ) < 2)
  by_cases hnn : n0 ≤ n
  · have hnot : ω ∉ A n := hn0 n hnn
    set k := ⌊(t : ℝ) * 2 ^ n⌋₊ with hk
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    have hk1 : (k : ℝ) ≤ t * 2 ^ n := Nat.floor_le (by positivity)
    have hk2 : (t : ℝ) * 2 ^ n < k + 1 := Nat.lt_floor_add_one _
    have hkN : k < N * 2 ^ n + 1 := by
      have : (k : ℝ) ≤ N * 2 ^ n := hk1.trans (by gcongr; exact_mod_cast ht)
      have : k ≤ N * 2 ^ n := by exact_mod_cast this
      omega
    have hosc : bmOsc X (g n k) (w n) ω ≤ a n := by
      by_contra hcon
      exact hnot (mem_biUnion (Finset.mem_range.2 hkN) (not_le.1 hcon))
    have hsn : (s : ℝ) * 2 ^ n ≤ 1 := by rw [le_div_iff₀ hs0'] at hn1; linarith
    have hgr : ((g n k : ℝ≥0) : ℝ) = k / 2 ^ n := by simp [hg]
    have hwr : ((w n : ℝ≥0) : ℝ) = 2 / 2 ^ n := by simp [hw]
    have hmem : ∀ r : ℝ≥0, (k : ℝ) ≤ r * 2 ^ n → (r : ℝ) * 2 ^ n ≤ k + 2 →
        r ∈ Icc (g n k) (g n k + w n) := by
      intro r h1 h2
      rw [mem_Icc, ← NNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_add, hgr, hwr,
        div_le_iff₀ hp, ← add_div, le_div_iff₀ hp]
      exact ⟨h1, h2⟩
    have hA1 := abs_sub_le_bmOsc (hXc ω) (hmem t hk1 (by linarith))
    have hA2 := abs_sub_le_bmOsc (hXc ω) (hmem (t + s) (by push_cast; nlinarith)
      (by push_cast; nlinarith))
    have hinc : |X (t + s) ω - X t ω| ≤ 2 * a n := by
      calc |X (t + s) ω - X t ω| = |(X (t + s) ω - X (g n k) ω) - (X t ω - X (g n k) ω)| := by
            ring_nf
        _ ≤ |X (t + s) ω - X (g n k) ω| + |X t ω - X (g n k) ω| := abs_sub _ _
        _ ≤ 2 * a n := by linarith
    have hnL : (n : ℝ) * log 2 ≤ L := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hn1
    have hinv : (1 : ℝ) / 2 ^ n ≤ 2 * s := by
      rw [div_le_iff₀ hp]
      have : 1 / (s : ℝ) < 2 ^ n * 2 := by rw [← pow_succ]; exact hn2
      rw [div_lt_iff₀ hs0'] at this
      linarith
    have hn4 : (n : ℝ) + 1 ≤ 4 * L := by nlinarith
    have hbound : 8 * ((n : ℝ) + 1) / 2 ^ n ≤ 64 * ((s : ℝ) * L) := by
      have h8 : 8 * ((n : ℝ) + 1) / 2 ^ n = 8 * ((n : ℝ) + 1) * (1 / 2 ^ n) := by ring
      rw [h8]
      have := one_div_pos.2 hp
      have hL0 : 0 ≤ L := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      calc 8 * ((n : ℝ) + 1) * (1 / 2 ^ n) ≤ 8 * (4 * L) * (1 / 2 ^ n) := by gcongr
        _ ≤ 8 * (4 * L) * (2 * s) := by gcongr
        _ = 64 * ((s : ℝ) * L) := by ring
    have hsq : a n ≤ 8 * √((s : ℝ) * L) := by
      calc a n ≤ √(64 * ((s : ℝ) * L)) := Real.sqrt_le_sqrt hbound
        _ = 8 * √((s : ℝ) * L) := by
          rw [Real.sqrt_mul (by norm_num), show (64 : ℝ) = 8 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
    calc |X (t + s) ω - X t ω| ≤ 2 * a n := hinc
      _ ≤ 16 * √((s : ℝ) * L) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hC16 (Real.sqrt_nonneg _)
  · have hn : n + 1 ≤ n0 := by omega
    have hsm : (1 : ℝ) / 2 ^ n0 ≤ s := by
      have h1 : (1 : ℝ) / s < 2 ^ n0 :=
        hn2.trans_le (pow_le_pow_right₀ (by norm_num) hn)
      rw [div_lt_iff₀ hs0'] at h1
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hmle : m ≤ √((s : ℝ) * L) :=
      Real.sqrt_le_sqrt (mul_le_mul hsm hL2 (by positivity) hs0'.le)
    have hb1 : |X (t + s) ω| ≤ Mb := by
      have := hMb (t + s) ⟨zero_le, by
        rw [← NNReal.coe_le_coe]; push_cast
        have : (t : ℝ) ≤ N := by exact_mod_cast ht
        linarith⟩
      rwa [Real.norm_eq_abs] at this
    have hb2 : |X t ω| ≤ Mb := by
      have := hMb t ⟨zero_le, by
        rw [← NNReal.coe_le_coe]; push_cast
        have : (t : ℝ) ≤ N := by exact_mod_cast ht
        linarith⟩
      rwa [Real.norm_eq_abs] at this
    have hC0 : 0 ≤ max 16 (2 * Mb / m) := le_trans (by norm_num) hC16
    calc |X (t + s) ω - X t ω| ≤ |X (t + s) ω| + |X t ω| := abs_sub _ _
      _ ≤ 2 * Mb / m * m := by rw [div_mul_cancel₀ _ hm0.ne']; linarith
      _ ≤ max 16 (2 * Mb / m) * m := mul_le_mul_of_nonneg_right (le_max_right _ _) hm0.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hmle hC0

/-- **RS P2: modulus of continuity of Brownian motion** (Kemppainen (6.17), p. 111; non-sharp
half of Lévy's modulus, Revuz–Yor Ch. I Thm (2.7), p. 30). -/
theorem bm_modulus {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ C : ℝ, ∀ t : ℝ≥0, t ≤ N → ∀ s : ℝ≥0, 0 < s → s ≤ 1 / 2 →
      |B (t + s) ω - B t ω| ≤ C * √((s : ℝ) * log (1 / (s : ℝ))) := by
  obtain ⟨Bt, hBtm, hBtc, hBtB⟩ := WedgeRes.exists_good_version hB
  have hBtmt : ∀ t, Measurable (Bt t) := fun t => hBtm.of_uncurry_left
  have hBtpre : IsPreBrownianReal Bt P :=
    hB.toIsPreBrownianReal.congr fun s => hBtB.mono fun ω h => (h s).symm
  have hall : ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ C : ℝ, ∀ t : ℝ≥0, t ≤ N → ∀ s : ℝ≥0, 0 < s → s ≤ 1 / 2 →
      |Bt (t + s) ω - Bt t ω| ≤ C * √((s : ℝ) * log (1 / (s : ℝ))) :=
    ae_all_iff.2 fun N => modulus_of_continuous hBtpre hBtmt hBtc N
  filter_upwards [hall, hBtB] with ω hω hEq N
  obtain ⟨C, hC⟩ := hω ⌈N⌉₊
  refine ⟨C, fun t ht s hs0 hs1 => ?_⟩
  have := hC t (ht.trans (Nat.le_ceil N)) s hs0 hs1
  rwa [hEq, hEq] at this

/-- **Hölder form of P2.** For `a < 1/2`: almost surely, for every `N` there is `C` with
`|B (t+s) − B t| ≤ C s^a` for `t ≤ N`, `s ∈ (0, 1/2]`. -/
theorem bm_holder {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {a : ℝ} (ha : a < 1 / 2) :
    ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ C : ℝ, ∀ t : ℝ≥0, t ≤ N → ∀ s : ℝ≥0, 0 < s → s ≤ 1 / 2 →
      |B (t + s) ω - B t ω| ≤ C * (s : ℝ) ^ a := by
  filter_upwards [bm_modulus hB] with ω hω N
  obtain ⟨C, hC⟩ := hω N
  set ε : ℝ := 1 - 2 * a with hε
  have hε0 : 0 < ε := by linarith
  refine ⟨|C| * √(1 / ε), fun t ht s hs0 hs1 => ?_⟩
  have hs0' : (0 : ℝ) < s := hs0
  have hlog : log (1 / (s : ℝ)) ≤ (1 / (s : ℝ)) ^ ε / ε :=
    Real.log_le_rpow_div (by positivity) hε0
  have hkey : (s : ℝ) * log (1 / (s : ℝ)) ≤ 1 / ε * ((s : ℝ) ^ a) ^ 2 := by
    have h1 : (s : ℝ) * ((1 / (s : ℝ)) ^ ε / ε) = 1 / ε * ((s : ℝ) ^ a) ^ 2 := by
      have e1 : ((s : ℝ) ^ a) ^ 2 = (s : ℝ) ^ (1 - ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs0'.le]
        congr 1
        simp only [hε]; push_cast; ring
      have e2 : (s : ℝ) ^ (1 - ε) = s / (s : ℝ) ^ ε := by
        rw [Real.rpow_sub hs0', Real.rpow_one]
      have e3 : (0 : ℝ) < (s : ℝ) ^ ε := Real.rpow_pos_of_pos hs0' ε
      rw [e1, e2, Real.div_rpow zero_le_one hs0'.le, Real.one_rpow]
      field_simp
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hlog hs0'.le
  have hsqrt : √((s : ℝ) * log (1 / (s : ℝ))) ≤ √(1 / ε) * (s : ℝ) ^ a := by
    calc √((s : ℝ) * log (1 / (s : ℝ))) ≤ √(1 / ε * ((s : ℝ) ^ a) ^ 2) := Real.sqrt_le_sqrt hkey
      _ = _ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  calc |B (t + s) ω - B t ω| ≤ C * √((s : ℝ) * log (1 / (s : ℝ))) := hC t ht s hs0 hs1
    _ ≤ |C| * √((s : ℝ) * log (1 / (s : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
    _ ≤ |C| * (√(1 / ε) * (s : ℝ) ^ a) := mul_le_mul_of_nonneg_left hsqrt (abs_nonneg C)
    _ = _ := by ring

end RS
end QuantumZipper
