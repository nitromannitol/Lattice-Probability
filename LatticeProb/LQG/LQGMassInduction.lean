import Mathlib
import LatticeProb.LQG.LQGMassStep

/-!
# Uniform positive moments of the mass of a cut-off against the approximate Liouville measure

Let `h` be a whole-plane Gaussian free field, `μ_n = lqgApprox γ h 2^{-n}` the approximate Liouville
measure at the dyadic scale `2^{-n}`, `f` a cut-off function supported in the disc `closedBall 0 (1/2)`
and `M_n = ∫ f dμ_n`. For every `1 ≤ p` with `p γ² < 4` the moments `E M_n^p` are bounded uniformly in
`n ≥ 1`, by a constant that depends only on `γ`, `f` and `p`.

The proof is an induction on the integer part of the exponent. The fixed-scale estimate gives `p = 1`, and
the one-step estimate (the mass splits into the masses of small dyadic squares) gives the exponent
`p ∈ (m, m + 1]` from the exponents `1, …, m`, after choosing the scale `2^{-k}` so that
`4^{p-1} · 256 · 2^{-k(ζ(p) - 2)} ≤ 1/2`, where `ζ(p) - 2 = (p - 1)(2 - p γ²/2) > 0`, and then a strong
induction on `n`.

* `LatticeProb.LQG.IsCutoffFn`: the hypotheses on the cut-off.
* `LatticeProb.LQG.MassMomentBound`: the bound `E M_n^p ≤ C` for all `n ≥ 1` and all models of the field.
* `LatticeProb.LQG.massMomentBound_step`: the exponent `p ∈ (m, m + 1]` from the exponents `1, …, m`.
* `LatticeProb.LQG.exists_massMomentBound`: the bound for all `1 ≤ p < 4/γ²`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling LatticeProb

/-- A cut-off function: measurable, at most `1`, at least `1` on `ball 0 (1/4)`, and zero outside
`closedBall 0 (1/2)`. -/
structure IsCutoffFn (f : ℂ → ℝ≥0∞) : Prop where
  measurable : Measurable f
  le_one : ∀ x, f x ≤ 1
  one_le_of_mem : ∀ x ∈ ball (0 : ℂ) (1 / 4), 1 ≤ f x
  eq_zero_of_not_mem : ∀ x ∉ closedBall (0 : ℂ) (1 / 2), f x = 0

/-- The moment bound `E (∫ f dμ_n)^p ≤ C`, for every `n ≥ 1` and every probability space carrying a
whole-plane Gaussian free field (all of them in the universe `u`). -/
def MassMomentBound.{u} (γ : ℝ) (f : ℂ → ℝ≥0∞) (p C : ℝ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    ∀ n : ℕ, 1 ≤ n →
      ∫⁻ ω, (lqgApproxMass γ (hcirc ω) f n) ^ p ∂P ≤ ENNReal.ofReal C

theorem MassMomentBound.mono.{u} {γ : ℝ} {f : ℂ → ℝ≥0∞} {p C C' : ℝ}
    (h : MassMomentBound.{u} γ f p C) (hCC : C ≤ C') : MassMomentBound.{u} γ f p C' :=
  fun Ω _ P _ hC hcirc hh n hn =>
    (h Ω P hC hcirc hh n hn).trans (ENNReal.ofReal_le_ofReal hCC)

/-- **First moment.** `E ∫ f dμ_n ≤ |B(0, 1/2)|` for all `n ≥ 1`. -/
theorem massMomentBound_one.{u} {f : ℂ → ℝ≥0∞} (hf : IsCutoffFn f) (γ : ℝ) :
    MassMomentBound.{u} γ f 1 (volume (closedBall (0 : ℂ) (1 / 2))).toReal := by
  intro Ω _ P _ hC hcirc hh n hn
  have h := LatticeProb.LQG.IsWholePlaneGFF.lintegral_rpow_lqgApproxMass_le hh γ (le_refl (1 : ℝ))
    hn hf.measurable hf.le_one hf.eq_zero_of_not_mem
  have h0 : (1 : ℝ) * (γ ^ 2 / 2) - 1 ^ 2 * γ ^ 2 / 2 = 0 := by ring
  rw [h0, Real.rpow_zero, ENNReal.ofReal_one, one_mul, sub_self, ENNReal.rpow_zero, one_mul] at h
  rw [ENNReal.ofReal_toReal measure_closedBall_lt_top.ne]
  exact h

/-- **Fixed scale, monotone form.** For `n ≤ k` the fixed-scale bound is at most its value at scale `k`. -/
theorem lintegral_rpow_lqgApproxMass_le_of_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {f : ℂ → ℝ≥0∞} (hf : IsCutoffFn f) {p : ℝ}
    (hp : 1 ≤ p) {n k : ℕ} (hn : 1 ≤ n) (hnk : n ≤ k) :
    ∫⁻ ω, (lqgApproxMass γ (hcirc ω) f n) ^ p ∂P ≤
      volume (closedBall (0 : ℂ) (1 / 2)) ^ (p - 1) *
        (ENNReal.ofReal (dyadicScale k ^ (p * (γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) *
          volume (closedBall (0 : ℂ) (1 / 2))) := by
  refine (LatticeProb.LQG.IsWholePlaneGFF.lintegral_rpow_lqgApproxMass_le hh γ hp hn hf.measurable
    hf.le_one hf.eq_zero_of_not_mem).trans ?_
  refine mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have he : p * (γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2 ≤ 0 := by
    nlinarith [mul_nonneg (sq_nonneg γ) (mul_nonneg (by linarith : (0 : ℝ) ≤ p)
      (by linarith : (0 : ℝ) ≤ p - 1))]
  exact Real.rpow_le_rpow_of_nonpos (dyadicScale_pos' k) (dyadicScale_le_of_le hnk) he

/-- `2^{-k e} → 0` for `e > 0`, so a scale `k ≥ 2` with `(2^{-k})^e < δ` exists. -/
theorem exists_dyadicScale_rpow_lt {e : ℝ} (he : 0 < e) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, 2 ≤ k ∧ dyadicScale k ^ e < δ := by
  have h0 : Tendsto dyadicScale atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 : Tendsto (fun k => dyadicScale k ^ e) atTop (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 e (Or.inr he.le)).tendsto.comp h0)
    rwa [Real.zero_rpow he.ne'] at this
  exact ((h1.eventually (gt_mem_nhds hδ)).and (eventually_ge_atTop 2)).exists.imp
    fun k hk => ⟨hk.2, hk.1⟩

theorem zeta_sub_two_pos {γ p : ℝ} (hp : 1 < p) (hpγ : p * γ ^ 2 < 4) :
    0 < p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2 - 2 := by
  have h : p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2 - 2 = (p - 1) * (4 - p * γ ^ 2) / 2 := by ring
  rw [h]
  have h1 : 0 < p - 1 := by linarith
  have h2 : 0 < 4 - p * γ ^ 2 := by linarith
  positivity

/-- **The inductive step.** Let `m ≥ 1`, `m < p ≤ m + 1`, `p γ² < 4`. If the integer exponents `1, …, m`
satisfy the uniform moment bound `K ≥ 1`, then the exponent `p` satisfies a uniform moment bound. -/
theorem massMomentBound_step.{u} {γ : ℝ} (hγ : γ ≠ 0) {f : ℂ → ℝ≥0∞} (hf : IsCutoffFn f) {m : ℕ}
    (hm1 : 1 ≤ m) {p : ℝ} (hpm : (m : ℝ) < p) (hpm1 : p ≤ m + 1) (hpγ : p * γ ^ 2 < 4) {K : ℝ}
    (hK : 1 ≤ K) (hU : ∀ a : ℕ, 1 ≤ a → a ≤ m → MassMomentBound.{u} γ f (a : ℝ) K) :
    ∃ C : ℝ, MassMomentBound.{u} γ f p C := by
  classical
  have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hp1 : 1 < p := by linarith
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hmγ : (m : ℝ) * γ ^ 2 ≤ 4 := by nlinarith
  set ζ : ℝ := p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2 with hζ
  have hζ2 : 0 < ζ - 2 := zeta_sub_two_pos hp1 hpγ
  -- the scale `2^{-k}`
  set A : ℝ := 4 ^ (p - 1) * 256 with hA
  have hApos : 0 < A := by positivity
  obtain ⟨k, hk2, hkδ⟩ := exists_dyadicScale_rpow_lt hζ2 (δ := 1 / (2 * A)) (by positivity)
  set R : ℝ := dyadicScale k with hR
  have hR0 : 0 < R := dyadicScale_pos' k
  have hR1 : R ≤ 1 := dyadicScale_le_one' k
  set r : ℝ := R * (1 / 4) with hrdef
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [hrdef]; linarith
  set N : ℕ := (squareIndex r).card with hNdef
  have hN : (N : ℝ) ≤ 256 / R ^ 2 := by
    have := card_squareIndex_le hr0 hr1
    have h2 : 16 / r ^ 2 = 256 / R ^ 2 := by rw [hrdef]; field_simp; ring
    rw [← h2]; exact this
  -- the contraction factor
  have hcontr : (4 : ℝ≥0∞) ^ (p - 1) * (N : ℝ≥0∞) * ENNReal.ofReal (R ^ ζ) ≤ 2⁻¹ := by
    have hreal : 4 ^ (p - 1) * (N : ℝ) * R ^ ζ ≤ 1 / 2 := by
      have hRζ : R ^ ζ = R ^ (ζ - 2) * R ^ 2 := by
        rw [← Real.rpow_two, ← Real.rpow_add hR0]; congr 1; ring
      have h4 : (0 : ℝ) < 4 ^ (p - 1) := by positivity
      calc 4 ^ (p - 1) * (N : ℝ) * R ^ ζ ≤ 4 ^ (p - 1) * (256 / R ^ 2) * R ^ ζ := by
            gcongr
        _ = A * R ^ (ζ - 2) := by rw [hRζ, hA]; field_simp
        _ ≤ A * (1 / (2 * A)) := by gcongr
        _ = 1 / 2 := by field_simp
    have h4 : ((4 : ℝ≥0∞) ^ (p - 1)) = ENNReal.ofReal (4 ^ (p - 1)) := by
      rw [← ENNReal.ofReal_rpow_of_pos (by norm_num)]; simp
    rw [h4, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (4 ^ (p - 1) * N * R ^ ζ) ≤ ENNReal.ofReal (1 / 2) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  -- the constant coming from the small-scale term
  set T : ℝ≥0∞ := 4 * ((N : ℝ≥0∞) ^ (m + 1) *
    (ENNReal.ofReal ((2 / r) ^ γ ^ 2) ^ ((m + 1) * (m + 1)) * ENNReal.ofReal K ^ (m + 1))) ^
      (p / ((m + 1 : ℕ) : ℝ)) with hT
  set Y : ℝ≥0∞ := (4 : ℝ≥0∞) ^ (p - 1) * T with hY
  have hYtop : Y ≠ ⊤ := by
    have hp0 : (0 : ℝ) ≤ p / ((m + 1 : ℕ) : ℝ) := by positivity
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)) ?_
    refine ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg hp0 ?_)
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) ?_
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  -- the constant coming from the small values of `n`
  set B : ℝ≥0∞ := volume (closedBall (0 : ℂ) (1 / 2)) with hB
  have hBtop : B ≠ ⊤ := measure_closedBall_lt_top.ne
  set Cb : ℝ≥0∞ := B ^ (p - 1) * (ENNReal.ofReal (R ^ (p * (γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) * B)
    with hCb
  have hCbtop : Cb ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hBtop)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop)
  set Cs : ℝ := max Cb.toReal (2 * Y.toReal) with hCs
  have hCb_le : Cb ≤ ENNReal.ofReal Cs := by
    rw [← ENNReal.ofReal_toReal hCbtop]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hY_le : (2 : ℝ≥0∞) * Y ≤ ENNReal.ofReal Cs := by
    have h2 : (2 : ℝ≥0∞) * Y = ENNReal.ofReal (2 * Y.toReal) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hYtop]; simp
    rw [h2]; exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hY_half : Y ≤ 2⁻¹ * ENNReal.ofReal Cs := by
    calc Y = 2⁻¹ * (2 * Y) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by simp), one_mul]
      _ ≤ 2⁻¹ * ENNReal.ofReal Cs := mul_le_mul' le_rfl hY_le
  refine ⟨Cs, ?_⟩
  -- strong induction on `n`
  have key : ∀ n : ℕ, 1 ≤ n → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
      ∫⁻ ω, (lqgApproxMass γ (hcirc ω) f n) ^ p ∂P ≤ ENNReal.ofReal Cs := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn Ω _ P _ hC hcirc hh
      by_cases hnk : n ≤ k
      · exact (lintegral_rpow_lqgApproxMass_le_of_le hh γ hf hp1.le hn hnk).trans hCb_le
      · have hkn : k < n := by omega
        have hrec : ∀ i : ℤ × ℤ, ∃ hC' : Ω → (ℂ → ℝ) → ℝ,
            IsWholePlaneGFF P hC' (recentredField hcirc k (dyadicSquareCentre r i)) :=
          fun i => isWholePlaneGFF_recentredField hh k _
        have hstep := LatticeProb.LQG.IsWholePlaneGFF.lintegral_rpow_lqgApproxMass_step hh hγ
          hf.measurable hf.le_one hf.one_le_of_mem hf.eq_zero_of_not_mem hk2 hkn hm1 hmγ hK
          (fun a ha1 ham i _ => by
            obtain ⟨hC', hh'⟩ := hrec i
            exact hU a ha1 ham Ω P hC' _ hh' (n - k) (by omega))
          hpm hpm1 (C := Cs)
          (fun i _ => by
            obtain ⟨hC', hh'⟩ := hrec i
            exact ih (n - k) (by omega) (by omega) Ω P hC' _ hh')
        refine hstep.trans ?_
        calc (4 : ℝ≥0∞) ^ (p - 1) * ((N : ℝ≥0∞) * (ENNReal.ofReal (R ^ ζ) * ENNReal.ofReal Cs) + T)
            = ((4 : ℝ≥0∞) ^ (p - 1) * (N : ℝ≥0∞) * ENNReal.ofReal (R ^ ζ)) * ENNReal.ofReal Cs + Y := by
              rw [hY]; ring
          _ ≤ 2⁻¹ * ENNReal.ofReal Cs + 2⁻¹ * ENNReal.ofReal Cs :=
              add_le_add (mul_le_mul' hcontr le_rfl) hY_half
          _ = ENNReal.ofReal Cs := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  intro Ω _ P _ hC hcirc hh n hn
  exact key n hn Ω P hC hcirc hh

/-- **Uniform positive moments of the mass.** For `γ ≠ 0`, a cut-off `f` and `1 ≤ p` with `p γ² < 4`,
`E (∫ f dμ_n)^p ≤ C` for all `n ≥ 1` and all models of the whole-plane Gaussian free field, with `C`
depending only on `γ`, `f` and `p`. -/
theorem exists_massMomentBound.{u} {γ : ℝ} (hγ : γ ≠ 0) {f : ℂ → ℝ≥0∞} (hf : IsCutoffFn f)
    {p : ℝ} (hp : 1 ≤ p) (hpγ : p * γ ^ 2 < 4) : ∃ C : ℝ, MassMomentBound.{u} γ f p C := by
  have main : ∀ m : ℕ, ∀ q : ℝ, (m : ℝ) < q → q ≤ m + 1 → 1 ≤ q → q * γ ^ 2 < 4 →
      ∃ C : ℝ, MassMomentBound.{u} γ f q C := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro q hqm hqm1 hq1 hqγ
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have hq : q = 1 := by
          have := hqm1
          simp only [Nat.cast_zero, zero_add] at this
          linarith
        subst hq
        exact ⟨_, massMomentBound_one hf γ⟩
      · have hU : ∀ a : ℕ, 1 ≤ a → a ≤ m → ∃ C : ℝ, MassMomentBound.{u} γ f (a : ℝ) C := by
          intro a ha1 ham
          obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
          have hbm : ((b + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast ham
          refine ih b (by omega) ((b + 1 : ℕ) : ℝ) ?_ ?_ ?_ ?_
          · push_cast; linarith
          · push_cast; exact le_rfl
          · exact_mod_cast ha1
          · nlinarith [sq_nonneg γ]
        choose! C hC using hU
        set K : ℝ := 1 + ∑ a ∈ Finset.Icc 1 m, |C a| with hKdef
        have hK : 1 ≤ K := by
          have : 0 ≤ ∑ a ∈ Finset.Icc 1 m, |C a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
          linarith
        refine massMomentBound_step hγ hf hm hqm hqm1 hqγ hK (fun a ha1 ham => ?_)
        refine (hC a ha1 ham).mono ?_
        calc C a ≤ |C a| := le_abs_self _
          _ ≤ ∑ a ∈ Finset.Icc 1 m, |C a| :=
              Finset.single_le_sum (f := fun a => |C a|) (fun _ _ => abs_nonneg _)
                (Finset.mem_Icc.2 ⟨ha1, ham⟩)
          _ ≤ K := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌈p⌉₊ = m + 1 :=
    ⟨⌈p⌉₊ - 1, by have := Nat.ceil_pos.2 (by linarith : 0 < p); omega⟩
  refine main m p ?_ ?_ hp hpγ
  · have := Nat.ceil_lt_add_one (by linarith : 0 ≤ p)
    rw [hm] at this; push_cast at this; linarith
  · have := Nat.le_ceil p
    rw [hm] at this; push_cast at this; exact this

end LatticeProb.LQG
