/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.TraceInterp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.KoebeLoewnerTime

/-!
# EXT-RS node TR2 (deterministic part): from the dyadic grid to all points of the axis

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §3, node TR2.
Source: A. Kemppainen, *Schramm–Loewner Evolution*, SpringerBriefs Math. Phys. 24 (2017),
proof of Thm 5.2, (6.16)–(6.18), pp. 111–112.

`tr2_interp`: there is a universal `A ≥ 1` such that, for a continuous driver `W` with
`W 0 = 0`, if the grid bound (6.16) `‖(f̂_{k/4ⁿ})'(i2^{−n})‖ ≤ C_g 2^{n(1−θ)}` holds for all
dyadic times `k/4ⁿ ≤ N`, and `W` is `a`-Hölder on `[0,N]` at scales `≤ 1/2` (the Hölder form
of (6.17), `a ≤ 1/2`), then for every `t ∈ [0,N]` and `y ∈ (0,1]`

  `‖(f̂_t)'(iy)‖ ≤ 2A³ C_g (1 + C_h²)^A y^{θ − 1 − (2 − 4a)A}`.

Proof exactly as Kemppainen (6.18): `2^{−n} ≤ y ≤ 2^{−n+1}` (`n ≥ 1`),
`t₀ = ⌊t4ⁿ⌋/4ⁿ`, `s = t − t₀ < 4^{−n} ≤ y²`; KD(b) (`kd_time_step`, Lemma 6.7) moves from time
`t` to `t₀` (in centred coordinates the point becomes `(W_t − W_{t₀}) + iy`), KD(a)
(`kd_distortion`, Lemma 6.6) moves horizontally back to `iy` at the price
`(1 + |W_t − W_{t₀}|²/y²)^A` and vertically from `iy` to `i2^{−n}`, and (6.16) finishes.
Kemppainen's subpower factor `ψ(1/y)` comes from `√(s log(1/s))`; with the Hölder form of the
Brownian modulus it becomes the polynomial loss `y^{−(2−4a)A}`, which is absorbed into a
smaller exponent by choosing `a` close to `1/2` (done in `TraceMain`).
-/

noncomputable section

open Set Metric Filter Complex
open scoped Topology

namespace QuantumZipper.RS

open UnzipInvariance

/-- The dyadic level of `y ∈ (0,1]`: `n ≥ 1` with `2^{−n} ≤ y ≤ 2·2^{−n}`. -/
theorem exists_dyadic_level {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ∃ n : ℕ, 1 ≤ n ∧ ((2 : ℝ) ^ n)⁻¹ ≤ y ∧ y ≤ 2 * ((2 : ℝ) ^ n)⁻¹ := by
  have hex : ∃ m : ℕ, ((2 : ℝ) ^ (m + 1))⁻¹ ≤ y := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / y) (by norm_num : (1 : ℝ) < 2)
    refine ⟨m, ?_⟩
    have h2 : (2 : ℝ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [inv_le_comm₀ (by positivity) hy]
    rw [one_div] at hm
    linarith
  refine ⟨Nat.find hex + 1, by omega, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; norm_num; exact hy1
  · have hnot := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push_neg at hnot
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hnot
    have e : ∀ m : ℕ, ((2 : ℝ) ^ m)⁻¹ = 2 * ((2 : ℝ) ^ (m + 1))⁻¹ := fun m => by
      rw [pow_succ]; field_simp
    rw [e] at hnot
    exact hnot.le

/-- `(2ⁿ)^{1−θ} ≤ 2 y^{θ−1}` when `y ≤ 2·2^{−n}`, `θ ≤ 1`. -/
theorem two_rpow_le_of_level {y θ : ℝ} {n : ℕ} (hy : 0 < y) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hyn : y ≤ 2 * ((2 : ℝ) ^ n)⁻¹) :
    (2 : ℝ) ^ ((n : ℝ) * (1 - θ)) ≤ 2 * y ^ (θ - 1) := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hle : (2 : ℝ) ^ n ≤ 2 / y := by
    rw [le_div_iff₀ hy]
    have := mul_le_mul_of_nonneg_left hyn h2n.le
    rwa [mul_left_comm, mul_inv_cancel₀ h2n.ne', mul_one] at this
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  calc ((2 : ℝ) ^ n) ^ (1 - θ) ≤ (2 / y) ^ (1 - θ) :=
        Real.rpow_le_rpow h2n.le hle (by linarith)
    _ = 2 ^ (1 - θ) * y ^ (θ - 1) := by
        rw [Real.div_rpow (by norm_num) hy.le, div_eq_mul_inv, ← Real.rpow_neg hy.le, neg_sub]
    _ ≤ 2 * y ^ (θ - 1) := by
        gcongr
        calc (2 : ℝ) ^ (1 - θ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2

/-- The horizontal Koebe factor: if `|x| ≤ C_h y^{2a}`, `0 < y ≤ 1`, `a ≤ 1/2`, `A ≥ 0`, then
`(1 + (x/y)²)^A ≤ (1 + C_h²)^A y^{(4a−2)A}`. -/
theorem horiz_factor_le {x y a Ch A : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (ha2 : a ≤ 1 / 2)
    (hA : 0 ≤ A) (hx : |x| ≤ Ch * y ^ (2 * a)) :
    (1 + (x / y) ^ 2) ^ A ≤ (1 + Ch ^ 2) ^ A * y ^ ((4 * a - 2) * A) := by
  have hq : 1 ≤ y ^ (4 * a - 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by linarith)
  have hx2 : x ^ 2 ≤ Ch ^ 2 * y ^ (4 * a) := by
    have h0 : 0 ≤ Ch * y ^ (2 * a) := (abs_nonneg x).trans hx
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at this
    refine this.trans (le_of_eq ?_)
    have e : (y ^ (2 * a)) ^ 2 = y ^ (4 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; congr 1; push_cast; ring
    rw [mul_pow, e]
  have hxi : (x / y) ^ 2 ≤ Ch ^ 2 * y ^ (4 * a - 2) := by
    rw [div_pow, div_le_iff₀ (by positivity), mul_assoc, ← Real.rpow_natCast y 2,
      ← Real.rpow_add hy]
    norm_num
    exact hx2
  have hbase : 1 + (x / y) ^ 2 ≤ (1 + Ch ^ 2) * y ^ (4 * a - 2) := by nlinarith
  calc (1 + (x / y) ^ 2) ^ A ≤ ((1 + Ch ^ 2) * y ^ (4 * a - 2)) ^ A :=
        Real.rpow_le_rpow (by positivity) hbase hA
    _ = (1 + Ch ^ 2) ^ A * y ^ ((4 * a - 2) * A) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hy.le]

/-- **TR2 (deterministic interpolation; Kemppainen (6.18), p. 112).** -/
theorem tr2_interp : ∃ A : ℝ, 1 ≤ A ∧ ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 →
    ∀ (N : ℕ) (θ a Cg Ch : ℝ), 0 < θ → θ ≤ 1 → 0 < a → a ≤ 1 / 2 → 0 ≤ Cg → 0 ≤ Ch →
    (∀ n k : ℕ, (k : ℝ) / 4 ^ n ≤ N →
      ‖deriv (fwdMapInv W ((k : ℝ) / 4 ^ n)) (Complex.I / 2 ^ n)‖ ≤
        Cg * 2 ^ ((n : ℝ) * (1 - θ))) →
    (∀ t₀ s : ℝ, 0 ≤ t₀ → t₀ ≤ N → 0 < s → s ≤ 1 / 2 → |W (t₀ + s) - W t₀| ≤ Ch * s ^ a) →
    ∀ t ∈ Icc (0 : ℝ) N, ∀ y ∈ Ioc (0 : ℝ) 1,
      ‖deriv (fwdMapInv W t) ((y : ℂ) * Complex.I)‖ ≤
        2 * A ^ 3 * Cg * (1 + Ch ^ 2) ^ A * y ^ (θ - 1 - (2 - 4 * a) * A) := by
  obtain ⟨CT, hCT1, hCT⟩ := kd_time_step
  obtain ⟨CA, hCA1, hCA⟩ := kd_distortion
  refine ⟨max CT CA, le_max_of_le_left hCT1, ?_⟩
  intro W hW hW0 N θ a Cg Ch hθ hθ1 ha ha2 hCg hCh hgrid hhol t ht y hy
  set A := max CT CA with hAdef
  have hA1 : 1 ≤ A := le_max_of_le_left hCT1
  have hA0 : 0 ≤ A := by linarith
  have hy0 : 0 < y := hy.1
  obtain ⟨n, hn1, hyn, hyn2⟩ := exists_dyadic_level hy0 hy.2
  set y0 : ℝ := ((2 : ℝ) ^ n)⁻¹ with hy0def
  have hy0pos : 0 < y0 := by positivity
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have h42 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  set k : ℕ := ⌊t * 4 ^ n⌋₊ with hk
  set t0 : ℝ := (k : ℝ) / 4 ^ n with ht0def
  have ht0le : t0 ≤ t := by
    rw [ht0def, div_le_iff₀ h4]; exact Nat.floor_le (by nlinarith [ht.1])
  have ht0lt : t < t0 + (4 ^ n : ℝ)⁻¹ := by
    have := Nat.lt_floor_add_one (t * 4 ^ n)
    rw [← hk] at this
    rw [ht0def, div_add' _ _ _ h4.ne', lt_div_iff₀ h4, inv_mul_cancel₀ h4.ne']
    linarith
  have ht00 : 0 ≤ t0 := by positivity
  have ht0N : t0 ≤ N := ht0le.trans ht.2
  set s : ℝ := t - t0 with hsdef
  have hs0 : 0 ≤ s := by linarith
  have hsy0 : s < y0 ^ 2 := by
    have : (4 ^ n : ℝ)⁻¹ = y0 ^ 2 := by rw [hy0def, inv_pow, h42]
    linarith
  have hsy : s ≤ y ^ 2 := hsy0.le.trans (pow_le_pow_left₀ hy0pos.le hyn 2)
  have hy0half : y0 ≤ 1 / 2 := by
    rw [hy0def]
    have : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn1
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hs12 : s ≤ 1 / 2 := by nlinarith
  have hts : t0 + s = t := by rw [hsdef]; ring
  set x : ℝ := W t - W t0 with hxdef
  have hx : |x| ≤ Ch * y ^ (2 * a) := by
    have hpos : 0 ≤ Ch * y ^ (2 * a) := by positivity
    rcases hs0.eq_or_lt with h | h
    · have : t = t0 := by linarith
      rw [hxdef, this, sub_self, abs_zero]; exact hpos
    · have h1 := hhol t0 s ht00 ht0N h hs12
      rw [hts] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCh)
      calc s ^ a ≤ (y ^ 2) ^ a := Real.rpow_le_rpow hs0 hsy ha.le
        _ = y ^ (2 * a) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
  -- KD(b): from time `t` to time `t₀`
  have hwim : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  obtain ⟨hT1, -, -⟩ := hCT W hW hW0 t0 s ht00 hs0 ((x : ℂ) + (y : ℂ) * I)
    (by rw [hwim]; exact hy0) (by rw [hwim]; exact hsy)
  have e1 : ((x : ℂ) + (y : ℂ) * I) - ((W (t0 + s) - W t0 : ℝ) : ℂ) = (y : ℂ) * I := by
    rw [hts, hxdef]; push_cast; ring
  rw [e1, hts] at hT1
  -- KD(a): horizontal move and vertical rescaling at time `t₀`
  have hd := differentiableOn_fwdMapInv hW hW0 ht00
  have hinj := injOn_fwdMapInv hW hW0 ht00
  obtain ⟨-, hhor, -⟩ := hCA (fwdMapInv W t0) hd hinj y hy0 (x / y)
  have e2 : (y : ℂ) * (((x / y : ℝ) : ℂ) + I) = (x : ℂ) + (y : ℂ) * I := by
    have : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    push_cast; field_simp
  rw [e2] at hhor
  obtain ⟨hvert, -, -⟩ := hCA (fwdMapInv W t0) hd hinj y0 hy0pos 0
  have hsv : y / y0 ∈ Icc (1 / 2 : ℝ) 2 := by
    constructor
    · rw [le_div_iff₀ hy0pos]; linarith
    · rw [div_le_iff₀ hy0pos]; linarith
  have hv := (hvert (y / y0) hsv).1
  have e3 : (((y / y0 * y0 : ℝ)) : ℂ) * I = (y : ℂ) * I := by
    rw [div_mul_cancel₀ y hy0pos.ne']
  have e4 : (y0 : ℂ) * I = I / 2 ^ n := by
    rw [hy0def]; push_cast; field_simp
  rw [e3, e4] at hv
  have hg := hgrid n k ht0N
  -- assembling
  have hhor' : ‖deriv (fwdMapInv W t0) ((x : ℂ) + (y : ℂ) * I)‖ ≤
      A * (1 + (x / y) ^ 2) ^ A * ‖deriv (fwdMapInv W t0) ((y : ℂ) * I)‖ := by
    refine hhor.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow_of_exponent_le
      (le_add_of_nonneg_right (sq_nonneg _)) (le_max_right _ _)) (by positivity) hA0
  have hT1' := hT1.trans (mul_le_mul_of_nonneg_right (le_max_left CT CA) (norm_nonneg _))
  have hv' := hv.trans (mul_le_mul_of_nonneg_right (le_max_right CT CA) (norm_nonneg _))
  have hfac := horiz_factor_le hy0 hy.2 ha2 hA0 hx
  have hpow := two_rpow_le_of_level (n := n) hy0 hθ.le hθ1 hyn2
  have hF0 : 0 ≤ (1 + (x / y) ^ 2) ^ A := by positivity
  set D0 := ‖deriv (fwdMapInv W t0) (I / 2 ^ n)‖
  set D1 := ‖deriv (fwdMapInv W t0) ((y : ℂ) * I)‖
  set D2 := ‖deriv (fwdMapInv W t0) ((x : ℂ) + (y : ℂ) * I)‖
  have hexp : y ^ (θ - 1) * y ^ ((4 * a - 2) * A) = y ^ (θ - 1 - (2 - 4 * a) * A) := by
    rw [← Real.rpow_add hy0]; congr 1; ring
  calc ‖deriv (fwdMapInv W t) ((y : ℂ) * I)‖ ≤ A * D2 := hT1'
    _ ≤ A * (A * (1 + (x / y) ^ 2) ^ A * D1) := by gcongr
    _ ≤ A * (A * (1 + (x / y) ^ 2) ^ A * (A * D0)) := by gcongr
    _ ≤ A * (A * ((1 + Ch ^ 2) ^ A * y ^ ((4 * a - 2) * A)) *
          (A * (Cg * (2 * y ^ (θ - 1))))) := by
        gcongr
        exact hg.trans (mul_le_mul_of_nonneg_left hpow hCg)
    _ = 2 * A ^ 3 * Cg * (1 + Ch ^ 2) ^ A * (y ^ (θ - 1) * y ^ ((4 * a - 2) * A)) := by ring
    _ = _ := by rw [hexp]

end QuantumZipper.RS
