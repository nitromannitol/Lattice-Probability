/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32G5 at commit fdb5cad; only the module paths of local imports are changed.
   Changed: docstring wording of the module. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32G4

/-!
# `L32StartPhiHPC` at `μIn`, unconditional (P2-DZZ32G)

Copy of `l32StartPhiHPC_of_geom` (S3P32F7, P2-DZZ32F) using `start_bound_explicitS` (S3P32G4,
with the proved cover `p32StartGeomS`).


DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1149–1153): `t = 2^{-q}` with `2^q ≤ δ^{-ι/2} < 2^{q+1}`
(DZZ: `t = 2^{-⌈log₂(δ^{-ι/2} λ)⌉}`; the factor `λ` is not needed, DV-P32F1), `ι = C_Mc/2`.
The bound `9K · 16 M t² e^E` of `start_bound_explicit` is `≤ δ^{ι/4}` for small `δ`
(DZZ: `(6/t + 6) t^{1.9} ≤ δ^{ι/10}`), and `M = 8/t + O(log δ⁻¹) ≤ δ^{-ι} λ`.

* **`l32StartPhiHPC_dzzMuIn`**: `L32StartPhiHPC P γ W μIn (rP32 γ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

universe u

set_option maxHeartbeats 4000000 in
/-- **DZZ (eq-B-good-Psi) + union at `μIn`** (D102 P-4bW, second input), from the cover. -/
theorem l32StartPhiHPC_dzzMuIn {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    L32StartPhiHPC P γ W (dzzMuIn γ W) (rP32 γ) := by
  have := hW.isProbabilityMeasure
  obtain ⟨α, G, hG, δ₀, hδ₀, hup⟩ := l32TildeMUpper_wickQArea (P := P) hW hγ hγ2
  obtain ⟨c1, hc1, δ3, hδ3, h1⟩ := dzz_lemma31 hW hγ hγ2
  obtain ⟨c2, hc2, δ4, hδ4, h2⟩ := hG
  set C := dzzCmc γ with hCdef
  have hC : 0 < C := by have := l31theta_pos hγ hγ2; rw [hCdef]; unfold dzzCmc; linarith
  set ι := dzzCMc γ / 2 with hιdef
  have hι : 0 < ι := by have := dzzCMc_pos γ; rw [hιdef]; linarith
  set m := min (min c1 c2) (ι / 4) with hmdef
  have hm : 0 < m := lt_min (lt_min hc1 hc2) (by positivity)
  set A : ℝ := 576 * C * (40 + 24 * C) with hAdef
  have hA : 0 < A := by rw [hAdef]; positivity
  obtain ⟨U, hU⟩ := eventually_atTop.1
    ((ev_pow_le (show 0 < ι / 2 by positivity) 15 (show 0 < 10 by norm_num)).and
    ((ev_pow_le (show (0 : ℝ) < 1 / 4 by norm_num) (48 * C) (show 10 < 14 by norm_num)).and
    ((ev_pow_le (show (0 : ℝ) < 1 / 4 by norm_num) 64 (show 0 < 14 by norm_num)).and
    (ev_pow_le (show 0 < ι / 4 by positivity) (|Real.log A| + 21 + 20 * |α| * γ)
      (show 6 < 10 by norm_num)))))
  set U'' := max U 1 with hU''
  refine ⟨m / 2, by positivity, min (min (min δ₀ δ3) δ4)
    (min (Real.exp (-(U'' ^ 10))) ((1 / 3) ^ (2 / m))), by positivity, ?_⟩
  rintro δ ⟨hδ0, hδ⟩ x hx
  have hδa : δ < δ₀ := hδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδb : δ < δ3 := hδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδc : δ < δ4 := hδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδd : δ < Real.exp (-(U'' ^ 10)) := hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδe : δ < (1 / 3) ^ (2 / m) := hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hU0 : (0 : ℝ) ≤ U'' := by positivity
  have hL : U'' ^ 10 < L := by
    have := Real.log_lt_log hδ0 hδd
    rw [Real.log_exp] at this; linarith
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
  have hδ1 : δ < 1 := (Real.log_neg_iff hδ0).1 (by linarith)
  set u := L ^ ((1 : ℝ) / 10) with hudef
  have hu10 : u ^ 10 = L := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hu7 : L ^ (0.7 : ℝ) = u ^ 7 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have huU : U'' ≤ u := by
    have h1 : (U'' ^ 10) ^ ((1 : ℝ) / 10) = U'' := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0]; norm_num
    rw [← h1]; exact Real.rpow_le_rpow (by positivity) hL.le (by norm_num)
  obtain ⟨F1, F2, F3, F4⟩ := hU u ((le_max_left _ _).trans huU)
  simp only [pow_zero, mul_one] at F1 F3
  have hu1 : 1 ≤ u := (le_max_right _ _).trans huU
  have hL1 : 1 ≤ L := by rw [← hu10]; exact one_le_pow₀ hu1
  have hsqrt : Real.sqrt L = u ^ 5 := by
    rw [← hu10, show u ^ 10 = (u ^ 5) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlogL : Real.log L ≤ 10 * u := by
    have := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 10 by norm_num)
    rw [← hudef] at this
    calc Real.log L ≤ u / (1 / 10) := this
      _ = 10 * u := by ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hδL : ∀ y : ℝ, δ ^ y = Real.exp (-(L * y)) := fun y => by
    rw [Real.rpow_def_of_pos hδ0, hlogδ]; ring_nf
  -- `X = δ^{-ι/2}`, `q`
  set X : ℝ := δ ^ (-(ι / 2)) with hXdef
  have hXe : X = Real.exp (ι / 2 * L) := by rw [hXdef, hδL]; ring_nf
  have hX16 : 16 ≤ X := by
    rw [hXe]; have := Real.add_one_le_exp (ι / 2 * L); rw [← hu10] at this ⊢; linarith
  have hX0 : 0 < X := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q, q = Nat.log 2 ⌊X⌋₊ := ⟨_, rfl⟩
  have hfl : ⌊X⌋₊ ≠ 0 := by
    have := Nat.floor_pos.2 (show (1 : ℝ) ≤ X by linarith); omega
  have hq1 : (2 : ℝ) ^ q ≤ X := by
    have h1 := Nat.pow_log_le_self 2 hfl
    rw [← hqdef] at h1
    have h2 : ((2 ^ q : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2; exact h2.trans (Nat.floor_le hX0.le)
  have hq2 : X < (2 : ℝ) ^ (q + 1) := by
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊X⌋₊
    rw [← hqdef] at h1
    have h2 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (q + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2; linarith [Nat.lt_floor_add_one X]
  have hq3 : 3 ≤ q := by
    by_contra hc; push Not at hc
    have : (2 : ℝ) ^ (q + 1) ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; linarith
  set t : ℝ := (2 : ℝ)⁻¹ ^ q with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have htq : t * 2 ^ q = 1 := pow_inv_mul_pow q
  have htX : t * X < 2 := by
    have : (2 : ℝ) ^ (q + 1) = 2 * 2 ^ q := by rw [pow_succ]; ring
    nlinarith
  -- `j`
  set k := kL37 γ δ with hkdef
  have hkL : (k : ℝ) ≤ 4 * C * L := by
    have h1 : k ≤ ⌊4 * C * L⌋₊ := Nat.log_le_self 2 _
    exact (Nat.cast_le.2 h1).trans (Nat.floor_le (by positivity))
  set r := rP32 γ δ with hrdef
  have hr0 : 0 < r := (isClipDepth_rP32 γ δ ⟨hδ0, hδ1⟩).1
  obtain ⟨j, hjdef⟩ : ∃ j, j = ⌈Real.logb 2 r⁻¹⌉₊ := ⟨_, rfl⟩
  have hlogr : Real.logb 2 r⁻¹ = 3 + k + C * L / Real.log 2 := by
    have e : r⁻¹ = 2 ^ 3 * 2 ^ k * Real.exp (C * L) := by
      rw [hrdef, rP32, hδL, ← hCdef]
      rw [show (2 : ℝ)⁻¹ ^ k = (2 ^ k)⁻¹ by rw [inv_pow], Real.exp_neg]
      field_simp; norm_num
    rw [e, Real.logb, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_exp]
    field_simp; push_cast; ring
  have hj : 1 ≤ 2 ^ j * r := by
    have h1 : r⁻¹ ≤ (2 : ℝ) ^ j := by
      rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) (inv_pos.2 hr0),
        ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hjdef ▸ Nat.le_ceil _)
    rw [← inv_mul_cancel₀ hr0.ne']
    exact mul_le_mul_of_nonneg_right h1 hr0.le
  have hjL : (j : ℝ) ≤ 4 + 6 * C * L := by
    have h1 : (j : ℝ) < Real.logb 2 r⁻¹ + 1 := by
      rw [hjdef]; exact Nat.ceil_lt_add_one (by rw [hlogr]; positivity)
    have h2 : C * L / Real.log 2 ≤ 2 * C * L := by
      rw [div_le_iff₀ hlog2]
      have := mul_le_mul_of_nonneg_left hlog2'.le (mul_pos hC hL0).le
      linarith
    rw [hlogr] at h1; linarith
  -- `λ`
  set lam := lamP32 δ with hlamdef
  have hlam : lam = Real.exp (u ^ 7) := by rw [hlamdef, lamP32, ← hLdef, hu7]
  have hexp7 : u ^ 14 / 2 ≤ Real.exp (u ^ 7) := by
    have := Real.pow_div_factorial_le_exp (u ^ 7) (by positivity) 2
    calc u ^ 14 / 2 = (u ^ 7) ^ 2 / (Nat.factorial 2) := by
          rw [Nat.factorial_two]; push_cast; ring
      _ ≤ _ := this
  have hlamJ : 64 + 48 * C * L ≤ lam := by rw [hlam, ← hu10]; nlinarith
  have hlam1 : 1 ≤ lam := by nlinarith [mul_pos hC hL0]
  -- `hM`
  have hX2 : δ ^ (-(dzzCMc γ / 2)) = X ^ 2 := by
    rw [hXe, hδL, ← Real.exp_nat_mul, ← hιdef]; congr 1; push_cast; ring
  have hM : (8 * 2 ^ q + 4 * j + 16 : ℝ) ≤ δ ^ (-(dzzCMc γ / 2)) * lam := by
    rw [hX2]
    have a1 : 8 * X ≤ X ^ 2 / 2 := by nlinarith
    have a2 : X ^ 2 / 2 ≤ X ^ 2 * lam / 2 := by nlinarith
    have a3 : lam / 2 ≤ X ^ 2 * lam / 2 := by nlinarith
    nlinarith
  have core := start_bound_explicitS hW hγ hγ2 α G hup ⟨hδ0, hδa⟩ hδ1 hq3 hj hx hM
  -- the last term
  set E := 2 * α * γ * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹) with hEdef
  have hE : E ≤ 20 * |α| * γ * u ^ 6 := by
    have t1 : α * Real.log L ≤ |α| * (10 * u) :=
      (mul_le_mul_of_nonneg_right (le_abs_self α) hlogL0).trans
        (mul_le_mul_of_nonneg_left hlogL (abs_nonneg α))
    have e : E = 2 * γ * u ^ 5 * (α * Real.log L) := by rw [hEdef, ← hLdef, hsqrt]; ring
    rw [e]
    calc 2 * γ * u ^ 5 * (α * Real.log L) ≤ 2 * γ * u ^ 5 * (|α| * (10 * u)) :=
          mul_le_mul_of_nonneg_left t1 (by positivity)
      _ = 20 * |α| * γ * u ^ 6 := by ring
  set K := ⌊C * Real.logb 2 δ⁻¹⌋₊ with hKdef
  have hK : (K : ℝ) ≤ 2 * C * L := by
    have h1 : (K : ℝ) ≤ C * Real.logb 2 δ⁻¹ := Nat.floor_le (by rw [Real.logb, ← hLdef]; positivity)
    rw [Real.logb, ← hLdef] at h1
    have h2 : C * (L / Real.log 2) ≤ 2 * C * L := by
      rw [mul_div_assoc', div_le_iff₀ hlog2]
      have := mul_le_mul_of_nonneg_left hlog2'.le (mul_pos hC hL0).le
      linarith
    linarith
  have hlast : 9 * (K : ℝ) * (16 * (8 * 2 ^ q + 4 * j + 16) * t ^ 2 * Real.exp E) ≤
      δ ^ (ι / 4) := by
    have hMt : (8 * 2 ^ q + 4 * j + 16 : ℝ) * t ^ 2 ≤ (40 + 24 * C * L) * t := by
      have e : (8 * 2 ^ q + 4 * j + 16 : ℝ) * t ^ 2 = 8 * t * (t * 2 ^ q) + (4 * j + 16) * t ^ 2 := by
        ring
      rw [e, htq]
      have : (4 * j + 16 : ℝ) * t ^ 2 ≤ (4 * j + 16) * t := by
        have : t ^ 2 ≤ t := by nlinarith
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have h4j : (4 * j + 16 : ℝ) * t ≤ (32 + 24 * C * L) * t :=
        mul_le_mul_of_nonneg_right (by linarith) ht0.le
      linarith
    have hpoly : 9 * (K : ℝ) * 16 * (40 + 24 * C * L) * 2 ≤ A * L ^ 2 := by
      have hCL0 : 0 ≤ 2 * C * L := by positivity
      have b2 : 40 + 24 * C * L ≤ (40 + 24 * C) * L := by
        have : (40 : ℝ) ≤ 40 * L := by linarith
        linarith [show (40 + 24 * C) * L = 40 * L + 24 * C * L by ring]
      calc 9 * (K : ℝ) * 16 * (40 + 24 * C * L) * 2 = (288 * (40 + 24 * C * L)) * K := by ring
        _ ≤ (288 * (40 + 24 * C * L)) * (2 * C * L) :=
            mul_le_mul_of_nonneg_left hK (by positivity)
        _ ≤ (288 * ((40 + 24 * C) * L)) * (2 * C * L) := by gcongr
        _ = A * L ^ 2 := by rw [hAdef]; ring
    have hAL : 2 * (A * L ^ 2 * Real.exp E) ≤ Real.exp (ι / 4 * L) := by
      have e : 2 * (A * L ^ 2) = Real.exp (Real.log 2 + Real.log A + 2 * Real.log L) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hA, Real.exp_log two_pos,
          show 2 * Real.log L = Real.log (L ^ 2) by rw [Real.log_pow]; norm_num,
          Real.exp_log (by positivity)]; ring
      rw [← mul_assoc, e, ← Real.exp_add, Real.exp_le_exp]
      have hu6 : u ≤ u ^ 6 := le_self_pow₀ hu1 (by norm_num)
      have hu61 : 1 ≤ u ^ 6 := one_le_pow₀ hu1
      have h3 := le_abs_self (Real.log A)
      have h4 := mul_le_mul_of_nonneg_left hu61 (abs_nonneg (Real.log A))
      have h5 := mul_le_mul_of_nonneg_left hu61 (show (0 : ℝ) ≤ 20 * |α| * γ by positivity)
      have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
      have F4' : (|Real.log A| + 21 + 20 * |α| * γ) * u ^ 6 ≤ ι / 4 * L := by
        rw [← hu10]; exact F4
      have e2 : (|Real.log A| + 21 + 20 * |α| * γ) * u ^ 6 =
          |Real.log A| * u ^ 6 + 21 * u ^ 6 + 20 * |α| * γ * u ^ 6 := by ring
      linarith
    have hfin : 9 * (K : ℝ) * (16 * (8 * 2 ^ q + 4 * j + 16) * t ^ 2 * Real.exp E) ≤
        A * L ^ 2 * Real.exp E * t := by
      have e : 9 * (K : ℝ) * (16 * (8 * 2 ^ q + 4 * j + 16) * t ^ 2 * Real.exp E) =
          9 * K * 16 * Real.exp E * ((8 * 2 ^ q + 4 * j + 16) * t ^ 2) := by ring
      rw [e]
      have hK0 : (0 : ℝ) ≤ K := by positivity
      calc 9 * (K : ℝ) * 16 * Real.exp E * ((8 * 2 ^ q + 4 * j + 16) * t ^ 2) ≤
            9 * K * 16 * Real.exp E * ((40 + 24 * C * L) * t) :=
            mul_le_mul_of_nonneg_left hMt (by positivity)
        _ = (9 * K * 16 * (40 + 24 * C * L) * 2) * Real.exp E * (t / 2) := by ring
        _ ≤ A * L ^ 2 * Real.exp E * (t / 2) := by gcongr
        _ ≤ A * L ^ 2 * Real.exp E * t := by
            apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have htX' : t ≤ 2 * Real.exp (-(ι / 2 * L)) := by
      rw [Real.exp_neg, ← hXe]
      rw [le_mul_inv_iff₀ hX0]; linarith
    calc 9 * (K : ℝ) * (16 * (8 * 2 ^ q + 4 * j + 16) * t ^ 2 * Real.exp E) ≤
          A * L ^ 2 * Real.exp E * t := hfin
      _ ≤ A * L ^ 2 * Real.exp E * (2 * Real.exp (-(ι / 2 * L))) :=
          mul_le_mul_of_nonneg_left htX' (by positivity)
      _ = (2 * (A * L ^ 2 * Real.exp E)) * Real.exp (-(ι / 2 * L)) := by ring
      _ ≤ Real.exp (ι / 4 * L) * Real.exp (-(ι / 2 * L)) :=
          mul_le_mul_of_nonneg_right hAL (Real.exp_pos _).le
      _ = δ ^ (ι / 4) := by rw [← Real.exp_add, hδL]; congr 1; ring
  refine core.trans ?_
  have m1 : δ ^ c1 ≤ δ ^ m := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le
    ((min_le_left _ _).trans (min_le_left _ _))
  have m2 : δ ^ c2 ≤ δ ^ m := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le
    ((min_le_left _ _).trans (min_le_right _ _))
  have m3 : δ ^ (ι / 4) ≤ δ ^ m := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right _ _)
  have hthird : δ ^ (m / 2) ≤ 1 / 3 := by
    have := Real.rpow_le_rpow hδ0.le hδe.le (by positivity : 0 ≤ m / 2)
    rwa [← Real.rpow_mul (by norm_num), show 2 / m * (m / 2) = 1 by field_simp,
      Real.rpow_one] at this
  have hsplit : δ ^ m = δ ^ (m / 2) * δ ^ (m / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hpos : 0 ≤ δ ^ (m / 2) := by positivity
  have hfin : δ ^ c1 + δ ^ c2 + δ ^ (ι / 4) ≤ δ ^ (m / 2) := by nlinarith
  calc P (cellSizeEvent γ W δ)ᶜ + P (G δ)ᶜ + ENNReal.ofReal (9 * (K : ℝ) *
        (16 * (8 * 2 ^ q + 4 * j + 16) * ((2 : ℝ)⁻¹ ^ q) ^ 2 * Real.exp E)) ≤
        ENNReal.ofReal (δ ^ c1) + ENNReal.ofReal (δ ^ c2) + ENNReal.ofReal (δ ^ (ι / 4)) := by
        exact add_le_add (add_le_add (h1 δ ⟨hδ0, hδb⟩) (h2 δ ⟨hδ0, hδc⟩))
          (ENNReal.ofReal_le_ofReal hlast)
    _ = ENNReal.ofReal (δ ^ c1 + δ ^ c2 + δ ^ (ι / 4)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (δ ^ (m / 2)) := ENNReal.ofReal_le_ofReal hfin

end DZZ
end LQGMetric
