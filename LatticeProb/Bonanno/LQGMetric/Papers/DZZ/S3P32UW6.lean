/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UW6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UW5

/-!
# Walled (Eq.boundDprime), UW6: (eq-B-percolation-Psi) for one sub-box of a dyadic wall, the
choice of parameters (P2-DZZUPW, packet P-317K-UP)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1104–1147) with Remark 5.2. **`p32_enc_percW`** is a
verbatim copy of `p32_enc_perc` (S3P32F3, P2-DZZ32F): all parameters are those of the real box
`b = wEmb Bw B_p` (level, side, centre), and the final step is the walled `p32_enc_boxW`
(S3P32UW5) at the pulled-back box `B_p` and pulled-back clipping depth `r_δ / s_{Bw}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

set_option maxHeartbeats 2000000 in
/-- **Walled DZZ (eq-B-percolation-Psi), one sub-box `wEmb Bw B_p` of the wall** (l. 1104–1147;
copy of `p32_enc_perc`). -/
theorem p32_enc_percW (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (α : ℝ)
    (G : ℝ → Set Ω) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (Bw : DyBox)
    (hup : ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ B : DyBox, δ ^ dzzCmc γ ≤ B.side → ∀ ω ∈ G δ,
      approxLQG γ W ω B ≤ δ ^ 2 → ∀ b' : DyBox, (∀ z ∈ b'.closedBox, ‖z - B.center‖ ≤ 3 * B.side) →
        wickQArea γ W ω b'.closedBox ≤
          ENNReal.ofReal (Real.exp (2 * α * γ * Real.sqrt (Real.log δ⁻¹) *
            Real.log (Real.log δ⁻¹)) * δ ^ 2 / B.side ^ 2) *
          etaChaos W γ ((2 : ℝ)⁻¹ ^ (B.n + 2 * kL37 γ δ)) b'.closedBox ω) :
    ∃ δ₁ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₁, ∀ Bp : DyBox, 1 ≤ Bp.n →
      ((wEmb Bw Bp).n : ℝ) ≤ dzzCmc γ * Real.logb 2 δ⁻¹ →
      P ({ω | approxLQG γ W ω (wEmb Bw Bp) ≤ δ ^ 2} ∩ G δ ∩
        {ω | ¬ HasEnclosure Bp (kL37 γ δ) fun c =>
          PhiLeW (wPullMeas Bw (dzzWall Bw.closedBox (dzzMuIn γ W ω))) δ (rP32 γ δ / Bw.side) c
            (lamP32 δ)}) ≤
        ENNReal.ofReal (δ ^ (10 * dzzCmc γ + 10)) := by
  have hC : 0 < dzzCmc γ := by have := l31theta_pos hγ hγ2; unfold dzzCmc; linarith
  obtain ⟨U, hU1, hU⟩ := l37_ev (dzzCmc γ) γ |α| hC
  obtain ⟨U', hU'⟩ := eventually_atTop.1
    (ev_pow_le (show (0 : ℝ) < 1 / 100 by norm_num) (8 + 20 * |α| * γ) (show 6 < 7 by norm_num))
  refine ⟨min δ₀ (Real.exp (-((max (max U U') 1) ^ 10))), lt_min hδ₀ (Real.exp_pos _), ?_⟩
  rintro δ ⟨hδ0, hδ1'⟩ Bp hb1 hbn
  set b := wEmb Bw Bp with hbdef
  have hδδ₀ : δ < δ₀ := hδ1'.trans_le (min_le_left _ _)
  have hδ1 : δ < Real.exp (-((max (max U U') 1) ^ 10)) := hδ1'.trans_le (min_le_right _ _)
  obtain ⟨k, hkdef⟩ : ∃ k, k = kL37 γ δ := ⟨_, rfl⟩
  rw [← hkdef]
  set C := dzzCmc γ with hCdef
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  set U'' := max (max U U') 1 with hU''
  have hU0 : (0 : ℝ) ≤ U'' := by positivity
  have hL : U'' ^ 10 < L := by
    have := Real.log_lt_log hδ0 hδ1
    rw [Real.log_exp] at this; linarith
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
  have hδlt1 : δ < 1 := by
    have : Real.log δ < 0 := by linarith
    exact (Real.log_neg_iff hδ0).1 this
  set u := L ^ ((1 : ℝ) / 10) with hudef
  have hu10 : u ^ 10 = L := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hu7 : L ^ (0.7 : ℝ) = u ^ 7 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have huU : U'' ≤ u := by
    have h1 : (U'' ^ 10) ^ ((1 : ℝ) / 10) = U'' := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0]; norm_num
    rw [← h1]; exact Real.rpow_le_rpow (by positivity) hL.le (by norm_num)
  obtain ⟨E2, E3, E4, E5, E6, E7⟩ := hU u ((le_max_left _ _).trans ((le_max_left _ _).trans huU))
  have E8 := hU' u ((le_max_right _ _).trans ((le_max_left _ _).trans huU))
  have hu1 : 1 ≤ u := hU1.trans ((le_max_left _ _).trans ((le_max_left _ _).trans huU))
  have hu0 : 0 < u := by linarith
  have hsqrt : Real.sqrt L = u ^ 5 := by
    rw [← hu10, show u ^ 10 = (u ^ 5) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by rw [← hu10]; exact one_le_pow₀ hu1)
  have hlogL : Real.log L ≤ 10 * u := by
    have := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 10 by norm_num)
    rw [← hudef] at this
    calc Real.log L ≤ u / (1 / 10) := this
      _ = 10 * u := by ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  -- `k`: `2^k ≤ 4 C L < 2^{k+1}`
  set x := 4 * C * L with hx
  have hCL : 8 ≤ C * L := by rw [← hu10]; exact E2
  have hx32 : 32 ≤ x := by rw [hx]; linarith
  have hk' : k = Nat.log 2 ⌊x⌋₊ := by rw [hkdef]; rfl
  have hfl : ⌊x⌋₊ ≠ 0 := by
    have := Nat.floor_pos.2 (show (1 : ℝ) ≤ x by linarith); omega
  have hxk : x < (2 : ℝ) ^ (k + 1) := by
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊x⌋₊
    rw [← hk'] at h1
    have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2; linarith [Nat.lt_floor_add_one x]
  have hk5 : 5 ≤ k := by
    by_contra hk; push Not at hk
    have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; linarith
  set h := 2 ^ (k - 1) with hhdef
  have hK : 2 ^ k = 2 * h := by
    rw [hhdef, ← pow_succ']; congr 1; omega
  have hhR : (2 : ℝ) ^ k = 2 * (h : ℝ) := by exact_mod_cast hK
  have h4 : 4 ≤ h := by
    calc 4 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hhCL : C * L < h := by
    have : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [hx] at hxk; linarith
  -- `ℓ`: `2^{ℓ+3} ≤ λ < 2^{ℓ+4}`
  set lam := lamP32 δ with hlamdef
  have hlam : lam = Real.exp (u ^ 7) := by rw [hlamdef, lamP32, ← hLdef, hu7]
  have hlam32 : 32 ≤ lam := by
    rw [hlam]; have := Real.add_one_le_exp (u ^ 7); linarith
  have hlam0 : 0 < lam := by linarith
  obtain ⟨ℓ₀, hℓdef⟩ : ∃ ℓ₀, ℓ₀ = Nat.log 2 ⌊lam⌋₊ := ⟨_, rfl⟩
  have hfl2 : ⌊lam⌋₊ ≠ 0 := by
    have := Nat.floor_pos.2 (show (1 : ℝ) ≤ lam by linarith); omega
  have hℓ1 : (2 : ℝ) ^ ℓ₀ ≤ lam := by
    have h1 := Nat.pow_log_le_self 2 hfl2
    rw [← hℓdef] at h1
    have h2 : ((2 ^ ℓ₀ : ℕ) : ℝ) ≤ (⌊lam⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2; exact h2.trans (Nat.floor_le hlam0.le)
  have hℓ2 : lam < (2 : ℝ) ^ (ℓ₀ + 1) := by
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊lam⌋₊
    rw [← hℓdef] at h1
    have h2 : ((⌊lam⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (ℓ₀ + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2; linarith [Nat.lt_floor_add_one lam]
  have hℓ5 : 5 ≤ ℓ₀ := by
    by_contra hc; push Not at hc
    have : (2 : ℝ) ^ (ℓ₀ + 1) ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; linarith
  set ℓ := ℓ₀ - 3 with hℓ
  have hℓ3 : (2 : ℝ) ^ ℓ * 8 = 2 ^ ℓ₀ := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
  have h1ℓ : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
  have hlamℓ : (4 * (2 ^ ℓ + 1) : ℝ) ≤ lam := by linarith
  have hℓlam : lam < 16 * 2 ^ ℓ := by
    have : (2 : ℝ) ^ (ℓ₀ + 1) = 2 * 2 ^ ℓ₀ := by rw [pow_succ]; ring
    linarith
  -- the exponent `E = 2αγ√L log L`
  set E := 2 * α * γ * Real.sqrt L * Real.log L with hEdef
  have hE : E ≤ 20 * |α| * γ * u ^ 6 := by
    have t1 : α * Real.log L ≤ |α| * (10 * u) :=
      (mul_le_mul_of_nonneg_right (le_abs_self α) hlogL0).trans
        (mul_le_mul_of_nonneg_left hlogL (abs_nonneg α))
    have e : E = 2 * γ * u ^ 5 * (α * Real.log L) := by rw [hEdef, hsqrt]; ring
    rw [e]
    calc 2 * γ * u ^ 5 * (α * Real.log L) ≤ 2 * γ * u ^ 5 * (|α| * (10 * u)) :=
          mul_le_mul_of_nonneg_left t1 (by positivity)
      _ = 20 * |α| * γ * u ^ 6 := by ring
  -- `θ`
  set ρ := Real.exp (-(u ^ 7 / 100)) with hρdef
  have h8 : 8 ≤ Real.exp (u ^ 7 / 200) := by
    have := Real.add_one_le_exp (u ^ 7 / 200); linarith
  have hρ8 : 8 * ρ ≤ Real.exp (-(u ^ 7 / 200)) := by
    rw [show -(u ^ 7 / 200) = u ^ 7 / 200 + -(u ^ 7 / 100) by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_right h8 (Real.exp_pos _).le
  have hρ2 : 8 * ρ ≤ 2⁻¹ := by
    have hm : Real.exp (-(u ^ 7 / 200)) ≤ 1 / 8 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; norm_num; exact h8
    linarith
  have hθ : 8 * ENNReal.ofReal ρ ≤ 2⁻¹ := by
    rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp, ← ENNReal.ofReal_mul (by norm_num),
      show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ by rw [ENNReal.ofReal_inv_of_pos two_pos]; simp]
    exact ENNReal.ofReal_le_ofReal hρ2
  -- `θ_open`, `K`
  set s := b.side with hsdef
  have hs0 : 0 < s := b.side_pos'
  set θo : ℝ := s ^ 2 * Real.exp (-E) / 4 with hθodef
  have hθo0 : 0 < θo := by positivity
  set K : ℝ := Real.exp E * δ ^ 2 / s ^ 2 with hKdef
  have hKθ : 4 * (ENNReal.ofReal K * ENNReal.ofReal θo) ≤ ENNReal.ofReal (δ ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity), show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply le_of_eq; congr 1
    rw [hKdef, hθodef, Real.exp_neg]
    field_simp
  -- `hεθ`
  have hεθ : ((8 * (2 ^ ℓ + 2) : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (b.n + k + ℓ)) ^ 2) / ENNReal.ofReal θo) ≤
      ENNReal.ofReal ρ ^ ((3 + 1) ^ 2) := by
    rw [← ENNReal.ofReal_div_of_pos hθo0, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hsplit : (2 : ℝ)⁻¹ ^ (b.n + k + ℓ) = s * ((2 : ℝ)⁻¹ ^ k * (2 : ℝ)⁻¹ ^ ℓ) := by
      rw [hsdef, DyBox.side, pow_add, pow_add]; ring
    have hq : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hq0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
    have hinvℓ : (2 : ℝ)⁻¹ ^ ℓ * 2 ^ ℓ = 1 := pow_inv_mul_pow ℓ
    have hp0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ ℓ := by positivity
    have hpl : (2 : ℝ)⁻¹ ^ ℓ < 16 * Real.exp (-(u ^ 7)) := by
      rw [Real.exp_neg, ← hlam]
      rw [lt_iff_not_ge]; intro hc
      have : 16 * lam⁻¹ * lam ≤ (2 : ℝ)⁻¹ ^ ℓ * lam := mul_le_mul_of_nonneg_right hc hlam0.le
      rw [mul_assoc, inv_mul_cancel₀ hlam0.ne'] at this
      have := mul_lt_mul_of_pos_left hℓlam hp0
      nlinarith
    have hcast : (((8 * (2 ^ ℓ + 2) : ℕ)) : ℝ) ≤ 24 * 2 ^ ℓ := by push_cast; linarith
    have key : (((8 * (2 ^ ℓ + 2) : ℕ)) : ℝ) * (((2 : ℝ)⁻¹ ^ (b.n + k + ℓ)) ^ 2 / θo) ≤
        96 * Real.exp E * (2 : ℝ)⁻¹ ^ ℓ := by
      rw [hsplit, hθodef, Real.exp_neg]
      have e : (s * ((2 : ℝ)⁻¹ ^ k * (2 : ℝ)⁻¹ ^ ℓ)) ^ 2 / (s ^ 2 * (Real.exp E)⁻¹ / 4) =
          4 * Real.exp E * ((2 : ℝ)⁻¹ ^ k) ^ 2 * ((2 : ℝ)⁻¹ ^ ℓ) ^ 2 := by
        field_simp
      rw [e]
      have hq2 : ((2 : ℝ)⁻¹ ^ k) ^ 2 ≤ 1 := pow_le_one₀ hq0.le hq
      have hx0 : 0 ≤ 4 * Real.exp E * ((2 : ℝ)⁻¹ ^ ℓ) ^ 2 := by positivity
      calc (((8 * (2 ^ ℓ + 2) : ℕ)) : ℝ) *
            (4 * Real.exp E * ((2 : ℝ)⁻¹ ^ k) ^ 2 * ((2 : ℝ)⁻¹ ^ ℓ) ^ 2)
          ≤ 24 * 2 ^ ℓ * (4 * Real.exp E * ((2 : ℝ)⁻¹ ^ ℓ) ^ 2) := by
            refine mul_le_mul hcast ?_ (by positivity) (by positivity)
            have := mul_le_mul_of_nonneg_left hq2 hx0
            nlinarith
        _ = 96 * Real.exp E * (2 : ℝ)⁻¹ ^ ℓ * ((2 : ℝ)⁻¹ ^ ℓ * 2 ^ ℓ) := by ring
        _ = 96 * Real.exp E * (2 : ℝ)⁻¹ ^ ℓ := by rw [hinvℓ, mul_one]
    refine key.trans ?_
    have h1536 : (1536 : ℝ) ≤ Real.exp 8 := by
      have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have e : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) h1 8
      linarith
    calc 96 * Real.exp E * (2 : ℝ)⁻¹ ^ ℓ ≤ 96 * Real.exp E * (16 * Real.exp (-(u ^ 7))) :=
          mul_le_mul_of_nonneg_left hpl.le (by positivity)
      _ = 1536 * Real.exp (E - u ^ 7) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ Real.exp 8 * Real.exp (E - u ^ 7) :=
          mul_le_mul_of_nonneg_right h1536 (Real.exp_pos _).le
      _ = Real.exp (8 + E - u ^ 7) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(u ^ 7 / 100) * 16) := by
          rw [Real.exp_le_exp]
          have hu6 : 1 ≤ u ^ 6 := one_le_pow₀ hu1
          have : (8 + 20 * |α| * γ) * u ^ 6 ≤ 1 / 100 * u ^ 7 := E8
          nlinarith
      _ = ρ ^ ((3 + 1) ^ 2) := by
          rw [hρdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- `hRs`
  have hbn' : (b.n : ℝ) * Real.log 2 ≤ C * L := by
    rw [Real.logb, ← hLdef] at hbn
    rw [← le_div_iff₀ hlog2]
    calc (b.n : ℝ) ≤ C * (L / Real.log 2) := hbn
      _ = C * L / Real.log 2 := by ring
  have hRs : 2 * (((2 : ℝ)⁻¹ ^ (b.n + 2 * k) * Real.log ((2 : ℝ)⁻¹ ^ (b.n + 2 * k))⁻¹ +
        (2 : ℝ)⁻¹ ^ (b.n + 2 * k)) / 2) + 2 * (2 : ℝ)⁻¹ ^ (b.n + k + ℓ) <
      3 * (2 : ℝ)⁻¹ ^ (b.n + k) := by
    have hlg : Real.log ((2 : ℝ)⁻¹ ^ (b.n + 2 * k))⁻¹ = ((b.n : ℝ) + 2 * k) * Real.log 2 := by
      rw [inv_pow, inv_inv, Real.log_pow]; push_cast; ring
    have he : (2 : ℝ)⁻¹ ^ (b.n + 2 * k) = (2 : ℝ)⁻¹ ^ (b.n + k) * (2 : ℝ)⁻¹ ^ k := by
      rw [← pow_add]; congr 1; ring
    have h3 : (2 : ℝ)⁻¹ ^ (b.n + k + ℓ) ≤ (2 : ℝ)⁻¹ ^ (b.n + k) * 2⁻¹ := by
      rw [← pow_succ]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hnat : 2 * k + 1 ≤ h := by
      have := two_mul_add_le_pow (k - 5)
      rw [show k - 5 + 5 = k by omega, show k - 5 + 4 = k - 1 by omega] at this
      exact this
    have hnatR : 2 * (k : ℝ) + 1 ≤ h := by exact_mod_cast hnat
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hkey : ((b.n : ℝ) + 2 * k) * Real.log 2 + 1 ≤ 2 ^ k := by
      rw [hhR]; nlinarith [mul_le_mul_of_nonneg_left hlog2'.le hk0]
    set s' := (2 : ℝ)⁻¹ ^ (b.n + k)
    set q := (2 : ℝ)⁻¹ ^ k
    have hs'0 : 0 < s' := by positivity
    have hq : q * 2 ^ k = 1 := pow_inv_mul_pow k
    have m1 : s' * q * (((b.n : ℝ) + 2 * k) * Real.log 2 + 1) ≤ s' * q * 2 ^ k :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have m2 : s' * q * 2 ^ k = s' := by rw [mul_assoc, hq, mul_one]
    rw [hlg, he]
    nlinarith
  -- the final bound (as in `dzz_lemma37_perc`)
  have hfinal : 4 * (((2 * (2 * h - 2) + 1 : ℕ) : ℝ≥0∞) *
      (8 * ENNReal.ofReal ρ) ^ ((2 * h - 2) - (h + 2) + 1)) ≤
      ENNReal.ofReal (δ ^ (10 * C + 10)) := by
    set m := (2 * h - 2) - (h + 2) + 1 with hmdef
    have hm : (m : ℝ) = h - 3 := by
      have : m = h - 3 := by omega
      rw [this, Nat.cast_sub (by omega)]; norm_num
    have hN : (((2 * (2 * h - 2) + 1 : ℕ)) : ℝ) ≤ 4 * h := by
      have : 2 * (2 * h - 2) + 1 ≤ 4 * h := by omega
      exact_mod_cast this
    have e8 : (8 : ℝ≥0∞) * ENNReal.ofReal ρ = ENNReal.ofReal (8 * ρ) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    rw [e8, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have hpow : (8 * ρ) ^ m ≤ Real.exp (m * (-(u ^ 7 / 200))) := by
      rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by positivity) hρ8 m
    have hexp10 : u ^ 20 / 2 ≤ Real.exp (u ^ 10) := by
      have := Real.pow_div_factorial_le_exp (u ^ 10) (by positivity) 2
      calc u ^ 20 / 2 = (u ^ 10) ^ 2 / (Nat.factorial 2) := by
            rw [Nat.factorial_two]; push_cast; ring
        _ ≤ _ := this
    have h4N : 4 * (((2 * (2 * h - 2) + 1 : ℕ)) : ℝ) ≤ Real.exp (u ^ 10) := by
      have : (h : ℝ) ≤ 2 * C * u ^ 10 := by
        have : (2 : ℝ) ^ k ≤ x := by
          have h1 := Nat.pow_log_le_self 2 hfl
          rw [← hk'] at h1
          have h2 : ((2 ^ k : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
          push_cast at h2; exact h2.trans (Nat.floor_le (by linarith))
        rw [hu10]; linarith
      linarith
    have hhu : C * u ^ 10 < h := by rw [hu10]; exact hhCL
    have hp : (C * u ^ 10 - 3) * u ^ 7 ≤ ((h : ℝ) - 3) * u ^ 7 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc 4 * ((((2 * (2 * h - 2) + 1 : ℕ)) : ℝ) * (8 * ρ) ^ m) =
          (4 * (((2 * (2 * h - 2) + 1 : ℕ)) : ℝ)) * (8 * ρ) ^ m := by ring
      _ ≤ Real.exp (u ^ 10) * Real.exp (m * (-(u ^ 7 / 200))) :=
          mul_le_mul h4N hpow (by positivity) (Real.exp_pos _).le
      _ = Real.exp (u ^ 10 + m * (-(u ^ 7 / 200))) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (Real.log δ * (10 * C + 10)) := by
          rw [Real.exp_le_exp, hlogδ, hm, ← hu10]
          have e17 : u ^ 17 = u ^ 10 * u ^ 7 := by ring
          linarith
      _ = δ ^ (10 * C + 10) := (Real.rpow_def_of_pos hδ0 _).symm
  -- assembly
  have hside : δ ^ C ≤ b.side := by
    rw [DyBox.side, inv_pow, Real.rpow_def_of_pos hδ0, hlogδ]
    rw [← Real.exp_log (show (0 : ℝ) < 2 ^ b.n by positivity), ← Real.exp_neg, Real.exp_le_exp,
      Real.log_pow]
    linarith
  have hr : 0 < rP32 γ δ / Bw.side :=
    div_pos (isClipDepth_rP32 γ δ ⟨hδ0, hδlt1⟩).1 (wside_pos Bw)
  have core := p32_enc_boxW (P := P) hW (γ := γ) (Bw := Bw) (Bp := Bp) (k := k) (h := h) (ℓ := ℓ)
    hK h4 hb1
    (δ := δ) (lam := lam) hr hlamℓ hKθ (ENNReal.ofReal_pos.2 hθo0).ne' ENNReal.ofReal_ne_top
    ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ G δ)
    (fun ω hω b' hb' => by
      have := hup δ ⟨hδ0, hδδ₀⟩ b hside ω hω.2 hω.1 b' hb'
      rw [← hkdef] at this
      exact this) hRs hθ hεθ
  exact core.trans hfinal

end DZZ
end LQGMetric
