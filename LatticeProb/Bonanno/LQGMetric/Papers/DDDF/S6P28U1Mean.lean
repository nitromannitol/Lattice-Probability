/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28U1Mean at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Sum
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamMean
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsABWire
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm11
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm11Xi

/-!
# DDDF Prop 28 Part 1 Step 1 for the family: the mean of the chaining sum (task P2-DDDF28U)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1418–1424: "Taking the expected value and using the
same bounds as those obtained in the proof of Proposition 27, we get
`E sup_{2^{-k} ≤ |x−x'| ≤ 2^{-k+1}} d_{0,n}(x,x') ≤ Σ_{i ≥ k} 2^{-iξ(Q−2)} e^{Ci^{1/2+ε}}
≤ C 2^{-kξ(Q−2)} e^{Ck^{1/2+ε}}`", here for `φ_δ`, `δ = 2^{-(N+r)}`, `r ∈ (0,1]` (l. 1648):
`E R_K ≤ A λ_δ 2^{-θK}` for any `θ < ξ(Q−2)` (`mean_RK`). The inputs are those of Prop 27
(`s6_diam_mean`): (2.11) `prop2_expMoment_int`, the moments of `L_{2,1}(φ_{δ'})` uniformly in
`δ'` (`moment_unif`, from the tails (6.102) `s6_tails_AB_of_554`), (6.98), (5.76) and (5.54).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28U

open LFPP T20E Blueprint WhiteNoise S6D SupTail

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `Σ_{s ≥ K} e^{-bs + D√s} ≤ S e^{-b'K}` for `0 < b' < b` -/
lemma tail_sum {b b' D : ℝ} (hb' : 0 < b') (hbb : b' < b) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ K n : ℕ, Real.exp (-b * K + D * √(K : ℝ)) +
      ∑ t ∈ Finset.range n, Real.exp (-b * ((K + t + 1 : ℕ) : ℝ) + D * √((K + t + 1 : ℕ) : ℝ))
        ≤ S * Real.exp (-b' * K) := by
  set A := Real.exp (D ^ 2 / (2 * (b - b')))
  have hA : 0 < A := Real.exp_pos _
  set u := Real.exp (-b')
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hu1 : u < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hpt : ∀ x : ℝ, 0 ≤ x → Real.exp (-b * x + D * √x) ≤ A * Real.exp (-b' * x) := by
    intro x hx
    have := sqrt_le_lin (D := D) (sub_pos.2 hbb) hx
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  refine ⟨A * (1 + 1 / (1 - u)), by have : 0 < 1 - u := by linarith
                                    positivity, fun K n => ?_⟩
  have hgeo : ∑ t ∈ Finset.range n, u ^ (t + 1) ≤ 1 / (1 - u) := by
    calc ∑ t ∈ Finset.range n, u ^ (t + 1) ≤ ∑ t ∈ Finset.range n, u ^ t :=
          Finset.sum_le_sum fun t _ => pow_le_pow_of_le_one hu0 hu1.le (Nat.le_succ t)
      _ = ∑ t ∈ Finset.Ico 0 n, u ^ t := by rw [Finset.range_eq_Ico]
      _ ≤ u ^ 0 / (1 - u) := geom_sum_Ico_le_of_lt_one hu0 hu1
      _ = 1 / (1 - u) := by rw [pow_zero]
  have hterm : ∀ t : ℕ, Real.exp (-b * ((K + t + 1 : ℕ) : ℝ) + D * √((K + t + 1 : ℕ) : ℝ)) ≤
      A * Real.exp (-b' * K) * u ^ (t + 1) := by
    intro t
    have e : Real.exp (-b' * ((K + t + 1 : ℕ) : ℝ)) = Real.exp (-b' * K) * u ^ (t + 1) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    refine (hpt _ (Nat.cast_nonneg _)).trans (le_of_eq ?_)
    rw [e, mul_assoc]
  have hE := Real.exp_pos (-b' * K)
  calc Real.exp (-b * K + D * √(K : ℝ)) +
      ∑ t ∈ Finset.range n, Real.exp (-b * ((K + t + 1 : ℕ) : ℝ) + D * √((K + t + 1 : ℕ) : ℝ))
      ≤ A * Real.exp (-b' * K) + ∑ t ∈ Finset.range n, A * Real.exp (-b' * K) * u ^ (t + 1) :=
        add_le_add (hpt _ (Nat.cast_nonneg _)) (Finset.sum_le_sum fun t _ => hterm t)
    _ = A * Real.exp (-b' * K) * (1 + ∑ t ∈ Finset.range n, u ^ (t + 1)) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ A * Real.exp (-b' * K) * (1 + 1 / (1 - u)) := by gcongr
    _ = _ := by ring

/-- **moments of `L_{2,1}(φ_{δ'})`, uniformly in `δ' ∈ (0,1)`** (from the right tail (6.102)) -/
theorem moment_unif {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P) (q : ℕ) (hq : 1 ≤ q) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ δ' ∈ Ioo (0 : ℝ) 1,
      ∫⁻ ω, rectLen (xiGamma γ) (fun x => phiVer W P δ' 1 x ω) (rectAB 2 1) ^ q ∂P ≤
        ENNReal.ofReal (Cm * lambdaDelta (xiGamma γ) W P δ' ^ q) := by
  have hP := hW.isProbabilityMeasure
  have hT := (s6_tails_AB_of_554 hγ hγ2 hW h554 (a := 2) (b := 1) two_pos one_pos).1
  obtain ⟨c, C, hc, hC, ht⟩ := hT
  obtain ⟨K₀, hK₀, hmom⟩ := moment_of_tail (Ω := Ω) (P := P) q hq hc hC
  have h698 := s6_eq6_98_of_554 hγ hγ2 hW h554
  refine ⟨K₀, hK₀, fun δ' hδ' => ?_⟩
  have hφ := isPhiVersion_phiVer hW hδ'.1 hδ'.2.le
  have hLm := measurable_lenObs (ξ := xiGamma γ) hφ.cont hφ.meas (rectAB 2 1)
  have hL0 : ∀ ω, 0 ≤ lenObs (xiGamma γ) (phiVer W P δ' 1) (rectAB 2 1) ω :=
    fun ω => ENNReal.toReal_nonneg
  have hlpos : 0 < lambdaDelta (xiGamma γ) W P δ' := S6Thm.lambdaDelta_pos_of_698 hW h698 hδ'
  have ht' : ∀ s : ℝ, 2 < s → P {ω | Real.exp s * lambdaDelta (xiGamma γ) W P δ' ≤
      lenObs (xiGamma γ) (phiVer W P δ' 1) (rectAB 2 1) ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) :=
    fun s hs => ht s hs δ' hδ'.1 hδ'.2
  have h := hmom (lenObs (xiGamma γ) (phiVer W P δ' 1) (rectAB 2 1))
    (lambdaDelta (xiGamma γ) W P δ') hP hLm hL0 hlpos ht'
  refine le_trans (le_of_eq ?_) h
  refine lintegral_congr fun ω => ?_
  have h01 : (0 : ℝ) ≤ (rectAB 2 1).w := by simp [rectAB]
  have h01' : (0 : ℝ) ≤ (rectAB 2 1).h := by simp [rectAB]
  have hne := rectLen_ne_top (ξ := xiGamma γ) (rectAB 2 1) h01 h01' (hφ.cont ω)
  rw [lenObs, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne]

/-- `2^s 2^{-(N+r)} = 2^{-((N−s)+r)}` -/
lemma two_pow_mul_split {N s : ℕ} (hs : s ≤ N) (r : ℝ) :
    (2 : ℝ) ^ s * (2 : ℝ) ^ (-((N : ℝ) + r)) = (2 : ℝ) ^ (-(((N - s : ℕ) : ℝ) + r)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
  congr 1
  rw [Nat.cast_sub hs]; ring

lemma inv_two_pow_split {N s : ℕ} (hs : s ≤ N) {r : ℝ} (hr0 : 0 < r) :
    (2 : ℝ) ^ (-((N : ℝ) + r)) < (2 : ℝ)⁻¹ ^ s ∧ (2 : ℝ) ^ s * (2 : ℝ) ^ (-((N : ℝ) + r)) < 1 := by
  have h1 : (2 : ℝ) ^ s * (2 : ℝ) ^ (-((N : ℝ) + r)) < 1 := by
    rw [two_pow_mul_split hs]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
      have : (0 : ℝ) ≤ ((N - s : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith)
  refine ⟨?_, h1⟩
  have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  rw [inv_pow, ← one_div, lt_div_iff₀ hp, mul_comm]; exact h1

/-- **the mean of the chaining sum at scale `K`** (DDDF l. 1418–1424 for `φ_δ`):
`E R_K ≤ A λ_δ 2^{-θK}` for `θ < ξ(Q−2)`, `δ = 2^{-(N+r)}`, `r ∈ (0,1]`, `1 ≤ K < N`. -/
theorem mean_RK {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ < xiGamma γ * (LQGMetric.Q γ - 2)) :
    ∃ q : ℕ, 2 ≤ q ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ) (r : ℝ), 0 < r → r ≤ 1 → ∀ K : ℕ, 1 ≤ K →
      K + 1 ≤ N →
      ∫⁻ ω, RK (xiGamma γ) W P ((2 : ℝ) ^ (-((N : ℝ) + r))) q K (N - 1) ω ∂P ≤
        ENNReal.ofReal (A * lambdaDelta (xiGamma γ) W P ((2 : ℝ) ^ (-((N : ℝ) + r))) *
          Real.exp (-(Real.log 2 * θ) * K)) := by
  have hP := hW.isProbabilityMeasure
  have hξ : 0 < xiGamma γ := xiGamma_pos' hγ
  have hQ := two_lt_Q' hγ hγ2
  set ξ := xiGamma γ with hξdef
  set η := ξ * (LQGMetric.Q γ - 2) - θ with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨q, hq2, hqη⟩ : ∃ q : ℕ, 2 ≤ q ∧ 2 / (q : ℝ) ≤ η / 4 := by
    refine ⟨max 2 ⌈8 / η⌉₊, le_max_left _ _, ?_⟩
    have h1 : (8 / η : ℝ) ≤ ((max 2 ⌈8 / η⌉₊ : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    have hpos : (0 : ℝ) < ((max 2 ⌈8 / η⌉₊ : ℕ) : ℝ) := by
      have : 2 ≤ max 2 ⌈8 / η⌉₊ := le_max_left _ _
      positivity
    rw [div_le_div_iff₀ hpos (by norm_num)]
    rw [div_le_iff₀ hη0] at h1
    linarith
  obtain ⟨K₂, hK₂⟩ := prop2_expMoment_int hξ (xiGamma_lt_two hγ hγ2)
  obtain ⟨Cm, hCm0, hCm⟩ := moment_unif hγ hγ2 hW h554 q (by omega)
  obtain ⟨c, hc, hlow⟩ := lambdaN_lower_of_554 hW h554 (ζ := η / 4) (by positivity)
  obtain ⟨C₇, h76⟩ := s6_eq5_76_of_554 hγ hγ2 hW h554
  obtain ⟨C0, hC0⟩ := s6_eq6_98_of_554 hγ hγ2 hW h554
  set L := Real.log 2 with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  set a := 1 - ξ * LQGMetric.Q γ + η / 4 with ha
  set D := 2 * L * |K₂| + |C₇| with hD
  obtain ⟨S, hS0, hS⟩ := tail_sum (b := L * (θ + η / 2)) (b' := L * θ) (D := D) (by positivity)
    (by nlinarith)
  set M₀ := max 1 (lambdaN ξ W P 0) with hM₀def
  have hM₀ : 0 ≤ M₀ := le_trans zero_le_one (le_max_left _ _)
  have hM₀1 : 1 ≤ M₀ := le_max_left _ _
  have hlam : ∀ n, 0 < lambdaN ξ W P n := fun n => lambdaN_pos hW n
  set A₁ := (4 * Cm) ^ ((q : ℝ)⁻¹) * (Real.exp C0 * M₀) / c * Real.exp C0 with hA₁
  have hA₁0 : 0 ≤ A₁ := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 4 * Cm by positivity) ((q : ℝ)⁻¹)
    positivity
  have hexp : ∀ s : ℕ, L * (2 * ξ + 2 / q - 1 + a) * s + (2 * L * K₂ + |C₇|) * √(s : ℝ) ≤
      -(L * (θ + η / 2)) * s + D * √(s : ℝ) := by
    intro s
    have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have hss : 0 ≤ √(s : ℝ) := Real.sqrt_nonneg _
    have e1 : 2 * ξ + 2 / q - 1 + a ≤ -(θ + η / 2) := by
      have : 2 * ξ + 2 / q - 1 + a = 2 / q + η / 4 - (θ + η) := by rw [ha, hη]; ring
      rw [this]; linarith
    have h1 : L * (2 * ξ + 2 / q - 1 + a) * s ≤ L * (-(θ + η / 2)) * s :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hL0.le) hs
    have h2 : (2 * L * K₂ + |C₇|) * √(s : ℝ) ≤ D * √(s : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ hss
      have : L * K₂ ≤ L * |K₂| := mul_le_mul_of_nonneg_left (le_abs_self _) hL0.le
      rw [hD]; linarith
    calc _ ≤ L * (-(θ + η / 2)) * s + D * √(s : ℝ) := add_le_add h1 h2
      _ = _ := by ring
  refine ⟨q, hq2, 24 * A₁ * S, by positivity, fun N r hr0 hr1 K hK1 hKN => ?_⟩
  set δ := (2 : ℝ) ^ (-((N : ℝ) + r)) with hδdef
  have hδ0 : 0 < δ := by positivity
  set lδ := lambdaDelta ξ W P δ
  have hδN : δ ≤ (2 : ℝ)⁻¹ ^ N := (inv_two_pow_split le_rfl hr0).1.le
  have hlδ0 : 0 ≤ lδ := (S6Thm.lambdaDelta_pos_of_698 hW ⟨C0, hC0⟩
    ⟨hδ0, hδN.trans_lt (by
      have : (2 : ℝ)⁻¹ ^ N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      rcases Nat.eq_zero_or_pos N with h | h
      · omega
      · exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega))⟩).le
  have hlN : lambdaN ξ W P N ≤ Real.exp C0 * lδ := by
    have h := (hC0 N r hr0.le hr1).1
    have : lambdaN ξ W P N = Real.exp C0 * (Real.exp (-C0) * lambdaN ξ W P N) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [this]; exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  -- one scale
  have hterm : ∀ s : ℕ, 1 ≤ s → s ≤ N → ∀ {ι : Type} (J : Finset ι) (j : ι → Circle × ℂ),
      (J.card : ℝ) ≤ 4 ^ (s + 1) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (ξ * supAbs (fun z => phiMN W P 0 s z ω))) *
        ZqG ξ (fun x => phiVer W P δ ((2 : ℝ)⁻¹ ^ s) x ω) s q J j ∂P ≤
      ENNReal.ofReal (A₁ * lδ * Real.exp (-(L * (θ + η / 2)) * s + D * √(s : ℝ))) := by
    intro s hs1 hsN ι J j hJ
    obtain ⟨hδs, hδ'1⟩ := inv_two_pow_split hsN hr0
    have hδ'0 : 0 < (2 : ℝ) ^ s * δ := by positivity
    set lam' := lambdaDelta ξ W P ((2 : ℝ) ^ s * δ)
    have hlam'0 : 0 ≤ lam' := (S6Thm.lambdaDelta_pos_of_698 hW ⟨C0, hC0⟩ ⟨hδ'0, hδ'1⟩).le
    refine (level_mean hW (hK₂ hW) hδ0 hδs.le hq2 hCm0 hlam'0
      (hCm _ ⟨hδ'0, hδ'1⟩) J j).trans (ENNReal.ofReal_le_ofReal ?_)
    -- `λ_{2^s δ} ≤ e^{C0} M₀ e^{|C₇|√s} λ_N / λ_s`
    have hNK : lam' ≤ Real.exp C0 * M₀ * Real.exp (|C₇| * √(s : ℝ)) * lambdaN ξ W P N /
        lambdaN ξ W P s := by
      have h98 : lam' ≤ Real.exp C0 * lambdaN ξ W P (N - s) := by
        have := (hC0 (N - s) r hr0.le hr1).2
        rwa [← two_pow_mul_split hsN] at this
      have h2 : lambdaN ξ W P (N - s) ≤ M₀ * Real.exp (|C₇| * √(s : ℝ)) * lambdaN ξ W P N /
          lambdaN ξ W P s := by
        rw [le_div_iff₀ (hlam _)]
        rcases Nat.eq_zero_or_pos (N - s) with h0 | hpos
        · have e : s = N := by omega
          rw [h0, ← e]
          have hl := hlam s
          have h1 : lambdaN ξ W P 0 ≤ M₀ := le_max_right _ _
          have h2 : 1 ≤ Real.exp (|C₇| * √(s : ℝ)) := Real.one_le_exp (by positivity)
          have : lambdaN ξ W P 0 * lambdaN ξ W P s ≤ M₀ * 1 * lambdaN ξ W P s := by nlinarith
          calc _ ≤ M₀ * 1 * lambdaN ξ W P s := this
            _ ≤ _ := by gcongr
        · obtain ⟨h1, -⟩ := h76 (N - s) s hpos hs1
          have e : N - s + s = N := by omega
          rw [e] at h1
          have h2 : Real.exp (C₇ * √(s : ℝ)) ≤ M₀ * Real.exp (|C₇| * √(s : ℝ)) := by
            calc Real.exp (C₇ * √(s : ℝ)) ≤ Real.exp (|C₇| * √(s : ℝ)) :=
                  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self _)
                    (Real.sqrt_nonneg _))
              _ ≤ M₀ * Real.exp (|C₇| * √(s : ℝ)) :=
                  le_mul_of_one_le_left (Real.exp_pos _).le hM₀1
          have h3 : lambdaN ξ W P (N - s) * lambdaN ξ W P s ≤
              Real.exp (C₇ * √(s : ℝ)) * lambdaN ξ W P N := by
            have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (C₇ * √(s : ℝ))).le
            rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, show C₇ * √(s : ℝ) +
              -(C₇ * √(s : ℝ)) = 0 by ring, Real.exp_zero, one_mul] at this
            linarith
          calc _ ≤ Real.exp (C₇ * √(s : ℝ)) * lambdaN ξ W P N := h3
            _ ≤ M₀ * Real.exp (|C₇| * √(s : ℝ)) * lambdaN ξ W P N :=
                mul_le_mul_of_nonneg_right h2 (hlam N).le
      calc lam' ≤ Real.exp C0 * lambdaN ξ W P (N - s) := h98
        _ ≤ Real.exp C0 * (M₀ * Real.exp (|C₇| * √(s : ℝ)) * lambdaN ξ W P N /
            lambdaN ξ W P s) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = _ := by ring
    have hcard : ((J.card : ℝ) * Cm) ^ ((q : ℝ)⁻¹) ≤ (4 ^ s * (4 * Cm)) ^ ((q : ℝ)⁻¹) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      calc (J.card : ℝ) * Cm ≤ 4 ^ (s + 1) * Cm := mul_le_mul_of_nonneg_right hJ hCm0
        _ = 4 ^ s * (4 * Cm) := by rw [pow_succ]; ring
    have htb := term_bound (ξ := ξ) (K₂ := K₂) (q := q) (C := 4 * Cm) (by positivity) s hc
      (hlow s) hNK (by positivity) (hlam N).le hlam'0
    have hp1 : (0 : ℝ) ≤ (4 : ℝ) ^ (ξ * (s : ℝ) + K₂ * √(s : ℝ)) := by positivity
    calc (4 : ℝ) ^ (ξ * (s : ℝ) + K₂ * √(s : ℝ)) *
          (((J.card : ℝ) * Cm) ^ ((q : ℝ)⁻¹) * ((2 : ℝ)⁻¹ ^ s * lam'))
        ≤ (4 : ℝ) ^ (ξ * (s : ℝ) + K₂ * √(s : ℝ)) *
          ((4 ^ s * (4 * Cm)) ^ ((q : ℝ)⁻¹) * ((2 : ℝ)⁻¹ ^ s * lam')) := by
          gcongr
      _ ≤ (4 * Cm) ^ ((q : ℝ)⁻¹) * (Real.exp C0 * M₀) / c * lambdaN ξ W P N *
          Real.exp (L * (2 * ξ + 2 / q - 1 + a) * s + (2 * L * K₂ + |C₇|) * √(s : ℝ)) := htb
      _ ≤ (4 * Cm) ^ ((q : ℝ)⁻¹) * (Real.exp C0 * M₀) / c * (Real.exp C0 * lδ) *
          Real.exp (-(L * (θ + η / 2)) * s + D * √(s : ℝ)) := by
          have := Real.rpow_nonneg (show (0 : ℝ) ≤ 4 * Cm by positivity) ((q : ℝ)⁻¹)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hlN (by positivity))
            (Real.exp_le_exp.2 (hexp s)) (Real.exp_pos _).le (by positivity)
      _ = A₁ * lδ * Real.exp (-(L * (θ + η / 2)) * s + D * √(s : ℝ)) := by rw [hA₁]; ring
  -- the sum
  have hXS := hterm K hK1 (by omega) (idxS K) (fun r => hmS K r.1.1 r.1.2 r.2) (card_idxS_le K)
  have hXH : ∀ t ∈ Finset.range (N - 1 - K + 1), ∫⁻ ω, XH ξ W P δ q (K + t) ω ∂P ≤
      ENNReal.ofReal (A₁ * lδ * Real.exp (-(L * (θ + η / 2)) * ((K + t + 1 : ℕ) : ℝ) +
        D * √((K + t + 1 : ℕ) : ℝ))) := by
    intro t ht
    have : t ≤ N - 1 - K := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    exact hterm (K + t + 1) (by omega) (by omega) (idxSet (K + t))
      (fun r => hm (K + t) r.1.1 r.1.2 r.2) (card_idxSet_le (K + t))
  have hmS' := measurable_XS (ξ := ξ) hW hδ0 q K (hδN.trans (inv_two_pow_anti (by omega)))
  have hmH : ∀ t ∈ Finset.range (N - 1 - K + 1), Measurable (XH ξ W P δ q (K + t)) := by
    intro t ht
    have : t ≤ N - 1 - K := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    exact measurable_XH hW hδ0 q (K + t) (hδN.trans (inv_two_pow_anti (by omega)))
  unfold RK
  rw [lintegral_add_left (hmS'.const_mul _), lintegral_const_mul _ hmS',
    lintegral_const_mul _ (Finset.measurable_sum _ hmH), lintegral_finsetSum _ hmH]
  set e : ℕ → ℝ := fun s => Real.exp (-(L * (θ + η / 2)) * s + D * √(s : ℝ))
  have he0 : ∀ s, 0 ≤ e s := fun s => (Real.exp_pos _).le
  have hsum : ∑ t ∈ Finset.range (N - 1 - K + 1), ∫⁻ ω, XH ξ W P δ q (K + t) ω ∂P ≤
      ENNReal.ofReal (A₁ * lδ * ∑ t ∈ Finset.range (N - 1 - K + 1), e (K + t + 1)) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun t _ => by
      have := he0 (K + t + 1); positivity)]
    exact Finset.sum_le_sum hXH
  have hS' := hS K (N - 1 - K + 1)
  have hfin : 8 * ENNReal.ofReal (A₁ * lδ * e K) +
      24 * ENNReal.ofReal (A₁ * lδ * ∑ t ∈ Finset.range (N - 1 - K + 1), e (K + t + 1)) ≤
      ENNReal.ofReal (24 * A₁ * S * lδ * Real.exp (-(L * θ) * K)) := by
    have hs0 : 0 ≤ ∑ t ∈ Finset.range (N - 1 - K + 1), e (K + t + 1) :=
      Finset.sum_nonneg fun t _ => he0 _
    rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
      show (24 : ℝ≥0∞) = ENNReal.ofReal 24 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by have := he0 K; positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hAl : 0 ≤ A₁ * lδ := mul_nonneg hA₁0 hlδ0
    have key : e K + ∑ t ∈ Finset.range (N - 1 - K + 1), e (K + t + 1) ≤
        S * Real.exp (-(L * θ) * K) := hS'
    have h8 : 8 * (A₁ * lδ * e K) ≤ 24 * (A₁ * lδ * e K) := by
      have := mul_nonneg hAl (he0 K); linarith
    calc 8 * (A₁ * lδ * e K) + 24 * (A₁ * lδ * ∑ t ∈ Finset.range (N - 1 - K + 1), e (K + t + 1))
        ≤ 24 * (A₁ * lδ) * (e K + ∑ t ∈ Finset.range (N - 1 - K + 1), e (K + t + 1)) := by
          nlinarith
      _ ≤ 24 * (A₁ * lδ) * (S * Real.exp (-(L * θ) * K)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = 24 * A₁ * S * lδ * Real.exp (-(L * θ) * K) := by ring
  calc 8 * ∫⁻ ω, XS ξ W P δ q K ω ∂P + 24 * ∑ t ∈ Finset.range (N - 1 - K + 1),
        ∫⁻ ω, XH ξ W P δ q (K + t) ω ∂P
      ≤ 8 * ENNReal.ofReal (A₁ * lδ * e K) +
        24 * ENNReal.ofReal (A₁ * lδ * ∑ t ∈ Finset.range (N - 1 - K + 1), e (K + t + 1)) := by
        gcongr
        exact hXS
    _ ≤ _ := hfin.trans_eq (by ring_nf)

end S6P28U
end DDDF
end LQGMetric
