/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412bStep1E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bStep1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bScale

/-!
# GM Lemma 4.15, Step 1 on `ℰ_𝕣`, one `k`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 1, l. 2123–2128.
`p412b_step1_E`: for `𝕫 ∈ 𝕣U`, `k ε^β ≤ a/c₂` (i.e. `k ≤ K + 1`, cf. `gm_S4_3`) and `N` with
`N^{-β_C} · p412bC ≤ ε^{2β}` (GM: "`β` sufficiently small depending on `ω, D`"),
`P[ℰ_𝕣, #𝒳_k > N] ≤ b₀ exp(−b₁N^{β_C})`, from the conclusion of CONF Theorem 3.9
(`CONFThm3_9At`, constants `b₀, b₁, β_C` for the given `a`; normalization `ξ = R.ξ`, `c = R.c`,
CONF parameters `R.p`, exponent `R.χ`), the D76 bridge at `(s_k, t_k)` a.s., the a.s. identities
`H = h_·(·)` at `(𝕣,0), (𝕣,𝕫), (ℓ𝕣,𝕫)` (D60), and a.s. `D_h` a length metric with bounded balls.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **GM L4.15 Step 1** (l. 2125–2128) on `ℰ_𝕣`, for one `k`. -/
theorem p412b_step1_E {D : DistC → ContMetric} {b₀ b₁ βC : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ) (R : RegPar) {𝕣 a : ℝ}
    (hT : ∀ (z₀ : ℂ) (Rr : ℝ), 0 < Rr → ∀ N : ℕ, 1 ≤ N →
      ∀ τ : Ω → ℝ, IsFilledBallStoppingTime D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      (∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ Rr ω) (tauR D h z₀ (2 * Rr) ω)) →
      P {ω | ω ∈ confReg R.ξ R.c D P h R.p R.χ z₀ Rr a ∧
          ((N : ℕ∞) : ℕ∞) < (hitSetLM (D (h ω)) z₀ (τ ω)
            (τ ω + (N : ℝ) ^ (-βC) * scaleFac R.ξ R.c (h ω) Rr z₀)).encard} ≤
        ENNReal.ofReal (b₀ * Real.exp (-b₁ * (N : ℝ) ^ βC)))
    (h𝕣 : 0 < 𝕣) (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ R.ℓ) (hχ : 0 ≤ R.χ)
    (hUV : R.U ⊆ R.V) (hc : 0 < R.c 𝕣) (hcℓ : 0 ≤ R.c (R.ℓ * 𝕣)) (hξ : 0 ≤ R.ξ)
    {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.U)
    (hH0 : ∀ᵐ ω ∂P, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0)
    (hH𝕫 : ∀ᵐ ω ∂P, H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫)
    (hHℓ : ∀ᵐ ω ∂P, H (R.ℓ * 𝕣) 𝕫 ω = circleAvg (h ω) (R.ℓ * 𝕣) 𝕫)
    (hLen : ∀ᵐ ω ∂P, (D (h ω)).IsLength ∧ ∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s))
    {ε β : ℝ} (hε : 0 < ε) (k : ℕ)
    (hloc : IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) 𝕫
      (min (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (tauR D h 𝕫 (2 * (R.ℓ * 𝕣)) ω))))
    (hk : k * ε ^ β ≤ a / regC2const R a) (N : ℕ) (hN : 1 ≤ N)
    (hNε : (N : ℝ) ^ (-βC) * p412bC R.ℓ a R.χ' ≤ ε ^ (2 * β))
    (hbr : ∀ᵐ ω ∂P, confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ⊆
      hitSetDD (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) :
    P (regEvent D P h H R 𝕣 a ∩ {ω | ((N : ℕ∞) : ℕ∞) <
        (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)).encard}) ≤
      ENNReal.ofReal (b₀ * Real.exp (-b₁ * (N : ℝ) ^ βC)) := by
  have hℓ : 0 < R.ℓ := lt_of_lt_of_le ha0 haℓ
  set Good : Set Ω := {ω | H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 ∧ H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 ∧
    H (R.ℓ * 𝕣) 𝕫 ω = circleAvg (h ω) (R.ℓ * 𝕣) 𝕫 ∧ (D (h ω)).IsLength ∧
    ∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)} with hGood
  set G := regEvent D P h H R 𝕣 a ∩ Good
  have hGood_ae : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [hH0, hH𝕫, hHℓ, hLen] with ω h1 h2 h3 h4 using ⟨h1, h2, h3, h4.1, h4.2⟩
  refine le_trans (measure_mono_ae ?_) (p412b_step1_k P h hT 𝕫 (mul_pos hℓ h𝕣)
    hε k hloc N hN hcℓ G ?_ hbr ?_ ?_ ?_)
  · filter_upwards [hGood_ae] with ω hω
    rintro ⟨hE, hX⟩
    exact ⟨⟨hE, hω⟩, hX⟩
  · filter_upwards [confRegH_ae_eq (ξ := R.ξ) (cc := R.c) (D := D) (P := P) (p := R.p)
      (χ := R.χ) (a := a) hHℓ] with ω hω
    rintro ⟨hE, -⟩
    have h7 := (gm_regEvent_mem.1 hE).2.2.2.2.2.2
    have : ω ∈ confRegH R.ξ R.c D P h H R.p R.χ 𝕫 (R.ℓ * 𝕣) a := by
      simp only [regC7, mem_iInter] at h7; exact h7 𝕫 h𝕫
    rw [← hω]; exact this
  · rintro ω ⟨hE, h1, h2, -, -, -⟩
    exact gm_S4_3 hE hc hξ h𝕣 hℓ ha0 ha1 hχ hUV h𝕫 h1 h2 hk
  · rintro ω ⟨hE, -, -, h3, hL, -⟩
    have hsc := p412b_scale_le_tau hE h𝕣 ha0 ha1 haℓ hχ hUV hc h𝕫 h3 hL
    have hτ0 : 0 ≤ tauR D h 𝕫 (R.ℓ * 𝕣) ω := Real.sInf_nonneg (fun _ hx => hx.1.le)
    have hN0 : 0 ≤ (N : ℝ) ^ (-βC) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    simp only [s4T, s4Unit]
    have : (N : ℝ) ^ (-βC) * scaleFac R.ξ R.c (h ω) (R.ℓ * 𝕣) 𝕫 ≤
        ε ^ (2 * β) * tauR D h 𝕫 (R.ℓ * 𝕣) ω :=
      calc (N : ℝ) ^ (-βC) * scaleFac R.ξ R.c (h ω) (R.ℓ * 𝕣) 𝕫
          ≤ (N : ℝ) ^ (-βC) * (p412bC R.ℓ a R.χ' * tauR D h 𝕫 (R.ℓ * 𝕣) ω) :=
            mul_le_mul_of_nonneg_left hsc hN0
        _ = ((N : ℝ) ^ (-βC) * p412bC R.ℓ a R.χ') * tauR D h 𝕫 (R.ℓ * 𝕣) ω := by ring
        _ ≤ ε ^ (2 * β) * tauR D h 𝕫 (R.ℓ * 𝕣) ω := mul_le_mul_of_nonneg_right hNε hτ0
    linarith
  · rintro ω ⟨hE, -, -, -, hL, hb⟩
    refine ⟨?_, hb _⟩
    obtain ⟨_, _, h3, _⟩ := gm_regEvent_mem.1 hE
    have hτ := p412b_tau_ge h3 h𝕣 ha0 haℓ hUV hc h𝕫 hL
    have hτ0 : 0 < tauR D h 𝕫 (R.ℓ * 𝕣) ω :=
      lt_of_lt_of_le (mul_pos (by positivity) (mul_pos hc (Real.exp_pos _))) hτ
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε.le β)
    simp only [s4S, s4Unit]
    nlinarith

/-- **GM (4.40), Step 1 count** (l. 2128–2131): union bound over `k ∈ [0, K]`. -/
theorem p412b_step1_union {D : DistC → ContMetric} {b₀ b₁ βC : ℝ} {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ) (R : RegPar)
    {𝕣 a : ℝ}
    (hT : ∀ (z₀ : ℂ) (Rr : ℝ), 0 < Rr → ∀ N : ℕ, 1 ≤ N →
      ∀ τ : Ω → ℝ, IsFilledBallStoppingTime D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      (∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ Rr ω) (tauR D h z₀ (2 * Rr) ω)) →
      P {ω | ω ∈ confReg R.ξ R.c D P h R.p R.χ z₀ Rr a ∧
          ((N : ℕ∞) : ℕ∞) < (hitSetLM (D (h ω)) z₀ (τ ω)
            (τ ω + (N : ℝ) ^ (-βC) * scaleFac R.ξ R.c (h ω) Rr z₀)).encard} ≤
        ENNReal.ofReal (b₀ * Real.exp (-b₁ * (N : ℝ) ^ βC)))
    (h𝕣 : 0 < 𝕣) (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ R.ℓ) (hχ : 0 ≤ R.χ)
    (hUV : R.U ⊆ R.V) (hc : 0 < R.c 𝕣) (hcℓ : 0 ≤ R.c (R.ℓ * 𝕣)) (hξ : 0 ≤ R.ξ)
    {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.U)
    (hH0 : ∀ᵐ ω ∂P, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0)
    (hH𝕫 : ∀ᵐ ω ∂P, H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫)
    (hHℓ : ∀ᵐ ω ∂P, H (R.ℓ * 𝕣) 𝕫 ω = circleAvg (h ω) (R.ℓ * 𝕣) 𝕫)
    (hLen : ∀ᵐ ω ∂P, (D (h ω)).IsLength ∧ ∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s))
    {ε β : ℝ} (hε : 0 < ε) (K : ℕ) (hK : (K : ℝ) * ε ^ β ≤ a / regC2const R a) (N : ℕ)
    (hN : 1 ≤ N) (hNε : (N : ℝ) ^ (-βC) * p412bC R.ℓ a R.χ' ≤ ε ^ (2 * β))
    (hbr : ∀ k ≤ K, ∀ᵐ ω ∂P,
      confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ⊆
      hitSetDD (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω))
    (hloc : ∀ k : ℕ, IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) 𝕫
      (min (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (tauR D h 𝕫 (2 * (R.ℓ * 𝕣)) ω)))) :
    P (regEvent D P h H R 𝕣 a ∩ {ω | ∃ k ≤ K, ((N : ℕ∞) : ℕ∞) <
        (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)).encard}) ≤
      (K + 1 : ENNReal) * ENNReal.ofReal (b₀ * Real.exp (-b₁ * (N : ℝ) ^ βC)) := by
  have hsub : regEvent D P h H R 𝕣 a ∩ {ω | ∃ k ≤ K, ((N : ℕ∞) : ℕ∞) <
        (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)).encard} ⊆
      ⋃ k ∈ Finset.range (K + 1), (regEvent D P h H R 𝕣 a ∩ {ω | ((N : ℕ∞) : ℕ∞) <
        (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)).encard}) := by
    rintro ω ⟨hE, k, hk, hcnt⟩
    exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le hk))) ⟨hE, hcnt⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hbd : ∀ k ∈ Finset.range (K + 1), P (regEvent D P h H R 𝕣 a ∩ {ω | ((N : ℕ∞) : ℕ∞) <
        (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)).encard}) ≤
      ENNReal.ofReal (b₀ * Real.exp (-b₁ * (N : ℝ) ^ βC)) := by
    intro k hk
    have hkK : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    refine p412b_step1_E P h H R hT h𝕣 ha0 ha1 haℓ hχ hUV hc hcℓ hξ h𝕫 hH0 hH𝕫 hHℓ hLen hε k
      (hloc k) ?_ N hN hNε (hbr k hkK)
    exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkK)
      (Real.rpow_nonneg hε.le β)) hK
  refine (Finset.sum_le_sum hbd).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; exact le_rfl

end LQGMetric.GM
