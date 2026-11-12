/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412U2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412U1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eCore
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eExt
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bRate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fIn

/-!
# The deterministic core of GM Prop 4.12 with a uniform threshold (P2-M2J2i, part 2)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, L4.15 Step 3 (l. 2155–2199) and the
proof of Prop 4.12 (l. 2212–2276). Primed copies (`…U`, same proofs, `∃ ε₁` before `R`, the space
and `𝕣`; see P412U1.lean) of `p412e_core` (P412eCore), `p412e_core_noHit` (P412eAsm) and
`p412f_times` (P412fIn).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

variable {ξN : ℝ} {cN : ℝ → ℝ} {pN : CONFParams} {χN χ'N μN νN : ℝ} {lamN : Fin 5 → ℝ} {ℓN : ℝ}
  {UN VN : Set ℂ}

theorem p412e_coreU
    {a β : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ ℓN) (hχ : 0 < χN) (hχ' : 0 < χ'N)
    (hβ : 0 < β) (hβχ : β < χN) (hl0 : 0 < lamN 0) (hl01 : lamN 0 < lamN 1)
    (hl12 : lamN 1 ≤ lamN 2) (hl23 : lamN 2 ≤ lamN 3) (hlam : 1 < lamN 3)
    (hUV : UN ⊆ VN) (hξ : 0 ≤ ξN) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : RegPar, RegNum R ξN cN pN χN χ'N μN νN lamN ℓN UN VN →
    ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {𝕣 : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < ε₁ → (2 : ℝ)⁻¹ ^ n ≤ a →
    ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
    (∀ k < ⌊R.μ * Real.logb 8 ((2 : ℝ)⁻¹ ^ n)⁻¹⌋₊,
      R.rr 𝕣 ((2 : ℝ)⁻¹ ^ n) k ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣) ((2 : ℝ)⁻¹ ^ n * 𝕣)) →
    ∀ k ≤ p4K R a ((2 : ℝ)⁻¹ ^ n) β,
    cthickening (4 * R.lam 3 * (2 : ℝ)⁻¹ ^ n * 𝕣)
      (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) ⊆ regRegion R 𝕣 →
    ∀ (Pc : ℝ → ℂ) (L : ℝ), 0 ≤ L → ContinuousOn Pc (Icc 0 L) → Pc 0 = 𝕫 →
    ∀ d₀ : ℝ,
    R.lam 3 * (2 : ℝ)⁻¹ ^ n * 𝕣 ≤
      d₀ - 2 * (R.lam 0 * ((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣 / 4) →
    d₀ + 2 * (R.lam 0 * ((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣 / 4) ≤
      2 * R.lam 3 * (2 : ℝ)⁻¹ ^ n * 𝕣 →
    d₀ < infDist (Pc L) (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) →
    ∀ x₀ ∈ confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
      (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω),
    ∀ ρ : ℝ,
    (∀ u ∈ Icc 0 L,
      Pc u ∉ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) →
      ∀ v ∈ frontier (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) \
          arcOf (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) x₀,
        ENNReal.ofReal ρ ≤
          dU (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω))ᶜ (Pc u) v) →
    (∀ r ∈ Ioc 0 ((2 : ℝ)⁻¹ ^ n * 𝕣),
      2 * (𝕣 * (⌈16 * Real.pi * R.lam 3⌉₊ * ((2 : ℝ)⁻¹ ^ n / 4) ^ R.χ) ^ (1 / R.χ')) +
          8 * R.lam 3 * ((2 : ℝ)⁻¹ ^ n * 𝕣) + 2 * r < ρ - 2 * (R.lam 1 * r)) →
    ∃ z r, (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω))
        (R.lam 0) (R.lam 3) ((2 : ℝ)⁻¹ ^ n) R.ν 𝕣 (p4Rads R 𝕣 ((2 : ℝ)⁻¹ ^ n)) ∧
      h ω ∈ R.E r z ∧
      stabCond (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
        (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) z r ∧
      ∃ u ∈ Icc 0 L, Pc u ∈ ball z (R.lam 1 * r) := by
  obtain ⟨ε₁, hε₁, HS⟩ := p412b_stab_of_extU (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)
    ha0 ha1
    haℓ hχ hχ' hβ hβχ hlam hUV  hξ
  refine ⟨ε₁, hε₁, ?_⟩
  intro R hRN Ω _ D P h H 𝕣 h𝕣 hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hRN
  replace HS := HS R (regNum_self R) (D := D) (P := P) (h := h) (H := H) h𝕣 hc
  try simp only [regC2N_eq] at *
  refine fun n hn hna ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod hrr k hk hKreg4 Pc L hL0 hPc hP0
    d₀ hlow hup hPL x₀ hx₀ ρ hext hsmall => ?_
  set ε := (2 : ℝ)⁻¹ ^ n with hεdef
  have hε0 : 0 < ε := by positivity
  set t := s4T D h 𝕫 R.ℓ 𝕣 ε β k ω with htdef
  set K := filledBall (D (h ω)) 𝕫 t with hKdef
  have hKc : IsClosed K := gm_filledBall_isClosed _ _ _
  -- `t > 0`
  obtain ⟨_, _, h3, _⟩ := gm_regEvent_mem.1 hω
  have hτ := p412b_tau_ge h3 h𝕣 ha0 haℓ hUV hc h𝕫 hL
  have hτ0 : 0 < tauR D h 𝕫 (R.ℓ * 𝕣) ω :=
    lt_of_lt_of_le (mul_pos (by positivity) (mul_pos hc (Real.exp_pos _))) hτ
  have ht0 : 0 < t := by
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε0.le β)
    have h2 : 0 ≤ ε ^ (2 * β) * tauR D h 𝕫 (R.ℓ * 𝕣) ω :=
      mul_nonneg (Real.rpow_nonneg hε0.le _) hτ0.le
    simp only [htdef, s4T, s4S, s4Unit]
    nlinarith
  have hKreg : cthickening (2 * R.lam 3 * ε * 𝕣) K ⊆ regRegion R 𝕣 :=
    (cthickening_mono (by nlinarith [mul_pos hε0 h𝕣]) K).trans hKreg4
  have hPK : Pc 0 ∈ K := hP0 ▸ jo_mem_filledBall_self ht0
  -- (a): `P` enters a good ball
  obtain ⟨z, r, hcand, hE, u, hu, hPu⟩ := p412b_S4_6 (gm_regEvent_mem.1 hω).2.2.2.2.1 hna h𝕣
    hl0 hl01 (fun j hj => (hrr j hj).1) hKc hKreg hL0 hPc hPK hlow hup hPL
  have hrIcc : r ∈ Icc (ε ^ (1 + R.ν) * 𝕣) (ε * 𝕣) := by
    obtain ⟨j, hj, rfl⟩ := hcand.2.2.1
    exact hrr j hj
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hrIcc.1
  have hl1 : 0 < R.lam 1 := hl0.trans hl01
  -- `B_{λ₂r}(z) ∩ 𝓑^•_{t_k} = ∅`
  have hlr : R.lam 1 * r ≤ R.lam 3 * ε * 𝕣 := by
    have := mul_le_mul (hl12.trans hl23) hrIcc.2 hr0.le (by linarith)
    linarith
  have hball := p412b_ball_disj_of_cand hKc hcand hlr
  have hPuK : Pc u ∉ K := fun h' => disjoint_left.1 hball hPu h'
  -- transfer (4.41) to the centre and apply the final step
  have hext' := p412b_ext_transfer ht0 hL (hbd t) hball hPu (hext u hu hPuK)
  refine ⟨z, r, hcand, hE, ?_, u, hu, hPu⟩
  -- `hfin` (DEC-86 (3)): `∂B_r(z) ⊆ B_{4ℓ𝕣}(𝕣V)`, then `regC3`
  have hfin : ∀ (x : ℂ) (Q : ℝ → ℂ) (T : ℝ), IsAvoidGeod (D (h ω)) 𝕫 z r x Q T →
      (D (h ω)).len Q 0 T ≠ ⊤ := by
    intro x Q T hQ
    refine p412e_hfin_regC3 h𝕣 ha0 hχ hc h3 hL hr0 hQ (hKreg4 ?_)
    exact p412e_sphere_mem_cthickening hKc hlam hε0 h𝕣 hcand hrIcc.2 hQ.2.2.2.2.1
  exact HS ε ⟨hε0, hn⟩ ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod k hk z r _ hcand ⟨hr0, hrIcc.2⟩
    hfin x₀ hx₀ z (mem_closedBall_self hr0.le) (ρ - 2 * (R.lam 1 * r)) hext'
    (hsmall r ⟨hr0, hrIcc.2⟩)


theorem p412e_core_noHitU
    {a β : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ ℓN) (hχ : 0 < χN) (hχ' : 0 < χ'N)
    (hβ : 0 < β) (hβχ : β < χN) (hl0 : 0 < lamN 0) (hl01 : lamN 0 < lamN 1)
    (hl12 : lamN 1 ≤ lamN 2) (hl23 : lamN 2 ≤ lamN 3) (hlam : 1 < lamN 3)
    (hUV : UN ⊆ VN) (hξ : 0 ≤ ξN) (hχχ : χN ≤ χ'N) {κ : ℝ}
    (he1 : κ * (χ'N / χN) < χN / χ'N) (he2 : κ * (χ'N / χN) < 1) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : RegPar, RegNum R ξN cN pN χN χ'N μN νN lamN ℓN UN VN →
    ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {𝕣 : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < ε₁ → (2 : ℝ)⁻¹ ^ n ≤ a →
    ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
    (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
    (∀ k < ⌊R.μ * Real.logb 8 ((2 : ℝ)⁻¹ ^ n)⁻¹⌋₊,
      R.rr 𝕣 ((2 : ℝ)⁻¹ ^ n) k ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣) ((2 : ℝ)⁻¹ ^ n * 𝕣)) →
    ∀ k ≤ p4K R a ((2 : ℝ)⁻¹ ^ n) β,
    cthickening (4 * R.lam 3 * (2 : ℝ)⁻¹ ^ n * 𝕣)
      (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) ⊆ regRegion R 𝕣 →
    ∀ (Pc : ℝ → ℂ) (L : ℝ) (𝕨 : ℂ), IsGeodesicL (D (h ω)) Pc L 𝕫 𝕨 →
    𝕨 ∉ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) → s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω < L →
    ∀ d₀ : ℝ,
    R.lam 3 * (2 : ℝ)⁻¹ ^ n * 𝕣 ≤
      d₀ - 2 * (R.lam 0 * ((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣 / 4) →
    d₀ + 2 * (R.lam 0 * ((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣 / 4) ≤
      2 * R.lam 3 * (2 : ℝ)⁻¹ ^ n * 𝕣 →
    d₀ < infDist (Pc L) (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) →
    ∀ x₀ ∈ confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
      (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω),
    Pc (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) ∈ arcOf (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) x₀ →
    -- smallness for L4.13′ with `ε' = (ε^κ/2)^{χ'/χ}`
    ((((2 : ℝ)⁻¹ ^ n) ^ κ / 2) ^ (R.χ' / R.χ)) ≤ 1 → ((((2 : ℝ)⁻¹ ^ n) ^ κ / 2) ^ (R.χ' / R.χ)) ≤ a → ((((2 : ℝ)⁻¹ ^ n) ^ κ / 2) ^ (R.χ' / R.χ)) ^ R.χ < a ^ R.χ' →
    cthickening (((((2 : ℝ)⁻¹ ^ n) ^ κ / 2) ^ (R.χ' / R.χ)) * 𝕣) (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) ⊆ regRegion R 𝕣 →
    (∀ u ∈ Icc (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) L,
      u ≤ s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω + scaleFac R.ξ R.c (h ω) 𝕣 0 * ((((2 : ℝ)⁻¹ ^ n) ^ κ / 2) ^ (R.χ' / R.χ)) ^ R.χ → Pc u ∈ regRegion R 𝕣) →
    -- `F = 𝓑^•_{s_{k+1}}`, the exit time `b` of `F`, the endpoints `E`, the centres `z_e`, `G_e`
    ∀ F : Set ℂ, IsClosed F → Bornology.IsBounded F → IsConnected Fᶜ →
    cthickening (16 * (2 * ((((2 : ℝ)⁻¹ ^ n) ^ κ / 2) ^ (R.χ' / R.χ)) ^ (R.χ / R.χ') * 𝕣)) (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) ⊆ F →
    ∀ b : ℝ, s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω < b → b ≤ L → Pc b ∉ F →
    ∀ (E : Set ℂ) (zf : ℂ → ℂ),
    closure (arcOf (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) x₀) ∩
        closure (frontier (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) \ arcOf (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) x₀) ⊆ E →
    (∀ e ∈ E, p412eGoodZ (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) e (zf e) (2 * ((((2 : ℝ)⁻¹ ^ n) ^ κ / 2) ^ (R.χ' / R.χ)) ^ (R.χ / R.χ') * 𝕣)) →
    (∀ e ∈ E, ∀ u ∈ Ioc (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) b, Pc u ∉ ball (zf e) (17 * (2 * ((((2 : ℝ)⁻¹ ^ n) ^ κ / 2) ^ (R.χ' / R.χ)) ^ (R.χ / R.χ') * 𝕣))) →
    ∃ z r, (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω))
        (R.lam 0) (R.lam 3) ((2 : ℝ)⁻¹ ^ n) R.ν 𝕣 (p4Rads R 𝕣 ((2 : ℝ)⁻¹ ^ n)) ∧
      h ω ∈ R.E r z ∧
      stabCond (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
        (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) z r ∧
      ∃ u ∈ Icc 0 L, Pc u ∈ ball z (R.lam 1 * r) := by
  obtain ⟨ε₁, hε₁, HC⟩ := p412e_coreU (ξN := ξN) (cN := cN) (pN := pN)
    (χN := χN) (χ'N := χ'N) (μN := μN) (νN := νN) (lamN := lamN) (ℓN := ℓN) (UN := UN) (VN := VN)
    ha0 ha1 haℓ hχ
    hχ' hβ hβχ hl0 hl01 hl12 hl23 hlam hUV  hξ
  obtain ⟨ε₂, hε₂, HS⟩ := p412b_small_A' (lam := lamN 3) (lam2 := lamN 1)
    (N := (⌈16 * Real.pi * lamN 3⌉₊ : ℝ)) hχ hχ' he1 he2 (Nat.cast_nonneg _)
    (hl0.trans hl01).le
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro R hRN Ω _ D P h H 𝕣 h𝕣 hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hRN
  replace HC := HC R (regNum_self R) (D := D) (P := P) (h := h) (H := H) h𝕣 hc
  try simp only [regC2N_eq] at *
  refine fun n hn hna ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod hrr k hk hKreg4
    Pc L 𝕨 hPg h𝕨 htL d₀ hlow hup hPL x₀ hx₀ hPI hε1 hεa hsm hKreg' hreg' F hF hFb hFc hKF b htb
    hbL hPb E zf hE hz hnohit => ?_
  set ε := (2 : ℝ)⁻¹ ^ n with hεdef
  have hε0 : 0 < ε := by positivity
  set t := s4T D h 𝕫 R.ℓ 𝕣 ε β k ω with htdef
  -- `t > 0` (as in `p412b_core`)
  obtain ⟨_, _, h3, _⟩ := gm_regEvent_mem.1 hω
  have hτ := p412b_tau_ge h3 h𝕣 ha0 haℓ hUV hc h𝕫 hL
  have hτ0 : 0 < tauR D h 𝕫 (R.ℓ * 𝕣) ω :=
    lt_of_lt_of_le (mul_pos (by positivity) (mul_pos hc (Real.exp_pos _))) hτ
  have ht0 : 0 < t := by
    have h1 : 0 ≤ (k : ℝ) * ε ^ β := mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg hε0.le β)
    have h2 : 0 ≤ ε ^ (2 * β) * tauR D h 𝕫 (R.ℓ * 𝕣) ω :=
      mul_nonneg (Real.rpow_nonneg hε0.le _) hτ0.le
    simp only [htdef, s4T, s4S, s4Unit]
    nlinarith
  have hε'0 : 0 < (ε ^ κ / 2) ^ (R.χ' / R.χ) := by positivity
  have hext := p412e_ext_of_noHit h𝕣 ha0 hχ hχχ hc (gm_regEvent_mem.1 hω).2.2.1 hL hPg ht0 htL
    (hbd t) h𝕨 hPI hε'0 hε1 hεa hsm hKreg' hreg' hF hFb hFc hKF htb hbL hPb hE hz hnohit
  exact HC n (hn.trans_le (min_le_left _ _)) hna ω hω 𝕫 h𝕫 hH0 hH𝕫 hL hbd hgeod hrr k hk hKreg4
    Pc L hPg.1 (gm_geodL_continuousOn hPg) hPg.2.1 d₀ hlow hup hPL x₀ hx₀ _ hext
    (fun r hr => HS ε ⟨hε0, hn.trans_le (min_le_right _ _)⟩ 𝕣 h𝕣 r hr)


theorem p412f_timesU
    {a β κ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (haℓ : a ≤ ℓN) (hχ : 0 < χN)
    (hχχ : χN ≤ χ'N) (hβ : 0 < β) (hκ : 0 < κ) (hβκ : β < κ * χN / 2) (hUV : UN ⊆ VN)
    (hξ : 0 ≤ ξN) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ R : RegPar, RegNum R ξN cN pN χN χ'N μN νN lamN ℓN UN VN →
    ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {𝕣 : ℝ}, 0 < 𝕣 → 0 < R.c 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) ε₁, ∀ ω ∈ regEvent D P h H R 𝕣 a,
    ∀ 𝕫 ∈ rScale 𝕣 R.U, H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
    (D (h ω)).IsLength → ∀ k ≤ p4K R a ε β,
      s4T D h 𝕫 R.ℓ 𝕣 ε β k ω + (17 * ε ^ κ) ^ R.χ * scaleFac R.ξ R.c (h ω) 𝕣 0 <
          s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω ∧
      s4T D h 𝕫 R.ℓ 𝕣 ε β k ω + scaleFac R.ξ R.c (h ω) 𝕣 0 * (ε ^ κ / 2) ^ R.χ' <
          s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω ∧
      0 < s4T D h 𝕫 R.ℓ 𝕣 ε β k ω ∧
      filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) ⊆ ball 𝕫 (2 * (R.ℓ * 𝕣)) ∧
      filledBall (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω) ⊆ ball 𝕫 (3 * (R.ℓ * 𝕣)) ∧
      s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω ≤ tauR D h 𝕫 (2 * (R.ℓ * 𝕣)) ω := by
  have hℓ : 0 < ℓN := lt_of_lt_of_le ha0 haℓ
  have hc2 : 0 < regC2N ℓN ξN a := by unfold regC2N; positivity
  have ha2 : 0 < (a / 2) ^ χ'N := by positivity
  have hgapev := gm_small_gap hβ hβκ
    (show 0 < ((17 : ℝ) ^ χN + 1) / (a / 2) ^ χ'N by positivity)
  have hβev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ β ≤ a / regC2N ℓN ξN a := by
    have := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto
    rw [Real.zero_rpow hβ.ne'] at this
    exact (this.mono_left nhdsWithin_le_nhds).eventually (Iic_mem_nhds (by positivity))
  have hlin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨ε₁, hε₁, hε₁'⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset).1 ((hgapev.and hβev).and hlin)
  refine ⟨ε₁, hε₁, ?_⟩
  intro R hRN Ω _ D P h H 𝕣 h𝕣 hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hRN
  try simp only [regC2N_eq] at *
  intro ε hε ω hω 𝕫 h𝕫 hH0 hH𝕫 hL k hk
  obtain ⟨⟨hgap0, hεβ⟩, hε01⟩ := hε₁' hε
  have hε0 : 0 < ε := hε01.1
  have hε1 : ε < 1 := hε01.2
  obtain ⟨_, _, h3, _, _, _, _⟩ := gm_regEvent_mem.1 hω
  set S := scaleFac R.ξ R.c (h ω) 𝕣 0 with hSdef
  have hS : 0 < S := mul_pos hc (Real.exp_pos _)
  set τ := tauR D h 𝕫 (R.ℓ * 𝕣) ω with hτdef
  have hτ : (a / 2) ^ R.χ' * S ≤ τ := p412b_tau_ge h3 h𝕣 ha0 haℓ hUV hc h𝕫 hL
  have hτ0 : 0 < τ := lt_of_lt_of_le (mul_pos ha2 hS) hτ
  set t := s4T D h 𝕫 R.ℓ 𝕣 ε β k ω with htdef
  set s' := s4S D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω with hs'def
  have hεβ0 : 0 ≤ ε ^ β := (Real.rpow_pos_of_pos hε0 _).le
  have hτt : τ ≤ t := by
    have := gm_s4S_le_s4T (D := D) (h := h) (𝕫 := 𝕫) (ℓ := R.ℓ) (𝕣 := 𝕣) (β := β) hε0 k ω
    have h1 : τ ≤ s4S D h 𝕫 R.ℓ 𝕣 ε β k ω := by
      simp only [s4S, s4Unit]; rw [← hτdef, mul_add, mul_one]
      have := mul_nonneg hτ0.le (mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hεβ0)
      linarith
    linarith
  have ht0 : 0 < t := lt_of_lt_of_le hτ0 hτt
  have hs't : s' - t = τ * (ε ^ β - ε ^ (2 * β)) := by
    simp only [hs'def, htdef, s4T, s4S, s4Unit]; rw [← hτdef]; push_cast; ring
  have hdiff0 : 0 < ε ^ β - ε ^ (2 * β) :=
    lt_of_le_of_lt (by positivity) hgap0
  -- `C ε^{κχ/2} S < s' − t` with `C = 17^χ + 1`
  have hgapS : ((17 : ℝ) ^ R.χ + 1) * ε ^ (κ * R.χ / 2) * S < s' - t := by
    have h1 : ((17 : ℝ) ^ R.χ + 1) * ε ^ (κ * R.χ / 2) <
        (a / 2) ^ R.χ' * (ε ^ β - ε ^ (2 * β)) := by
      have := mul_lt_mul_of_pos_left hgap0 ha2
      rwa [← mul_assoc, mul_div_cancel₀ _ ha2.ne'] at this
    rw [hs't]
    calc ((17 : ℝ) ^ R.χ + 1) * ε ^ (κ * R.χ / 2) * S
        < (a / 2) ^ R.χ' * (ε ^ β - ε ^ (2 * β)) * S := mul_lt_mul_of_pos_right h1 hS
      _ = (a / 2) ^ R.χ' * S * (ε ^ β - ε ^ (2 * β)) := by ring
      _ ≤ τ * (ε ^ β - ε ^ (2 * β)) := mul_le_mul_of_nonneg_right hτ hdiff0.le
  have hεκ0 : 0 < ε ^ κ := Real.rpow_pos_of_pos hε0 _
  have hεκ1 : ε ^ κ ≤ 1 := Real.rpow_le_one hε0.le hε1.le hκ.le
  have hpow1 : (17 * ε ^ κ) ^ R.χ ≤ (17 : ℝ) ^ R.χ * ε ^ (κ * R.χ / 2) := by
    rw [Real.mul_rpow (by norm_num) hεκ0.le, ← Real.rpow_mul hε0.le]
    refine mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by nlinarith)) (by positivity)
  have hpow2 : (ε ^ κ / 2) ^ R.χ' ≤ ε ^ (κ * R.χ / 2) := by
    calc (ε ^ κ / 2) ^ R.χ' ≤ (ε ^ κ) ^ R.χ' :=
          Real.rpow_le_rpow (by positivity) (by linarith) (hχ.le.trans hχχ)
      _ = ε ^ (κ * R.χ') := by rw [← Real.rpow_mul hε0.le]
      _ ≤ ε ^ (κ * R.χ / 2) :=
          Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by nlinarith)
  have h17 : 1 ≤ (17 : ℝ) ^ R.χ := Real.one_le_rpow (by norm_num) hχ.le
  have hepos : 0 ≤ ε ^ (κ * R.χ / 2) := (Real.rpow_pos_of_pos hε0 _).le
  have hA : t + (17 * ε ^ κ) ^ R.χ * S < s' := by
    have := mul_le_mul_of_nonneg_right hpow1 hS.le
    nlinarith
  have hB : t + S * (ε ^ κ / 2) ^ R.χ' < s' := by
    have h1 := mul_le_mul_of_nonneg_left hpow2 hS.le
    have h2 : S * ε ^ (κ * R.χ / 2) ≤ ((17 : ℝ) ^ R.χ + 1) * ε ^ (κ * R.χ / 2) * S := by
      nlinarith [mul_nonneg hS.le hepos]
    linarith
  have hk1 := p412f_succ_le hε0 hc2 ha0 hεβ hk
  have hs'2 : s' ≤ tauR D h 𝕫 (2 * (R.ℓ * 𝕣)) ω :=
    gm_S4_3 hω hc hξ h𝕣 hℓ ha0 ha1 hχ.le hUV h𝕫 hH0 hH𝕫 hk1
  have hts' : t < s' := by linarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < 17 ^ R.χ + 1)
    (Real.rpow_pos_of_pos hε0 (κ * R.χ / 2))) hS]
  refine ⟨hA, hB, ht0, gm_filledBall_subset_ball_of_lt_tauR ht0 (lt_of_lt_of_le hts' hs'2),
    gm_filledBall_s_subset_ball R h𝕣 ha0 ha1 haℓ hχ.le hUV hc hξ hε0 hω h𝕫 hH0 hH𝕫 hk1, hs'2⟩

end LQGMetric.GM
