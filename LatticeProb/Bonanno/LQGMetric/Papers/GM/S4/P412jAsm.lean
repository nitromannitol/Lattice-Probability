/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412jAsm at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iGood
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412b440
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412jEDet
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412jComp

/-!
# P-assembly of GM Proposition 4.12 (D98 §4 item 5): open inputs and numerics

Source: GM (arXiv:1905.00383v3, `uniqueness-final.tex`) L4.15 Step 3–4, l. 2155–2199, and the
proof of Prop 4.12 (l. 2212–2276); D98 §2 (filtration `ℱ k`, Borel guard centres).

Open inputs of the assembly, as exact statements:
* `P412jCentres` — output of P-Qk (D98 §2, handoff P2-M2J2g §3): `2L` surely
  `σ(𝓑^•_{t_k}, h|)`-measurable centres on `∂𝓑^•_{t_k}` which, a.s. on `{#Conf_k ≤ L}`, cover the
  endpoints `𝒴_k` in the sense (∗) of `p412f_good_near` at scale `ε^κ𝕣`;
* `P412jBridge` — the D76 bridge `Conf_k ⊆ hitSetDD` a.s. (hypothesis `hbr` of `p412b_eq440`);
* `P412jGoodU` — `p412i_good_k` with its threshold `ε₁` chosen uniformly in `E, rr`, the space and
  `𝕣` (as `GMP4_12At` requires; the proved chain `gm_L4_22 → … → p412i_good_k` produces `ε₁` from
  deterministic exponent inequalities only, but states it after these binders).

Numerics (own routine arguments): `p412j_dyadic` (a dyadic `δ ∈ [18x, 36x]`), `p412j_small`,
`p412j_NC_le` (`N C₀ δ^α ≤ ε^{κα/4}` for `N = 2⌊ε^{-κα/4}⌋`, `δ ≤ 36ε^κ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **the D76 bridge** (CONF L2.4 proof, C:557–566): a.s. `Conf_k ⊆ hitSetDD` -/
def P412jBridge (D : DistC → ContMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (𝕫 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ), ∀ᵐ ω ∂P,
      confPts (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (s4T D h 𝕫 ℓ 𝕣 ε β k ω) ⊆
        hitSetDD (D (h ω)) 𝕫 (s4S D h 𝕫 ℓ 𝕣 ε β k ω) (s4T D h 𝕫 ℓ 𝕣 ε β k ω)

/-- **`p412i_good_k` with a uniform threshold** (`ε₁` before `E, rr`, the space and `𝕣`) -/
def P412jGoodU : Prop :=
  ∀ (R₀ : RegPar) {a β κ : ℝ}, 0 < a → a < 1 → a ≤ R₀.ℓ → 0 < R₀.χ → 0 < R₀.χ' → 0 < β →
    β < R₀.χ → 0 < R₀.lam 0 → R₀.lam 0 < R₀.lam 1 → R₀.lam 1 ≤ R₀.lam 2 →
    R₀.lam 2 ≤ R₀.lam 3 → 1 < R₀.lam 3 → 0 ≤ R₀.ν → R₀.U ⊆ R₀.V → 0 ≤ R₀.ξ →
    R₀.χ ≤ R₀.χ' → 0 < κ → β < κ * R₀.χ / 4 → κ * (R₀.χ' / R₀.χ) < R₀.χ / R₀.χ' →
    κ * (R₀.χ' / R₀.χ) < 1 →
  ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (E : ℝ → ℂ → Set DistC) (rr : ℝ → ℝ → ℕ → ℝ) (R : RegPar),
    R = { R₀ with E := E, rr := rr } →
  ∀ {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
    {H : ℝ → ℂ → Ω → ℝ} {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {𝕣 : ℝ},
    0 < 𝕣 → 0 < R.c 𝕣 →
  ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < ε₁ →
  ∀ m : ℕ, 18 * ((2 : ℝ)⁻¹ ^ n) ^ κ ≤ (2 : ℝ)⁻¹ ^ m → (2 : ℝ)⁻¹ ^ m ≤ 36 * ((2 : ℝ)⁻¹ ^ n) ^ κ →
  ∀ ω ∈ regEvent D P h H R 𝕣 a,
  ∀ 𝕫 ∈ rScale 𝕣 R.U, ∀ 𝕨 : ℂ, 4 * (R.ℓ * 𝕣) ≤ ‖𝕫 - 𝕨‖ →
  H 𝕣 0 ω = circleAvg (h ω) 𝕣 0 → H 𝕣 𝕫 ω = circleAvg (h ω) 𝕣 𝕫 →
  (D (h ω)).IsLength → (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) →
  (∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y) →
  (∀ k < ⌊R.μ * Real.logb 8 ((2 : ℝ)⁻¹ ^ n)⁻¹⌋₊,
    R.rr 𝕣 ((2 : ℝ)⁻¹ ^ n) k ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣) ((2 : ℝ)⁻¹ ^ n * 𝕣)) →
  IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) →
  ∀ k ≤ p4K R a ((2 : ℝ)⁻¹ ^ n) β,
  (⋃ x ∈ confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
      (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω),
      arcOf (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) x =
    frontier (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω))) →
  ∀ (N L : ℕ) (x : ℕ → Ω → ℂ) (G : ℕ → Set Ω),
  (∀ e ∈ p412fEndSet (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
      (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω), ∃ j < N, ∃ z : ℂ,
    p412eGoodZ (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) e z
      (((2 : ℝ)⁻¹ ^ n) ^ κ * 𝕣) ∧ dist z (x j ω) ≤ ((2 : ℝ)⁻¹ ^ n) ^ κ * 𝕣) →
  (∀ j, ω ∈ G j → confRK R.ξ R.c D P h R.p 𝕣 ((2 : ℝ)⁻¹ ^ m)
        (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) ω ≤
        Metric.ediam (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) →
      ∀ (y : ℂ) (Q : ℝ → ℂ) (Lq : ℝ),
        y ∉ enbhd (confRK R.ξ R.c D P h R.p 𝕣 ((2 : ℝ)⁻¹ ^ m)
          (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) ω)
          (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) →
        IsGeodesicL (D (h ω)) Q Lq 𝕫 y → ∀ u ∈ Icc 0 Lq,
          Q u ∉ ball (x j ω) ((2 : ℝ)⁻¹ ^ m * 𝕣) \
            filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)) →
  ω ∈ (⋂ j ∈ Finset.range N, G j) ∪
        {ω | ENNReal.ofReal (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β (k + 1) ω) <
          confSigma R.ξ R.c D P h R.p 𝕫 𝕣 ((2 : ℝ)⁻¹ ^ m)
            (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω) ω} ∪
        {ω | ((L : ℕ∞) : ℕ∞) < (confPts (D (h ω)) 𝕫
          (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
          (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)).encard} →
  (confPts (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)
      (s4T D h 𝕫 R.ℓ 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω)).encard ≤ L →
  (zkE D sel h R 𝕫 𝕨 𝕣 ((2 : ℝ)⁻¹ ^ n) β k ω).Nonempty

/-- a dyadic number in `[18x, 36x]` for `0 < x ≤ 1/36` -/
theorem p412j_dyadic {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1 / 36) :
    ∃ m : ℕ, 18 * x ≤ (2 : ℝ)⁻¹ ^ m ∧ (2 : ℝ)⁻¹ ^ m ≤ 36 * x := by
  have hy : 1 ≤ (36 * x)⁻¹ := by
    rw [one_le_inv₀ (by positivity)]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hy (by norm_num : (1 : ℝ) < 2)
  have h36 : 0 < 36 * x := by positivity
  have h2n : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
  have e1 : (2 : ℝ)⁻¹ ^ (n + 1) = (2 ^ n)⁻¹ / 2 := by
    rw [inv_pow, pow_succ, mul_inv]; ring
  have k1 : 36 * x ≤ (2 ^ n)⁻¹ := (le_inv_comm₀ h2n h36).1 hn1
  have k2 : ((2 : ℝ) ^ (n + 1))⁻¹ < 36 * x := (inv_lt_comm₀ h36 (pow_pos two_pos _)).1 hn2
  refine ⟨n + 1, ?_, ?_⟩
  · rw [e1]; linarith
  · rw [inv_pow]; exact k2.le

/-- the smallness conditions on `ε` used in the assembly -/
theorem p412j_small {κ α C₀ : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hC₀ : 0 < C₀) :
    ∃ ε₄ : ℝ, 0 < ε₄ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₄, ε < 1 ∧ ε ^ κ < 1 / 36 ∧
      2 * C₀ * 36 ^ α * ε ^ (κ * α / 2) ≤ 1 := by
  have t1 := (Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto
  rw [Real.zero_rpow hκ.ne'] at t1
  have t2 := (Real.continuousAt_rpow_const 0 (κ * α / 2) (Or.inr (by positivity))).tendsto
  rw [Real.zero_rpow (by positivity)] at t2
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ κ < 1 / 36 :=
    (t1.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num))
  have hK : 0 < 2 * C₀ * (36 : ℝ) ^ α := by positivity
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (κ * α / 2) ≤ (2 * C₀ * 36 ^ α)⁻¹ :=
    (t2.mono_left nhdsWithin_le_nhds).eventually (Iic_mem_nhds (by positivity))
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨ε₄, hε₄, H⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 ((e1.and e2).and e3)
  refine ⟨ε₄, hε₄, fun ε hε => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := H hε
  refine ⟨h3.2, h1, ?_⟩
  calc 2 * C₀ * 36 ^ α * ε ^ (κ * α / 2) ≤ 2 * C₀ * 36 ^ α * (2 * C₀ * 36 ^ α)⁻¹ :=
        mul_le_mul_of_nonneg_left h2 hK.le
    _ = 1 := mul_inv_cancel₀ hK.ne'

/-- `N C₀ δ^α ≤ ε^{κα/4}` for `N = 2⌊ε^{-κα/4}⌋`, `δ ≤ 36 ε^κ`, and `C₀ δ^α < 1` -/
theorem p412j_NC_le {κ α C₀ ε δ : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hC₀ : 0 < C₀) (hε : 0 < ε)
    (hε1 : ε < 1) (hδ : 0 < δ) (hδ36 : δ ≤ 36 * ε ^ κ)
    (hsm : 2 * C₀ * 36 ^ α * ε ^ (κ * α / 2) ≤ 1) :
    ((2 * ⌊ε ^ (-(κ * α / 4))⌋₊ : ℕ) : ℝ) * (C₀ * δ ^ α) ≤ ε ^ (κ * α / 4) ∧
      C₀ * δ ^ α < 1 := by
  have hL : (⌊ε ^ (-(κ * α / 4))⌋₊ : ℝ) ≤ ε ^ (-(κ * α / 4)) :=
    Nat.floor_le (Real.rpow_nonneg hε.le _)
  have hδα : δ ^ α ≤ 36 ^ α * ε ^ (κ * α) := by
    calc δ ^ α ≤ (36 * ε ^ κ) ^ α := Real.rpow_le_rpow hδ.le hδ36 hα.le
      _ = 36 ^ α * ε ^ (κ * α) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le]
  have key : ε ^ (-(κ * α / 4)) * ε ^ (κ * α) = ε ^ (κ * α / 2) * ε ^ (κ * α / 4) := by
    rw [← Real.rpow_add hε, ← Real.rpow_add hε]; ring_nf
  have hpos : 0 ≤ C₀ * δ ^ α := by positivity
  have hq1 : ε ^ (κ * α / 2) ≤ 1 := Real.rpow_le_one hε.le hε1.le (by positivity)
  constructor
  · push_cast
    calc (2 * (⌊ε ^ (-(κ * α / 4))⌋₊ : ℝ)) * (C₀ * δ ^ α)
        ≤ (2 * ε ^ (-(κ * α / 4))) * (C₀ * (36 ^ α * ε ^ (κ * α))) :=
          mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hδα hC₀.le) hpos
            (by positivity)
      _ = (2 * C₀ * 36 ^ α * ε ^ (κ * α / 2)) * ε ^ (κ * α / 4) := by
          rw [show (2 * ε ^ (-(κ * α / 4))) * (C₀ * (36 ^ α * ε ^ (κ * α))) =
            2 * C₀ * 36 ^ α * (ε ^ (-(κ * α / 4)) * ε ^ (κ * α)) by ring, key]; ring
      _ ≤ 1 * ε ^ (κ * α / 4) := mul_le_mul_of_nonneg_right hsm (by positivity)
      _ = ε ^ (κ * α / 4) := one_mul _
  · have e : ε ^ (κ * α) = ε ^ (κ * α / 2) * ε ^ (κ * α / 2) := by
      rw [← Real.rpow_add hε]; ring_nf
    have h2 : 0 ≤ C₀ * 36 ^ α * ε ^ (κ * α / 2) := by positivity
    calc C₀ * δ ^ α ≤ C₀ * (36 ^ α * ε ^ (κ * α)) := mul_le_mul_of_nonneg_left hδα hC₀.le
      _ = (C₀ * 36 ^ α * ε ^ (κ * α / 2)) * ε ^ (κ * α / 2) := by rw [e]; ring
      _ ≤ (C₀ * 36 ^ α * ε ^ (κ * α / 2)) * 1 := mul_le_mul_of_nonneg_left hq1 h2
      _ < 1 := by nlinarith

end LQGMetric.GM
