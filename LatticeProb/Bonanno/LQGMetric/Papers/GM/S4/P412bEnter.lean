/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412bEnter at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodS46
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodP412

/-!
# GM.S4.6 on `ℰ_𝕣`: the geodesic enters a good ball (P4.12 assembly, piece (a))

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Proposition 4.12,
l. 2231–2236. `gm_S4_6_det` (ManyGoodS46.lean) is the deterministic statement with an abstract
covering hypothesis; here the covering is supplied by condition 5 of `ℰ_𝕣` (`regC5`) at a dyadic
`ε = 2^{-n} ≤ a`, with `Rads = p4Rads` (the radii of T4.2 (1)) and `Good z r = E_r(z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **GM.S4.6 on condition 5** (l. 2231–2236): if condition 5 of `ℰ_𝕣` holds at
`ε = 2^{-n} ≤ a`, the `2λ₄ε𝕣`-neighbourhood of `K` (`= 𝓑^•_{t_k}`) lies in the region of
condition 5, and `P` runs from `K` to distance `> d₀` from `K`, then `P` enters `B_{λ₂r}(z)`
for some `(z, r) ∈ 𝒵_k` with `E_r(z)`. -/
theorem p412b_S4_6 {Ω : Type} {h : Ω → DistC} {R : RegPar} {𝕣 a : ℝ} {ω : Ω}
    (hω : ω ∈ regC5 h R 𝕣 a) {n : ℕ} (hn : (2 : ℝ)⁻¹ ^ n ≤ a) (h𝕣 : 0 < 𝕣)
    (hl0 : 0 < R.lam 0) (hl01 : R.lam 0 < R.lam 1)
    (hrr : ∀ k < ⌊R.μ * Real.logb 8 ((2 : ℝ)⁻¹ ^ n)⁻¹⌋₊,
      ((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣 ≤ R.rr 𝕣 ((2 : ℝ)⁻¹ ^ n) k)
    {K : Set ℂ} (hK : IsClosed K)
    (hKreg : cthickening (2 * R.lam 3 * (2 : ℝ)⁻¹ ^ n * 𝕣) K ⊆ regRegion R 𝕣)
    {P : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hPc : ContinuousOn P (Icc 0 L)) (hP0 : P 0 ∈ K)
    {d₀ : ℝ}
    (hlow : R.lam 3 * (2 : ℝ)⁻¹ ^ n * 𝕣 ≤
      d₀ - 2 * (R.lam 0 * ((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣 / 4))
    (hup : d₀ + 2 * (R.lam 0 * ((2 : ℝ)⁻¹ ^ n) ^ (1 + R.ν) * 𝕣 / 4) ≤
      2 * R.lam 3 * (2 : ℝ)⁻¹ ^ n * 𝕣)
    (hPL : d₀ < infDist (P L) K) :
    ∃ z r, (z, r) ∈ candSet K (R.lam 0) (R.lam 3) ((2 : ℝ)⁻¹ ^ n) R.ν 𝕣
        (p4Rads R 𝕣 ((2 : ℝ)⁻¹ ^ n)) ∧ h ω ∈ R.E r z ∧
      ∃ u ∈ Icc 0 L, P u ∈ ball z (R.lam 1 * r) := by
  set ε : ℝ := (2 : ℝ)⁻¹ ^ n with hεdef
  have hε : 0 < ε := by positivity
  have hεν : 0 < ε ^ (1 + R.ν) := Real.rpow_pos_of_pos hε _
  have hσ : 0 < R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4 := by positivity
  have hKne : K.Nonempty := ⟨_, hP0⟩
  refine gm_S4_6_det hK hL hPc hP0 hσ rfl hlow hup hPL (fun z r => h ω ∈ R.E r z) ?_ ?_
  · intro z hz hz2
    have hzc : z ∈ cthickening (2 * R.lam 3 * ε * 𝕣) K := by
      rw [mem_cthickening_iff, ← ENNReal.ofReal_toReal (infEDist_ne_top hKne)]
      exact ENNReal.ofReal_le_ofReal hz2
    obtain ⟨k, hk, hE⟩ := hω n hn z ⟨hz, hKreg hzc⟩
    exact ⟨_, ⟨k, hk, rfl⟩, hE⟩
  · rintro r ⟨k, hk, rfl⟩
    have := hrr k hk
    have hl1 : 0 < R.lam 1 := hl0.trans hl01
    calc 2 * (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) < R.lam 1 * (ε ^ (1 + R.ν) * 𝕣) := by
          have : 0 < ε ^ (1 + R.ν) * 𝕣 := by positivity
          nlinarith
      _ ≤ R.lam 1 * R.rr 𝕣 ε k := mul_le_mul_of_nonneg_left this hl1.le

end LQGMetric.GM
