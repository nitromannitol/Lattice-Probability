/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Exp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Sub
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDBasic

/-!
# DZZ Lemma 5.3: the subadditive step (P2-DZZ56)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.3, l. 2414–2427.

DZZ's proof of Lemma 5.3 has three parts:
1. the probabilistic near-subadditive inequality (l. 2414–2418, from (Eq.calD1), (eq-040418) and
   (eq-union-bound-distance)): with `χ_δ = E log D̃_{γ,δ,η}(u,v) / log δ⁻¹`,
   `χ_{δδ̃} ≤ (log δ⁻¹ χ_δ + log δ̃⁻¹ χ_δ̃)/(log δ⁻¹ + log δ̃⁻¹) + (log δ⁻¹)^{−0.01}`;
2. "Applying [Hammersley 1962] … `χ_δ` converges … over `δ_k = 2^{−k}`, and then by continuity the
   convergence extends to arbitrary `δ → 0`" (l. 2421–2422);
3. "`χ` does not depend on `u, v`" (l. 2423, by Prop. 3.2, Lemmas 3.5, 3.10, 3.11, Cor. 3.9).

This file proves part 2 for the actual distances (`dzz_lem53_pair_tendsto`) and assembles
`DZZLem53Exp` from parts 1 and 3 (`dzzLem53Exp_of_subadd`). Parts 1 and 3 are the hypotheses
`DZZLem53Subadd` and `hindep` (verbatim DZZ displays, along the dyadic scales DZZ use).

The crude bound `0 ≤ χ_δ ≤ M` is DZZ (eq-very-crude) (`hM`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `χ_{2^{−k}}(u,v) = E log D̃_{2^{−k}}(u,v) / (k log 2)` for a measure `ν` (in DZZ:
`ν = dzzWall (tildeBox u v) μ`). -/
def chiDy (P : Measure Ω) (ν : Ω → Measure ℂ) (u v : ℂ) (k : ℕ) : ℝ :=
  (∫ ω, logMinLGD (ν ω) ((2 : ℝ)⁻¹ ^ k) {u} {v} ∂P) / (k * Real.log 2)

/-- **DZZ l. 2418–2420** (part 1 of the proof of Lemma 5.3), along `δ = 2^{−k}`, `δ̃ = 2^{−l}`,
`l ≤ k`, `k ≥ k₀`, with error `(log δ⁻¹)^{−θ}` (DZZ: `θ = 0.01`). -/
def DZZLem53Subadd (P : Measure Ω) (ν : Ω → Measure ℂ) (u v : ℂ) (θ : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
    chiDy P ν u v (k + l) ≤ (k : ℝ) / (k + l) * chiDy P ν u v k +
      (l : ℝ) / (k + l) * chiDy P ν u v l + ((k : ℝ) * Real.log 2) ^ (-θ)

lemma logMinLGD_singleton (μ : Measure ℂ) (δ : ℝ) (u v : ℂ) :
    logMinLGD μ δ {u} {v} = Real.log ((lgdDZZ μ δ u v).toNat : ℝ) := by
  simp [logMinLGD, lgdMinSet]

lemma logMinLGD_nonneg (μ : Measure ℂ) (δ : ℝ) (A B : Set ℂ) : 0 ≤ logMinLGD μ δ A B :=
  Real.log_natCast_nonneg _

/-- `log D_δ` is antitone in `δ` where `D_δ < ∞` (`lgdDZZ_antitone`). -/
lemma logMinLGD_singleton_anti (μ : Measure ℂ) {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ')
    (u v : ℂ) (hfin : lgdDZZ μ δ u v < ⊤) :
    logMinLGD μ δ' {u} {v} ≤ logMinLGD μ δ {u} {v} := by
  rw [logMinLGD_singleton, logMinLGD_singleton]
  have h1 := lgdDZZ_antitone μ hδ hδδ' u v
  have h2 : 1 ≤ (lgdDZZ μ δ' u v).toNat := by
    have := one_le_lgdDZZ μ δ' u v
    have hne : lgdDZZ μ δ' u v ≠ ⊤ := (h1.trans_lt hfin).ne
    have := ENat.toNat_le_toNat this hne
    simpa using this
  have h3 := ENat.toNat_le_toNat h1 hfin.ne
  have h2' : (0 : ℝ) < ((lgdDZZ μ δ' u v).toNat : ℝ) := by exact_mod_cast h2
  exact Real.log_le_log h2' (by exact_mod_cast h3)

/-- **DZZ Lemma 5.3, part 2** (l. 2421–2422) for one pair `(u,v)`: the near-subadditive
inequality, the crude bound and a.s. finiteness give convergence of
`E log D_δ(u,v) / log δ⁻¹` as `δ → 0⁺`. -/
theorem dzz_lem53_pair_tendsto {P : Measure Ω} {ν : Ω → Measure ℂ} {u v : ℂ} {θ M : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hsub : DZZLem53Subadd P ν u v θ)
    (hM : ∀ k, chiDy P ν u v k ≤ M)
    (hfin : ∀ δ : ℝ, 0 < δ → ∀ᵐ ω ∂P, lgdDZZ (ν ω) δ u v < ⊤)
    (hint : ∀ δ : ℝ, 0 < δ → Integrable (fun ω => logMinLGD (ν ω) δ {u} {v}) P) :
    ∃ χ, Tendsto (fun δ => (∫ ω, logMinLGD (ν ω) δ {u} {v} ∂P) / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 χ) := by
  obtain ⟨k₀, hk⟩ := hsub
  have h0 : ∀ k, 0 ≤ chiDy P ν u v k := fun k =>
    div_nonneg (integral_nonneg fun ω => logMinLGD_nonneg _ _ _ _)
      (mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg (by norm_num)))
  obtain ⟨χ, hχ⟩ := dzz_chi_dyadic_tendsto (k₀ := k₀) hθ hθ1 h0 hM hk
  refine ⟨χ, tendsto_of_dyadic_antitone (fun δ _ => integral_nonneg fun ω =>
    logMinLGD_nonneg _ _ _ _) (fun δ δ' hδ hδδ' => ?_) hχ⟩
  refine integral_mono_ae (hint δ' (hδ.trans_le hδδ')) (hint δ hδ) ?_
  filter_upwards [hfin δ hδ] with ω hω
  exact logMinLGD_singleton_anti _ hδ.le hδδ' u v hω

/-- **DZZ Lemma 5.3** (the `D̃` half, `DZZLem53Exp`) from part 1 (`DZZLem53Subadd`, for every
pair) and part 3 (`hindep`: "`χ` does not depend on `u, v`", l. 2423, stated as: the difference
of the normalized expectations of two pairs tends to `0`). -/
theorem dzzLem53Exp_of_subadd {P : Measure Ω} {μ : Ω → Measure ℂ} {θ M : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hsub : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v →
      DZZLem53Subadd P (fun ω => dzzWall (tildeBox u v) (μ ω)) u v θ)
    (hM : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ k,
      chiDy P (fun ω => dzzWall (tildeBox u v) (μ ω)) u v k ≤ M)
    (hfin : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ δ : ℝ, 0 < δ →
      ∀ᵐ ω ∂P, lgdDZZ (dzzWall (tildeBox u v) (μ ω)) δ u v < ⊤)
    (hint : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ δ : ℝ, 0 < δ →
      Integrable (fun ω => logMinLGD (dzzWall (tildeBox u v) (μ ω)) δ {u} {v}) P)
    (hindep : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ u' ∈ dzzVbar, ∀ v' ∈ dzzVbar, u' ≠ v' →
      Tendsto (fun δ => (∫ ω, logMinLGD (dzzWall (tildeBox u' v') (μ ω)) δ {u'} {v'} ∂P) /
        Real.log δ⁻¹ - (∫ ω, logMinLGD (dzzWall (tildeBox u v) (μ ω)) δ {u} {v} ∂P) /
        Real.log δ⁻¹) (𝓝[>] 0) (𝓝 0)) :
    ∃ χ, DZZLem53Exp P μ χ := by
  set u₀ : ℂ := ⟨1 / 2, 1 / 2⟩
  set v₀ : ℂ := ⟨1 / 2 + 1 / 40, 1 / 2⟩
  have hu₀ : u₀ ∈ dzzVbar := by
    simp only [dzzVbar, sqBox, mem_setOf_eq, u₀, sub_self, abs_zero]; norm_num
  have hv₀ : v₀ ∈ dzzVbar := by
    simp only [dzzVbar, sqBox, mem_setOf_eq, v₀]; norm_num
  have hne : u₀ ≠ v₀ := by
    intro h; have := congrArg Complex.re h; simp [u₀, v₀] at this
  obtain ⟨χ, hχ⟩ := dzz_lem53_pair_tendsto hθ hθ1 (hsub u₀ hu₀ v₀ hv₀ hne)
    (hM u₀ hu₀ v₀ hv₀ hne) (hfin u₀ hu₀ v₀ hv₀ hne) (hint u₀ hu₀ v₀ hv₀ hne)
  refine ⟨χ, fun u hu v hv huv => ?_⟩
  have := hχ.add (hindep u₀ hu₀ v₀ hv₀ hne u hu v hv huv)
  simpa using this

end DZZ
end LQGMetric
