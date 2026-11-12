/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_14 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinSetup
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_14Ratio

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.14 (`lem-lfpp-constant`, T:1073–1098): the scaling constants `𝔠_r` and their
Λ-bounds (form D78)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`), proof of Lemma 2.14, T:1096–1097:
the bounds (eqn-scaling-constant') "are immediate from [DDDF, Theorem 1, Equation (1.3)] and the
fact the ratio of our `𝔞_ε` and the scaling factor `λ_ε` from [DDDF] is bounded above and below
by deterministic, `ε`-independent constants (see the proof of Lemma 2.8)".

* `aEpsDF_lambda_white`: `C⁻¹ λ_ε ≤ 𝔞_ε ≤ C λ_ε` for small `ε`, with `λ_ε` defined from one
  white noise (`aEps_lambda_bounds`, DFGPS T:888–891, as in `unitSq_setup`);
* `aEpsDF_ratio_bounds`: `Λ⁻¹ δ^Λ ≤ 𝔞_{δη}/𝔞_η ≤ Λ δ^{−Λ}` for small `η`, from DDDF (1.3)
  (`DDDFEq1_3`) and (6.99) (`DDDFEq6_99`; needed, see `L2_14Ratio.lean`);
* `lem2_14`: `Lem2_14` in the form of D78 (decisions/DEC-78.md): `𝔠_r := liminf_n r 𝔞_{ε_n/r}/𝔞_{ε_n}`
  is a positive cluster point of the ratios with the Λ-bounds. The paper's claim that the limit
  exists (T:1080–1095, Portmanteau/median argument) is not used: it needs the median of the
  internal crossing of the limit metric (not a function of the limit, T:999–1000) to be unique
  (S8), and Lemma 2.13 only needs a subsequential limit of the ratio (DV-D78). The `liminf`
  bookkeeping (`L214.liminf_scaling`) is an own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP HeatSq WhiteNoise DDDF

namespace L214

/-- eventual two-sided bounds give the boundedness side conditions of `liminf` -/
lemma liminf_bdd {u : ℕ → ℝ} {L U : ℝ} (h : ∀ᶠ n in atTop, L ≤ u n ∧ u n ≤ U) :
    IsBoundedUnder (· ≥ ·) atTop u ∧ IsCoboundedUnder (· ≥ ·) atTop u ∧ L ≤ liminf u atTop :=
  have hc : IsCoboundedUnder (· ≥ ·) atTop u :=
    isCoboundedUnder_ge_of_eventually_le atTop (h.mono fun _ hn => hn.2)
  ⟨isBoundedUnder_of_eventually_ge (h.mono fun _ hn => hn.1), hc,
    le_liminf_of_le hc (h.mono fun _ hn => hn.1)⟩

/-- `liminf (A u) = A liminf u` for `A ≥ 0` and `u` eventually bounded -/
lemma liminf_const_mul_real {u : ℕ → ℝ} {L U A : ℝ} (hA : 0 ≤ A)
    (h : ∀ᶠ n in atTop, L ≤ u n ∧ u n ≤ U) :
    liminf (fun n => A * u n) atTop = A * liminf u atTop := by
  obtain ⟨hb, hc, -⟩ := liminf_bdd h
  exact (Monotone.map_liminf_of_continuousAt (f := fun y => A * y)
    (fun _ _ hxy => mul_le_mul_of_nonneg_left hxy hA) u (continuous_const.mul continuous_id).continuousAt
    hc hb).symm

/-- **The scaling constants as `liminf`s** (own bookkeeping for D78): if `x r n > 0` and
`A_δ x_n(r) ≤ x_n(δr) ≤ B_δ x_n(r)` eventually, and `x_n(1) = 1` eventually, then
`c r := liminf_n x_n(r)` is positive, a cluster point of `x(r)`, and `A_δ ≤ c(δr)/c(r) ≤ B_δ`. -/
theorem liminf_scaling {x : ℝ → ℕ → ℝ} {A B : ℝ → ℝ}
    (hA : ∀ δ ∈ Ioo (0 : ℝ) 1, 0 < A δ) (hB : ∀ δ ∈ Ioo (0 : ℝ) 1, 0 < B δ)
    (hrel : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r, 0 < r → ∀ᶠ n in atTop,
      0 < x r n ∧ A δ * x r n ≤ x (δ * r) n ∧ x (δ * r) n ≤ B δ * x r n)
    (h1 : ∀ᶠ n in atTop, x 1 n = 1) :
    (∀ r, 0 < r → 0 < liminf (x r) atTop ∧ MapClusterPt (liminf (x r) atTop) atTop (x r)) ∧
      ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r, 0 < r →
        A δ ≤ liminf (x (δ * r)) atTop / liminf (x r) atTop ∧
        liminf (x (δ * r)) atTop / liminf (x r) atTop ≤ B δ := by
  have hbd : ∀ r, 0 < r → ∃ L > 0, ∃ U, ∀ᶠ n in atTop, L ≤ x r n ∧ x r n ≤ U := by
    intro r hr
    rcases lt_trichotomy r 1 with hr1 | rfl | hr1
    · refine ⟨A r, hA r ⟨hr, hr1⟩, B r, ?_⟩
      filter_upwards [hrel r ⟨hr, hr1⟩ 1 one_pos, h1] with n hn hn1
      rw [hn1] at hn
      simp only [mul_one] at hn
      exact ⟨hn.2.1, hn.2.2⟩
    · exact ⟨1, one_pos, 1, h1.mono fun n hn => ⟨hn.ge, hn.le⟩⟩
    · have hδ : r⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.2 hr, inv_lt_one_of_one_lt₀ hr1⟩
      refine ⟨(B r⁻¹)⁻¹, inv_pos.2 (hB _ hδ), (A r⁻¹)⁻¹, ?_⟩
      filter_upwards [hrel r⁻¹ hδ r hr, h1] with n hn hn1
      rw [inv_mul_cancel₀ hr.ne', hn1] at hn
      obtain ⟨hp, h2, h3⟩ := hn
      have hA' := hA _ hδ
      have hB' := hB _ hδ
      constructor
      · calc (B r⁻¹)⁻¹ = 1 / B r⁻¹ := (one_div _).symm
          _ ≤ B r⁻¹ * x r n / B r⁻¹ := div_le_div_of_nonneg_right h3 hB'.le
          _ = x r n := mul_div_cancel_left₀ _ hB'.ne'
      · calc x r n = A r⁻¹ * x r n / A r⁻¹ := (mul_div_cancel_left₀ _ hA'.ne').symm
          _ ≤ 1 / A r⁻¹ := div_le_div_of_nonneg_right h2 hA'.le
          _ = (A r⁻¹)⁻¹ := one_div _
  have hpos : ∀ r, 0 < r → 0 < liminf (x r) atTop := fun r hr => by
    obtain ⟨L, hL, U, h⟩ := hbd r hr
    exact hL.trans_le (liminf_bdd h).2.2
  refine ⟨fun r hr => ⟨hpos r hr, ?_⟩, fun δ hδ r hr => ?_⟩
  · obtain ⟨L, -, U, h⟩ := hbd r hr
    obtain ⟨hb, hc, -⟩ := liminf_bdd h
    exact MapClusterPt.liminf hc hb
  · have hδr : 0 < δ * r := mul_pos hδ.1 hr
    obtain ⟨L, hL, U, h⟩ := hbd r hr
    obtain ⟨L', hL', U', h'⟩ := hbd (δ * r) hδr
    have hAδ := hA δ hδ
    have hBδ := hB δ hδ
    obtain ⟨hb', hc', -⟩ := liminf_bdd h'
    have hAu : ∀ᶠ n in atTop, A δ * L ≤ A δ * x r n ∧ A δ * x r n ≤ A δ * U :=
      h.mono fun n hn => ⟨mul_le_mul_of_nonneg_left hn.1 hAδ.le,
        mul_le_mul_of_nonneg_left hn.2 hAδ.le⟩
    have hBu : ∀ᶠ n in atTop, B δ * L ≤ B δ * x r n ∧ B δ * x r n ≤ B δ * U :=
      h.mono fun n hn => ⟨mul_le_mul_of_nonneg_left hn.1 hBδ.le,
        mul_le_mul_of_nonneg_left hn.2 hBδ.le⟩
    obtain ⟨hbA, -, -⟩ := liminf_bdd hAu
    obtain ⟨-, hcB, -⟩ := liminf_bdd hBu
    have hlo : A δ * liminf (x r) atTop ≤ liminf (x (δ * r)) atTop := by
      rw [← liminf_const_mul_real hAδ.le h]
      exact liminf_le_liminf ((hrel δ hδ r hr).mono fun n hn => hn.2.1) hbA hc'
    have hup : liminf (x (δ * r)) atTop ≤ B δ * liminf (x r) atTop := by
      rw [← liminf_const_mul_real hBδ.le h]
      exact liminf_le_liminf ((hrel δ hδ r hr).mono fun n hn => hn.2.2) hb' hcB
    have hc0 := hpos r hr
    exact ⟨(le_div_iff₀ hc0).2 hlo, (div_le_iff₀ hc0).2 hup⟩

/-- the eventual relation `x_n(δr) ≍ x_n(r)` for `x_n(r) = r a(ε_n/r)/a(ε_n)` (DFGPS T:1096–1097,
as in `scaling_const_bounds`) -/
theorem ratio_rel {a : ℝ → ℝ} {Λ : ℝ} (hΛ : 1 < Λ)
    (hr : ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ η₀ > 0, ∀ η, 0 < η → η < η₀ → 0 < a η ∧ 0 < a (δ * η) ∧
      Λ⁻¹ * δ ^ Λ ≤ a (δ * η) / a η ∧ a (δ * η) / a η ≤ Λ * δ ^ (-Λ))
    {εn : ℕ → ℝ} (hε : ∀ n, 0 < εn n) (hεt : Tendsto εn atTop (𝓝 0)) :
    (∀ᶠ n in atTop, 1 * a (εn n / 1) / a (εn n) = 1) ∧
    ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r, 0 < r → ∀ᶠ n in atTop,
      0 < r * a (εn n / r) / a (εn n) ∧
      (Λ + 1)⁻¹ * δ ^ (Λ + 1) * (r * a (εn n / r) / a (εn n)) ≤
        δ * r * a (εn n / (δ * r)) / a (εn n) ∧
      δ * r * a (εn n / (δ * r)) / a (εn n) ≤
        (Λ + 1) * δ ^ (-(Λ + 1)) * (r * a (εn n / r) / a (εn n)) := by
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨ηh, hηh, hh⟩ := hr (1 / 2) ⟨by norm_num, by norm_num⟩
  have hapos : ∀ᶠ n in atTop, 0 < a (εn n) := by
    filter_upwards [eventually_div_lt hεt 1 hηh] with n hn
    rw [div_one] at hn
    exact (hh _ (hε n) hn).1
  refine ⟨hapos.mono fun n hn => by rw [div_one, one_mul, div_self hn.ne'], fun δ hδ r hr0 => ?_⟩
  have hδ0 := hδ.1
  have hδr : 0 < δ * r := by positivity
  obtain ⟨η₀, hη₀, h⟩ := hr δ hδ
  filter_upwards [eventually_div_lt hεt (δ * r) hη₀, hapos] with n hn ha
  obtain ⟨h1, h2, h3, h4⟩ := h _ (div_pos (hε n) hδr) hn
  have e : δ * (εn n / (δ * r)) = εn n / r := by field_simp
  rw [e] at h2 h3 h4
  set x := a (εn n / (δ * r))
  set y := a (εn n / r)
  have hu : 0 < r * y / a (εn n) := by positivity
  have eq : δ * r * x / a (εn n) = δ / (y / x) * (r * y / a (εn n)) := by
    field_simp
  rw [eq]
  have hpΛ : 0 < δ ^ Λ := Real.rpow_pos_of_pos hδ0 Λ
  have e1 : δ ^ (Λ + 1) = δ ^ Λ * δ := Real.rpow_add_one hδ0.ne' Λ
  have e2 : δ ^ (-(Λ + 1)) = (δ ^ Λ * δ)⁻¹ := by rw [Real.rpow_neg hδ0.le, e1]
  have e3 : δ ^ (-Λ) = (δ ^ Λ)⁻¹ := Real.rpow_neg hδ0.le Λ
  rw [e3] at h4
  refine ⟨hu, mul_le_mul_of_nonneg_right ?_ hu.le, mul_le_mul_of_nonneg_right ?_ hu.le⟩
  · calc (Λ + 1)⁻¹ * δ ^ (Λ + 1) ≤ Λ⁻¹ * (δ ^ Λ * δ) := by
          rw [e1]; gcongr; linarith
      _ = δ / (Λ * (δ ^ Λ)⁻¹) := by field_simp
      _ ≤ δ / (y / x) := div_le_div_of_nonneg_left hδ0.le (by positivity) h4
  · have hδ1 : δ ≤ δ⁻¹ := hδ.2.le.trans ((one_le_inv₀ hδ0).2 hδ.2.le)
    calc δ / (y / x) ≤ δ / (Λ⁻¹ * δ ^ Λ) :=
          div_le_div_of_nonneg_left hδ0.le (by positivity) h3
      _ = Λ * (δ ^ Λ)⁻¹ * δ := by field_simp
      _ ≤ (Λ + 1) * (δ ^ Λ)⁻¹ * δ⁻¹ := by gcongr; linarith
      _ = (Λ + 1) * δ ^ (-(Λ + 1)) := by rw [e2, mul_inv]; ring

end L214

end LQGMetric.DFGPS
