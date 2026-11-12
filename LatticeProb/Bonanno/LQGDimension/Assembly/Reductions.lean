/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Assembly.Reductions at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.LFPP

/-!
# Assembly: the reduction steps of Theorem 1.1

This file assembles the second and third assertions of Theorem 1.1 from `Theorem11_AStar` and
the `LFPP` blueprint obligations (`Prop12Upper`, `Prop12Lower`).

* `lambdaAsymptotics_of` derives `Blueprint.LambdaAsymptotics` (equation (1.5), stated for
  arbitrary exponents) from `Theorem11_AStar` (so `a n / n → aStar`) together with the upper and
  lower bounds of Proposition 1.2: as `n → ∞`, both `(a n ± C n^{…})/log(…)` tend to
  `aStar / log 16`, so the bound of Proposition 1.2 at a suitable `n` gives the `η`-bound.
* `theorem11_lambda_of` turns `LambdaAsymptotics` into the `Tendsto` statement `Theorem11_Lambda`
  by unwinding the `∀ η, ∀ᶠ` form into the `ε`-`δ` characterization of `Tendsto _ _ (𝓝 _)`.
* `theorem11_dimension_of` derives `Theorem11_Dimension` from `LambdaAsymptotics` composed along
  `ξ_γ := γ / d_γ → 0⁺`, using the algebraic identity
  `(d_γ - 2) / γ^{4/3} = γ^{2/3}/2 + d_γ^{-1/3} · (λ_γ / ξ_γ^{4/3})`
  (with `λ_γ := 1 - (2 + γ²/2)/d_γ`, valid since `d_γ - 2 = λ_γ d_γ + γ²/2` and
  `ξ_γ^{4/3} = γ^{4/3} d_γ^{-4/3}`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace LQGDimension

namespace Assembly

/-- `n ^ p / n → 0` along `n : ℕ → ∞`, for any exponent `p < 1`. -/
lemma tendsto_rpow_div_self_atTop {p : ℝ} (hp : p < 1) :
    Tendsto (fun n : ℕ => (n:ℝ) ^ p / (n:ℝ)) atTop (𝓝 0) := by
  have hy : Tendsto (fun n : ℕ => (n:ℝ) ^ (p - 1)) atTop (𝓝 0) := by
    have hbase := tendsto_rpow_neg_atTop (y := 1 - p) (by linarith)
    simp only [show -(1-p) = p - 1 from by ring] at hbase
    exact hbase.comp tendsto_natCast_atTop_atTop
  have heq : (fun n:ℕ => (n:ℝ)^(p-1)) =ᶠ[atTop] (fun n:ℕ => (n:ℝ)^p / (n:ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    rw [Real.rpow_sub hn', Real.rpow_one]
  exact hy.congr' heq

/-- The lower-bound sequence of Proposition 1.2, `(a n - C n^{7/8}) / log(16^n)`, tends to
`aStar / log 16`. -/
lemma tendsto_lower_seq (hA : Theorem11_AStar) (C : ℝ) :
    Tendsto (fun n : ℕ => (a n - C * (n:ℝ)^(7/8:ℝ)) / Real.log (16^n)) atTop
      (𝓝 (aStar / Real.log 16)) := by
  have hlog16 : (0:ℝ) < Real.log 16 := Real.log_pos (by norm_num)
  have hAn : Tendsto (fun n:ℕ => a n / n) atTop (𝓝 aStar) := hA.2.2.2
  have hp : Tendsto (fun n:ℕ => (n:ℝ)^(7/8:ℝ) / (n:ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_div_self_atTop (by norm_num)
  have hnum : Tendsto (fun n:ℕ => a n / n - C * ((n:ℝ)^(7/8:ℝ)/(n:ℝ))) atTop (𝓝 (aStar - C*0)) :=
    hAn.sub (tendsto_const_nhds.mul hp)
  rw [mul_zero, sub_zero] at hnum
  have hfrac : Tendsto (fun n:ℕ => (a n / n - C * ((n:ℝ)^(7/8:ℝ)/(n:ℝ))) / Real.log 16)
      atTop (𝓝 (aStar / Real.log 16)) := hnum.div_const _
  refine hfrac.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  rw [Real.log_pow]
  field_simp

/-- The upper-bound sequence of Proposition 1.2, `(a n + C n^{3/4}) / log(2·16^n/3)`, tends to
`aStar / log 16`. -/
lemma tendsto_upper_seq (hA : Theorem11_AStar) (C : ℝ) :
    Tendsto (fun n : ℕ => (a n + C * (n:ℝ)^(3/4:ℝ)) / Real.log (2 * 16^n / 3)) atTop
      (𝓝 (aStar / Real.log 16)) := by
  have hlog16 : (0:ℝ) < Real.log 16 := Real.log_pos (by norm_num)
  have hAn : Tendsto (fun n:ℕ => a n / n) atTop (𝓝 aStar) := hA.2.2.2
  have hp : Tendsto (fun n:ℕ => (n:ℝ)^(3/4:ℝ) / (n:ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_div_self_atTop (by norm_num)
  have hnum : Tendsto (fun n:ℕ => a n / n + C * ((n:ℝ)^(3/4:ℝ)/(n:ℝ))) atTop (𝓝 (aStar + C*0)) :=
    hAn.add (tendsto_const_nhds.mul hp)
  rw [mul_zero, add_zero] at hnum
  have hden0 : Tendsto (fun n:ℕ => (Real.log 2 - Real.log 3) / (n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n:ℕ => Real.log 16 + (Real.log 2 - Real.log 3)/(n:ℝ)) atTop
      (𝓝 (Real.log 16 + 0)) := tendsto_const_nhds.add hden0
  rw [add_zero] at hden
  have hfrac : Tendsto (fun n:ℕ =>
      (a n / n + C * ((n:ℝ)^(3/4:ℝ)/(n:ℝ))) / (Real.log 16 + (Real.log 2 - Real.log 3)/(n:ℝ)))
      atTop (𝓝 (aStar / Real.log 16)) := hnum.div hden hlog16.ne'
  refine hfrac.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hpow_pos : (0:ℝ) < (16:ℝ)^n := by positivity
  rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by norm_num) hpow_pos.ne',
    Real.log_pow]
  field_simp
  ring

end Assembly

open Assembly in
/-- `LambdaAsymptotics` (equation (1.5) for arbitrary exponents), from `Theorem11_AStar` and
Proposition 1.2's upper and lower bounds. -/
theorem lambdaAsymptotics_of (hA : Theorem11_AStar) (hU : Blueprint.Prop12Upper)
    (hL : Blueprint.Prop12Lower) : Blueprint.LambdaAsymptotics := by
  intro Ω _ P h hGFF η hη
  obtain ⟨CU, NU, hU'⟩ := hU Ω P h hGFF
  obtain ⟨CL, NL, hL'⟩ := hL Ω P h hGFF
  have hUtendsto := tendsto_upper_seq hA CU
  have hLtendsto := tendsto_lower_seq hA CL
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hUtendsto (η/4) (by linarith))
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hLtendsto (η/4) (by linarith))
  set n := max (max NU NL) (max N1 N2) with hn_def
  have hnU : n ≥ NU := le_trans (le_max_left NU NL) (le_max_left _ _)
  have hnL : n ≥ NL := le_trans (le_max_right NU NL) (le_max_left _ _)
  have hnN1 : n ≥ N1 := le_trans (le_max_left N1 N2) (le_max_right _ _)
  have hnN2 : n ≥ N2 := le_trans (le_max_right N1 N2) (le_max_right _ _)
  have hub := hN1 n hnN1
  have hlb := hN2 n hnN2
  rw [Real.dist_eq, abs_lt] at hub hlb
  have hev1 := hU' n hnU (η/4) (by linarith)
  have hev2 := hL' n hnL (η/4) (by linarith)
  filter_upwards [hev1, hev2] with ξ he1 he2
  intro lam hlam
  have b1 := he1 lam hlam
  have b2 := he2 lam hlam
  rw [abs_le]
  constructor <;> nlinarith [hub.1, hub.2, hlb.1, hlb.2]

/-- Theorem 1.1, equation (1.5) (`Theorem11_Lambda`), from `LambdaAsymptotics`: unwind the
`∀ η, ∀ᶠ` bound into the `ε`-characterization of `Tendsto`. -/
theorem theorem11_lambda_of (hLA : Blueprint.LambdaAsymptotics) : Theorem11_Lambda := by
  intro Ω _ P h hGFF lam hex
  obtain ⟨ξ₀, hξ₀, hexp⟩ := hex
  rw [Metric.tendsto_nhds]
  intro ε hε
  have heventually_exp : ∀ᶠ ξ in 𝓝[>] (0:ℝ), IsLFPPExponent h P ξ (lam ξ) := by
    filter_upwards [Ioo_mem_nhdsGT hξ₀] with ξ hξ using hexp ξ hξ
  have hbound := hLA Ω P h hGFF (ε/2) (by linarith)
  filter_upwards [hbound, heventually_exp] with ξ hb he
  have hb' := hb (lam ξ) he
  rw [Real.dist_eq]
  calc |lam ξ / ξ ^ (4/3:ℝ) - aStar/Real.log 16| ≤ ε/2 := hb'
  _ < ε := by linarith

open Assembly in
/-- Theorem 1.1, equation (1.6) (`Theorem11_Dimension`), from `LambdaAsymptotics`, composed
along `ξ_γ = γ / d_γ → 0⁺` and the algebraic identity relating `(d_γ-2)/γ^{4/3}` to
`λ_γ / ξ_γ^{4/3}`. -/
theorem theorem11_dimension_of (hLA : Blueprint.LambdaAsymptotics) : Theorem11_Dimension := by
  intro Ω _ P h hGFF d hd hexp
  obtain ⟨γ₀, hγ₀, hexp'⟩ := hexp
  have hd_pos : ∀ᶠ γ in 𝓝[>] (0:ℝ), 0 < d γ :=
    hd.eventually_mem (isOpen_Ioi.mem_nhds (by norm_num : (2:ℝ) ∈ Ioi (0:ℝ)))
  have hid_tendsto0 : Tendsto (fun γ : ℝ => γ) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hξ_tendsto0 : Tendsto (fun γ => γ / d γ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h0 := hid_tendsto0.div hd (by norm_num : (2:ℝ) ≠ 0)
    have h02 : (0:ℝ) / 2 = 0 := by norm_num
    rw [h02] at h0
    exact h0
  have hξ_pos : ∀ᶠ γ in 𝓝[>] (0:ℝ), γ / d γ ∈ Ioi (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin, hd_pos] with γ hγpos hdpos
    exact div_pos hγpos hdpos
  have hξ_tendsto : Tendsto (fun γ => γ / d γ) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hξ_tendsto0 hξ_pos
  have hexp_ev : ∀ᶠ γ in 𝓝[>] (0:ℝ),
      IsLFPPExponent h P (γ / d γ) (1 - (2 + γ^2/2) / d γ) := by
    filter_upwards [Ioo_mem_nhdsGT hγ₀] with γ hγ using hexp' γ hγ
  -- `λ_γ / ξ_γ^{4/3} → aStar / log 16` by composing `LambdaAsymptotics` along `ξ_γ → 0⁺`.
  have hratio : Tendsto (fun γ => (1 - (2+γ^2/2)/d γ) / (γ/d γ)^(4/3:ℝ)) (𝓝[>] (0:ℝ))
      (𝓝 (aStar / Real.log 16)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hbound := hLA Ω P h hGFF (ε/2) (by linarith)
    have hbound' := hξ_tendsto.eventually hbound
    filter_upwards [hbound', hexp_ev] with γ hb he
    rw [Real.dist_eq]
    have hle := hb _ he
    calc |(1 - (2+γ^2/2)/d γ) / (γ/d γ)^(4/3:ℝ) - aStar/Real.log 16| ≤ ε/2 := hle
    _ < ε := by linarith
  have hpow23 : Tendsto (fun γ:ℝ => γ^(2/3:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    hid_tendsto0.rpow_const_nhds_zero (by norm_num)
  have hdpow : Tendsto (fun γ => (d γ)^(-1/3:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 ((2:ℝ)^(-1/3:ℝ))) :=
    hd.rpow_const (Or.inl (by norm_num))
  have hrhs : Tendsto (fun γ => γ^(2/3:ℝ)/2 + (d γ)^(-1/3:ℝ) *
      ((1 - (2+γ^2/2)/d γ) / (γ/d γ)^(4/3:ℝ))) (𝓝[>] (0:ℝ))
      (𝓝 ((0:ℝ)/2 + (2:ℝ)^(-1/3:ℝ) * (aStar/Real.log 16))) :=
    (hpow23.div_const 2).add (hdpow.mul hratio)
  rw [zero_div, zero_add] at hrhs
  -- The algebraic identity `(d-2)/γ^{4/3} = γ^{2/3}/2 + d^{-1/3}·(λ/ξ^{4/3})`, using
  -- `d - 2 = λ·d + γ²/2` and `ξ^{4/3} = γ^{4/3}·d^{-4/3}`.
  have heq : (fun γ:ℝ => γ^(2/3:ℝ)/2 + (d γ)^(-1/3:ℝ) *
        ((1 - (2+γ^2/2)/d γ) / (γ/d γ)^(4/3:ℝ))) =ᶠ[𝓝[>] (0:ℝ)]
      (fun γ => (d γ - 2)/γ^(4/3:ℝ)) := by
    filter_upwards [self_mem_nhdsWithin, hd_pos] with γ hγpos hdpos
    have hξ43 : (γ/d γ)^(4/3:ℝ) = γ^(4/3:ℝ) / (d γ)^(4/3:ℝ) :=
      Real.div_rpow hγpos.le hdpos.le (4/3)
    have hdcomb : (d γ)^(-1/3:ℝ) * (d γ)^(4/3:ℝ) = d γ := by
      rw [← Real.rpow_add hdpos]; norm_num
    have hγcomb : γ^(2/3:ℝ) * γ^(4/3:ℝ) = γ^2 := by
      rw [← Real.rpow_add hγpos]; norm_num
    have hγ430 : γ^(4/3:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hγpos _).ne'
    have hd430 : (d γ)^(4/3:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hdpos _).ne'
    rw [hξ43, div_div_eq_mul_div]
    field_simp
    nlinarith [hγcomb, hdcomb]
  have hfinal := hrhs.congr' heq
  have heq2 : (2:ℝ)^(-1/3:ℝ) * (aStar/Real.log 16) = (2:ℝ)^(-1/3:ℝ) * aStar / Real.log 16 :=
    (mul_div_assoc _ _ _).symm
  rwa [heq2] at hfinal

end LQGDimension
