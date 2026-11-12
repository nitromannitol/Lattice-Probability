/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent4Dy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDBasic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The LGD exponent along dyadic scales (P2-GMCID4)

`tendsto_lgdRatio_iff_dyadic`: for a function `g : ℝ → ℕ∞` that is non-increasing on `(0,∞)` and
`≥ 1` (as `δ ↦ D_{γ,δ}(u,v)`, `lgdDZZ_antitone`, `one_le_lgdDZZ`),

  `log (g δ) / log δ⁻¹ → χ` as `δ → 0⁺`  ⟺  `log (g 2^{-n}) / log 2^n → χ` as `n → ∞`.

For `2^{-N-1} < δ ≤ 2^{-N}`, monotonicity sandwiches `log g(δ) / log δ⁻¹` between
`log g(2^{-N}) / ((N+1) log 2)` and `log g(2^{-N-1}) / (N log 2)`. This turns the LGD event of
`IsLGDExponent` (a limit over a continuum of scales) into a countable limit, hence a measurable
event. DZZ use the same reduction along dyadic `δ` (l. 135–141, "amalgamation"); own elementary
proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace GMCIdent4

/-- the ratio `log g(δ) / log δ⁻¹` -/
def lgdRatio (g : ℝ → ℕ∞) (δ : ℝ) : ℝ := Real.log (g δ).toNat / Real.log δ⁻¹

lemma log_inv_two_inv_pow (n : ℕ) : Real.log ((2 : ℝ)⁻¹ ^ n)⁻¹ = n * Real.log 2 := by
  rw [inv_pow, inv_inv, Real.log_pow]

lemma exists_dyadic_scale {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ n : ℕ, (2 : ℝ) ^ n ≤ δ⁻¹ ∧ δ⁻¹ < 2 ^ (n + 1) :=
  exists_nat_pow_near ((one_le_inv₀ hδ).2 hδ1) one_lt_two

open Classical in
/-- the dyadic scale `N` with `2^{-N-1} < δ ≤ 2^{-N}` -/
def dyScale (δ : ℝ) : ℕ :=
  if h : 0 < δ ∧ δ ≤ 1 then (exists_dyadic_scale h.1 h.2).choose else 0

lemma dyScale_spec {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (2 : ℝ) ^ dyScale δ ≤ δ⁻¹ ∧ δ⁻¹ < 2 ^ (dyScale δ + 1) := by
  unfold dyScale
  rw [dif_pos ⟨hδ, hδ1⟩]
  exact (exists_dyadic_scale hδ hδ1).choose_spec

lemma tendsto_dyScale : Tendsto dyScale (𝓝[>] 0) atTop := by
  rw [tendsto_atTop]
  intro m
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < (2 : ℝ)⁻¹ ^ m by positivity)] with δ hδ
  have h1 : δ ≤ 1 := hδ.2.le.trans (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨-, h2⟩ := dyScale_spec hδ.1 h1
  have h3 : (2 : ℝ) ^ m < δ⁻¹ := by
    have := (inv_lt_inv₀ (by positivity) hδ.1).2 hδ.2
    rwa [inv_pow, inv_inv] at this
  have := (pow_lt_pow_iff_right₀ one_lt_two).1 (h3.trans h2)
  omega

/-- **the LGD ratio converges iff it converges along dyadic scales** -/
theorem tendsto_lgdRatio_iff_dyadic {g : ℝ → ℕ∞}
    (hg : ∀ δ δ', 0 < δ → δ ≤ δ' → g δ' ≤ g δ) (hg1 : ∀ δ, 1 ≤ g δ) (χ : ℝ) :
    Tendsto (lgdRatio g) (𝓝[>] 0) (𝓝 χ) ↔
      Tendsto (fun n : ℕ => lgdRatio g ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 χ) := by
  have ht : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
      Eventually.of_forall fun n => show (0 : ℝ) < _ by positivity⟩
  refine ⟨fun h => h.comp ht, fun h => ?_⟩
  by_cases hT : ∃ δ₀, 0 < δ₀ ∧ g δ₀ = ⊤
  · obtain ⟨δ₀, hδ₀, hT⟩ := hT
    have hz : ∀ δ, 0 < δ → δ ≤ δ₀ → lgdRatio g δ = 0 := fun δ hδ hle => by
      have : g δ = ⊤ := top_le_iff.1 (hT ▸ hg δ δ₀ hδ hle)
      simp [lgdRatio, this]
    have hev : ∀ᶠ n : ℕ in atTop, lgdRatio g ((2 : ℝ)⁻¹ ^ n) = 0 := by
      filter_upwards [(tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num) :
        Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0)).eventually (ge_mem_nhds hδ₀)] with n hn
      exact hz _ (by positivity) hn
    have hχ : χ = 0 :=
      tendsto_nhds_unique h (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm))
    rw [hχ]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
    exact (hz δ hδ.1 hδ.2.le).symm
  push_neg at hT
  set H : ℝ → ℝ := fun δ => Real.log (g δ).toNat
  have hH : ∀ δ δ', 0 < δ → δ ≤ δ' → H δ' ≤ H δ := by
    intro δ δ' hδ hle
    have hδ' : 0 < δ' := hδ.trans_le hle
    have h1 : 1 ≤ (g δ').toNat := by
      have := ENat.toNat_le_toNat (hg1 δ') (hT δ' hδ')
      simpa using this
    refine Real.log_le_log (by exact_mod_cast h1) ?_
    exact_mod_cast ENat.toNat_le_toNat (hg δ δ' hδ hle) (hT δ hδ)
  have hH0 : ∀ δ, 0 ≤ H δ := fun δ => Real.log_natCast_nonneg _
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set a : ℕ → ℝ := fun n => lgdRatio g ((2 : ℝ)⁻¹ ^ n)
  have ha : ∀ n, a n = H ((2 : ℝ)⁻¹ ^ n) / (n * Real.log 2) := fun n => by
    simp only [a, lgdRatio, log_inv_two_inv_pow, H]
  set lo : ℕ → ℝ := fun N => H ((2 : ℝ)⁻¹ ^ N) / ((N + 1) * Real.log 2)
  set up : ℕ → ℝ := fun N => H ((2 : ℝ)⁻¹ ^ (N + 1)) / (N * Real.log 2)
  have hlo : Tendsto lo atTop (𝓝 χ) := by
    have := h.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    show a N * (N / (N + 1)) = lo N
    rw [ha]
    simp only [lo]
    field_simp
  have hup : Tendsto up atTop (𝓝 χ) := by
    have hr : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      field_simp
    have := (h.comp (tendsto_add_atTop_nat 1)).mul hr
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    show a (N + 1) * ((N + 1) / N) = up N
    rw [ha]
    simp only [up]
    push_cast
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlo.comp tendsto_dyScale)
    (hup.comp tendsto_dyScale) ?_ ?_
  all_goals
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2⁻¹ by norm_num)] with δ hδ
    have hδ0 := hδ.1
    have hδ1 : δ ≤ 1 := hδ.2.le.trans (by norm_num)
    obtain ⟨h1, h2⟩ := dyScale_spec hδ0 hδ1
    set N := dyScale δ
    have hinv : (2 : ℝ) < δ⁻¹ := by
      have := (inv_lt_inv₀ (by norm_num) hδ0).2 hδ.2
      rwa [inv_inv] at this
    have hN : 1 ≤ N := by
      have := (pow_lt_pow_iff_right₀ one_lt_two).1
        ((show (2 : ℝ) ^ 1 < δ⁻¹ by rw [pow_one]; exact hinv).trans h2)
      omega
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hL1 : (N : ℝ) * Real.log 2 ≤ Real.log δ⁻¹ := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h1
    have hL2 : Real.log δ⁻¹ ≤ ((N : ℝ) + 1) * Real.log 2 := by
      rw [show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; ring, ← Real.log_pow]
      exact Real.log_le_log (by positivity) h2.le
    have hd1 : δ ≤ (2 : ℝ)⁻¹ ^ N := by
      rw [inv_pow]
      have := (inv_le_inv₀ (by positivity) (by positivity)).2 h1
      rwa [inv_inv] at this
    have hd2 : (2 : ℝ)⁻¹ ^ (N + 1) ≤ δ := by
      rw [inv_pow]
      have := (inv_le_inv₀ (by positivity) (by positivity)).2 h2.le
      rwa [inv_inv] at this
    have hLp : 0 < Real.log δ⁻¹ := lt_of_lt_of_le (by positivity) hL1
  · exact div_le_div₀ (hH0 δ) (hH δ _ hδ0 hd1) hLp hL2
  · exact div_le_div₀ (hH0 _) (hH _ δ (by positivity) hd2) (by positivity) hL1

end GMCIdent4
end LQGMetric
