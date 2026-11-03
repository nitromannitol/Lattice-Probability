/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Analysis.Multiplicative at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Multiplicative scaling constants (GM Lemma 1.10, proof)

* `LQGMetric.Analysis.exists_rpow_of_mul_of_continuousOn` (node GM.S1.11): a continuous map
  `𝔨 : (0,∞) → (0,∞)` with `𝔨 (b₁ b₂) = 𝔨 b₁ 𝔨 b₂` is `b ↦ b ^ α`.
  `exists_rpow_of_mul_of_measurable`: the same for a Borel-measurable `𝔨` (GM's parenthetical
  "actually, just Lebesgue measurability is enough"; we prove the Borel version).
  Source: Gwynne–Miller, *Existence and uniqueness of the LQG metric*, arXiv:1905.00383, proof of
  Lemma 1.10 (`uniqueness-final.tex` l. 519). The proof is the standard Cauchy-equation argument:
  `t ↦ log 𝔨 (eᵗ)` is a continuous additive map `ℝ → ℝ`, hence linear (mathlib
  `map_real_smul`; measurable ⇒ continuous by `AddMonoidHom.continuous_of_measurable`).
* `LQGMetric.Analysis.eq_one_of_map_const_mul_eq_map` (core of node GM.S1.10): if `X ∈ (0,∞)`
  a.s. and `k X` has the law of `X` for a constant `k > 0`, then `k = 1` (the implicit step
  "`𝔨_b D_h → D_h` in law forces `𝔨_b → 1`", GM l. 515–517, applied to `D_h(0,1)`). GM give no
  proof; own elementary proof: the law `μ` satisfies `μ (Iic t) = μ (Iic (t/k))`, iterating gives
  `μ (Iic t) = μ (Iic 0) = 0` if `k > 1`, so `μ = 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric
namespace Analysis

open MeasureTheory Set Filter Topology

/-- Core of GM.S1.11: if `t ↦ log (𝔨 (exp t))` is continuous, a multiplicative positive `𝔨`
is a power. -/
lemma exists_rpow_of_mul_of_continuous_logExp (k : ℝ → ℝ) (hpos : ∀ b, 0 < b → 0 < k b)
    (hmul : ∀ b₁ b₂, 0 < b₁ → 0 < b₂ → k (b₁ * b₂) = k b₁ * k b₂)
    (hF : Continuous fun t => Real.log (k (Real.exp t))) :
    ∃ α : ℝ, ∀ b, 0 < b → k b = b ^ α := by
  let F : ℝ →+ ℝ := AddMonoidHom.mk' (fun t => Real.log (k (Real.exp t))) (by
    intro s t
    rw [Real.exp_add, hmul _ _ (Real.exp_pos s) (Real.exp_pos t),
      Real.log_mul (hpos _ (Real.exp_pos s)).ne' (hpos _ (Real.exp_pos t)).ne'])
  refine ⟨F 1, fun b hb => ?_⟩
  have h1 : F (Real.log b) = Real.log b * F 1 := by
    simpa [smul_eq_mul] using map_real_smul F hF (Real.log b) 1
  have h2 : F (Real.log b) = Real.log (k b) := by
    simp [F, Real.exp_log hb]
  rw [Real.rpow_def_of_pos hb, ← h1, h2, Real.exp_log (hpos b hb)]

/-- If the distribution function of a finite measure on `ℝ` is invariant under `t ↦ t / c` with
`c > 1` and the measure gives no mass to `(-∞,0]`, the measure is zero. -/
lemma measure_eq_zero_of_Iic_div_invariant {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hsupp : μ (Iic 0) = 0) {c : ℝ} (hc : 1 < c)
    (h : ∀ t, μ (Iic t) = μ (Iic (t / c))) : μ = 0 := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hiter : ∀ t (n : ℕ), μ (Iic t) = μ (Iic (t / c ^ n)) := by
    intro t n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, h, pow_succ, div_div]
  have hzero : ∀ t, 0 < t → μ (Iic t) = 0 := by
    intro t ht
    have hanti : Antitone fun n : ℕ => Iic (t / c ^ n) := by
      intro m n hmn
      exact Iic_subset_Iic.2 (div_le_div_of_nonneg_left ht.le (pow_pos hc0 m)
        (pow_le_pow_right₀ hc.le hmn))
    have hT := tendsto_measure_iInter_atTop (μ := μ) (fun n => measurableSet_Iic.nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    have hconst : (μ ∘ fun n : ℕ => Iic (t / c ^ n)) = fun _ => μ (Iic t) := by
      funext n; exact (hiter t n).symm
    rw [hconst] at hT
    have heq := tendsto_nhds_unique tendsto_const_nhds hT
    have hsub : (⋂ n : ℕ, Iic (t / c ^ n)) ⊆ Iic 0 := by
      intro x hx
      by_contra hx0
      have hx0 : 0 < x := lt_of_not_ge hx0
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (t / x) hc
      have := mem_iInter.1 hx n
      rw [mem_Iic, le_div_iff₀ (pow_pos hc0 n)] at this
      rw [div_lt_iff₀ hx0] at hn
      linarith [mul_comm x (c ^ n)]
    exact le_antisymm (heq ▸ (measure_mono hsub).trans hsupp.le) (zero_le)
  have huniv : (univ : Set ℝ) ⊆ ⋃ n : ℕ, Iic ((n : ℝ) + 1) := by
    intro x _
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact mem_iUnion.2 ⟨n, by simp only [mem_Iic]; linarith⟩
  have : μ univ = 0 :=
    measure_mono_null huniv (measure_iUnion_null fun n => hzero _ (by positivity))
  exact Measure.measure_univ_eq_zero.1 this

end Analysis
end LQGMetric
