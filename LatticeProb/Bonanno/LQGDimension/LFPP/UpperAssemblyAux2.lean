/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.UpperAssemblyAux2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.UpperAssemblyAux1

/-!
# Auxiliary lemmas for the conditional assembly of (1.7) (`Draft.UpperAssembly`), part 2

* summability of the series `Σ_k N(k) exp(t m(k) + κ t² v(k))` of (4.8) under the crude mean
  bound (4.5) and a `√(k+1)` variance bound (needed as a hypothesis of `ChainUnionBound`, and
  not provided by `ZLimitBound`);
* the variance of a chain sum of local variables is `δ⁻¹` times the circle-average variance of
  the concatenated test combination (through `SegCombLaw`);
* the geometric tail `Σ_{l ≥ L} e^{-l} ≤ 2 e^{-L}` in `ℝ≥0∞`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped Classical

namespace LQGDimension

namespace UpperAssemblyAux

open Blueprint.Draft

/-! ### Summability of the chain generating series -/

theorem summable_chain_terms (A D Cn b κ t : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b) (ht : 0 < t)
    (m v : ℕ → ℝ) (hm : ∀ k : ℕ, m k ≤ Cn * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k)
    (hv : ∀ k : ℕ, κ * t ^ 2 * v k ≤ b * Real.sqrt ((k : ℝ) + 1)) :
    Summable (fun k : ℕ => A * ((k : ℝ) + 1) ^ D * Real.exp (t * m k + κ * t ^ 2 * v k)) := by
  set a : ℝ := t * |Cn| + b with ha_def
  have ha : 0 ≤ a := by positivity
  set s : ℝ := t / 2 with hs_def
  have hs : 0 < s := by positivity
  set K0 : ℝ := t / 2 + a ^ 2 / (2 * t) with hK0
  set m' : ℕ := ⌈D⌉₊ with hm'
  have hg : Summable (fun k : ℕ =>
      (A * Real.exp K0) * (((k : ℝ) + 1) ^ m' * Real.exp (-(s * k)))) := by
    apply Summable.mul_left
    have h1 := Real.summable_pow_mul_exp_neg_nat_mul m' hs
    have h2 := (summable_nat_add_iff 1).mpr h1
    have h3 := h2.mul_left (Real.exp s)
    refine h3.congr (fun k => ?_)
    push_cast
    rw [show -(s * (k : ℝ)) = s + -s * ((k : ℝ) + 1) by ring, Real.exp_add]
    ring
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hg
  set y : ℝ := (k : ℝ) + 1 with hy_def
  have hy1 : 1 ≤ y := by rw [hy_def]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hy0 : 0 ≤ y := by linarith
  -- exponent bound
  have hq : y ^ (1 / 4 : ℝ) ≤ Real.sqrt y := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
  have hq0 : 0 ≤ y ^ (1 / 4 : ℝ) := Real.rpow_nonneg hy0 _
  have hCn : Cn * y ^ (1 / 4 : ℝ) ≤ |Cn| * Real.sqrt y := by
    calc Cn * y ^ (1 / 4 : ℝ) ≤ |Cn| * y ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hq0
      _ ≤ |Cn| * Real.sqrt y := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  have hamgm : a * Real.sqrt y ≤ t / 2 * y + a ^ 2 / (2 * t) := by
    have hsq := Real.sq_sqrt hy0
    rw [show t / 2 * y + a ^ 2 / (2 * t) = (t ^ 2 * y + a ^ 2) / (2 * t) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (t * Real.sqrt y - a)]
  have hE : t * m k + κ * t ^ 2 * v k ≤ -(s * k) + K0 := by
    have h1 : t * m k ≤ t * (Cn * y ^ (1 / 4 : ℝ) - k) := mul_le_mul_of_nonneg_left (hm k) ht.le
    have h2 := hv k
    have h3 : t * (Cn * y ^ (1 / 4 : ℝ)) ≤ t * (|Cn| * Real.sqrt y) :=
      mul_le_mul_of_nonneg_left hCn ht.le
    have h4 : t * (|Cn| * Real.sqrt y) + b * Real.sqrt y = a * Real.sqrt y := by
      rw [ha_def]; ring
    rw [hs_def, hK0]
    rw [hy_def] at hamgm
    nlinarith
  have hpow : y ^ D ≤ y ^ m' := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hy1 (Nat.le_ceil D)
  have hexp : Real.exp (t * m k + κ * t ^ 2 * v k) ≤ Real.exp K0 * Real.exp (-(s * k)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  calc A * y ^ D * Real.exp (t * m k + κ * t ^ 2 * v k)
      ≤ A * y ^ m' * (Real.exp K0 * Real.exp (-(s * k))) := by
        gcongr
    _ = (A * Real.exp K0) * (y ^ m' * Real.exp (-(s * k))) := by ring

/-! ### Variance of chain sums -/

theorem variance_coord_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}
    {F : Finset ι} {C : ι → ι → ℝ} {Y : Ω → F → ℝ} (hY : HasLaw Y (gaussVecLaw F C) P)
    (i : F) : Var[fun ω => Y ω i; P] ≤ max (C i i) 0 := by
  have hYi : AEMeasurable (fun y : F → ℝ => y i) (P.map Y) :=
    (measurable_pi_apply i).aemeasurable
  have h1 : Var[fun ω => Y ω i; P] = Var[fun y : F → ℝ => y i; P.map Y] := by
    rw [variance_map hYi hY.aemeasurable]; rfl
  rw [h1, hY.map_eq, gaussVecLaw,
    variance_map (measurable_pi_apply i).aemeasurable (by fun_prop)]
  by_cases hS : (Matrix.of fun i j : F => C i j).PosSemidef
  · have h2 := variance_eval_multivariateGaussian (μ := 0) hS i
    have e : ((fun y : F → ℝ => y i) ∘ fun (x : EuclideanSpace ℝ F) (j : F) => x j) =
        fun x => x i := rfl
    rw [e, h2]
    exact le_max_left _ _
  · rw [multivariateGaussian_of_not_posSemidef _ hS, variance_dirac]
    exact le_max_right _ _

theorem rpow_neg_half_sq {δ : ℝ} (hδ : 0 < δ) : (δ ^ (-(1 / 2 : ℝ))) ^ 2 = δ⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
  norm_num
  exact Real.rpow_neg_one δ

/-- The variance of a chain sum of local variables under `h_ε`. -/
theorem variance_chain_le (hP1 : SegCombLaw) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : ℝ → ℂ → Ω → ℝ} (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε) {δ : ℝ}
    (hδ : 0 < δ) (k : ℕ → ℕ) (c : ℕ → Config) (l : ℕ) :
    Var[fun ω => ∑ i ∈ Finset.range l, cfgVal (fun z => h ε z ω) δ (k i) (c i); P] ≤
      max (δ⁻¹ * (sumComb c l).circCov ε (sumComb c l)) 0 := by
  have := hG.isProbabilityMeasure
  have hlaw := hP1 Ω P h hG ε hε Unit {()} (fun _ => sumComb c l)
  set i0 : ({()} : Finset Unit) := ⟨(), Finset.mem_singleton_self _⟩
  set Y : Ω → ℝ := fun ω => (sumComb c l).avg (fun z => h ε z ω) with hY_def
  have hYm : AEMeasurable Y P := (measurable_pi_apply i0).comp_aemeasurable hlaw.aemeasurable
  have hvarY : Var[Y; P] ≤ max ((sumComb c l).circCov ε (sumComb c l)) 0 :=
    variance_coord_le hlaw i0
  have hfun : (fun ω => ∑ i ∈ Finset.range l, cfgVal (fun z => h ε z ω) δ (k i) (c i)) =
      fun ω => δ ^ (-(1 / 2 : ℝ)) * Y ω - ∑ i ∈ Finset.range l, (k i : ℝ) := by
    funext ω
    rw [sum_cfgVal_eq]
  rw [hfun, variance_sub_const (by fun_prop), variance_const_mul, rpow_neg_half_sq hδ]
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.le
  calc δ⁻¹ * Var[Y; P] ≤ δ⁻¹ * max ((sumComb c l).circCov ε (sumComb c l)) 0 :=
        mul_le_mul_of_nonneg_left hvarY hδi
    _ = max (δ⁻¹ * (sumComb c l).circCov ε (sumComb c l)) 0 := by
        rw [mul_max_of_nonneg _ _ hδi, mul_zero]

/-! ### Geometric tail -/

theorem tsum_exp_tail_le (L : ℕ) :
    ∑' l : ℕ, ENNReal.ofReal (Real.exp (-(((l + L : ℕ) : ℝ)))) ≤
      ENNReal.ofReal (2 * Real.exp (-(L : ℝ))) := by
  have hle : ∀ l : ℕ, Real.exp (-(((l + L : ℕ) : ℝ))) ≤ Real.exp (-(L : ℝ)) * (1 / 2) ^ l := by
    intro l
    have he1 : Real.exp (-1) ≤ 1 / 2 := by
      have := Real.add_one_le_exp 1
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    have e : Real.exp (-(((l + L : ℕ) : ℝ))) = Real.exp (-(L : ℝ)) * Real.exp (-1) ^ l := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      ring_nf
    rw [e]
    gcongr
  have hsum : Summable (fun l : ℕ => Real.exp (-(L : ℝ)) * (1 / 2 : ℝ) ^ l) :=
    summable_geometric_two.mul_left _
  have hsum' : Summable (fun l : ℕ => Real.exp (-(((l + L : ℕ) : ℝ)))) :=
    Summable.of_nonneg_of_le (fun l => (Real.exp_pos _).le) hle hsum
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => (Real.exp_pos _).le) hsum']
  apply ENNReal.ofReal_le_ofReal
  calc ∑' l : ℕ, Real.exp (-(((l + L : ℕ) : ℝ)))
      ≤ ∑' l : ℕ, Real.exp (-(L : ℝ)) * (1 / 2 : ℝ) ^ l := hsum'.tsum_le_tsum hle hsum
    _ = 2 * Real.exp (-(L : ℝ)) := by rw [tsum_mul_left, tsum_geometric_two]; ring

end UpperAssemblyAux

end LQGDimension
