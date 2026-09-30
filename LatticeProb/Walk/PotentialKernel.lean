import Mathlib
import LatticeProb.Walk.PotentialKernelFourier
import LatticeProb.Walk.GaussTimeIntegral
import LatticeProb.Walk.LogTimeIntegral
import LatticeProb.Walk.SRWSup

/-!
# The planar potential kernel

`potentialKernel x = lim_M [G_M(0) - G_M(x)]`, the limit of the partial sums
`∑_{j<M} [P^j(0,0) - P^j(0,x)]` of the simple random walk on `ℤ²`. The limit exists for every
`x` (`tendsto_potentialKernel`); the kernel vanishes at the origin and solves
`(P - I) b = δ₀`. Its asymptotics are `b(x) = (2/π) log |x| + κ + O(|x|^{-2})`
(Lawler–Limic, *Random Walk: A Modern Introduction*, Theorem 4.4.4;
`exists_abs_potentialKernel_sub_log_le`): the kernel is `∫_0^∞ [q_t(0) - q_t(x)] dt` for the
continuous-time kernel `q_t`, the Gaussian part of which gives the logarithm, and the
local limit error and the times `t ≤ 1` give `O(|x|^{-2})`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb

open ContinuousTime

/-- The planar potential kernel `b(x) = lim_M [G_M(0) - G_M(x)]`, the limit of the partial
sums `∑_{j<M} [P^j(0,0) - P^j(0,x)]` (`tendsto_potentialKernel` proves that it exists). -/
def potentialKernel (x : Site 2) : ℝ :=
  limUnder atTop fun M : ℕ => srwGreen 2 M 0 - srwGreen 2 M x

/-- The partial sums `G_M(0) - G_M(x)` converge to the potential kernel. -/
theorem tendsto_potentialKernel (x : Site 2) :
    Tendsto (fun M : ℕ => srwGreen 2 M 0 - srwGreen 2 M x) atTop (𝓝 (potentialKernel x)) :=
  tendsto_nhds_limUnder ⟨_, tendsto_srwGreen_sub_fourierPotential x⟩

/-- The potential kernel is its Fourier form
`(2π)^{-2} ∫ (1 - cos θ·x)/(1 - φ(θ)) dθ`. -/
theorem potentialKernel_eq_fourierPotential (x : Site 2) :
    potentialKernel x = fourierPotential x :=
  tendsto_nhds_unique (tendsto_potentialKernel x) (tendsto_srwGreen_sub_fourierPotential x)

/-- The potential kernel vanishes at the origin. -/
theorem potentialKernel_zero : potentialKernel 0 = 0 :=
  tendsto_nhds_unique (tendsto_potentialKernel 0) (by simp)

/-- The potential kernel solves `(P - I) b = δ₀`: the partial sums satisfy
`(P - I)(G_M(0) - G_M) = δ₀ - p_M` and `p_M → 0`. -/
theorem walkOp_potentialKernel_sub (x : Site 2) :
    walkOp potentialKernel x - potentialKernel x = if x = 0 then 1 else 0 := by
  set S : ℕ → Site 2 → ℝ := fun M y => srwGreen 2 M 0 - srwGreen 2 M y with hS
  have hwalk_add : ∀ (u v : Site 2 → ℝ) (y : Site 2),
      walkOp (fun z => u z + v z) y = walkOp u y + walkOp v y := by
    intro u v y
    simp only [walkOp, nbrSum, ← add_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hwalk_neg : ∀ (u : Site 2 → ℝ) (y : Site 2),
      walkOp (fun z => -u z) y = -walkOp u y := by
    intro u y
    simp only [walkOp, nbrSum, ← neg_div, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hwalk_const : ∀ (c : ℝ) (y : Site 2), walkOp (fun _ => c) y = c := by
    intro c y
    simp only [walkOp, nbrSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
    ring
  have hstep : ∀ M : ℕ, walkOp (S M) x - S M x = srwHeat 2 0 x - srwHeat 2 M x := by
    intro M
    induction M with
    | zero =>
        simp only [hS, srwGreen_zero, sub_self]
        simp [walkOp, nbrSum]
    | succ M ih =>
        have hsplit : S (M + 1) = fun y => S M y + (fun z => srwHeat 2 M 0 + -srwHeat 2 M z) y := by
          funext y
          simp only [hS, srwGreen_succ]
          ring
        rw [hsplit, hwalk_add, hwalk_add, hwalk_const, hwalk_neg, srwHeat_succ]
        simp only at ih ⊢
        linarith
  have hheat : Tendsto (fun M : ℕ => srwHeat 2 M x) atTop (𝓝 0) := by
    have hb : ∀ M : ℕ, 1 ≤ M → srwHeat 2 M x
        ≤ Real.sqrt 2 ^ 2 * greenConst 2 * (M : ℝ) ^ (-((2 : ℕ) : ℝ) / 2) :=
      fun M hM => srwHeat_sup_bound (by norm_num) hM x
    have hlim : Tendsto
        (fun M : ℕ => Real.sqrt 2 ^ 2 * greenConst 2 * (M : ℝ) ^ (-((2 : ℕ) : ℝ) / 2))
        atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
        tendsto_natCast_atTop_atTop
      have h2 := h.const_mul (Real.sqrt 2 ^ 2 * greenConst 2)
      rw [mul_zero] at h2
      refine h2.congr' (Filter.Eventually.of_forall fun M => ?_)
      simp only [Function.comp]
      norm_num
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun M => srwHeat_nonneg M x)
      (Filter.eventually_atTop.mpr ⟨1, fun M hM => hb M hM⟩)
  have hwalkT : Tendsto (fun M => walkOp (S M) x) atTop (𝓝 (walkOp potentialKernel x)) := by
    simp only [walkOp, nbrSum]
    refine Tendsto.div_const (tendsto_finsetSum _ fun i _ => ?_) _
    exact (tendsto_potentialKernel _).add (tendsto_potentialKernel _)
  have hlim := (hwalkT.sub (tendsto_potentialKernel x))
  have hlim2 : Tendsto (fun M => walkOp (S M) x - S M x) atTop (𝓝 (srwHeat 2 0 x - 0)) := by
    simp_rw [hstep]
    exact tendsto_const_nhds.sub hheat
  rw [sub_zero, srwHeat_zero] at hlim2
  exact tendsto_nhds_unique hlim hlim2

/-- **The planar potential kernel asymptotics** (Lawler–Limic, Theorem 4.4.4):
`|b(x) - ((2/π) log |x| + κ)| ≤ C |x|^{-2}` for `|x| ≥ 1`. The kernel is
`∫_0^∞ [q_t(0) - q_t(x)] dt`; the Gaussian part gives `(2/π) log |x|` plus a constant, and
the rest is split at time one. -/
theorem exists_abs_potentialKernel_sub_log_le :
    ∃ κ C R : ℝ, 1 ≤ R ∧ ∀ x : Site 2, R ≤ euclidNorm x →
      |potentialKernel x - (2 / Real.pi * Real.log (euclidNorm x) + κ)|
        ≤ C * euclidNorm x ^ (-2 : ℝ) := by
  obtain ⟨C₁, hC₁, h₁⟩ :=
    exists_norm_integral_ctHeat_sub_ctGauss_le (d := 2) (by norm_num)
  obtain ⟨κ₁, C₃, h₃⟩ := exists_integral_log_integrand
  have hC₃ : 0 ≤ C₃ := by
    have h := h₃ 1 le_rfl
    have : (0 : ℝ) ≤ C₃ * 1 ^ (-2 : ℝ) := (abs_nonneg _).trans h
    simpa using this
  set E₀ := ∫ t in Set.Ioi 1, (ctHeat 2 t 0 - ctGauss 2 t 0) with hE₀
  set Q₀ := ∫ t in Set.Ioc 0 1, ctHeat 2 t 0 with hQ₀
  refine ⟨Q₀ + E₀ + κ₁ / Real.pi,
    Real.exp 1 * (2 ^ 2 * (2 : ℕ).factorial) + C₁ + C₃ / Real.pi,
    1, le_rfl, fun x hx => ?_⟩
  set r := euclidNorm x with hr
  have hr0 : 0 < r := by linarith
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [hr] at hr0
  have hpi := Real.pi_pos
  -- the Gaussian part of the kernel difference
  have hgdiff : ∀ t ∈ Set.Ioi (0 : ℝ), ctGauss 2 t 0 - ctGauss 2 t x
      = Real.pi⁻¹ * ((1 - Real.exp (-r ^ 2 / t)) / t) := by
    intro t ht
    rw [ctGauss_eq (by norm_num) ht, ctGauss_eq (by norm_num) ht, euclidNorm_zero]
    have htpos : 0 < t := ht
    have h1 : (2 * Real.pi / ((2 : ℕ) : ℝ)) ^ (-((2 : ℕ) : ℝ) / 2) = Real.pi⁻¹ := by
      norm_num [Real.rpow_neg_one]
    have h2 : t ^ (-(((2 : ℕ) : ℝ) / 2)) = t⁻¹ := by norm_num [Real.rpow_neg_one]
    rw [h1, h2, ← hr]
    have h3 : -(((2 : ℕ) : ℝ) * r ^ 2 / 2) / t = -r ^ 2 / t := by push_cast; ring
    rw [h3]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      neg_zero, Real.exp_zero, mul_one]
    field_simp
  -- integrability of the pieces
  have hqI : ∀ y : Site 2, IntegrableOn (fun t => ctHeat 2 t y) (Set.Ioc 0 1) :=
    fun y => (continuous_ctHeat y).integrableOn_Ioc
  have hL := integrableOn_log_integrand r
  have he0 := integrableOn_ctHeat_sub_ctGauss (d := 2) (by norm_num) (0 : Site 2)
  have hex := integrableOn_ctHeat_sub_ctGauss (d := 2) (by norm_num) x
  have hD1 : ∀ t ∈ Set.Ioi (1 : ℝ), ctHeat 2 t 0 - ctHeat 2 t x
      = (ctHeat 2 t 0 - ctGauss 2 t 0) - (ctHeat 2 t x - ctGauss 2 t x)
        + Real.pi⁻¹ * ((1 - Real.exp (-r ^ 2 / t)) / t) := by
    intro t ht
    rw [← hgdiff t (Set.mem_Ioi.mpr (lt_trans zero_lt_one ht))]
    ring
  have hDint1 : IntegrableOn (fun t => ctHeat 2 t 0 - ctHeat 2 t x) (Set.Ioi 1) :=
    ((he0.sub hex).add (hL.const_mul Real.pi⁻¹)).congr_fun
      (fun t ht => (hD1 t ht).symm) measurableSet_Ioi
  -- the split at time one
  have hsplit : potentialKernel x
      = (Q₀ - ∫ t in Set.Ioc 0 1, ctHeat 2 t x)
        + (E₀ - (∫ t in Set.Ioi 1, (ctHeat 2 t x - ctGauss 2 t x))
          + Real.pi⁻¹ * ∫ t in Set.Ioi 1, (1 - Real.exp (-r ^ 2 / t)) / t) := by
    rw [potentialKernel_eq_fourierPotential, fourierPotential_eq_integral_ctHeat,
      ← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (f := fun t => ctHeat 2 t 0 - ctHeat 2 t x)
        (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ((hqI 0).sub (hqI x)) hDint1,
      integral_sub (hqI 0) (hqI x), setIntegral_congr_fun measurableSet_Ioi hD1,
      integral_add (f := fun t => (ctHeat 2 t 0 - ctGauss 2 t 0) - (ctHeat 2 t x - ctGauss 2 t x))
        (g := fun t => Real.pi⁻¹ * ((1 - Real.exp (-r ^ 2 / t)) / t)) (he0.sub hex)
        (hL.const_mul _),
      integral_sub he0 hex, integral_const_mul]
  have hlog := h₃ r hx
  have hsmall := norm_integral_Ioc_ctHeat_le (d := 2) (by norm_num) x
  have hbig := h₁ x hx
  have hexp := exp_neg_half_le_rpow hr0 2
  have hrpow2 : r ^ (-((2 : ℕ) : ℝ)) = r ^ (-2 : ℝ) := by norm_num
  rw [hrpow2] at hexp
  have hrr : 0 < r ^ (-2 : ℝ) := Real.rpow_pos_of_pos hr0 _
  rw [← Real.norm_eq_abs] at hlog
  have hrearr : potentialKernel x - (2 / Real.pi * Real.log r + (Q₀ + E₀ + κ₁ / Real.pi))
      = -(∫ t in Set.Ioc 0 1, ctHeat 2 t x) - (∫ t in Set.Ioi 1, (ctHeat 2 t x - ctGauss 2 t x))
        + Real.pi⁻¹ * ((∫ t in Set.Ioi 1, (1 - Real.exp (-r ^ 2 / t)) / t)
          - (2 * Real.log r + κ₁)) := by
    rw [hsplit]
    ring
  rw [hrearr, ← Real.norm_eq_abs]
  have hsmall' : ‖∫ t in Set.Ioc 0 1, ctHeat 2 t x‖
      ≤ Real.exp 1 * (2 ^ 2 * (2 : ℕ).factorial) * r ^ (-2 : ℝ) := by
    refine hsmall.trans ?_
    rw [mul_assoc]
    gcongr
  have hlog' : ‖Real.pi⁻¹ * ((∫ t in Set.Ioi 1, (1 - Real.exp (-r ^ 2 / t)) / t)
      - (2 * Real.log r + κ₁))‖ ≤ C₃ / Real.pi * r ^ (-2 : ℝ) := by
    rw [norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hpi, div_eq_inv_mul, mul_assoc]
    gcongr
  calc _ ≤ ‖-(∫ t in Set.Ioc 0 1, ctHeat 2 t x)
          - (∫ t in Set.Ioi 1, (ctHeat 2 t x - ctGauss 2 t x))‖
        + ‖Real.pi⁻¹ * ((∫ t in Set.Ioi 1, (1 - Real.exp (-r ^ 2 / t)) / t)
          - (2 * Real.log r + κ₁))‖ := norm_add_le _ _
    _ ≤ (‖∫ t in Set.Ioc 0 1, ctHeat 2 t x‖
          + ‖∫ t in Set.Ioi 1, (ctHeat 2 t x - ctGauss 2 t x)‖)
        + C₃ / Real.pi * r ^ (-2 : ℝ) := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ (Real.exp 1 * (2 ^ 2 * (2 : ℕ).factorial) * r ^ (-2 : ℝ) + C₁ * r ^ (-2 : ℝ))
        + C₃ / Real.pi * r ^ (-2 : ℝ) := by
        gcongr
        simpa using hbig
    _ = _ := by ring

end LatticeProb
