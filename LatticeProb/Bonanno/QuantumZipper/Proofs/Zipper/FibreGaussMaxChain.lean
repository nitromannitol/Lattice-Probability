/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.FibreGaussMaxChain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Chaining on a box with a Hölder increment bound (FIBRE-GAUSSMAX-CHAIN)

Hölder-exponent version of `LQGDimension.ChainBox.chainingBox_bound`: if the parameters
`p i ∈ ℝ^d` (sup norm) have diameter at most `a` on `F` and
`‖v i - v j‖² ≤ L² ‖p i - p j‖^β` on `F` (`0 < β ≤ 1`), then for `i₀ ∈ F`,
`E max_{i ∈ F} ⟪v i - v i₀, x⟫ ≤ fgmChainConst d β · L · a^{β/2}`.

Sources: generic (Dudley) chaining, M. Talagrand, *Upper and Lower Bounds for Stochastic
Processes* (2nd ed.), §2.2; R. Adler, J. Taylor, *Random Fields and Geometry*, Thm 1.3.3
(Dudley's entropy bound).  The proof is a line-by-line adaptation of
`LQGDimension.ChainBox.chainingBox_bound_pos` and reuses its cell/projection machinery; only
the level sizes change: the parameter step at level `k` is `≤ 5a/4^{k+1}`, so the increments
have norm `≤ σ_k = L (5a)^{β/2} r^{k+1}` with `r = 2^{-β} ∈ (0,1)`, the per-level bound is
`10 √(d+1) σ_k (k+1)` as before, and `∑_{k<K} (k+1) r^{k+1} ≤ r/(1-r)²` (mathlib's
`hasSum_coe_mul_geometric_of_norm_lt_one`).  The hypothesis `β ≤ 1` is not needed by the proof.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped RealInnerProductSpace
open LQGDimension LQGDimension.ChainBox

namespace QuantumZipper.RegUnif

/-- The explicit chaining constant `10 √(d+1) 5^{β/2} / (1 - 2^{-β})²`. -/
def fgmChainConst (d : ℕ) (β : ℝ) : ℝ :=
  10 * √((d : ℝ) + 1) * (5 : ℝ) ^ (β / 2) / (1 - (2 : ℝ) ^ (-β)) ^ 2

theorem fgmChainConst_nonneg (d : ℕ) {β : ℝ} (hβ : 0 < β) : 0 ≤ fgmChainConst d β := by
  have _ := hβ
  unfold fgmChainConst
  positivity

section Main

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Hölder chaining bound in the nondegenerate case `L > 0`, `a > 0`. -/
theorem fgmChain_bound_pos {d : ℕ} (F : Finset ι) (p : ι → Fin d → ℝ) (v : ι → E)
    {L a β : ℝ} (hβ : 0 < β) (hL : 0 < L) (ha : 0 < a)
    (hp : ∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ ≤ a)
    (hv : ∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ^ 2 ≤ L ^ 2 * ‖p i - p j‖ ^ β) {i₀ : ι}
    (hi₀ : i₀ ∈ F) :
    vecExpectedMax F (fun i => v i - v i₀) 0 ≤ fgmChainConst d β * L * a ^ (β / 2) := by
  classical
  have hFne : F.Nonempty := ⟨i₀, hi₀⟩
  set r : ℝ := ((2 : ℝ) ^ β)⁻¹ with hrdef
  have hq1 : 1 < (2 : ℝ) ^ β := Real.one_lt_rpow (by norm_num) hβ
  have hr0 : 0 < r := inv_pos.2 (by linarith)
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hq1
  set w : ℕ → ι → E := fun k i => v (proj F p a i₀ (k + 1) i) - v (proj F p a i₀ k i) with hw
  set σ : ℕ → ℝ := fun k => L * (5 * a) ^ (β / 2) * r ^ (k + 1) with hσdef
  set s : ℝ := √((d : ℝ) + 1) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hσpos : ∀ k, 0 < σ k := fun k => by simp only [hσdef]; positivity
  -- the level sizes
  have hscale : ∀ k : ℕ, L ^ 2 * (5 * a / 4 ^ (k + 1)) ^ β = σ k ^ 2 := by
    intro k
    have h5a : ((5 * a) ^ (β / 2)) ^ 2 = (5 * a) ^ β := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have h4 : ((4 : ℝ) ^ (k + 1)) ^ β = (((2 : ℝ) ^ β) ^ (k + 1)) ^ 2 := by
      have e : (4 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1)) ^ 2 := by
        rw [← pow_mul, pow_mul']; norm_num
      rw [e, ← Real.rpow_pow_comm (x := (2 : ℝ) ^ (k + 1)) (by positivity) β 2,
        ← Real.rpow_pow_comm (x := (2 : ℝ)) (by norm_num) β (k + 1)]
    simp only [hσdef, hrdef]
    rw [Real.div_rpow (by positivity) (by positivity), h4, mul_pow, mul_pow, h5a, inv_pow]
    field_simp
  -- termination of the chain
  obtain ⟨K, hK1, hKsep⟩ := exists_level_sep F p (a := a)
  have hterm : ∀ i ∈ F, v (proj F p a i₀ K i) = v i := by
    intro i hi
    have hmem : proj F p a i₀ K i ∈ F := proj_mem hi₀ hi K
    have hpeq : p (proj F p a i₀ K i) = p i :=
      hKsep _ hmem i hi (norm_proj_sub_lt ha (by omega) hi)
    have h := hv _ hmem i hi
    rw [hpeq, sub_self, norm_zero, Real.zero_rpow hβ.ne', mul_zero] at h
    have h0 : ‖v (proj F p a i₀ K i) - v i‖ = 0 := by
      nlinarith [norm_nonneg (v (proj F p a i₀ K i) - v i)]
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  -- size of the increments
  have hwσ : ∀ k, ∀ i ∈ F, ‖w k i‖ ≤ σ k := by
    intro k i hi
    have hd1 := norm_proj_sub_le ha hp hi₀ hi (k + 1)
    have hd0 := norm_proj_sub_le ha hp hi₀ hi k
    have hdist : ‖p (proj F p a i₀ (k + 1) i) - p (proj F p a i₀ k i)‖ ≤
        5 * a / 4 ^ (k + 1) := by
      calc ‖p (proj F p a i₀ (k + 1) i) - p (proj F p a i₀ k i)‖
          = ‖(p (proj F p a i₀ (k + 1) i) - p i) - (p (proj F p a i₀ k i) - p i)‖ := by
            congr 1; abel
        _ ≤ ‖p (proj F p a i₀ (k + 1) i) - p i‖ + ‖p (proj F p a i₀ k i) - p i‖ :=
            norm_sub_le _ _
        _ ≤ a / 4 ^ (k + 1) + a / 4 ^ k := add_le_add hd1 hd0
        _ = 5 * a / 4 ^ (k + 1) := by rw [pow_succ]; field_simp; ring
    have hsq : ‖w k i‖ ^ 2 ≤ σ k ^ 2 := by
      calc ‖w k i‖ ^ 2 ≤ L ^ 2 * ‖p (proj F p a i₀ (k + 1) i) - p (proj F p a i₀ k i)‖ ^ β :=
            hv _ (proj_mem hi₀ hi (k + 1)) _ (proj_mem hi₀ hi k)
        _ ≤ L ^ 2 * (5 * a / 4 ^ (k + 1)) ^ β :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hdist hβ.le)
              (sq_nonneg L)
        _ = σ k ^ 2 := hscale k
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hσpos k).le two_ne_zero).1 hsq
  -- the increments only depend on the cells at levels `k` and `k + 1`
  set fk : ℕ → ι → (Fin d → ℤ) × (Fin d → ℤ) :=
    fun k i => (cell a k (p i), cell a (k + 1) (p i)) with hfk
  have hfib : ∀ k, ∀ i ∈ F, ∀ j ∈ F, fk k i = fk k j → w k i = w k j := by
    intro k i _ j _ h
    simp only [hfk, Prod.mk.injEq] at h
    simp only [hw]
    rw [proj_congr h.1, proj_congr h.2]
  -- counting the increments
  have hlog : ∀ k : ℕ, Real.log (F.image (fk k)).card ≤ 9 * ((d : ℝ) + 1) * ((k : ℝ) + 1) := by
    intro k
    have hsub : F.image (fk k) ⊆ box a k (p i₀) ×ˢ box a (k + 1) (p i₀) := by
      intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      exact Finset.mem_product.2 ⟨cell_mem_box ha k (hp i hi i₀ hi₀),
        cell_mem_box ha (k + 1) (hp i hi i₀ hi₀)⟩
    have hcard : (F.image (fk k)).card ≤ 4 ^ ((2 * k + 3) * d) := by
      calc (F.image (fk k)).card ≤ (box a k (p i₀) ×ˢ box a (k + 1) (p i₀)).card :=
            Finset.card_le_card hsub
        _ = (box a k (p i₀)).card * (box a (k + 1) (p i₀)).card := Finset.card_product _ _
        _ ≤ (4 ^ (k + 1)) ^ d * (4 ^ (k + 1 + 1)) ^ d :=
            Nat.mul_le_mul (card_box_le a k _) (card_box_le a (k + 1) _)
        _ = 4 ^ ((2 * k + 3) * d) := by
            rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    have hpos : (0 : ℝ) < (F.image (fk k)).card := by
      exact_mod_cast (hFne.image _).card_pos
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    calc Real.log (F.image (fk k)).card ≤ Real.log ((4 : ℝ) ^ ((2 * k + 3) * d)) :=
          Real.log_le_log hpos (by exact_mod_cast hcard)
      _ = (((2 * k + 3) * d : ℕ) : ℝ) * Real.log 4 := Real.log_pow _ _
      _ ≤ 9 * ((d : ℝ) + 1) * ((k : ℝ) + 1) := by
          push_cast
          have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith [mul_le_mul_of_nonneg_left hlog4 (by positivity : (0 : ℝ) ≤ (2 * k + 3) * d)]
  -- bound at each level
  have hlev : ∀ k ∈ Finset.range K,
      ∫ x, (⨆ i : F, ⟪w k i, x⟫) ∂stdGaussian E ≤ 10 * s * σ k * ((k : ℝ) + 1) := by
    intro k _
    have hl : 0 < s / σ k := div_pos hs (hσpos k)
    have h := integral_iSup_inner_le_of_fiber F hFne (fk k) (w k) (hfib k) hl (hwσ k)
    refine h.trans ?_
    rw [div_le_iff₀ hl]
    have hσne : σ k ≠ 0 := (hσpos k).ne'
    have e1 : (s / σ k) ^ 2 * σ k ^ 2 = s ^ 2 := by field_simp
    have e2 : 10 * s * σ k * ((k : ℝ) + 1) * (s / σ k) = 10 * s ^ 2 * ((k : ℝ) + 1) := by
      rw [mul_div_assoc', div_eq_iff hσne]; ring
    rw [e1, e2, hs2]
    have := hlog k
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg hd hk]
  -- pointwise chaining
  have hpt : ∀ x : E, (⨆ i : F, ⟪v i - v i₀, x⟫ + (0 : ι → ℝ) i) ≤
      ∑ k ∈ Finset.range K, ⨆ i : F, ⟪w k i, x⟫ := by
    intro x
    have : Nonempty F := hFne.to_subtype
    refine ciSup_le fun i => ?_
    have htel : ∑ k ∈ Finset.range K, w k i =
        v (proj F p a i₀ K i) - v (proj F p a i₀ 0 i) :=
      Finset.sum_range_sub (fun k => v (proj F p a i₀ k i)) K
    rw [hterm i i.2, proj_zero] at htel
    rw [Pi.zero_apply, add_zero, ← htel, sum_inner]
    exact Finset.sum_le_sum fun k _ =>
      le_ciSup (f := fun j : F => ⟪w k j, x⟫) (Set.finite_range _).bddAbove i
  have hint : ∀ k, Integrable (fun x => ⨆ i : F, ⟪w k i, x⟫) (stdGaussian E) :=
    fun k => integrable_iSup_inner F (w k)
  have hint0 : Integrable (fun x => ⨆ i : F, ⟪v i - v i₀, x⟫ + (0 : ι → ℝ) i)
      (stdGaussian E) := integrable_iSup_inner_add F (fun i => v i - v i₀) 0
  have h1 : vecExpectedMax F (fun i => v i - v i₀) 0 ≤
      ∫ x, (∑ k ∈ Finset.range K, ⨆ i : F, ⟪w k i, x⟫) ∂stdGaussian E :=
    integral_mono hint0 (integrable_finsetSum _ fun k _ => hint k) hpt
  rw [integral_finsetSum _ fun k _ => hint k] at h1
  -- the arithmetico-geometric sum
  have hsum : ∑ k ∈ Finset.range K, ((k : ℝ) + 1) * r ^ (k + 1) ≤ 1 / (1 - r) ^ 2 := by
    have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
    have hle := sum_le_hasSum (Finset.range (K + 1))
      (fun n _ => by positivity) (hasSum_coe_mul_geometric_of_norm_lt_one hnorm)
    rw [Finset.sum_range_succ'] at hle
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_succ] at hle
    refine hle.trans ?_
    have h1r : 0 < (1 - r) ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_right hr1.le h1r.le
  have hc : 0 ≤ 10 * s * (L * (5 * a) ^ (β / 2)) := by positivity
  calc vecExpectedMax F (fun i => v i - v i₀) 0
      ≤ ∑ k ∈ Finset.range K, ∫ x, (⨆ i : F, ⟪w k i, x⟫) ∂stdGaussian E := h1
    _ ≤ ∑ k ∈ Finset.range K, 10 * s * σ k * ((k : ℝ) + 1) := Finset.sum_le_sum hlev
    _ = 10 * s * (L * (5 * a) ^ (β / 2)) *
          ∑ k ∈ Finset.range K, ((k : ℝ) + 1) * r ^ (k + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hσdef]
        ring
    _ ≤ 10 * s * (L * (5 * a) ^ (β / 2)) * (1 / (1 - r) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hc
    _ = fgmChainConst d β * L * a ^ (β / 2) := by
        rw [fgmChainConst, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) ha.le, hsdef, hrdef]
        ring

/-- **Chaining on a box, Hölder version.**  If the parameters `p i ∈ ℝ^d` (sup norm) have
diameter at most `a` on `F` and `‖v i - v j‖² ≤ L² ‖p i - p j‖^β` on `F`, then for `i₀ ∈ F`,
`E max_{i ∈ F} ⟪v i - v i₀, x⟫ ≤ fgmChainConst d β · L · a^{β/2}`. -/
theorem fgmChain_bound {d : ℕ} (F : Finset ι) (p : ι → Fin d → ℝ) (v : ι → E)
    {L a β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 ≤ L)
    (hp : ∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ ≤ a)
    (hv : ∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ^ 2 ≤ L ^ 2 * ‖p i - p j‖ ^ β) {i₀ : ι}
    (hi₀ : i₀ ∈ F) :
    vecExpectedMax F (fun i => v i - v i₀) 0 ≤ fgmChainConst d β * L * a ^ (β / 2) := by
  have _ := hβ1
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (hp i₀ hi₀ i₀ hi₀)
  have hRHS : 0 ≤ fgmChainConst d β * L * a ^ (β / 2) :=
    mul_nonneg (mul_nonneg (fgmChainConst_nonneg d hβ) hL) (Real.rpow_nonneg ha0 _)
  have hdeg : (∀ i ∈ F, L ^ 2 * ‖p i - p i₀‖ ^ β = 0) →
      vecExpectedMax F (fun i => v i - v i₀) 0 ≤ fgmChainConst d β * L * a ^ (β / 2) := by
    intro h0
    have hv0 : ∀ i ∈ F, v i = v i₀ := by
      intro i hi
      have h := hv i hi i₀ hi₀
      rw [h0 i hi] at h
      have hn : ‖v i - v i₀‖ = 0 := by nlinarith [norm_nonneg (v i - v i₀)]
      exact sub_eq_zero.1 (norm_eq_zero.1 hn)
    rw [vecExpectedMax_sub_eq_zero F v i₀ hv0]
    exact hRHS
  rcases hL.eq_or_lt with hL0 | hLpos
  · exact hdeg fun i _ => by rw [← hL0]; ring
  rcases ha0.eq_or_lt with ha0' | hapos
  · refine hdeg fun i hi => ?_
    have : ‖p i - p i₀‖ = 0 :=
      le_antisymm ((hp i hi i₀ hi₀).trans ha0'.symm.le) (norm_nonneg _)
    rw [this, Real.zero_rpow hβ.ne', mul_zero]
  exact fgmChain_bound_pos F p v hβ hLpos hapos hp hv hi₀

end Main

end QuantumZipper.RegUnif
