/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperStep at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperAux

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Elementary estimates for the assembly of the upper half of DFGPS Lemma 3.6 (D52)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L36

lemma tendsto_rpow_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun δ : ℝ => δ ^ c) (𝓝[>] 0) (𝓝 0) := by
  have := Real.continuousAt_rpow_const 0 c (Or.inr hc.le)
  rw [ContinuousAt, Real.zero_rpow hc.ne'] at this
  exact this.mono_left nhdsWithin_le_nhds

lemma two_pow_mul_rk (n : ℕ) : (2:ℝ) ^ n * rk n = 1/2 := by
  unfold rk; rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num

lemma rpow_split {δ a : ℝ} (hδ : 0 < δ) : δ = δ ^ a * δ ^ (1 - a) := by
  rw [← Real.rpow_add hδ]; simp

lemma sixtyfour_le {δ a : ℝ} (hδ : 0 < δ) (N : ℕ) (h1 : δ ^ (1 - a) ≤ rk (N + 1))
    (h2 : δ ^ a ≤ 1/64) : 64 * δ ≤ rk (N + 1) := by
  have hs := rpow_split (a := a) hδ
  have hp := Real.rpow_pos_of_pos hδ (1 - a)
  have : 64 * δ ≤ δ ^ (1 - a) := by
    calc 64 * δ = 64 * δ ^ a * δ ^ (1 - a) := by rw [mul_assoc, ← hs]
      _ ≤ 1 * δ ^ (1 - a) := by gcongr; linarith
      _ = δ ^ (1 - a) := one_mul _
  linarith

lemma ratio_lt {δ a ρ₀ : ℝ} (hδ : 0 < δ) (N : ℕ) (h1 : δ ^ (1 - a) ≤ rk (N + 1))
    (h2 : δ ^ a < ρ₀) : ∀ k < N + 1, δ / rk k < ρ₀ := fun k hk => by
  have hrk : 2 * rk (N + 1) ≤ rk k := by
    have := rk_anti (show k ≤ N by omega)
    have e := rk_succ N
    linarith
  have hs := rpow_split (a := a) hδ
  have hpa := Real.rpow_pos_of_pos hδ a
  have hrk0 := rk_pos k
  rw [div_lt_iff₀ hrk0]
  calc δ = δ ^ a * δ ^ (1 - a) := hs
    _ ≤ δ ^ a * rk (N + 1) := by gcongr
    _ < ρ₀ * rk (N + 1) := by gcongr; exact rk_pos _
    _ ≤ ρ₀ * rk k := by
        have : 0 < ρ₀ := hpa.trans h2
        have := rk_pos (N + 1)
        nlinarith

lemma two_pow_mul_le {δ a : ℝ} (hδ : 0 < δ) (N : ℕ) (h1 : δ ^ (1 - a) ≤ rk (N + 1)) :
    (2:ℝ) ^ (N + 1) * δ ≤ δ ^ a := by
  have e := two_pow_mul_rk (N + 1)
  have hs := rpow_split (a := a) hδ
  have hpa := Real.rpow_pos_of_pos hδ a
  have hp2 : (0:ℝ) < 2 ^ (N + 1) := by positivity
  have h1' : δ ≤ δ ^ a * rk (N + 1) := by
    calc δ = δ ^ a * δ ^ (1 - a) := hs
      _ ≤ δ ^ a * rk (N + 1) := by gcongr
  calc (2:ℝ) ^ (N + 1) * δ ≤ 2 ^ (N + 1) * (δ ^ a * rk (N + 1)) := by gcongr
    _ = δ ^ a * (2 ^ (N + 1) * rk (N + 1)) := by ring
    _ = δ ^ a / 2 := by rw [e]; ring
    _ ≤ δ ^ a := by linarith

/-- sum of the box failure bounds -/
lemma box_sum_le {δ a m C p : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hp : 0 < p) (hmp : m ≤ a * p)
    (N : ℕ) (h1 : δ ^ (1 - a) ≤ rk (N + 1)) :
    ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (C * (δ / rk k) ^ p) ≤
      ENNReal.ofReal (max C 0 * (2 ^ p / (2 ^ p - 1)) * δ ^ m) := by
  have h2p : 1 < (2:ℝ) ^ p := Real.one_lt_rpow (by norm_num) hp
  have hnn : ∀ k, 0 ≤ (δ / rk k) ^ p := fun k =>
    Real.rpow_nonneg (div_nonneg hδ.le (rk_pos k).le) _
  calc ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (C * (δ / rk k) ^ p)
      ≤ ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (max C 0 * (δ / rk k) ^ p) :=
        Finset.sum_le_sum fun k _ => ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn k))
    _ = ENNReal.ofReal (max C 0 * ∑ k ∈ Finset.range (N + 1), (δ / rk k) ^ p) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun k _ =>
          mul_nonneg (le_max_right _ _) (hnn k)]
    _ ≤ ENNReal.ofReal (max C 0 * (2 ^ p / (2 ^ p - 1)) * δ ^ m) := by
        apply ENNReal.ofReal_le_ofReal
        have hg := box_geom_le hδ hp (N + 1)
        have h1' : ((2:ℝ) ^ (N + 1) * δ) ^ p ≤ δ ^ m := by
          calc ((2:ℝ) ^ (N + 1) * δ) ^ p ≤ (δ ^ a) ^ p :=
                Real.rpow_le_rpow (by positivity) (two_pow_mul_le hδ N h1) hp.le
            _ = δ ^ (a * p) := by rw [← Real.rpow_mul hδ.le]
            _ ≤ δ ^ m := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hmp
        have hq : 0 ≤ (2:ℝ) ^ p / (2 ^ p - 1) := div_nonneg (by positivity) (by linarith)
        calc max C 0 * ∑ k ∈ Finset.range (N + 1), (δ / rk k) ^ p
            ≤ max C 0 * (((2:ℝ) ^ (N + 1) * δ) ^ p * (2 ^ p / (2 ^ p - 1))) :=
              mul_le_mul_of_nonneg_left hg (le_max_right _ _)
          _ ≤ max C 0 * (δ ^ m * (2 ^ p / (2 ^ p - 1))) := by gcongr
          _ = _ := by ring

/-- the real bound of the moment term -/
lemma moment_real_le {δ ζ₁ θ a m E u : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 2 * a = θ * ζ₁)
    (hma : m ≤ a) (ha0 : 0 < a) (hE : 0 ≤ E) (hu : 1 < (2:ℝ) ^ u) :
    (δ ^ (-ζ₁)) ^ (-θ) * E / (2 ^ u - 1) ≤ E / (2 ^ u - 1) * δ ^ m := by
  have e : (δ ^ (-ζ₁)) ^ (-θ) = δ ^ (2 * a) := by
    rw [← Real.rpow_mul hδ.le, ha]; ring_nf
  rw [e]
  have : δ ^ (2 * a) ≤ δ ^ m := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hden : 0 < (2:ℝ) ^ u - 1 := by linarith
  rw [mul_div_assoc, mul_comm]
  exact mul_le_mul_of_nonneg_left this (div_nonneg hE hden.le)

/-- the real bound of the walk term -/
lemma walk_real_le {δ s ζ₁ θ ξ a m u E ρ W : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : 2 * a = θ * ζ₁) (hudef : u = θ * s - (θ * ξ) ^ 2 / 2) (hu : 0 < u) (hma : m ≤ a)
    (ha0 : 0 < a) (hE : 0 ≤ E) (hρ : ρ < 2 * δ ^ (1 - a)) (hW0 : 0 ≤ W) (hW : W ≤ ρ / δ + 4) :
    (δ ^ (-s - ζ₁)) ^ (-θ) * W * (δ ^ (-((θ * ξ) ^ 2 / 2)) * E) ≤ 6 * E * δ ^ m := by
  have hρδ : ρ / δ ≤ 2 * δ ^ (-a) := by
    rw [div_le_iff₀ hδ]
    have : δ ^ (1 - a) = δ ^ (-a) * δ := by
      rw [← Real.rpow_add_one hδ.ne']; ring_nf
    linarith
  have hda : 1 ≤ δ ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hcount : W ≤ 6 * δ ^ (-a) := by linarith
  have e : (δ ^ (-s - ζ₁)) ^ (-θ) * δ ^ (-a) * δ ^ (-((θ * ξ) ^ 2 / 2)) = δ ^ (u + a) := by
    rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ, hudef]
    congr 1; linarith
  have hua : δ ^ (u + a) ≤ δ ^ m := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hT0 : 0 ≤ (δ ^ (-s - ζ₁)) ^ (-θ) := Real.rpow_nonneg (Real.rpow_nonneg hδ.le _) _
  have hd0 : 0 ≤ δ ^ (-((θ * ξ) ^ 2 / 2)) := Real.rpow_nonneg hδ.le _
  calc (δ ^ (-s - ζ₁)) ^ (-θ) * W * (δ ^ (-((θ * ξ) ^ 2 / 2)) * E)
      ≤ (δ ^ (-s - ζ₁)) ^ (-θ) * (6 * δ ^ (-a)) * (δ ^ (-((θ * ξ) ^ 2 / 2)) * E) := by
        gcongr
    _ = 6 * E * ((δ ^ (-s - ζ₁)) ^ (-θ) * δ ^ (-a) * δ ^ (-((θ * ξ) ^ 2 / 2))) := by ring
    _ ≤ 6 * E * δ ^ m := by rw [e]; gcongr

end LQGMetric.DFGPS.L36
