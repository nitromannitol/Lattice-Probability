/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112G1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112A

/-!
# D112 packet G1a: a chain of at most five squares to a full square (`CONFChainFull 4`)

Decision D112 (`decisions/DEC-112.md` §2–§4), grid claim used for CONF (3.21) (Gwynne–Miller,
*Confluence of geodesics in LQG*, arXiv:1905.00381, `confluence-final.tex` C:1392–1396).

Let `u ∈ 𝔸_{3r,4r}(z)` lie in the square `k₀` of side `ε = δr`, `v = u − z`, `R = |v|`. Pick the
axis direction `d` (`d ∈ {±1, ±i}`) with `⟨d, v⟩ ≥ 0` and `2⟨d, v⟩² ≥ R²`. The squares
`k₀ + j d` contain `u + jε d`, and `|v + t d|² = R² + 2t⟨d, v⟩ + t²`, so (`0 ≤ t ≤ 4ε`, `8ε < r`):

* if `R < 3r + 2ε`: `R + t/2 ≤ |v + t d| ≤ R + t`; after 4 steps the point is in `confMidAnn`;
* if `R > 4r − 2ε`: `R − t ≤ |v − t d| ≤ R − t/2`; after 4 steps the point is in `confMidAnn`;
* otherwise `k₀` itself is full (`m = 0`).

All intermediate points stay in `𝔸_{3r,4r}(z)`. **`confChainFull : CONFChainFull 4`**.

Own elementary proof (DEC-112 §4, packet G1a; DEVIATIONS DV-D112).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric.CONF

open Blueprint

theorem conf_norm_sq_shift (u z : ℂ) (t a b : ℝ) :
    ‖(⟨u.re + t * a, u.im + t * b⟩ : ℂ) - z‖ ^ 2 =
      (u.re - z.re + t * a) ^ 2 + (u.im - z.im + t * b) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- a straight chain `k₀ + j d`, `j ≤ m`, through the points `u + jε d` -/
theorem conf_straight_chain {ε r : ℝ} {z u : ℂ} {k₀ dd : ℤ × ℤ} (hdd : dd.1 ^ 2 + dd.2 ^ 2 = 1)
    (hu : u ∈ confSq ε z k₀) {m K : ℕ} (hmK : m ≤ K)
    (hA : ∀ j ≤ m, (⟨u.re + (j : ℝ) * ε * dd.1, u.im + (j : ℝ) * ε * dd.2⟩ : ℂ) ∈
      (annulus z (3 * r) (4 * r) : Set ℂ))
    (hM : (⟨u.re + (m : ℝ) * ε * dd.1, u.im + (m : ℝ) * ε * dd.2⟩ : ℂ) ∈ confMidAnn z r ε) :
    SqChain ε z r K k₀ (confFull ε z r) := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  have hmem : ∀ j : ℕ, (⟨u.re + (j : ℝ) * ε * dd.1, u.im + (j : ℝ) * ε * dd.2⟩ : ℂ) ∈
      confSq ε z (k₀.1 + j * dd.1, k₀.2 + j * dd.2) := by
    intro j
    refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith
  refine ⟨m, fun j => (k₀.1 + j * dd.1, k₀.2 + j * dd.2), hmK, by simp, fun j hj =>
    ⟨_, hmem j, hA j hj⟩, fun j _ => ?_, ⟨_, hmem m, hM⟩⟩
  unfold SqAdj
  push_cast
  ring_nf
  ring_nf at hdd
  linarith

/-- the axis direction closest to `(x, y)` -/
theorem conf_exists_dir (x y : ℝ) : ∃ dd : ℤ × ℤ, dd.1 ^ 2 + dd.2 ^ 2 = 1 ∧
    0 ≤ (dd.1 : ℝ) * x + dd.2 * y ∧ x ^ 2 + y ^ 2 ≤ 2 * ((dd.1 : ℝ) * x + dd.2 * y) ^ 2 := by
  rcases le_total |y| |x| with h | h
  · rcases le_total 0 x with hx | hx
    · refine ⟨(1, 0), by norm_num, ?_, ?_⟩ <;> push_cast <;>
        nlinarith [abs_nonneg x, sq_abs x, sq_abs y, abs_nonneg y]
    · refine ⟨(-1, 0), by norm_num, ?_, ?_⟩ <;> push_cast <;>
        nlinarith [abs_nonneg x, sq_abs x, sq_abs y, abs_nonneg y]
  · rcases le_total 0 y with hy | hy
    · refine ⟨(0, 1), by norm_num, ?_, ?_⟩ <;> push_cast <;>
        nlinarith [abs_nonneg x, sq_abs x, sq_abs y, abs_nonneg y]
    · refine ⟨(0, -1), by norm_num, ?_, ?_⟩ <;> push_cast <;>
        nlinarith [abs_nonneg x, sq_abs x, sq_abs y, abs_nonneg y]

/-- the modulus moves outwards by between `t/2` and `t` -/
theorem conf_dir_out {a b x y t R N : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (hR : R ^ 2 = x ^ 2 + y ^ 2)
    (hR0 : 0 ≤ R) (hN0 : 0 ≤ N) (hN : N ^ 2 = (x + t * a) ^ 2 + (y + t * b) ^ 2) (ht : 0 ≤ t)
    (hs0 : 0 ≤ a * x + b * y) (hs : R ^ 2 ≤ 2 * (a * x + b * y) ^ 2) :
    R + t / 2 ≤ N ∧ N ≤ R + t := by
  set s := a * x + b * y
  have hN' : N ^ 2 = R ^ 2 + 2 * t * s + t ^ 2 := by rw [hN, hR]; simp only [s]; linear_combination t ^ 2 * hab
  have hsR : s ^ 2 ≤ R ^ 2 := by
    have : s ^ 2 + (a * y - b * x) ^ 2 = R ^ 2 := by rw [hR]; simp only [s]; linear_combination (x ^ 2 + y ^ 2) * hab
    nlinarith [sq_nonneg (a * y - b * x)]
  have hsR' : s ≤ R := by nlinarith
  have h2s : R ≤ 2 * s := by nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- the modulus moves inwards by between `t/2` and `t` (for `6t ≤ R`) -/
theorem conf_dir_in {a b x y t R N : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (hR : R ^ 2 = x ^ 2 + y ^ 2)
    (hR0 : 0 ≤ R) (hN0 : 0 ≤ N) (hN : N ^ 2 = (x + t * a) ^ 2 + (y + t * b) ^ 2) (ht : 0 ≤ t)
    (htR : 6 * t ≤ R) (hs0 : a * x + b * y ≤ 0) (hs : R ^ 2 ≤ 2 * (a * x + b * y) ^ 2) :
    R - t ≤ N ∧ N ≤ R - t / 2 := by
  set s := a * x + b * y
  have hN' : N ^ 2 = R ^ 2 + 2 * t * s + t ^ 2 := by rw [hN, hR]; simp only [s]; linear_combination t ^ 2 * hab
  have hsR : s ^ 2 ≤ R ^ 2 := by
    have : s ^ 2 + (a * y - b * x) ^ 2 = R ^ 2 := by rw [hR]; simp only [s]; linear_combination (x ^ 2 + y ^ 2) * hab
    nlinarith [sq_nonneg (a * y - b * x)]
  have hsR' : -R ≤ s := by nlinarith
  have h2s : 6 * R ≤ -10 * s := by nlinarith
  have hup : N ^ 2 ≤ (R - t / 2) ^ 2 := by nlinarith
  have hlo : (R - t) ^ 2 ≤ N ^ 2 := by nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- **D112 packet G1a**: from every square containing a point of `𝔸_{3r,4r}(z)` there is a chain
of at most five edge-adjacent squares of `𝒮^z_{δr}(𝔸_{3r,4r}(z))` to a full square -/
theorem confChainFull : CONFChainFull 4 := by
  intro δ r hδ hδ8 hr z u hu k₀ hk₀
  set ε := δ * r with hεdef
  have hε : 0 < ε := by positivity
  have h8 : 8 * ε < r := by rw [hεdef]; nlinarith
  have hu' : 3 * r < ‖u - z‖ ∧ ‖u - z‖ < 4 * r := hu
  set R := ‖u - z‖ with hRdef
  set x := u.re - z.re
  set y := u.im - z.im
  have hR : R ^ 2 = x ^ 2 + y ^ 2 := by
    rw [hRdef, Complex.sq_norm, Complex.normSq_apply]; simp only [Complex.sub_re, Complex.sub_im, x, y]; ring
  have hR0 : 0 ≤ R := norm_nonneg _
  have hN : ∀ (a b : ℤ) (j : ℕ), ‖(⟨u.re + (j : ℝ) * ε * a, u.im + (j : ℝ) * ε * b⟩ : ℂ) - z‖ ^ 2 =
      (x + ((j : ℝ) * ε) * a) ^ 2 + (y + ((j : ℝ) * ε) * b) ^ 2 := fun a b j =>
    conf_norm_sq_shift u z _ _ _
  obtain ⟨dd, hdd, hs0, hs⟩ := conf_exists_dir x y
  have hddR : ((dd.1 : ℝ)) ^ 2 + (dd.2 : ℝ) ^ 2 = 1 := by exact_mod_cast hdd
  by_cases hlo : R < 3 * r + 2 * ε
  · refine conf_straight_chain hdd hk₀ le_rfl (fun j hj => ?_) ?_
    · have hj' : (j : ℝ) ≤ 4 := by exact_mod_cast hj
      obtain ⟨b1, b2⟩ := conf_dir_out hddR hR hR0 (norm_nonneg _) (hN dd.1 dd.2 j)
        (by positivity) hs0 (by rw [hR]; exact hs)
      constructor <;> nlinarith
    · obtain ⟨b1, b2⟩ := conf_dir_out hddR hR hR0 (norm_nonneg _) (hN dd.1 dd.2 4)
        (by positivity) hs0 (by rw [hR]; exact hs)
      push_cast at b1 b2
      constructor <;> push_cast <;> linarith
  by_cases hhi : 4 * r - 2 * ε < R
  · have hdd' : (-dd.1) ^ 2 + (-dd.2) ^ 2 = 1 := by rw [neg_sq, neg_sq]; exact hdd
    have hddR' : (((-dd.1 : ℤ) : ℝ)) ^ 2 + ((-dd.2 : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast hdd'
    have hs0' : ((-dd.1 : ℤ) : ℝ) * x + ((-dd.2 : ℤ) : ℝ) * y ≤ 0 := by push_cast; linarith
    have hs' : R ^ 2 ≤ 2 * (((-dd.1 : ℤ) : ℝ) * x + ((-dd.2 : ℤ) : ℝ) * y) ^ 2 := by
      push_cast; nlinarith
    refine conf_straight_chain (dd := (-dd.1, -dd.2)) hdd' hk₀ le_rfl (fun j hj => ?_) ?_
    · have hj' : (j : ℝ) ≤ 4 := by exact_mod_cast hj
      obtain ⟨b1, b2⟩ := conf_dir_in hddR' hR hR0 (norm_nonneg _) (hN (-dd.1) (-dd.2) j)
        (by positivity) (by nlinarith) hs0' hs'
      constructor <;> nlinarith
    · obtain ⟨b1, b2⟩ := conf_dir_in hddR' hR hR0 (norm_nonneg _) (hN (-dd.1) (-dd.2) 4)
        (by positivity) (by push_cast; nlinarith) hs0' hs'
      push_cast at b1 b2
      constructor <;> push_cast <;> linarith
  rw [not_lt] at hlo hhi
  exact ⟨0, fun _ => k₀, by norm_num, rfl, fun _ _ => ⟨u, hk₀, hu⟩,
    fun i hi => absurd hi (Nat.not_lt_zero _), ⟨u, hk₀, hlo, hhi⟩⟩

end LQGMetric.CONF
