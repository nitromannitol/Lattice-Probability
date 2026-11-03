/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentPos2 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.Kahane2Const
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Positive moments of discrete GMC sums over dyadic grids: setting and scaling step (P2-KAHANE3)

Abstract setting for the positive-moment bound of Gaussian multiplicative chaos (Berestycki–Powell,
*Gaussian free field and Liouville quantum gravity*, arXiv:2404.16642, Theorem 3.23
`T:finiteposmoments`, `GMCproperties.tex` l. 1270–1430; Rhodes–Vargas arXiv:1305.6221, proof of
Theorem 2.11), discretized so that only the finite-dimensional Kahane inequality is needed.

* `DGMC.cpt j i` : the centre of the level-`j` dyadic cell `i = (a, b)` of `[0,1]²`;
  `DGMC.grid j` : the `4^j` cells of `[0,1]²`; `DGMC.sh m k u a` : the cell `a` of level `k`
  placed in the level-`m` square `u` (a cell of level `m + k`).
* `DGMC.gM Z P j S ω = ∑_{i ∈ S} 4^{-j} e^{Z(cpt j i) − Var Z(cpt j i)/2}` : the discrete chaos
  mass of the cells `S`.
* `DGMC.LogCorr Z P β c` : the family of centred Gaussian processes `Z n` (`n` the scale index,
  `ε = 2^{-n}`) is `β`-log-correlated on `[0,1]²` up to `c`:
  `|Cov(Z n x, Z n y) + β log max(2^{-n}, ‖x − y‖)| ≤ c` (BP l. 1205–1210, "encadr-cov").
* `DGMC.integral_gM_sh_rpow_le` (BP Lemma `L:ondiagbase`, l. 1310–1322, via the scaling relation
  (scalingeps) l. 1239–1250): for `q ≥ 1`,
  `E gM_{m+l}(S_u)^q ≤ 4^{-mq} e^{q(q−1)(β m log 2 + 2c)/2} E gM_l([0,1]²)^q`.
  BP derive this from an exactly scale-invariant field; here it is Kahane's inequality with an
  additive constant (`Kahane.kahane_rpow_le_add_const`) applied directly to the two-sided
  log-correlation bound, which gives the same estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

/-- the closed unit square `[0,1]²` -/
def unitSq : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1}

/-- centre of the level-`j` dyadic cell `i` -/
def cpt (j : ℕ) (i : ℕ × ℕ) : ℂ := ⟨((i.1 : ℝ) + 1 / 2) / 2 ^ j, ((i.2 : ℝ) + 1 / 2) / 2 ^ j⟩

/-- the level-`j` dyadic cells of `[0,1]²` -/
def grid (j : ℕ) : Finset (ℕ × ℕ) := range (2 ^ j) ×ˢ range (2 ^ j)

/-- the level-`k` cell `a` placed inside the level-`m` square `u` -/
def sh (k : ℕ) (u a : ℕ × ℕ) : ℕ × ℕ := (u.1 * 2 ^ k + a.1, u.2 * 2 ^ k + a.2)

/-- the level-`(m + k)` cells inside the level-`m` square `u` -/
def sub (k : ℕ) (u : ℕ × ℕ) : Finset (ℕ × ℕ) := (grid k).image (sh k u)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- the discrete chaos mass of the cells `S` of level `j` -/
def gM (Z : ℂ → Ω → ℝ) (P : Measure Ω) (j : ℕ) (S : Finset (ℕ × ℕ)) (ω : Ω) : ℝ :=
  ∑ i ∈ S, (4 : ℝ)⁻¹ ^ j * Real.exp (Z (cpt j i) ω - Var[Z (cpt j i); P] / 2)

/-- `β`-log-correlated family of centred Gaussian processes on `[0,1]²`, up to `c` -/
structure LogCorr (Z : ℕ → ℂ → Ω → ℝ) (P : Measure Ω) (β c : ℝ) : Prop where
  gauss : ∀ n, IsGaussianProcess (Z n) P
  meas : ∀ n x, Measurable (Z n x)
  mean : ∀ n x, ∫ ω, Z n x ω ∂P = 0
  cov : ∀ n x y, x ∈ unitSq → y ∈ unitSq →
    |cov[Z n x, Z n y; P] + β * Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖)| ≤ c

lemma mem_grid {j : ℕ} {i : ℕ × ℕ} : i ∈ grid j ↔ i.1 < 2 ^ j ∧ i.2 < 2 ^ j := by
  simp [grid, mem_product]

lemma cpt_mem_unitSq {j : ℕ} {i : ℕ × ℕ} (hi : i ∈ grid j) : cpt j i ∈ unitSq := by
  rw [mem_grid] at hi
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have a1 : (i.1 : ℝ) + 1 / 2 ≤ 2 ^ j := by
    have : (i.1 : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast hi.1
    linarith
  have a2 : (i.2 : ℝ) + 1 / 2 ≤ 2 ^ j := by
    have : (i.2 : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast hi.2
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [cpt]
  · positivity
  · rw [div_le_one h2]; exact a1
  · positivity
  · rw [div_le_one h2]; exact a2

lemma sh_injective (k : ℕ) (u : ℕ × ℕ) : Function.Injective (sh k u) := by
  intro a b h
  simp only [sh, Prod.mk.injEq, add_right_inj] at h
  exact Prod.ext h.1 h.2

lemma sh_mem_grid {m k : ℕ} {u a : ℕ × ℕ} (hu : u ∈ grid m) (ha : a ∈ grid k) :
    sh k u a ∈ grid (m + k) := by
  rw [mem_grid] at hu ha ⊢
  simp only [sh, pow_add]
  constructor
  · nlinarith [hu.1, ha.1]
  · nlinarith [hu.2, ha.2]

lemma cpt_sh (m k : ℕ) (u a : ℕ × ℕ) :
    cpt (m + k) (sh k u a) = ((2 : ℂ) ^ m)⁻¹ * (⟨u.1, u.2⟩ + cpt k a) := by
  apply Complex.ext <;>
  · simp only [cpt, sh, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.inv_re, Complex.inv_im, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have h1 : ((2 : ℂ) ^ m).re = 2 ^ m := by norm_cast
    have h2 : ((2 : ℂ) ^ m).im = 0 := by norm_cast
    rw [h1, h2, Complex.normSq_apply, h1, h2]
    field_simp
    ring

lemma norm_cpt_sh_sub (m k : ℕ) (u a b : ℕ × ℕ) :
    ‖cpt (m + k) (sh k u a) - cpt (m + k) (sh k u b)‖ = (2 : ℝ)⁻¹ ^ m * ‖cpt k a - cpt k b‖ := by
  rw [cpt_sh, cpt_sh, ← mul_sub, add_sub_add_left_eq_sub, norm_mul, norm_inv, norm_pow,
    Complex.norm_two, inv_pow]

/-- `log max(2^{-(m+l)}, 2^{-m} d) = −m log 2 + log max(2^{-l}, d)` -/
lemma log_max_scale (m l : ℕ) (d : ℝ) :
    Real.log (max ((2 : ℝ)⁻¹ ^ (m + l)) ((2 : ℝ)⁻¹ ^ m * d)) =
      -(m * Real.log 2) + Real.log (max ((2 : ℝ)⁻¹ ^ l) d) := by
  rw [pow_add, ← mul_max_of_nonneg _ _ (by positivity), Real.log_mul (by positivity)
    (lt_max_of_lt_left (by positivity)).ne', Real.log_pow, Real.log_inv]
  ring

/-- the vector `(X (t i))_i` of a Gaussian process along a finite index type is Gaussian
(as `SupTail.hasGaussianLaw_finVec`) -/
lemma hasGaussianLaw_fintype {T ι : Type*} [Fintype ι] {P : Measure Ω} {X : T → Ω → ℝ}
    (hX : IsGaussianProcess X P) (t : ι → T) : HasGaussianLaw (fun ω i => X (t i) ω) P := by
  have hY : IsGaussianProcess (fun i : ι => X (t i)) P := hX.comp_right t
  let L : (↥(Finset.univ : Finset ι) → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj ⟨i, Finset.mem_univ i⟩
  exact (hY.hasGaussianLaw Finset.univ).map L

variable {P : Measure Ω} {Z : ℕ → ℂ → Ω → ℝ} {β c : ℝ}

lemma LogCorr.c_nonneg (hZ : LogCorr Z P β c) : 0 ≤ c :=
  (abs_nonneg _).trans (hZ.cov 0 0 0 (by simp [unitSq]) (by simp [unitSq]))

/-- `gM` over the sub-square `u` of level `m` as a sum over the level-`k` grid -/
lemma gM_sub (Z : ℂ → Ω → ℝ) (m k : ℕ) (u : ℕ × ℕ) (ω : Ω) :
    gM Z P (m + k) (sub k u) ω = (4 : ℝ)⁻¹ ^ m * ∑ a : ↥(grid k), (4 : ℝ)⁻¹ ^ k *
      Real.exp (Z (cpt (m + k) (sh k u a)) ω - Var[Z (cpt (m + k) (sh k u a)); P] / 2) := by
  rw [gM, sub, sum_image fun a _ b _ h => sh_injective k u h, Finset.mul_sum,
    ← Finset.sum_coe_sort (grid k)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pow_add, mul_assoc]

lemma gM_grid (Z : ℂ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    gM Z P k (grid k) ω = ∑ a : ↥(grid k), (4 : ℝ)⁻¹ ^ k *
      Real.exp (Z (cpt k a) ω - Var[Z (cpt k a); P] / 2) := by
  rw [gM, ← Finset.sum_coe_sort (grid k)]

lemma grid_nonempty (k : ℕ) : Nonempty ↥(grid k) :=
  ⟨⟨(0, 0), mem_grid.2 ⟨by positivity, by positivity⟩⟩⟩

/-- same-square covariance comparison across scales (from the two-sided log bound) -/
lemma LogCorr.cov_sh_le (hZ : LogCorr Z P β c) (m l k : ℕ) {u a b : ℕ × ℕ} (hu : u ∈ grid m)
    (ha : a ∈ grid k) (hb : b ∈ grid k) :
    cov[Z (m + l) (cpt (m + k) (sh k u a)), Z (m + l) (cpt (m + k) (sh k u b)); P] ≤
      cov[Z l (cpt k a), Z l (cpt k b); P] + (β * (m * Real.log 2) + 2 * c) := by
  have h1 := hZ.cov (m + l) _ _ (cpt_mem_unitSq (sh_mem_grid hu ha))
    (cpt_mem_unitSq (sh_mem_grid hu hb))
  have h2 := hZ.cov l _ _ (cpt_mem_unitSq ha) (cpt_mem_unitSq hb)
  rw [norm_cpt_sh_sub, log_max_scale m l] at h1
  rw [abs_le] at h1 h2
  nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- the parity class (checkerboard group) of a level-`m` square -/
def par (u : ℕ × ℕ) : Fin 2 × Fin 2 := (⟨u.1 % 2, Nat.mod_lt _ two_pos⟩, ⟨u.2 % 2, Nat.mod_lt _ two_pos⟩)

lemma abs_cpt_re_sub_lt {k : ℕ} {a b : ℕ × ℕ} (ha : a ∈ grid k) (hb : b ∈ grid k) :
    |(cpt k a).re - (cpt k b).re| < 1 ∧ |(cpt k a).im - (cpt k b).im| < 1 := by
  have h1 := cpt_mem_unitSq ha
  have h2 := cpt_mem_unitSq hb
  rw [mem_grid] at ha hb
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have l1 : ∀ i : ℕ, i < 2 ^ k → 0 < ((i : ℝ) + 1 / 2) / 2 ^ k ∧ ((i : ℝ) + 1 / 2) / 2 ^ k < 1 :=
    fun i hi => ⟨by positivity, by
      rw [div_lt_one h2k]
      have : (i : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast hi
      linarith⟩
  simp only [cpt]
  obtain ⟨a1, a2⟩ := l1 a.1 ha.1
  obtain ⟨b1, b2⟩ := l1 b.1 hb.1
  obtain ⟨c1, c2⟩ := l1 a.2 ha.2
  obtain ⟨d1, d2⟩ := l1 b.2 hb.2
  exact ⟨abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩

lemma two_le_of_par {x y : ℕ} (hxy : x ≠ y) (hp : x % 2 = y % 2) : 2 ≤ |(x : ℝ) - y| := by
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · have : x + 2 ≤ y := by omega
    rw [abs_sub_comm, abs_of_nonneg (by
      have : (x : ℝ) ≤ y := by exact_mod_cast h.le
      linarith)]
    have : (x : ℝ) + 2 ≤ y := by exact_mod_cast this
    linarith
  · have : y + 2 ≤ x := by omega
    rw [abs_of_nonneg (by
      have : (y : ℝ) ≤ x := by exact_mod_cast h.le
      linarith)]
    have : (y : ℝ) + 2 ≤ x := by exact_mod_cast this
    linarith

/-- **separation of a checkerboard group**: points of two distinct level-`m` squares of the
same parity class are at distance at least `2^{-m}` (BP l. 1283–1285) -/
lemma le_norm_cpt_sh_sub {m k : ℕ} {u v a b : ℕ × ℕ} (huv : u ≠ v) (hp : par u = par v)
    (ha : a ∈ grid k) (hb : b ∈ grid k) :
    (2 : ℝ)⁻¹ ^ m ≤ ‖cpt (m + k) (sh k u a) - cpt (m + k) (sh k v b)‖ := by
  have e : cpt (m + k) (sh k u a) - cpt (m + k) (sh k v b) =
      ((2 : ℂ) ^ m)⁻¹ * ((⟨(u.1 : ℝ) - v.1, (u.2 : ℝ) - v.2⟩ : ℂ) + (cpt k a - cpt k b)) := by
    rw [cpt_sh, cpt_sh, ← mul_sub]
    congr 1
    apply Complex.ext <;> simp <;> ring
  rw [e, norm_mul, norm_inv, norm_pow, Complex.norm_two, inv_pow]
  refine le_mul_of_one_le_right (by positivity) ?_
  obtain ⟨hre, him⟩ := abs_cpt_re_sub_lt ha hb
  simp only [par, Prod.mk.injEq, Fin.mk.injEq] at hp
  by_cases h1 : u.1 = v.1
  · have h2 : u.2 ≠ v.2 := fun h => huv (Prod.ext h1 h)
    have := two_le_of_par h2 hp.2
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.add_im, Complex.sub_im]
    have := abs_sub_abs_le_abs_sub ((u.2 : ℝ) - v.2) (-((cpt k a).im - (cpt k b).im))
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  · have := two_le_of_par h1 hp.1
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    simp only [Complex.add_re, Complex.sub_re]
    have := abs_sub_abs_le_abs_sub ((u.1 : ℝ) - v.1) (-((cpt k a).re - (cpt k b).re))
    rw [abs_neg, sub_neg_eq_add] at this
    linarith

/-- **off-diagonal covariance bound** (BP Lemma `L:offdiagbase`, l. 1335–1338): across distinct
squares of one checkerboard group, `Cov ≤ β m log 2 + c` -/
lemma cov_sh_le_of_par (hZ : LogCorr Z P β c) (hβ : 0 ≤ β) {m k n : ℕ} {u v a b : ℕ × ℕ}
    (hu : u ∈ grid m) (hv : v ∈ grid m) (huv : u ≠ v) (hp : par u = par v)
    (ha : a ∈ grid k) (hb : b ∈ grid k) :
    cov[Z n (cpt (m + k) (sh k u a)), Z n (cpt (m + k) (sh k v b)); P] ≤
      β * (m * Real.log 2) + c := by
  have h := hZ.cov n _ _ (cpt_mem_unitSq (sh_mem_grid hu ha)) (cpt_mem_unitSq (sh_mem_grid hv hb))
  have hd := le_norm_cpt_sh_sub (m := m) huv hp ha hb
  have hl : Real.log ((2 : ℝ)⁻¹ ^ m) ≤
      Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖cpt (m + k) (sh k u a) - cpt (m + k) (sh k v b)‖) :=
    Real.log_le_log (by positivity) (hd.trans (le_max_right _ _))
  rw [Real.log_pow, Real.log_inv] at hl
  rw [abs_le] at h
  nlinarith [h.1, h.2]

end DGMC

end LQGMetric
