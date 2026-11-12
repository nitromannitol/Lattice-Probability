/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Lemma51Aux3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma51Aux2

/-!
# Lemma 5.1, auxiliary file 3: the cross covariance, point by point

* `gdiff_mass`, `gdiff_nondeg`: `μ_{δ,f} - μ_{δ,g}` has zero mass and nondegenerate segments.
* `edgeSim_sub_hpt_le`: for `z` in the tube `T_δ`, the block point `T^f_i z` is within
  `12 δ² K²` of the idealized point `x + iδ(f(x) + ζ)`, `x = (i + Re z)/M`, `ζ = Im z/(δM)`
  (this includes the overshoot of `Re z` beyond `[0,1]`).
* `cross_hpt`: **(5.6) for a vertical dipole**, by splitting the log kernel into the scales
  `(0,a]`, `(a,b]`, `(b,∞)`: the log part is given by (5.5), the small scales cost `4√π a`,
  the large scales `4√π δ² K |w(x)| / b`.
* `cross_pert`: replacing points by points at distance `≤ d` costs
  `2 √(d² log(b/a)/(2a²)) √B(m,m)` (Cauchy–Schwarz for the band form).
* `riemann_lower`, `sum_abs_incr_le`: the one-point-per-cell Riemann sum of `|w|` and the total
  variation bound `Σ |Δ f| ≤ √(2 E(f))`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.L51

open Blueprint.Draft HeatKernel

/-! ## The graph measures -/

lemma mass_pc {M : ℕ} (hM : 0 < M) (P : ℝ → ℂ) : (GraphCov.pc M P).mass = 1 := by
  unfold SegComb.mass GraphCov.pc
  rw [List.map_map, GraphCov.list_sum_map_range]
  simp only [Function.comp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (M : ℝ) ≠ 0 := by positivity
  field_simp

lemma nondeg_pc_gc (M : ℕ) (δ : ℝ) (h : ℝ → ℝ) :
    ∀ p ∈ GraphCov.pc M (GraphCov.gc δ h), p.2.1 ≠ p.2.2 := by
  intro p hp
  unfold GraphCov.pc at hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  have hM : 0 < M := by have := List.mem_range.1 hi; omega
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  intro heq
  have hre := congrArg Complex.re heq
  simp only [GraphCov.gc, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] at hre
  rw [div_eq_div_iff hM'.ne' hM'.ne'] at hre
  nlinarith

lemma gdiff_mass (n : ℕ) (δ : ℝ) (f g : ℝ → ℝ) : (gdiff (16 ^ n) δ f g).mass = 0 := by
  rw [gdiff, mass_sub, GraphCov.graphComb_eq, GraphCov.graphComb_eq, mass_pc (by positivity),
    mass_pc (by positivity)]
  ring

lemma gdiff_nondeg (n : ℕ) (δ : ℝ) (f g : ℝ → ℝ) : (gdiff (16 ^ n) δ f g).Nondeg := by
  intro p hp _
  rw [gdiff, GraphCov.graphComb_eq, GraphCov.graphComb_eq, SegComb.sub] at hp
  rcases List.mem_append.1 hp with hp | hp
  · exact nondeg_pc_gc _ δ f p hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact nondeg_pc_gc _ δ g q hq

/-! ## Geometry of the block points -/

lemma tube_bounds {δ K : ℝ} {z : ℂ} (hz : z ∈ tube δ K) :
    |z.im| ≤ 2 * δ * K ∧ ∃ s ∈ Icc (0:ℝ) 1, |z.re - s| ≤ 2 * δ * K := by
  obtain ⟨s, hs, hzs⟩ := hz
  refine ⟨?_, s, hs, ?_⟩
  · have := Complex.abs_im_le_norm (z - (s : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    linarith
  · have := Complex.abs_re_le_norm (z - (s : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith

/-- Distance of `u` to its clamp into `[0,1]`. -/
lemma clamp_dist {u s ε : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (hu : |u - s| ≤ ε) :
    max 0 (min u 1) ∈ Icc (0:ℝ) 1 ∧ |u - max 0 (min u 1)| ≤ ε := by
  refine ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩, ?_⟩
  have h := abs_le.1 hu
  rcases le_total u 0 with h0 | h0
  · rw [min_eq_left (h0.trans zero_le_one), max_eq_left h0, sub_zero, abs_of_nonpos h0]
    linarith [hs.1]
  · rcases le_total u 1 with h1 | h1
    · rw [min_eq_left h1, max_eq_right h0, sub_self, abs_zero]
      exact (abs_nonneg _).trans hu
    · rw [min_eq_right h1, max_eq_right zero_le_one, abs_of_nonneg (by linarith)]
      linarith [hs.2]

/-- **The block point `T^f_i z` is `O(δ²)`-close to `x + iδ(f(x) + ζ)`.** -/
lemma edgeSim_sub_hpt_le {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) {K : ℝ} (hfK : ∀ x, |f x| ≤ K)
    {δ : ℝ} (hδ : 0 < δ) {i : ℕ} (hi : i < 16 ^ n) {z : ℂ} (hz : z ∈ tube δ K) :
    ‖edgeSim (16 ^ n) δ f i z - hpt δ (((i : ℝ) + z.re) / (16 : ℝ) ^ n)
        (f (((i : ℝ) + z.re) / (16 : ℝ) ^ n) + z.im / (δ * (16 : ℝ) ^ n))‖ ≤
      12 * δ ^ 2 * K ^ 2 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hfK 0)
  set Mr : ℝ := (16 : ℝ) ^ n with hMr
  have hM : 0 < Mr := by positivity
  obtain ⟨hv, s, hs, hus⟩ := tube_bounds hz
  set u := z.re with hu
  set v := z.im with hv'
  set a₀ := f ((i : ℝ) / Mr) with ha₀
  set a₁ := f (((i : ℝ) + 1) / Mr) with ha₁
  set x := ((i : ℝ) + u) / Mr with hx
  obtain ⟨hub, hud⟩ := clamp_dist hs hus
  set ub := max 0 (min u 1) with hub'
  -- affine formula at the clamped point
  have hy : ((i : ℝ) + ub) / Mr ∈ Icc ((i : ℝ) / Mr) (((i : ℝ) + 1) / Mr) := by
    constructor
    · exact div_le_div_of_nonneg_right (by linarith [hub.1]) hM.le
    · exact div_le_div_of_nonneg_right (by linarith [hub.2]) hM.le
  have hpiece := Subadd.V_piece hf hi hy
  have hMy : Mr * (((i : ℝ) + ub) / Mr) - i = ub := by field_simp; ring
  rw [hMy] at hpiece
  have hΔ : |a₁ - a₀| ≤ 2 * K := by
    have := abs_sub a₁ a₀; linarith [hfK (((i : ℝ) + 1) / Mr), hfK ((i : ℝ) / Mr)]
  have hlip := V_lipL hf hfK (((i : ℝ) + ub) / Mr) x
  have hxy : |((i : ℝ) + ub) / Mr - x| = |u - ub| / Mr := by
    rw [hx, ← sub_div, abs_div, abs_of_pos hM, abs_sub_comm]; congr 1; ring
  rw [hxy] at hlip
  have himb : |a₀ + u * (a₁ - a₀) - f x| ≤ 8 * δ * K ^ 2 := by
    have e : a₀ + u * (a₁ - a₀) - f x = (u - ub) * (a₁ - a₀) +
        (f (((i : ℝ) + ub) / Mr) - f x) := by rw [hpiece]; ring
    rw [e]
    calc |(u - ub) * (a₁ - a₀) + (f (((i : ℝ) + ub) / Mr) - f x)|
        ≤ |(u - ub) * (a₁ - a₀)| + |f (((i : ℝ) + ub) / Mr) - f x| := abs_add_le _ _
      _ ≤ |u - ub| * (2 * K) + 2 * K * Mr * (|u - ub| / Mr) := by
          rw [abs_mul]; gcongr
      _ = 4 * K * |u - ub| := by field_simp; ring
      _ ≤ 4 * K * (2 * δ * K) := by gcongr
      _ = 8 * δ * K ^ 2 := by ring
  -- the difference in coordinates
  have hp0 : pVert (16 ^ n) δ f i = (((i : ℝ) / Mr : ℝ) : ℂ) + ((δ * a₀ : ℝ) : ℂ) * Complex.I := by
    unfold pVert; rw [ha₀, hMr]; push_cast; ring
  have hp1 : pVert (16 ^ n) δ f (i + 1) =
      ((((i : ℝ) + 1) / Mr : ℝ) : ℂ) + ((δ * a₁ : ℝ) : ℂ) * Complex.I := by
    unfold pVert; rw [ha₁, hMr]; push_cast; ring
  have hes : edgeSim (16 ^ n) δ f i z =
      pVert (16 ^ n) δ f i + z * (pVert (16 ^ n) δ f (i + 1) - pVert (16 ^ n) δ f i) := rfl
  have hzuv : z = (u : ℂ) + (v : ℂ) * Complex.I := by rw [hu, hv']; exact (Complex.re_add_im z).symm
  have hdiff : edgeSim (16 ^ n) δ f i z - hpt δ x (f x + v / (δ * Mr)) =
      ((-(v * δ * (a₁ - a₀)) : ℝ) : ℂ) + ((δ * (a₀ + u * (a₁ - a₀) - f x) : ℝ) : ℂ) *
        Complex.I := by
    rw [hes, hp0, hp1, hzuv]
    unfold hpt
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im,
        Complex.sub_im, Complex.mul_im, mul_zero, mul_one, sub_zero, zero_add, add_zero,
        zero_mul, sub_self]
      rw [hx]
      field_simp
      ring
    · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im,
        Complex.sub_im, Complex.mul_im, mul_zero, mul_one, sub_zero, zero_add, add_zero,
        zero_mul, sub_self]
      field_simp
      ring
  rw [hdiff]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
    Complex.mul_im, zero_add]
  rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos hδ]
  have h1 : |v| * δ * |a₁ - a₀| ≤ 2 * δ * K * δ * (2 * K) := by gcongr
  have h2 : δ * |a₀ + u * (a₁ - a₀) - f x| ≤ δ * (8 * δ * K ^ 2) := by gcongr
  nlinarith

/-! ## Scale-range integral bounds -/

lemma abs_setIntegral_Ioc_le {F : ℝ → ℝ} {C a : ℝ} (ha : 0 ≤ a)
    (hC : ∀ t ∈ Ioc (0:ℝ) a, |F t| ≤ C) : |∫ t in Ioc (0:ℝ) a, F t| ≤ C * a := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0:ℝ) a) (f := F)
    (C := C) (by simp) (fun t ht => by rw [Real.norm_eq_abs]; exact hC t ht)
  rw [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ha] at h
  exact h

lemma abs_setIntegral_Ioi_le {F : ℝ → ℝ} {C b : ℝ} (_hC0 : 0 ≤ C) (hb : 0 < b)
    (hC : ∀ t ∈ Ioi b, |F t| ≤ C / t ^ 2) : |∫ t in Ioi b, F t| ≤ C / b := by
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (-2 : ℝ)) (Ioi b) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hb).const_mul C
  have h := norm_integral_le_of_norm_le hint (f := F)
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
      have ht0 : 0 < t := hb.trans ht
      rw [Real.norm_eq_abs, Real.rpow_neg ht0.le, Real.rpow_two, ← div_eq_mul_inv]
      exact hC t ht)
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hb] at h
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one] at h
  rw [div_eq_mul_inv]
  convert h using 1
  ring

/-! ## (5.6) for a vertical dipole -/

/-- **(5.6) for one vertical dipole `x + iδ(f(x)+ζ)`, `x + iδ(g(x)+ζ)`.** -/
lemma cross_hpt {n : ℕ} {f g : ℝ → ℝ} (hf : f ∈ V n) (hg : g ∈ V n) {K : ℝ}
    (hfK : ∀ x, |f x| ≤ K) (hgK : ∀ x, |g x| ≤ K) {δ : ℝ} (hδ : 0 < δ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (x ζ : ℝ) (hζ : |ζ| ≤ K) :
    δ * (2 * π * |f x - g x| - 2 * π * |ζ| -
        2 * ∫ u, min (2 * K * (16 : ℝ) ^ n * δ) (GraphCov.lk (2 * K + K) u)) -
      4 * √π * a - 4 * √π * δ ^ 2 * K * |f x - g x| / b ≤
    bandForm a b ((pt (hpt δ x (f x + ζ))).sub (pt (hpt δ x (g x + ζ))))
      (gdiff (16 ^ n) δ f g) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hfK 0)
  have hb : 0 < b := ha.trans_le hab
  set η := ∫ u, min (2 * K * (16 : ℝ) ^ n * δ) (GraphCov.lk (2 * K + K) u) with hη
  set c := (pt (hpt δ x (f x + ζ))).sub (pt (hpt δ x (g x + ζ))) with hc
  set m := gdiff (16 ^ n) δ f g with hm
  have hcm : c.mass = 0 := by rw [hc, mass_sub, mass_pt, mass_pt]; ring
  have hsplit := logCov_split ha hab c m hcm (gdiff_nondeg n δ f g)
  -- the log part
  have hY1 : |f x + ζ| ≤ 2 * K := (abs_add_le _ _).trans (by linarith [hfK x])
  have hY2 : |g x + ζ| ≤ 2 * K := (abs_add_le _ _).trans (by linarith [hgK x])
  have p1 := abs_pot_sub_le hf hg hfK hgK hδ x (f x + ζ) hY1
  have p2 := abs_pot_sub_le hf hg hfK hgK hδ x (g x + ζ) hY2
  rw [← hη] at p1 p2
  have hlog : c.logCov m = (pt (hpt δ x (f x + ζ))).logCov m - (pt (hpt δ x (g x + ζ))).logCov m := by
    rw [hc, logCov_eq_dsum, dsum_sub_left, ← logCov_eq_dsum, ← logCov_eq_dsum]
  have hlog2 : δ * (2 * π * |f x - g x| - 2 * π * |ζ| - 2 * η) ≤ c.logCov m := by
    rw [hlog]
    have q1 := (abs_le.1 p1).1
    have q2 := (abs_le.1 p2).2
    have e1 : f x + ζ - f x = ζ := by ring
    have e2 : g x + ζ - g x = ζ := by ring
    rw [e1] at q1; rw [e2] at q2
    have htri : 2 * |f x - g x| ≤ |f x + ζ - g x| + |g x + ζ - f x| := by
      have := abs_sub (f x + ζ - g x) (g x + ζ - f x)
      rw [show f x + ζ - g x - (g x + ζ - f x) = 2 * (f x - g x) by ring, abs_mul,
        abs_two] at this
      exact this
    have hA : (pt (hpt δ x (f x + ζ))).logCov m / δ ≥ π * (|f x + ζ - g x| - |ζ|) - η := by
      linarith
    have hB : (pt (hpt δ x (g x + ζ))).logCov m / δ ≤ π * (|ζ| - |g x + ζ - f x|) + η := by
      linarith
    rw [ge_iff_le, le_div_iff₀ hδ] at hA
    rw [div_le_iff₀ hδ] at hB
    have hπ := Real.pi_pos
    have hprod := mul_le_mul_of_nonneg_left htri (le_of_lt (mul_pos hπ hδ))
    nlinarith
  -- small scales
  have hsmall : |∫ t in Ioc (0:ℝ) a, gaussPair t c m / t| ≤ 4 * √π * a := by
    refine abs_setIntegral_Ioc_le ha.le fun t ht => ?_
    have ht0 : 0 < t := ht.1
    rw [hc, gaussPair_eq_dsum, dsum_sub_left, ← gaussPair_eq_dsum, ← gaussPair_eq_dsum,
      abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    have h1 := abs_gaussPair_pt_gdiff_le hf hg ht0 δ x (f x + ζ)
    have h2 := abs_gaussPair_pt_gdiff_le hf hg ht0 δ x (g x + ζ)
    calc |gaussPair t (pt (hpt δ x (f x + ζ))) m - gaussPair t (pt (hpt δ x (g x + ζ))) m|
        ≤ |gaussPair t (pt (hpt δ x (f x + ζ))) m| + |gaussPair t (pt (hpt δ x (g x + ζ))) m| :=
          abs_sub _ _
      _ ≤ 2 * √π * t + 2 * √π * t := add_le_add h1 h2
      _ = 4 * √π * t := by ring
  -- large scales
  have hW : ∀ y, |f y - g y| ≤ 2 * K := fun y =>
    (abs_sub _ _).trans (by linarith [hfK y, hgK y])
  have hlarge : |∫ t in Ioi b, gaussPair t c m / t| ≤
      4 * √π * δ ^ 2 * K * |f x - g x| / b := by
    have hC0 : 0 ≤ 4 * √π * δ ^ 2 * K * |f x - g x| := by positivity
    refine abs_setIntegral_Ioi_le hC0 hb fun t ht => ?_
    have ht0 : 0 < t := hb.trans ht
    have h1 := abs_gaussPair_vdip_le hf hg hW ht0 hδ.le x (f x + ζ) (g x + ζ)
    rw [show f x + ζ - (g x + ζ) = f x - g x by ring] at h1
    rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    calc |gaussPair t c m| ≤ 2 * √π * δ ^ 2 * |f x - g x| * (2 * K) / t := h1
      _ = 4 * √π * δ ^ 2 * K * |f x - g x| / t ^ 2 * t := by field_simp; ring
  rw [hsplit] at hlog2
  have := (abs_le.1 hsmall).2
  have := (abs_le.1 hlarge).2
  linarith

/-- The perturbation bound `√(d² log(b/a) / (2a²))`. -/
def pertB (d a b : ℝ) : ℝ := √(d ^ 2 / (2 * a ^ 2) * Real.log (b / a))

lemma abs_bandForm_dip_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {p q : ℂ} {d : ℝ}
    (hd : ‖p - q‖ ≤ d) (m : SegComb) :
    |bandForm a b ((pt p).sub (pt q)) m| ≤ pertB d a b * √(bandForm a b m m) := by
  refine (abs_bandForm_le ha hab _ _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  unfold pertB
  refine Real.sqrt_le_sqrt ((bandForm_dip_self_le ha hab p q).trans ?_)
  have hlog : 0 ≤ Real.log (b / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  gcongr

/-- **Moving the points of a dipole** by at most `d` each. -/
lemma cross_pert {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {p q P Q : ℂ} {d : ℝ} (hp : ‖p - P‖ ≤ d)
    (hq : ‖q - Q‖ ≤ d) (m : SegComb) :
    bandForm a b ((pt P).sub (pt Q)) m - 2 * pertB d a b * √(bandForm a b m m) ≤
      bandForm a b ((pt p).sub (pt q)) m := by
  have e : bandForm a b ((pt p).sub (pt q)) m = bandForm a b ((pt P).sub (pt Q)) m +
      bandForm a b ((pt p).sub (pt P)) m - bandForm a b ((pt q).sub (pt Q)) m := by
    simp only [bandForm_sub_left ha hab]; ring
  have h1 := abs_bandForm_dip_le ha hab hp m
  have h2 := abs_bandForm_dip_le ha hab hq m
  rw [e]
  have := (abs_le.1 h1).1
  have := (abs_le.1 h2).2
  linarith

/-! ## Riemann sums and total variation -/

lemma sum_abs_incr_le {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ V n) :
    ∑ i ∈ Finset.range (16 ^ n), |f (((i : ℝ) + 1) / 16 ^ n) - f ((i : ℝ) / 16 ^ n)| ≤
      √(2 * energy f) := by
  have hE := Subadd.V_energy hf
  set Δ : ℕ → ℝ := fun i => f (((i : ℝ) + 1) / 16 ^ n) - f ((i : ℝ) / 16 ^ n) with hΔ
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (16 ^ n)) (fun _ => (1 : ℝ))
    (fun i => |Δ i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    sq_abs] at hcs
  have hN : (0:ℝ) < (16:ℝ) ^ n := by positivity
  have hsum : ∑ i ∈ Finset.range (16 ^ n), Δ i ^ 2 = 2 * energy f / (16 : ℝ) ^ n := by
    simp only [hΔ]; rw [hE]; field_simp
  rw [hsum, Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel₀ _ hN.ne'] at hcs
  exact Real.le_sqrt_of_sq_le hcs

/-- **One-point-per-cell Riemann sums of `|w|`**, with the sample parameter `u` possibly
outside `[0,1]` by `ε`. -/
lemma riemann_lower {n : ℕ} {w : ℝ → ℝ} (hw : w ∈ V n) {W₀ : ℝ} (hW : ∀ x, |w x| ≤ W₀)
    {u s ε : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (hu : |u - s| ≤ ε) :
    ∫ x in (0:ℝ)..1, |w x| ≤
      (1 / (16 : ℝ) ^ n) * ∑ i ∈ Finset.range (16 ^ n), |w (((i : ℝ) + u) / 16 ^ n)| +
      (1 / (16 : ℝ) ^ n) * ∑ i ∈ Finset.range (16 ^ n),
        |w (((i : ℝ) + 1) / 16 ^ n) - w ((i : ℝ) / 16 ^ n)| + 2 * W₀ * ε := by
  set Mr : ℝ := (16 : ℝ) ^ n with hMr
  have hM : 0 < Mr := by positivity
  have hMn : 0 < 16 ^ n := by positivity
  obtain ⟨hub, hud⟩ := clamp_dist hs hu
  set ub := max 0 (min u 1) with hub'
  have hwc := Subadd.V_continuous hw
  have hint : IntervalIntegrable (fun x => |w x|) volume 0 1 :=
    (continuous_abs.comp hwc).intervalIntegrable 0 1
  have hpieces := GraphCov.sum_pieces hMn (fun x => |w x|) hint
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hpieces
  rw [← hpieces]
  have hcell : ∀ i ∈ Finset.range (16 ^ n),
      ∫ x in (i : ℝ) / Mr..((i : ℝ) + 1) / Mr, |w x| ≤
        (1 / Mr) * (|w (((i : ℝ) + u) / Mr)| + |w (((i : ℝ) + 1) / Mr) - w ((i : ℝ) / Mr)| +
          2 * W₀ * ε) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hle : (i : ℝ) / Mr ≤ ((i : ℝ) + 1) / Mr := by gcongr; linarith
    have hbound : ∀ x ∈ Icc ((i : ℝ) / Mr) (((i : ℝ) + 1) / Mr),
        |w x| ≤ |w (((i : ℝ) + u) / Mr)| + |w (((i : ℝ) + 1) / Mr) - w ((i : ℝ) / Mr)| +
          2 * W₀ * ε := by
      intro x hx
      have hy : ((i : ℝ) + ub) / Mr ∈ Icc ((i : ℝ) / Mr) (((i : ℝ) + 1) / Mr) := by
        constructor
        · exact div_le_div_of_nonneg_right (by linarith [hub.1]) hM.le
        · exact div_le_div_of_nonneg_right (by linarith [hub.2]) hM.le
      have p1 := Subadd.V_piece hw hi' hx
      have p2 := Subadd.V_piece hw hi' hy
      have hMy : Mr * (((i : ℝ) + ub) / Mr) - i = ub := by field_simp; ring
      rw [hMy] at p2
      have hxr : Mr * x - i ∈ Icc (0:ℝ) 1 := by
        have h1 := hx.1; have h2 := hx.2
        rw [div_le_iff₀ hM] at h1; rw [le_div_iff₀ hM] at h2
        constructor <;> nlinarith
      have hd1 : |w x - w (((i : ℝ) + ub) / Mr)| ≤
          |w (((i : ℝ) + 1) / Mr) - w ((i : ℝ) / Mr)| := by
        rw [p1, p2, show w ((i : ℝ) / Mr) + (Mr * x - i) * (w (((i : ℝ) + 1) / Mr) -
          w ((i : ℝ) / Mr)) - (w ((i : ℝ) / Mr) + ub * (w (((i : ℝ) + 1) / Mr) -
          w ((i : ℝ) / Mr))) = (Mr * x - i - ub) * (w (((i : ℝ) + 1) / Mr) - w ((i : ℝ) / Mr))
          by ring, abs_mul]
        have : |Mr * x - i - ub| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [hxr.1, hxr.2, hub.1, hub.2]
        calc |Mr * x - ↑i - ub| * |w ((↑i + 1) / Mr) - w (↑i / Mr)|
            ≤ 1 * |w ((↑i + 1) / Mr) - w (↑i / Mr)| := by gcongr
          _ = _ := one_mul _
      have hd2 : |w (((i : ℝ) + ub) / Mr) - w (((i : ℝ) + u) / Mr)| ≤ 2 * W₀ * ε := by
        have := V_lipL hw hW (((i : ℝ) + ub) / Mr) (((i : ℝ) + u) / Mr)
        have e : |((i : ℝ) + ub) / Mr - ((i : ℝ) + u) / Mr| = |u - ub| / Mr := by
          rw [← sub_div, abs_div, abs_of_pos hM, abs_sub_comm]; congr 1; ring
        rw [e] at this
        have hW0 : 0 ≤ W₀ := (abs_nonneg _).trans (hW 0)
        calc _ ≤ 2 * W₀ * Mr * (|u - ub| / Mr) := this
          _ = 2 * W₀ * |u - ub| := by field_simp
          _ ≤ 2 * W₀ * ε := by gcongr
      have := abs_sub_abs_le_abs_sub (w x) (w (((i : ℝ) + ub) / Mr))
      have := abs_sub_abs_le_abs_sub (w (((i : ℝ) + ub) / Mr)) (w (((i : ℝ) + u) / Mr))
      linarith
    calc ∫ x in (i : ℝ) / Mr..((i : ℝ) + 1) / Mr, |w x|
        ≤ ∫ _x in (i : ℝ) / Mr..((i : ℝ) + 1) / Mr, (|w (((i : ℝ) + u) / Mr)| +
            |w (((i : ℝ) + 1) / Mr) - w ((i : ℝ) / Mr)| + 2 * W₀ * ε) :=
          intervalIntegral.integral_mono_on hle
            ((continuous_abs.comp hwc).intervalIntegrable _ _) intervalIntegrable_const hbound
      _ = (1 / Mr) * (|w (((i : ℝ) + u) / Mr)| +
            |w (((i : ℝ) + 1) / Mr) - w ((i : ℝ) / Mr)| + 2 * W₀ * ε) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          congr 1; field_simp; ring
  refine (Finset.sum_le_sum hcell).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp
  ring

end LQGDimension.L51
