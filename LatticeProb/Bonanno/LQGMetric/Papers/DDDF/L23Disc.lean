/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L23Disc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic

/-!
# The discretized crossing length `L^{(n)}_{1,1}(D_k)` (DDDF Lemma 23, deterministic part)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1043–1050 (proof of `Lem:VarApriori`):
`L^{(n)}_{1,1}(D_k)` is the left–right distance of `[0,1]²` for `e^{ξ φ^k_{0,n}} ds`, where
`φ^k_{0,n}` is piecewise constant on the dyadic blocks of size `2^{-k}`, equal to `φ_{0,n}` at the
block centre. Its logarithm is a `ξ`-Lipschitz function of the `4^k` centre values for the sup
metric, and it converges to `log L^{(n)}_{1,1}` as `k → ∞`.

* `grid k`: the `4^k` dyadic block centres `((i + 1/2) 2^{-k}, (j + 1/2) 2^{-k})`;
  `snap k x`: a nearest centre (for `x ∈ [0,1]²`, at distance `≤ 2^{-k}`; on block boundaries
  DDDF's piecewise-constant field is ambiguous, any nearest centre is a valid choice);
* `logLen ξ f = log L([0,1]², f)`; `discLogLen ξ k y = log L([0,1]², y ∘ snap k)` for
  `y : grid k → ℝ`;
* `abs_logLen_sub_le`: `|log L(f) − log L(g)| ≤ |ξ| sup_{[0,1]²} |f − g|` (from DDDF l. 482–485,
  `crossLenIn_le_of_abs_sub_le`);
* `lipschitzWith_discLogLen`: `discLogLen ξ k` is `|ξ|`-Lipschitz (DDDF l. 1050);
* `tendsto_discLogLen`: for continuous `f`, `log L(f ∘ snap k) → log L(f)` (DDDF l. 1046–1047,
  here by uniform continuity of `f` on `[0,1]²` instead of DDDF's gradient bound).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF
namespace L23

/-- the unit square `[0,1]²` -/
abbrev sq01 : Set ℂ := (rectAB 1 1).toSet

lemma mem_sq01 {x : ℂ} : x ∈ sq01 ↔ x.re ∈ Icc (0 : ℝ) 1 ∧ x.im ∈ Icc (0 : ℝ) 1 := by
  simp [sq01, MarkedRect.toSet, rectAB, Complex.mem_reProdIm]

/-- the centre of the dyadic block `(i, j)` of size `2^{-k}` -/
def gridPt (k : ℕ) (p : ℕ × ℕ) : ℂ := ⟨((p.1 : ℝ) + 1 / 2) / 2 ^ k, ((p.2 : ℝ) + 1 / 2) / 2 ^ k⟩

/-- the `4^k` dyadic block centres of `[0,1]²` -/
def grid (k : ℕ) : Finset ℂ := (Finset.range (2 ^ k) ×ˢ Finset.range (2 ^ k)).image (gridPt k)

lemma grid_nonempty (k : ℕ) : (grid k).Nonempty :=
  ⟨gridPt k (0, 0), Finset.mem_image_of_mem _ (by simp)⟩

lemma coord_mem {k i : ℕ} (hi : i < 2 ^ k) : ((i : ℝ) + 1 / 2) / 2 ^ k ∈ Icc (0 : ℝ) 1 := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hi' : (i : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast hi
  constructor
  · positivity
  · rw [div_le_one h2]; linarith

lemma grid_subset {k : ℕ} {c : ℂ} (hc : c ∈ grid k) : c ∈ sq01 := by
  obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.1 hc
  simp only [Finset.mem_product, Finset.mem_range] at hp
  exact mem_sq01.2 ⟨coord_mem hp.1, coord_mem hp.2⟩

/-- one coordinate: some centre is within `2^{-k-1}` -/
lemma exists_coord_near (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ i : ℕ, i < 2 ^ k ∧ |t - ((i : ℝ) + 1 / 2) / 2 ^ k| ≤ 1 / 2 / 2 ^ k := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  set i := min (⌊t * 2 ^ k⌋₊) (2 ^ k - 1) with hi
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  refine ⟨i, lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) one_pos), ?_⟩
  have e : t - ((i : ℝ) + 1 / 2) / 2 ^ k = (t * 2 ^ k - ((i : ℝ) + 1 / 2)) / 2 ^ k := by
    field_simp
  rw [e, abs_div, abs_of_pos h2]
  refine div_le_div_of_nonneg_right ?_ h2.le
  rw [abs_le]
  have hfl := Nat.floor_le (mul_nonneg ht.1 h2.le)
  have hfl2 := Nat.lt_floor_add_one (t * 2 ^ k)
  have htk : t * 2 ^ k ≤ 2 ^ k := by nlinarith [ht.2]
  rcases le_total (⌊t * 2 ^ k⌋₊) (2 ^ k - 1) with h | h
  · rw [hi, min_eq_left h]
    constructor <;> linarith
  · rw [hi, min_eq_right h]
    have : ((2 ^ k - 1 : ℕ) : ℝ) = 2 ^ k - 1 := by
      rw [Nat.cast_sub h1]; push_cast; ring
    have h' : ((2 ^ k - 1 : ℕ) : ℝ) ≤ ⌊t * 2 ^ k⌋₊ := by exact_mod_cast h
    rw [this] at h' ⊢
    constructor <;> linarith

lemma exists_grid_near (k : ℕ) {x : ℂ} (hx : x ∈ sq01) :
    ∃ c ∈ grid k, ‖x - c‖ ≤ (2 : ℝ)⁻¹ ^ k := by
  obtain ⟨h1, h2⟩ := mem_sq01.1 hx
  obtain ⟨i, hi, hi'⟩ := exists_coord_near k h1
  obtain ⟨j, hj, hj'⟩ := exists_coord_near k h2
  refine ⟨gridPt k (i, j), Finset.mem_image_of_mem _ (by simp [hi, hj]), ?_⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im, gridPt]
  rw [inv_pow]
  have : 1 / 2 / (2 : ℝ) ^ k + 1 / 2 / 2 ^ k = (2 ^ k)⁻¹ := by field_simp; ring
  linarith

/-- a nearest dyadic block centre -/
def snap (k : ℕ) (x : ℂ) : ℂ :=
  Classical.choose (Finset.exists_min_image (grid k) (fun c => ‖x - c‖) (grid_nonempty k))

lemma snap_mem (k : ℕ) (x : ℂ) : snap k x ∈ grid k :=
  (Classical.choose_spec (Finset.exists_min_image (grid k) (fun c => ‖x - c‖)
    (grid_nonempty k))).1

lemma norm_sub_snap_le (k : ℕ) {x : ℂ} (hx : x ∈ sq01) : ‖x - snap k x‖ ≤ (2 : ℝ)⁻¹ ^ k := by
  obtain ⟨c, hc, hxc⟩ := exists_grid_near k hx
  exact ((Classical.choose_spec (Finset.exists_min_image (grid k) (fun c => ‖x - c‖)
    (grid_nonempty k))).2 c hc).trans hxc

/-- `log L([0,1]², f)` -/
def logLen (ξ : ℝ) (f : ℂ → ℝ) : ℝ := Real.log (rectLen ξ f (rectAB 1 1)).toReal

/-- `log L^{(n)}_{1,1}(D_k)` as a function of the centre values `y` -/
def discLogLen (ξ : ℝ) (k : ℕ) (y : grid k → ℝ) : ℝ :=
  logLen ξ fun x => y ⟨snap k x, snap_mem k x⟩

variable {ξ : ℝ}

lemma crossWidth_rectAB : (rectAB 1 1).crossWidth = 1 := by
  simp [MarkedRect.crossWidth, rectAB]

/-- a bounded weight has finite positive crossing length, with real value in
`[e^{−|ξ|M}, e^{|ξ|M}]` -/
lemma toReal_rectLen_bounds {f : ℂ → ℝ} {M : ℝ} (hf : ∀ x ∈ sq01, |f x| ≤ M) :
    rectLen ξ f (rectAB 1 1) ≠ ∞ ∧
      Real.exp (-(|ξ| * M)) ≤ (rectLen ξ f (rectAB 1 1)).toReal ∧
      (rectLen ξ f (rectAB 1 1)).toReal ≤ Real.exp (|ξ| * M) := by
  have hle := rectLen_le (ξ := ξ) (rectAB 1 1) (by simp [rectAB]) (by simp [rectAB]) hf
  have hge := rectLen_ge (ξ := ξ) (rectAB 1 1) hf
  rw [crossWidth_rectAB, mul_one] at hle hge
  have hne : rectLen ξ f (rectAB 1 1) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hne, ?_, ?_⟩
  · exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hge
  · exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hle

/-- one direction of `abs_logLen_sub_le` -/
lemma logLen_le_add {f g : ℂ → ℝ} {M M' c : ℝ} (hf : ∀ x ∈ sq01, |f x| ≤ M)
    (hg : ∀ x ∈ sq01, |g x| ≤ M') (h : ∀ x ∈ sq01, |f x - g x| ≤ c) :
    logLen ξ f ≤ logLen ξ g + |ξ| * c := by
  obtain ⟨hfne, hf1, -⟩ := toReal_rectLen_bounds (ξ := ξ) hf
  obtain ⟨hgne, hg1, -⟩ := toReal_rectLen_bounds (ξ := ξ) hg
  have hcmp := crossLenIn_le_of_abs_sub_le (ξ := ξ) (A := (rectAB 1 1).side₁)
    (B := (rectAB 1 1).side₂) h
  have hR : (rectLen ξ f (rectAB 1 1)).toReal ≤
      Real.exp (|ξ| * c) * (rectLen ξ g (rectAB 1 1)).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgne) hcmp
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have hfp := (Real.exp_pos _).trans_le hf1
  have hgp := (Real.exp_pos _).trans_le hg1
  have := Real.log_le_log hfp hR
  rw [Real.log_mul (Real.exp_pos _).ne' hgp.ne', Real.log_exp] at this
  unfold logLen; linarith

/-- `|log L(f) − log L(g)| ≤ |ξ| sup_{[0,1]²} |f − g|` for bounded `f, g` -/
lemma abs_logLen_sub_le {f g : ℂ → ℝ} {M M' c : ℝ} (hf : ∀ x ∈ sq01, |f x| ≤ M)
    (hg : ∀ x ∈ sq01, |g x| ≤ M') (h : ∀ x ∈ sq01, |f x - g x| ≤ c) :
    |logLen ξ f - logLen ξ g| ≤ |ξ| * c := by
  have h1 := logLen_le_add (ξ := ξ) hf hg h
  have h2 := logLen_le_add (ξ := ξ) hg hf fun x hx => by rw [abs_sub_comm]; exact h x hx
  rw [abs_le]; constructor <;> linarith

/-- `log L^{(n)}_{1,1}(D_k)` is `|ξ|`-Lipschitz in the centre values for the sup metric
(DDDF l. 1050) -/
lemma lipschitzWith_discLogLen (ξ : ℝ) (k : ℕ) : LipschitzWith ‖ξ‖₊ (discLogLen ξ k) := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  rw [Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
  exact abs_logLen_sub_le (M := ‖y‖) (M' := ‖y'‖)
    (fun x _ => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y _)
    (fun x _ => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y' _)
    (fun x _ => by rw [← Real.dist_eq]; exact dist_le_pi_dist y y' _)

/-- `log L(f ∘ snap k) → log L(f)` for continuous `f` (DDDF l. 1046–1047) -/
lemma tendsto_logLen_snap {f : ℂ → ℝ} (hf : Continuous f) :
    Tendsto (fun k => logLen ξ fun x => f (snap k x)) atTop (𝓝 (logLen ξ f)) := by
  have hK : IsCompact sq01 := (rectAB 1 1).isCompact_toSet
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn (continuous_abs.comp hf).continuousOn).isBounded
    |>.bddAbove
  have hb : ∀ x ∈ sq01, |f x| ≤ M := fun x hx => hM ⟨x, hx, rfl⟩
  have hbs : ∀ k, ∀ x ∈ sq01, |f (snap k x)| ≤ M := fun k x _ =>
    hb _ (grid_subset (snap_mem k x))
  have huc := hK.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := huc (ε / (|ξ| + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq]
  have hc : ∀ x ∈ sq01, |f (snap k x) - f x| ≤ ε / (|ξ| + 1) := by
    intro x hx
    have hd : dist (snap k x) x < δ := by
      rw [dist_eq_norm, norm_sub_rev]
      refine (norm_sub_snap_le k hx).trans_lt (lt_of_le_of_lt ?_ hN)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    have := hδf _ (grid_subset (snap_mem k x)) _ hx hd
    rw [Real.dist_eq] at this
    exact this.le
  refine (abs_logLen_sub_le (hbs k) hb hc).trans_lt ?_
  rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
  nlinarith [abs_nonneg ξ]

end L23
end DDDF
end LQGMetric
