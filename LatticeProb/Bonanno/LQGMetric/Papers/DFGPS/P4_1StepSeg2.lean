/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1StepSeg2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepSeg

/-!
# DFGPS Proposition 4.1: `TubeBlocks` for a line segment

DFGPS (arXiv:1905.00380), proof of Proposition 4.1, Step 2 (T:2486–2490) and Step 3 (T:2502),
for `L ⊆ {a + σe : σ ∈ [0, ℓ]}` (`‖e‖ = 1`). Blocks `m < M`: centres
`w m k = a + ((m − 2)b/8 + 9kε) e`, `k < ⌊b/(72ε)⌋`. For `u, v` in the tube with `|u − v| ≥ b𝕣`
the line coordinates differ by `≥ b/2`; the block starting at `(⌈8x/b⌉ + 1) b/8`
(`x = min(q(u), q(v))`) lies between `x + b/8` and `x + 3b/8`, and the intermediate value theorem
for `q ∘ γ` gives the crossings. See `P4_1StepSeg` for the elementary facts used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.DFGPS.P41

open Blueprint

lemma continuous_lineCoord (a e : ℂ) (r : ℝ) : Continuous (lineCoord a e r) := by
  unfold lineCoord
  fun_prop

/-- tube points have line coordinate in `(-ε, ℓ + ε)` -/
lemma tube_coord_range {a e : ℂ} (he : ‖e‖ = 1) {ℓ : ℝ} {L : Set ℂ}
    (hL : ∀ x ∈ L, ∃ σ ∈ Icc 0 ℓ, x = a + σ * e) {r ε : ℝ} (hr : 0 < r) {y : ℂ}
    (hy : y ∈ thickening (ε * r) (scaleSet r 0 L)) :
    -ε < lineCoord a e r y ∧ lineCoord a e r y < ℓ + ε := by
  obtain ⟨σ, hσ, hd⟩ := tube_near hL hy
  have h1 := lineCoord_lip (a := a) he hr y (r * (a + σ * e))
  rw [lineCoord_pt he hr, le_div_iff₀ hr] at h1
  have h2 : |lineCoord a e r y - σ| < ε := by
    by_contra hc
    push Not at hc
    nlinarith
  rw [abs_lt] at h2
  constructor <;> linarith [hσ.1, hσ.2]

/-- **DFGPS Prop 4.1, Steps 2–3, segment case**: the tube condition for (a subset of) a segment. -/
theorem tubeBlocks_line {a e : ℂ} (he : ‖e‖ = 1) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {L : Set ℂ}
    (hL : ∀ x ∈ L, ∃ σ ∈ Icc 0 ℓ, x = a + σ * e) {b : ℝ} (hb : 0 < b) : TubeBlocks L b := by
  set M : ℕ := ⌈8 * (ℓ + 1) / b⌉₊ + 4 with hM
  refine ⟨b / 144, b / 72, 9 / 2, ‖a‖ + (M + 3) * b / 8, min (b / 200) 1, M, by positivity,
    by norm_num, by positivity, by positivity, ?_⟩
  intro ε hε
  obtain ⟨hε0, hεlt⟩ := hε
  have hεb : ε < b / 200 := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hε1 : ε < 1 := lt_of_lt_of_le hεlt (min_le_right _ _)
  set N : ℕ := ⌊b / (72 * ε)⌋₊ with hN
  have hNle : (N : ℝ) ≤ b / (72 * ε) := Nat.floor_le (by positivity)
  have hNge : b / (72 * ε) - 1 < N := by
    have := Nat.lt_floor_add_one (b / (72 * ε)); linarith
  have hNε : 9 * N * ε ≤ b / 8 := by
    have : (N : ℝ) * (72 * ε) ≤ b := by rwa [le_div_iff₀ (by positivity)] at hNle
    linarith
  refine ⟨fun _ => N, fun m k => a + (((m : ℝ) - 2) * b / 8 + 9 * k * ε : ℝ) * e, ?_, ?_, ?_, ?_⟩
  · -- block sizes
    intro m
    constructor
    · have h1 : b / 144 / ε ≤ b / (72 * ε) - 1 := by
        rw [div_div, le_sub_iff_add_le, show b / (72 * ε) = 2 * (b / (144 * ε)) by
          field_simp; ring]
        have : 1 ≤ b / (144 * ε) := by rw [le_div_iff₀ (by positivity)]; linarith
        linarith
      linarith
    · simpa [div_div] using hNle
  · -- the centres are bounded
    intro m k
    have hk : (k : ℝ) < N := by exact_mod_cast k.2
    have hm : (m : ℝ) < M := by exact_mod_cast m.2
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs]
    refine add_le_add le_rfl ?_
    rw [abs_le]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    constructor <;> nlinarith
  · -- separation
    intro m j k hjk
    have hne : (j : ℝ) ≠ k := by
      intro h; exact hjk (Fin.ext (by exact_mod_cast h))
    have heq : ‖a + ((((m : ℝ) - 2) * b / 8 + 9 * j * ε : ℝ) : ℂ) * e -
        (a + ((((m : ℝ) - 2) * b / 8 + 9 * k * ε : ℝ) : ℂ) * e)‖ = 9 * ε * |(j : ℝ) - k| := by
      rw [show a + ((((m : ℝ) - 2) * b / 8 + 9 * j * ε : ℝ) : ℂ) * e -
        (a + ((((m : ℝ) - 2) * b / 8 + 9 * k * ε : ℝ) : ℂ) * e) =
          ((9 * ε * ((j : ℝ) - k) : ℝ) : ℂ) * e by push_cast; ring,
        norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 9 * ε)]
    rw [heq, dN_cast]
    have h1 : 1 ≤ |(j : ℝ) - k| := by
      rcases lt_or_gt_of_ne hjk with h | h
      · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
      · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
    constructor <;> nlinarith
  · -- the crossing property
    intro r hr u hu v hv huv γ hγ h0 h1 hV
    set qu := lineCoord a e r u
    set qv := lineCoord a e r v
    have hd := tube_dist_le he hL hr hu hv
    have hsep : b / 2 ≤ |qu - qv| := by
      have : b * r ≤ r * |qu - qv| + 4 * (ε * r) := huv.trans hd
      by_contra hc
      push Not at hc
      nlinarith
    obtain ⟨hqu1, hqu2⟩ := tube_coord_range he hL hr hu
    obtain ⟨hqv1, hqv2⟩ := tube_coord_range he hL hr hv
    set x := min qu qv with hx
    have hxl : -ε < x := lt_min hqu1 hqv1
    have hxu : x < ℓ + ε := lt_of_le_of_lt (min_le_left _ _) hqu2
    set J : ℤ := ⌈8 * x / b⌉ with hJ
    have hJ1 : 8 * x / b ≤ J := Int.le_ceil _
    have hJ2 : (J : ℝ) < 8 * x / b + 1 := Int.ceil_lt_add_one _
    have hJ1' : 8 * x ≤ J * b := by rwa [div_le_iff₀ hb] at hJ1
    have hJ2' : J * b < 8 * x + b := by
      have := (lt_div_iff₀ hb).1 (show (J : ℝ) - 1 < 8 * x / b by linarith)
      linarith
    have hJ0 : 0 ≤ J := by
      have h1 : (-1 : ℝ) < J := by
        have : -1 < 8 * x / b := by rw [lt_div_iff₀ hb]; linarith
        linarith
      have : (-1 : ℤ) < J := by exact_mod_cast h1
      omega
    have hJnat : ((J.toNat : ℕ) : ℝ) = (J : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hJ0
    have hmM : J.toNat + 3 < M := by
      have h2 : 8 * (ℓ + 1) / b ≤ ⌈8 * (ℓ + 1) / b⌉₊ := Nat.le_ceil _
      have h3 : 8 * x / b < 8 * (ℓ + 1) / b := div_lt_div_of_pos_right (by linarith) hb
      have : ((J.toNat + 3 : ℕ) : ℝ) < M := by
        rw [hM]; push_cast; rw [hJnat]; linarith
      exact_mod_cast this
    have hm2 : (((⟨J.toNat + 3, hmM⟩ : Fin M) : ℕ) : ℝ) - 2 = J + 1 := by
      simp only [Nat.cast_add, hJnat]; push_cast; ring
    have hsk : ∀ k : Fin N, x + b / 8 ≤ (((⟨J.toNat + 3, hmM⟩ : Fin M) : ℕ) - 2) * b / 8 +
        9 * (k : ℕ) * ε ∧ (((⟨J.toNat + 3, hmM⟩ : Fin M) : ℕ) - 2) * b / 8 + 9 * (k : ℕ) * ε ≤
          x + 3 * b / 8 := by
      intro k
      have hk : (k : ℝ) < N := by exact_mod_cast k.2
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      have h9 : 9 * (k : ℝ) * ε ≤ b / 8 := by nlinarith
      rw [hm2]
      constructor <;> nlinarith
    refine ⟨⟨J.toNat + 3, hmM⟩, fun k => ?_, fun k => ?_⟩
    · obtain ⟨hs1, hs2⟩ := hsk k
      set sk := (((⟨J.toNat + 3, hmM⟩ : Fin M) : ℕ) - 2) * b / 8 + 9 * ((k : ℕ) : ℝ) * ε
      have hlip := lineCoord_lip (a := a) he hr u (r * (a + sk * e))
      rw [lineCoord_pt he hr, le_div_iff₀ hr] at hlip
      have hfar : b / 8 ≤ |qu - sk| := by
        rcases le_total qu qv with h | h
        · have : x = qu := min_eq_left h
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
        · have hx' : x = qv := min_eq_right h
          rw [abs_of_nonneg (by linarith)] at hsep
          rw [abs_of_nonneg (by linarith)]
          linarith
      have : |qu - sk| * r ≤ ‖u - r * (a + sk * e)‖ := hlip
      have h4 : 4 * (ε * r) < b / 8 * r := by nlinarith
      have h5 := mul_le_mul_of_nonneg_right hfar hr.le
      exact lt_of_lt_of_le h4 (h5.trans this)
    · obtain ⟨hs1, hs2⟩ := hsk k
      set sk := (((⟨J.toNat + 3, hmM⟩ : Fin M) : ℕ) - 2) * b / 8 + 9 * ((k : ℕ) : ℝ) * ε
      have hf : Continuous (lineCoord a e r ∘ γ) := (continuous_lineCoord a e r).comp hγ
      have hmem : sk ∈ uIcc ((lineCoord a e r ∘ γ) 0) ((lineCoord a e r ∘ γ) 1) := by
        simp only [Function.comp, h0, h1]
        rw [mem_uIcc]
        rcases le_total qu qv with h | h
        · have : x = qu := min_eq_left h
          rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hsep
          left; constructor <;> linarith
        · have : x = qv := min_eq_right h
          rw [abs_of_nonneg (by linarith)] at hsep
          right; constructor <;> linarith
      obtain ⟨t, ht, hft⟩ := intermediate_value_uIcc hf.continuousOn hmem
      rw [uIcc_of_le zero_le_one] at ht
      have hγt : γ t ∈ thickening (ε * r) (scaleSet r 0 L) := hV ⟨t, ht, rfl⟩
      exact ⟨t, ht, (tube_coord_close he hL hr hγt hft).le⟩

end LQGMetric.DFGPS.P41
