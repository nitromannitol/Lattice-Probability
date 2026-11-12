/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1StepArc2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepArc
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepSeg2

/-!
# DFGPS Proposition 4.1: `TubeBlocks` for an arc of a circle or a whole circle

DFGPS (arXiv:1905.00380), proof of Proposition 4.1, Steps 2–3 (T:2486–2490, T:2502), for
`L ⊆ ∂B_ρ(z)`. Centres on the circle `∂B_ρ(z)` at angular spacing `15ε/ρ` (chord `≥ 9ε`);
blocks are the centres in an angular window `[α_j, α_j + λ/8]`, `α_j = −5 + jλ/8`,
`λ = min(b/(2ρ), 1)`. Along a path from `u` to `v` in the tube the argument around `𝕣z` lifts
to a continuous function `φ` (`exists_arg_lift`) with `|φ(1) − φ(0)| ≥ λ`; the window between
`φ(0) ± λ/4` and `φ(0) ± λ/2` (on the side of `φ(1)`) is swept by `φ`, and a tube point at
angle `θ` is within `ε𝕣` of `𝕣(z + ρe^{iθ})`. The window depends on the path (for a whole circle
the path may go either way around: DEV-P41-5). Own elementary write-up.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.DFGPS.P41

open Blueprint

lemma circle_chord_ge {z : ℂ} {ρ ε α δ : ℝ} (hρ : 0 < ρ) (hδ : δ = 15 * ε / ρ) (hε : 0 < ε)
    (j k : ℕ) (hjk : |(j : ℝ) - k| * δ ≤ Real.pi) :
    9 * ε * |(j : ℝ) - k| ≤
      ‖(z + ρ * cis' (α + j * δ)) - (z + ρ * cis' (α + k * δ))‖ := by
  rw [show (z + ρ * cis' (α + j * δ)) - (z + ρ * cis' (α + k * δ)) =
    (ρ : ℂ) * (cis' (α + j * δ) - cis' (α + k * δ)) by ring, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hρ.le]
  have hab : |α + j * δ - (α + k * δ)| = |(j : ℝ) - k| * δ := by
    rw [show α + j * δ - (α + k * δ) = ((j : ℝ) - k) * δ by ring, abs_mul,
      abs_of_pos (by rw [hδ]; positivity : 0 < δ)]
  have h1 := norm_cis'_sub_ge (α + j * δ) (α + k * δ) (by rw [hab]; exact hjk)
  rw [hab] at h1
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have h2 : 9 * ε * |(j : ℝ) - k| ≤ ρ * (2 / Real.pi * (|(j : ℝ) - k| * δ)) := by
    rw [hδ]
    have e : ρ * (2 / Real.pi * (|(j : ℝ) - k| * (15 * ε / ρ))) =
        30 / Real.pi * ε * |(j : ℝ) - k| := by field_simp; ring
    rw [e]
    have : 9 ≤ 30 / Real.pi := by rw [le_div_iff₀ hπ0]; norm_num at hπ ⊢; linarith
    have h0 : 0 ≤ ε * |(j : ℝ) - k| := by positivity
    nlinarith
  exact h2.trans (mul_le_mul_of_nonneg_left h1 hρ.le)

lemma grid_exists {lam t : ℝ} (hl : 0 < lam) (hl1 : lam ≤ 1) (ht : -5 ≤ t) (ht' : t ≤ 4) :
    ∃ j : ℕ, j < ⌈80 / lam⌉₊ + 2 ∧ t ≤ -5 + j * lam / 8 ∧ -5 + j * lam / 8 < t + lam / 8 := by
  set J : ℤ := ⌈8 * (t + 5) / lam⌉ with hJ
  have hJ1 : 8 * (t + 5) / lam ≤ J := Int.le_ceil _
  have hJ2 : (J : ℝ) < 8 * (t + 5) / lam + 1 := Int.ceil_lt_add_one _
  have hJ0 : 0 ≤ J := by
    have : (0 : ℝ) ≤ 8 * (t + 5) / lam := by apply div_nonneg <;> linarith
    exact_mod_cast this.trans hJ1
  have hJn : ((J.toNat : ℕ) : ℝ) = (J : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hJ0
  refine ⟨J.toNat, ?_, ?_, ?_⟩
  · have h1 : 8 * (t + 5) / lam ≤ 80 / lam := div_le_div_of_nonneg_right (by linarith) hl.le
    have h2 : 80 / lam ≤ ⌈80 / lam⌉₊ := Nat.le_ceil _
    have : ((J.toNat : ℕ) : ℝ) < ⌈80 / lam⌉₊ + 2 := by rw [hJn]; linarith
    exact_mod_cast this
  · rw [hJn]
    have := (div_le_iff₀ hl).1 hJ1
    linarith
  · rw [hJn]
    have := (lt_div_iff₀ hl).1 (show (J : ℝ) - 1 < 8 * (t + 5) / lam by linarith)
    linarith

/-- the final step of the circle case: a window angle `θ` at angular distance `∈ [λ/4, λ/2]` from
`φ(0)` and swept by `φ` gives a far centre met by the path -/
lemma circle_window {z u : ℂ} {ρ r ε lam : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hε : 0 < ε)
    (hεl : ε < lam * ρ / 240) (hl1 : lam ≤ 1) {L : Set ℂ} (hL : L ⊆ sphere z ρ)
    (γ : ℝ → ℂ) (φ : ℝ → ℝ) (hφc : Continuous φ)
    (hφpol : ∀ t ∈ Icc (0 : ℝ) 1, γ t - r * z = ‖γ t - r * z‖ * cis' (φ t))
    (hV : γ '' Icc 0 1 ⊆ thickening (ε * r) (scaleSet r 0 L)) (h0 : γ 0 = u)
    (θ : ℝ) (hθ1 : lam / 4 ≤ |θ - φ 0|) (hθ2 : |θ - φ 0| ≤ lam / 2) (hθ : θ ∈ uIcc (φ 0) (φ 1)) :
    4 * (ε * r) < ‖u - r * (z + ρ * cis' θ)‖ ∧
      ∃ t ∈ Icc (0 : ℝ) 1, ‖γ t - r * (z + ρ * cis' θ)‖ ≤ 2 * (ε * r) := by
  have hrw : ∀ ψ : ℝ, (r : ℂ) * (z + ρ * cis' ψ) = r * z + ((r * ρ : ℝ) : ℂ) * cis' ψ := by
    intro ψ; push_cast; ring
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, |‖γ t - r * z‖ - r * ρ| < ε * r :=
    fun t ht => tube_circle hL hr (hV ⟨t, ht, rfl⟩)
  constructor
  · have hu0 := hφpol 0 ⟨le_rfl, zero_le_one⟩
    rw [h0] at hu0
    have hc0 := dist_polar (R := r * ρ) hu0
    have hm0 := hmem 0 ⟨le_rfl, zero_le_one⟩
    rw [h0] at hm0
    rw [← hc0] at hm0
    have hP : ‖(r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 0)) - (r * z + ((r * ρ : ℝ) : ℂ) * cis' θ)‖ =
        r * ρ * ‖cis' (φ 0) - cis' θ‖ := by
      rw [show (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 0)) - (r * z + ((r * ρ : ℝ) : ℂ) * cis' θ) =
        ((r * ρ : ℝ) : ℂ) * (cis' (φ 0) - cis' θ) by ring, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    have hπ := Real.pi_lt_d2
    have hch := norm_cis'_sub_ge (φ 0) θ (by rw [abs_sub_comm]; linarith [Real.pi_gt_three])
    rw [abs_sub_comm] at hch
    have hlow : 5 * (ε * r) < r * ρ * ‖cis' (φ 0) - cis' θ‖ := by
      have h1 : 2 / Real.pi * (lam / 4) ≤ ‖cis' (φ 0) - cis' θ‖ :=
        le_trans (mul_le_mul_of_nonneg_left hθ1 (by positivity)) hch
      have h2 : 5 * ε < ρ * (2 / Real.pi * (lam / 4)) := by
        have e : ρ * (2 / Real.pi * (lam / 4)) = lam * ρ / (2 * Real.pi) := by field_simp; ring
        rw [e, lt_div_iff₀ (by positivity)]
        have : 0 < lam * ρ := by
          have : 0 < lam * ρ / 240 := hε.trans hεl
          linarith
        nlinarith [Real.pi_pos]
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ r * ρ)
      nlinarith
    rw [hrw]
    have := norm_sub_le_norm_sub_add_norm_sub (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 0)) u
      (r * z + ((r * ρ : ℝ) : ℂ) * cis' θ)
    rw [norm_sub_rev (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 0)) u, hP] at this
    have hm0' : ‖u - (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 0))‖ < ε * r := by
      exact hm0
    linarith
  · obtain ⟨t, ht, hφt⟩ := intermediate_value_uIcc hφc.continuousOn hθ
    rw [uIcc_of_le zero_le_one] at ht
    refine ⟨t, ht, ?_⟩
    have hpt := hφpol t ht
    rw [hφt] at hpt
    rw [hrw, dist_polar hpt]
    exact (hmem t ht).le.trans (by linarith [mul_pos hε hr])

/-- **DFGPS Prop 4.1, Steps 2–3, arc and circle case**: the tube condition for any
`L ⊆ ∂B_ρ(z)`. -/
theorem tubeBlocks_circle {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {L : Set ℂ} (hL : L ⊆ sphere z ρ)
    {b : ℝ} (hb : 0 < b) : TubeBlocks L b := by
  set lam := min (b / (2 * ρ)) 1 with hlam
  have hl : 0 < lam := lt_min (by positivity) one_pos
  have hl1 : lam ≤ 1 := min_le_right _ _
  have hlb : lam ≤ b / (2 * ρ) := min_le_left _ _
  refine ⟨lam * ρ / 240, lam * ρ / 120, 9 / 2, ‖z‖ + ρ, lam * ρ / 240, ⌈80 / lam⌉₊ + 2,
    by positivity, by norm_num, by positivity, by positivity, ?_⟩
  intro ε hε
  obtain ⟨hε0, hεl⟩ := hε
  set δ := 15 * ε / ρ with hδ
  set N : ℕ := ⌊lam * ρ / (120 * ε)⌋₊ with hN
  have hNle : (N : ℝ) ≤ lam * ρ / (120 * ε) := Nat.floor_le (by positivity)
  have hNge : lam * ρ / (120 * ε) - 1 < N := by
    have := Nat.lt_floor_add_one (lam * ρ / (120 * ε)); linarith
  have hNδ : N * δ ≤ lam / 8 := by
    have : N * δ ≤ lam * ρ / (120 * ε) * δ :=
      mul_le_mul_of_nonneg_right hNle (by rw [hδ]; positivity)
    have e : lam * ρ / (120 * ε) * δ = lam / 8 := by rw [hδ]; field_simp; ring
    linarith
  refine ⟨fun _ => N, fun j k => z + ρ * cis' ((-5 + ((j : ℕ) : ℝ) * lam / 8) + ((k : ℕ) : ℝ) * δ),
    ?_, ?_, ?_, ?_⟩
  · intro m
    constructor
    · have h1 : lam * ρ / 240 / ε ≤ lam * ρ / (120 * ε) - 1 := by
        rw [div_div, le_sub_iff_add_le, show lam * ρ / (120 * ε) = 2 * (lam * ρ / (240 * ε)) by
          field_simp; ring]
        have : 1 ≤ lam * ρ / (240 * ε) := by rw [le_div_iff₀ (by positivity)]; linarith
        linarith
      linarith
    · simpa [div_div] using hNle
  · intro m k
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_cis', mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  · intro m j k hjk
    have hj : (j : ℝ) < N := by exact_mod_cast j.2
    have hk : (k : ℝ) < N := by exact_mod_cast k.2
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hjkπ : |((j : ℕ) : ℝ) - (k : ℕ)| * δ ≤ Real.pi := by
      have : |((j : ℕ) : ℝ) - (k : ℕ)| ≤ N := by rw [abs_le]; constructor <;> linarith
      have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
      have := mul_le_mul_of_nonneg_right this hδ0
      linarith [Real.pi_gt_three]
    have h := circle_chord_ge (z := z) (α := -5 + ((m : ℕ) : ℝ) * lam / 8) hρ hδ hε0 j k hjkπ
    rw [dN_cast]
    have h1 : 1 ≤ |((j : ℕ) : ℝ) - (k : ℕ)| := by
      rcases lt_or_gt_of_ne hjk with h | h
      · have : ((j : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
      · have : ((k : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
    constructor <;> nlinarith
  · intro r hr u hu v hv huv γ hγ h0 h1 hV
    have hερ : ε < ρ := by
      have : lam * ρ / 240 ≤ ρ / 240 := by
        have := mul_le_mul_of_nonneg_right hl1 hρ.le; linarith
      linarith
    have hne : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ r * z := by
      intro t ht heq
      have := tube_circle hL hr (hV ⟨t, ht, rfl⟩)
      rw [heq, sub_self, norm_zero, zero_sub, abs_neg, abs_of_pos (by positivity)] at this
      nlinarith
    obtain ⟨φ, hφc, hφ0, hφpol⟩ := exists_arg_lift γ hγ (r * z) hne
    rw [h0, Complex.log_im] at hφ0
    have hφr1 : -Real.pi < φ 0 := hφ0 ▸ Complex.neg_pi_lt_arg _
    have hφr2 : φ 0 ≤ Real.pi := hφ0 ▸ Complex.arg_le_pi _
    -- the sweep `|φ(1) − φ(0)| ≥ λ`
    have hsweep : lam ≤ |φ 1 - φ 0| := by
      have hu0 := hφpol 0 ⟨le_rfl, zero_le_one⟩
      have hv1 := hφpol 1 ⟨zero_le_one, le_rfl⟩
      rw [h0] at hu0
      rw [h1] at hv1
      have hcu := dist_polar (R := r * ρ) hu0
      have hcv := dist_polar (R := r * ρ) hv1
      have hmu := tube_circle hL hr hu
      have hmv := tube_circle hL hr hv
      have hP : ‖(r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 0)) - (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 1))‖
          ≤ r * ρ * |φ 1 - φ 0| := by
        rw [show (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 0)) - (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 1))
          = ((r * ρ : ℝ) : ℂ) * (cis' (φ 0) - cis' (φ 1)) by ring, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity), abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (norm_cis'_sub_le _ _) (by positivity)
      have htri : ‖u - v‖ ≤ ‖u - (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 0))‖ +
          ‖(r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 0)) - (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 1))‖ +
          ‖v - (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 1))‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub u (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 0)) v
        have h4 := norm_sub_le_norm_sub_add_norm_sub (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 0))
          (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 1)) v
        rw [norm_sub_rev (r * z + ((r * ρ : ℝ) : ℂ) * cis' (φ 1)) v] at h4
        linarith
      rw [hcu, hcv] at htri
      have hεb : 2 * ε ≤ b / 2 := by
        have : lam * ρ ≤ b / 2 := by
          have := mul_le_mul_of_nonneg_right hlb hρ.le
          rwa [show b / (2 * ρ) * ρ = b / 2 by field_simp] at this
        linarith
      have key : b * r < 2 * (ε * r) + r * ρ * |φ 1 - φ 0| := by linarith
      have key2 : b / 2 * r < r * ρ * |φ 1 - φ 0| := by nlinarith
      have key3 : b / 2 < ρ * |φ 1 - φ 0| := by
        by_contra hc; push Not at hc; nlinarith
      have : b / (2 * ρ) ≤ |φ 1 - φ 0| := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    have hπ := Real.pi_lt_d2
    have hπ3 := Real.pi_gt_three
    rcases le_abs'.1 hsweep with hB | hA
    · -- `φ(1) ≤ φ(0) − λ`: window in `[φ(0) − λ/2, φ(0) − λ/4)`
      obtain ⟨j, hjM, hj1, hj2⟩ := grid_exists (t := φ 0 - lam / 2) hl hl1 (by norm_num at hπ ⊢; linarith)
        (by norm_num at hπ ⊢; linarith)
      refine ⟨⟨j, hjM⟩, fun k => ?_, fun k => ?_⟩ <;>
      · have hk : (k : ℝ) < N := by exact_mod_cast k.2
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        have hkδ : (k : ℝ) * δ ≤ lam / 8 :=
          le_trans (mul_le_mul_of_nonneg_right hk.le (by rw [hδ]; positivity)) hNδ
        have hkδ0 : 0 ≤ (k : ℝ) * δ := mul_nonneg hk0 (by rw [hδ]; positivity)
        have W := circle_window hρ hr hε0 hεl hl1 hL γ φ hφc hφpol hV h0
          ((-5 + ((j : ℕ) : ℝ) * lam / 8) + ((k : ℕ) : ℝ) * δ)
          (by rw [abs_of_neg (by simp only at hj1 hj2 ⊢; linarith)]; simp only at hj1 hj2 ⊢; linarith)
          (by rw [abs_of_neg (by simp only at hj1 hj2 ⊢; linarith)]; simp only at hj1 hj2 ⊢; linarith)
          (by rw [mem_uIcc]; right; simp only at hj1 hj2 ⊢; constructor <;> linarith)
        first
        | exact W.1
        | exact W.2
    · -- `φ(1) ≥ φ(0) + λ`: window in `[φ(0) + λ/4, φ(0) + λ/2)`
      obtain ⟨j, hjM, hj1, hj2⟩ := grid_exists (t := φ 0 + lam / 4) hl hl1 (by norm_num at hπ ⊢; linarith)
        (by norm_num at hπ ⊢; linarith)
      refine ⟨⟨j, hjM⟩, fun k => ?_, fun k => ?_⟩ <;>
      · have hk : (k : ℝ) < N := by exact_mod_cast k.2
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        have hkδ : (k : ℝ) * δ ≤ lam / 8 :=
          le_trans (mul_le_mul_of_nonneg_right hk.le (by rw [hδ]; positivity)) hNδ
        have hkδ0 : 0 ≤ (k : ℝ) * δ := mul_nonneg hk0 (by rw [hδ]; positivity)
        have W := circle_window hρ hr hε0 hεl hl1 hL γ φ hφc hφpol hV h0
          ((-5 + ((j : ℕ) : ℝ) * lam / 8) + ((k : ℕ) : ℝ) * δ)
          (by rw [abs_of_pos (by simp only at hj1 hj2 ⊢; linarith)]; simp only at hj1 hj2 ⊢; linarith)
          (by rw [abs_of_pos (by simp only at hj1 hj2 ⊢; linarith)]; simp only at hj1 hj2 ⊢; linarith)
          (by rw [mem_uIcc]; left; simp only at hj1 hj2 ⊢; constructor <;> linarith)
        first
        | exact W.1
        | exact W.2

end LQGMetric.DFGPS.P41
