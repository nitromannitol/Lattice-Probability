/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L6Max at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Log
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.GaussianTail
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2HatTail

/-!
# DZZ Lemma 2.6, second inequality: tail form (task P2-DZZPRE2)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 521, 527–529: "By Lemma 2.5, we can
apply Lemma 2.3 [Fernique] … Combined with Lemma 2.1 [concentration], this yields the second
inequality by considering a union bound over `u ∈ 𝔠_{⌈log₂ δ⁻¹⌉+1}`."

`dzz_sup_incr_tail`: for a continuous centred Gaussian field `X` with
`E(X_v − X_u)² ≤ K|u − v|/δ` (Lemma 2.5), the modulus `max_{u,v ∈ 𝕍, |u−v| ≤ δ} |X_u − X_v|`
exceeds `2(√(12K log(2m²)) + C_F √(3K) + x)` (`m = ⌈1/δ⌉`) with probability `≤ e^{−x²/(12K)}`.
This is DZZ's union bound (over the `2m²` boxes of side `3δ` around the grid squares of side
`1/m ≤ δ`, and both signs) with Fernique + concentration per box, i.e. Ding–Goswami's Lemma 3.4
(`DGo.dgo_lemma34`). The expectation form `E max = O(√(log δ⁻¹))` follows by integrating the
tail (remaining, see handoff/P2-DZZPRE2.md).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DZZ

open SupTail DGo

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **DZZ Lemma 2.6, second inequality, tail form**, for one field `X ∈ {h̃_δ, η_δ}`. -/
theorem dzz_sup_incr_tail [IsProbabilityMeasure P] {X : ℂ → Ω → ℝ} (hX : IsGaussianProcess X P)
    (h0 : ∀ v, ∫ ω, X v ω ∂P = 0) (hc : ∀ ω, Continuous fun v => X v ω) {K δ : ℝ} (hK : 0 < K)
    (hδ : 0 < δ) (hinc : ∀ u v, ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ K * ‖u - v‖ / δ) {x : ℝ}
    (hx : 0 ≤ x) :
    P.real {ω | ∃ u ∈ ferniqueBox 0 1, ∃ v ∈ ferniqueBox 0 1, ‖u - v‖ ≤ δ ∧
      2 * (Real.sqrt (2 * (6 * K) * Real.log (2 * (⌈1 / δ⌉₊ : ℝ) ^ 2)) +
        ferniqueCF * Real.sqrt (3 * K) + x) ≤ |X u ω - X v ω|} ≤
      Real.exp (-x ^ 2 / (2 * (6 * K))) := by
  set m := ⌈1 / δ⌉₊ with hm_def
  have hm : 0 < m := Nat.ceil_pos.2 (by positivity)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have h1m : 1 / (m : ℝ) ≤ δ := by
    have h := Nat.le_ceil (1 / δ)
    rw [← hm_def, div_le_iff₀ hδ] at h
    rw [div_le_iff₀ hm']
    linarith
  have : NeZero m := ⟨hm.ne'⟩
  set ι := (Fin m × Fin m) × Bool
  have : Nonempty ι := ⟨((0, 0), true)⟩
  set cr : Fin m × Fin m → ℂ := fun kl => ⟨kl.1 * (1 / m), kl.2 * (1 / m)⟩
  set yy : ι → ℂ := fun i => cr i.1 - ⟨δ, δ⟩
  set sg : Bool → ℝ := fun b => if b then 1 else -1
  have hsg : ∀ b, sg b ^ 2 = 1 := fun b => by cases b <;> simp [sg]
  set Y : ι → ℂ → Ω → ℝ := fun i v ω => sg i.2 * (X v ω - X (cr i.1) ω)
  have hL2 : ∀ v, MemLp (X v) 2 P := fun v => (hX.hasGaussianLaw_eval v).memLp_two
  have hY : ∀ i, IsGaussianProcess (Y i) P := fun i =>
    (isGaussianProcess_sub_const hX (cr i.1)).smul (fun _ => sg i.2)
  have hY0 : ∀ i v, ∫ ω, Y i v ω ∂P = 0 := fun i v => by
    simp only [Y]
    rw [integral_const_mul, integral_sub ((hL2 v).integrable one_le_two)
      ((hL2 _).integrable one_le_two), h0, h0, sub_self, mul_zero]
  have hYsq : ∀ i u v, ∫ ω, (Y i v ω - Y i u ω) ^ 2 ∂P = ∫ ω, (X v ω - X u ω) ^ 2 ∂P :=
    fun i u v => integral_congr_ae (Eventually.of_forall fun ω => by
      simp only [Y]
      have := hsg i.2
      linear_combination (X v ω - X u ω) ^ 2 * this)
  have hcen : ∀ i, cr i.1 ∈ ferniqueBox (yy i) (3 * δ) := fun i => by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [yy] <;> linarith
  have h34 := dgo_lemma34 (Y := Y) (y := yy) (b := fun _ => 3 * δ) (P := P) hY hY0
    (fun _ => by positivity) (C := 3 * K) (C' := 6 * K) (by positivity) (by positivity)
    (fun i ω => ((continuous_const.mul ((hc ω).sub continuous_const))).continuousOn)
    (fun i u _ v _ => by
      rw [hYsq]
      refine (hinc u v).trans (le_of_eq ?_)
      field_simp)
    (fun i v hv => by
      refine (variance_le_expectation_sq ((hY i).aemeasurable v).aestronglyMeasurable).trans ?_
      have e : ∫ ω, (Y i v ^ 2) ω ∂P = ∫ ω, (X v ω - X (cr i.1) ω) ^ 2 ∂P := by
        have := hYsq i (cr i.1) v
        simp only [Y, sub_self, mul_zero, sub_zero] at this
        simpa [Y] using this
      rw [e]
      refine (hinc _ _).trans ?_
      have hd := norm_sub_le_of_mem_ferniqueBox (hcen i) hv
      rw [div_le_iff₀ hδ]
      nlinarith)
    hx
  have hcard : (Fintype.card ι : ℝ) = 2 * (m : ℝ) ^ 2 := by
    simp only [ι, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    push_cast; ring
  rw [hcard] at h34
  refine (measureReal_mono (fun ω hω => ?_)).trans h34
  obtain ⟨u, hu, v, hv, huv, hω⟩ := hω
  simp only [mem_ofPred_eq]
  set T := Real.sqrt (2 * (6 * K) * Real.log (2 * (m : ℝ) ^ 2)) +
    ferniqueCF * Real.sqrt (3 * K) + x
  obtain ⟨k, l, hkl⟩ := exists_mem_subBox one_pos hm hu
  set kl : Fin m × Fin m := (k, l)
  -- `u, v` lie in the box `R = yy (kl, _)` of side `3δ`
  have hmemR : ∀ b : Bool, u ∈ ferniqueBox (yy (kl, b)) (3 * δ) ∧
      v ∈ ferniqueBox (yy (kl, b)) (3 * δ) := by
    intro b
    have h1m' : (m : ℝ)⁻¹ ≤ δ := by rwa [one_div] at h1m
    obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hkl
    simp only [zero_add] at a1 a2 a3 a4
    have r1 := Complex.abs_re_le_norm (u - v)
    have r2 := Complex.abs_im_le_norm (u - v)
    rw [Complex.sub_re, abs_le] at r1
    rw [Complex.sub_im, abs_le] at r2
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [yy, cr, kl] at a1 a2 a3 a4 ⊢ <;>
      nlinarith
  -- one of `|X_u − X_c|`, `|X_v − X_c|` is `≥ T`
  set c := cr kl
  have htri : |X u ω - X v ω| ≤ |X u ω - X c ω| + |X v ω - X c ω| := by
    have := abs_sub_le (X u ω) (X c ω) (X v ω)
    rwa [abs_sub_comm (X c ω) (X v ω)] at this
  have hex : ∃ w ∈ ferniqueBox (yy (kl, true)) (3 * δ), T ≤ |X w ω - X c ω| := by
    by_contra hn
    push Not at hn
    have := hn u (hmemR true).1
    have := hn v (hmemR true).2
    linarith
  obtain ⟨w, hw, hTw⟩ := hex
  set b : Bool := decide (0 ≤ X w ω - X c ω)
  have hYw : Y (kl, b) w ω = |X w ω - X c ω| := by
    simp only [Y, sg, b, c]
    by_cases h : 0 ≤ X w ω - X (cr kl) ω
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (not_le.mp h)]
  have hwb : w ∈ ferniqueBox (yy (kl, b)) (3 * δ) := hw
  have hbdd : ∀ i, BddAbove (range fun z : ferniqueBox (yy i) (3 * δ) => Y i z ω) := by
    intro i
    obtain ⟨M, hM⟩ := (isCompact_ferniqueBox (yy i) (3 * δ)).bddAbove_image
      (f := fun z => Y i z ω) (continuous_const.mul ((hc ω).sub continuous_const)).continuousOn
    exact ⟨M, by rintro _ ⟨z, rfl⟩; exact hM ⟨z, z.2, rfl⟩⟩
  calc T ≤ Y (kl, b) w ω := by rw [hYw]; exact hTw
    _ ≤ ⨆ z : ferniqueBox (yy (kl, b)) (3 * δ), Y (kl, b) z ω :=
        le_ciSup (f := fun z : ferniqueBox (yy (kl, b)) (3 * δ) => Y (kl, b) z ω)
          (hbdd _) ⟨w, hwb⟩
    _ ≤ ⨆ i, ⨆ z : ferniqueBox (yy i) (3 * δ), Y i z ω :=
        le_ciSup (f := fun i => ⨆ z : ferniqueBox (yy i) (3 * δ), Y i z ω)
          (Finite.bddAbove_range _) (kl, b)

end DZZ
end LQGMetric
