/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56P3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56P2

/-!
# GM Lemma 5.6: `L56Paths` (task P2-M2L56c)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6, l. 2963–2966.
`l56Paths` transfers the normalized construction `l56PathsNorm` (Geom56P2.lean) by the similarity
`Φ ζ = z + r e ζ` (inverse `Ψ w = (w − z) ē / r`), where `e` is the unit normal of the half
annulus `H`; `b = min (1/8) (1 − α)` (GM take `b = 1 − α`; only `b > 0` is used).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Complex

namespace LQGMetric.GM
open Blueprint

/-- **GM l. 2963–2966**: the paths `π₋`, `π₊` exist -/
theorem l56Paths : L56Paths := by
  intro α hα hα1
  refine ⟨min (1 / 8) (1 - α), lt_min (by norm_num) (by linarith), ?_⟩
  intro z r hr H hH u hu v hv huH hvH
  obtain ⟨e, he, rfl⟩ := hH
  set c := (starRingEnd ℂ) e with hcdef
  have hc : ‖c‖ = 1 := by rw [hcdef, Complex.norm_conj, he]
  have hec : e * c = 1 := by
    rw [hcdef, Complex.mul_conj, Complex.normSq_eq_norm_sq, he]; norm_num
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hcl : ∀ h ∈ closure ((annulus z (α * r) r : Set ℂ) ∩
      {w | 0 < ((w - z) * (starRingEnd ℂ) e).re}),
      α * r ≤ ‖h - z‖ ∧ ‖h - z‖ ≤ r ∧ 0 ≤ ((h - z) * c).re := by
    refine closure_minimal ?_ ?_
    · rintro w ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1.le, h2.le, le_of_lt h3⟩
    · exact (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
        ((isClosed_le (continuous_id.sub continuous_const).norm continuous_const).inter
        (isClosed_le continuous_const (Complex.continuous_re.comp
          ((continuous_id.sub continuous_const).mul continuous_const))))
  set Φ : ℂ → ℂ := fun ζ => z + (r : ℂ) * e * ζ with hΦ
  set Ψ : ℂ → ℂ := fun w => (w - z) * c / r with hΨ
  have hΦΨ : ∀ w, Φ (Ψ w) = w := by
    intro w
    have : (r : ℂ) * e * ((w - z) * c / r) = (w - z) * (e * c) := by field_simp
    simp only [hΦ, hΨ]; rw [this, hec]; ring
  have hdist : ∀ a b, dist (Φ a) (Φ b) = r * ‖a - b‖ := by
    intro a b
    rw [dist_eq_norm, show Φ a - Φ b = (r : ℂ) * e * (a - b) by simp only [hΦ]; ring, norm_mul,
      norm_mul, he, Complex.norm_real, Real.norm_of_nonneg hr.le, mul_one]
  have hΨn : ∀ w, ‖Ψ w‖ = ‖w - z‖ / r := by
    intro w
    simp only [hΨ]
    rw [norm_div, norm_mul, hc, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hΨre : ∀ w, (Ψ w).re = ((w - z) * c).re / r := fun w => Complex.div_ofReal_re _ _
  have hΦk : ∀ (k : ℝ) (ζ : ℂ), Φ ((k : ℂ) * ζ) = z + (k : ℂ) * (Φ ζ - z) := by
    intro k ζ; simp only [hΦ]; ring
  have hvz : ‖v - z‖ = r := by rw [← dist_eq_norm]; exact hv
  have hω : ‖Ψ v‖ = 1 := by rw [hΨn, hvz, div_self hr.ne']
  have hωre : 0 ≤ (Ψ v).re := by rw [hΨre]; exact div_nonneg (hcl v hvH).2.2 hr.le
  obtain ⟨Pm, Pp, hPm, hPp, hball, hm2, hm0, hp1, hp2, hH', hsep⟩ :=
    l56PathsNorm hα hα1 hc hω hωre
  have hΦc : Continuous Φ := by simp only [hΦ]; fun_prop
  have hΦ0 : Φ 0 = z := by simp only [hΦ]; ring
  have hball' : ∀ ζ ∈ Pm ∪ Pp, Φ ζ ∈ closedBall z (2 * r) := by
    intro ζ hζ
    rw [mem_closedBall, ← hΦ0, hdist, sub_zero]
    nlinarith [hball ζ hζ]
  have hdist' : ∀ p q, dist p q = r * ‖Ψ p - Ψ q‖ := by
    intro p q; rw [← hdist, hΦΨ, hΦΨ]
  refine ⟨Φ '' Pm, Φ '' Pp, hPm.image _ hΦc.continuousOn, hPp.image _ hΦc.continuousOn,
    ?_, ?_, ⟨_, hm2, ?_⟩, ⟨0, hm0, hΦ0⟩, ⟨_, hp1, ?_⟩, ⟨_, hp2, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨ζ, hζ, rfl⟩; exact hball' ζ (Or.inl hζ)
  · rintro _ ⟨ζ, hζ, rfl⟩; exact hball' ζ (Or.inr hζ)
  · simp only [hΦ]; push_cast; linear_combination (-2 * (r : ℂ)) * hec
  · rw [hΦk, hΦΨ]; push_cast; ring
  · simp only [hΦ]; push_cast; linear_combination (2 * (r : ℂ)) * hec
  · rintro p hp h hh
    obtain ⟨ζ, hζ, rfl⟩ : ∃ ζ ∈ Pm ∪ Pp, Φ ζ = p := by
      rcases hp with ⟨ζ, hζ, rfl⟩ | ⟨ζ, hζ, rfl⟩
      · exact ⟨ζ, Or.inl hζ, rfl⟩
      · exact ⟨ζ, Or.inr hζ, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hcl h hh
    rw [← hΦΨ h, hdist, mul_comm]
    refine mul_le_mul_of_nonneg_left (hH' ζ hζ (Ψ h) ?_ ?_ ?_) hr.le
    · rw [hΨn, le_div_iff₀ hr]; exact h1
    · rw [hΨn, div_le_one hr]; exact h2
    · rw [hΨre]; exact div_nonneg h3 hr.le
  · intro p hp q hq
    rw [hdist', mul_comm]
    refine mul_le_mul_of_nonneg_left (hsep (Ψ p) ?_ (Ψ q) ?_) hr.le
    · rcases hp with ⟨ζ, hζ, rfl⟩ | hp
      · left; rw [show Ψ (Φ ζ) = ζ by
          simp only [hΦ, hΨ]; field_simp; linear_combination (r : ℂ) * ζ * hec]
        exact hζ
      · right
        have hpb := (convex_closedBall z (α * r)).segment_subset (mem_closedBall_self
          (by nlinarith)) (sphere_subset_closedBall hu) hp
        rw [mem_closedBall, dist_eq_norm] at hpb
        rw [hΨn, div_le_iff₀ hr]; exact hpb
    · rcases hq with ⟨ζ, hζ, rfl⟩ | hq
      · left; rw [show Ψ (Φ ζ) = ζ by
          simp only [hΦ, hΨ]; field_simp; linear_combination (r : ℂ) * ζ * hec]
        exact hζ
      · right
        rw [segment_eq_image ℝ] at hq
        obtain ⟨θ, hθ, rfl⟩ := hq
        refine ⟨1 + θ / 2, by linarith [hθ.1], by linarith [hθ.2], ?_⟩
        simp only [hΨ, Complex.real_smul]; push_cast; ring

end LQGMetric.GM
