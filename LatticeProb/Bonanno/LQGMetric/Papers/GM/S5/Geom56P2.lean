/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56P2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56P1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CPaths

/-!
# GM Lemma 5.6: the paths `π₋`, `π₊` (task P2-M2L56c), proof of `L56Paths`

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.6, l. 2963–2966: "We can choose a path `π₋` from `z − 2r` to `z` and a path `π₊` from
`v'` to `z + 2r` in `B_{2r}(z)` such that the Euclidean distances from `π₋ ∪ π₊` to `H_r(z)` and
from `π₋ ∪ L₋` to `π₊ ∪ L₊` are each at least `b r`."

GM give no construction; ours (own elementary argument) in the coordinates
`ζ = (w − z) ē / r`, where `H = A_{αr,r}(z) ∩ {Re((w − z) ē) > 0}` becomes the standard half annulus
`{α < |ζ| < 1, Re ζ > 0}`, `z ± 2r` become `± 2c` with `c = ē`, and `v` becomes a unit `ω` with
`Re ω ≥ 0`. Pick a unit `g` with `Re g ≤ −1/2` and `|g − c| ≥ 1/2` (`l56_exists_dir`).
* `π₋ = [0, 7/4 · g] ∪ 7/4 · (arc from g to −c avoiding c) ∪ [−7/4 · c, −2c]`;
* `π₊ = 3/2 · (arc from ω to c avoiding g) ∪ [3/2 · c, 2c]`.
Distances: the radii `7/4`, `3/2`, `≤ 3/2` (of `L₊`), `≤ α` (of `L₋`), `≤ 1` (of `H`) separate most
pieces; the remaining pairs are two rays whose directions are `≥ 1/2` apart (`l56_rad_sep`), and the
ray `[0, 7/4 g]` against `cl H` (`l56_rad_hp_sep`). The constant is `b = min (1/8) (1 − α)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Complex

namespace LQGMetric.GM

/-- **normalized paths** (`z = 0`, `r = 1`, half plane `Re (ζ c̄ ) …` rotated to `Re ζ > 0`) -/
theorem l56PathsNorm {α : ℝ} (hα : 3 / 4 ≤ α) (hα1 : α < 1) {c ω : ℂ} (hc : ‖c‖ = 1)
    (hω : ‖ω‖ = 1) (hωre : 0 ≤ ω.re) :
    ∃ Pm Pp : Set ℂ, IsPreconnected Pm ∧ IsPreconnected Pp ∧ (∀ p ∈ Pm ∪ Pp, ‖p‖ ≤ 2) ∧
      ((2 : ℝ) : ℂ) * -c ∈ Pm ∧ (0 : ℂ) ∈ Pm ∧ ((3 / 2 : ℝ) : ℂ) * ω ∈ Pp ∧
      ((2 : ℝ) : ℂ) * c ∈ Pp ∧
      (∀ p ∈ Pm ∪ Pp, ∀ h : ℂ, α ≤ ‖h‖ → ‖h‖ ≤ 1 → 0 ≤ h.re →
        min (1 / 8) (1 - α) ≤ ‖p - h‖) ∧
      (∀ p : ℂ, (p ∈ Pm ∨ ‖p‖ ≤ α) → ∀ q : ℂ,
        (q ∈ Pp ∨ ∃ s : ℝ, 1 ≤ s ∧ s ≤ 3 / 2 ∧ q = (s : ℂ) * ω) →
        min (1 / 8) (1 - α) ≤ ‖p - q‖) := by
  obtain ⟨g, hg, hgre, hgc⟩ := l56_exists_dir c
  have hωg : 1 / 2 ≤ ‖ω - g‖ := by
    have := Complex.re_le_norm (ω - g); rw [Complex.sub_re] at this; linarith
  have hnc : ‖-c‖ = 1 := by rw [norm_neg, hc]
  have hcc : ‖-c - c‖ = 2 := by
    rw [show -c - c = ((-2 : ℝ) : ℂ) * c by push_cast; ring, norm_mul, hc, Complex.norm_real]
    norm_num
  obtain ⟨A, hA, hgA, hcA, hAx⟩ := l56_exists_arc_avoid hg hnc hc hgc (by rw [hcc]; norm_num)
  obtain ⟨B, hB, hωB, hcB, hBx⟩ := l56_exists_arc_avoid hω hc hg hωg (by rwa [norm_sub_rev])
  have hb8 : min (1 / 8) (1 - α) ≤ 1 / 8 := min_le_left _ _
  have hb1 : min (1 / 8) (1 - α) ≤ 1 - α := min_le_right _ _
  set b := min (1 / 8) (1 - α)
  have hrad : ∀ x : ℂ, ∀ a b : ℝ, IsPreconnected ((fun t : ℝ => (t : ℂ) * x) '' Icc a b) :=
    fun x a b => isPreconnected_Icc.image _ (by fun_prop : Continuous _).continuousOn
  have hsc : ∀ (ρ : ℝ) (S : Set ℂ), IsPreconnected S →
      IsPreconnected ((fun x => (ρ : ℂ) * x) '' S) :=
    fun ρ S hS => hS.image _ (by fun_prop : Continuous _).continuousOn
  refine ⟨((fun t : ℝ => (t : ℂ) * g) '' Icc 0 (7 / 4) ∪ (fun x => ((7 / 4 : ℝ) : ℂ) * x) '' A)
      ∪ (fun t : ℝ => (t : ℂ) * -c) '' Icc (7 / 4) 2,
    (fun x => ((3 / 2 : ℝ) : ℂ) * x) '' B ∪ (fun t : ℝ => (t : ℂ) * c) '' Icc (3 / 2) 2,
    ((hrad g 0 (7 / 4)).union (((7 / 4 : ℝ) : ℂ) * g) (by exact ⟨7 / 4, ⟨by norm_num, le_refl _⟩, rfl⟩)
      (by exact ⟨g, hgA, rfl⟩)
      (hsc _ A hA)).union (((7 / 4 : ℝ) : ℂ) * -c) (by exact Or.inr ⟨-c, hcA, rfl⟩)
      (by exact ⟨7 / 4, ⟨le_refl _, by norm_num⟩, rfl⟩)
      (hrad _ _ _),
    (hsc _ B hB).union (((3 / 2 : ℝ) : ℂ) * c) (by exact ⟨c, hcB, rfl⟩)
      (by exact ⟨3 / 2, ⟨le_refl _, by norm_num⟩, rfl⟩) (hrad _ _ _),
    ?_, Or.inr ⟨2, ⟨by norm_num, le_refl _⟩, rfl⟩,
    Or.inl (Or.inl ⟨0, ⟨le_refl _, by norm_num⟩, by simp⟩), Or.inl ⟨ω, hωB, rfl⟩,
    Or.inr ⟨2, ⟨by norm_num, le_refl _⟩, rfl⟩, ?_, ?_⟩
  · rintro p (((⟨t, ht, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨t, ht, rfl⟩) | (⟨x, hx, rfl⟩ | ⟨t, ht, rfl⟩))
    · rw [l56_norm_ofReal_mul hg ht.1]; linarith [ht.2]
    · rw [l56_norm_ofReal_mul (hAx x hx).1 (by norm_num)]; norm_num
    · rw [l56_norm_ofReal_mul hnc (by linarith [ht.1])]; exact ht.2
    · rw [l56_norm_ofReal_mul (hBx x hx).1 (by norm_num)]; norm_num
    · rw [l56_norm_ofReal_mul hc (by linarith [ht.1])]; exact ht.2
  · have far : ∀ p : ℂ, 3 / 2 ≤ ‖p‖ → ∀ h : ℂ, ‖h‖ ≤ 1 → b ≤ ‖p - h‖ := fun p hp h hh =>
      le_trans (by linarith) (l56_nsep' (p := h) (q := p) (a := 1) (d := 1 / 2) hh (by linarith))
    rintro p (((⟨t, ht, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨t, ht, rfl⟩) | (⟨x, hx, rfl⟩ | ⟨t, ht, rfl⟩))
      h hh1 hh2 hre
    · have := l56_rad_hp_sep hg hgre ht.1 hh1 hre; linarith
    · exact far _ (by rw [l56_norm_ofReal_mul (hAx x hx).1 (by norm_num)]; norm_num) h hh2
    · exact far _ (by rw [l56_norm_ofReal_mul hnc (by linarith [ht.1])]; linarith [ht.1]) h hh2
    · exact far _ (by rw [l56_norm_ofReal_mul (hBx x hx).1 (by norm_num)]) h hh2
    · exact far _ (by rw [l56_norm_ofReal_mul hc (by linarith [ht.1])]; linarith [ht.1]) h hh2
  · rintro p ((((⟨t, ht, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨t, ht, rfl⟩)) | hp) q
      ((⟨y, hy, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs1, hs2, rfl⟩)
    -- the ray `[0, 7/4 g]`
    · have := l56_rad_sep hg (hBx y hy).1 ht.1 (S := 3 / 2) (by norm_num) (le_refl _)
      rw [norm_sub_rev g] at this; linarith [(hBx y hy).2]
    · have := l56_rad_sep hg hc ht.1 (S := 3 / 2) (by norm_num) hs.1
      linarith
    · have := l56_rad_sep hg hω ht.1 (S := 1) (by norm_num) hs1
      rw [norm_sub_rev g] at this; linarith
    -- the arc of radius `7/4`
    · exact le_trans (by linarith) (l56_nsep' (a := 3 / 2) (d := 1 / 4)
        (l56_norm_ofReal_mul (hBx y hy).1 (by norm_num)).le
        (by rw [l56_norm_ofReal_mul (hAx x hx).1 (by norm_num)]; norm_num))
    · have := l56_rad_sep hc (hAx x hx).1 (by linarith [hs.1] : (0 : ℝ) ≤ s) (S := 7 / 4)
        (by norm_num) (le_refl _)
      rw [norm_sub_rev c, norm_sub_rev ((s : ℂ) * c)] at this; linarith [(hAx x hx).2]
    · exact le_trans (by linarith) (l56_nsep' (a := 3 / 2) (d := 1 / 4)
        ((l56_norm_ofReal_mul hω (by linarith)).le.trans hs2)
        (by rw [l56_norm_ofReal_mul (hAx x hx).1 (by norm_num)]; norm_num))
    -- the ray `[−7/4 c, −2c]`
    · exact le_trans (by linarith) (l56_nsep' (a := 3 / 2) (d := 1 / 4)
        (l56_norm_ofReal_mul (hBx y hy).1 (by norm_num)).le
        (by rw [l56_norm_ofReal_mul hnc (by linarith [ht.1])]; linarith [ht.1]))
    · have := l56_rad_sep hnc hc (by linarith [ht.1] : (0 : ℝ) ≤ t) (S := 3 / 2) (by norm_num) hs.1
      rw [hcc] at this; linarith
    · exact le_trans (by linarith) (l56_nsep' (a := 3 / 2) (d := 1 / 4)
        ((l56_norm_ofReal_mul hω (by linarith)).le.trans hs2)
        (by rw [l56_norm_ofReal_mul hnc (by linarith [ht.1])]; linarith [ht.1]))
    -- `L₋`, of radius `≤ α`
    · exact le_trans hb1 (l56_nsep (a := α) hp
        (by rw [l56_norm_ofReal_mul (hBx y hy).1 (by norm_num)]; linarith))
    · exact le_trans hb1 (l56_nsep (a := α) hp
        (by rw [l56_norm_ofReal_mul hc (by linarith [hs.1])]; linarith [hs.1]))
    · exact le_trans hb1 (l56_nsep (a := α) hp
        (by rw [l56_norm_ofReal_mul hω (by linarith)]; linarith))

end LQGMetric.GM
