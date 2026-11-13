import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RItinerary

/-!
# A cell of a template walk near every point of the circle

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* (arXiv:1807.07511), Proposition 3.6 (the walk
follows a similarity-rotated polar template around the circle), used as in Berestycki–Gwynne, *Random walks on
mated-CRT maps and Liouville Brownian motion* (arXiv:2003.10320), proof of Lemma 3.9.

An `IsTemplateWalk H z r ϑ n v α β` is a walk of cells following the moved polar template of the circle
`∂B_r(z)` up to `r / 60`. The template passes, at every angle, through the annulus `0.9 r ≤ |· − z| ≤ 1.1 r`, so
some cell of the walk lies within `r / 6` of every point `w` with `|‖w − z‖ − r| ≤ r / 50`.

Main results:
* `exists_mem_Icc_of_isTemplateWalk`: the template intervals `[α j, β j]` cover `[0, 1]`.
* `exists_polarAngle_eq`: the polar angle takes every value of `[0, 2π + 1/10]` on `[2, 4]`.
* `exists_cell_subset_ball_of_isTemplateWalk`: some cell `H.cell (v j)`, `j ≤ n`, lies in `B_{r/6}(w)`.
-/

set_option autoImplicit false

noncomputable section

open Set Real
open MatedCRTHarmonic MatedCRTHarmonic.RouteM MatedCRTHarmonic.Topology

namespace LatticeProb.LQG

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-- The template intervals `[α j, β j]`, `j ≤ n`, of a template walk cover `[0, 1]`. -/
theorem exists_mem_Icc_of_isTemplateWalk {H : CellularEmbedding G o} {z : ℂ} {r ϑ : ℝ} {n : ℕ}
    {v : ℕ → V} {α β : ℕ → ℝ} (hW : IsTemplateWalk H z r ϑ n v α β) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : ∃ j ≤ n, s ∈ Icc (α j) (β j) := by
  classical
  have hex : ∃ j, s ≤ β j := ⟨n, by rw [hW.β_last]; exact hs1⟩
  have hjn : Nat.find hex ≤ n := Nat.find_min' hex (by rw [hW.β_last]; exact hs1)
  refine ⟨Nat.find hex, hjn, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, hW.α_zero]
    exact hs0
  · obtain ⟨j', hj'⟩ : ∃ j', Nat.find hex = j' + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : ¬ s ≤ β j' := Nat.find_min hex (by omega)
    have hov := hW.overlap j' (by omega)
    rw [hj']
    linarith [not_le.mp hlt]

/-- The polar angle of the template runs continuously from `0` to `2π + 1/10` on `[2, 4]`. -/
theorem exists_polarAngle_eq {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ 2 * π + 1 / 10) :
    ∃ u ∈ Icc (2 : ℝ) 4, polarAngle u = φ := by
  have hcont : Continuous polarAngle := by
    unfold polarAngle
    fun_prop
  have h2 : polarAngle 2 = 0 := polarAngle_eq_zero_on_radial le_rfl
  have h4 : polarAngle 4 = 2 * π + 1 / 10 := by
    have e1 : max ((4 : ℝ) - 2) 0 = 2 := by norm_num
    have e2 : max ((4 : ℝ) - 3) 0 = 1 := by norm_num
    unfold polarAngle
    rw [e1, e2]
    ring
  have hmem : φ ∈ Icc (polarAngle 2) (polarAngle 4) := by
    rw [h2, h4]
    exact ⟨h0, h1⟩
  obtain ⟨u, hu, hu'⟩ := intermediate_value_Icc (show (2 : ℝ) ≤ 4 by norm_num)
    hcont.continuousOn hmem
  exact ⟨u, hu, hu'⟩

/-- **A cell near every point of the circle.** A template walk around `∂B_r(z)` visits, for every point `w`
with `|‖w − z‖ − r| ≤ r / 50`, a cell contained in `B_{r/6}(w)`. -/
theorem exists_cell_subset_ball_of_isTemplateWalk {H : CellularEmbedding G o} {z : ℂ} {r ϑ : ℝ}
    {n : ℕ} {v : ℕ → V} {α β : ℕ → ℝ} (hW : IsTemplateWalk H z r ϑ n v α β) (hr : 0 < r) {w : ℂ}
    (hw : |‖w - z‖ - r| ≤ r / 50) : ∃ j ≤ n, H.cell (v j) ⊆ Metric.ball w (r / 6) := by
  have hρ : r - r / 50 ≤ ‖w - z‖ := by linarith [(abs_le.mp hw).1]
  -- an angle in `[0, 2π)` congruent to `arg (w - z) - ϑ`
  set θ : ℝ := Complex.arg (w - z) - ϑ with hθ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, toIcoMod Real.two_pi_pos 0 θ = θ - k * (2 * π) :=
    ⟨toIcoDiv Real.two_pi_pos 0 θ, by rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]⟩
  have hmem := toIcoMod_mem_Ico Real.two_pi_pos 0 θ
  set φ : ℝ := toIcoMod Real.two_pi_pos 0 θ with hφ
  have hφ0 : 0 ≤ φ := hmem.1
  have hφ1 : φ < 2 * π := by simpa using hmem.2
  obtain ⟨u, hu, huφ⟩ := exists_polarAngle_eq hφ0 (by linarith [Real.pi_pos])
  have hs0 : 0 ≤ u / 4 := by linarith [hu.1]
  have hs1 : u / 4 ≤ 1 := by linarith [hu.2]
  obtain ⟨j, hjn, hjs⟩ := exists_mem_Icc_of_isTemplateWalk hW hs0 hs1
  refine ⟨j, hjn, fun x hx => ?_⟩
  have hnear := hW.near j hjn (u / 4) hjs x hx
  -- the template point
  have hR := polarRadius_bounds (show 0 ≤ u by linarith [hu.1]) hu.2
  have hq : CellularEmbedding.movedTemplate z r ϑ (u / 4) =
      z + r * Complex.exp (ϑ * Complex.I) *
        (polarRadius u * Complex.exp (φ * Complex.I)) := by
    have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one (u / 4) = ⟨u / 4, ⟨hs0, hs1⟩⟩ :=
      Set.projIcc_of_mem _ ⟨hs0, hs1⟩
    have h4 : 4 * (u / 4) = u := by ring
    unfold CellularEmbedding.movedTemplate
    rw [hproj]
    simp only [polarTemplate, ContinuousMap.coe_mk, h4, huφ]
  have hexp : Complex.exp (ϑ * Complex.I) * Complex.exp (φ * Complex.I) =
      Complex.exp (Complex.arg (w - z) * Complex.I) := by
    have hsum : ((ϑ + φ : ℝ) : ℂ) * Complex.I =
        (Complex.arg (w - z) : ℂ) * Complex.I - (k : ℂ) * (2 * π * Complex.I) := by
      have hϑφ : ϑ + φ = Complex.arg (w - z) - k * (2 * π) := by
        rw [hk, hθ]
        ring
      rw [hϑφ]
      push_cast
      ring
    rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, hsum, Complex.exp_sub,
      Complex.exp_int_mul_two_pi_mul_I, div_one]
  have hwz : w - z = (‖w - z‖ : ℂ) * Complex.exp (Complex.arg (w - z) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I (w - z)).symm
  have hdiff : CellularEmbedding.movedTemplate z r ϑ (u / 4) - w =
      ((r * polarRadius u - ‖w - z‖ : ℝ) : ℂ) *
        Complex.exp (Complex.arg (w - z) * Complex.I) := by
    rw [hq, ← hexp]
    have : w = z + (w - z) := by ring
    conv_lhs => rw [this, hwz, ← hexp]
    push_cast
    ring
  have hnorm : ‖CellularEmbedding.movedTemplate z r ϑ (u / 4) - w‖ ≤ r / 10 + r / 50 := by
    rw [hdiff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    have := abs_le.mp hw
    constructor <;> nlinarith [hR.1, hR.2]
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖x - w‖ = ‖(x - CellularEmbedding.movedTemplate z r ϑ (u / 4)) +
          (CellularEmbedding.movedTemplate z r ϑ (u / 4) - w)‖ := by ring_nf
    _ ≤ ‖x - CellularEmbedding.movedTemplate z r ϑ (u / 4)‖ +
          ‖CellularEmbedding.movedTemplate z r ϑ (u / 4) - w‖ := norm_add_le _ _
    _ < r / 6 := by linarith

end LatticeProb.LQG
