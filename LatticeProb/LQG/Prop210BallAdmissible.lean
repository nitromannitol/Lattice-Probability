import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsAProp210
import LatticeProb.Analysis.AnnulusThickeningVolume

/-!
# [18] Proposition 2.10 on a Euclidean ball with the test function one

Gwynne, Miller and Sheffield ([18] = GMS19, *The Tutte embedding of the mated-CRT map converges to Liouville quantum
gravity*, Proposition 2.10) bound the localized integral `∫_D f u^ε` of the cell density
`u^ε = ∑_x deg(x) diam(H_x)² / area(H_x) 1_{H_x}` of the mated-CRT map by `A ∫_D f + ε^α`, with polynomially high
probability, uniformly over the admissible pairs `(D, f)`. This file specializes it to a Euclidean ball `D = B_s(z)`
inside `B_ρ(0)` and the test function `f = 1`.

## Main results

* `MatedCRTHarmonic.GMS4.prop210BallConst`: the threshold `8 π` on the test constant `C`.
* `MatedCRTHarmonic.GMS4.prop210Admissible_ball_one`: for `C > 8 π`, the pair `(B_s(z), 1)` is admissible at
  `(ε, ρ, C, β)` whenever `B_s(z) ⊆ B_ρ(0)`. The boundary regularity `area(B_r(∂B_s(z))) ≤ 4 π r (s + r) ≤ 8 π r`
  (`r < 1`, `s ≤ ρ < 1`) comes from `LatticeProb.volume_thickening_sphere_le`.
* `MatedCRTHarmonic.GMSMain.lintegral_uDens_ball_le_of_not_mem_epsAProp210Bad`: off the failure event
  `EpsAProp210Bad` at `(B_s(z), 1)`, the curve cells form a cellular embedding of the mated-CRT map, and every such
  embedding satisfies `∫⁻_{B_s(z)} u^ε ≤ A area(B_s(z)) + tol`.
* `MatedCRTHarmonic.GMSMain.exists_epsAProp210Bad_ball_one_le`: from `EpsAProp210At P bm η ρ C` with `C > 8 π`, the
  failure probability at `(B_s(z), 1)` is at most `Cfail ε^α`, uniformly over the balls `B_s(z) ⊆ B_ρ(0)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

/-- **The threshold on the test constant for balls**: `8 π`. A ball `B_s(z) ⊆ B_ρ(0)` with `ρ < 1` has
`area(B_r(∂B_s(z))) ≤ 4 π r (s + r) ≤ 8 π r` for `r ∈ (0, 1)`. -/
def prop210BallConst : ℝ := 8 * Real.pi

theorem one_lt_prop210BallConst : 1 < prop210BallConst := by
  unfold prop210BallConst
  linarith [Real.two_le_pi]

/-- A ball `B_s(z)` contained in `B_ρ(0) ⊆ ℂ` has radius `s ≤ ρ`: the points `z ± ρ` are at distance `2 ρ`. -/
theorem radius_le_of_ball_subset_ball_zero {z : ℂ} {s ρ : ℝ} (hρ : 0 < ρ)
    (hsub : ball z s ⊆ ball (0 : ℂ) ρ) : s ≤ ρ := by
  refine not_lt.1 fun h => ?_
  have hρn : ‖(ρ : ℂ)‖ = ρ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hρ.le]
  have h1 : z + (ρ : ℂ) ∈ ball (0 : ℂ) ρ := hsub (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hρn]
    exact h)
  have h2 : z - (ρ : ℂ) ∈ ball (0 : ℂ) ρ := hsub (by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, hρn]
    exact h)
  rw [mem_ball_zero_iff] at h1 h2
  have h3 : ‖(z + (ρ : ℂ)) - (z - (ρ : ℂ))‖ ≤ ‖z + (ρ : ℂ)‖ + ‖z - (ρ : ℂ)‖ := norm_sub_le _ _
  have h4 : (z + (ρ : ℂ)) - (z - (ρ : ℂ)) = ((2 * ρ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h4, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h3
  linarith

/-- **Boundary regularity of a ball** in the form of `Prop210Admissible`: if `0 < s ≤ ρ < 1` and
`C ≥ 8 π`, then `area(B_r(∂B_s(z))) ≤ C r` for every `r ∈ (0, 1)`. -/
theorem volume_thickening_frontier_ball_le {z : ℂ} {s ρ C : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) (hsρ : s ≤ ρ)
    (hC : prop210BallConst ≤ C) :
    ∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier (ball z s))) ≤ ENNReal.ofReal (C * r) := by
  intro r hr
  rw [frontier_ball z hs.ne']
  refine (LatticeProb.volume_thickening_sphere_le z hs.le hr.1).trans (ENNReal.ofReal_le_ofReal ?_)
  have hpi := Real.pi_pos
  have h4 : 0 ≤ 4 * Real.pi * r := mul_nonneg (mul_nonneg (by norm_num) hpi.le) hr.1.le
  have h1 : 4 * Real.pi * r * (s + r) ≤ 4 * Real.pi * r * 2 :=
    mul_le_mul_of_nonneg_left (by linarith [hr.2]) h4
  have h2 : 8 * Real.pi * r ≤ C * r := mul_le_mul_of_nonneg_right hC hr.1.le
  linarith

/-- **The pair `(B_s(z), 1)` is admissible for [18] Proposition 2.10**: for `ε, ρ ∈ (0, 1)`, `β > 0`, `s > 0`,
`B_s(z) ⊆ B_ρ(0)` and a test constant `C > 8 π`, the ball is open, connected, inside `B_ρ(0)`, its boundary has
`area(B_r(∂B_s(z))) ≤ C r` for `r ∈ (0, 1)`, and the constant function `1` satisfies `0 ≤ 1 ≤ C ε^{-β}` and is
`C ε^{-β}`-Lipschitz. -/
theorem prop210Admissible_ball_one {ε ρ C β s : ℝ} {z : ℂ} (hε0 : 0 < ε) (hε1 : ε < 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hβ : 0 < β) (hs : 0 < s) (hsub : ball z s ⊆ ball 0 ρ) (hC : prop210BallConst < C) :
    Prop210Admissible ε ρ C β (ball z s) (fun _ => 1) := by
  have hC1 : 1 < C := one_lt_prop210BallConst.trans hC
  have hrpow : 1 ≤ ε ^ (-β) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1.le (by linarith)
  have hCe : 1 ≤ C * ε ^ (-β) := by nlinarith
  refine ⟨hε0, hε1, hρ0, hρ1, hC1, hβ, isOpen_ball, (convex_ball z s).isConnected (nonempty_ball.2 hs), hsub,
    volume_thickening_frontier_ball_le hs hρ1 (radius_le_of_ball_subset_ball_zero hρ0 hsub) hC.le,
    fun _ _ => ⟨zero_le_one, hCe⟩, fun _ _ _ _ => ?_⟩
  rw [sub_self, abs_zero]
  exact mul_nonneg (by linarith) dist_nonneg

end MatedCRTHarmonic.GMS4

namespace MatedCRTHarmonic.GMSMain

/-- **G3's Proposition 2.10 bound with the test function one** is the localized integral bound
`∫⁻_D u^ε ≤ A area(D) + tol`. -/
theorem prop210Bound_one_iff {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)
    (D : Set ℂ) (A tol : ℝ) :
    GMS3.Prop210Bound H D (fun _ => 1) A tol ↔
      ∫⁻ w in D, GMS3.uDens H w ≤ ENNReal.ofReal A * volume D + ENNReal.ofReal tol := by
  unfold GMS3.Prop210Bound
  simp only [ENNReal.ofReal_one, one_mul, lintegral_one, Measure.restrict_apply_univ]

/-- **The good event of [18] Proposition 2.10 at `(B_s(z), 1)`, unfolded**: off `EpsAProp210Bad` at the ball
`B_s(z)` with the test function one, the mated-CRT map at mesh `ε` is locally finite and the curve cells
`η([ε(x−1), εx])` form a cellular embedding of it rooted at `0`, and every such embedding `H` satisfies
`∫⁻_{B_s(z)} u^ε ≤ A area(B_s(z)) + tol`. -/
theorem lintegral_uDens_ball_le_of_not_mem_epsAProp210Bad {Ω : Type*} {bm : Ω → MatedCRT.Path2}
    {η : Ω → C(ℝ, ℂ)} {ε A tol s : ℝ} {z : ℂ} {ω : Ω}
    (hω : ω ∉ EpsAProp210Bad bm η ε (ball z s) (fun _ => 1) A tol) :
    (∃ (hlf : MatedCRT.IsLocallyFinite ε (bm ω)) (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        ∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
      ∀ (hlf : MatedCRT.IsLocallyFinite ε (bm ω)) (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        (∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) →
          ∫⁻ w in ball z s, GMS3.uDens H w ≤ ENNReal.ofReal A * volume (ball z s) + ENNReal.ofReal tol := by
  have h : (∃ (hlf : MatedCRT.IsLocallyFinite ε (bm ω))
        (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        ∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
      ∀ (hlf : MatedCRT.IsLocallyFinite ε (bm ω)) (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        (∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) →
          GMS3.Prop210Bound H (ball z s) (fun _ => 1) A tol := by
    by_contra hc
    exact hω hc
  exact ⟨h.1, fun hlf H hH => (prop210Bound_one_iff H (ball z s) A tol).1 (h.2 hlf H hH)⟩

/-- **[18] Proposition 2.10 on balls with the test function one**: from one fixed-parameter instance
`EpsAProp210At P bm η ρ C` with `ρ ∈ (0, 1)` and `C > 8 π`, there are `β, α > 0` and `A, Cfail ≥ 0` such that for
every `ε ∈ (0, 1)` and every ball `B_s(z) ⊆ B_ρ(0)` with `s > 0`, the failure event at `(B_s(z), 1)` with
tolerance `ε^α` has outer probability at most `Cfail ε^α`. -/
theorem exists_epsAProp210Bad_ball_one_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {bm : Ω → MatedCRT.Path2} {η : Ω → C(ℝ, ℂ)} {ρ C : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hC : GMS4.prop210BallConst < C) (h : EpsAProp210At P bm η ρ C) :
    ∃ β A α Cfail : ℝ, 0 < β ∧ 0 < α ∧ 0 ≤ A ∧ 0 ≤ Cfail ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (z : ℂ) (s : ℝ), 0 < s → ball z s ⊆ ball 0 ρ →
        P (EpsAProp210Bad bm η ε (ball z s) (fun _ => 1) A (ε ^ α)) ≤ ENNReal.ofReal (Cfail * ε ^ α) := by
  obtain ⟨β, A, α, Cfail, hβ, hα, hA, hCfail, hbound⟩ := h
  exact ⟨β, A, α, Cfail, hβ, hα, hA, hCfail, fun ε hε z s hs hsub =>
    hbound ε hε _ _ (GMS4.prop210Admissible_ball_one hε.1 hε.2 hρ0 hρ1 hβ hs hsub hC)⟩

end MatedCRTHarmonic.GMSMain
