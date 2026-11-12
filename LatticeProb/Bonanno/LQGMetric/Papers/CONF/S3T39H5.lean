/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39H5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39H3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4B
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L214Sep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9: the a.s. facts used by Lemma 3.7 A

The premises of property A of `CONFLem3_7AtAE0` (S3T39H2) that hold a.s. for a weak LQG metric:
geodesics from `𝕫` to every point (GM.S1.1, `gm_S1_1`, GM l. 647) in the length parametrization
`IsGeodesicL`, and bounded `D_h`-balls (bounded compactness, `gm_S1_1_bcpt`, DFGPS Lemma 3.8).

* `t39h_geodL_of_geod01`: a constant-speed geodesic on `[0,1]` gives one on `[0, D(z,w)]`;
* **`t39h_good_ae`**: the `hgood` input of `t39h_iterData_of` (S3T39H4) minus the `τ`-facts;
* `t39h_tauR_pos`: `τ_𝕣 > 0` surely (`D` is continuous and small `D`-balls are small, own
  elementary proof);
* `t39h_disconnectsIn_trivial`: the conclusion form of `confL214` (`DisconnectsIn U X {0}` with only a
  diameter bound on `X`) is satisfied by a small circle around `0`, so `confL214` cannot give
  CONF's Lemma 2.15 (`lem-disconnect-set-infty`, C:912–924) by inversion (report, statement issue).
-/

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

/-- reparametrize an `IsGeod01` geodesic by length -/
theorem t39h_geodL_of_geod01 {D : ContMetric} {z w : ℂ} {η : C(unitInterval, ℂ)}
    (hη : IsGeod01 D z w η) : ∃ (Q : ℝ → ℂ) (L : ℝ), IsGeodesicL D Q L z w := by
  set L := D.1 (z, w) with hL
  have hL0 : 0 ≤ L := @dist_nonneg D.Space _ z w
  rcases hL0.lt_or_eq with hpos | h0
  · refine ⟨fun t => η (Set.projIcc 0 1 zero_le_one (t / L)), L, hL0, ?_, ?_, ?_⟩
    · simp only [zero_div]
      rw [show Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) from
        Set.projIcc_left _]
      exact hη.1
    · simp only [div_self hpos.ne']
      rw [show Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) from
        Set.projIcc_right _]
      exact hη.2.1
    · intro a ha b hb
      rw [hη.2.2]
      have hpa : ((Set.projIcc (0 : ℝ) 1 zero_le_one (a / L) : unitInterval) : ℝ) = a / L :=
        by rw [Set.projIcc_of_mem]; exact ⟨div_nonneg ha.1 hL0, (div_le_one hpos).2 ha.2⟩
      have hpb : ((Set.projIcc (0 : ℝ) 1 zero_le_one (b / L) : unitInterval) : ℝ) = b / L :=
        by rw [Set.projIcc_of_mem]; exact ⟨div_nonneg hb.1 hL0, (div_le_one hpos).2 hb.2⟩
      rw [hpa, hpb, ← sub_div, abs_div, abs_of_pos hpos, div_mul_cancel₀ _ hpos.ne']
  · have hzw : z = w := D.2.eq_of_eq_zero z w h0.symm
    refine ⟨fun _ => z, 0, le_rfl, rfl, hzw, fun a ha b hb => ?_⟩
    have ha0 : a = 0 := le_antisymm ha.2 ha.1
    have hb0 : b = 0 := le_antisymm hb.2 hb.1
    rw [ha0, hb0, sub_zero, abs_zero]
    exact D.2.self_eq_zero z

/-- **a.s. geodesics from `𝕫` to every point and bounded balls** (GM.S1.1, DFGPS Lemma 3.8) -/
theorem t39h_good_ae (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) :
    ∀ᵐ ω ∂P, (∀ w, ∃ (Q : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) Q L z₀ w) ∧
      ∀ s' : ℝ, Bornology.IsBounded (ballM (D (h ω)) z₀ s') := by
  filter_upwards [gm_S1_1 h38 hγ hγ2 hD P h hh, gm_S1_1_bcpt h38 hγ hγ2 hD P h hh] with ω hg hc
  exact ⟨fun w => by obtain ⟨η, hη⟩ := hg z₀ w; exact t39h_geodL_of_geod01 hη,
    fun s' => isBounded_ballM_of_bc hc z₀ s'⟩

/-- `τ_𝕣 > 0` for every continuous metric (own elementary proof) -/
theorem t39h_tauR_pos {Ω : Type} (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) {R : ℝ}
    (hR : 0 < R) (ω : Ω) : 0 < tauR D h z₀ R ω := by
  obtain ⟨δ, hδ, hδε⟩ := (D (h ω)).2.euclidean_of_small z₀ (R / 2) (by linarith)
  have hsmall : ∀ s, s ≤ δ → filledBall (D (h ω)) z₀ s ⊆ ball z₀ R := fun s hs => by
    have h1 : closure (ballM (D (h ω)) z₀ s) ⊆ closedBall z₀ (R / 2) :=
      closure_minimal (fun y (hy : (D (h ω)).1 (z₀, y) < s) => by
        rw [mem_closedBall, dist_comm, dist_eq_norm]
        exact (hδε y (hy.trans_le hs)).le) isClosed_closedBall
    exact (gm_filledBall_subset_closedBall h1).trans (closedBall_subset_ball (by linarith))
  -- the defining set is nonempty
  set u : ℂ := z₀ + (R : ℂ)
  have hu : u ∉ ball z₀ R := by
    rw [mem_ball, dist_eq_norm, show u - z₀ = (R : ℂ) by simp [u], Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
    exact lt_irrefl R
  have hne : ({s | 0 < s ∧ ¬ filledBall (D (h ω)) z₀ s ⊆ ball z₀ R} : Set ℝ).Nonempty := by
    have h0 : 0 ≤ (D (h ω)).1 (z₀, u) := @dist_nonneg (D (h ω)).Space _ z₀ u
    refine ⟨(D (h ω)).1 (z₀, u) + 1, by linarith,
      fun hsub => hu (hsub ?_)⟩
    exact Or.inl (subset_closure (show (D (h ω)).1 (z₀, u) < (D (h ω)).1 (z₀, u) + 1 by linarith))
  refine lt_of_lt_of_le hδ (le_csInf hne fun s hs => ?_)
  by_contra hlt
  exact hs.2 (hsmall s (not_le.1 hlt).le)

/-- **the a.s. inputs of Theorem 3.9** for `τ ∈ [τ_𝕣, τ_{2𝕣}]` a.s.: `τ > 0`, `τ ≥ τ_𝕣`,
geodesics from `𝕫`, bounded balls (the `hgood` input of `t39h_iterData_of`, and the first
conjunct of `CONFThm3_9Iter`'s conclusion) -/
theorem t39h_tau_ae (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) {R : ℝ} (hR : 0 < R) (τ : Ω → ℝ)
    (hτI : ∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ R ω) (tauR D h z₀ (2 * R) ω)) :
    ∀ᵐ ω ∂P, 0 < τ ω ∧ tauR D h z₀ R ω ≤ τ ω ∧
      (∀ w, ∃ (Q : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) Q L z₀ w) ∧
      ∀ s' : ℝ, Bornology.IsBounded (ballM (D (h ω)) z₀ s') := by
  filter_upwards [hτI, t39h_good_ae h38 hγ hγ2 hD P h hh z₀] with ω h1 h2
  exact ⟨(t39h_tauR_pos D h z₀ hR ω).trans_le h1.1, h1.1, h2⟩

end CONF
end LQGMetric
