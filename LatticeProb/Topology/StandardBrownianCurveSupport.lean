import LatticeProb.Prob.BrownianOpenExitFinite
import LatticeProb.Topology.ScalarBrownianCurveLaw

/-! # Unbounded support of standard Brownian path laws -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open LatticeProb.UnboundedRayIntervalIntegrand

namespace BouRabeeGwynne

/-- A standard Brownian path in positive dimension has unbounded range almost surely. -/
theorem ae_unbounded_range_standardBrownian {d : ℕ} (hd : 0 < d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    ∀ᵐ (f : BrownianPath d) ∂μ, ¬ Bornology.IsBounded (Set.range f) := by
  let i : Fin d := ⟨0, hd⟩
  have hcoord : ∀ᵐ (f : BrownianPath d) ∂μ, ∀ n : ℕ,
      ¬ ∀ m : ℕ, |f (((m : ℝ≥0) + 1) ^ 2) i| ≤ (n : ℝ) :=
    ae_all_iff.mpr (fun n => LatticeProb.preBrownian_ae_not_bounded_square_times
      (hμ.2.1 i).toIsPreBrownianReal (Nat.cast_nonneg n))
  filter_upwards [hcoord] with f hf hbounded
  obtain ⟨R, _, hR⟩ := hbounded.exists_pos_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt R
  apply hf n
  intro m
  calc
    |f (((m : ℝ≥0) + 1) ^ 2) i| ≤ ‖f (((m : ℝ≥0) + 1) ^ 2)‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le _ _
    _ ≤ R := hR _ ⟨_, rfl⟩
    _ ≤ (n : ℝ) := le_of_lt hn

end BouRabeeGwynne

namespace LatticeProb.UnboundedRayCurveSpace

/-- A positive scalar image of standard planar Brownian motion has the same local curve law. -/
theorem curveLaw_scalarBrownian_of_positive
    (target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget)
    {s : ℝ≥0} (hs : 0 < s) (hfac : target.factor = (s : ℝ) • 1) :
    ∃ hν : ∀ᵐ (f : Path 2) ∂(target.pathLaw : Measure (Path 2)),
      ¬ Bornology.IsBounded (Set.range f),
      curveLaw (target.pathLaw : Measure (Path 2)) hν =
        curveLaw (target.standardLaw : Measure (Path 2))
          (BouRabeeGwynne.ae_unbounded_range_standardBrownian (by decide) target.isStandard) :=
  curveLaw_scalarBrownian target hs hfac
    (BouRabeeGwynne.ae_unbounded_range_standardBrownian (by decide) target.isStandard)

end LatticeProb.UnboundedRayCurveSpace
