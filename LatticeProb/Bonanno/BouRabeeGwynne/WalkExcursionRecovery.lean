/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkExcursionRecovery at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82;
   only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkSegmentRestriction
import LatticeProb.Bonanno.BouRabeeGwynne.WeakExcursionRecovery

/-! Pasting actual discrete excursions recovers the original polygonal path
in the Fréchet quotient, including repeated clocks and zero total duration. -/

open scoped unitInterval

namespace BouRabeeGwynne

lemma exists_weakWalkTimeKnots {n M : ℕ} (P : TimePartition n)
    (times : Fin (n + 2) → ℕ) (hmono : Monotone times)
    (hfirst : times 0 = 0) (hlast : times (Fin.last (n + 1)) = M) :
    ∃ Q : WeakTimeKnots n, ∀ i, (M : ℝ) * (Q.knots i : ℝ) = (times i : ℝ) := by
  have hle (i : Fin (n + 2)) : times i ≤ M := (hmono (Fin.le_last i)).trans_eq hlast
  by_cases hzero : M = 0
  · let Q : WeakTimeKnots n :=
      ⟨P.knots, P.strictMono_knots.monotone, P.first, P.last⟩
    refine ⟨Q, ?_⟩
    intro i
    have hi : times i = 0 := Nat.eq_zero_of_le_zero (by simpa only [hzero] using hle i)
    simp only [hzero, hi, Nat.cast_zero, zero_mul]
  · have hpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hzero
    let knots : Fin (n + 2) → unitInterval := fun i =>
      ⟨(times i : ℝ) / (M : ℝ), div_nonneg (Nat.cast_nonneg _) hpos.le,
        (div_le_one hpos).mpr (by exact_mod_cast hle i)⟩
    have hm : Monotone knots := by
      intro i j hij
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmono hij) hpos.le
    have hf : knots 0 = 0 := by
      apply Subtype.ext
      simp only [knots, hfirst, Nat.cast_zero, zero_div, Set.Icc.coe_zero]
    have hl : knots (Fin.last (n + 1)) = 1 := by
      apply Subtype.ext
      simp only [knots, hlast, div_self hpos.ne', Set.Icc.coe_one]
    refine ⟨⟨knots, hm, hf, hl⟩, ?_⟩
    intro i
    change (M : ℝ) * ((times i : ℝ) / (M : ℝ)) = (times i : ℝ)
    rw [mul_comm, div_mul_cancel₀ _ hpos.ne']

lemma clockedWalkSegments_eq_restrictChain {n d M : ℕ} {V : Type*}
    (Q : WeakTimeKnots n) (pos : V → Euc d) (ω : ℕ → V)
    (times : Fin (n + 2) → ℕ) (hmono : Monotone times)
    (hlast : times (Fin.last (n + 1)) = M)
    (hQ : ∀ i, (M : ℝ) * (Q.knots i : ℝ) = (times i : ℝ))
    (c : ExcursionChain n d)
    (hpieces : ∀ i, c.val i = ClockedWalkExcursion.curve
      (FiniteConductanceNetwork.clockedWalkSegment pos ω (times i.castSucc) (times i.succ))) :
    c = Q.restrictChain (polygonalCurve pos ω M) := by
    apply Subtype.ext
    funext i
    apply ContinuousMap.ext
    intro u
    change c.val i u = polygonalCurve pos ω M (Q.intervalParam i u)
    rw [hpieces i]
    have hab := hmono i.castSucc_lt_succ.le
    have hbM : times i.succ ≤ M := (hmono (Fin.le_last i.succ)).trans_eq hlast
    apply clockedWalkSegment_curve_of_scaled_time pos ω hab hbM
    change (M : ℝ) * ((Q.knots i.castSucc : ℝ) + (u : ℝ) *
      ((Q.knots i.succ : ℝ) - (Q.knots i.castSucc : ℝ))) = _
    calc
      _ = (M : ℝ) * (Q.knots i.castSucc : ℝ) +
          ((M : ℝ) * (Q.knots i.succ : ℝ) - (M : ℝ) * (Q.knots i.castSucc : ℝ)) *
            (u : ℝ) := by ring
      _ = _ := by simp only [hQ, Nat.cast_sub hab]
theorem project_concatenate_clockedWalkSegments {n d M : ℕ} {V : Type*}
    (P : TimePartition n) (pos : V → Euc d) (ω : ℕ → V)
    (times : Fin (n + 2) → ℕ) (hmono : Monotone times)
    (hfirst : times 0 = 0) (hlast : times (Fin.last (n + 1)) = M)
    (c : ExcursionChain n d)
    (hpieces : ∀ i, c.val i = ClockedWalkExcursion.curve
      (FiniteConductanceNetwork.clockedWalkSegment pos ω (times i.castSucc) (times i.succ))) :
    CurveSpace.project (P.concatenate c) = CurveSpace.project (polygonalCurve pos ω M) := by
  obtain ⟨Q, hQ⟩ := exists_weakWalkTimeKnots P times hmono hfirst hlast
  rw [clockedWalkSegments_eq_restrictChain Q pos ω times hmono hlast hQ c hpieces]
  exact Q.project_concatenate_restrictChain P (polygonalCurve pos ω M)

end BouRabeeGwynne
