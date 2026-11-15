/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ClockedWalkStopping at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkConcatenation

/-! Stop reconstructed spatial vertex sequences at their actual first vertex
outside the domain. Measurability uses the domain's measurable complement. -/

open MeasureTheory ProbabilityTheory Set

namespace BouRabeeGwynne

namespace FiniteConductanceNetwork

lemma exitTime_congr_prefix_of_le {V : Type*} (A : Set V) {ω ξ : ℕ → V} {M : ℕ}
    (hp : ∀ k ≤ M, ξ k = ω k) (hω : exitTime A ω ≤ (M : WithTop ℕ)) :
    exitTime A ξ = exitTime A ω := by
  have hξ : exitTime A ξ ≤ (M : WithTop ℕ) := by
    obtain ⟨k, hk, hout⟩ := (exitTime_le_iff A ω M).mp hω
    exact (exitTime_le_iff A ξ M).mpr ⟨k, hk, by simpa only [hp k hk] using hout⟩
  apply WithTop.eq_of_forall_le_coe_iff
  intro n
  by_cases hn : n ≤ M
  · constructor
    · intro h
      obtain ⟨k, hk, hout⟩ := (exitTime_le_iff A ξ n).mp h
      exact (exitTime_le_iff A ω n).mpr
        ⟨k, hk, by simpa only [hp k (hk.trans hn)] using hout⟩
    · intro h
      obtain ⟨k, hk, hout⟩ := (exitTime_le_iff A ω n).mp h
      exact (exitTime_le_iff A ξ n).mpr
        ⟨k, hk, by simpa only [hp k (hk.trans hn)] using hout⟩
  · have hMn : (M : WithTop ℕ) ≤ n := WithTop.coe_le_coe.mpr (lt_of_not_ge hn).le
    exact iff_of_true (hξ.trans hMn) (hω.trans hMn)

lemma exitTime_map {V X : Type*} (f : V → X) (A : Set X) (ω : ℕ → V) :
    exitTime A (fun k => f (ω k)) = exitTime (f ⁻¹' A) ω := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro n
  exact (exitTime_le_iff A (fun k => f (ω k)) n).trans
    (exitTime_le_iff (f ⁻¹' A) ω n).symm

end FiniteConductanceNetwork

namespace ClockedWalkExcursion

variable {d : ℕ}

noncomputable def vertexStoppedCurve (U : Set (Euc d)) (e : ClockedWalkExcursion d) :
    CurveSpace d := stoppedPolygonalCurve id U e.2

lemma measurable_vertexStoppedCurve {U : Set (Euc d)} (hU : MeasurableSet U) :
    Measurable (vertexStoppedCurve U) := by
  have hτ : Measurable (FiniteConductanceNetwork.exitTime U) :=
    (FiniteConductanceNetwork.coordinateProcess_adapted.isStoppingTime_hittingAfter hU.compl).measurable'
  have hd : Measurable (fun e : ClockedWalkExcursion d =>
      (FiniteConductanceNetwork.exitTime U e.2).untopD 0) :=
    (hτ.comp measurable_snd).untopD 0
  exact CurveSpace.continuous_project.measurable.comp
    (measurable_curve.comp (hd.prodMk measurable_snd))

theorem vertexStoppedCurve_clockedWalkSegment {V : Type*} (pos : V → Euc d)
    (U : Set (Euc d)) (ω : ℕ → V) {M : ℕ}
    (hτ : FiniteConductanceNetwork.exitTime (pos ⁻¹' U) ω ≤ (M : WithTop ℕ)) :
    vertexStoppedCurve U (FiniteConductanceNetwork.clockedWalkSegment pos ω 0 M) =
      stoppedPolygonalCurve pos (pos ⁻¹' U) ω := by
  have he : FiniteConductanceNetwork.exitTime U
      (FiniteConductanceNetwork.clockedWalkSegment pos ω 0 M).2 =
      FiniteConductanceNetwork.exitTime (pos ⁻¹' U) ω := by
    rw [← FiniteConductanceNetwork.exitTime_map pos U ω]
    apply FiniteConductanceNetwork.exitTime_congr_prefix_of_le U (M := M)
    · intro k hk
      change pos (ω (0 + min k (M - 0))) = pos (ω k)
      simp only [Nat.sub_zero, Nat.zero_add, min_eq_left hk]
    · simpa only [FiniteConductanceNetwork.exitTime_map] using hτ
  have hfin : FiniteConductanceNetwork.exitTime (pos ⁻¹' U) ω ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hτ
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hmM : m ≤ M := WithTop.coe_le_coe.mp (hm.trans_le hτ)
  unfold vertexStoppedCurve stoppedPolygonalCurve
  rw [he, ← hm, WithTop.untopD_coe]
  apply congrArg CurveSpace.project
  change polygonalCurve id (fun k => pos (ω (0 + min k (M - 0)))) m = polygonalCurve pos ω m
  calc
    _ = polygonalCurve id (fun k => pos (ω k)) m := by
      apply polygonalCurve_congr_prefix
      intro k hk
      simp only [Nat.sub_zero, Nat.zero_add, min_eq_left (hk.trans hmM)]
    _ = _ := rfl

end ClockedWalkExcursion
end BouRabeeGwynne
