import LatticeProb.Prob.Percolation.DeterministicIntegerSlope

/-!
# A realized deterministic subgroup after a nonempty bond flip

The producer supplies an actual configuration in the simultaneous event. A genuine constant
source plane proves zero membership. Classification holds for every real slope after flipping
the horizontal bond at the two-dimensional origin, and that flip changes the configuration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory

noncomputable section

/-- The genuine unordered horizontal bond from the origin to the first coordinate unit. -/
def horizontalOriginBond : Bond 2 :=
  ⟨s((0 : Vertex 2), Pi.single 0 1), 0, Pi.single 0 1, rfl, by
    norm_num [Fin.sum_univ_two, Pi.single_apply]⟩

/-- The constructed common event has a real configuration; zero belongs by an actual
constant source plane, and every real slope is classified after a nonempty singleton flip. -/
theorem exists_deterministicIntegerSlope_singleton_consumer
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (G : Set (Configuration 2)) (hG : MeasurableSet G)
    (hmass : latticeBondLaw 2 p G = 1) (hvalid : G ⊆ correctorValidEvent 2)
    (hinv : ∀ z ω, configurationTranslation z ω ∈ G ↔ ω ∈ G) :
    ∃ data : DeterministicIntegerSlopeData G hvalid p,
      ∃ (ω : Configuration 2) (hω : ω ∈ data.flipEvent),
        0 ∈ data.subgroup ∧ ({horizontalOriginBond} : Finset (Bond 2)).Nonempty ∧
        finiteBondFlip {horizontalOriginBond} ω ≠ ω ∧
        ∀ q : Fin 2 → ℝ,
          q ∈ data.subgroup ↔
            ∃ u : uniqueInfiniteComponent
                (hvalid (data.flip_mem ω hω {horizontalOriginBond})).1 → ℝ,
              IsCorrectedPlane (uniqueInfiniteComponent
                (hvalid (data.flip_mem ω hω {horizontalOriginBond})).1) q u ∧
              ∀ x y : uniqueInfiniteComponent
                (hvalid (data.flip_mem ω hω {horizontalOriginBond})).1,
                (openGraph (finiteBondFlip {horizontalOriginBond} ω)).Adj x.val y.val →
                  ∃ n : ℤ, u y - u x = (n : ℝ) := by
  classical
  obtain ⟨data⟩ := exists_deterministicIntegerSlopeData p hp0 hp1 G hG hmass hvalid hinv
  have hae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ data.flipEvent :=
    (mem_ae_iff_prob_eq_one data.measurable_flipEvent).mpr data.mass_flipEvent
  obtain ⟨ω, hω⟩ := hae.exists
  have hD := data.flipEvent_subset hω
  have hzero : HasIntegerGradientCorrectedPlane (hvalid (data.event_subset hD)).1 0 := by
    refine ⟨fun _ => 0, isCorrectedPlane_const _ 0, ?_⟩
    intro x y _
    exact ⟨0, by simp only [sub_self, Int.cast_zero]⟩
  have hchange : finiteBondFlip {horizontalOriginBond} ω ≠ ω := by
    intro h
    have he := congrFun h horizontalOriginBond
    rw [finiteBondFlip, BernoulliFiniteFlip.flip_apply,
      if_pos (Finset.mem_singleton_self horizontalOriginBond)] at he
    cases hv : ω horizontalOriginBond <;> simp only [hv, Bool.not_false, Bool.not_true] at he
    all_goals contradiction
  exact ⟨data, ω, hω, (data.source_iff ω hD 0).mpr hzero,
    Finset.singleton_nonempty _, hchange,
    fun q => data.flip_source_iff ω hω {horizontalOriginBond} q⟩

end

end LatticeProb.Percolation
