import LatticeProb.LQG.ContactWindowCountableCoverage
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! # Contact-window coverage from dimension bounds -/

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb.Topology

/-- A preconnected metric set with two distinct points has Hausdorff dimension at least one. -/
theorem one_le_dimH_of_isPreconnected_of_ne {X : Type*} [MetricSpace X]
    {K : Set X} (hK : IsPreconnected K) {x y : X}
    (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) : 1 ≤ dimH K := by
  let d : X → ℝ := fun z => dist z x
  have hlip : LipschitzWith 1 d := LipschitzWith.mk_one fun a b => dist_dist_dist_le_left a b x
  have himage : IsPreconnected (d '' K) := hK.image d hlip.continuous.continuousOn
  have h0 : (0 : ℝ) ∈ d '' K := ⟨x, hx, by simp [d]⟩
  have hy' : dist y x ∈ d '' K := ⟨y, hy, rfl⟩
  have hsub : Icc (0 : ℝ) (dist y x) ⊆ d '' K := himage.ordConnected.out h0 hy'
  have hdist : (0 : ℝ) ≠ dist y x := ne_of_lt (dist_pos.mpr hxy.symm)
  calc
    1 = dimH (segment ℝ (0 : ℝ) (dist y x)) := (Real.dimH_segment hdist).symm
    _ ≤ dimH (d '' K) := dimH_mono (by simpa [segment_eq_Icc, dist_nonneg] using hsub)
    _ ≤ dimH K := hlip.dimH_image_le K

end LatticeProb.Topology

namespace MatedCRTHarmonic.RouteM

/-- A dimension bound on non-direct contacts gives strict-window coverage of each
nonsingleton component of a cell intersection. -/
theorem Peanosphere.contact_components_meet_windows_of_dimH_nondirect_lt_one
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 < y)
    (hbad : dimH {z | z ∈ η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
          η '' Icc (ε * ((y : ℝ) - 1)) (ε * y) ∧
        ¬ ∃ s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x),
          ∃ t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y),
            (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) ∧ η s = z} < 1) :
    ∀ C ∈ LatticeProb.nonSingletonComponents
        (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
          η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)),
      (C ∩ ((fun level => η (ellMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) ∪
        (fun level => η (rhoMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y))).Nonempty := by
  let S := η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
    η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
  let W := (fun level => η (ellMinus ω (ε * x) level)) ''
      Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) ∪
    (fun level => η (rhoMinus ω (ε * x) level)) ''
      Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y)
  let B := {z | z ∈ S ∧ ¬ ∃ s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x),
        ∃ t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y),
          (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) ∧ η s = z}
  let E := {z | ∃ s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x),
        ∃ t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y),
          (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) ∧ η s = z ∧ z ∉ W}
  have hex : E.Countable := P.countable_direct_contacts_outside_windows hε hxy
  have hdim : dimH (S \ W) < 1 := by
    have hsub : S \ W ⊆ B ∪ E := by
      intro z hz
      by_cases hd : ∃ s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x),
          ∃ t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y),
            (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) ∧ η s = z
      · obtain ⟨s, hs, t, ht, hr, he⟩ := hd
        exact Or.inr ⟨s, hs, t, ht, hr, he, hz.2⟩
      · exact Or.inl ⟨hz.1, hd⟩
    calc
      dimH (S \ W) ≤ dimH (B ∪ E) := dimH_mono hsub
      _ = dimH B := by rw [dimH_union, hex.dimH_zero, max_zero]
      _ < 1 := hbad
  intro C hC
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hC.2
  obtain ⟨c, hc, rfl⟩ := hC.1
  by_contra hmeet
  have hsub : connectedComponentIn S c ⊆ S \ W := by
    intro z hz
    exact ⟨connectedComponentIn_subset S c hz, fun hw => hmeet ⟨z, hz, hw⟩⟩
  have hge := LatticeProb.Topology.one_le_dimH_of_isPreconnected_of_ne
    isPreconnected_connectedComponentIn ha hb hab
  exact (not_le_of_gt (lt_of_le_of_lt (dimH_mono hsub) hdim)) hge

end MatedCRTHarmonic.RouteM
