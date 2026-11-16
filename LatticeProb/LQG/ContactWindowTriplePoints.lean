import LatticeProb.LQG.FullFibreContactLocalization
import LatticeProb.LQG.ContactWindowDimensionCoverage

/-! # Triple points and contact-window coverage -/

open Set
open scoped ENNReal

namespace MatedCRTHarmonic.RouteM

/-- A non-direct contour identification has at least three distinct visits. -/
theorem Peanosphere.exists_third_visit_of_nondirect
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {s t : ℝ} (hst : s < t) (he : η s = η t)
    (hno : ¬ (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t)) :
    ∃ u, u ≠ s ∧ u ≠ t ∧ η u = η s := by
  obtain ⟨a, b, hab, _, hcross⟩ :=
    eqvGen_exists_crossing_link (P.onlyMerge s t he) {s} (by simp)
      (by simpa using hst.ne.symm)
  simp only [mem_singleton_iff] at hcross
  rcases hcross with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · subst a
    refine ⟨b, hb, ?_, (P.merge s b hab).symm⟩
    intro hbt
    subst b
    exact hno hab
  · subst b
    refine ⟨a, ha, ?_, P.merge a s hab⟩
    have has : a < s := hab.elim (fun h => h.1) (fun h => h.1)
    exact ne_of_lt (lt_trans has hst)

/-- If spatial triple points have dimension below one, every nonsingleton
component of a cell intersection meets a strict contact window. -/
theorem Peanosphere.contact_components_meet_windows_of_dimH_triple_lt_one
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 < y)
    (htriple : dimH {z | ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      η a = z ∧ η b = z ∧ η c = z} < 1) :
    ∀ C ∈ LatticeProb.nonSingletonComponents
        (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
          η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)),
      (C ∩ ((fun level => η (ellMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) ∪
        (fun level => η (rhoMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y))).Nonempty := by
  apply P.contact_components_meet_windows_of_dimH_nondirect_lt_one hε hxy
  apply lt_of_le_of_lt (dimH_mono ?_) htriple
  rintro z ⟨⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩, hno⟩
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have hst : s < t := by nlinarith [hs.2, ht.1]
  have hrel : ¬ (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) := by
    intro h
    exact hno ⟨s, hs, t, ht, h, hsz⟩
  obtain ⟨u, hus, hut, hu⟩ :=
    P.exists_third_visit_of_nondirect hst (hsz.trans htz.symm) hrel
  exact ⟨s, t, u, hst.ne, hus.symm, hut.symm, hsz, htz, hu.trans hsz⟩

end MatedCRTHarmonic.RouteM
