import LatticeProb.LQG.PeanosphereContactWindow

/-! # Direct contacts in strict contour windows -/

open Set

namespace MatedCRTHarmonic.RouteM

/-- A direct left contact between two nonconsecutive cells is represented by
its strict-window selector at the boundary of the first cell. -/
theorem left_direct_contact_mem_window_image {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    {ε : ℝ} {x y : ℤ} {s t : ℝ}
    (hε : 0 < ε) (hxy : x + 1 < y)
    (hs : s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x))
    (ht : t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y))
    (h : directRel (lCoord ω) s t)
    (hlevel : lCoord ω s ∈ Ioo (dWinLo ε (lCoord ω) x y)
      (dWinHi ε (lCoord ω) x y)) :
    η s ∈ (fun level => η (ellMinus ω (ε * x) level)) ''
      Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) := by
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have hst : ε * (x : ℝ) < t := by nlinarith [ht.1]
  have heq : ellMinus ω (ε * x) (lCoord ω s) = s :=
    ellMinus_eq_left_of_above s t (lCoord ω s) rfl h.2.2 hs.2 hst
  exact ⟨lCoord ω s, hlevel, by simp only [heq]⟩

/-- A direct right contact between two nonconsecutive cells is represented by
its strict-window selector at the boundary of the first cell. -/
theorem right_direct_contact_mem_window_image {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    {ε : ℝ} {x y : ℤ} {s t : ℝ}
    (hε : 0 < ε) (hxy : x + 1 < y)
    (hs : s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x))
    (ht : t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y))
    (h : directRel (rCoord ω) s t)
    (hlevel : rCoord ω s ∈ Ioo (dWinLo ε (rCoord ω) x y)
      (dWinHi ε (rCoord ω) x y)) :
    η s ∈ (fun level => η (rhoMinus ω (ε * x) level)) ''
      Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y) := by
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have hst : ε * (x : ℝ) < t := by nlinarith [ht.1]
  have heq : rhoMinus ω (ε * x) (rCoord ω s) = s :=
    rhoMinus_eq_left_of_above s t (rCoord ω s) rfl h.2.2 hs.2 hst
  exact ⟨rCoord ω s, hlevel, by simp only [heq]⟩

end MatedCRTHarmonic.RouteM
