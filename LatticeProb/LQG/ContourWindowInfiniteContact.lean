import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.DLevels

/-! # Contact points from contour windows -/

set_option autoImplicit false

open Set

namespace LatticeProb

open MatedCRTHarmonic.RouteM

/-- A strict contour window gives infinitely many shared cell points when
point fibres are finite and direct contour identifications are merged. -/
theorem infinite_cell_inter_of_strict_contour_window
    {X : ℝ → ℝ} {η : ℝ → ℂ} {ε : ℝ} {x y : ℤ}
    (hX : Continuous X) (hε : 0 < ε) (hxy : x + 1 < y)
    (hmerge : ∀ s t, directRel X s t → η s = η t)
    (hfinite : ∀ z : ℂ, (η ⁻¹' {z}).Finite)
    (hwin : dWinLo ε X x y < dWinHi ε X x y) :
    (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
      η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)).Infinite := by
  intro hfin
  have htimes : (η ⁻¹' (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
      η '' Icc (ε * ((y : ℝ) - 1)) (ε * y))).Finite :=
    hfin.preimage' (fun z _ => hfinite z)
  apply (Set.Ioo_infinite hwin) ((htimes.image X).subset ?_)
  intro lev hlev
  obtain ⟨hd, hlevel⟩ := lowArcData_contacts hX hε hxy hlev.1 hlev.2
  refine ⟨_, ?_, hlevel⟩
  change η (dLast X (ε * x) lev) ∈
    (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩
      (η '' Icc (ε * ((y : ℝ) - 1)) (ε * y))
  constructor
  · exact ⟨_, ⟨hd.mem₁.1.le, hd.mem₁.2.le⟩, rfl⟩
  · exact ⟨_, ⟨hd.mem₂.1.le, hd.mem₂.2.le⟩, (hmerge _ _ hd.rel).symm⟩

end LatticeProb
