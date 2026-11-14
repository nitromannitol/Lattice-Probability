/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSiteWalk at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFourWalk
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Geom

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

 



theorem laneB_siteCirc_walk {ξ : ℝ} {f : ℂ → ℝ} {z : ℤ × ℤ}
    {c : ℝ≥0∞} (C : SiteCirc ξ f z c) {U : Set ℂ}
    (hU : SiteCirc.Sub U z) :
    ∃ (W : ℝ → ℂ) (a b : ℂ),
      IsPiecewiseC1Path W a b ∧
      MapsTo W (Icc (0 : ℝ) 1) U ∧
      (∀ x, C.On x → x ∈ W '' Icc (0 : ℝ) 1) ∧
      lfppLen ξ f W ≤ 3 * c := by
  obtain ⟨hUB, hUT, hUL, hUR⟩ := hU
  obtain ⟨aB, _haB, bB, _hbB, hpB, hmB⟩ := C.hB
  obtain ⟨aT, _haT, bT, _hbT, hpT, hmT⟩ := C.hT
  obtain ⟨aL, _haL, bL, _hbL, hpL, hmL⟩ := C.hL
  obtain ⟨aR, _haR, bR, _hbR, hpR, hmR⟩ := C.hR
  have hBL : ∃ s ∈ Icc (0 : ℝ) 1,
      ∃ t ∈ Icc (0 : ℝ) 1, C.B s = C.L t := by
    obtain ⟨s, hs, t, ht, e⟩ := hv_meet (H := sB z) (V := sL z) rfl rfl
      (by simp [sL] <;> linarith) (by simp [sB] <;> linarith)
      (by simp [sB, sL] <;> linarith) (by simp [sB, sL] <;> linarith)
      (by simp [sB, sL] <;> linarith) (by simp [sB, sL] <;> linarith)
      C.hB C.hL
    exact ⟨s, hs, t, ht, e⟩
  have hLT : ∃ s ∈ Icc (0 : ℝ) 1,
      ∃ t ∈ Icc (0 : ℝ) 1, C.L s = C.T t := by
    obtain ⟨t, ht, s, hs, e⟩ := hv_meet (H := sT z) (V := sL z) rfl rfl
      (by simp [sL]) (by simp [sT])
      (by simp [sT, sL] <;> linarith) (by simp [sT, sL] <;> linarith)
      (by simp [sT, sL] <;> linarith) (by simp [sT, sL] <;> linarith)
      C.hT C.hL
    exact ⟨s, hs, t, ht, e.symm⟩
  have hBR : ∃ s ∈ Icc (0 : ℝ) 1,
      ∃ t ∈ Icc (0 : ℝ) 1, C.B s = C.R t := by
    obtain ⟨s, hs, t, ht, e⟩ := hv_meet (H := sB z) (V := sR z) rfl rfl
      (by simp [sR] <;> linarith) (by simp [sB] <;> linarith)
      (by simp [sB, sR] <;> linarith) (by simp [sB, sR] <;> linarith)
      (by simp [sB, sR] <;> linarith) (by simp [sB, sR] <;> linarith)
      C.hB C.hR
    exact ⟨s, hs, t, ht, e⟩
  obtain ⟨W, hpW, hmW, htrace, hcost⟩ :=
    laneB_four_crossings_walk (ξ := ξ) (f := f) hpB hpL hpT hpR
      (fun t ht => hUB (hmB t ht))
      (fun t ht => hUL (hmL t ht))
      (fun t ht => hUT (hmT t ht))
      (fun t ht => hUR (hmR t ht)) hBL hLT hBR
  refine ⟨W, aB, bB, hpW, hmW, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ |
      ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact htrace (Or.inl (Or.inl (Or.inl ⟨t, ht, rfl⟩)))
    · exact htrace (Or.inl (Or.inr ⟨t, ht, rfl⟩))
    · exact htrace (Or.inl (Or.inl (Or.inr ⟨t, ht, rfl⟩)))
    · exact htrace (Or.inr ⟨t, ht, rfl⟩)
  · have hB3 : lfppLen ξ f C.B ≤ 3 * lfppLen ξ f C.B := by
      calc
        _ = 1 * lfppLen ξ f C.B := by simp
        _ ≤ 3 * lfppLen ξ f C.B := by gcongr; norm_num
    calc
      lfppLen ξ f W ≤ lfppLen ξ f C.B +
          3 * (lfppLen ξ f C.L + lfppLen ξ f C.T + lfppLen ξ f C.R) := hcost
      _ ≤ 3 * (lfppLen ξ f C.B + lfppLen ξ f C.T +
          lfppLen ξ f C.L + lfppLen ξ f C.R) := by
        simp only [mul_add]
        calc
          _ ≤ 3 * lfppLen ξ f C.B +
              (3 * lfppLen ξ f C.L + 3 * lfppLen ξ f C.T +
                3 * lfppLen ξ f C.R) := add_le_add_left hB3 _
          _ = _ := by ac_rfl
      _ ≤ 3 * c := by gcongr <;> exact C.hc

end SupercriticalLQGUniqueness.B2.DG20Conc
