/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBMeetDetour at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundSeg
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundConcat
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLengthSplit

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

 

def laneBMeetDetour (P Q : ℝ → ℂ) (s t : ℝ) : ℝ → ℂ :=
  concatPath
    (concatPath (Strong.seg P 0 s)
      (concatPath (concatPath (Strong.seg Q t 0) Q) (Strong.seg Q 1 t)))
    (Strong.seg P s 1)

private theorem laneB_concatPath_one (P Q : ℝ → ℂ) :
    concatPath P Q 1 = Q 1 := by
  norm_num [concatPath]

 



theorem laneB_meetDetour_piecewise {P Q : ℝ → ℂ} {a b c d : ℂ}
    (hP : IsPiecewiseC1Path P a b) (hQ : IsPiecewiseC1Path Q c d)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hmeet : P s = Q t) : IsPiecewiseC1Path (laneBMeetDetour P Q s t) a b := by
  have hP₀ := DG20Pt.isPiecewiseC1Path_aroundSeg hP
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hs
  have hP₁ := DG20Pt.isPiecewiseC1Path_aroundSeg hP hs
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have hQ₀ := DG20Pt.isPiecewiseC1Path_aroundSeg hQ ht
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  have hQ₂ := DG20Pt.isPiecewiseC1Path_aroundSeg hQ
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ht
  have hQa : IsPiecewiseC1Path Q (Q 0) (Q 1) := by
    rw [hQ.source, hQ.target]
    exact hQ
  have hQ' := isPiecewiseC1Path_concatPath
    (isPiecewiseC1Path_concatPath hQ₀ hQa) hQ₂
  have hP' := isPiecewiseC1Path_concatPath hP₀ (by simpa [hmeet] using hQ')
  have hP₁' : IsPiecewiseC1Path (Strong.seg P s 1) (Q t) (P 1) := by
    rw [← hmeet]
    exact hP₁
  simpa only [laneBMeetDetour, hP.source, hP.target] using
    (isPiecewiseC1Path_concatPath hP' hP₁')

 


theorem laneB_meetDetour_contains_crossing {P Q : ℝ → ℂ}
    {s t : ℝ} (hmeet : P s = Q t) :
    Q '' Icc (0 : ℝ) 1 ⊆ laneBMeetDetour P Q s t '' Icc (0 : ℝ) 1 := by
  have hQ₀ : (Strong.seg Q t 0) 1 = Q 0 := by simp
  have hQ₁ : (concatPath (Strong.seg Q t 0) Q) 1 = (Strong.seg Q 1 t) 0 := by
    norm_num [concatPath, Strong.seg]
  have hP₀ : (Strong.seg P 0 s) 1 =
      (concatPath (concatPath (Strong.seg Q t 0) Q) (Strong.seg Q 1 t)) 0 := by
    norm_num [concatPath, Strong.seg, hmeet]
  have hP₁ : (concatPath (Strong.seg P 0 s)
      (concatPath (concatPath (Strong.seg Q t 0) Q) (Strong.seg Q 1 t))) 1 =
      (Strong.seg P s 1) 0 := by
    simp only [laneB_concatPath_one, Strong.seg_one, Strong.seg_zero]
    exact hmeet.symm
  rw [laneBMeetDetour, DG20Pt.concatPath_image_Icc _ _ hP₁,
    DG20Pt.concatPath_image_Icc _ _ hP₀,
    DG20Pt.concatPath_image_Icc _ _ hQ₁,
    DG20Pt.concatPath_image_Icc _ _ hQ₀]
  intro z hz
  exact Or.inl (Or.inr (Or.inl (Or.inr hz)))

 

theorem laneB_seg_split_cover (P : ℝ → ℂ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    P '' Icc (0 : ℝ) 1 ⊆
      (Strong.seg P 0 s) '' Icc (0 : ℝ) 1 ∪
        (Strong.seg P s 1) '' Icc (0 : ℝ) 1 := by
  rintro z ⟨u, hu, rfl⟩
  by_cases hus : u ≤ s
  · by_cases hs0 : s = 0
    · have hu0 : u = 0 := by linarith [hu.1]
      left
      exact ⟨0, by norm_num, by simp [Strong.seg, hu0]⟩
    · have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      left
      refine ⟨u / s, ⟨div_nonneg hu.1 hsp.le, (div_le_one hsp).2 hus⟩, ?_⟩
      simp only [Strong.seg, zero_add, sub_zero]
      congr 1
      field_simp
  · have hsu : s ≤ u := le_of_lt (lt_of_not_ge hus)
    by_cases hs1 : s = 1
    · have hu1 : u = 1 := by linarith [hu.2]
      right
      exact ⟨0, by norm_num, by simp [Strong.seg, hs1, hu1]⟩
    · have hsp : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hs1)
      right
      refine ⟨(u - s) / (1 - s),
        ⟨div_nonneg (sub_nonneg.mpr hsu) hsp.le,
          (div_le_one hsp).2 (by linarith [hu.2])⟩, ?_⟩
      simp only [Strong.seg]
      congr 1
      field_simp
      ring

 


theorem laneB_meetDetour_contains_base {P Q : ℝ → ℂ}
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hmeet : P s = Q t) :
    P '' Icc (0 : ℝ) 1 ⊆ laneBMeetDetour P Q s t '' Icc (0 : ℝ) 1 := by
  have hQ₀ : (Strong.seg Q t 0) 1 = Q 0 := by simp
  have hQ₁ : (concatPath (Strong.seg Q t 0) Q) 1 = (Strong.seg Q 1 t) 0 := by
    norm_num [concatPath, Strong.seg]
  have hP₀ : (Strong.seg P 0 s) 1 =
      (concatPath (concatPath (Strong.seg Q t 0) Q) (Strong.seg Q 1 t)) 0 := by
    norm_num [concatPath, Strong.seg, hmeet]
  have hP₁ : (concatPath (Strong.seg P 0 s)
      (concatPath (concatPath (Strong.seg Q t 0) Q) (Strong.seg Q 1 t))) 1 =
      (Strong.seg P s 1) 0 := by
    simp only [laneB_concatPath_one, Strong.seg_one, Strong.seg_zero]
    exact hmeet.symm
  rw [laneBMeetDetour, DG20Pt.concatPath_image_Icc _ _ hP₁,
    DG20Pt.concatPath_image_Icc _ _ hP₀,
    DG20Pt.concatPath_image_Icc _ _ hQ₁,
    DG20Pt.concatPath_image_Icc _ _ hQ₀]
  intro z hz
  rcases laneB_seg_split_cover P hs hz with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr h

 


theorem laneB_meetDetour_mapsTo {P Q : ℝ → ℂ} {U : Set ℂ}
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hmeet : P s = Q t)
    (hP : MapsTo P (Icc (0 : ℝ) 1) U)
    (hQ : MapsTo Q (Icc (0 : ℝ) 1) U) :
    MapsTo (laneBMeetDetour P Q s t) (Icc (0 : ℝ) 1) U := by
  have hQ₀ : (Strong.seg Q t 0) 1 = Q 0 := by simp
  have hQ₁ : (concatPath (Strong.seg Q t 0) Q) 1 = (Strong.seg Q 1 t) 0 := by
    norm_num [concatPath, Strong.seg]
  have hP₀ : (Strong.seg P 0 s) 1 =
      (concatPath (concatPath (Strong.seg Q t 0) Q) (Strong.seg Q 1 t)) 0 := by
    norm_num [concatPath, Strong.seg, hmeet]
  have hP₁ : (concatPath (Strong.seg P 0 s)
      (concatPath (concatPath (Strong.seg Q t 0) Q) (Strong.seg Q 1 t))) 1 =
      (Strong.seg P s 1) 0 := by
    simp only [laneB_concatPath_one, Strong.seg_one, Strong.seg_zero]
    exact hmeet.symm
  have p₀ : (Strong.seg P 0 s) '' Icc (0 : ℝ) 1 ⊆ U := by
    rintro z ⟨u, hu, rfl⟩
    exact Strong.mapsTo_seg hP (by norm_num) hs hu
  have p₁ : (Strong.seg P s 1) '' Icc (0 : ℝ) 1 ⊆ U := by
    rintro z ⟨u, hu, rfl⟩
    exact Strong.mapsTo_seg hP hs (by norm_num) hu
  have q₀ : (Strong.seg Q t 0) '' Icc (0 : ℝ) 1 ⊆ U := by
    rintro z ⟨u, hu, rfl⟩
    exact Strong.mapsTo_seg hQ ht (by norm_num) hu
  have q₂ : (Strong.seg Q 1 t) '' Icc (0 : ℝ) 1 ⊆ U := by
    rintro z ⟨u, hu, rfl⟩
    exact Strong.mapsTo_seg hQ (by norm_num) ht hu
  have q₁ : Q '' Icc (0 : ℝ) 1 ⊆ U := by
    rintro z ⟨u, hu, huz⟩
    rw [← huz]
    exact hQ hu
  have hsub : laneBMeetDetour P Q s t '' Icc (0 : ℝ) 1 ⊆ U := by
    rw [laneBMeetDetour, DG20Pt.concatPath_image_Icc _ _ hP₁,
      DG20Pt.concatPath_image_Icc _ _ hP₀,
      DG20Pt.concatPath_image_Icc _ _ hQ₁,
      DG20Pt.concatPath_image_Icc _ _ hQ₀]
    exact union_subset (union_subset p₀
      (union_subset (union_subset q₀ q₁) q₂)) p₁
  exact fun u hu => hsub ⟨u, hu, rfl⟩

 




theorem laneB_meetDetour_len_le_add {ξ : ℝ} {f : ℂ → ℝ}
    {P Q : ℝ → ℂ} {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hmeet : P s = Q t) :
    lfppLen ξ f (laneBMeetDetour P Q s t) ≤
      lfppLen ξ f P + 3 * lfppLen ξ f Q := by
  have hQ₀ : (Strong.seg Q t 0) 1 = Q 0 := by simp
  have hQ₁ : (concatPath (Strong.seg Q t 0) Q) 1 = (Strong.seg Q 1 t) 0 := by
    norm_num [concatPath, Strong.seg]
  have hP₀ : (Strong.seg P 0 s) 1 =
      (concatPath (concatPath (Strong.seg Q t 0) Q) (Strong.seg Q 1 t)) 0 := by
    norm_num [concatPath, Strong.seg, hmeet]
  have hP₁ : (concatPath (Strong.seg P 0 s)
      (concatPath (concatPath (Strong.seg Q t 0) Q) (Strong.seg Q 1 t))) 1 =
      (Strong.seg P s 1) 0 := by
    simp only [laneB_concatPath_one, Strong.seg_one, Strong.seg_zero]
    exact hmeet.symm
  rw [laneBMeetDetour, lfppLen_concatPath hP₁,
    lfppLen_concatPath hP₀, lfppLen_concatPath hQ₁,
    lfppLen_concatPath hQ₀]
  have h₂ := DG20Pt.lfppLen_aroundSeg_le ξ f Q ht
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  have h₃ := DG20Pt.lfppLen_aroundSeg_le ξ f Q
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ht
  calc
    _ ≤ (lfppLen ξ f (Strong.seg P 0 s) +
          (lfppLen ξ f Q + lfppLen ξ f Q + lfppLen ξ f Q)) +
          lfppLen ξ f (Strong.seg P s 1) := by gcongr
    _ = (lfppLen ξ f (Strong.seg P 0 s) +
          lfppLen ξ f (Strong.seg P s 1)) +
          (lfppLen ξ f Q + lfppLen ξ f Q + lfppLen ξ f Q) := by ac_rfl
    _ = lfppLen ξ f P +
          (lfppLen ξ f Q + lfppLen ξ f Q + lfppLen ξ f Q) := by
          rw [laneB_lfppLen_split ξ f P hs]
    _ = lfppLen ξ f P + 3 * lfppLen ξ f Q := by
      rw [show (3 : ℝ≥0∞) = 1 + 1 + 1 by norm_num]
      simp only [add_mul, one_mul]

 


end SupercriticalLQGUniqueness.B2.DG20Conc
