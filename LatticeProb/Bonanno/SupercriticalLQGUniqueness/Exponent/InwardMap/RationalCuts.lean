/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.RationalCuts at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.AffineCost




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

 

def ratCrossing (r x y : ℚ) : ℚ :=
  if x = y then 0 else (r-x)/(y-x)

def ratKinks : Finset ℚ := {-1, 0, 1, 2}

def ratAxisCuts (x y : ℚ) : Finset ℚ :=
  ratKinks.image (fun r => ratCrossing r x y)

def ratSegmentCuts (p q : ℚ × ℚ) : Finset ℚ :=
  insert 0 (insert 1
    ((ratAxisCuts p.1 q.1 ∪ ratAxisCuts p.2 q.2).filter
      (fun t => 0 < t ∧ t < 1)))

theorem ratCrossing_spec (r x y : ℚ) (hxy : x ≠ y) :
    x + ratCrossing r x y * (y-x) = r := by
  unfold ratCrossing
  rw [if_neg hxy]
  have hden : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  field_simp
  ring

theorem ratAxisCuts_has_crossing (r x y t : ℚ)
    (hr : r ∈ ratKinks) (hxy : x ≠ y)
    (ht : x+t*(y-x)=r) : t ∈ ratAxisCuts x y := by
  have heq : t = ratCrossing r x y := by
    have hden : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    unfold ratCrossing
    rw [if_neg hxy]
    apply (eq_div_iff hden).mpr
    linear_combination ht
  rw [heq]
  exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

theorem ratSegmentCuts_zero (p q : ℚ × ℚ) :
    (0:ℚ) ∈ ratSegmentCuts p q := by simp [ratSegmentCuts]

theorem ratSegmentCuts_one (p q : ℚ × ℚ) :
    (1:ℚ) ∈ ratSegmentCuts p q := by simp [ratSegmentCuts]

theorem ratSegmentCuts_mem_Icc (p q : ℚ × ℚ) {t : ℚ}
    (ht : t ∈ ratSegmentCuts p q) : 0 ≤ t ∧ t ≤ 1 := by
  simp only [ratSegmentCuts, Finset.mem_insert, Finset.mem_filter] at ht
  rcases ht with rfl | rfl | ⟨_, ht⟩
  · exact ⟨le_rfl, by norm_num⟩
  · exact ⟨by norm_num, le_rfl⟩
  · exact ⟨ht.1.le, ht.2.le⟩

theorem ratSegmentCuts_has_vertical (p q : ℚ × ℚ) (r t : ℚ)
    (hr : r ∈ ratKinks) (hpq : p.1 ≠ q.1)
    (ht0 : 0 < t) (ht1 : t < 1) (heq : p.1+t*(q.1-p.1)=r) :
    t ∈ ratSegmentCuts p q := by
  simp only [ratSegmentCuts, Finset.mem_insert, Finset.mem_filter]
  exact Or.inr (Or.inr ⟨Finset.mem_union_left _
    (ratAxisCuts_has_crossing r p.1 q.1 t hr hpq heq), ⟨ht0, ht1⟩⟩)

theorem ratSegmentCuts_has_horizontal (p q : ℚ × ℚ) (r t : ℚ)
    (hr : r ∈ ratKinks) (hpq : p.2 ≠ q.2)
    (ht0 : 0 < t) (ht1 : t < 1) (heq : p.2+t*(q.2-p.2)=r) :
    t ∈ ratSegmentCuts p q := by
  simp only [ratSegmentCuts, Finset.mem_insert, Finset.mem_filter]
  exact Or.inr (Or.inr ⟨Finset.mem_union_right _
    (ratAxisCuts_has_crossing r p.2 q.2 t hr hpq heq), ⟨ht0, ht1⟩⟩)

 
private theorem rat_affine_strictMono {x y : ℚ} (h : 0 < y-x) :
    StrictMono (fun u : ℚ => x+u*(y-x)) := by
  intro s t hst
  have hm := mul_lt_mul_of_pos_right hst h
  linarith

private theorem rat_affine_strictAnti {x y : ℚ} (h : y-x < 0) :
    StrictAnti (fun u : ℚ => x+u*(y-x)) := by
  intro s t hst
  have hm := mul_lt_mul_of_neg_right hst h
  linarith

theorem ratCrossing_between (r x y s t : ℚ) (hst : s < t)
    (hxy : x ≠ y)
    (hbetween :
      (x+s*(y-x) < r ∧ r < x+t*(y-x)) ∨
      (x+t*(y-x) < r ∧ r < x+s*(y-x))) :
    s < ratCrossing r x y ∧ ratCrossing r x y < t := by
  let c := ratCrossing r x y
  have hc : x+c*(y-x)=r := ratCrossing_spec r x y hxy
  rcases hbetween with h | h
  · have hD : 0 < y-x := by
      by_contra hn
      have hm := mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hst.le) (le_of_not_gt hn)
      nlinarith
    have hm := rat_affine_strictMono hD
    constructor
    · apply hm.lt_iff_lt.mp
      rw [hc]
      exact h.1
    · apply hm.lt_iff_lt.mp
      rw [hc]
      exact h.2
  · have hD : y-x < 0 := by
      by_contra hn
      have hm := mul_nonneg (sub_nonneg.mpr hst.le) (le_of_not_gt hn)
      nlinarith
    have hm := rat_affine_strictAnti hD
    constructor
    · by_contra hn
      have hs : c ≤ s := le_of_not_gt hn
      have hb := hm.antitone hs
      rw [hc] at hb
      linarith [h.2]
    · by_contra hn
      have ht : t ≤ c := le_of_not_gt hn
      have hb := hm.antitone ht
      rw [hc] at hb
      linarith [h.1]

theorem ratSegmentCuts_no_vertical_kink (p q : ℚ × ℚ) (s t r : ℚ)
    (hs : s ∈ ratSegmentCuts p q) (ht : t ∈ ratSegmentCuts p q)
    (hst : s < t)
    (hadj : ∀ u ∈ ratSegmentCuts p q, ¬(s < u ∧ u < t))
    (hr : r ∈ ratKinks) (hpq : p.1 ≠ q.1) :
    ¬((p.1+s*(q.1-p.1) < r ∧ r < p.1+t*(q.1-p.1)) ∨
      (p.1+t*(q.1-p.1) < r ∧ r < p.1+s*(q.1-p.1))) := by
  intro hb
  let u := ratCrossing r p.1 q.1
  have hu := ratCrossing_between r p.1 q.1 s t hst hpq hb
  have hbounds := ratSegmentCuts_mem_Icc p q hs
  have hbounds' := ratSegmentCuts_mem_Icc p q ht
  have hu0 : 0 < u := lt_of_le_of_lt hbounds.1 hu.1
  have hu1 : u < 1 := lt_of_lt_of_le hu.2 hbounds'.2
  exact hadj u
    (ratSegmentCuts_has_vertical p q r u hr hpq hu0 hu1
      (ratCrossing_spec r p.1 q.1 hpq)) hu

theorem ratSegmentCuts_no_horizontal_kink (p q : ℚ × ℚ) (s t r : ℚ)
    (hs : s ∈ ratSegmentCuts p q) (ht : t ∈ ratSegmentCuts p q)
    (hst : s < t)
    (hadj : ∀ u ∈ ratSegmentCuts p q, ¬(s < u ∧ u < t))
    (hr : r ∈ ratKinks) (hpq : p.2 ≠ q.2) :
    ¬((p.2+s*(q.2-p.2) < r ∧ r < p.2+t*(q.2-p.2)) ∨
      (p.2+t*(q.2-p.2) < r ∧ r < p.2+s*(q.2-p.2))) := by
  intro hb
  let u := ratCrossing r p.2 q.2
  have hu := ratCrossing_between r p.2 q.2 s t hst hpq hb
  have hbounds := ratSegmentCuts_mem_Icc p q hs
  have hbounds' := ratSegmentCuts_mem_Icc p q ht
  have hu0 : 0 < u := lt_of_le_of_lt hbounds.1 hu.1
  have hu1 : u < 1 := lt_of_lt_of_le hu.2 hbounds'.2
  exact hadj u
    (ratSegmentCuts_has_horizontal p q r u hr hpq hu0 hu1
      (ratCrossing_spec r p.2 q.2 hpq)) hu

theorem ratSegmentCuts_no_cut_between (p q : ℚ × ℚ)
    {n : ℕ} {t : Fin (n+1) → ℚ} (hm : StrictMono t)
    (hr : Finset.univ.image t = ratSegmentCuts p q) (i : Fin n) :
    ∀ u ∈ ratSegmentCuts p q, ¬(t i.castSucc < u ∧ u < t i.succ) := by
  intro u hu hbetween
  rw [← hr] at hu
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
  have hj1 : i.castSucc < j := hm.lt_iff_lt.mp hbetween.1
  have hj2 : j < i.succ := hm.lt_iff_lt.mp hbetween.2
  exact absurd hj2 (not_lt.mpr (Fin.castSucc_lt_iff_succ_le.mp hj1))


end SupercriticalLQGUniqueness.Exponent.InwardMap
