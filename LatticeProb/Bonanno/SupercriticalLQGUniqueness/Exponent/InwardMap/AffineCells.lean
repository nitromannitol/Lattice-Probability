/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.AffineCells at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.MappedSegment




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

theorem inwardAxis_left_outer (a x : ℝ) (hx : x ≤ -1) :
    inwardAxis a x = x+32*a := by
  unfold inwardAxis inwardCoord
  split_ifs <;> nlinarith

theorem inwardAxis_left_inner (a x : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 0) :
    inwardAxis a x = (1-64*a)*x-32*a := by
  by_cases hb : x = -1
  · subst x
    rw [inwardAxis_neg_one]
    ring
  have hx0' : -1 < x := lt_of_le_of_ne hx0 (Ne.symm hb)
  unfold inwardAxis inwardCoord
  split_ifs <;> nlinarith

theorem inwardAxis_middle (a x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    inwardAxis a x = (1+64*a)*x-32*a := by
  by_cases hb : x = 0
  · subst x
    rw [inwardAxis_zero]
    ring
  have hx0' : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hb)
  unfold inwardAxis inwardCoord
  split_ifs <;> nlinarith

theorem inwardAxis_right_inner (a x : ℝ) (hx0 : 1 ≤ x) (hx1 : x ≤ 2) :
    inwardAxis a x = (1-64*a)*x+96*a := by
  by_cases hb : x = 1
  · subst x
    rw [inwardAxis_one]
    ring
  have hx0' : 1 < x := lt_of_le_of_ne hx0 (Ne.symm hb)
  unfold inwardAxis inwardCoord
  split_ifs <;> nlinarith

theorem inwardAxis_right_outer (a x : ℝ) (hx : 2 ≤ x) :
    inwardAxis a x = x-32*a := by
  by_cases hb : x = 2
  · subst x
    rw [inwardAxis_two]
  have hx' : 2 < x := lt_of_le_of_ne hx (Ne.symm hb)
  unfold inwardAxis inwardCoord
  split_ifs <;> nlinarith

 
def SameAxisCell (x y : ℝ) : Prop :=
  (x ≤ -1 ∧ y ≤ -1) ∨
  ((-1 ≤ x ∧ x ≤ 0) ∧ (-1 ≤ y ∧ y ≤ 0)) ∨
  ((0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1)) ∨
  ((1 ≤ x ∧ x ≤ 2) ∧ (1 ≤ y ∧ y ≤ 2)) ∨
  (2 ≤ x ∧ 2 ≤ y)

theorem inwardAxis_affine_on_cell (a x y t : ℝ)
    (hcell : SameAxisCell x y) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    inwardAxis a (x+t*(y-x)) =
      inwardAxis a x+t*(inwardAxis a y-inwardAxis a x) := by
  have hmem {S : Set ℝ} (hS : Convex ℝ S) (hx : x ∈ S) (hy : y ∈ S) :
      x+t*(y-x) ∈ S := by
    simpa only [smul_eq_mul] using hS.add_smul_sub_mem hx hy ht
  rcases hcell with h | h | h | h | h
  · have hu : x+t*(y-x) ≤ -1 :=
      hmem (convex_Iic _) h.1 h.2
    rw [inwardAxis_left_outer a _ hu,
      inwardAxis_left_outer a x h.1, inwardAxis_left_outer a y h.2]
    ring
  · have hu : x+t*(y-x) ∈ Set.Icc (-1:ℝ) 0 :=
      hmem (convex_Icc _ _) h.1 h.2
    rw [inwardAxis_left_inner a _ hu.1 hu.2,
      inwardAxis_left_inner a x h.1.1 h.1.2,
      inwardAxis_left_inner a y h.2.1 h.2.2]
    ring
  · have hu : x+t*(y-x) ∈ Set.Icc (0:ℝ) 1 :=
      hmem (convex_Icc _ _) h.1 h.2
    rw [inwardAxis_middle a _ hu.1 hu.2,
      inwardAxis_middle a x h.1.1 h.1.2,
      inwardAxis_middle a y h.2.1 h.2.2]
    ring
  · have hu : x+t*(y-x) ∈ Set.Icc (1:ℝ) 2 :=
      hmem (convex_Icc _ _) h.1 h.2
    rw [inwardAxis_right_inner a _ hu.1 hu.2,
      inwardAxis_right_inner a x h.1.1 h.1.2,
      inwardAxis_right_inner a y h.2.1 h.2.2]
    ring
  · have hu : 2 ≤ x+t*(y-x) :=
      hmem (convex_Ici _) h.1 h.2
    rw [inwardAxis_right_outer a _ hu,
      inwardAxis_right_outer a x h.1, inwardAxis_right_outer a y h.2]
    ring

theorem sameAxisCell_of_no_strict_kink (x y : ℝ) (hxy : x ≤ y)
    (hm1 : ¬(x < -1 ∧ -1 < y))
    (h0 : ¬(x < 0 ∧ 0 < y))
    (h1 : ¬(x < 1 ∧ 1 < y))
    (h2 : ¬(x < 2 ∧ 2 < y)) :
    SameAxisCell x y := by
  by_cases hy : y ≤ -1
  · exact Or.inl ⟨hxy.trans hy, hy⟩
  have hx : -1 ≤ x := by
    by_contra h
    exact hm1 ⟨lt_of_not_ge h, lt_of_not_ge hy⟩
  by_cases hy0 : y ≤ 0
  · exact Or.inr (Or.inl ⟨⟨hx, hxy.trans hy0⟩, ⟨le_of_lt (lt_of_not_ge hy), hy0⟩⟩)
  have hx0 : 0 ≤ x := by
    by_contra h
    exact h0 ⟨lt_of_not_ge h, lt_of_not_ge hy0⟩
  by_cases hy1 : y ≤ 1
  · exact Or.inr (Or.inr (Or.inl
      ⟨⟨hx0, hxy.trans hy1⟩, ⟨le_of_lt (lt_of_not_ge hy0), hy1⟩⟩))
  have hx1 : 1 ≤ x := by
    by_contra h
    exact h1 ⟨lt_of_not_ge h, lt_of_not_ge hy1⟩
  by_cases hy2 : y ≤ 2
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨hx1, hxy.trans hy2⟩, ⟨le_of_lt (lt_of_not_ge hy1), hy2⟩⟩)))
  have hx2 : 2 ≤ x := by
    by_contra h
    exact h2 ⟨lt_of_not_ge h, lt_of_not_ge hy2⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hx2, hx2.trans hxy⟩)))

theorem sameAxisCell_symm {x y : ℝ} (h : SameAxisCell x y) :
    SameAxisCell y x := by
  rcases h with h | h | h | h | h
  · exact Or.inl ⟨h.2, h.1⟩
  · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩)))

theorem sameAxisCell_rat_of_no_kink (x y : ℚ)
    (h : ∀ r ∈ ratKinks,
      ¬((x < r ∧ r < y) ∨ (y < r ∧ r < x))) :
    SameAxisCell (x:ℝ) (y:ℝ) := by
  have hk (r : ℚ) (hr : r ∈ ratKinks) :
      ¬((x:ℝ) < (r:ℝ) ∧ (r:ℝ) < (y:ℝ)) := by
    intro hb
    have hbq : x < r ∧ r < y :=
      ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩
    exact h r hr (Or.inl hbq)
  have hk' (r : ℚ) (hr : r ∈ ratKinks) :
      ¬((y:ℝ) < (r:ℝ) ∧ (r:ℝ) < (x:ℝ)) := by
    intro hb
    have hbq : y < r ∧ r < x :=
      ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩
    exact h r hr (Or.inr hbq)
  have hm1 : (-1:ℚ) ∈ ratKinks := by norm_num [ratKinks]
  have h0 : (0:ℚ) ∈ ratKinks := by norm_num [ratKinks]
  have h1 : (1:ℚ) ∈ ratKinks := by norm_num [ratKinks]
  have h2 : (2:ℚ) ∈ ratKinks := by norm_num [ratKinks]
  rcases le_total x y with hxy | hyx
  · exact sameAxisCell_of_no_strict_kink (x:ℝ) (y:ℝ)
      (by exact_mod_cast hxy)
      (by simpa using hk (-1) hm1)
      (by simpa using hk 0 h0)
      (by simpa using hk 1 h1)
      (by simpa using hk 2 h2)
  · apply sameAxisCell_symm
    exact sameAxisCell_of_no_strict_kink (y:ℝ) (x:ℝ)
      (by exact_mod_cast hyx)
      (by simpa using hk' (-1) hm1)
      (by simpa using hk' 0 h0)
      (by simpa using hk' 1 h1)
      (by simpa using hk' 2 h2)

theorem ratSegmentCuts_adjacent_sameCell (p q : ℚ × ℚ)
    {n : ℕ} {t : Fin (n+1) → ℚ} (hm : StrictMono t)
    (hr : Finset.univ.image t = ratSegmentCuts p q) (i : Fin n) :
    SameAxisCell ((ratLinePoint p q (t i.castSucc)).1:ℝ)
      ((ratLinePoint p q (t i.succ)).1:ℝ) ∧
    SameAxisCell ((ratLinePoint p q (t i.castSucc)).2:ℝ)
      ((ratLinePoint p q (t i.succ)).2:ℝ) := by
  have hs : t i.castSucc ∈ ratSegmentCuts p q := by
    rw [← hr]
    exact Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩
  have ht : t i.succ ∈ ratSegmentCuts p q := by
    rw [← hr]
    exact Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, rfl⟩
  have hst : t i.castSucc < t i.succ := hm Fin.castSucc_lt_succ
  have hadj := ratSegmentCuts_no_cut_between p q hm hr i
  constructor
  · apply sameAxisCell_rat_of_no_kink
    intro r hrk
    by_cases hdiff : p.1 = q.1
    · simp [ratLinePoint, ← hdiff]
      exact fun h => h.le
    · exact ratSegmentCuts_no_vertical_kink p q
        (t i.castSucc) (t i.succ) r hs ht hst hadj hrk hdiff
  · apply sameAxisCell_rat_of_no_kink
    intro r hrk
    by_cases hdiff : p.2 = q.2
    · simp [ratLinePoint, ← hdiff]
      exact fun h => h.le
    · exact ratSegmentCuts_no_horizontal_kink p q
        (t i.castSucc) (t i.succ) r hs ht hst hadj hrk hdiff

theorem inwardMap_affine_on_cells (a : ℝ) (z w : ℂ)
    (hre : SameAxisCell z.re w.re) (him : SameAxisCell z.im w.im)
    {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    inwardMap a (LQGMetric.LFPP.segPath z w u) =
      LQGMetric.LFPP.segPath (inwardMap a z) (inwardMap a w) u := by
  apply Complex.ext
  · have h := inwardAxis_affine_on_cell a z.re w.re u hre hu
    simpa [inwardMap_re, LQGMetric.LFPP.segPath, Complex.add_re,
      Complex.sub_re, Complex.smul_re, smul_eq_mul] using h
  · have h := inwardAxis_affine_on_cell a z.im w.im u him hu
    simpa [inwardMap_im, LQGMetric.LFPP.segPath, Complex.add_im,
      Complex.sub_im, Complex.smul_im, smul_eq_mul] using h

theorem inwardMap_affine_between_cuts (a : ℝ) (p q : ℚ × ℚ)
    {n : ℕ} {t : Fin (n+1) → ℚ} (hm : StrictMono t)
    (hr : Finset.univ.image t = ratSegmentCuts p q) (i : Fin n)
    {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    inwardMap a (LQGMetric.LFPP.segPath
      (ratComplex (ratLinePoint p q (t i.castSucc)))
      (ratComplex (ratLinePoint p q (t i.succ))) u) =
    LQGMetric.LFPP.segPath
      (inwardMap a (ratComplex (ratLinePoint p q (t i.castSucc))))
      (inwardMap a (ratComplex (ratLinePoint p q (t i.succ)))) u := by
  have hc := ratSegmentCuts_adjacent_sameCell p q hm hr i
  apply inwardMap_affine_on_cells a _ _
  · simpa [ratComplex] using hc.1
  · simpa [ratComplex] using hc.2
  · exact hu


end SupercriticalLQGUniqueness.Exponent.InwardMap
