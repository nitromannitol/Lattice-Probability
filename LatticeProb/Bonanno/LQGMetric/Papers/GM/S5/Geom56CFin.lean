/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56CFin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CPlan
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CPaths
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56Main

/-!
# GM Lemma 5.6: the tube `V_r(z)` from the paths `π±` (task P2-M2L56b)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6, l. 2963–2989,
with the corridors of decision D69 and condition (2) of decision D77.

`l56ConstrN_of_paths : L56Paths → L56ConstrN`. Given GM's paths `π₋ ∋ z − 2r, z` and
`π₊ ∋ v', z + 2r` (`L56Paths`, GM l. 2963–2966), the tube is the interior of the union of
* the grid corridor `C_u` at `u` (axis within `45°` of the outward normal, D69) and the squares
  meeting `P_u = π₋ ∪ [z, c_u]` (GM's `π₋ ∪ L₋`, with `L₋` rerouted through `C_u`),
* the squares meeting `T` (GM's `P̃`, which lies in `cl H`),
* the grid corridor `C_v` at `v` and the squares meeting `P_v = π₊ ∪ [c_v, v']` (GM's `L₊ ∪ π₊`).
All squares meet `cl B_{2r}(z)`; the tube is connected (`tube_isPreconnected`), contains
`z ± 2r` and `T`, and condition (2) at `u` and at `v` follows from `sepDiscNear_side` (GM
l. 2982–2989) with the planar distance estimates of `corrU_facts`, `corrV_facts` and `L56Paths`.
Constants: `b₁ = min (1 − α) (1/200)`, `ε' = min (1/30000) (min (b/1000) ((1 − α)/1000))`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

lemma dist_add_two_mul {z : ℂ} {r : ℝ} (hr : 0 < r) : dist (z + 2 * (r : ℂ)) z = 2 * r := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  norm_num

lemma dist_sub_two_mul {z : ℂ} {r : ℝ} (hr : 0 < r) : dist (z - 2 * (r : ℂ)) z = 2 * r := by
  rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr.le]
  norm_num

set_option maxHeartbeats 1000000 in
/-- **GM Lemma 5.6, construction of the tube**: `L56Paths` implies `L56ConstrN` -/
theorem l56ConstrN_of_paths (hpaths : L56Paths) : L56ConstrN := by
  intro α hα1 hα2
  obtain ⟨b, hb, hP⟩ := hpaths α hα1 hα2
  refine ⟨min (1 - α) (1 / 200), min (1 / 30000) (min (b / 1000) ((1 - α) / 1000)),
    ⟨lt_min (by linarith) (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩,
    min_le_left _ _, lt_min (by norm_num) (lt_min (by positivity) (by linarith)), ?_⟩
  intro ε₁ hε₁ z r hr H hH u hu v hv T hT hTc huT hvT
  have hε0 := hε₁.1
  have hε1 : ε₁ < 1 / 30000 := hε₁.2.trans_le (min_le_left _ _)
  have hε2 : ε₁ < b / 1000 := hε₁.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε₁ < (1 - α) / 1000 :=
    hε₁.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have e20 : 20 * ε₁ * r = 20 * (ε₁ * r) := by ring
  rw [e20]
  set s := ε₁ * r with hsdef
  have hs : 0 < s := mul_pos hε0 hr
  have hs1 : 30000 * s ≤ r := by rw [hsdef]; nlinarith
  have hs2 : 1000 * s ≤ b * r := by rw [hsdef]; nlinarith
  have hs3 : 1000 * s ≤ (1 - α) * r := by rw [hsdef]; nlinarith
  have hαr : 20000 * s ≤ α * r := by nlinarith
  have hrs : 20000 * s ≤ r := by linarith
  have huz : dist u z = α * r := mem_sphere.1 hu
  have hvz : dist v z = r := mem_sphere.1 hv
  have hclH : ∀ h ∈ closure H, α * r ≤ dist h z ∧ dist h z ≤ r := fun h hh => by
    rw [dist_eq_norm]; exact closure_halfAnnulus_subset hH hh
  have huH := hT huT
  have hvH := hT hvT
  obtain ⟨Pm, Pp, hPm, hPp, hPmB, hPpB, hzm, hz0, hv'P, hzp, hdH, hdmp⟩ :=
    hP z r hr H hH u hu v hv huH hvH
  set v' : ℂ := z + (3 / 2 : ℂ) * (v - z) with hv'def
  -- the axes and the corridors
  have hu0 : u - z ≠ 0 := by
    intro h; rw [dist_eq_norm, h, norm_zero] at huz; nlinarith
  have hv0 : -(v - z) ≠ 0 := by
    intro h; rw [neg_eq_zero] at h; rw [dist_eq_norm, h, norm_zero] at hvz; linarith
  obtain ⟨eu, heu, heu7⟩ := exists_axis' hu0
  obtain ⟨ev, hev, hev7⟩ := exists_axis' hv0
  have heu1 := norm_axis heu
  have hev1 := norm_axis hev
  rw [← dist_eq_norm, huz] at heu7
  rw [norm_neg, ← dist_eq_norm, hvz, neg_mul, Complex.neg_re] at hev7
  have hev7' : ((v - z) * (starRingEnd ℂ) ev).re ≤ -(7 / 10 * r) := by linarith
  obtain ⟨cu, Fcu, hcu, hξu1, hξu2, hηu⟩ := exists_corridor hs u eu heu
  obtain ⟨cv, Fcv, hcv, hξv1, hξv2, hηv⟩ := exists_corridor hs v ev hev
  obtain ⟨huR, hcuR⟩ := corr_mem hs hξu1 hξu2 hηu
  obtain ⟨hvR, hcvR⟩ := corr_mem hs hξv1 hξv2 hηv
  have Cu1 : ∀ x ∈ rectC cu eu (50 * s) (2 * s), dist x u ≤ 104 * s :=
    fun x hx => corr_near heu1 huR hx
  have Cv1 : ∀ x ∈ rectC cv ev (50 * s) (2 * s), dist x v ≤ 104 * s :=
    fun x hx => corr_near hev1 hvR hx
  obtain ⟨Cu2, Cu3⟩ := corrU_facts hs hαr heu1 huz heu7 hξu1 hξu2 hηu
  obtain ⟨Cv3, SegV⟩ := corrV_facts hs hrs hev1 hvz hev7' hξv1 hξv2 hηv
  have hcuu : dist cu u ≤ 104 * s := Cu1 cu hcuR
  have hcvv : dist cv v ≤ 104 * s := Cv1 cv hcvR
  have SegU : ∀ p ∈ segment ℝ z cu, dist p z ≤ α * r - 25 * s := by
    intro p hp
    have := (convex_closedBall z (α * r - 25 * s)).segment_subset
      (mem_closedBall_self (by linarith)) (mem_closedBall.2 Cu2) hp
    exact mem_closedBall.1 this
  have NearU : ∀ p ∈ segment ℝ z cu, ∃ p' ∈ segment ℝ z u, dist p p' ≤ 104 * s := by
    intro p hp
    rw [segment_symm] at hp
    obtain ⟨p', hp', hd⟩ := segment_near (a' := u) hp
    exact ⟨p', by rwa [segment_symm], hd.trans hcuu⟩
  have NearV : ∀ q ∈ segment ℝ cv v', ∃ q' ∈ segment ℝ v v', dist q q' ≤ 104 * s := by
    intro q hq
    obtain ⟨q', hq', hd⟩ := segment_near (a' := v) hq
    exact ⟨q', hq', hd.trans hcvv⟩
  -- the sets `P_u`, `P_v`
  set Pu := Pm ∪ segment ℝ z cu with hPudef
  set Pv := Pp ∪ segment ℝ cv v' with hPvdef
  have hPu : IsPreconnected Pu :=
    hPm.union' ⟨z, hz0, left_mem_segment ℝ z cu⟩ (convex_segment z cu).isPreconnected
  have hPv : IsPreconnected Pv :=
    hPp.union' ⟨v', hv'P, right_mem_segment ℝ cv v'⟩ (convex_segment cv v').isPreconnected
  have hPuB : Pu ⊆ closedBall z (2 * r) := by
    rintro p (hp | hp)
    · exact hPmB hp
    · rw [mem_closedBall]; have := SegU p hp; nlinarith
  have hv'z : dist v' z = 3 / 2 * r := by
    rw [hv'def, dist_eq_norm, add_sub_cancel_left, norm_mul, ← dist_eq_norm, hvz]; norm_num
  have hPvB : Pv ⊆ closedBall z (2 * r) := by
    rintro q (hq | hq)
    · exact hPpB hq
    · refine (convex_closedBall z (2 * r)).segment_subset ?_ ?_ hq
      · rw [mem_closedBall]; have := dist_triangle cv v z; linarith
      · rw [mem_closedBall, hv'z]; linarith
  have hTB : T ⊆ closedBall z (2 * r) := fun t ht => by
    rw [mem_closedBall]; have := (hclH t (hT ht)).2; linarith
  have hzm2 : z - 2 * (r : ℂ) ∈ Pu := Or.inl hzm
  have hzp2 : z + 2 * (r : ℂ) ∈ Pv := Or.inl hzp
  have hd2p := dist_add_two_mul (z := z) hr
  have hd2m := dist_sub_two_mul (z := z) hr
  set FT := sqF s r z T with hFTdef
  set F := Fcu ∪ sqF s r z Pu ∪ (Fcv ∪ sqF s r z Pv ∪ FT) with hFdef
  have hF' : F = Fcv ∪ sqF s r z Pv ∪ (Fcu ∪ sqF s r z Pu ∪ FT) := by
    rw [hFdef]; ext m; simp only [Finset.mem_union]
    constructor <;> rintro ((h | h) | (h | h) | h) <;> simp only [h, true_or, or_true]
  -- condition (2) at `u`
  have hsepU : SepDiscNear (tubeOf s F) (20 * s) u (z - 2 * r) (z + 2 * r) s := by
    refine sepDiscNear_side (Y := rectC cv ev (50 * s) (2 * s) ∪
      {y | ∃ q ∈ Pv, dist y q ≤ 3 * s} ∪ {y | ∃ h ∈ T, dist y h ≤ 3 * s}) hs hr heu1 hcu hξu1
      hξu2 hηu hPu hPuB hzm2 (Or.inr (right_mem_segment ℝ z cu)) ?_ ?_ ?_ ?_ ?_ ?_
    · intro y hy
      rw [mem_iUnion₂] at hy
      obtain ⟨m, hm, hym⟩ := hy
      simp only [Finset.mem_union] at hm
      rcases hm with (hm | hm) | hm
      · exact Or.inl (Or.inl (hcv ▸ mem_biUnion hm hym))
      · exact Or.inl (Or.inr (exists_near_of_mem_sq hs ((mem_sqF hs hr hPvB).1 hm) hym))
      · exact Or.inr (exists_near_of_mem_sq hs ((mem_sqF hs hr hTB).1 hm) hym)
    · intro x hx hxu y hy
      have hxz := Cu3 x hx hxu
      have hxu' := Cu1 x hx
      rcases hy with (hy | ⟨q, hq, hyq⟩) | ⟨h, hh, hyh⟩
      · have := Cv1 y hy
        linarith [dist_triangle v y z, dist_triangle y x z, dist_comm x y, dist_comm v y]
      · rcases hq with hq | hq
        · have := hdH q (Or.inr hq) u huH
          linarith [dist_triangle q y u, dist_triangle y x u, dist_comm q y, dist_comm x y]
        · have := (SegV q hq).1
          linarith [dist_triangle q y z, dist_triangle y x z, dist_comm q y, dist_comm x y]
      · have := (hclH h (hT hh)).1
        linarith [dist_triangle h y z, dist_triangle y x z, dist_comm h y, dist_comm x y]
    · intro p hp y hy
      rcases hp with hp | hp
      · rcases hy with (hy | ⟨q, hq, hyq⟩) | ⟨h, hh, hyh⟩
        · have := Cv1 y hy
          have := hdH p (Or.inl hp) v hvH
          linarith [dist_triangle p y v]
        · rcases hq with hq | hq
          · have := hdmp p (Or.inl hp) q (Or.inl hq)
            linarith [dist_triangle p y q]
          · obtain ⟨q', hq', hqq'⟩ := NearV q hq
            have := hdmp p (Or.inl hp) q' (Or.inr hq')
            linarith [dist_triangle p y q', dist_triangle y q q']
        · have := hdH p (Or.inl hp) h (hT hh)
          linarith [dist_triangle p y h]
      · have hpz := SegU p hp
        rcases hy with (hy | ⟨q, hq, hyq⟩) | ⟨h, hh, hyh⟩
        · have := Cv1 y hy
          linarith [dist_triangle v y z, dist_triangle y p z, dist_comm p y, dist_comm v y]
        · rcases hq with hq | hq
          · obtain ⟨p', hp', hpp'⟩ := NearU p hp
            have := hdmp p' (Or.inr hp') q (Or.inl hq)
            linarith [dist_triangle p' p q, dist_triangle p y q, dist_comm p' p]
          · have := (SegV q hq).1
            linarith [dist_triangle q y z, dist_triangle y p z, dist_comm q y, dist_comm p y]
        · have := (hclH h (hT hh)).1
          linarith [dist_triangle h y z, dist_triangle y p z, dist_comm h y, dist_comm p y]
    · rintro p (hp | hp)
      · have := hdH p (Or.inl hp) u huH; linarith
      · have := SegU p hp; linarith [dist_triangle u p z, dist_comm u p]
    · intro h
      have := Cu1 _ h
      have := hdH _ (Or.inr hzp) u huH
      linarith
    · rintro p (hp | hp)
      · have := hdmp p (Or.inl hp) _ (Or.inl hzp); linarith
      · have := SegU p hp
        linarith [dist_triangle (z + 2 * (r : ℂ)) p z, dist_comm p (z + 2 * (r : ℂ))]
  -- condition (2) at `v`
  have hsepV : SepDiscNear (tubeOf s F) (20 * s) v (z + 2 * r) (z - 2 * r) s := by
    rw [hF']
    refine sepDiscNear_side (Y := rectC cu eu (50 * s) (2 * s) ∪
      {y | ∃ p ∈ Pu, dist y p ≤ 3 * s} ∪ {y | ∃ h ∈ T, dist y h ≤ 3 * s}) hs hr hev1 hcv hξv1
      hξv2 hηv hPv hPvB hzp2 (Or.inr (left_mem_segment ℝ cv v')) ?_ ?_ ?_ ?_ ?_ ?_
    · intro y hy
      rw [mem_iUnion₂] at hy
      obtain ⟨m, hm, hym⟩ := hy
      simp only [Finset.mem_union] at hm
      rcases hm with (hm | hm) | hm
      · exact Or.inl (Or.inl (hcu ▸ mem_biUnion hm hym))
      · exact Or.inl (Or.inr (exists_near_of_mem_sq hs ((mem_sqF hs hr hPuB).1 hm) hym))
      · exact Or.inr (exists_near_of_mem_sq hs ((mem_sqF hs hr hTB).1 hm) hym)
    · intro x hx hxv y hy
      have hxz := Cv3 x hx hxv
      have hxv' := Cv1 x hx
      rcases hy with (hy | ⟨p, hp, hyp⟩) | ⟨h, hh, hyh⟩
      · have := Cu1 y hy
        linarith [dist_triangle y u z, dist_triangle x y z]
      · rcases hp with hp | hp
        · have := hdH p (Or.inl hp) v hvH
          linarith [dist_triangle p y v, dist_triangle y x v, dist_comm p y, dist_comm x y]
        · have := SegU p hp
          linarith [dist_triangle x y z, dist_triangle y p z]
      · have := (hclH h (hT hh)).2
        linarith [dist_triangle x y z, dist_triangle y h z]
    · intro q hq y hy
      rcases hq with hq | hq
      · rcases hy with (hy | ⟨p, hp, hyp⟩) | ⟨h, hh, hyh⟩
        · have := Cu1 y hy
          have := hdH q (Or.inr hq) u huH
          linarith [dist_triangle q y u]
        · rcases hp with hp | hp
          · have := hdmp p (Or.inl hp) q (Or.inl hq)
            linarith [dist_triangle p y q, dist_comm p y, dist_comm q y]
          · obtain ⟨p', hp', hpp'⟩ := NearU p hp
            have := hdmp p' (Or.inr hp') q (Or.inl hq)
            linarith [dist_triangle p' p q, dist_triangle p y q, dist_comm p' p, dist_comm p y,
              dist_comm q y]
        · have := hdH q (Or.inr hq) h (hT hh)
          linarith [dist_triangle q y h]
      · have hqz := (SegV q hq).1
        rcases hy with (hy | ⟨p, hp, hyp⟩) | ⟨h, hh, hyh⟩
        · have := Cu1 y hy
          linarith [dist_triangle q y z, dist_triangle y u z]
        · rcases hp with hp | hp
          · obtain ⟨q', hq', hqq'⟩ := NearV q hq
            have := hdmp p (Or.inl hp) q' (Or.inr hq')
            linarith [dist_triangle p y q', dist_triangle y q q', dist_comm p y, dist_comm q y]
          · have := SegU p hp
            linarith [dist_triangle q y z, dist_triangle y p z]
        · have := (hclH h (hT hh)).2
          linarith [dist_triangle q y z, dist_triangle y h z]
    · rintro q (hq | hq)
      · have := hdH q (Or.inr hq) v hvH; linarith
      · have := (SegV q hq).2; linarith
    · intro h
      have := Cv1 _ h
      have := hdH _ (Or.inl hzm) v hvH
      linarith
    · rintro q (hq | hq)
      · have := hdmp _ (Or.inl hzm) q (Or.inl hq); rw [dist_comm] at this; linarith
      · obtain ⟨q', hq', hqq'⟩ := NearV q hq
        have := hdmp _ (Or.inl hzm) q' (Or.inr hq')
        linarith [dist_triangle (z - 2 * (r : ℂ)) q q', dist_comm (z - 2 * (r : ℂ)) q]
  -- the global properties
  have hsubF : ∀ {G : Finset (ℤ × ℤ)}, G ⊆ F → ∀ {X : Set ℂ}, X ⊆ closedBall z (2 * r) →
      sqF s r z X ⊆ G → X ⊆ tubeOf s F :=
    fun hG _ hX hXG => subset_tubeOf_of_sqF hs hr hX (hXG.trans hG)
  have hFsq : (↑F : Set (ℤ × ℤ)) ⊆ squareSet s (closedBall z (2 * r)) := by
    intro m hm
    simp only [hFdef, Finset.coe_union, Set.mem_union, Finset.mem_coe] at hm
    have hcorner : (⟨m.1 * s, m.2 * s⟩ : ℂ) ∈ gridSquare s m :=
      ⟨le_rfl, by linarith, le_rfl, by linarith⟩
    rcases hm with (hm | hm) | (hm | hm) | hm
    · refine ⟨_, hcorner, ?_⟩
      have := Cu1 _ (hcu ▸ mem_biUnion hm hcorner)
      rw [mem_closedBall]; linarith [dist_triangle (⟨m.1 * s, m.2 * s⟩ : ℂ) u z]
    · exact squareSet_mono s hPuB ((mem_sqF hs hr hPuB).1 hm)
    · refine ⟨_, hcorner, ?_⟩
      have := Cv1 _ (hcv ▸ mem_biUnion hm hcorner)
      rw [mem_closedBall]; linarith [dist_triangle (⟨m.1 * s, m.2 * s⟩ : ℂ) v z]
    · exact squareSet_mono s hPvB ((mem_sqF hs hr hPvB).1 hm)
    · exact squareSet_mono s hTB ((mem_sqF hs hr hTB).1 hm)
  have hFpu : sqF s r z Pu ⊆ F := fun m hm => by simp [hFdef, hm]
  have hFpv : sqF s r z Pv ⊆ F := fun m hm => by simp [hFdef, hm]
  have hFT : FT ⊆ F := fun m hm => by simp [hFdef, hm]
  have hzmV : z - 2 * (r : ℂ) ∈ tubeOf s F := hsubF hFpu hPuB subset_rfl hzm2
  have huO : u ∈ interior (rectC cu eu (50 * s) (2 * s)) :=
    rectO_subset_interior _ _ _ _ ⟨abs_lt.2 ⟨by linarith, by linarith⟩,
      abs_lt.2 ⟨by linarith [(abs_le.1 hηu).1], by linarith [(abs_le.1 hηu).2]⟩⟩
  have hvO : v ∈ interior (rectC cv ev (50 * s) (2 * s)) :=
    rectO_subset_interior _ _ _ _ ⟨abs_lt.2 ⟨by linarith, by linarith⟩,
      abs_lt.2 ⟨by linarith [(abs_le.1 hηv).1], by linarith [(abs_le.1 hηv).2]⟩⟩
  refine ⟨F, hFsq, ⟨⟨_, hzmV⟩, tube_isPreconnected hs hr hcu hcv (convex_rectC _ _ _ _)
    (convex_rectC _ _ _ _) ⟨u, huO⟩ ⟨v, hvO⟩ hPu hPv hTc.isPreconnected hPuB hPvB hTB
    (Or.inr (right_mem_segment ℝ z cu)) hcuR (Or.inr (left_mem_segment ℝ cv v')) hcvR huR huT
    hvR hvT⟩, ?_, hzmV, hsubF hFpv hPvB subset_rfl hzp2, hsubF hFT hTB subset_rfl,
    hsepU, hsepV⟩
  intro x hx
  obtain ⟨m, hm, hxm⟩ := mem_tubeOf_exists hx
  obtain ⟨w, hwm, hwB⟩ := hFsq hm
  have := dist_lt_two_of_mem_sq hs hxm hwm
  rw [mem_closedBall] at hwB
  rw [mem_ball]
  have : 2 * s = 2 * ε₁ * r := by rw [hsdef]; ring
  nlinarith [dist_triangle x w z]

/-- **GM Lemma 5.6, deterministic node**: `L56Paths` implies `L56GeomN` -/
theorem l56GeomN_of_paths (hpaths : L56Paths) : L56GeomN :=
  l56GeomN_of_constr (l56ConstrN_of_paths hpaths)

end LQGMetric.GM
