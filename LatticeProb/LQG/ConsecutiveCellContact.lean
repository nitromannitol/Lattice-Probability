import LatticeProb.LQG.ContactWindowComponentOneSidedCount

/-! # Contact paths of two consecutive cells

For the contour pair `(L, R)` of a Peanosphere and a time `t`, the paths
`level ↦ η (ellMinus t level)` and `level ↦ η (rhoMinus t level)` of last left and right
contacts are continuous up to and including the top level `L_t`, respectively `R_t`, where
they take the value `η t`.

For two consecutive cells `η([ε(x-1), εx])` and `η([εx, ε(x+1)])`, every last left contact
before `εx` at a level of the left window `(max(inf L on the two cells), L_{εx}]` lies in
both cells, and likewise on the right. Consequently, for the curve of a mating-of-trees
coupling, almost surely for all meshes: if one of the two windows is strict, the connected
component of `η(εx)` in the intersection of the two cells is not a singleton and contains
every left and right window contact. If moreover every nonsingleton component meets an open
window image, this component is the only nonsingleton component.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.RouteM

variable {ω : MatedCRT.Path2} {η : ℝ → ℂ}

/-- The last time no later than `t` at which `L ≤ L_t` is `t` itself. -/
theorem ellMinus_self (t : ℝ) : ellMinus ω t (lCoord ω t) = t :=
  le_antisymm (csSup_le ⟨t, le_rfl, le_rfl⟩ fun _ hs => hs.1)
    (le_csSup ⟨t, fun _ hs => hs.1⟩ ⟨le_rfl, le_rfl⟩)

/-- The last time no later than `t` at which `R ≤ R_t` is `t` itself. -/
theorem rhoMinus_self (t : ℝ) : rhoMinus ω t (rCoord ω t) = t :=
  le_antisymm (csSup_le ⟨t, le_rfl, le_rfl⟩ fun _ hs => hs.1)
    (le_csSup ⟨t, fun _ hs => hs.1⟩ ⟨le_rfl, le_rfl⟩)

/-- The path of last left contacts is continuous up to the top level `L_t`. -/
theorem Peanosphere.continuousOn_eta_ellMinus_Iic (P : Peanosphere ω η) (t : ℝ) :
    ContinuousOn (fun level => η (ellMinus ω t level)) (Iic (lCoord ω t)) := by
  have hc : Continuous (fun level : ℝ =>
      shearedStripMap P (stripPoint t (level - lCoord ω t))) :=
    (shearedStripMap_continuous P).comp
      (continuous_stripPoint_pair.comp (continuous_const.prodMk (continuous_id.sub continuous_const)))
  apply hc.continuousOn.congr
  intro level hlevel
  change level ≤ lCoord ω t at hlevel
  rcases hlevel.lt_or_eq with hlt | heq
  · have hneg : level - lCoord ω t < 0 := sub_neg.mpr hlt
    simp only [shearedStripMap, stripPoint,
      not_le_of_gt hneg, false_and, ite_false, hneg, ite_true]
    congr 2
    ring
  · subst heq
    beta_reduce
    rw [sub_self, shearedStripMap_stripPoint_mid P le_rfl zero_le_one, ellMinus_self]

/-- The path of last right contacts is continuous up to the top level `R_t`. -/
theorem Peanosphere.continuousOn_eta_rhoMinus_Iic (P : Peanosphere ω η) (t : ℝ) :
    ContinuousOn (fun level => η (rhoMinus ω t level)) (Iic (rCoord ω t)) := by
  have hc : Continuous (fun level : ℝ =>
      shearedStripMap P (stripPoint t (1 + rCoord ω t - level))) :=
    (shearedStripMap_continuous P).comp
      (continuous_stripPoint_pair.comp
        (continuous_const.prodMk ((continuous_const.add continuous_const).sub continuous_id)))
  apply hc.continuousOn.congr
  intro level hlevel
  change level ≤ rCoord ω t at hlevel
  rcases hlevel.lt_or_eq with hlt | heq
  · have hpos : 0 ≤ 1 + rCoord ω t - level := by linarith
    have hlarge : ¬1 + rCoord ω t - level ≤ 1 := by linarith
    have hnonneg : ¬1 + rCoord ω t - level < 0 := not_lt_of_ge hpos
    simp only [shearedStripMap, stripPoint,
      hlarge, and_false, ite_false, hnonneg]
    congr 2
    ring
  · subst heq
    beta_reduce
    rw [add_sub_cancel_right, shearedStripMap_stripPoint_mid P zero_le_one le_rfl,
      rhoMinus_self]

/-- For consecutive cells, every last left contact before `εx` at a level of the left window,
closed at the top level `L_{εx}`, lies in both cells. -/
theorem Peanosphere.consecutive_left_contact_mem (P : Peanosphere ω η) {ε : ℝ} {x y : ℤ}
    (hε : 0 < ε) (hy : y = x + 1) {level : ℝ}
    (hlo : dWinLo ε (lCoord ω) x y < level) (hhi : level ≤ lCoord ω (ε * x)) :
    η (ellMinus ω (ε * x) level) ∈
      η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ η '' Icc (ε * ((y : ℝ) - 1)) (ε * y) := by
  have hy' : (y : ℝ) - 1 = x := by rw [hy]; push_cast; ring
  have hab : ε * ((x : ℝ) - 1) ≤ ε * x := by nlinarith
  have hbc : ε * (x : ℝ) ≤ ε * y := by rw [hy]; push_cast; nlinarith
  rw [hy']
  rw [dWinLo, max_lt_iff, hy'] at hlo
  obtain ⟨hlo1, hlo2⟩ := hlo
  rcases hhi.lt_or_eq with hlt | heq
  · obtain ⟨⟨u, hu, hLu⟩, -⟩ := DAux.intervalInf_spec continuous_lCoord hab
    obtain ⟨⟨v, hv, hLv⟩, -⟩ := DAux.intervalInf_spec continuous_lCoord hbc
    have hs := ellMinus_mem P (ε * x) level
    have hLs : lCoord ω (ellMinus ω (ε * x) level) = level := ellMinus_level P hlt
    have hf := ellPlus_mem P (ε * x) level
    have hLf : lCoord ω (ellPlus ω (ε * x) level) = level := ellPlus_level P hlt
    have hus : u ≤ ellMinus ω (ε * x) level :=
      le_csSup ⟨ε * x, fun _ h => h.1⟩ ⟨hu.2, (hLu.trans_lt hlo1).le⟩
    have hfv : ellPlus ω (ε * x) level ≤ v :=
      csInf_le ⟨ε * x, fun _ h => h.1⟩ ⟨hv.1, (hLv.trans_lt hlo2).le⟩
    have hbf : ε * x < ellPlus ω (ε * x) level := by
      refine lt_of_le_of_ne hf.1 fun h => ?_
      rw [← h] at hLf
      exact absurd hLf (ne_of_gt hlt)
    have hdir : directRel (fun u => (ω u).1) (ellMinus ω (ε * x) level)
        (ellPlus ω (ε * x) level) := by
      refine ⟨lt_of_le_of_lt hs.1 hbf, hLs.trans hLf.symm, ?_⟩
      intro w hw
      change lCoord ω (ellMinus ω (ε * x) level) < lCoord ω w
      rw [hLs]
      by_contra hle
      rw [not_lt] at hle
      rcases le_or_gt w (ε * x) with hwb | hbw
      · have : w ≤ ellMinus ω (ε * x) level := le_csSup ⟨ε * x, fun _ h => h.1⟩ ⟨hwb, hle⟩
        exact (not_lt.mpr this) hw.1
      · have : ellPlus ω (ε * x) level ≤ w := csInf_le ⟨ε * x, fun _ h => h.1⟩ ⟨hbw.le, hle⟩
        exact (not_lt.mpr this) hw.2
    exact ⟨⟨_, ⟨hu.1.trans hus, hs.1⟩, rfl⟩,
      ⟨_, ⟨hf.1, hfv.trans hv.2⟩, (P.merge _ _ (Or.inl hdir)).symm⟩⟩
  · rw [heq, ellMinus_self]
    exact ⟨⟨_, ⟨hab, le_rfl⟩, rfl⟩, ⟨_, ⟨le_rfl, hbc⟩, rfl⟩⟩

/-- For consecutive cells, every last right contact before `εx` at a level of the right
window, closed at the top level `R_{εx}`, lies in both cells. -/
theorem Peanosphere.consecutive_right_contact_mem (P : Peanosphere ω η) {ε : ℝ} {x y : ℤ}
    (hε : 0 < ε) (hy : y = x + 1) {level : ℝ}
    (hlo : dWinLo ε (rCoord ω) x y < level) (hhi : level ≤ rCoord ω (ε * x)) :
    η (rhoMinus ω (ε * x) level) ∈
      η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ η '' Icc (ε * ((y : ℝ) - 1)) (ε * y) := by
  have hy' : (y : ℝ) - 1 = x := by rw [hy]; push_cast; ring
  have hab : ε * ((x : ℝ) - 1) ≤ ε * x := by nlinarith
  have hbc : ε * (x : ℝ) ≤ ε * y := by rw [hy]; push_cast; nlinarith
  rw [hy']
  rw [dWinLo, max_lt_iff, hy'] at hlo
  obtain ⟨hlo1, hlo2⟩ := hlo
  rcases hhi.lt_or_eq with hlt | heq
  · obtain ⟨⟨u, hu, hLu⟩, -⟩ := DAux.intervalInf_spec continuous_rCoord hab
    obtain ⟨⟨v, hv, hLv⟩, -⟩ := DAux.intervalInf_spec continuous_rCoord hbc
    have hs := rhoMinus_mem P (ε * x) level
    have hLs : rCoord ω (rhoMinus ω (ε * x) level) = level := rhoMinus_level P hlt
    have hf := rhoPlus_mem P (ε * x) level
    have hLf : rCoord ω (rhoPlus ω (ε * x) level) = level := rhoPlus_level P hlt
    have hus : u ≤ rhoMinus ω (ε * x) level :=
      le_csSup ⟨ε * x, fun _ h => h.1⟩ ⟨hu.2, (hLu.trans_lt hlo1).le⟩
    have hfv : rhoPlus ω (ε * x) level ≤ v :=
      csInf_le ⟨ε * x, fun _ h => h.1⟩ ⟨hv.1, (hLv.trans_lt hlo2).le⟩
    have hbf : ε * x < rhoPlus ω (ε * x) level := by
      refine lt_of_le_of_ne hf.1 fun h => ?_
      rw [← h] at hLf
      exact absurd hLf (ne_of_gt hlt)
    have hdir : directRel (fun u => (ω u).2) (rhoMinus ω (ε * x) level)
        (rhoPlus ω (ε * x) level) := by
      refine ⟨lt_of_le_of_lt hs.1 hbf, hLs.trans hLf.symm, ?_⟩
      intro w hw
      change rCoord ω (rhoMinus ω (ε * x) level) < rCoord ω w
      rw [hLs]
      by_contra hle
      rw [not_lt] at hle
      rcases le_or_gt w (ε * x) with hwb | hbw
      · have : w ≤ rhoMinus ω (ε * x) level := le_csSup ⟨ε * x, fun _ h => h.1⟩ ⟨hwb, hle⟩
        exact (not_lt.mpr this) hw.1
      · have : rhoPlus ω (ε * x) level ≤ w := csInf_le ⟨ε * x, fun _ h => h.1⟩ ⟨hbw.le, hle⟩
        exact (not_lt.mpr this) hw.2
    exact ⟨⟨_, ⟨hu.1.trans hus, hs.1⟩, rfl⟩,
      ⟨_, ⟨hf.1, hfv.trans hv.2⟩, (P.merge _ _ (Or.inr hdir)).symm⟩⟩
  · rw [heq, rhoMinus_self]
    exact ⟨⟨_, ⟨hab, le_rfl⟩, rfl⟩, ⟨_, ⟨le_rfl, hbc⟩, rfl⟩⟩

/-- For consecutive cells the upper end of a contact window is the value at `εx`. -/
theorem dWinHi_consecutive {X : ℝ → ℝ} (hX : Continuous X) {ε : ℝ} {x y : ℤ}
    (hy : y = x + 1) : dWinHi ε X x y = X (ε * x) := by
  have hy' : (y : ℝ) - 1 = x := by rw [hy]; push_cast; ring
  obtain ⟨⟨s, hs, hXs⟩, -⟩ := DAux.intervalInf_spec hX (le_refl (ε * (x : ℝ)))
  rw [dWinHi, hy', ← hXs, le_antisymm hs.2 hs.1]

end MatedCRTHarmonic.RouteM

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Almost surely, for all meshes and consecutive cells with at least one strict contact
window, the component of `η(εx)` in the intersection of the two cells is not a singleton and
contains every left and right window contact. -/
theorem ae_consecutive_contact_component
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ), 0 < ε → y = x + 1 →
      (dWinLo ε (lCoord (bm ω)) x y < lCoord (bm ω) (ε * x) ∨
        dWinLo ε (rCoord (bm ω)) x y < rCoord (bm ω) (ε * x)) →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      ∃ C ∈ LatticeProb.nonSingletonComponents S, η ω (ε * x) ∈ C ∧
        (∀ level ∈ Ioc (dWinLo ε (lCoord (bm ω)) x y) (lCoord (bm ω) (ε * x)),
          η ω (ellMinus (bm ω) (ε * x) level) ∈ C) ∧
        (∀ level ∈ Ioc (dWinLo ε (rCoord (bm ω)) x y) (rCoord (bm ω) (ε * x)),
          η ω (rhoMinus (bm ω) (ε * x) level) ∈ C) := by
  filter_upwards [ae_peanosphere D, GMS4c.ae_bundle_finite_quantum_visits D] with ω hP hfinite
  intro ε x y hε hy hstrict S
  have hy' : (y : ℝ) - 1 = x := by rw [hy]; push_cast; ring
  have hab : ε * ((x : ℝ) - 1) ≤ ε * x := by nlinarith
  have hbc : ε * (x : ℝ) ≤ ε * y := by rw [hy]; push_cast; nlinarith
  have hz : η ω (ε * x) ∈ S :=
    ⟨⟨_, ⟨hab, le_rfl⟩, rfl⟩, ⟨_, ⟨by rw [hy'], hbc⟩, rfl⟩⟩
  have hL : ∀ level ∈ Ioc (dWinLo ε (lCoord (bm ω)) x y) (lCoord (bm ω) (ε * x)),
      η ω (ellMinus (bm ω) (ε * x) level) ∈ connectedComponentIn S (η ω (ε * x)) := by
    intro level hl
    have hpre : IsPreconnected ((fun l => η ω (ellMinus (bm ω) (ε * x) l)) ''
        Icc level (lCoord (bm ω) (ε * x))) :=
      isPreconnected_Icc.image _ ((hP.continuousOn_eta_ellMinus_Iic _).mono
        fun l hl' => hl'.2)
    refine hpre.subset_connectedComponentIn ?_ ?_ ⟨level, ⟨le_rfl, hl.2⟩, rfl⟩
    · refine ⟨lCoord (bm ω) (ε * x), ⟨hl.2, le_rfl⟩, ?_⟩
      simp only [ellMinus_self]
    · rintro _ ⟨l, hl', rfl⟩
      exact hP.consecutive_left_contact_mem hε hy (hl.1.trans_le hl'.1) hl'.2
  have hR : ∀ level ∈ Ioc (dWinLo ε (rCoord (bm ω)) x y) (rCoord (bm ω) (ε * x)),
      η ω (rhoMinus (bm ω) (ε * x) level) ∈ connectedComponentIn S (η ω (ε * x)) := by
    intro level hl
    have hpre : IsPreconnected ((fun l => η ω (rhoMinus (bm ω) (ε * x) l)) ''
        Icc level (rCoord (bm ω) (ε * x))) :=
      isPreconnected_Icc.image _ ((hP.continuousOn_eta_rhoMinus_Iic _).mono
        fun l hl' => hl'.2)
    refine hpre.subset_connectedComponentIn ?_ ?_ ⟨level, ⟨le_rfl, hl.2⟩, rfl⟩
    · refine ⟨rCoord (bm ω) (ε * x), ⟨hl.2, le_rfl⟩, ?_⟩
      simp only [rhoMinus_self]
    · rintro _ ⟨l, hl', rfl⟩
      exact hP.consecutive_right_contact_mem hε hy (hl.1.trans_le hl'.1) hl'.2
  refine ⟨connectedComponentIn S (η ω (ε * x)), ⟨mem_image_of_mem _ hz, ?_⟩,
    mem_connectedComponentIn hz, hL, hR⟩
  intro hsub
  rcases hstrict with hl | hr
  · obtain ⟨m, hm1, hm2⟩ := exists_between hl
    obtain ⟨m', hm'1, hm'2⟩ := exists_between hm2
    have hinf : ((fun l => η ω (ellMinus (bm ω) (ε * x) l)) '' Icc m m').Infinite := by
      intro hfin
      have htimes : (η ω ⁻¹' ((fun l => η ω (ellMinus (bm ω) (ε * x) l)) ''
          Icc m m')).Finite := hfin.preimage' (fun z _ => hfinite z)
      apply (Set.Icc_infinite hm'1) ((htimes.image (lCoord (bm ω))).subset ?_)
      intro l hl'
      exact ⟨ellMinus (bm ω) (ε * x) l, ⟨l, hl', rfl⟩,
        ellMinus_level hP (hl'.2.trans_lt hm'2)⟩
    exact hinf (hsub.anti (by
      rintro _ ⟨l, hl', rfl⟩
      exact hL l ⟨hm1.trans_le hl'.1, hl'.2.trans hm'2.le⟩)).finite
  · obtain ⟨m, hm1, hm2⟩ := exists_between hr
    obtain ⟨m', hm'1, hm'2⟩ := exists_between hm2
    have hinf : ((fun l => η ω (rhoMinus (bm ω) (ε * x) l)) '' Icc m m').Infinite := by
      intro hfin
      have htimes : (η ω ⁻¹' ((fun l => η ω (rhoMinus (bm ω) (ε * x) l)) ''
          Icc m m')).Finite := hfin.preimage' (fun z _ => hfinite z)
      apply (Set.Icc_infinite hm'1) ((htimes.image (rCoord (bm ω))).subset ?_)
      intro l hl'
      exact ⟨rhoMinus (bm ω) (ε * x) l, ⟨l, hl', rfl⟩,
        rhoMinus_level hP (hl'.2.trans_lt hm'2)⟩
    exact hinf (hsub.anti (by
      rintro _ ⟨l, hl', rfl⟩
      exact hR l ⟨hm1.trans_le hl'.1, hl'.2.trans hm'2.le⟩)).finite

/-- Almost surely, for all meshes and consecutive cells with at least one strict contact
window: if every nonsingleton component of the intersection meets an open window image, the
intersection has exactly one nonsingleton component, the component of `η(εx)`. -/
theorem ae_consecutive_contact_components_count_one
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ), 0 < ε → y = x + 1 →
      (dWinLo ε (lCoord (bm ω)) x y < lCoord (bm ω) (ε * x) ∨
        dWinLo ε (rCoord (bm ω)) x y < rCoord (bm ω) (ε * x)) →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      (∀ C ∈ LatticeProb.nonSingletonComponents S,
        (C ∩ ((fun level => η ω (ellMinus (bm ω) (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord (bm ω)) x y) (dWinHi ε (lCoord (bm ω)) x y) ∪
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord (bm ω)) x y) (dWinHi ε (rCoord (bm ω)) x y))).Nonempty) →
      LatticeProb.nonSingletonComponents S = {connectedComponentIn S (η ω (ε * x))} ∧
        (LatticeProb.nonSingletonComponents S).ncard = 1 ∧
        (LatticeProb.nonSingletonComponents S).encard = 1 := by
  filter_upwards [ae_consecutive_contact_component D] with ω hcomp
  intro ε x y hε hy hstrict S hmeet
  obtain ⟨C, hC, hzC, hL, hR⟩ := hcomp ε x y hε hy hstrict
  have hCeq : C = connectedComponentIn S (η ω (ε * x)) := by
    obtain ⟨p, -, rfl⟩ := hC.1
    exact connectedComponentIn_eq hzC
  have hset : LatticeProb.nonSingletonComponents S = {connectedComponentIn S (η ω (ε * x))} := by
    ext E
    simp only [mem_singleton_iff]
    constructor
    · intro hE
      rw [← hCeq]
      obtain ⟨p, hpE, hp⟩ := hmeet E hE
      refine LatticeProb.eq_of_mem_connectedComponentIn_image_of_inter_nonempty hE.1 hC.1
        ⟨p, hpE, ?_⟩
      rcases hp with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
      · rw [dWinHi_consecutive continuous_lCoord hy] at hl
        exact hL l ⟨hl.1, hl.2.le⟩
      · rw [dWinHi_consecutive continuous_rCoord hy] at hl
        exact hR l ⟨hl.1, hl.2.le⟩
    · rintro rfl
      rw [← hCeq]
      exact hC
  refine ⟨hset, ?_, ?_⟩
  · rw [hset, ncard_singleton]
  · rw [hset, encard_singleton]

end MatedCRTHarmonic.MoTInput
