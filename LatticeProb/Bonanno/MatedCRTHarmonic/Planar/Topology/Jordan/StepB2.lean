/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.Topology.Jordan.StepB2 at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.StepB1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Jordan curve theorem (Maehara's proof), part: Step B: normalized uniqueness of the bounded component

Ported from github.com/rkirov/jordan_pick (Apache-2.0, R. Kirov), commit
`b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, file `JordanPick/JordanCurve.lean`, lines 2214–2548.
Original proofs kept; changed only where our pin (Lean v4.34.0-rc2, mathlib a4c8ef0a) forces
it. Namespace `JordanCurve` → `MatedCRTHarmonic.Planar.Jordan`; `private` dropped so that the original
file can be split into modules. Source: H. Maehara, *The Jordan curve theorem via the Brouwer
fixed point theorem*, Amer. Math. Monthly 91 (1984) 641–643. -/

namespace MatedCRTHarmonic.Planar.Jordan

open Metric Set Function Bornology

/-- **Maehara Step B (normalized).** Uniqueness of the bounded component in
normalized coordinates (farthest pair at `!₂[-1,0]`, `!₂[1,0]`). Any bounded
component equals the `z₀`-component `U`, hence all bounded components coincide. -/
theorem step_B_normalized (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∀ x ∈ (range r)ᶜ, ∀ y ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x) →
      IsBounded (connectedComponentIn (range r)ᶜ y) →
      connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  classical
  obtain ⟨J_n, J_s, l, m, p, q, z₀, hUnion, hInter, hpcJn,
    ⟨hlJn, hl0, hlmax⟩, ⟨hmJn, hm0, hmmin⟩, ⟨hpJs, hp0, hpm, hpmax⟩,
    ⟨hqJs, hq0, hqmin⟩, hz₀def, hml, hqp, hpz₀, hz₀m,
    hpcJs, hJoinJn, hJoinJs⟩ := exists_construction_points hbr hcont hinj hm hp hfar
  -- basic containments, coordinates, and rectangle bounds
  have hJnr : J_n ⊆ range r := hUnion ▸ subset_union_left
  have hJsr : J_s ⊆ range r := hUnion ▸ subset_union_right
  have hErect := normalized_subset_rectangle hm hp hfar
  have ha0 : (!₂[(-1:ℝ), 0] : Plane) 0 = -1 := by simp
  have ha1 : (!₂[(-1:ℝ), 0] : Plane) 1 = 0 := by simp
  have hb0 : (!₂[(1:ℝ), 0] : Plane) 0 = 1 := by simp
  have hb1 : (!₂[(1:ℝ), 0] : Plane) 1 = 0 := by simp
  have hs0 : (!₂[(0:ℝ), -2] : Plane) 0 = 0 := by simp
  have hs1 : (!₂[(0:ℝ), -2] : Plane) 1 = -2 := by simp
  have hn0 : (!₂[(0:ℝ), 2] : Plane) 0 = 0 := by simp
  have hn1 : (!₂[(0:ℝ), 2] : Plane) 1 = 2 := by simp
  have hz₀0 : z₀ 0 = 0 := by rw [hz₀def]; simp
  have hz₀1e : z₀ 1 = (m 1 + p 1) / 2 := by rw [hz₀def]; simp
  have hmr : m ∈ range r := hJnr hmJn
  have hlr : l ∈ range r := hJnr hlJn
  have hpr : p ∈ range r := hJsr hpJs
  have hqr : q ∈ range r := hJsr hqJs
  have hmE1 : m 1 ∈ Icc (-2:ℝ) 2 := (hErect hmr).2
  have hlE1 : l 1 ∈ Icc (-2:ℝ) 2 := (hErect hlr).2
  have hpE1 : p 1 ∈ Icc (-2:ℝ) 2 := (hErect hpr).2
  have hqE1 : q 1 ∈ Icc (-2:ℝ) 2 := (hErect hqr).2
  have hpm_lt : p 1 < m 1 := by
    rcases lt_or_eq_of_le hpm with h | h
    · exact h
    · exfalso
      have hpm_eq : p = m := by ext i; fin_cases i <;> simp [hp0, hm0, h]
      have hmem : m ∈ J_n ∩ J_s := ⟨hmJn, hpm_eq ▸ hpJs⟩
      rw [hInter] at hmem
      rcases hmem with h' | h' <;>
        (have hc := congrArg (fun x : Plane => x 0) h'; simp only [hm0] at hc; norm_num at hc)
  have hqm : q 1 < m 1 := lt_of_le_of_lt hqp hpm_lt
  have hpz₀_lt : p 1 < z₀ 1 := by rw [hz₀1e]; linarith
  have hz₀m_lt : z₀ 1 < m 1 := by rw [hz₀1e]; linarith
  have hz₀1lb : (-2:ℝ) ≤ z₀ 1 := le_of_lt (lt_of_le_of_lt hpE1.1 hpz₀_lt)
  have hz₀1ub : z₀ 1 ≤ 2 := le_of_lt (lt_of_lt_of_le hz₀m_lt hmE1.2)
  have hmab : m ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hm0] at hc; norm_num at hc)
  have hlab : l ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hl0] at hc; norm_num at hc)
  have hqab : q ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hq0] at hc; norm_num at hc)
  have hpab : p ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h) <;>
      (have hc := congrArg (fun x : Plane => x 0) h; simp only [hp0] at hc; norm_num at hc)
  have hz₀c : z₀ ∈ (range r)ᶜ := by
    intro hz₀r
    rw [← hUnion] at hz₀r
    rcases hz₀r with hJn | hJs
    · exact absurd (hmmin z₀ hJn hz₀0) (not_le.2 hz₀m_lt)
    · exact absurd (hpmax z₀ hJs hz₀0 hz₀m_lt.le) (not_le.2 hpz₀_lt)
  -- interval facts
  have hIcc0x : (0:ℝ) ∈ Icc (-1:ℝ) 1 := by rw [mem_Icc]; norm_num
  have hIcc0y : (0:ℝ) ∈ Icc (-2:ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIcc2y : (2:ℝ) ∈ Icc (-2:ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIccm2y : (-2:ℝ) ∈ Icc (-2:ℝ) 2 := by rw [mem_Icc]; norm_num
  have hIccm1x : (-1:ℝ) ∈ Icc (-1:ℝ) 1 := by rw [mem_Icc]; norm_num
  have hIcc1x : (1:ℝ) ∈ Icc (-1:ℝ) 1 := by rw [mem_Icc]; norm_num
  -- the `z₀`-component `U`, the rectangle `E`
  set U : Set Plane := connectedComponentIn (range r)ᶜ z₀ with hUdef
  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn hz₀c
  set E : Set Plane := {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} with hEdef
  -- the open middle axis segment `(p,m)` lies in `U`
  set Mid : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioo (p 1) (m 1)} with hMiddef
  have hMidPC : IsPathConnected Mid :=
    isPathConnected_vertSeg 0 ((convex_Ioo (p 1) (m 1)).isPathConnected (Set.nonempty_Ioo.mpr hpm_lt))
  have hMidc : Mid ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr
    rw [← hUnion] at hvr
    rcases hvr with h | h
    · exact absurd (hmmin v h hv0) (not_le.2 hv1.2)
    · exact absurd (hpmax v h hv0 hv1.2.le) (not_le.2 hv1.1)
  have hz₀Mid : z₀ ∈ Mid :=
    ⟨hz₀0, by rw [hz₀1e]; exact ⟨by linarith [hpm_lt], by linarith [hpm_lt]⟩⟩
  have hMidU : Mid ⊆ U :=
    hMidPC.isConnected.isPreconnected.subset_connectedComponentIn hz₀Mid hMidc
  -- upward and downward axis rays lie in the complement
  set RayN : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Ioi (l 1)} with hRayNdef
  have hRayNPC : IsPathConnected RayN :=
    isPathConnected_vertSeg 0 ((convex_Ioi (l 1)).isPathConnected Set.nonempty_Ioi)
  have hRayNc : RayN ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr; exact absurd (hlmax v hvr hv0) (not_le.2 hv1)
  set RayS : Set Plane := {v : Plane | v 0 = 0 ∧ v 1 ∈ Iio (q 1)} with hRaySdef
  have hRaySPC : IsPathConnected RayS :=
    isPathConnected_vertSeg 0 ((convex_Iio (q 1)).isPathConnected Set.nonempty_Iio)
  have hRaySc : RayS ⊆ (range r)ᶜ := by
    rintro v ⟨hv0, hv1⟩ hvr
    rw [← hUnion] at hvr
    rcases hvr with h | h
    · exact absurd (le_trans (le_trans hqp hpm) (hmmin v h hv0)) (not_le.2 hv1)
    · exact absurd (hqmin v h hv0) (not_le.2 hv1)
  -- **KEY**: every bounded component equals `U`.
  have KEY : ∀ w ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ w) →
      connectedComponentIn (range r)ᶜ w = U := by
    intro w hw hwb
    by_contra hWne
    set W : Set Plane := connectedComponentIn (range r)ᶜ w with hWdef
    have hWsub : W ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
    have hwW : w ∈ W := mem_connectedComponentIn hw
    have hWpc : IsPathConnected W := isPathConnected_component r hcont hw
    -- `W` and `U` are disjoint
    have hWU_disj : Disjoint W U := by
      rw [Set.disjoint_left]
      intro v hvW hvU
      apply hWne
      rw [hWdef, connectedComponentIn_eq (hWdef ▸ hvW), hUdef]
      exact (connectedComponentIn_eq (hUdef ▸ hvU)).symm
    -- component-equation helper: any `v ∈ W` has component `= W`
    have compW : ∀ {v : Plane}, v ∈ W → connectedComponentIn (range r)ᶜ v = W := by
      intro v hvW; rw [hWdef]; exact (connectedComponentIn_eq (hWdef ▸ hvW)).symm
    -- avoid lemmas
    have avoid_up : ∀ v : Plane, v 0 = 0 → l 1 ≤ v 1 → v ∉ W := by
      intro v hv0 hvl hvW
      rcases eq_or_lt_of_le hvl with h | h
      · have hveq : v = l := by ext i; fin_cases i <;> simp [hv0, hl0, h]
        exact hWsub hvW (by rw [hveq]; exact hlr)
      · have h1 := hRayNPC.isConnected.isPreconnected.subset_connectedComponentIn
          (show v ∈ RayN from ⟨hv0, h⟩) hRayNc
        exact axis_ray_up_unbounded (l 1) (hwb.subset (compW hvW ▸ h1))
    have avoid_down : ∀ v : Plane, v 0 = 0 → v 1 ≤ q 1 → v ∉ W := by
      intro v hv0 hvq hvW
      rcases eq_or_lt_of_le hvq with h | h
      · have hveq : v = q := by ext i; fin_cases i <;> simp [hv0, hq0, h]
        exact hWsub hvW (by rw [hveq]; exact hqr)
      · have h1 := hRaySPC.isConnected.isPreconnected.subset_connectedComponentIn
          (show v ∈ RayS from ⟨hv0, h⟩) hRaySc
        exact axis_ray_down_unbounded (q 1) (hwb.subset (compW hvW ▸ h1))
    have avoid_mid : ∀ v : Plane, v 0 = 0 → p 1 ≤ v 1 → v 1 ≤ m 1 → v ∉ W := by
      intro v hv0 hvp hvm hvW
      rcases eq_or_lt_of_le hvp with h | h
      · have hveq : v = p := by ext i; fin_cases i <;> simp [hv0, hp0, h]
        exact hWsub hvW (by rw [hveq]; exact hpr)
      · rcases eq_or_lt_of_le hvm with h' | h'
        · have hveq : v = m := by ext i; fin_cases i <;> simp [hv0, hm0, h']
          exact hWsub hvW (by rw [hveq]; exact hmr)
        · exact (Set.disjoint_left.mp hWU_disj hvW) (hMidU ⟨hv0, ⟨h, h'⟩⟩)
    -- `W ⊆ E` (a bounded component lies in the rectangle)
    have hWE : W ⊆ E := by
      intro v hvW
      by_contra hvE
      rw [hEdef, Set.mem_ofPred_eq] at hvE
      have hvEc : v ∈ {u : Plane | ¬(u 0 ∈ Icc (-1:ℝ) 1 ∧ u 1 ∈ Icc (-2:ℝ) 2)} := hvE
      have hEcc : {u : Plane | ¬(u 0 ∈ Icc (-1:ℝ) 1 ∧ u 1 ∈ Icc (-2:ℝ) 2)} ⊆ (range r)ᶜ :=
        fun u hu hur => hu (hErect hur)
      have h1 := isPreconnected_rect_compl.subset_connectedComponentIn hvEc hEcc
      have hup : {p : Plane | p 0 = 0 ∧ p 1 ∈ Ioi (2:ℝ)}
          ⊆ {u : Plane | ¬(u 0 ∈ Icc (-1:ℝ) 1 ∧ u 1 ∈ Icc (-2:ℝ) 2)} := by
        rintro u ⟨_, hu1⟩ ⟨_, hu2⟩
        rw [mem_Icc] at hu2; rw [mem_Ioi] at hu1; linarith [hu2.2]
      exact axis_ray_up_unbounded 2 (hwb.subset (subset_trans hup (compW hvW ▸ h1)))
    -- **spine path** `β : n → s`, top to bottom, missing `W`, inside `E`
    have hnl_cont : ContinuousOn (segP (!₂[(0:ℝ), 2]) l) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨lm, hlm_cont, hlm_a, hlm_b, hlm_mem⟩ :=
      arc_path (hpcJn.joinedIn l ⟨hlJn, hlab⟩ m ⟨hmJn, hmab⟩)
    have hmp_cont : ContinuousOn (segP m p) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨pq, hpq_cont, hpq_a, hpq_b, hpq_mem⟩ :=
      arc_path (hpcJs.joinedIn p ⟨hpJs, hpab⟩ q ⟨hqJs, hqab⟩)
    have hqs_cont : ContinuousOn (segP q (!₂[(0:ℝ), -2])) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨β, hβcont, hβa, hβb, hβmem⟩ :=
      concatPath5 hnl_cont hlm_cont hmp_cont hpq_cont hqs_cont
        (by rw [segP_one, hlm_a]) (by rw [hlm_b, segP_neg1]) (by rw [segP_one, hpq_a])
        (by rw [hpq_b, segP_neg1])
    have hβE : ∀ t ∈ Icc (-1:ℝ) 1, β t 0 ∈ Icc (-1:ℝ) 1 ∧ β t 1 ∈ Icc (-2:ℝ) 2 := by
      intro t ht
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hn0]; exact hIcc0x) (by rw [hl0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 (by rw [hn1]; exact hIcc2y) hlE1 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJnr (hlm_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hm0]; exact hIcc0x) (by rw [hp0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 hmE1 hpE1 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJsr (hpq_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [hq0]; exact hIcc0x) (by rw [hs0]; exact hIcc0x) hu,
          segP_coord_mem_Icc 1 hqE1 (by rw [hs1]; exact hIccm2y) hu⟩
    have hβmiss : ∀ t ∈ Icc (-1:ℝ) 1, β t ∉ W := by
      intro t ht
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_up _ ?_ ?_
        · rw [segP_coord, hn0, hl0]; ring
        · rw [segP_coord, hn1]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hlE1.2]
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact fun hW => hWsub hW (hJnr (hlm_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_mid _ ?_ ?_ ?_
        · rw [segP_coord, hm0, hp0]; ring
        · rw [segP_coord]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hpm_lt.le]
        · rw [segP_coord]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hpm_lt.le]
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact fun hW => hWsub hW (hJsr (hpq_mem u hu).1)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        refine avoid_down _ ?_ ?_
        · rw [segP_coord, hq0, hs0]; ring
        · rw [segP_coord, hs1]; rw [mem_Icc] at hu; nlinarith [hu.1, hu.2, hqE1.1]
    -- `a, b ∈ closure W` (frontier of a component is the whole curve)
    have hfrW : frontier W = range r := by
      have hexists : ∃ y ∈ (range r)ᶜ,
          connectedComponentIn (range r)ᶜ y ≠ connectedComponentIn (range r)ᶜ w := by
        refine ⟨z₀, hz₀c, ?_⟩
        rw [← hUdef, ← hWdef]; exact fun h => hWne h.symm
      have hcbe := component_boundary_eq hbr hcont hinj hw hexists
      rwa [← hWdef] at hcbe
    have hafrW : (!₂[(-1:ℝ), 0] : Plane) ∈ frontier W := by rw [hfrW]; exact hm
    have hbfrW : (!₂[(1:ℝ), 0] : Plane) ∈ frontier W := by rw [hfrW]; exact hp
    have haclW : (!₂[(-1:ℝ), 0] : Plane) ∈ closure W := frontier_subset_closure hafrW
    have hbclW : (!₂[(1:ℝ), 0] : Plane) ∈ closure W := frontier_subset_closure hbfrW
    -- compact image of `β`, and small balls at `a, b` avoiding it
    set βimg : Set Plane := β '' Icc (-1:ℝ) 1 with hβimgdef
    have hβimg_closed : IsClosed βimg := (isCompact_Icc.image_of_continuousOn hβcont).isClosed
    have ha_notβ : (!₂[(-1:ℝ), 0] : Plane) ∉ βimg := by
      rintro ⟨t, ht, hta⟩
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(-1:ℝ), 0] : Plane) 0 = 0 := by rw [← hta, ← hue, segP_coord, hn0, hl0]; ring
        rw [ha0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hlm_mem u hu).2 (by rw [hue, hta]; exact Set.mem_insert _ _)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(-1:ℝ), 0] : Plane) 0 = 0 := by rw [← hta, ← hue, segP_coord, hm0, hp0]; ring
        rw [ha0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hpq_mem u hu).2 (by rw [hue, hta]; exact Set.mem_insert _ _)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(-1:ℝ), 0] : Plane) 0 = 0 := by rw [← hta, ← hue, segP_coord, hq0, hs0]; ring
        rw [ha0] at hcz; norm_num at hcz
    have hb_notβ : (!₂[(1:ℝ), 0] : Plane) ∉ βimg := by
      rintro ⟨t, ht, htb⟩
      rcases hβmem t ht with ((((h | h) | h) | h) | h)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(1:ℝ), 0] : Plane) 0 = 0 := by rw [← htb, ← hue, segP_coord, hn0, hl0]; ring
        rw [hb0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hlm_mem u hu).2 (by rw [hue, htb]; exact Set.mem_insert_of_mem _ rfl)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(1:ℝ), 0] : Plane) 0 = 0 := by rw [← htb, ← hue, segP_coord, hm0, hp0]; ring
        rw [hb0] at hcz; norm_num at hcz
      · obtain ⟨u, hu, hue⟩ := h
        exact (hpq_mem u hu).2 (by rw [hue, htb]; exact Set.mem_insert_of_mem _ rfl)
      · obtain ⟨u, hu, hue⟩ := h
        have hcz : (!₂[(1:ℝ), 0] : Plane) 0 = 0 := by rw [← htb, ← hue, segP_coord, hq0, hs0]; ring
        rw [hb0] at hcz; norm_num at hcz
    obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hβimg_closed.isOpen_compl _ ha_notβ
    obtain ⟨εb, hεb, hballb⟩ := Metric.isOpen_iff.mp hβimg_closed.isOpen_compl _ hb_notβ
    -- points of `W` near `a, b`
    rw [Metric.mem_closure_iff] at haclW hbclW
    obtain ⟨a₁, ha₁W, ha₁d⟩ := haclW εa hεa
    obtain ⟨b₁, hb₁W, hb₁d⟩ := hbclW εb hεb
    have ha₁E : a₁ 0 ∈ Icc (-1:ℝ) 1 ∧ a₁ 1 ∈ Icc (-2:ℝ) 2 := hWE ha₁W
    have hb₁E : b₁ 0 ∈ Icc (-1:ℝ) 1 ∧ b₁ 1 ∈ Icc (-2:ℝ) 2 := hWE hb₁W
    -- **path** `H : a → b`, left to right, inside `E`, missing `β`
    have hHp1_cont : ContinuousOn (segP (!₂[(-1:ℝ), 0]) a₁) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨Harc, hHarc_cont, hHarc_a, hHarc_b, hHarc_mem⟩ :=
      arc_path (hWpc.joinedIn a₁ ha₁W b₁ hb₁W)
    have hHp3_cont : ContinuousOn (segP b₁ (!₂[(1:ℝ), 0])) (Icc (-1:ℝ) 1) := (segP_cont _ _).continuousOn
    obtain ⟨H, hHcont, hHa, hHb, hHmem⟩ :=
      concatPath3 hHp1_cont hHarc_cont hHp3_cont
        (by rw [segP_one, hHarc_a]) (by rw [hHarc_b, segP_neg1])
    have hHa0 : H (-1) 0 = -1 := by rw [hHa, segP_neg1, ha0]
    have hHb0 : H 1 0 = 1 := by rw [hHb, segP_one, hb0]
    have hHE : ∀ t ∈ Icc (-1:ℝ) 1, H t 0 ∈ Icc (-1:ℝ) 1 ∧ H t 1 ∈ Icc (-2:ℝ) 2 := by
      intro t ht
      rcases hHmem t ht with (h | h) | h
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 (by rw [ha0]; exact hIccm1x) ha₁E.1 hu,
          segP_coord_mem_Icc 1 (by rw [ha1]; exact hIcc0y) ha₁E.2 hu⟩
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hWE (hHarc_mem u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
        exact ⟨segP_coord_mem_Icc 0 hb₁E.1 (by rw [hb0]; exact hIcc1x) hu,
          segP_coord_mem_Icc 1 hb₁E.2 (by rw [hb1]; exact hIcc0y) hu⟩
    have hHmiss : ∀ t ∈ Icc (-1:ℝ) 1, H t ∉ βimg := by
      intro t ht
      rcases hHmem t ht with (h | h) | h
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        have hin : segP (!₂[(-1:ℝ), 0]) a₁ u ∈ Metric.ball (!₂[(-1:ℝ), 0] : Plane) εa := by
          rw [Metric.mem_ball]
          calc dist (segP (!₂[(-1:ℝ), 0]) a₁ u) (!₂[(-1:ℝ), 0])
                ≤ dist a₁ (!₂[(-1:ℝ), 0]) := segP_dist_le _ _ hu
            _ < εa := by rw [dist_comm]; exact ha₁d
        exact hballa hin hmemβ
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        obtain ⟨t', ht', ht'e⟩ := hmemβ
        exact hβmiss t' ht' (by rw [ht'e]; exact hHarc_mem u hu)
      · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; intro hmemβ
        have hin : segP b₁ (!₂[(1:ℝ), 0]) u ∈ Metric.ball (!₂[(1:ℝ), 0] : Plane) εb := by
          rw [Metric.mem_ball]
          calc dist (segP b₁ (!₂[(1:ℝ), 0]) u) (!₂[(1:ℝ), 0])
                ≤ dist b₁ (!₂[(1:ℝ), 0]) := segP_dist_le' _ _ hu
            _ < εb := by rw [dist_comm]; exact hb₁d
        exact hballb hin hmemβ
    -- reorient `β` bottom-to-top and cross with `H`
    set v : ℝ → Plane := fun t => β (-t) with hvdef
    have hvcont : ContinuousOn v (Icc (-1:ℝ) 1) :=
      hβcont.comp continuous_neg.continuousOn (fun t ht => by
        rw [mem_Icc] at ht ⊢; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hvE : ∀ t ∈ Icc (-1:ℝ) 1, v t 0 ∈ Icc (-1:ℝ) 1 ∧ v t 1 ∈ Icc (-2:ℝ) 2 := by
      intro t ht; rw [mem_Icc] at ht
      exact hβE (-t) (by rw [mem_Icc]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hv1 : v (-1) 1 = -2 := by show β (-(-1)) 1 = -2; rw [neg_neg, hβb, segP_one, hs1]
    have hv2 : v 1 1 = 2 := by show β (-1) 1 = 2; rw [hβa, segP_neg1, hn1]
    obtain ⟨s, hs, t, ht, heq⟩ := crossing hbr (by norm_num : (-1:ℝ) ≤ 1) (by norm_num : (-2:ℝ) ≤ 2)
      H v hHcont hvcont hHE hvE hHa0 hHb0 hv1 hv2
    apply hHmiss s hs
    rw [heq]
    exact Set.mem_image_of_mem β (show (-t) ∈ Icc (-1:ℝ) 1 by
      rw [mem_Icc] at ht ⊢; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  -- assemble: bounded components of `x, y` both equal `U`
  intro x hx y hy hxb hyb
  rw [KEY x hx hxb, KEY y hy hyb]

end MatedCRTHarmonic.Planar.Jordan
