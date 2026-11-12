/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.Topology.Jordan.StepA2 at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.StepA1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Jordan curve theorem (Maehara's proof), part: Step A: a bounded component exists

Ported from github.com/rkirov/jordan_pick (Apache-2.0, R. Kirov), commit
`b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, file `JordanPick/JordanCurve.lean`, lines 1726–2086.
Original proofs kept; changed only where our pin (Lean v4.34.0-rc2, mathlib a4c8ef0a) forces
it. Namespace `JordanCurve` → `MatedCRTHarmonic.Planar.Jordan`; `private` dropped so that the original
file can be split into modules. Source: H. Maehara, *The Jordan curve theorem via the Brouwer
fixed point theorem*, Amer. Math. Monthly 91 (1984) 641–643. -/

namespace MatedCRTHarmonic.Planar.Jordan

open Metric Set Function Bornology

/-- **Step A, low exit case.** If the escaping path first meets the frontier at a point
below the axis, the concatenation `s → w → z₀ → m → l → n` (lower boundary region,
escaping path reversed, axis, north arc, axis) misses `J_s`, contradicting
`vertical_meets_arc`. -/
lemma step_A_case_low (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2)
    {J_n J_s : Set Plane} (hJnr : J_n ⊆ range r) (hJsr : J_s ⊆ range r)
    (hInter : J_n ∩ J_s = ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane))
    (hpcJn : IsPathConnected (J_n \ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane)))
    (hJoinJs : JoinedIn J_s (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]))
    {l m p z₀ : Plane}
    (hlJn : l ∈ J_n) (hl0 : l 0 = 0) (hlmax : ∀ w ∈ range r, w 0 = 0 → w 1 ≤ l 1)
    (hmJn : m ∈ J_n) (hm0 : m 0 = 0)
    (hpJs : p ∈ J_s) (hpmax : ∀ w ∈ J_s, w 0 = 0 → w 1 ≤ m 1 → w 1 ≤ p 1)
    (hz₀0 : z₀ 0 = 0) (hpz₀_lt : p 1 < z₀ 1) (hz₀m_lt : z₀ 1 < m 1)
    {α : ℝ → Plane} {tw : ℝ}
    (hαcont : Continuous α) (hα0 : α 0 = z₀) (htw0 : 0 ≤ tw)
    (hαE : ∀ u ∈ Icc (0:ℝ) tw, α u 0 ∈ Icc (-1:ℝ) 1 ∧ α u 1 ∈ Icc (-2:ℝ) 2)
    (hαnr : ∀ u : ℝ, α u ∉ range r)
    (hwC0 : α tw 0 ∈ Icc (-1:ℝ) 1) (hwC1 : α tw 1 ∈ Icc (-2:ℝ) 2)
    (hwO : ¬(α tw 0 ∈ Ioo (-1:ℝ) 1 ∧ α tw 1 ∈ Ioo (-2:ℝ) 2))
    (hwneg : α tw 1 < 0) : False := by
  have hErect := normalized_subset_rectangle hm hp hfar
  have hmab := off_axis_endpoints hm0
  have hlab := off_axis_endpoints hl0
  have hlE1 : l 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJnr hlJn)).2
  have hmE1 : m 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJnr hmJn)).2
  have hpE1 : p 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJsr hpJs)).2
  have hz₀1lb : (-2:ℝ) ≤ z₀ 1 := le_of_lt (lt_of_le_of_lt hpE1.1 hpz₀_lt)
  have hs1 : (!₂[(0:ℝ), -2] : Plane) 1 = -2 := by simp
  have hn1 : (!₂[(0:ℝ), 2] : Plane) 1 = 2 := by simp
  obtain ⟨Glo, hGloPC, hsGlo, hGloSub, hGloAvoid, hGloFrom⟩ :=
    exists_lower_boundary_path hm hp hfar
  have hwGlo : α tw ∈ Glo := hGloFrom (α tw) hwC0 hwC1 hwO hwneg
  -- piece 1 : `s → w` inside `Glo`
  obtain ⟨g1, hg1cont, hg1a, hg1b, hg1mem⟩ :=
    arc_path (hGloPC.joinedIn (!₂[(0:ℝ), -2]) hsGlo (α tw) hwGlo)
  -- piece 2 : `w → z₀` along the escaping path
  set g2 : ℝ → Plane := fun t => α (tw * (1 - t) / 2) with hg2def
  have hg2cont : ContinuousOn g2 (Icc (-1:ℝ) 1) :=
    (hαcont.comp (by fun_prop : Continuous fun t : ℝ => tw * (1 - t) / 2)).continuousOn
  have hg2a : g2 (-1) = α tw := by show α (tw * (1 - (-1)) / 2) = α tw; congr 1; ring
  have hg2b : g2 1 = z₀ := by
    show α (tw * (1 - 1) / 2) = z₀; rw [show tw * (1 - 1) / 2 = (0:ℝ) from by ring, hα0]
  have hg2arg : ∀ t ∈ Icc (-1:ℝ) 1, tw * (1 - t) / 2 ∈ Icc (0:ℝ) tw := by
    intro t ht; rw [mem_Icc] at ht
    rw [mul_div_assoc]
    exact mul_unit_mem_Icc htw0 (by linarith [ht.2]) (by linarith [ht.1])
  -- piece 3 : `z₀ → m` along the axis
  obtain ⟨g3, hg3cont, hg3a, hg3b, hg3x, hg3y⟩ := axis_segment hz₀0 hm0 hz₀m_lt.le
  have hg3missJs : ∀ t ∈ Icc (-1:ℝ) 1, g3 t ∉ J_s := by
    intro t ht hJs
    have hy := hg3y t ht; rw [mem_Icc] at hy
    have := hpmax (g3 t) hJs (hg3x t) hy.2
    linarith [hy.1, hpz₀_lt]
  -- piece 4 : `m → l` inside `J_n \ {a,b}`
  obtain ⟨g4, hg4cont, hg4a, hg4b, hg4mem⟩ :=
    arc_path (hpcJn.joinedIn m ⟨hmJn, hmab⟩ l ⟨hlJn, hlab⟩)
  have hg4missJs : ∀ t ∈ Icc (-1:ℝ) 1, g4 t ∉ J_s := by
    intro t ht hJs
    have hg4 := hg4mem t ht
    have hmem : g4 t ∈ J_n ∩ J_s := ⟨hg4.1, hJs⟩
    rw [hInter] at hmem; exact hg4.2 hmem
  -- piece 5 : `l → n` along the axis
  obtain ⟨g5, hg5cont, hg5a, hg5b, hg5x, hg5y⟩ :=
    axis_segment hl0 (show (!₂[(0:ℝ), 2] : Plane) 0 = 0 from by simp) (by rw [hn1]; exact hlE1.2)
  have hg5missJs : ∀ t ∈ Icc (-1:ℝ) 1, g5 t ∉ J_s := by
    intro t ht hJs
    have hy := hg5y t ht; rw [mem_Icc] at hy
    have hle := hlmax (g5 t) (hJsr hJs) (hg5x t)
    have heq : g5 t 1 = l 1 := le_antisymm hle hy.1
    have hgl : g5 t = l := by ext i; fin_cases i <;> simp [hg5x t, hl0, heq]
    rw [hgl] at hJs
    have hmem : l ∈ J_n ∩ J_s := ⟨hlJn, hJs⟩
    rw [hInter] at hmem; exact hlab hmem
  -- concatenate `s → w → z₀ → m → l → n`
  obtain ⟨V, hVcont, hVa, hVb, hVmem⟩ :=
    concatPath5 hg1cont hg2cont hg3cont hg4cont hg5cont
      (by rw [hg1b, hg2a]) (by rw [hg2b, hg3a]) (by rw [hg3b, hg4a]) (by rw [hg4b, hg5a])
  have hVm1 : V (-1) 1 = -2 := by rw [hVa, hg1a]; exact hs1
  have hVn1 : V 1 1 = 2 := by rw [hVb, hg5b]; exact hn1
  have hVE : ∀ t ∈ Icc (-1:ℝ) 1, V t 0 ∈ Icc (-1:ℝ) 1 ∧ V t 1 ∈ Icc (-2:ℝ) 2 := by
    intro t ht
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hGloSub (hg1mem u hu)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hαE _ (hg2arg u hu)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg3y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg3x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨le_trans hz₀1lb hy.1, le_trans hy.2 hmE1.2⟩⟩
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJnr (hg4mem u hu).1)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg5y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg5x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨le_trans hlE1.1 hy.1, hy.2⟩⟩
  have hVmiss : ∀ t ∈ Icc (-1:ℝ) 1, V t ∉ J_s := by
    intro t ht hJs
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs
      exact hGloAvoid (g1 u) (hg1mem u hu) (hJsr hJs)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs
      exact hαnr (tw * (1 - u) / 2) (hJsr hJs)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg3missJs u hu hJs
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg4missJs u hu hJs
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJs; exact hg5missJs u hu hJs
  have hJsrect : J_s ⊆ {w : Plane | w 0 ∈ Icc (-1:ℝ) 1 ∧ w 1 ∈ Icc (-2:ℝ) 2} :=
    fun w hw => hErect (hJsr hw)
  obtain ⟨t, ht, htJs⟩ := vertical_meets_arc hbr hJsrect hJoinJs hVcont hVE hVm1 hVn1
  exact hVmiss t ht htJs

/-- **Step A, high exit case.** Mirror of `step_A_case_low`: if the escaping path first
meets the frontier above the axis, the concatenation `s → q → p → z₀ → w → n` misses
`J_n`, contradicting `vertical_meets_arc`. -/
lemma step_A_case_high (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2)
    {J_n J_s : Set Plane} (hJnr : J_n ⊆ range r) (hJsr : J_s ⊆ range r)
    (hInter : J_n ∩ J_s = ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane))
    (hpcJs : IsPathConnected (J_s \ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane)))
    (hJoinJn : JoinedIn J_n (!₂[(-1:ℝ), 0]) (!₂[(1:ℝ), 0]))
    {m p q z₀ : Plane}
    (hmJn : m ∈ J_n) (_hm0 : m 0 = 0) (hmmin : ∀ w ∈ J_n, w 0 = 0 → m 1 ≤ w 1)
    (hpJs : p ∈ J_s) (hp0 : p 0 = 0)
    (hqJs : q ∈ J_s) (hq0 : q 0 = 0) (hqm : q 1 < m 1)
    (hz₀0 : z₀ 0 = 0) (hpz₀_lt : p 1 < z₀ 1) (hz₀m_lt : z₀ 1 < m 1)
    {α : ℝ → Plane} {tw : ℝ}
    (hαcont : Continuous α) (hα0 : α 0 = z₀) (htw0 : 0 ≤ tw)
    (hαE : ∀ u ∈ Icc (0:ℝ) tw, α u 0 ∈ Icc (-1:ℝ) 1 ∧ α u 1 ∈ Icc (-2:ℝ) 2)
    (hαnr : ∀ u : ℝ, α u ∉ range r)
    (hwC0 : α tw 0 ∈ Icc (-1:ℝ) 1) (hwC1 : α tw 1 ∈ Icc (-2:ℝ) 2)
    (hwO : ¬(α tw 0 ∈ Ioo (-1:ℝ) 1 ∧ α tw 1 ∈ Ioo (-2:ℝ) 2))
    (hwpos : 0 < α tw 1) : False := by
  have hErect := normalized_subset_rectangle hm hp hfar
  have hqab := off_axis_endpoints hq0
  have hpab := off_axis_endpoints hp0
  have hqE1 : q 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJsr hqJs)).2
  have hpE1 : p 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJsr hpJs)).2
  have hmE1 : m 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJnr hmJn)).2
  have hz₀1ub : z₀ 1 ≤ 2 := le_of_lt (lt_of_lt_of_le hz₀m_lt hmE1.2)
  have hs1 : (!₂[(0:ℝ), -2] : Plane) 1 = -2 := by simp
  have hn1 : (!₂[(0:ℝ), 2] : Plane) 1 = 2 := by simp
  obtain ⟨Gup, hGupPC, hnGup, hGupSub, hGupAvoid, hGupFrom⟩ :=
    exists_upper_boundary_path hm hp hfar
  have hwGup : α tw ∈ Gup := hGupFrom (α tw) hwC0 hwC1 hwO hwpos
  -- piece 1 : `s → q` along the axis
  obtain ⟨g1, hg1cont, hg1a, hg1b, hg1x, hg1y⟩ :=
    axis_segment (show (!₂[(0:ℝ), -2] : Plane) 0 = 0 from by simp) hq0 (by rw [hs1]; exact hqE1.1)
  have hg1missJn : ∀ t ∈ Icc (-1:ℝ) 1, g1 t ∉ J_n := by
    intro t ht hJn
    have hy := hg1y t ht; rw [mem_Icc] at hy
    have := hmmin (g1 t) hJn (hg1x t)
    linarith [hy.2, hqm]
  -- piece 2 : `q → p` inside `J_s \ {a,b}`
  obtain ⟨g2, hg2cont, hg2a, hg2b, hg2mem⟩ :=
    arc_path (hpcJs.joinedIn q ⟨hqJs, hqab⟩ p ⟨hpJs, hpab⟩)
  have hg2missJn : ∀ t ∈ Icc (-1:ℝ) 1, g2 t ∉ J_n := by
    intro t ht hJn
    have hg2' := hg2mem t ht
    have hmem : g2 t ∈ J_n ∩ J_s := ⟨hJn, hg2'.1⟩
    rw [hInter] at hmem; exact hg2'.2 hmem
  -- piece 3 : `p → z₀` along the axis
  obtain ⟨g3, hg3cont, hg3a, hg3b, hg3x, hg3y⟩ := axis_segment hp0 hz₀0 hpz₀_lt.le
  have hg3missJn : ∀ t ∈ Icc (-1:ℝ) 1, g3 t ∉ J_n := by
    intro t ht hJn
    have hy := hg3y t ht; rw [mem_Icc] at hy
    have := hmmin (g3 t) hJn (hg3x t)
    linarith [hy.2, hz₀m_lt]
  -- piece 4 : `z₀ → w` along the escaping path
  set g4 : ℝ → Plane := fun t => α (tw * (t + 1) / 2) with hg4def
  have hg4cont : ContinuousOn g4 (Icc (-1:ℝ) 1) :=
    (hαcont.comp (by fun_prop : Continuous fun t : ℝ => tw * (t + 1) / 2)).continuousOn
  have hg4a : g4 (-1) = z₀ := by
    show α (tw * ((-1) + 1) / 2) = z₀; rw [show tw * ((-1) + 1) / 2 = (0:ℝ) from by ring, hα0]
  have hg4b : g4 1 = α tw := by show α (tw * (1 + 1) / 2) = α tw; congr 1; ring
  have hg4arg : ∀ t ∈ Icc (-1:ℝ) 1, tw * (t + 1) / 2 ∈ Icc (0:ℝ) tw := by
    intro t ht; rw [mem_Icc] at ht
    rw [mul_div_assoc]
    exact mul_unit_mem_Icc htw0 (by linarith [ht.1]) (by linarith [ht.2])
  -- piece 5 : `w → n` inside `Gup`
  obtain ⟨g5, hg5cont, hg5a, hg5b, hg5mem⟩ :=
    arc_path (hGupPC.joinedIn (α tw) hwGup (!₂[(0:ℝ), 2]) hnGup)
  have hg5missJn : ∀ t ∈ Icc (-1:ℝ) 1, g5 t ∉ J_n := by
    intro t ht hJn; exact hGupAvoid (g5 t) (hg5mem t ht) (hJnr hJn)
  -- concatenate `s → q → p → z₀ → w → n`
  obtain ⟨V, hVcont, hVa, hVb, hVmem⟩ :=
    concatPath5 hg1cont hg2cont hg3cont hg4cont hg5cont
      (by rw [hg1b, hg2a]) (by rw [hg2b, hg3a]) (by rw [hg3b, hg4a]) (by rw [hg4b, hg5a])
  have hVm1 : V (-1) 1 = -2 := by rw [hVa, hg1a]; exact hs1
  have hVn1 : V 1 1 = 2 := by rw [hVb, hg5b]; exact hn1
  have hVE : ∀ t ∈ Icc (-1:ℝ) 1, V t 0 ∈ Icc (-1:ℝ) 1 ∧ V t 1 ∈ Icc (-2:ℝ) 2 := by
    intro t ht
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg1y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg1x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨hy.1, le_trans hy.2 hqE1.2⟩⟩
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hErect (hJsr (hg2mem u hu).1)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]
      have hy := hg3y u hu; rw [mem_Icc] at hy
      exact ⟨by rw [hg3x u, mem_Icc]; constructor <;> norm_num,
        mem_Icc.2 ⟨le_trans hpE1.1 hy.1, le_trans hy.2 hz₀1ub⟩⟩
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hαE _ (hg4arg u hu)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hGupSub (hg5mem u hu)
  have hVmiss : ∀ t ∈ Icc (-1:ℝ) 1, V t ∉ J_n := by
    intro t ht hJn
    rcases hVmem t ht with ((((h | h) | h) | h) | h)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg1missJn u hu hJn
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg2missJn u hu hJn
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg3missJn u hu hJn
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn
      exact hαnr (tw * (u + 1) / 2) (hJnr hJn)
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue] at hJn; exact hg5missJn u hu hJn
  have hJnrect : J_n ⊆ {w : Plane | w 0 ∈ Icc (-1:ℝ) 1 ∧ w 1 ∈ Icc (-2:ℝ) 2} :=
    fun w hw => hErect (hJnr hw)
  obtain ⟨t, ht, htJn⟩ := vertical_meets_arc hbr hJnrect hJoinJn hVcont hVE hVm1 hVn1
  exact hVmiss t ht htJn

/-- **Maehara Step A (normalized).** The geometric core in normalized coordinates:
the farthest pair sits at `!₂[-1,0]`, `!₂[1,0]` (so the diameter is `2`). -/
theorem step_A_normalized (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r)
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ x ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ x) := by
  classical
  obtain ⟨J_n, J_s, l, m, p, q, z₀, hUnion, hInter, hpcJn,
    ⟨hlJn, hl0, hlmax⟩, ⟨hmJn, hm0, hmmin⟩, ⟨hpJs, hp0, hpm, hpmax⟩,
    ⟨hqJs, hq0, hqmin⟩, hz₀def, hml, hqp, hpz₀, hz₀m,
    hpcJs, hJoinJn, hJoinJs⟩ := exists_construction_points hbr hcont hinj hm hp hfar
  -- basic containments, coordinates, and rectangle bounds
  have hJnr : J_n ⊆ range r := hUnion ▸ subset_union_left
  have hJsr : J_s ⊆ range r := hUnion ▸ subset_union_right
  have hErect := normalized_subset_rectangle hm hp hfar
  have hz₀0 : z₀ 0 = 0 := by rw [hz₀def]; simp
  have hz₀1e : z₀ 1 = (m 1 + p 1) / 2 := by rw [hz₀def]; simp
  have hmE1 : m 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJnr hmJn)).2
  have hpE1 : p 1 ∈ Icc (-2:ℝ) 2 := (hErect (hJsr hpJs)).2
  -- `p 1 < m 1` (else `p = m` would lie in `J_n ∩ J_s = {a,b}` off the axis)
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
  -- **A.0** : `z₀ ∉ range r`
  have hz₀c : z₀ ∈ (range r)ᶜ := by
    intro hz₀r
    rw [← hUnion] at hz₀r
    rcases hz₀r with hJn | hJs
    · exact absurd (hmmin z₀ hJn hz₀0) (not_le.2 hz₀m_lt)
    · exact absurd (hpmax z₀ hJs hz₀0 hz₀m_lt.le) (not_le.2 hpz₀_lt)
  refine ⟨z₀, hz₀c, ?_⟩
  -- the rectangle `E`, its open interior `O`
  set E : Set Plane := {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} with hEdef
  set O : Set Plane := {p : Plane | p 0 ∈ Ioo (-1:ℝ) 1 ∧ p 1 ∈ Ioo (-2:ℝ) 2} with hOdef
  have hEbdd : IsBounded E := by rw [hEdef]; exact isBounded_rectE
  have hOopen : IsOpen O := by rw [hOdef]; exact isOpen_rectO
  have hEclosed : IsClosed E := by rw [hEdef]; exact isClosed_rectE
  have hOE : O ⊆ E := fun w hw => ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩
  have hz₀O : z₀ ∈ O := by
    refine ⟨?_, ?_⟩
    · rw [mem_Ioo, hz₀0]; constructor <;> norm_num
    · rw [mem_Ioo, hz₀1e]; exact ⟨by linarith [hpE1.1, hpm_lt], by linarith [hmE1.2, hpm_lt]⟩
  -- assume the component is unbounded and derive a contradiction
  by_contra hUunb
  set U : Set Plane := connectedComponentIn (range r)ᶜ z₀ with hUeq
  have hUsub : U ⊆ (range r)ᶜ := connectedComponentIn_subset _ _
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn hz₀c
  have hUpc : IsPathConnected U := isPathConnected_component r hcont hz₀c
  have hUnotsub : ¬ U ⊆ E := fun h => hUunb (hEbdd.subset h)
  obtain ⟨y, hyU, hyE⟩ := Set.not_subset.mp hUnotsub
  -- reparametrized escaping path `α : ℝ → Plane`
  have hJoinU : JoinedIn U z₀ y := hUpc.joinedIn z₀ hz₀U y hyU
  set α : ℝ → Plane := fun t => hJoinU.somePath (Set.projIcc (0:ℝ) 1 (by norm_num) t) with hαdef
  have hαcont : Continuous α := hJoinU.somePath.continuous.comp continuous_projIcc
  have hα0 : α 0 = z₀ := by
    show hJoinU.somePath _ = z₀
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) 0 = 0 from Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hJoinU.somePath.source
  have hα1 : α 1 = y := by
    show hJoinU.somePath _ = y
    rw [show Set.projIcc (0:ℝ) 1 (by norm_num) 1 = 1 from Subtype.ext (by rw [Set.coe_projIcc]; norm_num)]
    exact hJoinU.somePath.target
  have hαU : ∀ t : ℝ, α t ∈ U := fun t => hJoinU.somePath_mem _
  -- first exit through the frontier `E \ O`
  obtain ⟨tw, htw, hwC, hwO, hbelow⟩ :=
    exists_first_exit hOopen hEclosed hOE hαcont.continuousOn (by rw [hα0]; exact hz₀O)
      (by rw [hα1]; exact hyE)
  have hαE : ∀ u ∈ Icc (0:ℝ) tw, α u ∈ E := by
    intro u hu
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h]; exact hwC
    · exact hOE (hbelow u ⟨hu.1, h⟩)
  have hwnr : α tw ∉ range r := hUsub (hαU tw)
  -- `α tw` is off the axis
  have hw1ne : α tw 1 ≠ 0 := fun hzero =>
    hwnr (axis_zero_mem_range hm hp hwC.1 hwO hzero)
  rcases lt_or_gt_of_ne hw1ne with hwneg | hwpos
  · exact step_A_case_low hbr hm hp hfar hJnr hJsr hInter hpcJn hJoinJs
      hlJn hl0 hlmax hmJn hm0 hpJs hpmax hz₀0 hpz₀_lt hz₀m_lt
      hαcont hα0 htw.1.le (fun u hu => hαE u hu) (fun u => hUsub (hαU u))
      hwC.1 hwC.2 hwO hwneg
  · exact step_A_case_high hbr hm hp hfar hJnr hJsr hInter hpcJs hJoinJn
      hmJn hm0 hmmin hpJs hp0 hqJs hq0 hqm hz₀0 hpz₀_lt hz₀m_lt
      hαcont hα0 htw.1.le (fun u hu => hαE u hu) (fun u => hUsub (hαU u))
      hwC.1 hwC.2 hwO hwpos

/-- **Maehara Step A (geometric core).** The complement `ℝ²∖J` of a Jordan curve
has at least one *bounded* connected component. Reduced to the normalized version
`step_A_normalized` via the farthest-pair similarity `T`. -/
theorem step_A_exists_bounded (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r) :
    ∃ x ∈ (range r)ᶜ, IsBounded (connectedComponentIn (range r)ᶜ x) := by
  obtain ⟨a, ha, b, hb, hfar, hab⟩ := exists_farthest_pair hcont hinj
  obtain ⟨T, hscale, hTa, hTb⟩ := exists_similarity hab
  have hdpos : 0 < dist a b := dist_pos.mpr hab
  have hcpos : (0:ℝ) < 2 / dist a b := by positivity
  -- the transported curve `r' = T ∘ r`
  set r' : sphere (0 : Plane) 1 → Plane := fun p => T (r p) with hr'
  have hr'cont : Continuous r' := T.continuous.comp hcont
  have hr'inj : Injective r' := T.injective.comp hinj
  have hrange : range r' = T '' range r := by
    rw [hr', show (fun p => T (r p)) = (T : Plane → Plane) ∘ r from rfl, Set.range_comp]
  -- normalized hypotheses for `r'`
  have hm' : (!₂[(-1:ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTa]; exact mem_image_of_mem _ ha
  have hp' : (!₂[(1:ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTb]; exact mem_image_of_mem _ hb
  have hfar' : ∀ z ∈ range r', ∀ w ∈ range r', dist z w ≤ 2 := by
    rw [hrange]
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hscale]
    calc 2 / dist a b * dist z w
        ≤ 2 / dist a b * dist a b := by
          exact mul_le_mul_of_nonneg_left (hfar z hz w hw) hcpos.le
      _ = 2 := by field_simp
  obtain ⟨x, hx, hxb⟩ := step_A_normalized hbr hr'cont hr'inj hm' hp' hfar'
  -- transport the bounded component back by `T⁻¹`
  rw [hrange] at hx hxb
  -- `x ∈ (T '' range r)ᶜ = T '' (range r)ᶜ`
  have himg : (T '' range r)ᶜ = T '' (range r)ᶜ :=
    (Set.image_compl_eq (f := (T : Plane → Plane)) T.bijective).symm
  rw [himg] at hx hxb
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  refine ⟨x₀, hx₀, ?_⟩
  -- component of `x = T x₀` corresponds to component of `x₀` under `T`
  have hcc : connectedComponentIn ((T : Plane → Plane) '' (range r)ᶜ) (T x₀)
      = T '' connectedComponentIn (range r)ᶜ x₀ :=
    (T.image_connectedComponentIn hx₀).symm
  rw [hcc] at hxb
  exact (isBounded_image_scaling hcpos hscale _).mp hxb

end MatedCRTHarmonic.Planar.Jordan
