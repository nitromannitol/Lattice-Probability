/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.Topology.Jordan.StepA1 at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.Paths

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Jordan curve theorem (Maehara's proof), part: Step A helpers

Ported from github.com/rkirov/jordan_pick (Apache-2.0, R. Kirov), commit
`b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, file `JordanPick/JordanCurve.lean`, lines 1438–1725.
Original proofs kept; changed only where our pin (Lean v4.34.0-rc2, mathlib a4c8ef0a) forces
it. Namespace `JordanCurve` → `MatedCRTHarmonic.Planar.Jordan`; `private` dropped so that the original
file can be split into modules. Source: H. Maehara, *The Jordan curve theorem via the Brouwer
fixed point theorem*, Amer. Math. Monthly 91 (1984) 641–643. -/

namespace MatedCRTHarmonic.Planar.Jordan

open Metric Set Function Bornology

/-- **First-exit lemma (A.1).** A path `α` on `[0,1]` starting inside an open set `O`
and ending outside a closed superset `C ⊇ O` has a *first exit time* `tw ∈ (0,1]`:
`α tw` lies in the frontier layer `C \ O`, and `α u ∈ O` for all `u < tw`. -/
theorem exists_first_exit {α : ℝ → Plane} {O C : Set Plane}
    (hO : IsOpen O) (hC : IsClosed C) (hOC : O ⊆ C)
    (hcont : ContinuousOn α (Icc (0:ℝ) 1))
    (h0 : α 0 ∈ O) (h1 : α 1 ∉ C) :
    ∃ tw ∈ Ioc (0:ℝ) 1, α tw ∈ C ∧ α tw ∉ O ∧ ∀ u ∈ Ico (0:ℝ) tw, α u ∈ O := by
  set S : Set ℝ := {t ∈ Icc (0:ℝ) 1 | α t ∉ O} with hSdef
  -- `S` is closed: it is `Icc 0 1 ∩ α⁻¹(Oᶜ)`
  have hScl : IsClosed S := by
    have hEq : S = Icc (0:ℝ) 1 ∩ α ⁻¹' Oᶜ := by
      ext t; simp only [hSdef, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff]
    rw [hEq]; exact hcont.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have hSne : S.Nonempty :=
    ⟨1, ⟨by norm_num, fun h => h1 (hOC h)⟩⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set tw := sInf S with htw
  have htwS : tw ∈ S := hScl.csInf_mem hSne hSbdd
  have htw01 : tw ∈ Icc (0:ℝ) 1 := htwS.1
  have htwO : α tw ∉ O := htwS.2
  -- `tw > 0` (since `0 ∉ S`)
  have h0S : (0:ℝ) ∉ S := fun h => h.2 h0
  have htwpos : 0 < tw := lt_of_le_of_ne htw01.1 (fun h => h0S (h ▸ htwS))
  -- points strictly below `tw` are still in `O`
  have hbelow : ∀ u ∈ Ico (0:ℝ) tw, α u ∈ O := by
    intro u hu
    by_contra hnot
    have huS : u ∈ S := ⟨⟨hu.1, le_trans hu.2.le htw01.2⟩, hnot⟩
    exact absurd (csInf_le hSbdd huS) (not_le.2 hu.2)
  -- `α tw ∈ C` by closure of the pre-exit segment
  have htwC : α tw ∈ C := by
    have hT : IsClosed (Icc (0:ℝ) 1 ∩ α ⁻¹' C) :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc hC
    have hsub : Ico (0:ℝ) tw ⊆ Icc (0:ℝ) 1 ∩ α ⁻¹' C := by
      intro u hu
      exact ⟨⟨hu.1, le_trans hu.2.le htw01.2⟩, hOC (hbelow u hu)⟩
    have : tw ∈ Icc (0:ℝ) 1 ∩ α ⁻¹' C := by
      apply hT.closure_subset_iff.mpr hsub
      rw [closure_Ico (ne_of_lt htwpos)]
      exact ⟨htwpos.le, le_refl tw⟩
    exact this.2
  exact ⟨tw, ⟨htwpos, htw01.2⟩, htwC, htwO, hbelow⟩

/-- A vertical segment `{p | p 0 = c ∧ p 1 ∈ T}` (with `T` path-connected) is
path-connected: it is the image of `T` under `y ↦ !₂[c, y]`. -/
theorem isPathConnected_vertSeg (c : ℝ) {T : Set ℝ} (hT : IsPathConnected T) :
    IsPathConnected {p : Plane | p 0 = c ∧ p 1 ∈ T} := by
  have hfcont : Continuous (fun y : ℝ => (!₂[c, y] : Plane)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have himg := hT.image hfcont
  have hEq : (fun y : ℝ => (!₂[c, y] : Plane)) '' T = {p : Plane | p 0 = c ∧ p 1 ∈ T} := by
    ext p
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨by simp, by simpa using hy⟩
    · rintro ⟨h0, h1⟩
      exact ⟨p 1, h1, by ext i; fin_cases i <;> simp [h0]⟩
  rwa [hEq] at himg

/-- A horizontal segment `{p | p 1 = c ∧ p 0 ∈ T}` is path-connected. -/
theorem isPathConnected_horizSeg (c : ℝ) {T : Set ℝ} (hT : IsPathConnected T) :
    IsPathConnected {p : Plane | p 1 = c ∧ p 0 ∈ T} := by
  have hfcont : Continuous (fun x : ℝ => (!₂[x, c] : Plane)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have himg := hT.image hfcont
  have hEq : (fun x : ℝ => (!₂[x, c] : Plane)) '' T = {p : Plane | p 1 = c ∧ p 0 ∈ T} := by
    ext p
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨by simp, by simpa using hy⟩
    · rintro ⟨h0, h1⟩
      exact ⟨p 0, h1, by ext i; fin_cases i <;> simp [h0]⟩
  rwa [hEq] at himg

/-- **Curve meets the rectangle boundary only on the axis (A.2).** Any curve point on
the frontier of the normalized rectangle `[-1,1]×[-2,2]` has `y = 0` (so it is `a` or
`b`). The "lens" bound `(p 0±1)²+(p 1)² ≤ 4` rules out the top/bottom edges outright
and pins the left/right edges to `y = 0`. -/
theorem curve_boundary_axis
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∀ p ∈ range r, (p 0 = -1 ∨ p 0 = 1 ∨ p 1 = -2 ∨ p 1 = 2) → p 1 = 0 := by
  intro p hp' hbdry
  have hza : dist p (!₂[(-1:ℝ), 0]) ^ 2 ≤ 4 := by
    have := hfar p hp' _ hm; nlinarith [dist_nonneg (x := p) (y := (!₂[(-1:ℝ),0] : Plane))]
  have hzb : dist p (!₂[(1:ℝ), 0]) ^ 2 ≤ 4 := by
    have := hfar p hp' _ hp; nlinarith [dist_nonneg (x := p) (y := (!₂[(1:ℝ),0] : Plane))]
  rw [dist_sq_coord] at hza hzb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hza hzb
  rcases hbdry with h | h | h | h
  · have h2 : (p 1)^2 = 0 := le_antisymm (by nlinarith [hzb]) (sq_nonneg _)
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  · have h2 : (p 1)^2 = 0 := le_antisymm (by nlinarith [hza]) (sq_nonneg _)
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  · exfalso; nlinarith [hza, hzb, sq_nonneg (p 0 + 1), sq_nonneg (p 0 - 1), h, sq_nonneg (p 1 + 2)]
  · exfalso; nlinarith [hza, hzb, sq_nonneg (p 0 + 1), sq_nonneg (p 0 - 1), h, sq_nonneg (p 1 - 2)]

/-- **Lower boundary arc (A.2).** The part of the rectangle frontier with `y < 0` is
path-connected, contains the bottom axis point `!₂[0,-2]`, lies in the rectangle, and
avoids the curve; moreover any frontier point with `y < 0` lies in it. -/
theorem exists_lower_boundary_path
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ G : Set Plane,
      IsPathConnected G ∧
      (!₂[(0:ℝ), -2] : Plane) ∈ G ∧
      G ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} ∧
      (∀ p ∈ G, p ∉ range r) ∧
      (∀ p : Plane, p 0 ∈ Icc (-1:ℝ) 1 → p 1 ∈ Icc (-2:ℝ) 2 →
        ¬(p 0 ∈ Ioo (-1:ℝ) 1 ∧ p 1 ∈ Ioo (-2:ℝ) 2) → p 1 < 0 → p ∈ G) := by
  set L : Set Plane := {p : Plane | p 0 = -1 ∧ p 1 ∈ Ico (-2:ℝ) 0} with hLdef
  set Rt : Set Plane := {p : Plane | p 0 = 1 ∧ p 1 ∈ Ico (-2:ℝ) 0} with hRdef
  set Bot : Set Plane := {p : Plane | p 1 = -2 ∧ p 0 ∈ Icc (-1:ℝ) 1} with hBdef
  have hLpc : IsPathConnected L :=
    isPathConnected_vertSeg (-1) ((convex_Ico _ _).isPathConnected (nonempty_Ico.mpr (by norm_num)))
  have hRpc : IsPathConnected Rt :=
    isPathConnected_vertSeg 1 ((convex_Ico _ _).isPathConnected (nonempty_Ico.mpr (by norm_num)))
  have hBpc : IsPathConnected Bot :=
    isPathConnected_horizSeg (-2) ((convex_Icc _ _).isPathConnected (nonempty_Icc.mpr (by norm_num)))
  have memL : (!₂[(-1:ℝ), -2] : Plane) ∈ L := ⟨by simp, by rw [mem_Ico]; exact ⟨by simp, by norm_num⟩⟩
  have memBotL : (!₂[(-1:ℝ), -2] : Plane) ∈ Bot := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memBotR : (!₂[(1:ℝ), -2] : Plane) ∈ Bot := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memR : (!₂[(1:ℝ), -2] : Plane) ∈ Rt := ⟨by simp, by rw [mem_Ico]; exact ⟨by simp, by norm_num⟩⟩
  have hLB : IsPathConnected (L ∪ Bot) := hLpc.union hBpc ⟨_, memL, memBotL⟩
  have hG : IsPathConnected ((L ∪ Bot) ∪ Rt) := hLB.union hRpc ⟨_, Or.inr memBotR, memR⟩
  refine ⟨(L ∪ Bot) ∪ Rt, hG,
    Or.inl (Or.inr ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩), ?_, ?_, ?_⟩
  · rintro p ((hpp | hpp) | hpp)
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ico] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨h1.1, by linarith [h1.2]⟩⟩
    · obtain ⟨h1, h0⟩ := hpp
      exact ⟨h0, by rw [mem_Icc, h1]; norm_num⟩
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ico] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨h1.1, by linarith [h1.2]⟩⟩
  · rintro p ((hpp | hpp) | hpp) hpr
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inl hpp.1); linarith [hpp.2.2]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inr (Or.inl hpp.1))); linarith [hpp.1]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inl hpp.1)); linarith [hpp.2.2]
  · intro p hp0 hp1 hnint hpneg
    rcases not_and_or.mp hnint with hn0 | hn1
    · rw [mem_Ioo, not_and_or] at hn0
      rcases hn0 with h | h
      · exact Or.inl (Or.inl ⟨le_antisymm (not_lt.mp h) hp0.1, mem_Ico.mpr ⟨hp1.1, hpneg⟩⟩)
      · exact Or.inr ⟨le_antisymm hp0.2 (not_lt.mp h), mem_Ico.mpr ⟨hp1.1, hpneg⟩⟩
    · rw [mem_Ioo, not_and_or] at hn1
      rcases hn1 with h | h
      · exact Or.inl (Or.inr ⟨le_antisymm (not_lt.mp h) hp1.1, hp0⟩)
      · exfalso; linarith [not_lt.mp h]

/-- **Upper boundary arc (A.2).** The part of the rectangle frontier with `y > 0` is
path-connected, contains the top axis point `!₂[0,2]`, lies in the rectangle, and
avoids the curve; moreover any frontier point with `y > 0` lies in it. -/
theorem exists_upper_boundary_path
    {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    (hfar : ∀ z ∈ range r, ∀ w ∈ range r, dist z w ≤ 2) :
    ∃ G : Set Plane,
      IsPathConnected G ∧
      (!₂[(0:ℝ), 2] : Plane) ∈ G ∧
      G ⊆ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-2:ℝ) 2} ∧
      (∀ p ∈ G, p ∉ range r) ∧
      (∀ p : Plane, p 0 ∈ Icc (-1:ℝ) 1 → p 1 ∈ Icc (-2:ℝ) 2 →
        ¬(p 0 ∈ Ioo (-1:ℝ) 1 ∧ p 1 ∈ Ioo (-2:ℝ) 2) → 0 < p 1 → p ∈ G) := by
  set L : Set Plane := {p : Plane | p 0 = -1 ∧ p 1 ∈ Ioc (0:ℝ) 2} with hLdef
  set Rt : Set Plane := {p : Plane | p 0 = 1 ∧ p 1 ∈ Ioc (0:ℝ) 2} with hRdef
  set Top : Set Plane := {p : Plane | p 1 = 2 ∧ p 0 ∈ Icc (-1:ℝ) 1} with hTdef
  have hLpc : IsPathConnected L :=
    isPathConnected_vertSeg (-1) ((convex_Ioc _ _).isPathConnected (nonempty_Ioc.mpr (by norm_num)))
  have hRpc : IsPathConnected Rt :=
    isPathConnected_vertSeg 1 ((convex_Ioc _ _).isPathConnected (nonempty_Ioc.mpr (by norm_num)))
  have hTpc : IsPathConnected Top :=
    isPathConnected_horizSeg 2 ((convex_Icc _ _).isPathConnected (nonempty_Icc.mpr (by norm_num)))
  have memL : (!₂[(-1:ℝ), 2] : Plane) ∈ L := ⟨by simp, by rw [mem_Ioc]; exact ⟨by norm_num, by simp⟩⟩
  have memTopL : (!₂[(-1:ℝ), 2] : Plane) ∈ Top := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memTopR : (!₂[(1:ℝ), 2] : Plane) ∈ Top := ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩
  have memR : (!₂[(1:ℝ), 2] : Plane) ∈ Rt := ⟨by simp, by rw [mem_Ioc]; exact ⟨by norm_num, by simp⟩⟩
  have hLT : IsPathConnected (L ∪ Top) := hLpc.union hTpc ⟨_, memL, memTopL⟩
  have hG : IsPathConnected ((L ∪ Top) ∪ Rt) := hLT.union hRpc ⟨_, Or.inr memTopR, memR⟩
  refine ⟨(L ∪ Top) ∪ Rt, hG,
    Or.inl (Or.inr ⟨by simp, by rw [mem_Icc]; exact ⟨by norm_num, by norm_num⟩⟩), ?_, ?_, ?_⟩
  · rintro p ((hpp | hpp) | hpp)
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ioc] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨by linarith [h1.1], h1.2⟩⟩
    · obtain ⟨h1, h0⟩ := hpp
      exact ⟨h0, by rw [mem_Icc, h1]; norm_num⟩
    · obtain ⟨h0, h1⟩ := hpp; rw [mem_Ioc] at h1
      exact ⟨by rw [mem_Icc, h0]; norm_num, by rw [mem_Icc]; exact ⟨by linarith [h1.1], h1.2⟩⟩
  · rintro p ((hpp | hpp) | hpp) hpr
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inl hpp.1); linarith [hpp.2.1]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inr (Or.inr hpp.1))); linarith [hpp.1]
    · have := curve_boundary_axis hm hp hfar p hpr (Or.inr (Or.inl hpp.1)); linarith [hpp.2.1]
  · intro p hp0 hp1 hnint hppos
    rcases not_and_or.mp hnint with hn0 | hn1
    · rw [mem_Ioo, not_and_or] at hn0
      rcases hn0 with h | h
      · exact Or.inl (Or.inl ⟨le_antisymm (not_lt.mp h) hp0.1, mem_Ioc.mpr ⟨hppos, hp1.2⟩⟩)
      · exact Or.inr ⟨le_antisymm hp0.2 (not_lt.mp h), mem_Ioc.mpr ⟨hppos, hp1.2⟩⟩
    · rw [mem_Ioo, not_and_or] at hn1
      rcases hn1 with h | h
      · exfalso; linarith [not_lt.mp h]
      · exact Or.inl (Or.inr ⟨le_antisymm hp1.2 (not_lt.mp h), hp0⟩)

/-- Points on the vertical axis are neither `!₂[-1,0]` nor `!₂[1,0]`. -/
lemma off_axis_endpoints {x : Plane} (hx : x 0 = 0) :
    x ∉ ({!₂[(-1:ℝ), 0], !₂[(1:ℝ), 0]} : Set Plane) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h) <;>
    (have hc := congrArg (fun w : Plane => w 0) h; simp only [hx] at hc; norm_num at hc)

/-- `tw * u ∈ [0, tw]` for a unit-interval scalar `u`. -/
lemma mul_unit_mem_Icc {tw u : ℝ} (htw : 0 ≤ tw) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    tw * u ∈ Icc (0:ℝ) tw := by
  rw [mem_Icc]
  refine ⟨mul_nonneg htw h0, ?_⟩
  calc tw * u ≤ tw * 1 := mul_le_mul_of_nonneg_left h1 htw
    _ = tw := mul_one tw

/-- The vertical segment from `x` up to `y` on the axis, parametrized over `[-1,1]`. -/
lemma axis_segment {x y : Plane} (hx0 : x 0 = 0) (hy0 : y 0 = 0) (hxy : x 1 ≤ y 1) :
    ∃ g : ℝ → Plane, ContinuousOn g (Icc (-1:ℝ) 1) ∧ g (-1) = x ∧ g 1 = y ∧
      (∀ t, g t 0 = 0) ∧ ∀ t ∈ Icc (-1:ℝ) 1, g t 1 ∈ Icc (x 1) (y 1) := by
  refine ⟨fun t => x + ((t + 1) / 2) • (y - x),
    (by fun_prop : Continuous fun t : ℝ => x + ((t + 1) / 2) • (y - x)).continuousOn,
    by show x + (((-1:ℝ) + 1) / 2) • (y - x) = x; module,
    by show x + (((1:ℝ) + 1) / 2) • (y - x) = y; module,
    fun t => by simp [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, hx0, hy0], ?_⟩
  intro t ht; rw [mem_Icc] at ht ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  have h0 : (0:ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have h1 : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
  have hd : (0:ℝ) ≤ y 1 - x 1 := by linarith
  constructor
  · linarith [mul_nonneg h0 hd]
  · linarith [mul_le_mul_of_nonneg_right h1 hd]

/-- The closed rectangle `[-1,1] × [-2,2]` is bounded. -/
lemma isBounded_rectE :
    IsBounded {w : Plane | w 0 ∈ Icc (-1:ℝ) 1 ∧ w 1 ∈ Icc (-2:ℝ) 2} := by
  apply (Metric.isBounded_closedBall (x := (0:Plane)) (r := 3)).subset
  intro z hz
  rw [Metric.mem_closedBall]
  have hz1 := hz.1; have hz2 := hz.2; rw [mem_Icc] at hz1 hz2
  have hsq : dist z (0:Plane) ^ 2 ≤ 9 := by
    rw [dist_sq_coord, show (0:Plane) 0 = 0 from by simp, show (0:Plane) 1 = 0 from by simp]
    nlinarith [hz1.1, hz1.2, hz2.1, hz2.2]
  nlinarith [dist_nonneg (x := z) (y := (0:Plane)), hsq]

/-- The open rectangle `(-1,1) × (-2,2)` is open. -/
lemma isOpen_rectO :
    IsOpen {w : Plane | w 0 ∈ Ioo (-1:ℝ) 1 ∧ w 1 ∈ Ioo (-2:ℝ) 2} := by
  have hEq : {w : Plane | w 0 ∈ Ioo (-1:ℝ) 1 ∧ w 1 ∈ Ioo (-2:ℝ) 2}
      = (fun w : Plane => w 0) ⁻¹' Ioo (-1:ℝ) 1 ∩ (fun w : Plane => w 1) ⁻¹' Ioo (-2:ℝ) 2 := by
    ext w; simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  rw [hEq]
  exact (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))

/-- The closed rectangle `[-1,1] × [-2,2]` is closed. -/
lemma isClosed_rectE :
    IsClosed {w : Plane | w 0 ∈ Icc (-1:ℝ) 1 ∧ w 1 ∈ Icc (-2:ℝ) 2} := by
  have hEq : {w : Plane | w 0 ∈ Icc (-1:ℝ) 1 ∧ w 1 ∈ Icc (-2:ℝ) 2}
      = (fun w : Plane => w 0) ⁻¹' Icc (-1:ℝ) 1 ∩ (fun w : Plane => w 1) ⁻¹' Icc (-2:ℝ) 2 := by
    ext w; simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  rw [hEq]
  exact (isClosed_Icc.preimage (by fun_prop)).inter (isClosed_Icc.preimage (by fun_prop))

/-- A point of the frontier `E ∖ O` on the horizontal axis is one of the endpoints
`!₂[±1, 0]`, hence on the curve. -/
lemma axis_zero_mem_range {r : sphere (0 : Plane) 1 → Plane}
    (hm : (!₂[(-1:ℝ), 0] : Plane) ∈ range r) (hp : (!₂[(1:ℝ), 0] : Plane) ∈ range r)
    {x : Plane} (hxIcc : x 0 ∈ Icc (-1:ℝ) 1)
    (hxO : ¬(x 0 ∈ Ioo (-1:ℝ) 1 ∧ x 1 ∈ Ioo (-2:ℝ) 2))
    (hx1 : x 1 = 0) : x ∈ range r := by
  have hnotIoo0 : x 0 ∉ Ioo (-1:ℝ) 1 := fun hIoo =>
    hxO ⟨hIoo, by rw [hx1, mem_Ioo]; constructor <;> norm_num⟩
  rw [mem_Ioo, not_and_or] at hnotIoo0
  rcases hnotIoo0 with h | h
  · have hx : x 0 = -1 := le_antisymm (not_lt.mp h) hxIcc.1
    rw [show x = !₂[(-1:ℝ), 0] from by ext i; fin_cases i <;> simp [hx, hx1]]; exact hm
  · have hx : x 0 = 1 := le_antisymm hxIcc.2 (not_lt.mp h)
    rw [show x = !₂[(1:ℝ), 0] from by ext i; fin_cases i <;> simp [hx, hx1]]; exact hp

end MatedCRTHarmonic.Planar.Jordan
