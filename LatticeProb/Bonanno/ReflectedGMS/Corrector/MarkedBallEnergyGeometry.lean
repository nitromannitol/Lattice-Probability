/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedBallEnergyGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BallEnergyReRooting
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedRootedSpecificEnergyMeasurability

/-!
# The random geometric constant of a graph ball

The re-rooting identity `BallEnergyReRooting.lintegral_rootedBallSum_eq` reads

`E[∑_{v ∈ B(H_0,R)} f(v)] = E[f(H_0) · W_R(H_0)]`,  `W_R(H) = (∑_{u : d(u,H) ≤ R} a_u) / a_H`.

The ball-to-root area ratio `W_R` is **not** integrable under the manuscript's (FE) moment, so
the right-hand side cannot be controlled by `E[f(H_0)]` directly.  This module supplies the
geometric half of the device that removes that obstruction without any new hypothesis:

* `slotAreaRatio R e n` — the ratio `W_R` read at a **code label**.  It is measurable in the
  environment (`measurable_slotAreaRatio`), similarity invariant
  (`slotAreaRatio_relabel`: both the ball area and the cell area pick up `s²`), and at the
  root it *is* `BallEnergyReRooting.rootedBallAreaRatio` (`slotBallArea_eq`).  Gating the
  observable by `1_{W_R ≤ M}` keeps it scale invariant and bounds the incoming side by
  `M · f(H_0)`.
* `rootedGeom R e` — one rooted random constant dominating, uniformly over the graph ball
  `B(H_0, R+1)`, the three geometric quantities that the re-rooting and the discrete Poincaré
  inequality need: the area ratio `W_R`, the cell area `a`, and the inverse conductances `1/c`
  (`slotAreaRatio_le_rootedGeom`, `volume_cell_le_rootedGeom`,
  `invConductance_le_rootedGeom`).
* `rootedGeom_ne_top` — it is **finite at every environment**.  Reachability sets are finite
  because conductance rows are finite (`Code.AdmissibleConductance.finiteRow`), which is all
  that is used (`finite_reach_ne_zero_right`, `finite_reach_ne_zero_left`).
* `measurable_rootedGeom` — it is measurable, through the slot-sum form of the root selector
  (`measurable_rootAt_elim`, a generic statement: any label observable vanishing at absent
  labels, read at the root cell, is measurable).
* `tendsto_measure_rootedGeom_gt` — hence `P(rootedGeom > M) → 0` as `M → ∞` for every finite
  law.  This is the only probabilistic statement here, and it uses nothing about the law.

Nothing here mentions a field, a stage, a grid mark or a mass-transport hypothesis.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.MarkedBallEnergyGeometry

open Code EnvironmentLaws RootDensities GraphBallReach Spatial
open RootedFiniteEnergyDensityMeasurable MarkedRootedSpecificEnergyMeasurability

/-! ### Finite reachability sets -/

/-- One step of the reachability recursion: a nonzero weight in `k + 1` steps is a nonzero
weight in `k` steps or a positive conductance out of the source followed by one. -/
theorem reach_succ_ne_zero {c : ℕ → ℕ → ℝ} {k n n' : ℕ} (h : reach c (k + 1) n n' ≠ 0) :
    reach c k n n' ≠ 0 ∨ ∃ x : ℕ, 0 < c n x ∧ reach c k x n' ≠ 0 := by
  rw [reach_succ] at h
  by_cases h1 : reach c k n n' = 0
  · right
    by_contra hcon
    push_neg at hcon
    have hsup : (⨆ x : ℕ, if 0 < c n x then reach c k x n' else 0) = 0 := by
      refine ENNReal.iSup_eq_zero.2 fun x => ?_
      by_cases hc : 0 < c n x
      · rw [if_pos hc]
        exact hcon x hc
      · rw [if_neg hc]
    exact h (by rw [h1, hsup, max_self])
  · exact Or.inl h1

/-- **The labels reachable from a fixed source form a finite set.**  Only the finiteness of
conductance rows is used. -/
theorem finite_reach_ne_zero_right (e : Env) (k : ℕ) :
    ∀ n : ℕ, {x : ℕ | reach e.val.2 k n x ≠ 0}.Finite := by
  have hadm : AdmissibleConductance e.val := e.property.choose
  induction k with
  | zero =>
      intro n
      refine (Set.finite_singleton n).subset fun x hx => ?_
      have hx' : reach e.val.2 0 n x ≠ 0 := hx
      rw [reach_zero] at hx'
      have hnx : n = x := by
        by_contra hnx
        exact hx' (if_neg hnx)
      exact hnx.symm
  | succ k ih =>
      intro n
      have hrow : {y : ℕ | 0 < e.val.2 n y}.Finite :=
        (hadm.finiteRow n).subset fun y hy => (show 0 < e.val.2 n y from hy).ne'
      refine ((ih n).union (hrow.biUnion fun y _ => ih y)).subset fun x hx => ?_
      have hx' : reach e.val.2 (k + 1) n x ≠ 0 := hx
      rcases reach_succ_ne_zero hx' with h | ⟨y, hy, h⟩
      · exact Or.inl h
      · exact Or.inr (Set.mem_biUnion hy h)

/-- **The labels from which a fixed target is reachable form a finite set.**  Finiteness of
conductance rows and their symmetry are used. -/
theorem finite_reach_ne_zero_left (e : Env) (k : ℕ) :
    ∀ x : ℕ, {y : ℕ | reach e.val.2 k y x ≠ 0}.Finite := by
  have hadm : AdmissibleConductance e.val := e.property.choose
  induction k with
  | zero =>
      intro x
      refine (Set.finite_singleton x).subset fun y hy => ?_
      have hy' : reach e.val.2 0 y x ≠ 0 := hy
      rw [reach_zero] at hy'
      have hyx : y = x := by
        by_contra hyx
        exact hy' (if_neg hyx)
      exact hyx
  | succ k ih =>
      intro x
      have hnb : (⋃ z ∈ {z : ℕ | reach e.val.2 k z x ≠ 0}, {y : ℕ | 0 < e.val.2 z y}).Finite :=
        (ih x).biUnion fun z _ =>
          (hadm.finiteRow z).subset fun y hy => (show 0 < e.val.2 z y from hy).ne'
      refine ((ih x).union hnb).subset fun y hy => ?_
      have hy' : reach e.val.2 (k + 1) y x ≠ 0 := hy
      rcases reach_succ_ne_zero hy' with h | ⟨z, hz, h⟩
      · exact Or.inl h
      · refine Or.inr (Set.mem_biUnion h ?_)
        show 0 < e.val.2 z y
        rw [hadm.symm z y]
        exact hz

/-! ### Finiteness of series and suprema with finite support -/

theorem tsum_ne_top_of_finite_support {f : ℕ → ℝ≥0∞} {S : Set ℕ} (hS : S.Finite)
    (h0 : ∀ x, x ∉ S → f x = 0) (hfin : ∀ x, x ∈ S → f x ≠ ∞) : ∑' x, f x ≠ ∞ := by
  rw [tsum_eq_sum (s := hS.toFinset) fun x hx => h0 x (by simpa using hx)]
  exact (ENNReal.sum_lt_top.2 fun x hx => (hfin x (by simpa using hx)).lt_top).ne

theorem iSup_ne_top_of_finite_support {f : ℕ → ℝ≥0∞} {S : Set ℕ} (hS : S.Finite)
    (h0 : ∀ x, x ∉ S → f x = 0) (hfin : ∀ x, x ∈ S → f x ≠ ∞) : (⨆ x, f x) ≠ ∞ :=
  ne_top_of_le_ne_top (tsum_ne_top_of_finite_support hS h0 hfin)
    (iSup_le fun x => ENNReal.le_tsum x)

/-! ### The ball-to-cell area ratio at a code label -/

/-- The area of the reachability ball *into* a vertex, summed over the decoded vertices. -/
noncomputable def vertexBallArea (R : ℕ) (e : Env) (v : Vertex e.val) : ℝ≥0∞ :=
  ∑' w : Vertex e.val, reach e.val.2 R w.val v.val * volume ((decode e).cell w : Set Plane)

/-- The same area, summed over all code labels. -/
noncomputable def slotBallArea (R : ℕ) (e : Env) (n : ℕ) : ℝ≥0∞ :=
  ∑' x : ℕ, reach e.val.2 R x n * volume (slotCell e x : Set Plane)

/-- **The area ratio `W_R` at a code label.** -/
noncomputable def slotAreaRatio (R : ℕ) (e : Env) (n : ℕ) : ℝ≥0∞ :=
  slotBallArea R e n / volume (slotCell e n : Set Plane)

/-- At an active label the slot sum is the vertex sum: absent labels reach nothing else. -/
theorem slotBallArea_eq (R : ℕ) (e : Env) (v : Vertex e.val) :
    slotBallArea R e v.val = vertexBallArea R e v := by
  have hsupp : Function.support
      (fun x : ℕ => reach e.val.2 R x v.val * volume (slotCell e x : Set Plane))
      ⊆ {x : ℕ | (e.val.1 x).isSome} := by
    intro x hx
    by_contra hmem
    have hnone : e.val.1 x = none := by
      rw [← Option.not_isSome_iff_eq_none]
      exact hmem
    have hne : x ≠ v.val := by
      intro hxv
      apply hmem
      rw [hxv]
      exact v.property
    apply hx
    show reach e.val.2 R x v.val * volume (slotCell e x : Set Plane) = 0
    rw [reach_eq_zero_of_absent e hnone R hne, zero_mul]
  calc slotBallArea R e v.val
      = ∑' x : {x : ℕ | (e.val.1 x).isSome},
          reach e.val.2 R x.val v.val * volume (slotCell e x.val : Set Plane) :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' w : Vertex e.val,
          reach e.val.2 R w.val v.val * volume (slotCell e w.val : Set Plane) := rfl
    _ = vertexBallArea R e v := tsum_congr fun w => by rw [slotCell_eq_cell]

theorem measurable_slotBallArea (R n : ℕ) : Measurable fun e : Env => slotBallArea R e n :=
  Measurable.ennreal_tsum fun x =>
    (measurable_reach R x n).mul (measurable_cellVolume.comp (measurable_slotCell_env x))

theorem measurable_slotAreaRatio (R n : ℕ) : Measurable fun e : Env => slotAreaRatio R e n :=
  (measurable_slotBallArea R n).div (measurable_cellVolume.comp (measurable_slotCell_env n))

/-- The vertex ball area scales by `s²` along a similarity relabelling. -/
theorem vertexBallArea_relabel {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {rel : Vertex e.val ≃ Vertex e'.val} (h : IsSimilarityRelabel s u hs e e' rel) (R : ℕ)
    (v : Vertex e.val) :
    vertexBallArea R e' (rel v) = ENNReal.ofReal (s ^ 2) * vertexBallArea R e v := by
  unfold vertexBallArea
  rw [← Equiv.tsum_eq rel (fun w' : Vertex e'.val =>
      reach e'.val.2 R w'.val (rel v).val * volume ((decode e').cell w' : Set Plane)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun w => ?_
  show reach e'.val.2 R (rel w).val (rel v).val * volume ((decode e').cell (rel w) : Set Plane)
    = ENNReal.ofReal (s ^ 2) * (reach e.val.2 R w.val v.val * volume ((decode e).cell w : Set Plane))
  rw [reach_relabel h R w v, h.1 w, coe_transformCell, volume_image_positiveSimilarity]
  ring

/-- **The area ratio is similarity invariant.** -/
theorem slotAreaRatio_relabel {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {rel : Vertex e.val ≃ Vertex e'.val} (h : IsSimilarityRelabel s u hs e e' rel) (R : ℕ)
    (v : Vertex e.val) :
    slotAreaRatio R e' (rel v).val = slotAreaRatio R e v.val := by
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hc0 : ENNReal.ofReal (s ^ 2) ≠ 0 := by simpa using hs2.ne'
  unfold slotAreaRatio
  rw [slotBallArea_eq R e' (rel v), slotBallArea_eq R e v, slotCell_eq_cell e' (rel v),
    slotCell_eq_cell e v, vertexBallArea_relabel h R v, h.1 v, coe_transformCell,
    volume_image_positiveSimilarity, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]

/-! ### Inverse conductances -/

/-- The inverse conductance `1 / c(n, x)` of an edge, and `0` off the edges. -/
noncomputable def invConductance (e : Env) (n x : ℕ) : ℝ≥0∞ :=
  if 0 < e.val.2 n x then ENNReal.ofReal (e.val.2 n x)⁻¹ else 0

theorem measurable_invConductance (n x : ℕ) :
    Measurable fun e : Env => invConductance e n x :=
  Measurable.ite (measurableSet_lt measurable_const (measurable_conductance_env n x))
    (measurable_conductance_env n x).inv.ennreal_ofReal measurable_const

/-! ### The rooted geometric constant -/

/-- The geometric quantities at one label: area ratio, cell area and the largest inverse
conductance of an edge out of it. -/
noncomputable def geomTerm (R : ℕ) (e : Env) (x : ℕ) : ℝ≥0∞ :=
  if (e.val.1 x).isSome then
    slotAreaRatio R e x + volume (slotCell e x : Set Plane) + ⨆ y : ℕ, invConductance e x y
  else 0

/-- Their supremum over the reachability ball of a label. -/
noncomputable def geomSup (R : ℕ) (e : Env) (n : ℕ) : ℝ≥0∞ :=
  if (e.val.1 n).isSome then ⨆ x : ℕ, reach e.val.2 R n x * geomTerm R e x else 0

/-- **The rooted random geometric constant** of the graph ball `B(H_0, R+1)`. -/
noncomputable def rootedGeom (R : ℕ) (e : Env) : ℝ≥0∞ :=
  (rootAt (decode e) 0).elim 0 fun r => geomSup R e r.val

theorem measurableSet_slotIsSome_env (n : ℕ) : MeasurableSet {e : Env | (e.val.1 n).isSome} :=
  HarmonicCoordinateAssembly.measurable_slot n measurableSet_slotIsSome

theorem measurable_geomTerm (R x : ℕ) : Measurable fun e : Env => geomTerm R e x :=
  Measurable.ite (measurableSet_slotIsSome_env x)
    (((measurable_slotAreaRatio R x).add
      (measurable_cellVolume.comp (measurable_slotCell_env x))).add
      (Measurable.iSup fun y => measurable_invConductance x y))
    measurable_const

theorem measurable_geomSup (R n : ℕ) : Measurable fun e : Env => geomSup R e n :=
  Measurable.ite (measurableSet_slotIsSome_env n)
    (Measurable.iSup fun x => (measurable_reach R n x).mul (measurable_geomTerm R x))
    measurable_const

/-- **Measurability of a label observable read at the root cell.**  Any label observable that
is measurable label by label and vanishes at absent labels is measurable once read at the
boundary-masked root: off the mask exactly one label has the origin in its cell interior, and
on the mask the rooted value is `0` by convention.  This is the slot-sum technique of
`Spatial/RootedFiniteEnergyDensityMeasurable`, stated once for an arbitrary observable. -/
theorem measurable_rootAt_elim {Ω : Type*} [MeasurableSpace Ω] {E : Ω → Env}
    (hE : Measurable E) {f : Ω → ℕ → ℝ≥0∞} (hf : ∀ n : ℕ, Measurable fun ω => f ω n)
    (habs : ∀ (ω : Ω) (n : ℕ), (E ω).val.1 n = none → f ω n = 0) :
    Measurable fun ω => (rootAt (decode (E ω)) 0).elim 0 fun r => f ω r.val := by
  have hEq : (fun ω => (rootAt (decode (E ω)) 0).elim 0 fun r => f ω r.val)
      = Set.indicator (maskAt E)ᶜ
          (fun ω => ∑' n : ℕ, (rootSlotSet E n).indicator (fun ω' => f ω' n) ω) := by
    funext ω
    by_cases hz : (0 : Plane) ∈ boundaryMask (decode (E ω))
    · have hmem : ω ∉ (maskAt E)ᶜ := fun h => h hz
      rw [Set.indicator_of_notMem hmem, rootAt_eq_none_of_mem_boundaryMask (decode (E ω)) hz]
      rfl
    · have hgeom := decode_geometry (E ω)
      have hmem : ω ∈ (maskAt E)ᶜ := hz
      obtain ⟨v, hv, hint⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode (E ω)) hgeom hz
      have huniq := existsUnique_interiorRoot_of_not_mem_boundaryMask (decode (E ω)) hgeom hz
      have hsingle : ∀ n : ℕ, n ≠ v.val →
          (rootSlotSet E n).indicator (fun ω' => f ω' n) ω = 0 := by
        intro n hn
        cases hcase : (E ω).val.1 n with
        | none =>
            by_cases hmemn : ω ∈ rootSlotSet E n
            · rw [Set.indicator_of_mem hmemn]
              exact habs ω n hcase
            · rw [Set.indicator_of_notMem hmemn]
        | some K =>
            have hsome : ((E ω).val.1 n).isSome := by rw [hcase]; rfl
            have hne : (⟨n, hsome⟩ : Vertex (E ω).val) ≠ v :=
              fun h => hn (congrArg Subtype.val h)
            have hnot : ω ∉ rootSlotSet E n := by
              intro hmemn
              have hmem' : (0 : Plane) ∈
                  interior ((decode (E ω)).cell ⟨n, hsome⟩ : Set Plane) := by
                rw [← slotCell_eq_cell (E ω) ⟨n, hsome⟩]
                exact hmemn
              exact hne (huniq.unique hmem' hint)
            rw [Set.indicator_of_notMem hnot]
      have hmemv : ω ∈ rootSlotSet E v.val := by
        show (0 : Plane) ∈ interior (slotCell (E ω) v.val : Set Plane)
        rw [slotCell_eq_cell]
        exact hint
      rw [Set.indicator_of_mem hmem, tsum_eq_single v.val hsingle,
        Set.indicator_of_mem hmemv, hv]
      rfl
  rw [hEq]
  exact (Measurable.ennreal_tsum fun n =>
    (hf n).indicator (measurableSet_rootSlotSet hE n)).indicator (measurableSet_maskAt hE).compl

theorem geomSup_of_absent (R : ℕ) (e : Env) {n : ℕ} (hn : e.val.1 n = none) :
    geomSup R e n = 0 := by
  simp [geomSup, hn]

theorem measurable_rootedGeom (R : ℕ) : Measurable (rootedGeom R) :=
  measurable_rootAt_elim (E := fun e : Env => e) measurable_id'
    (f := fun e n => geomSup R e n) (fun n => measurable_geomSup R n)
    (fun e _ hn => geomSup_of_absent R e hn)

/-! ### Finiteness at every environment -/

theorem geomTerm_ne_top (R : ℕ) (e : Env) (x : ℕ) : geomTerm R e x ≠ ∞ := by
  have hadm : AdmissibleConductance e.val := e.property.choose
  unfold geomTerm
  split_ifs with hx
  · have hpos := cellVolume_pos_lt_top (decode e) (decode_geometry e) ⟨x, hx⟩
    have hvol : volume (slotCell e x : Set Plane)
        = volume ((decode e).cell ⟨x, hx⟩ : Set Plane) :=
      congrArg (fun K : CompactCell => volume (K : Set Plane)) (slotCell_eq_cell e ⟨x, hx⟩)
    have hW : slotAreaRatio R e x ≠ ∞ := by
      unfold slotAreaRatio
      refine (ENNReal.div_lt_top ?_ ?_).ne
      · refine tsum_ne_top_of_finite_support (finite_reach_ne_zero_left e R x)
          (fun y hy => ?_) (fun y _ => ?_)
        · have hy' : reach e.val.2 R y x = 0 := by simpa using hy
          show reach e.val.2 R y x * volume (slotCell e y : Set Plane) = 0
          rw [hy', zero_mul]
        · exact ENNReal.mul_ne_top
            (ne_top_of_le_ne_top ENNReal.one_ne_top (reach_le_one e.val.2 R y x))
            (slotCell e y).isCompact.measure_lt_top.ne
      · rw [hvol]
        exact hpos.1.ne'
    have hV : volume (slotCell e x : Set Plane) ≠ ∞ :=
      (slotCell e x).isCompact.measure_lt_top.ne
    have hC : (⨆ y : ℕ, invConductance e x y) ≠ ∞ := by
      refine iSup_ne_top_of_finite_support (hadm.finiteRow x) (fun y hy => ?_) (fun y _ => ?_)
      · have hy' : e.val.2 x y = 0 := by simpa [Function.mem_support] using hy
        show invConductance e x y = 0
        unfold invConductance
        rw [if_neg (show ¬ (0 < e.val.2 x y) by rw [hy']; exact lt_irrefl 0)]
      · show invConductance e x y ≠ ∞
        unfold invConductance
        split_ifs
        · exact ENNReal.ofReal_ne_top
        · exact ENNReal.zero_ne_top
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hW, hV⟩, hC⟩
  · exact ENNReal.zero_ne_top

theorem geomSup_ne_top (R : ℕ) (e : Env) (n : ℕ) : geomSup R e n ≠ ∞ := by
  unfold geomSup
  split_ifs
  · refine iSup_ne_top_of_finite_support (finite_reach_ne_zero_right e R n)
      (fun x hx => ?_) (fun x _ => ?_)
    · have hx' : reach e.val.2 R n x = 0 := by simpa using hx
      show reach e.val.2 R n x * geomTerm R e x = 0
      rw [hx', zero_mul]
    · exact ENNReal.mul_ne_top
        (ne_top_of_le_ne_top ENNReal.one_ne_top (reach_le_one e.val.2 R n x))
        (geomTerm_ne_top R e x)
  · exact ENNReal.zero_ne_top

/-- **The rooted geometric constant is finite at every environment.** -/
theorem rootedGeom_ne_top (R : ℕ) (e : Env) : rootedGeom R e ≠ ∞ := by
  unfold rootedGeom
  cases rootAt (decode e) 0 with
  | none => exact ENNReal.zero_ne_top
  | some r => exact geomSup_ne_top R e r.val

/-! ### Domination over the graph ball -/

theorem geomTerm_le_rootedGeom {R : ℕ} {e : Env} {r : Vertex e.val}
    (hr : rootAt (decode e) 0 = some r) {v : Vertex e.val}
    (hv : v ∈ (decode e).graph.toSimpleGraph.ball r ((R + 1 : ℕ) : ℕ∞)) :
    geomTerm R e v.val ≤ rootedGeom R e := by
  have hone : 1 ≤ reach e.val.2 R r.val v.val := one_le_reach_of_mem_ball e r R hv
  unfold rootedGeom
  rw [hr]
  show geomTerm R e v.val ≤ geomSup R e r.val
  unfold geomSup
  rw [if_pos r.property]
  calc geomTerm R e v.val = 1 * geomTerm R e v.val := (one_mul _).symm
    _ ≤ reach e.val.2 R r.val v.val * geomTerm R e v.val := mul_le_mul' hone le_rfl
    _ ≤ ⨆ x : ℕ, reach e.val.2 R r.val x * geomTerm R e x :=
        le_iSup (fun x : ℕ => reach e.val.2 R r.val x * geomTerm R e x) v.val

theorem slotAreaRatio_le_rootedGeom {R : ℕ} {e : Env} {r : Vertex e.val}
    (hr : rootAt (decode e) 0 = some r) {v : Vertex e.val}
    (hv : v ∈ (decode e).graph.toSimpleGraph.ball r ((R + 1 : ℕ) : ℕ∞)) :
    slotAreaRatio R e v.val ≤ rootedGeom R e := by
  refine le_trans ?_ (geomTerm_le_rootedGeom hr hv)
  unfold geomTerm
  rw [if_pos v.property]
  exact le_add_right (le_add_right le_rfl)

theorem volume_cell_le_rootedGeom {R : ℕ} {e : Env} {r : Vertex e.val}
    (hr : rootAt (decode e) 0 = some r) {v : Vertex e.val}
    (hv : v ∈ (decode e).graph.toSimpleGraph.ball r ((R + 1 : ℕ) : ℕ∞)) :
    volume ((decode e).cell v : Set Plane) ≤ rootedGeom R e := by
  refine le_trans ?_ (geomTerm_le_rootedGeom hr hv)
  unfold geomTerm
  rw [if_pos v.property, slotCell_eq_cell e v]
  exact le_add_right (le_add_left le_rfl)

theorem invConductance_le_rootedGeom {R : ℕ} {e : Env} {r : Vertex e.val}
    (hr : rootAt (decode e) 0 = some r) {v : Vertex e.val}
    (hv : v ∈ (decode e).graph.toSimpleGraph.ball r ((R + 1 : ℕ) : ℕ∞)) (y : ℕ) :
    invConductance e v.val y ≤ rootedGeom R e := by
  refine le_trans ?_ (geomTerm_le_rootedGeom hr hv)
  unfold geomTerm
  rw [if_pos v.property]
  exact le_add_left (le_iSup (fun y : ℕ => invConductance e v.val y) y)

/-! ### The tail of the geometric constant -/

/-- **`P(rootedGeom > M) → 0` for every finite law.**  The events decrease in `M`, are
measurable, and have empty intersection because the constant is finite everywhere. -/
theorem tendsto_measure_rootedGeom_gt {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {E : α → Env} (hE : Measurable E) (R : ℕ) :
    Tendsto (fun M : ℕ => μ {a | (M : ℝ≥0∞) < rootedGeom R (E a)}) atTop (𝓝 0) := by
  have hmeas : ∀ M : ℕ, NullMeasurableSet {a | (M : ℝ≥0∞) < rootedGeom R (E a)} μ :=
    fun M => (measurableSet_lt measurable_const
      ((measurable_rootedGeom R).comp hE)).nullMeasurableSet
  have hanti : Antitone fun M : ℕ => {a | (M : ℝ≥0∞) < rootedGeom R (E a)} := by
    intro M N hMN a ha
    have hMN' : (M : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by exact_mod_cast hMN
    have ha' : (N : ℝ≥0∞) < rootedGeom R (E a) := ha
    exact lt_of_le_of_lt hMN' ha'
  have hempty : (⋂ M : ℕ, {a | (M : ℝ≥0∞) < rootedGeom R (E a)}) = ∅ := by
    ext a
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_lt]
    obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt (rootedGeom_ne_top R (E a))
    exact ⟨M, hM.le⟩
  have h := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top μ _⟩
  simpa [Function.comp_def, hempty] using h

end ReflectedGMS.MarkedBallEnergyGeometry
