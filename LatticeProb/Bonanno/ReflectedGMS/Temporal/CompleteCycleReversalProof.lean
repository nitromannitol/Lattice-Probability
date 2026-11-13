/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CompleteCycleReversalProof at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CompleteCycleReversalGrid
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FirstCycleLaw
import LatticeProb.Bonanno.ReflectedGMS.Forms.AreaTransitionReversibility

/-!
# Clause (b) at the actual walk: `CompleteCycleReversal (firstCycleLaw …)` (milestone 2(b))

`Temporal/FirstCycleLaw.firstCycleLaw G hwalk n e` is the law of the first complete cycle
(holding at slot `n`, then the excursion, killed at the first complete return) of the actual
area-clock walk of `e` started at slot `n`, in the label coding.  This module proves

* **`completeCycleReversal_firstCycleLaw`**: `CompleteCycleReversal (firstCycleLaw G hwalk n e)`
  for EVERY `G`, `hwalk`, `n`, `e` — on the live set from reversibility of the walk, off it
  because the law is the point mass at the `cycRev`-fixed default cycle;
* **`hcyc_rootedRegKernel_of_decomposition`**: `hcyc` at the actual kernel from clause (c)
  alone, at `ν = firstCycleLaw` (the input of `TwoSidedCycleSpliceKernel.hcyc_rootedRegKernel`
  with clause (b) discharged).

## Route

`Temporal/CompleteCycleReversalGrid.completeCycleReversal_of_grid` reduces clause (b) to two
facts about the lifted slot law `regSlotLaw`:

1. **grid block reversal** (`label_grid_reversal`): on the grid of mesh `1/(N+1)`, a word that
   holds at the start `z` on `[0,a)` and is back at `z` at `n` has the same probability as its
   block reversal on `[a, n)`.  If all letters are vertex labels, the word event is the
   vertex grid cylinder `reflectedGridEvent`, whose probability is the product of the walk's
   own transition probabilities (`TwoSided.reflectedGridEvent_start_real_processTransition`,
   Markov property only); the prefix factors agree and the loop factors
   `z → w_a → ⋯ → w_{n-1} → z` are reversed by detailed balance
   (`TwoSided.processTransition_grid_path_weight_reverse`) with respect to the cell area
   (`AreaReversibility.processTransitionReversible_cellArea`, no summability), the two end
   weights `area(z)` cancelling.  Otherwise both events are null (property (i): the walk is at a
   vertex at every fixed time);
2. **good paths** (`ae_good_regSlotLaw`): almost every lifted path starts at `n` and returns,
   so it is a regular complete cycle (`FirstCycleLaw.exists_hold_of_fwdReturn`) whose first
   cycle is `firstCycle n` (`firstCycle_of_good`); the return is finite by
   `CadlagRegenerationActual.ae_isRegenPath`, transported to the label coding
   (`isRegenPath_labelTraj`).

No semigroup identification, no summability of the speed, no non-explosion input.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CycleReversalProof

open Code EnvironmentLaws AreaClocks RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.RegenerationKernel
open ReflectedGMS.CadlagRegeneration ReflectedGMS.RegenerativeInvarianceFiberwise
open ReflectedGMS.TwoSidedCycleSplice ReflectedGMS.FirstCycleLaw ReflectedGMS.CycleReversalGrid

/-! ### 1. Path weights under block reversal -/

/-- The block reversal of `[a, n)` on vertex sequences. -/
def vblockRev {V : Type*} (a n : ℕ) (f : ℕ → V) : ℕ → V :=
  fun k => if a ≤ k ∧ k < n then f (n + a - 1 - k) else f k

section Weights

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  [Nontrivial V] [DecidableEq V]

/-- **Detailed balance reverses the loop block of a grid path.**  If the vertex before the
block and the vertex after it coincide, the path weight is unchanged by reversing the block. -/
theorem prod_vblockRev (PF : ProcessFamily V) (m : V → ℝ) (δ : ℝ≥0)
    (hrev : TwoSided.ProcessTransitionReversible PF m δ) (hm : ∀ u, 0 < m u)
    {a n : ℕ} (ha : 1 ≤ a) (han : a ≤ n) (f : ℕ → V) (hloop : f (a - 1) = f n) :
    ∏ k ∈ Finset.range n,
        TwoSided.processTransition PF δ (vblockRev a n f k) (vblockRev a n f (k + 1)) =
      ∏ k ∈ Finset.range n, TwoSided.processTransition PF δ (f k) (f (k + 1)) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', n = b + m' := ⟨n - (b + 1) + 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hloop
  rw [Finset.prod_range_add, Finset.prod_range_add]
  congr 1
  · refine Finset.prod_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    simp only [vblockRev]
    rw [if_neg (by omega), if_neg (by omega)]
  · have hbal := TwoSided.processTransition_grid_path_weight_reverse PF m δ hrev
      (fun j => f (b + j)) m'
    simp only [add_zero] at hbal
    rw [hloop] at hbal
    have hc := mul_left_cancel₀ (hm (f (b + m'))).ne' hbal
    calc ∏ x ∈ Finset.range m', TwoSided.processTransition PF δ
            (vblockRev (b + 1) (b + m') f (b + x)) (vblockRev (b + 1) (b + m') f (b + x + 1))
        = ∏ i ∈ Finset.range m', TwoSided.processTransition PF δ
            (f (b + (m' - i))) (f (b + (m' - (i + 1)))) := by
          refine Finset.prod_congr rfl fun j hj => ?_
          have hj' := Finset.mem_range.1 hj
          congr 1
          · simp only [vblockRev]
            split_ifs with hcnd
            · congr 1
              omega
            · have hj0 : j = 0 := by omega
              subst hj0
              simp only [add_zero, Nat.sub_zero]
              exact hloop
          · simp only [vblockRev]
            split_ifs with hcnd
            · congr 1
              omega
            · have hjm : j + 1 = m' := by omega
              rw [show m' - (j + 1) = 0 by omega, add_zero, show b + j + 1 = b + m' by omega]
              exact hloop.symm
      _ = ∏ i ∈ Finset.range m', TwoSided.processTransition PF δ (f (b + i)) (f (b + (i + 1))) :=
          hc.symm
      _ = ∏ x ∈ Finset.range m', TwoSided.processTransition PF δ (f (b + x)) (f (b + x + 1)) := by
          simp only [add_assoc]

end Weights

/-! ### 2. Grid block reversal for the label coding of a reflected walk -/

section Grid

variable {r : RawCode} [Nontrivial (Vertex r)]

/-- The word events of the label coding are vertex grid cylinders. -/
theorem labelGridEvent_eq (PF : ProcessFamily (Vertex r)) (N n : ℕ) (u : ℕ → Vertex r)
    (w : Fin (n + 1) → Option ℕ) (hw : ∀ k : Fin (n + 1), w k = some (u k).val) :
    PF.trajectory ⁻¹' (labelTraj ⁻¹' (gridWord N n ⁻¹' {w})) =
      ReflectedGMS.reflectedGridEvent PF (gδ N) n u := by
  ext ω
  simp only [mem_preimage, mem_singleton_iff, ReflectedGMS.reflectedGridEvent, Finset.mem_range,
    mem_setOf_eq]
  constructor
  · intro hω i hi
    have h1 := congrFun hω ⟨i, hi⟩
    rw [hw] at h1
    obtain ⟨u', hx, hu'⟩ := labelTraj_eq_some.1 h1
    rw [show PF.X ((i : ℝ≥0) * gδ N) ω = some u' from hx, Subtype.ext hu']
  · intro hω
    funext k
    rw [hw]
    exact labelTraj_eq_some.2 ⟨u k, hω k k.isLt, rfl⟩

/-- A word event with a letter that is not a vertex label is null. -/
theorem measure_labelGridEvent_eq_zero (PF : ProcessFamily (Vertex r)) (z : Vertex r)
    (hdef : ∀ t, ∀ᵐ ω ∂PF.P z, ∃ x, PF.X t ω = some x) (N n : ℕ)
    (w : Fin (n + 1) → Option ℕ) (hw : ¬ ∀ k, ∃ u : Vertex r, w k = some u.val) :
    PF.P z (PF.trajectory ⁻¹' (labelTraj ⁻¹' (gridWord N n ⁻¹' {w}))) = 0 := by
  push_neg at hw
  obtain ⟨k, hk⟩ := hw
  have hnull := ae_iff.1 (hdef (((k : ℕ) : ℝ≥0) * gδ N))
  refine measure_mono_null ?_ hnull
  intro ω hω
  simp only [mem_setOf_eq]
  rintro ⟨x, hx⟩
  have h1 := congrFun (show gridWord N n (labelTraj (PF.trajectory ω)) = w from hω) k
  have h2 : labelTraj (PF.trajectory ω) (((k : ℕ) : ℝ≥0) * gδ N) = some x.val :=
    labelTraj_eq_some.2 ⟨x, hx, rfl⟩
  exact hk x (h1.symm.trans h2)

omit [Nontrivial (Vertex r)] in
theorem allVertex_wordRev {a n : ℕ} {w : Fin (n + 1) → Option ℕ}
    (hw : ∀ k, ∃ u : Vertex r, w k = some u.val) :
    ∀ k, ∃ u : Vertex r, wordRev a w k = some u.val := by
  intro k
  simp only [wordRev]
  split_ifs
  · exact hw _
  · exact hw k

/-- **Grid block reversal for the label coding of a reversible reflected walk.** -/
theorem label_grid_reversal {G : ConductanceGraph (Vertex r)} {rate : Vertex r → ℝ}
    {hmin : G.EnergyMinimizer} {PF : ProcessFamily (Vertex r)}
    (h : IsReflectedWalk G rate hmin PF) (m : Vertex r → ℝ) (hm : ∀ u, 0 < m u)
    (hrev : ∀ δ, TwoSided.ProcessTransitionReversible PF m δ) (z : Vertex r)
    (N a n : ℕ) (w : Fin (n + 1) → Option ℕ) (hw : DCyc z.val a n (wext w)) :
    PF.P z (PF.trajectory ⁻¹' (labelTraj ⁻¹' (gridWord N n ⁻¹' {w}))) =
      PF.P z (PF.trajectory ⁻¹' (labelTraj ⁻¹' (gridWord N n ⁻¹' {wordRev a w}))) := by
  classical
  have hdef : ∀ t, ∀ᵐ ω ∂PF.P z, ∃ x, PF.X t ω = some x := fun t => by
    filter_upwards [(h z).2.1 t] with ω hω
    exact hω.1
  by_cases hall : ∀ k, ∃ u : Vertex r, w k = some u.val
  · choose uf huf using hall
    let useq : ℕ → Vertex r := fun k => if hk : k < n + 1 then uf ⟨k, hk⟩ else z
    have hw1 : ∀ k : Fin (n + 1), w k = some (useq k).val := fun k => by
      simp only [useq, dif_pos k.isLt, Fin.eta]
      exact huf k
    have hw2 : ∀ k : Fin (n + 1), wordRev a w k = some (vblockRev a n useq k).val := fun k => by
      simp only [wordRev, vblockRev]
      split_ifs with hc
      · exact hw1 _
      · exact hw1 k
    have hval : ∀ k, k ≤ n → wext w k = some (useq k).val := fun k hk => by
      simp only [wext, dif_pos (Nat.lt_succ_of_le hk)]
      exact hw1 ⟨k, Nat.lt_succ_of_le hk⟩
    have hz : ∀ k, k ≤ n → wext w k = some z.val → useq k = z := fun k hk hkz => by
      rw [hval k hk] at hkz
      exact Subtype.ext (Option.some_injective _ hkz)
    have ha := hw.one_le
    have han := hw.lt
    have h0 : useq 0 = z := hz 0 (by omega) (hw.hold 0 (by omega))
    have h0' : vblockRev a n useq 0 = z := by
      simp only [vblockRev]
      rw [if_neg (by omega)]
      exact h0
    have hloop : useq (a - 1) = useq n := by
      rw [hz (a - 1) (by omega) (hw.hold (a - 1) (by omega)), hz n le_rfl hw.ret]
    rw [labelGridEvent_eq PF N n useq w hw1, labelGridEvent_eq PF N n _ _ hw2]
    have hA := TwoSided.reflectedGridEvent_start_real_processTransition h (gδ N) n useq
    have hB := TwoSided.reflectedGridEvent_start_real_processTransition h (gδ N) n
      (vblockRev a n useq)
    rw [h0] at hA
    rw [h0'] at hB
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [← measureReal_def, ← measureReal_def, hA, hB,
      prod_vblockRev PF m (gδ N) (hrev _) hm ha han.le useq hloop]
  · have hall' : ¬ ∀ k, ∃ u : Vertex r, wordRev a w k = some u.val := fun h' => by
      apply hall
      rw [← wordRev_wordRev a w]
      exact allVertex_wordRev h'
    rw [measure_labelGridEvent_eq_zero PF z hdef N n w hall,
      measure_labelGridEvent_eq_zero PF z hdef N n _ hall']

omit [Nontrivial (Vertex r)] in
/-- The regenerative coding transports to the label coding. -/
theorem isRegenPath_labelTraj {z : Vertex r} {y : Trajectory (Vertex r)} (hy : IsRegenPath z y) :
    IsRegenPath z.val (labelTraj y) where
  regular := rightRegularAt_labelTraj hy.regular
  start := labelTraj_eq_some.2 ⟨z, hy.start, rfl⟩
  leaves T := by
    obtain ⟨t, hT, ht⟩ := hy.leaves T
    refine ⟨t, hT, fun h' => ht ?_⟩
    obtain ⟨u, hu, huz⟩ := labelTraj_eq_some.1 h'
    rw [hu, Subtype.ext huz]
  recurs T := by
    obtain ⟨t, hT, ht⟩ := hy.recurs T
    exact ⟨t, hT, labelTraj_eq_some.2 ⟨z, ht, rfl⟩⟩
  dense a b hab := by
    obtain ⟨s, h1, h2, hs⟩ := hy.dense a b hab
    refine ⟨s, h1, h2, fun h' => hs ?_⟩
    rw [labelTraj_apply] at h'
    cases hys : y s with
    | none => rfl
    | some u => rw [hys] at h'; exact absurd h' (by simp)

end Grid

/-! ### 3. Clause (b) at the first-cycle law -/

/-- Almost every lifted path starts at the slot and returns. -/
theorem ae_good_regSlotLaw (G : Set Env) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (n : ℕ) (e : Env) (hlive : e ∈ G ∧ (e.val.1 n).isSome) :
    ∀ᵐ x ∂regSlotLaw G hwalk n e, x.1 0 = some n ∧ fwdReturn x.1 ≠ ⊤ := by
  haveI := nontrivial_vertex e
  have hadm := hwalk e hlive.1
  have hW := isReflectedWalk_areaFamily e hadm
  let z : Vertex e.val := ⟨n, hlive.2⟩
  have hGm := (measurableSet_goodStart n).compl
  obtain ⟨B, hB, hBeq⟩ := MeasurableSpace.measurableSet_comap.1 hGm
  rw [ae_iff]
  show regSlotLaw G hwalk n e {x : RegLL | x.1 0 = some n ∧ fwdReturn x.1 ≠ ⊤}ᶜ = 0
  rw [← hBeq, ← Measure.map_apply measurable_subtype_coe hB, regSlotLaw_map_val,
    slotLaw_apply_of_mem hlive.1 hlive.2 hB]
  have hae : ∀ᵐ ω ∂(areaFamily e).P z, labelTraj ((areaFamily e).trajectory ω) ∉ B := by
    filter_upwards [ae_isRegenPath hW z, ae_isRegLL_label e hadm z] with ω h1 h2
    intro hmem
    have hx : (⟨labelTraj ((areaFamily e).trajectory ω), h2⟩ : RegLL) ∈
        Subtype.val ⁻¹' B := hmem
    rw [hBeq] at hx
    apply hx
    have hreg := isRegenPath_labelTraj h1
    refine ⟨hreg.start, ?_⟩
    obtain ⟨r, hr, -, -⟩ := retTime_spec hreg
    show fwdReturn (labelTraj ((areaFamily e).trajectory ω)) ≠ ⊤
    unfold fwdReturn
    rw [hreg.start]
    show retTime z.val (labelTraj ((areaFamily e).trajectory ω)) ≠ ⊤
    rw [hr]
    exact WithTop.coe_ne_top
  exact measure_mono_null (fun ω hω => not_not.2 hω) (ae_iff.1 hae)

/-- **Clause (b) at the actual walk**: the first-cycle law is reversal invariant, at every
environment and every slot. -/
theorem completeCycleReversal_firstCycleLaw (G : Set Env)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (n : ℕ) (e : Env) :
    CompleteCycleReversal (firstCycleLaw G hwalk n e) := by
  by_cases hlive : e ∈ G ∧ (e.val.1 n).isSome
  · haveI := nontrivial_vertex e
    have hadm := hwalk e hlive.1
    have hW := isReflectedWalk_areaFamily e hadm
    let z : Vertex e.val := ⟨n, hlive.2⟩
    refine completeCycleReversal_of_grid (regSlotLaw G hwalk n e) measurable_subtype_coe
      (measurable_firstCycle n) ?_ ?_
    · filter_upwards [ae_good_regSlotLaw G hwalk n e hlive] with x hx
      obtain ⟨h0, hr⟩ := hx
      obtain ⟨-, a, ha0, har, hbef, haft, hxr⟩ := exists_hold_of_fwdReturn x.2.regular h0 hr
      exact ⟨a, retLen x.1, ⟨x.2, ha0, har, hbef, haft, hxr⟩,
        Subtype.ext (firstCycle_of_good h0 hr)⟩
    · intro N a k w hw
      have hpre : ∀ w' : Fin (k + 1) → Option ℕ,
          regSlotLaw G hwalk n e ((gridWord N k ∘ Subtype.val) ⁻¹' {w'}) =
            (areaFamily e).P z ((areaFamily e).trajectory ⁻¹'
              (labelTraj ⁻¹' (gridWord N k ⁻¹' {w'}))) := fun w' => by
        rw [Set.preimage_comp, ← Measure.map_apply measurable_subtype_coe
            ((measurable_gridWord N k) (measurableSet_singleton w')),
          regSlotLaw_map_val, slotLaw_apply_of_mem hlive.1 hlive.2
            ((measurable_gridWord N k) (measurableSet_singleton w'))]
      rw [hpre, hpre]
      exact label_grid_reversal hW (StatementIngredients.cellArea (decode e))
        (StatementIngredients.cellArea_pos (decode e) (decode_geometry e))
        (fun δ => AreaReversibility.processTransitionReversible_cellArea (decode e)
          (decode_geometry e) hW (decode_connected e) δ) z N a k w hw
  · -- off the live set the law is the point mass at the `cycRev`-fixed default cycle
    have hreg : regSlotLaw G hwalk n e = Measure.dirac ⟨cem, isRegLL_cem⟩ := by
      refine regSlotLaw_eq_of_map_val_eq G hwalk n e ?_
      rw [Measure.map_dirac' measurable_subtype_coe, slotLaw_of_not hlive]
      rfl
    have hfc : firstCycle n ⟨cem, isRegLL_cem⟩ = defaultCycle n := by
      apply Subtype.ext
      show firstCycleRaw n ⟨cem, isRegLL_cem⟩ = (defaultCycle n).1
      unfold firstCycleRaw
      rw [if_neg (fun hc => by simp [cem] at hc)]
    rw [firstCycleLaw, hreg, Measure.map_dirac' (measurable_firstCycle n), hfc]
    exact completeCycleReversal_dirac_twoStep (Nat.succ_ne_self n).symm

end ReflectedGMS.CycleReversalProof
