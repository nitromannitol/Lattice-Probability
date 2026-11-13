/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullEnergyPathNoNonvertexJumps at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyPotentialPathLimit
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryPairIncrement
import LatticeProb.Bonanno.ReflectedGMS.Forms.SojournOccupationLowerBound

/-!
# The full-energy potential paths do not jump at nonvertex times

**Theorem (★).**  For every vector `U` of the full Hilbert energy domain and every start `z`,
almost surely under `P_z` the càdlàg path `t ↦ fullEnergyPotentialPathLimit … U t ω` has
`leftLim = value` at every positive time `t` with `X_t = none`.

This is the nonvertex half of manuscript `p:prop:purejump`, in the per-`U` form consumed by the
càdlàg spatial extension (`Process/SpatialExtensionCadlag`).  The proof is an **energy budget
with matching constants**:

* **Upper bound** (`StationaryPairIncrement`): under the speed mixture `P_m`, the expected
  dyadic partition square sums of the raw path are at most `2 T 𝓔(u)`, hence so is the
  expectation of their `liminf` (Fatou).
* **Pathwise Fatou** (`CadlagJumpPartitionFatou`): for the càdlàg potential path, the sum of the
  squared jumps over the sojourn exits ending in `(0, T]`, plus the squared jump at any one
  nonvertex time, is at most that `liminf`.
* **Lower bound** (`SojournOccupationLowerBound`): the expected sum of the squared sojourn-exit
  jumps, mixed over `P_m`, is at least `2 T 𝓔(u)`.

So the `liminf` and the edge-jump sum have the same finite `P_m`-expectation while the latter
is pathwise dominated; they agree `P_z`-a.s. for every `z`, leaving no room for a nonvertex
jump.  Nothing here assumes any spatial-extension, boundary-jump or bracket predicate; the only
process inputs are `IsReflectedWalk` and connectivity.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ReflectedGMS.FullEnergyPathNoNonvertexJumps

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open CadlagJumpPartitionFatou StationaryPairIncrement SojournOccupationLowerBound
open SojournSquaredJumpIdentity TargetReturnRecursion TargetReturnClockCompatibility
open TargetReturnPairProcessLaw

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-! ## An `ℝ≥0∞` bookkeeping lemma -/

/-- Termwise `a ≤ b` with `∑ b ≤ ∑ a < ∞` forces termwise equality. -/
theorem tsum_eq_of_le_of_tsum_le {ι : Type*} (a b : ι → ℝ≥0∞) (hab : ∀ i, a i ≤ b i)
    (hle : ∑' i, b i ≤ ∑' i, a i) (hfin : ∑' i, a i ≠ ∞) : ∀ i, a i = b i := by
  have hsplit : ∑' i, b i = ∑' i, a i + ∑' i, (b i - a i) := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun i => (add_tsub_cancel_of_le (hab i)).symm
  rw [hsplit] at hle
  have hzero : ∑' i, (b i - a i) = 0 :=
    nonpos_iff_eq_zero.1 (ENNReal.le_of_add_le_add_left hfin (by rw [add_zero]; exact hle))
  intro i
  exact le_antisymm (hab i) (tsub_eq_zero_iff_le.1 (ENNReal.tsum_eq_zero.1 hzero i))

/-! ## The raw `liminf` -/

/-- The `liminf` of the dyadic partition square sums of the raw path. -/
noncomputable def rawLiminf (PF : ProcessFamily V) (u : V → ℝ) (T : ℝ≥0) (ω : PF.Ω) : ℝ≥0∞ :=
  liminf (fun n => ENNReal.ofReal (partitionSquareSum (rawPath PF u ω) T n)) atTop

theorem measurable_rawLiminf (PF : ProcessFamily V) (u : V → ℝ) (T : ℝ≥0) :
    Measurable (rawLiminf PF u T) :=
  Measurable.liminf fun n =>
    ENNReal.measurable_ofReal.comp (measurable_partitionSquareSum_rawPath PF u T n)

section Main

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF) (hG : G.toSimpleGraph.Connected)
  (hm : ∀ v, 0 < m v) (hmsum : Summable m) (default : V) (U : hilbertDomain G m)

include h hG hm hmsum

/-- The partition square sums of the potential path and of the raw path agree: the two paths
differ by the constant `u z` at the countably many partition points. -/
theorem ae_partitionSquareSum_eq (z : V) (T : ℝ≥0) :
    ∀ᵐ ω ∂PF.P z, ∀ n : ℕ,
      partitionSquareSum (fun t => fullEnergyPotentialPathLimit G m hm PF default U t ω) T n =
        partitionSquareSum (rawPath PF (unweight m (valueInclusion G m U)) ω) T n := by
  have hpt : ∀ᵐ ω ∂PF.P z, ∀ n i : ℕ,
      fullEnergyPotentialPathLimit G m hm PF default U (dyadicPoint T n i) ω =
        rawPath PF (unweight m (valueInclusion G m U)) ω (dyadicPoint T n i) -
          unweight m (valueInclusion G m U) z := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro i
    exact fullEnergyPotentialPathLimit_ae_eq h hG hm hmsum default U z (dyadicPoint T n i)
  filter_upwards [hpt] with ω hω n
  unfold partitionSquareSum
  refine Finset.sum_congr rfl fun i _ => ?_
  show (fullEnergyPotentialPathLimit G m hm PF default U (dyadicPoint T n (i + 1)) ω -
        fullEnergyPotentialPathLimit G m hm PF default U (dyadicPoint T n i) ω) ^ 2 =
      (rawPath PF (unweight m (valueInclusion G m U)) ω (dyadicPoint T n (i + 1)) -
        rawPath PF (unweight m (valueInclusion G m U)) ω (dyadicPoint T n i)) ^ 2
  rw [hω n (i + 1), hω n i]
  ring

/-- **The sojourn-exit jumps of the potential path.**  Almost surely, every nonzero term of the
edge-jump sum is the squared jump of the potential path at the (finite, positive, `≤ T`) sojourn
end, which is a vertex time; and distinct nonzero terms have distinct sojourn ends. -/
theorem ae_sojourn_jump_data (z : V) (T : ℝ≥0) :
    ∀ᵐ ω ∂PF.P z,
      (∀ x n, sojournJumpTerm PF z x (unweight m (valueInclusion G m U)) T n ω ≠ 0 →
        sojournEnd PF z x n ω ≠ ⊤ ∧
        (ENNReal.toNNReal (sojournEnd PF z x n ω)) ∈ Ioc 0 T ∧
        (∃ v, PF.X (ENNReal.toNNReal (sojournEnd PF z x n ω)) ω = some v) ∧
        sojournJumpTerm PF z x (unweight m (valueInclusion G m U)) T n ω =
          jumpSq (fun s => fullEnergyPotentialPathLimit G m hm PF default U s ω)
            (ENNReal.toNNReal (sojournEnd PF z x n ω))) ∧
      (∀ x n x' n', sojournJumpTerm PF z x (unweight m (valueInclusion G m U)) T n ω ≠ 0 →
        sojournJumpTerm PF z x' (unweight m (valueInclusion G m U)) T n' ω ≠ 0 →
        sojournEnd PF z x n ω = sojournEnd PF z x' n' ω → x = x' ∧ n = n') := by
  have hw : ∀ v, 0 < G.pi v / m v := fun v => div_pos (G.pi_pos_of_connected hG v) (hm v)
  have hgood : ∀ᵐ ω ∂PF.P z, ∀ x : V,
      (∀ n : ℕ, targetReturnTime PF.X (sojournTarget z x) n ω ≠ ⊤ ∧
        stoppedValue PF.X (targetReturnTime PF.X (sojournTarget z x) n) ω ∈
          some '' ((sojournTarget z x : Finset V) : Set V)) ∧
      (∀ n : ℕ, 0 < exitAfter PF.X (targetReturnTime PF.X (sojournTarget z x) n) ω -
        targetReturnTime PF.X (sojournTarget z x) n ω) := by
    rw [ae_all_iff]
    intro x
    filter_upwards [ae_forall_targetReturnTime_finite_mem h hG (sojournTarget_nonempty z x)
      (mem_sojournTarget_right z x),
      ae_forall_targetHolding_pos h hG hw (sojournTarget_nonempty z x)
        (mem_sojournTarget_right z x)] with ω h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hgood, fullEnergyPotentialPathLimit_ae_eq_at_vertex_times h hG hm hmsum default U z,
    fullEnergyPotentialPathLimit_ae_cadlag_and_uniform h hG hm hmsum default U z]
    with ω hω hvert hcad
  -- unpacking a nonzero term
  have key : ∀ x n, sojournJumpTerm PF z x (unweight m (valueInclusion G m U)) T n ω ≠ 0 →
      ω ∈ stopEvent PF.X (sojournStart PF z x n) x ∧ sojournEnd PF z x n ω ≤ (T : ℝ≥0∞) ∧
      ∃ v, stoppedValue PF.X (sojournEnd PF z x n) ω = some v ∧
        sojournJumpTerm PF z x (unweight m (valueInclusion G m U)) T n ω =
          ENNReal.ofReal ((unweight m (valueInclusion G m U) v -
            unweight m (valueInclusion G m U) x) ^ 2) := by
    intro x n hne
    by_cases hstop : ω ∈ stopEvent PF.X (sojournStart PF z x n) x
    · have hval : sojournJumpTerm PF z x (unweight m (valueInclusion G m U)) T n ω =
          stateJumpSq (unweight m (valueInclusion G m U)) x
            (stoppedValue PF.X (sojournEnd PF z x n) ω) *
            (Iic (T : ℝ≥0∞)).indicator 1 (sojournEnd PF z x n ω : ℝ≥0∞) := by
        unfold sojournJumpTerm
        rw [indicator_of_mem hstop]
      rw [hval] at hne
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
      have hρT : sojournEnd PF z x n ω ≤ (T : ℝ≥0∞) := by
        by_contra hcon
        exact h2 (indicator_of_notMem (fun hh => hcon (mem_Iic.1 hh)) _)
      refine ⟨hstop, hρT, ?_⟩
      cases hX : stoppedValue PF.X (sojournEnd PF z x n) ω with
      | none =>
          rw [hX] at h1
          exact absurd rfl h1
      | some v =>
          refine ⟨v, rfl, ?_⟩
          have hI : (Iic (T : ℝ≥0∞)).indicator (1 : ℝ≥0∞ → ℝ≥0∞)
              (sojournEnd PF z x n ω : ℝ≥0∞) = 1 :=
            indicator_of_mem (mem_Iic.2 hρT) _
          rw [hval, hX, hI, mul_one]
          rfl
    · exfalso
      apply hne
      unfold sojournJumpTerm
      exact indicator_of_notMem hstop _
  -- the time structure of a genuine sojourn
  have hstruct : ∀ x n, ω ∈ stopEvent PF.X (sojournStart PF z x n) x →
      sojournEnd PF z x n ω = exitAfter PF.X (sojournStart PF z x n) ω ∧
      sojournStart PF z x n ω < sojournEnd PF z x n ω ∧
      ∀ s : ℝ≥0, sojournStart PF z x n ω ≤ (s : ℝ≥0∞) → (s : ℝ≥0∞) < sojournEnd PF z x n ω →
        PF.X s ω = some x := by
    intro x n hstop
    obtain ⟨hfin, hpos⟩ := hω x
    have hfin' : ∀ j, targetReturnTime PF.X (sojournTarget z x) j ω ≠ ⊤ := fun j => (hfin j).1
    have hend : sojournEnd PF z x n ω = exitAfter PF.X (sojournStart PF z x n) ω := by
      rw [exitAfter, hstop.2]
      rfl
    refine ⟨hend, ?_, ?_⟩
    · rw [hend]
      exact tsub_pos_iff_lt.1 (hpos n)
    · intro s hs1 hs2
      have hexit_ne : exitAfter PF.X (targetReturnTime PF.X (sojournTarget z x) n) ω ≠ ⊤ :=
        targetExit_ne_top (hfin' (n + 1))
      have h1 : targetReturnAt PF.X (sojournTarget z x) n ω ≤ s := by
        rw [← WithTop.coe_le_coe, coe_targetReturnAt (hfin' n)]
        exact hs1
      have h2 : s < targetExitAt PF.X (sojournTarget z x) n ω := by
        rw [← WithTop.coe_lt_coe, coe_targetExitAt hexit_ne]
        exact lt_of_lt_of_eq hs2 hend
      rw [eq_stoppedValue_of_mem_target_hold hfin' h1 h2]
      exact hstop.2
  have hmono : ∀ x j k, j ≤ k → sojournStart PF z x j ω ≤ sojournStart PF z x k ω := by
    intro x j k hjk
    have hfin' : ∀ j, targetReturnTime PF.X (sojournTarget z x) j ω ≠ ⊤ :=
      fun j => ((hω x).1 j).1
    show targetReturnTime PF.X (sojournTarget z x) j ω ≤ targetReturnTime PF.X (sojournTarget z x) k ω
    rw [← coe_targetReturnAt (hfin' j), ← coe_targetReturnAt (hfin' k)]
    exact WithTop.coe_le_coe.2 (targetReturnAt_mono hfin' hjk)
  refine ⟨?_, ?_⟩
  · intro x n hne
    obtain ⟨hstop, hρT, v, hv, hterm⟩ := key x n hne
    obtain ⟨hend, hlt, hconst⟩ := hstruct x n hstop
    have hρtop : sojournEnd PF z x n ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hρT
    have hρcoe : ((ENNReal.toNNReal (sojournEnd PF z x n ω)) : ℝ≥0∞) = sojournEnd PF z x n ω :=
      ENNReal.coe_toNNReal hρtop
    have hτtop : sojournStart PF z x n ω ≠ ⊤ := ne_top_of_lt hlt
    have hτcoe : ((ENNReal.toNNReal (sojournStart PF z x n ω)) : ℝ≥0∞) = sojournStart PF z x n ω :=
      ENNReal.coe_toNNReal hτtop
    have hτρ : (ENNReal.toNNReal (sojournStart PF z x n ω)) < (ENNReal.toNNReal (sojournEnd PF z x n ω)) := by
      rw [← ENNReal.coe_lt_coe, hτcoe, hρcoe]
      exact hlt
    have hXρ : PF.X (ENNReal.toNNReal (sojournEnd PF z x n ω)) ω = some v := by
      rw [← hv]
      exact (stoppedValue_of_eq hρcoe.symm).symm
    have hZρ : fullEnergyPotentialPathLimit G m hm PF default U (ENNReal.toNNReal (sojournEnd PF z x n ω)) ω =
        unweight m (valueInclusion G m U) v - unweight m (valueInclusion G m U) z :=
      hvert _ v hXρ
    have hZleft : ∀ s ∈ Ico (ENNReal.toNNReal (sojournStart PF z x n ω)) (ENNReal.toNNReal (sojournEnd PF z x n ω)),
        fullEnergyPotentialPathLimit G m hm PF default U s ω =
          unweight m (valueInclusion G m U) x - unweight m (valueInclusion G m U) z := by
      intro s hs
      refine hvert s x (hconst s ?_ ?_)
      · rw [← hτcoe]
        exact ENNReal.coe_le_coe.2 hs.1
      · rw [← hρcoe]
        exact ENNReal.coe_lt_coe.2 hs.2
    have hρpos : 0 < (ENNReal.toNNReal (sojournEnd PF z x n ω)) := lt_of_le_of_lt zero_le hτρ
    haveI : (𝓝[<] (ENNReal.toNNReal (sojournEnd PF z x n ω))).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, hρpos⟩
    have hleft : Function.leftLim (fun s => fullEnergyPotentialPathLimit G m hm PF default U s ω)
        (ENNReal.toNNReal (sojournEnd PF z x n ω)) =
        unweight m (valueInclusion G m U) x - unweight m (valueInclusion G m U) z := by
      apply leftLim_eq_of_tendsto
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ico_mem_nhdsLT hτρ] with s hs
      exact (hZleft s hs).symm
    refine ⟨hρtop, ⟨hρpos, ?_⟩, ⟨v, hXρ⟩, ?_⟩
    · rw [← ENNReal.coe_le_coe, hρcoe]
      exact hρT
    · rw [hterm]
      unfold jumpSq
      -- `unfold` leaves a beta-redex at the evaluation point, which `rw` cannot see through
      show ENNReal.ofReal ((unweight m (valueInclusion G m U) v -
            unweight m (valueInclusion G m U) x) ^ 2) =
          ENNReal.ofReal
            ((fullEnergyPotentialPathLimit G m hm PF default U
                (ENNReal.toNNReal (sojournEnd PF z x n ω)) ω -
              Function.leftLim (fun s => fullEnergyPotentialPathLimit G m hm PF default U s ω)
                (ENNReal.toNNReal (sojournEnd PF z x n ω))) ^ 2)
      rw [hZρ, hleft]
      congr 1
      ring
  · intro x n x' n' hne hne' heq
    obtain ⟨hstop, hρT, -⟩ := key x n hne
    obtain ⟨hstop', -, -⟩ := key x' n' hne'
    obtain ⟨hend, hlt, hconst⟩ := hstruct x n hstop
    obtain ⟨hend', hlt', hconst'⟩ := hstruct x' n' hstop'
    have hρtop : sojournEnd PF z x n ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hρT
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hρtop
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    obtain ⟨a', ha'⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt')
    have har : a < r := by
      rw [← WithTop.coe_lt_coe, ha, hr]
      exact hlt
    have har' : a' < r := by
      rw [← WithTop.coe_lt_coe, ha', hr, heq]
      exact hlt'
    have hxx : x = x' := by
      have h1 := hconst (max a a') (by rw [← ha]; exact WithTop.coe_le_coe.2 (le_max_left _ _))
        (by rw [← hr]; exact WithTop.coe_lt_coe.2 (max_lt har har'))
      have h2 := hconst' (max a a') (by rw [← ha']; exact WithTop.coe_le_coe.2 (le_max_right _ _))
        (by rw [← heq, ← hr]; exact WithTop.coe_lt_coe.2 (max_lt har har'))
      exact Option.some.inj (h1.symm.trans h2)
    subst hxx
    refine ⟨rfl, ?_⟩
    by_contra hnn
    rcases lt_or_gt_of_ne hnn with hlt_n | hlt_n
    · have h1 : sojournEnd PF z x n ω ≤ sojournStart PF z x (n + 1) ω := by
        rw [hend]
        exact exitAfter_targetReturnTime_le_succ PF.X _ n ω
      have h2 : sojournStart PF z x (n + 1) ω ≤ sojournStart PF z x n' ω :=
        hmono x (n + 1) n' hlt_n
      exact absurd heq (ne_of_lt (lt_of_le_of_lt (h1.trans h2) hlt'))
    · have h1 : sojournEnd PF z x n' ω ≤ sojournStart PF z x (n' + 1) ω := by
        rw [hend']
        exact exitAfter_targetReturnTime_le_succ PF.X _ n' ω
      have h2 : sojournStart PF z x (n' + 1) ω ≤ sojournStart PF z x n ω :=
        hmono x (n' + 1) n hlt_n
      exact absurd heq.symm (ne_of_lt (lt_of_le_of_lt (h1.trans h2) hlt))

/-- **Pathwise Fatou, instantiated.**  Almost surely the edge-jump sum is at most the raw
`liminf`, and so is the edge-jump sum plus the squared jump at any one nonvertex time in
`(0, T]`. -/
theorem ae_edgeJumpSum_le_rawLiminf (z : V) (T : ℝ≥0) :
    ∀ᵐ ω ∂PF.P z,
      edgeJumpSum PF z (unweight m (valueInclusion G m U)) T ω ≤
        rawLiminf PF (unweight m (valueInclusion G m U)) T ω ∧
      ∀ t : ℝ≥0, t ∈ Ioc 0 T → PF.X t ω = none →
        jumpSq (fun s => fullEnergyPotentialPathLimit G m hm PF default U s ω) t +
          edgeJumpSum PF z (unweight m (valueInclusion G m U)) T ω ≤
        rawLiminf PF (unweight m (valueInclusion G m U)) T ω := by
  classical
  filter_upwards [ae_sojourn_jump_data h hG hm hmsum default U z T,
    ae_partitionSquareSum_eq h hG hm hmsum default U z T,
    fullEnergyPotentialPathLimit_ae_cadlag_and_uniform h hG hm hmsum default U z]
    with ω hdata hpss hcad
  obtain ⟨hdata, hinj⟩ := hdata
  have hlim : liminf (fun n => ENNReal.ofReal (partitionSquareSum
      (fun t => fullEnergyPotentialPathLimit G m hm PF default U t ω) T n)) atTop =
      rawLiminf PF (unweight m (valueInclusion G m U)) T ω := by
    unfold rawLiminf
    congr 1
    funext n
    rw [hpss n]
  let a : V × ℕ → ℝ≥0∞ := fun p =>
    sojournJumpTerm PF z p.1 (unweight m (valueInclusion G m U)) T p.2 ω
  let s : V × ℕ → ℝ≥0 := fun p => (ENNReal.toNNReal (sojournEnd PF z p.1 p.2 ω))
  have hle : ∀ p, a p ≠ 0 → a p ≤
      jumpSq (fun t => fullEnergyPotentialPathLimit G m hm PF default U t ω) (s p) :=
    fun p hp => (hdata p.1 p.2 hp).2.2.2.le
  have hmem : ∀ p, a p ≠ 0 → s p ∈ Ioc 0 T := fun p hp => (hdata p.1 p.2 hp).2.1
  have hinjS : Set.InjOn s {p | a p ≠ 0} := by
    intro p hp q hq hpq
    have hρtop : sojournEnd PF z p.1 p.2 ω ≠ ⊤ := (hdata p.1 p.2 hp).1
    have hρtop' : sojournEnd PF z q.1 q.2 ω ≠ ⊤ := (hdata q.1 q.2 hq).1
    have heq : sojournEnd PF z p.1 p.2 ω = sojournEnd PF z q.1 q.2 ω := by
      rw [← ENNReal.coe_toNNReal hρtop, ← ENNReal.coe_toNNReal hρtop']
      exact congrArg _ hpq
    obtain ⟨h1, h2⟩ := hinj p.1 p.2 q.1 q.2 hp hq heq
    exact Prod.ext h1 h2
  refine ⟨?_, ?_⟩
  · rw [← hlim]
    exact tsum_le_liminf_of_jumpSq hcad.1 T s a hle hinjS hmem
  · intro t ht hnone
    rw [← hlim, edgeJumpSum, ENNReal.tsum_eq_iSup_sum, ENNReal.add_iSup]
    refine iSup_le fun F => ?_
    rw [← Finset.sum_filter_ne_zero]
    let F' : Finset (Option (V × ℕ)) :=
      insert none ((F.filter fun p => a p ≠ 0).map Function.Embedding.some)
    let s' : Option (V × ℕ) → ℝ≥0 := fun o => o.elim t s
    have hnone_notin : none ∉ (F.filter fun p => a p ≠ 0).map Function.Embedding.some := by
      simp [Finset.mem_map]
    have hsupp : ∀ p ∈ F.filter (fun p => a p ≠ 0), a p ≠ 0 :=
      fun p hp => (Finset.mem_filter.1 hp).2
    calc jumpSq (fun u => fullEnergyPotentialPathLimit G m hm PF default U u ω) t +
          ∑ p ∈ F.filter (fun p => a p ≠ 0), a p ≤
        jumpSq (fun u => fullEnergyPotentialPathLimit G m hm PF default U u ω) t +
          ∑ p ∈ F.filter (fun p => a p ≠ 0),
            jumpSq (fun u => fullEnergyPotentialPathLimit G m hm PF default U u ω) (s p) :=
          add_le_add le_rfl (Finset.sum_le_sum fun p hp => hle p (hsupp p hp))
      _ = ∑ o ∈ F', jumpSq (fun u => fullEnergyPotentialPathLimit G m hm PF default U u ω) (s' o) := by
          rw [Finset.sum_insert hnone_notin, Finset.sum_map]
          rfl
      _ ≤ _ := by
          refine sum_jumpSq_le_liminf hcad.1 T F' s' ?_ ?_
          · intro o ho o' ho' hoo'
            rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_map] at ho ho'
            rcases ho with rfl | ⟨p, hp, rfl⟩ <;> rcases ho' with rfl | ⟨q, hq, rfl⟩
            · rfl
            · exfalso
              obtain ⟨v, hv⟩ := (hdata q.1 q.2 (hsupp q hq)).2.2.1
              have : PF.X t ω = some v := by
                have hts : t = s q := hoo'
                rw [hts]
                exact hv
              rw [hnone] at this
              exact Option.some_ne_none v this.symm
            · exfalso
              obtain ⟨v, hv⟩ := (hdata p.1 p.2 (hsupp p hp)).2.2.1
              have : PF.X t ω = some v := by
                have hts : t = s p := hoo'.symm
                rw [hts]
                exact hv
              rw [hnone] at this
              exact Option.some_ne_none v this.symm
            · have hpq : p = q := hinjS (hsupp p hp) (hsupp q hq) hoo'
              rw [hpq]
          · intro o ho
            rw [Finset.mem_insert, Finset.mem_map] at ho
            rcases ho with rfl | ⟨p, hp, rfl⟩
            · exact ht
            · exact hmem p (hsupp p hp)

/-- **The energy budget closes.**  For every start `z`, the raw `liminf` and the edge-jump sum
agree almost surely, and the raw `liminf` has finite expectation.

The base point `base` enters only through the (`ω`-independent) recentring of the potential
path and does not occur in the conclusion; it is an explicit argument because the section
variable `default` is not in scope in a statement that does not mention it — and, being named
`default`, it would silently resolve to `Inhabited.default` instead. -/
theorem ae_rawLiminf_eq_edgeJumpSum (base : V) (z : V) (T : ℝ≥0) :
    (rawLiminf PF (unweight m (valueInclusion G m U)) T =ᵐ[PF.P z]
      edgeJumpSum PF z (unweight m (valueInclusion G m U)) T) ∧
    (∫⁻ ω, rawLiminf PF (unweight m (valueInclusion G m U)) T ω ∂PF.P z) ≠ ∞ := by
  have hu : G.HasFiniteEnergy (unweight m (valueInclusion G m U)) :=
    hilbertDomain_hasFiniteEnergy G m U
  have hEL : ∀ z, edgeJumpSum PF z (unweight m (valueInclusion G m U)) T ≤ᵐ[PF.P z]
      rawLiminf PF (unweight m (valueInclusion G m U)) T := fun z =>
    (ae_edgeJumpSum_le_rawLiminf h hG hm hmsum base U z T).mono fun ω hω => hω.1
  have hab : ∀ z, ENNReal.ofReal (m z) *
      (∫⁻ ω, edgeJumpSum PF z (unweight m (valueInclusion G m U)) T ω ∂PF.P z) ≤
      ENNReal.ofReal (m z) *
        ∫⁻ ω, rawLiminf PF (unweight m (valueInclusion G m U)) T ω ∂PF.P z :=
    fun z => mul_le_mul' le_rfl (lintegral_mono_ae (hEL z))
  have hb : (∑' z, ENNReal.ofReal (m z) *
      ∫⁻ ω, rawLiminf PF (unweight m (valueInclusion G m U)) T ω ∂PF.P z) ≤
      ENNReal.ofReal ((T : ℝ) * (2 * G.Energy (unweight m (valueInclusion G m U)))) := by
    rw [← lintegral_reflectedSpeedLaw_eq_tsum PF m]
    exact lintegral_liminf_partitionSquareSum_rawPath_le h hG hm hmsum U T
  have ha : ENNReal.ofReal ((T : ℝ) * (2 * G.Energy (unweight m (valueInclusion G m U)))) ≤
      ∑' z, ENNReal.ofReal (m z) *
        ∫⁻ ω, edgeJumpSum PF z (unweight m (valueInclusion G m U)) T ω ∂PF.P z :=
    ofReal_energy_le_tsum_lintegral_edgeJumpSum h hG hm hmsum hu T
  have hfin : (∑' z, ENNReal.ofReal (m z) *
      ∫⁻ ω, edgeJumpSum PF z (unweight m (valueInclusion G m U)) T ω ∂PF.P z) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((ENNReal.tsum_le_tsum hab).trans hb)
  have heq := tsum_eq_of_le_of_tsum_le _ _ hab (hb.trans ha) hfin z
  have hm0 : ENNReal.ofReal (m z) ≠ 0 := (ENNReal.ofReal_pos.2 (hm z)).ne'
  have hmtop : ENNReal.ofReal (m z) ≠ ∞ := ENNReal.ofReal_ne_top
  have hEfin : (∫⁻ ω, edgeJumpSum PF z (unweight m (valueInclusion G m U)) T ω ∂PF.P z) ≠ ∞ := by
    intro htop
    have hz : ENNReal.ofReal (m z) *
        (∫⁻ ω, edgeJumpSum PF z (unweight m (valueInclusion G m U)) T ω ∂PF.P z) = ∞ := by
      rw [htop]
      exact ENNReal.mul_top hm0
    exact (ne_top_of_le_ne_top hfin (ENNReal.le_tsum z)) hz
  have hLE : (∫⁻ ω, rawLiminf PF (unweight m (valueInclusion G m U)) T ω ∂PF.P z) ≤
      ∫⁻ ω, edgeJumpSum PF z (unweight m (valueInclusion G m U)) T ω ∂PF.P z :=
    le_of_eq ((ENNReal.mul_right_inj hm0 hmtop).1 heq).symm
  refine ⟨?_, ne_top_of_le_ne_top hEfin hLE⟩
  exact (ae_eq_of_ae_le_of_lintegral_le (hEL z) hEfin
    (measurable_rawLiminf PF _ T).aemeasurable hLE).symm

/-- **(★) on a finite horizon.** -/
theorem ae_leftLim_eq_of_none_of_le (z : V) (T : ℝ≥0) :
    ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0, 0 < t → t ≤ T → PF.X t ω = none →
      Function.leftLim (fun s => fullEnergyPotentialPathLimit G m hm PF default U s ω) t =
        fullEnergyPotentialPathLimit G m hm PF default U t ω := by
  obtain ⟨heq, hfin⟩ := ae_rawLiminf_eq_edgeJumpSum h hG hm hmsum U default z T
  filter_upwards [ae_edgeJumpSum_le_rawLiminf h hG hm hmsum default U z T, heq,
    ae_lt_top (measurable_rawLiminf PF _ T) hfin] with ω h1 h2 h3
  intro t ht htT hnone
  have hsum := h1.2 t ⟨ht, htT⟩ hnone
  rw [h2] at hsum h3
  have hEtop : edgeJumpSum PF z (unweight m (valueInclusion G m U)) T ω ≠ ∞ := h3.ne
  have hj : jumpSq (fun s => fullEnergyPotentialPathLimit G m hm PF default U s ω) t = 0 :=
    nonpos_iff_eq_zero.1 (ENNReal.le_of_add_le_add_right hEtop (by rwa [zero_add]))
  unfold jumpSq at hj
  rw [ENNReal.ofReal_eq_zero] at hj
  have hsq : (fullEnergyPotentialPathLimit G m hm PF default U t ω -
      Function.leftLim (fun s => fullEnergyPotentialPathLimit G m hm PF default U s ω) t) ^ 2 = 0 :=
    le_antisymm hj (sq_nonneg _)
  rw [sq_eq_zero_iff] at hsq
  exact (sub_eq_zero.1 hsq).symm

/-- **Theorem (★): the full-energy potential path does not jump at nonvertex times.**  For
every vector `U` of the full Hilbert energy domain and every start `z`, almost surely the càdlàg
path `t ↦ fullEnergyPotentialPathLimit … U t ω` has `leftLim = value` at every positive time
at which the walk is at the collapsed end state. -/
theorem ae_leftLim_eq_of_none (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0, 0 < t → PF.X t ω = none →
      Function.leftLim (fun s => fullEnergyPotentialPathLimit G m hm PF default U s ω) t =
        fullEnergyPotentialPathLimit G m hm PF default U t ω := by
  have hall := ae_all_iff.2 fun T : ℕ =>
    ae_leftLim_eq_of_none_of_le h hG hm hmsum default U z (T : ℝ≥0)
  filter_upwards [hall] with ω hω t ht hnone
  exact hω ⌈t⌉₊ t ht (Nat.le_ceil t) hnone

end Main

end ReflectedGMS.FullEnergyPathNoNonvertexJumps
