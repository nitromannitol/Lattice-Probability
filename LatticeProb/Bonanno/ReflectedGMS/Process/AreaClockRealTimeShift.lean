/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.AreaClockRealTimeShift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.AreaTransitionReversibility
import LatticeProb.Bonanno.ReflectedWalk.TransitionUniqueness

/-! # Real-time shift invariance of the area-weighted two-sided law of the area clock

The fixed-environment half of `p:lem:timeMTP` (tex:1348-1391) rests on one sentence:

> The sigma-finite path measure `𝕢_H = ∑_v a_v ℙ_H^v` is invariant under every
> deterministic time shift.  This follows directly from the Markov cylinder
> distributions and `a_v p_t(v,u) = a_u p_t(u,v)`; no finite total speed mass is
> required.

The detailed-balance input `a_v p_t(v,u) = a_u p_t(u,v)` for the **area** speed, at every
real time `t ≥ 0`, is already proved:
`AreaReversibility.processTransitionReversible_cellArea` (`Forms/AreaTransitionReversibility`,
no summability; the scope warning in `Temporal/AreaCylinderShiftIdentity` predates it).
What existed downstream of it is the **constant-step grid** form
(`AreaReversibility.twoSidedGridLaw_cellArea_twoSidedFinsetCylinder_shift_of_geometry`):
invariance under integer shifts of the grid `δℤ`, which contains the time origin.  A real
shift `r` that is incommensurable with the prescribed times never lies on such a grid, so
the grid statement does not give the real-time sentence.

This file proves the real-time sentence at the level of finite-dimensional
distributions, for arbitrary real times and an arbitrary real shift.

## Statement

`twoSidedReal PF ω t` reads the two-sided path of `ω = (ω₁, ω₂)` (the forward copy for
`t ≥ 0`, the backward copy at `-t` for `t < 0`), exactly as `TwoSided.twoSidedPath` does on
the grid.  `realCyl PF I g` prescribes the vertex `g i` at every time `i` of a finite set
`I ⊆ ℝ`.

* `twoSidedSpeedLaw_realCyl` — **the closed form**: with `m = min I`,
  `𝕢(realCyl I g) = w(g m) · ℙ^{g m}(X_{i - m} = g i ∀ i ∈ I)`.
  The mass of a two-sided cylinder is the weight of its *earliest* vertex times the
  forward fdd from that vertex at the relative times; the time origin has disappeared.
* `twoSidedSpeedLaw_realCyl_shift` — hence **invariance under every real shift `r`**.
* `twoSidedSpeedLaw_cellArea_realCyl_shift` — the area instance, unconditional.

## Proof

Only the Markov property (iv) of `IsReflectedWalk`, a.e. definedness (i), `X₀ = z`, and the
two-point detailed balance at every time are used:

* `measure_cyl_inter_shiftedPath` — (iv) with a finite past cylinder;
* `measure_shiftedPath_preimage` — summing over the state at a fixed time (the
  Chapman–Kolmogorov identity in path form); `tsum_transition_eq_one` is its `B = univ` case;
* `ofReal_mul_bwdCyl_eq` — **path reversal**: `w(g M) ℙ^{g M}(backward reading) =
  w(g m) ℙ^{g m}(forward reading)` for every finite time set, by induction on the minimum;
* the straddling step `∑_v w_v p_s(v,y) ℙ^v(forward) = w_y ℙ^y(forward after s)`.

No summability of the weight, no `IsFiniteMeasure`, no analytic semigroup.

## Scope

This is a statement about the two independent copies `twoSidedSpeedLaw PF w` on
`PF.Ω × PF.Ω`, read at finitely many real times.  It is **not** a statement about a law on
the càdlàg coding `TrajectoryCoding.CadlagPath`: no two-sided càdlàg coding of the actual
process is constructed anywhere in the tree (the regeneration lane's `TwoSidedCoding` is a
raw product of forward trajectories).  The bridge to the coding is
`Temporal/AreaClockCodingShift`, consumed by `Temporal/FixedEnvironmentTemporalTransport`.
Nothing here certifies `p:lem:timeMTP`,
`ScaledRootChainSystem.transport` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.AreaClockRealTimeShift

open ReflectedWalk ReflectedWalk.Theorem16 ReflectedGMS.TwoSided

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-! ## Time arithmetic -/

theorem toNNReal_sub_add_toNNReal_sub {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (b - a).toNNReal + (c - b).toNNReal = (c - a).toNNReal := by
  rw [← Real.toNNReal_add (sub_nonneg.2 hab) (sub_nonneg.2 hbc)]
  congr 1
  ring

theorem toNNReal_sub_add_toNNReal_sub' {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (c - b).toNNReal + (b - a).toNNReal = (c - a).toNNReal := by
  rw [add_comm]
  exact toNNReal_sub_add_toNNReal_sub hab hbc

theorem toNNReal_sub_tsub_toNNReal_sub_left {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (c - a).toNNReal - (b - a).toNNReal = (c - b).toNNReal := by
  rw [← toNNReal_sub_add_toNNReal_sub hab hbc, add_tsub_cancel_left]

theorem toNNReal_sub_tsub_toNNReal_sub_right {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (c - a).toNNReal - (c - b).toNNReal = (b - a).toNNReal := by
  rw [← toNNReal_sub_add_toNNReal_sub hab hbc, add_tsub_cancel_right]

/-! ## Finite cylinders of the forward process -/

/-- The finite cylinder `{X_{τ i} = g i for all i ∈ J}` of the forward process, for an
arbitrary index set and reading of times. -/
def cyl (PF : ProcessFamily V) {ι : Type*} (J : Finset ι) (τ : ι → ℝ≥0) (g : ι → V) :
    Set PF.Ω :=
  {ω | ∀ i ∈ J, PF.X (τ i) ω = some (g i)}

/-- The same cylinder on path space. -/
def trajCyl {ι : Type*} (J : Finset ι) (τ : ι → ℝ≥0) (g : ι → V) : Set (Trajectory V) :=
  {γ | ∀ i ∈ J, γ (τ i) = some (g i)}

theorem measurableSet_cyl (PF : ProcessFamily V) {ι : Type*} (J : Finset ι) (τ : ι → ℝ≥0)
    (g : ι → V) : MeasurableSet (cyl PF J τ g) := by
  have hset : cyl PF J τ g = ⋂ i ∈ (J : Set ι), {ω | PF.X (τ i) ω = some (g i)} := by
    ext ω
    simp [cyl]
  rw [hset]
  exact MeasurableSet.biInter J.countable_toSet fun i _ =>
    PF.measurable_X _ (measurableSet_singleton _)

theorem measurableSet_trajCyl {ι : Type*} (J : Finset ι) (τ : ι → ℝ≥0) (g : ι → V) :
    MeasurableSet (trajCyl J τ g) := by
  have hset : trajCyl J τ g = ⋂ i ∈ (J : Set ι), {γ : Trajectory V | γ (τ i) = some (g i)} := by
    ext γ
    simp [trajCyl]
  rw [hset]
  exact MeasurableSet.biInter J.countable_toSet fun i _ =>
    measurable_pi_apply (τ i) (measurableSet_singleton _)

theorem law_trajCyl (PF : ProcessFamily V) (z : V) {ι : Type*} (J : Finset ι) (τ : ι → ℝ≥0)
    (g : ι → V) : PF.law z (trajCyl J τ g) = PF.P z (cyl PF J τ g) := by
  rw [ProcessFamily.law, Measure.map_apply PF.measurable_trajectory (measurableSet_trajCyl J τ g)]
  rfl

theorem law_univ (PF : ProcessFamily V) (z : V) : PF.law z univ = 1 := by
  rw [ProcessFamily.law, Measure.map_apply PF.measurable_trajectory MeasurableSet.univ,
    preimage_univ, measure_univ]

section Markov

variable {G : ConductanceGraph V} {rate : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- **Property (iv) with a finite past cylinder.**  If the time `τ j` is the latest time of
the cylinder, the future after `τ j` is independent of the cylinder with law
`ℙ^{g j}`. -/
theorem measure_cyl_inter_shiftedPath (h : IsReflectedWalk G rate hmin PF) (x : V)
    {ι : Type*} (J : Finset ι) (τ : ι → ℝ≥0) (g : ι → V) {j : ι} (hj : j ∈ J)
    (hle : ∀ i ∈ J, τ i ≤ τ j) {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    PF.P x (cyl PF J τ g ∩ shiftedPath PF.X (τ j) ⁻¹' B) =
      PF.P x (cyl PF J τ g) * PF.law (g j) B := by
  classical
  let t : ℝ≥0 := τ j
  let E : Set PF.Ω := {ω | PF.X t ω = some (g j)}
  let S : Set (Set.Iic t → Option V) :=
    {f | ∀ i ∈ J, ∀ hi : τ i ≤ t, f ⟨τ i, hi⟩ = some (g i)}
  have hS : MeasurableSet S := by
    have hset : S = ⋂ i ∈ (J : Set ι), ⋂ hi : τ i ≤ t,
        {f : Set.Iic t → Option V | f ⟨τ i, hi⟩ = some (g i)} := by
      ext f
      simp [S]
    rw [hset]
    exact MeasurableSet.biInter J.countable_toSet fun i _ => MeasurableSet.iInter fun hi =>
      measurable_pi_apply (⟨τ i, hi⟩ : Set.Iic t) (measurableSet_singleton _)
  have hpast : Measurable (pastPath PF.X t) := measurable_pastPath PF.measurable_X t
  have hshift : Measurable (shiftedPath PF.X t) := measurable_shiftedPath PF.measurable_X t
  have hpair : Measurable fun ω => (pastPath PF.X t ω, shiftedPath PF.X t ω) :=
    hpast.prodMk hshift
  have hcyl : cyl PF J τ g = pastPath PF.X t ⁻¹' S ∩ E := by
    ext ω
    simp only [cyl, S, E, mem_setOf_eq, mem_inter_iff, mem_preimage, pastPath]
    exact ⟨fun hω => ⟨fun i hi _ => hω i hi, hω j hj⟩, fun hω i hi => hω.1 i hi (hle i hi)⟩
  have hM := congrArg
    (fun μ : Measure ((Set.Iic t → Option V) × Trajectory V) => μ (S ×ˢ B))
    ((h x).2.2.2.2.2.1 t (g j))
  rw [Measure.map_apply hpair (hS.prod hB), Measure.prod_prod,
    Measure.map_apply hpast hS, Measure.restrict_apply (hpair (hS.prod hB)),
    Measure.restrict_apply (hpast hS)] at hM
  have hpre : (fun ω => (pastPath PF.X t ω, shiftedPath PF.X t ω)) ⁻¹' (S ×ˢ B) ∩
      {ω | PF.X t ω = some (g j)} = cyl PF J τ g ∩ shiftedPath PF.X (τ j) ⁻¹' B := by
    rw [hcyl]
    ext ω
    simp only [E, mem_inter_iff, mem_preimage, mem_prod, mem_setOf_eq]
    tauto
  have hpre' : pastPath PF.X t ⁻¹' S ∩ {ω | PF.X t ω = some (g j)} = cyl PF J τ g :=
    hcyl.symm
  rw [hpre, hpre'] at hM
  exact hM

/-- **Splitting a finite cylinder at its earliest time** (property (iv) at that time). -/
theorem measure_cyl_split_min (h : IsReflectedWalk G rate hmin PF) (z : V)
    {ι : Type*} (J : Finset ι) (τ : ι → ℝ≥0) (g : ι → V) {j : ι} (hj : j ∈ J)
    (hmin : ∀ i ∈ J, τ j ≤ τ i) :
    PF.P z (cyl PF J τ g) =
      PF.transition z (τ j) (g j) * PF.P (g j) (cyl PF J (fun i => τ i - τ j) g) := by
  have hset : cyl PF J τ g = cyl PF {j} τ g ∩
      shiftedPath PF.X (τ j) ⁻¹' trajCyl J (fun i => τ i - τ j) g := by
    ext ω
    simp only [cyl, trajCyl, mem_inter_iff, mem_setOf_eq, mem_preimage, shiftedPath,
      Finset.mem_singleton, forall_eq]
    constructor
    · intro hω
      refine ⟨hω j hj, fun i hi => ?_⟩
      rw [tsub_add_cancel_of_le (hmin i hi)]
      exact hω i hi
    · rintro ⟨-, hω⟩ i hi
      have hi' := hω i hi
      rwa [tsub_add_cancel_of_le (hmin i hi)] at hi'
  rw [hset, measure_cyl_inter_shiftedPath h z {j} τ g (Finset.mem_singleton_self j)
      (fun i hi => by rw [Finset.mem_singleton.1 hi]) (measurableSet_trajCyl _ _ _),
    law_trajCyl]
  congr 1
  have hc : cyl PF {j} τ g = {ω | PF.X (τ j) ω = some (g j)} := by
    ext ω
    simp [cyl]
  rw [hc]
  rfl

/-- **Summing over the state at a fixed time** (Chapman–Kolmogorov in path form). -/
theorem measure_shiftedPath_preimage (h : IsReflectedWalk G rate hmin PF) (x : V) (s : ℝ≥0)
    {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    PF.P x (shiftedPath PF.X s ⁻¹' B) = ∑' z : V, PF.transition x s z * PF.law z B := by
  have hdisj : Pairwise (Function.onFun Disjoint
      fun z : V => {ω | PF.X s ω = some z} ∩ shiftedPath PF.X s ⁻¹' B) := by
    intro a b hab
    refine Set.disjoint_left.2 fun ω ha hb => hab ?_
    exact Option.some_injective _ (ha.1.symm.trans hb.1)
  have hmeas : ∀ z : V, MeasurableSet ({ω | PF.X s ω = some z} ∩ shiftedPath PF.X s ⁻¹' B) :=
    fun z => (PF.measurable_X s (measurableSet_singleton _)).inter
      (measurable_shiftedPath PF.measurable_X s hB)
  have hunion : PF.P x (shiftedPath PF.X s ⁻¹' B) =
      PF.P x (⋃ z, {ω | PF.X s ω = some z} ∩ shiftedPath PF.X s ⁻¹' B) := by
    refine le_antisymm ?_ (measure_mono (iUnion_subset fun z => inter_subset_right))
    calc PF.P x (shiftedPath PF.X s ⁻¹' B)
        ≤ PF.P x ((⋃ z, {ω | PF.X s ω = some z} ∩ shiftedPath PF.X s ⁻¹' B) ∪
            {ω | PF.X s ω = none}) := by
          refine measure_mono fun ω hω => ?_
          cases hX : PF.X s ω with
          | none => exact Or.inr hX
          | some z => exact Or.inl (mem_iUnion.2 ⟨z, hX, hω⟩)
      _ ≤ PF.P x (⋃ z, {ω | PF.X s ω = some z} ∩ shiftedPath PF.X s ⁻¹' B) +
            PF.P x {ω | PF.X s ω = none} := measure_union_le _ _
      _ = PF.P x (⋃ z, {ω | PF.X s ω = some z} ∩ shiftedPath PF.X s ⁻¹' B) := by
          rw [measure_none_eq_zero (h x).2.1 s, add_zero]
  rw [hunion, measure_iUnion hdisj hmeas]
  refine tsum_congr fun z => ?_
  have hz := measure_cyl_inter_shiftedPath h x ({()} : Finset Unit) (fun _ => s)
    (fun _ => z) (Finset.mem_singleton_self ()) (fun _ _ => le_rfl) hB
  have hc : cyl PF ({()} : Finset Unit) (fun _ => s) (fun _ => z) =
      {ω | PF.X s ω = some z} := by
    ext ω
    simp [cyl]
  rw [hc] at hz
  rw [hz]
  rfl

/-- The transition probabilities out of a vertex sum to one (property (i)). -/
theorem tsum_transition_eq_one (h : IsReflectedWalk G rate hmin PF) (x : V) (s : ℝ≥0) :
    ∑' z : V, PF.transition x s z = 1 := by
  have hs := measure_shiftedPath_preimage h x s MeasurableSet.univ
  simp only [preimage_univ, measure_univ, law_univ, mul_one] at hs
  exact hs.symm

end Markov

/-! ## Detailed balance in `ℝ≥0∞` form -/

/-- The two-point detailed balance of `TwoSided.ProcessTransitionReversible`, transported to
the `ℝ≥0∞` transition function of the family. -/
theorem ofReal_mul_transition_comm (PF : ProcessFamily V) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x)
    {t : ℝ≥0} (hrev : ProcessTransitionReversible PF w t) (x y : V) :
    ENNReal.ofReal (w x) * PF.transition x t y =
      ENNReal.ofReal (w y) * PF.transition y t x := by
  have h1 := congrArg ENNReal.ofReal (hrev x y)
  simp only [processTransition] at h1
  rw [ENNReal.ofReal_mul (hw x), ENNReal.ofReal_mul (hw y),
    ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)] at h1
  exact h1

/-! ## Forward and backward readings of a finite set of real times -/

/-- The forward reading from the anchor `c`: `X_{i - c} = g i` for `i ∈ J`. -/
def fwdCyl (PF : ProcessFamily V) (c : ℝ) (J : Finset ℝ) (g : ℝ → V) : Set PF.Ω :=
  cyl PF J (fun i => (i - c).toNNReal) g

/-- The backward reading from the anchor `c`: `X_{c - i} = g i` for `i ∈ J`. -/
def bwdCyl (PF : ProcessFamily V) (c : ℝ) (J : Finset ℝ) (g : ℝ → V) : Set PF.Ω :=
  cyl PF J (fun i => (c - i).toNNReal) g

theorem measurableSet_fwdCyl (PF : ProcessFamily V) (c : ℝ) (J : Finset ℝ) (g : ℝ → V) :
    MeasurableSet (fwdCyl PF c J g) :=
  measurableSet_cyl PF J _ g

theorem measurableSet_bwdCyl (PF : ProcessFamily V) (c : ℝ) (J : Finset ℝ) (g : ℝ → V) :
    MeasurableSet (bwdCyl PF c J g) :=
  measurableSet_cyl PF J _ g

section Readings

variable {G : ConductanceGraph V} {rate : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- Splitting a forward reading at its earliest time. -/
theorem measure_fwdCyl_split (h : IsReflectedWalk G rate hmin PF) (z : V) (c : ℝ)
    (J : Finset ℝ) (g : ℝ → V) {m : ℝ} (hm : m ∈ J) (hmle : ∀ i ∈ J, m ≤ i) (hcm : c ≤ m) :
    PF.P z (fwdCyl PF c J g) =
      PF.transition z (m - c).toNNReal (g m) * PF.P (g m) (fwdCyl PF m J g) := by
  rw [fwdCyl, measure_cyl_split_min h z J (fun i => (i - c).toNNReal) g hm
    (fun i hi => Real.toNNReal_le_toNNReal (by linarith [hmle i hi]))]
  congr 2
  ext ω
  simp only [cyl, fwdCyl, mem_setOf_eq]
  refine forall₂_congr fun i hi => ?_
  rw [toNNReal_sub_tsub_toNNReal_sub_left hcm (hmle i hi)]

/-- Splitting a backward reading at its latest prescribed time (its earliest reading). -/
theorem measure_bwdCyl_split (h : IsReflectedWalk G rate hmin PF) (z : V) (c : ℝ)
    (J : Finset ℝ) (g : ℝ → V) {M : ℝ} (hM : M ∈ J) (hMle : ∀ i ∈ J, i ≤ M) (hMc : M ≤ c) :
    PF.P z (bwdCyl PF c J g) =
      PF.transition z (c - M).toNNReal (g M) * PF.P (g M) (bwdCyl PF M J g) := by
  rw [bwdCyl, measure_cyl_split_min h z J (fun i => (c - i).toNNReal) g hM
    (fun i hi => Real.toNNReal_le_toNNReal (by linarith [hMle i hi]))]
  congr 2
  ext ω
  simp only [cyl, bwdCyl, mem_setOf_eq]
  refine forall₂_congr fun i hi => ?_
  rw [toNNReal_sub_tsub_toNNReal_sub_right (hMle i hi) hMc]

/-- **Path reversal.**  Under detailed balance at every time, the weighted backward reading
of a finite time set from its latest vertex equals the weighted forward reading from its
earliest vertex:
`w(g M) ℙ^{g M}(X_{M - i} = g i ∀ i) = w(g m) ℙ^{g m}(X_{i - m} = g i ∀ i)`. -/
theorem ofReal_mul_bwdCyl_eq (h : IsReflectedWalk G rate hmin PF) (w : V → ℝ)
    (hrev : ∀ (t : ℝ≥0) (x y : V),
      ENNReal.ofReal (w x) * PF.transition x t y = ENNReal.ofReal (w y) * PF.transition y t x)
    (g : ℝ → V) (J : Finset ℝ) :
    ∀ m M : ℝ, m ∈ J → (∀ i ∈ J, m ≤ i) → M ∈ J → (∀ i ∈ J, i ≤ M) →
      ENNReal.ofReal (w (g M)) * PF.P (g M) (bwdCyl PF M J g) =
        ENNReal.ofReal (w (g m)) * PF.P (g m) (fwdCyl PF m J g) := by
  classical
  induction J using Finset.induction_on_min with
  | empty =>
      intro m M hm
      simp at hm
  | insert a J ha ih =>
      intro m' M' hm' hm'le hM' hM'le
      have hma : m' = a := by
        rcases Finset.mem_insert.1 hm' with hh | hh
        · exact hh
        · exact absurd (hm'le a (Finset.mem_insert_self a J)) (not_le.2 (ha m' hh))
      rw [hma]
      rcases J.eq_empty_or_nonempty with hJ | hJ
      · subst hJ
        have hMa : M' = a := by simpa using hM'
        rw [hMa]
        congr 2
        ext ω
        simp [bwdCyl, fwdCyl, cyl]
      · have hM'J : M' ∈ J := by
          rcases Finset.mem_insert.1 hM' with hh | hh
          · exfalso
            obtain ⟨b, hb⟩ := hJ
            have hle := hM'le b (Finset.mem_insert_of_mem hb)
            rw [hh] at hle
            exact absurd (ha b hb) (not_lt.2 hle)
          · exact hh
        have hMJle : ∀ i ∈ J, i ≤ M' := fun i hi => hM'le i (Finset.mem_insert_of_mem hi)
        set m := J.min' hJ with hmdef
        have hmJ : m ∈ J := J.min'_mem hJ
        have hmle : ∀ i ∈ J, m ≤ i := fun i hi => J.min'_le i hi
        have hIH := ih m M' hmJ hmle hM'J hMJle
        have ham : a < m := ha m hmJ
        have hmM : m ≤ M' := hmle M' hM'J
        -- the backward side: the new vertex is read last
        have hL : PF.P (g M') (bwdCyl PF M' (insert a J) g) =
            PF.P (g M') (bwdCyl PF M' J g) *
              PF.transition (g m) (m - a).toNNReal (g a) := by
          have hset : bwdCyl PF M' (insert a J) g = bwdCyl PF M' J g ∩
              shiftedPath PF.X (M' - m).toNNReal ⁻¹'
                ((fun γ : Trajectory V => γ (m - a).toNNReal) ⁻¹' {some (g a)}) := by
            ext ω
            simp only [bwdCyl, cyl, Finset.mem_insert, forall_eq_or_imp, mem_inter_iff,
              mem_setOf_eq, mem_preimage, shiftedPath, mem_singleton_iff]
            rw [toNNReal_sub_add_toNNReal_sub ham.le hmM]
            tauto
          have key := measure_cyl_inter_shiftedPath h (g M') J
              (fun i => (M' - i).toNNReal) g hmJ
              (fun i hi => Real.toNNReal_le_toNNReal (by linarith [hmle i hi]))
              (B := (fun γ : Trajectory V => γ (m - a).toNNReal) ⁻¹' {some (g a)})
              (measurable_pi_apply _ (measurableSet_singleton _))
          beta_reduce at key
          rw [ProcessFamily.law_eval] at key
          rw [hset]
          exact key
        -- the forward side: split at the earliest time of `J`
        have hR : PF.P (g a) (fwdCyl PF a (insert a J) g) =
            PF.transition (g a) (m - a).toNNReal (g m) * PF.P (g m) (fwdCyl PF m J g) := by
          have h1 : PF.P (g a) (fwdCyl PF a (insert a J) g) =
              PF.P (g a) (fwdCyl PF a J g) := by
            have hset : fwdCyl PF a (insert a J) g =
                fwdCyl PF a J g ∩ {ω | PF.X 0 ω = some (g a)} := by
              ext ω
              simp only [fwdCyl, cyl, Finset.mem_insert, forall_eq_or_imp, mem_inter_iff,
                mem_setOf_eq, sub_self, Real.toNNReal_zero]
              tauto
            rw [hset, measure_inter_conull]
            rw [compl_setOf]
            exact ae_iff.1 (h (g a)).1
          rw [h1, measure_fwdCyl_split h (g a) a J g hmJ hmle ham.le]
        rw [hL, hR]
        calc ENNReal.ofReal (w (g M')) * (PF.P (g M') (bwdCyl PF M' J g) *
              PF.transition (g m) (m - a).toNNReal (g a))
            = (ENNReal.ofReal (w (g M')) * PF.P (g M') (bwdCyl PF M' J g)) *
                PF.transition (g m) (m - a).toNNReal (g a) := by ring
          _ = (ENNReal.ofReal (w (g m)) * PF.P (g m) (fwdCyl PF m J g)) *
                PF.transition (g m) (m - a).toNNReal (g a) := by rw [hIH]
          _ = (ENNReal.ofReal (w (g m)) * PF.transition (g m) (m - a).toNNReal (g a)) *
                PF.P (g m) (fwdCyl PF m J g) := by ring
          _ = (ENNReal.ofReal (w (g a)) * PF.transition (g a) (m - a).toNNReal (g m)) *
                PF.P (g m) (fwdCyl PF m J g) := by rw [hrev]
          _ = ENNReal.ofReal (w (g a)) * (PF.transition (g a) (m - a).toNNReal (g m) *
                PF.P (g m) (fwdCyl PF m J g)) := by ring

end Readings

/-! ## The two-sided law at real times -/

/-- The two-sided path at a real time: the forward copy for `t ≥ 0`, the backward copy at
`-t` for `t < 0` (the real-time form of `TwoSided.twoSidedPath`). -/
noncomputable def twoSidedReal (PF : ProcessFamily V) (ω : PF.Ω × PF.Ω) (t : ℝ) : Option V :=
  if 0 ≤ t then PF.X t.toNNReal ω.1 else PF.X (-t).toNNReal ω.2

theorem measurable_twoSidedReal (PF : ProcessFamily V) (t : ℝ) :
    Measurable fun ω : PF.Ω × PF.Ω => twoSidedReal PF ω t := by
  unfold twoSidedReal
  split_ifs
  · exact (PF.measurable_X _).comp measurable_fst
  · exact (PF.measurable_X _).comp measurable_snd

/-- The real-time two-sided cylinder prescribing `g i` at every `i ∈ I`. -/
def realCyl (PF : ProcessFamily V) (I : Finset ℝ) (g : ℝ → V) : Set (PF.Ω × PF.Ω) :=
  {ω | ∀ i ∈ I, twoSidedReal PF ω i = some (g i)}

theorem realCyl_eq_prod (PF : ProcessFamily V) (I : Finset ℝ) (g : ℝ → V) :
    realCyl PF I g = fwdCyl PF 0 (I.filter fun i => 0 ≤ i) g ×ˢ
      bwdCyl PF 0 (I.filter fun i => ¬ 0 ≤ i) g := by
  ext ω
  simp only [realCyl, fwdCyl, bwdCyl, cyl, mem_setOf_eq, mem_prod, Finset.mem_filter,
    sub_zero, zero_sub]
  constructor
  · intro hω
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi' := hω i hi.1
      simpa only [twoSidedReal, if_pos hi.2] using hi'
    · have hi' := hω i hi.1
      simpa only [twoSidedReal, if_neg hi.2] using hi'
  · rintro ⟨h1, h2⟩ i hi
    by_cases hi0 : 0 ≤ i
    · simpa only [twoSidedReal, if_pos hi0] using h1 i ⟨hi, hi0⟩
    · simpa only [twoSidedReal, if_neg hi0] using h2 i ⟨hi, hi0⟩

section TwoSidedLaw

variable {G : ConductanceGraph V} {rate : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- **The closed form of a real-time two-sided cylinder mass.**  With `m` the earliest
prescribed time, the area-weighted two-sided mass is the weight of the earliest vertex times
the forward fdd from it at the relative times.  Only detailed balance at every time, the
Markov property and a.e. definedness are used; the weight need not be summable. -/
theorem twoSidedSpeedLaw_realCyl (h : IsReflectedWalk G rate hmin PF) (w : V → ℝ)
    (hrev : ∀ (t : ℝ≥0) (x y : V),
      ENNReal.ofReal (w x) * PF.transition x t y = ENNReal.ofReal (w y) * PF.transition y t x)
    (I : Finset ℝ) (g : ℝ → V) {m : ℝ} (hm : m ∈ I) (hmle : ∀ i ∈ I, m ≤ i) :
    twoSidedSpeedLaw PF w (realCyl PF I g) =
      ENNReal.ofReal (w (g m)) * PF.P (g m) (fwdCyl PF m I g) := by
  classical
  rw [realCyl_eq_prod, twoSidedSpeedLaw_prod_apply PF w (measurableSet_fwdCyl PF 0 _ g)
    (measurableSet_bwdCyl PF 0 _ g)]
  set Ip := I.filter fun i => 0 ≤ i with hIpdef
  set In := I.filter fun i => ¬ 0 ≤ i with hIndef
  rcases In.eq_empty_or_nonempty with hIn | hIn
  · -- every prescribed time is nonnegative
    have hm0 : 0 ≤ m := by
      by_contra hneg
      have hmem : m ∈ In := Finset.mem_filter.2 ⟨hm, hneg⟩
      rw [hIn] at hmem
      simp at hmem
    have hIp : Ip = I := Finset.filter_true_of_mem fun i hi => le_trans hm0 (hmle i hi)
    have hB : ∀ z, PF.P z (bwdCyl PF 0 In g) = 1 := by
      intro z
      rw [hIn]
      simp [bwdCyl, cyl]
    calc ∑' z : V, ENNReal.ofReal (w z) *
          (PF.P z (fwdCyl PF 0 Ip g) * PF.P z (bwdCyl PF 0 In g))
        = ∑' z : V, (ENNReal.ofReal (w (g m)) * PF.P (g m) (fwdCyl PF m I g)) *
            PF.transition (g m) (m - 0).toNNReal z := by
          refine tsum_congr fun z => ?_
          rw [hB z, mul_one, hIp, measure_fwdCyl_split h z 0 I g hm hmle hm0, ← mul_assoc,
            hrev]
          ring
      _ = ENNReal.ofReal (w (g m)) * PF.P (g m) (fwdCyl PF m I g) := by
          rw [ENNReal.tsum_mul_left, tsum_transition_eq_one h, mul_one]
  · -- some prescribed time is negative: straddle the time origin at the latest negative one
    set M := In.max' hIn with hMdef
    have hMIn : M ∈ In := In.max'_mem hIn
    have hMle : ∀ i ∈ In, i ≤ M := fun i hi => In.le_max' i hi
    have hM0 : M < 0 := not_le.1 (Finset.mem_filter.1 hMIn).2
    have hmIn : m ∈ In := Finset.mem_filter.2
      ⟨hm, fun h0 => absurd (lt_of_lt_of_le hM0 h0)
        (not_lt.2 (hmle M (Finset.mem_filter.1 hMIn).1))⟩
    have hmleIn : ∀ i ∈ In, m ≤ i := fun i hi => hmle i (Finset.mem_filter.1 hi).1
    -- backward factor
    have hB : ∀ z, PF.P z (bwdCyl PF 0 In g) =
        PF.transition z (0 - M).toNNReal (g M) * PF.P (g M) (bwdCyl PF M In g) :=
      fun z => measure_bwdCyl_split h z 0 In g hMIn hMle hM0.le
    -- forward factor after summing over the state at the origin
    have hF : ∑' z : V, PF.transition (g M) (0 - M).toNNReal z * PF.P z (fwdCyl PF 0 Ip g) =
        PF.P (g M) (fwdCyl PF M Ip g) := by
      have hset : shiftedPath PF.X (0 - M).toNNReal ⁻¹'
          trajCyl Ip (fun i => (i - 0).toNNReal) g = fwdCyl PF M Ip g := by
        ext ω
        simp only [trajCyl, fwdCyl, cyl, mem_preimage, mem_setOf_eq, shiftedPath]
        refine forall₂_congr fun i hi => ?_
        rw [toNNReal_sub_add_toNNReal_sub' hM0.le (Finset.mem_filter.1 hi).2]
      rw [← hset, measure_shiftedPath_preimage h (g M) _ (measurableSet_trajCyl _ _ _)]
      refine tsum_congr fun z => ?_
      rw [law_trajCyl]
      rfl
    -- the final Markov split at `M`
    have hsplit : PF.P (g m) (fwdCyl PF m I g) =
        PF.P (g m) (fwdCyl PF m In g) * PF.P (g M) (fwdCyl PF M Ip g) := by
      have hset : fwdCyl PF m I g = fwdCyl PF m In g ∩
          shiftedPath PF.X (M - m).toNNReal ⁻¹' trajCyl Ip (fun i => (i - M).toNNReal) g := by
        ext ω
        simp only [fwdCyl, cyl, trajCyl, mem_inter_iff, mem_setOf_eq, mem_preimage,
          shiftedPath]
        constructor
        · intro hω
          refine ⟨fun i hi => hω i (Finset.mem_filter.1 hi).1, fun i hi => ?_⟩
          rw [toNNReal_sub_add_toNNReal_sub' (hmleIn M hMIn)
            (le_trans hM0.le (Finset.mem_filter.1 hi).2)]
          exact hω i (Finset.mem_filter.1 hi).1
        · rintro ⟨h1, h2⟩ i hi
          by_cases hi0 : 0 ≤ i
          · have hi' := h2 i (Finset.mem_filter.2 ⟨hi, hi0⟩)
            rwa [toNNReal_sub_add_toNNReal_sub' (hmleIn M hMIn) (le_trans hM0.le hi0)] at hi'
          · exact h1 i (Finset.mem_filter.2 ⟨hi, hi0⟩)
      have key := measure_cyl_inter_shiftedPath h (g m) In (fun i => (i - m).toNNReal) g hMIn
          (fun i hi => Real.toNNReal_le_toNNReal (by linarith [hMle i hi]))
          (measurableSet_trajCyl Ip (fun i => (i - M).toNNReal) g)
      beta_reduce at key
      rw [law_trajCyl] at key
      rw [hset]
      exact key
    have hrevIn := ofReal_mul_bwdCyl_eq h w hrev g In m M hmIn hmleIn hMIn hMle
    calc ∑' z : V, ENNReal.ofReal (w z) *
          (PF.P z (fwdCyl PF 0 Ip g) * PF.P z (bwdCyl PF 0 In g))
        = ∑' z : V, (ENNReal.ofReal (w (g M)) * PF.P (g M) (bwdCyl PF M In g)) *
            (PF.transition (g M) (0 - M).toNNReal z * PF.P z (fwdCyl PF 0 Ip g)) := by
          refine tsum_congr fun z => ?_
          rw [hB z]
          calc ENNReal.ofReal (w z) * (PF.P z (fwdCyl PF 0 Ip g) *
                (PF.transition z (0 - M).toNNReal (g M) * PF.P (g M) (bwdCyl PF M In g)))
              = (ENNReal.ofReal (w z) * PF.transition z (0 - M).toNNReal (g M)) *
                  (PF.P (g M) (bwdCyl PF M In g) * PF.P z (fwdCyl PF 0 Ip g)) := by ring
            _ = (ENNReal.ofReal (w (g M)) * PF.transition (g M) (0 - M).toNNReal z) *
                  (PF.P (g M) (bwdCyl PF M In g) * PF.P z (fwdCyl PF 0 Ip g)) := by
                rw [hrev]
            _ = _ := by ring
      _ = (ENNReal.ofReal (w (g M)) * PF.P (g M) (bwdCyl PF M In g)) *
            PF.P (g M) (fwdCyl PF M Ip g) := by rw [ENNReal.tsum_mul_left, hF]
      _ = ENNReal.ofReal (w (g m)) * PF.P (g m) (fwdCyl PF m I g) := by
          rw [hrevIn, hsplit, mul_assoc]

/-- The one-time marginal of the area-weighted two-sided law is the weight, at **every** real
time: `𝕢(X_t = x) = w x`.  (Sanity check of the closed form; it already fails to follow from
the grid statement when `t` is off the grid.) -/
theorem twoSidedSpeedLaw_realCyl_singleton (h : IsReflectedWalk G rate hmin PF) (w : V → ℝ)
    (hrev : ∀ (t : ℝ≥0) (x y : V),
      ENNReal.ofReal (w x) * PF.transition x t y = ENNReal.ofReal (w y) * PF.transition y t x)
    (t : ℝ) (x : V) :
    twoSidedSpeedLaw PF w (realCyl PF {t} fun _ => x) = ENNReal.ofReal (w x) := by
  rw [twoSidedSpeedLaw_realCyl h w hrev {t} (fun _ => x) (Finset.mem_singleton_self t)
    (fun i hi => le_of_eq (Finset.mem_singleton.1 hi).symm)]
  beta_reduce
  have hset : fwdCyl PF t {t} (fun _ => x) = {ω | PF.X 0 ω = some x} := by
    ext ω
    simp [fwdCyl, cyl]
  rw [hset]
  have hone : PF.P x {ω | PF.X 0 ω = some x} = 1 := by
    have hmeas : MeasurableSet {ω : PF.Ω | PF.X 0 ω = some x} :=
      PF.measurable_X 0 (measurableSet_singleton _)
    have hcompl : PF.P x {ω : PF.Ω | PF.X 0 ω = some x}ᶜ = 0 := by
      rw [compl_setOf]
      exact ae_iff.1 (h x).1
    exact (prob_compl_eq_zero_iff hmeas).1 hcompl
  rw [hone, mul_one]

/-- **Invariance of the weighted two-sided law under every real time shift**, on
finite-dimensional cylinders at arbitrary real times. -/
theorem twoSidedSpeedLaw_realCyl_shift (h : IsReflectedWalk G rate hmin PF) (w : V → ℝ)
    (hrev : ∀ (t : ℝ≥0) (x y : V),
      ENNReal.ofReal (w x) * PF.transition x t y = ENNReal.ofReal (w y) * PF.transition y t x)
    (I : Finset ℝ) (g : ℝ → V) (r : ℝ) :
    twoSidedSpeedLaw PF w {ω | ∀ i ∈ I, twoSidedReal PF ω (i + r) = some (g i)} =
      twoSidedSpeedLaw PF w (realCyl PF I g) := by
  classical
  rcases I.eq_empty_or_nonempty with hI | hI
  · subst hI
    simp [realCyl]
  set m := I.min' hI with hmdef
  have hm : m ∈ I := I.min'_mem hI
  have hmle : ∀ i ∈ I, m ≤ i := fun i hi => I.min'_le i hi
  have hset : {ω | ∀ i ∈ I, twoSidedReal PF ω (i + r) = some (g i)} =
      realCyl PF (I.image fun i => i + r) fun s => g (s - r) := by
    ext ω
    simp only [realCyl, mem_setOf_eq, Finset.forall_mem_image, add_sub_cancel_right]
  rw [hset, twoSidedSpeedLaw_realCyl h w hrev (I.image fun i => i + r) (fun s => g (s - r))
      (m := m + r) (Finset.mem_image_of_mem (fun i => i + r) hm)
      (by
        intro s hs
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hs
        linarith [hmle i hi]),
    twoSidedSpeedLaw_realCyl h w hrev I g hm hmle]
  simp only [add_sub_cancel_right]
  congr 2
  ext ω
  simp only [fwdCyl, cyl, mem_setOf_eq, Finset.forall_mem_image, add_sub_cancel_right,
    add_sub_add_right_eq_sub]

end TwoSidedLaw

/-! ## The area clock -/

end ReflectedGMS.AreaClockRealTimeShift
