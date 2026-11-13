/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.UncoveredRootTransport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Laws
import LatticeProb.Bonanno.ReflectedGMS.Environment.RootDensities
import LatticeProb.Bonanno.ReflectedGMS.Environment.CellArea
import LatticeProb.Bonanno.ReflectedGMS.Spatial.CellSlotMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The root is covered: the covering half of the manuscript's Lemma 2.4

The manuscript's Lemma 2.4 ("The root is covered") states that under spatial mass transport the
origin lies in a unique cell interior almost surely.  Its second half — the origin lies on no cell
frontier — is `ReflectedGMS.Spatial.ae_notMem_boundaryMask_of_massTransport`.  This file proves the
**first** half: almost surely the origin lies in *some* cell.

The argument is the manuscript's own.  The intrinsic uncovered set
`U(𝓗) = ℂ \ ⋃_{H ∈ 𝓗} H` is similarity covariant, and it is Lebesgue-null by hypothesis.  Apply
mass transport to

  `T(𝓗, w, z) = 1_{w ∈ U(𝓗)} · |w - z|⁻²`,

which has scaling degree `-2`.  The incoming integral at the origin is zero, because the uncovered
set is Lebesgue-null, so the outgoing integral from the origin vanishes almost surely; but the
outgoing integral is `1_{0 ∈ U(𝓗)} · ∫ |z|⁻² dz`, and `∫ |z|⁻² dz ≠ 0`.  Hence `0 ∉ U(𝓗)` almost
surely.  (The manuscript records the stronger fact that the outgoing integral is *infinite* when the
root is uncovered; only nonvanishing is used here.)

## Independence from the covering clause of `Geometry`

The whole point of this file is that it is available *after* the covering clause of
`ReflectedGMS.Geometry` is weakened from `⋃ v, cell v = univ` to nullity of the uncovered set.  No
declaration below uses any clause of `Geometry`, and none uses `decode_geometry`: the transport's
joint measurability comes from the code slots alone, and its `(s ^ 2)⁻¹` covariance comes from the
physical similarity relation `EnvironmentLaws.IsSimilarity` alone.  In particular the nullity of the
uncovered set enters only as the explicit hypothesis `huncov`, never from the environment's own
geometry.

The measurability inputs are reused verbatim from `ReflectedGMS.Spatial.NullBoundaryRoots`
(`isClosed_cellMem` / `measurableSet_cellMem`, `measurableSet_slotIsSome`, `measurable_slotCell`,
`referenceCell`); none of their statements mentions `Geometry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.Spatial

open Code EnvironmentLaws

/-! ### The covered set of an environment -/

/-- The set of plane points lying in at least one cell of the environment.  Its complement is the
manuscript's intrinsic uncovered set `U(𝓗)`; it is determined by the environment, and no chosen
geometric witness is involved. -/
def envCoveredSet (e : Env) : Set Plane :=
  ⋃ v : Vertex e.val, ((decode e).cell v : Set Plane)

/-- The slot-level covering condition: the code slot is present and its cell contains the point. -/
def slotCoveredSupport : Set (Option CompactCell × Plane) :=
  {q | q.1.isSome ∧ q.2 ∈ ((q.1.getD referenceCell : CompactCell) : Set Plane)}

theorem mem_slotCoveredSupport_iff (o : Option CompactCell) (w : Plane) :
    (o, w) ∈ slotCoveredSupport ↔
      o.isSome ∧ w ∈ ((o.getD referenceCell : CompactCell) : Set Plane) :=
  Iff.rfl

theorem measurableSet_slotCoveredSupport : MeasurableSet slotCoveredSupport := by
  have hcellmap : Measurable fun q : Option CompactCell × Plane =>
      (q.1.getD referenceCell : CompactCell) := measurable_slotCell.comp measurable_fst
  have hS0 : MeasurableSet {q : Option CompactCell × Plane | q.1.isSome} :=
    measurable_fst measurableSet_slotIsSome
  have hS1 : MeasurableSet {q : Option CompactCell × Plane |
      q.2 ∈ ((q.1.getD referenceCell : CompactCell) : Set Plane)} :=
    (hcellmap.prodMk measurable_snd) measurableSet_cellMem
  have hEq : slotCoveredSupport
      = {q : Option CompactCell × Plane | q.1.isSome} ∩
        {q : Option CompactCell × Plane |
          q.2 ∈ ((q.1.getD referenceCell : CompactCell) : Set Plane)} :=
    Set.ext fun _ => Iff.rfl
  rw [hEq]
  exact hS0.inter hS1

/-- Covering is a countable slot condition: this is what makes it jointly measurable. -/
theorem mem_envCoveredSet_iff (e : Env) (w : Plane) :
    w ∈ envCoveredSet e ↔ ∃ n : ℕ, (e.val.1 n, w) ∈ slotCoveredSupport := by
  constructor
  · intro hw
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hw
    refine ⟨v.val, ?_⟩
    rw [mem_slotCoveredSupport_iff]
    refine ⟨v.property, ?_⟩
    have hslot : e.val.1 v.val = some ((decode e).cell v) := (Option.some_get v.property).symm
    rw [hslot]
    simp only [Option.getD_some]
    exact hv
  · rintro ⟨n, hn⟩
    rw [mem_slotCoveredSupport_iff] at hn
    obtain ⟨hsome, hw⟩ := hn
    have hslot : e.val.1 n = some ((decode e).cell ⟨n, hsome⟩) := (Option.some_get hsome).symm
    rw [hslot] at hw
    simp only [Option.getD_some] at hw
    exact Set.mem_iUnion.mpr ⟨⟨n, hsome⟩, hw⟩

theorem measurableSet_envCoveredProd :
    MeasurableSet {p : Env × Plane | p.2 ∈ envCoveredSet p.1} := by
  have hEq : {p : Env × Plane | p.2 ∈ envCoveredSet p.1}
      = ⋃ n : ℕ, (fun p : Env × Plane => (p.1.val.1 n, p.2)) ⁻¹' slotCoveredSupport := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    exact mem_envCoveredSet_iff p.1 p.2
  rw [hEq]
  refine MeasurableSet.iUnion fun n => ?_
  have hmap : Measurable fun p : Env × Plane => (p.1.val.1 n, p.2) :=
    (((measurable_pi_apply n).comp
      (measurable_fst.comp measurable_inclusion)).comp measurable_fst).prodMk measurable_snd
  exact hmap measurableSet_slotCoveredSupport

/-- The uncovered set transforms as it must: a positive similarity carries the covered set of an
environment onto the covered set of any similar environment. -/
theorem envCoveredSet_of_isSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (hsim : IsSimilarity s u hs e e') :
    envCoveredSet e' = positiveSimilarity s u '' envCoveredSet e := by
  obtain ⟨relabel, hcell, -⟩ := hsim
  calc envCoveredSet e'
      = ⋃ v : Vertex e.val, ((decode e').cell (relabel v) : Set Plane) :=
        (relabel.surjective.iUnion_comp
          (fun v' : Vertex e'.val => ((decode e').cell v' : Set Plane))).symm
    _ = ⋃ v : Vertex e.val, positiveSimilarity s u '' ((decode e).cell v : Set Plane) := by
        refine Set.iUnion_congr fun v => ?_
        rw [hcell v, coe_transformCell]
    _ = positiveSimilarity s u '' envCoveredSet e := (Set.image_iUnion).symm

/-! ### The manuscript's uncovered transport -/

/-- The source points the manuscript's uncovered transport sends mass from: those covered by no
cell. -/
def uncoveredSourceSet : Set (Env × Plane × Plane) :=
  {p | p.2.1 ∉ envCoveredSet p.1}

theorem measurableSet_uncoveredSourceSet : MeasurableSet uncoveredSourceSet := by
  have hmap : Measurable fun p : Env × Plane × Plane => (p.1, p.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hEq : uncoveredSourceSet
      = ((fun p : Env × Plane × Plane => (p.1, p.2.1)) ⁻¹'
          {p : Env × Plane | p.2 ∈ envCoveredSet p.1})ᶜ :=
    Set.ext fun _ => Iff.rfl
  rw [hEq]
  exact (hmap measurableSet_envCoveredProd).compl

/-- The manuscript's transport `T(𝓗, w, z) = 1_{w ∈ U(𝓗)} |w - z|⁻²`, with the inverse square
written multiplicatively in `ℝ≥0∞`.  On the diagonal the factor is `∞` rather than the manuscript's
`0`; the diagonal is Lebesgue-null, so neither the outgoing nor the incoming integral is affected,
and the pointwise covariance below holds with either convention. -/
noncomputable def uncoveredRootTransport (p : Env × Plane × Plane) : ℝ≥0∞ :=
  Set.indicator uncoveredSourceSet
    (fun q : Env × Plane × Plane => (edist q.2.1 q.2.2)⁻¹ * (edist q.2.1 q.2.2)⁻¹) p

theorem uncoveredRootTransport_of_mem (e : Env) (w z : Plane) (hw : w ∈ envCoveredSet e) :
    uncoveredRootTransport (e, w, z) = 0 := by
  unfold uncoveredRootTransport
  exact Set.indicator_of_notMem
    (show (e, w, z) ∉ uncoveredSourceSet from fun h => h hw) _

theorem uncoveredRootTransport_of_notMem (e : Env) (w z : Plane) (hw : w ∉ envCoveredSet e) :
    uncoveredRootTransport (e, w, z) = (edist w z)⁻¹ * (edist w z)⁻¹ := by
  unfold uncoveredRootTransport
  exact Set.indicator_of_mem (show (e, w, z) ∈ uncoveredSourceSet from hw) _

theorem measurable_uncoveredRootTransport : Measurable uncoveredRootTransport := by
  have hpair : Measurable fun q : Env × Plane × Plane => (q.2.1, q.2.2) :=
    (measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)
  have hed : Measurable fun q : Env × Plane × Plane => edist q.2.1 q.2.2 :=
    measurable_edist.comp hpair
  exact (hed.inv.mul hed.inv).indicator measurableSet_uncoveredSourceSet

/-- A positive similarity scales distances exactly by `s`. -/
theorem edist_positiveSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) (w z : Plane) :
    edist (positiveSimilarity s u w) (positiveSimilarity s u z)
      = ENNReal.ofReal s * edist w z := by
  rw [edist_dist, edist_dist, ← ENNReal.ofReal_mul hs.le]
  congr 1
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : positiveSimilarity s u w - positiveSimilarity s u z = s • (w - z) := by
    show s • (w - u) - s • (z - u) = s • (w - z)
    rw [← smul_sub]
    congr 1
    abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hs]

/-- The inverse square distance has scaling degree `-2`. -/
theorem invEdist_mul_invEdist_positiveSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) (w z : Plane) :
    (edist (positiveSimilarity s u w) (positiveSimilarity s u z))⁻¹ *
        (edist (positiveSimilarity s u w) (positiveSimilarity s u z))⁻¹
      = ENNReal.ofReal ((s ^ 2)⁻¹) * ((edist w z)⁻¹ * (edist w z)⁻¹) := by
  have ha0 : ENNReal.ofReal s ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hs
  have hatop : ENNReal.ofReal s ≠ ∞ := ENNReal.ofReal_ne_top
  have hinv : (ENNReal.ofReal s * edist w z)⁻¹
      = (ENNReal.ofReal s)⁻¹ * (edist w z)⁻¹ :=
    ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)
  have hofReal : ENNReal.ofReal ((s ^ 2)⁻¹)
      = (ENNReal.ofReal s)⁻¹ * (ENNReal.ofReal s)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), sq, ENNReal.ofReal_mul hs.le,
      ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
  rw [edist_positiveSimilarity s u hs, hinv, hofReal]
  ring

/-- Exact `(s ^ 2)⁻¹` covariance of the uncovered transport under the physical similarity relation
of the environment law: the covered-set indicator is invariant and the inverse square distance
carries the whole scaling. -/
theorem uncoveredRootTransport_covariant (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (hsim : IsSimilarity s u hs e e') (w z : Plane) :
    uncoveredRootTransport (e', positiveSimilarity s u w, positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * uncoveredRootTransport (e, w, z) := by
  have hcov := envCoveredSet_of_isSimilarity s u hs e e' hsim
  have hhom : ⇑(positiveSimilarityHomeomorph s u hs) = positiveSimilarity s u := rfl
  have hinj : Function.Injective (positiveSimilarity s u) := by
    rw [← hhom]
    exact (positiveSimilarityHomeomorph s u hs).injective
  by_cases hw : w ∈ envCoveredSet e
  · have hw' : positiveSimilarity s u w ∈ envCoveredSet e' := by
      rw [hcov]
      exact Set.mem_image_of_mem _ hw
    rw [uncoveredRootTransport_of_mem e' _ _ hw', uncoveredRootTransport_of_mem e w z hw,
      mul_zero]
  · have hw' : positiveSimilarity s u w ∉ envCoveredSet e' := by
      rw [hcov]
      intro hmem
      exact hw (hinj.mem_set_image.mp hmem)
    rw [uncoveredRootTransport_of_notMem e' _ _ hw', uncoveredRootTransport_of_notMem e w z hw]
    exact invEdist_mul_invEdist_positiveSimilarity s u hs w z

/-- The uncovered transport as an actual `MassTransportKernel`: jointly measurable on the full trace
sigma algebra and exactly `(s ^ 2)⁻¹`-covariant.  No clause of `Geometry` is used. -/
noncomputable def uncoveredRootTransportKernel : MassTransportKernel where
  toFun := uncoveredRootTransport
  measurable_toFun := measurable_uncoveredRootTransport
  covariant := fun s u hs e e' hsim w z =>
    uncoveredRootTransport_covariant s u hs e e' hsim w z

/-! ### Outgoing and incoming integrals -/

/-- The outgoing mass of the manuscript's kernel from an uncovered root does not vanish.  The
manuscript asserts that it is infinite; the unit ball already gives the nonvanishing used here. -/
theorem lintegral_invEdist_ne_zero :
    (∫⁻ z : Plane, (edist (0 : Plane) z)⁻¹ * (edist (0 : Plane) z)⁻¹ ∂volume) ≠ 0 := by
  have hle : ∀ z : Plane,
      Set.indicator (Metric.ball (0 : Plane) 1) (fun _ => (1 : ℝ≥0∞)) z
        ≤ (edist (0 : Plane) z)⁻¹ * (edist (0 : Plane) z)⁻¹ := by
    intro z
    by_cases hz : z ∈ Metric.ball (0 : Plane) 1
    · rw [Set.indicator_of_mem hz]
      have hdist : dist (0 : Plane) z < 1 := by
        rw [dist_comm]
        exact Metric.mem_ball.mp hz
      have hd : edist (0 : Plane) z ≤ 1 := by
        rw [edist_dist]
        calc ENNReal.ofReal (dist (0 : Plane) z) ≤ ENNReal.ofReal 1 :=
              ENNReal.ofReal_le_ofReal hdist.le
          _ = 1 := ENNReal.ofReal_one
      have h1 : (1 : ℝ≥0∞) ≤ (edist (0 : Plane) z)⁻¹ := ENNReal.one_le_inv.mpr hd
      calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
        _ ≤ (edist (0 : Plane) z)⁻¹ * (edist (0 : Plane) z)⁻¹ := mul_le_mul' h1 h1
    · rw [Set.indicator_of_notMem hz]
      exact zero_le
  intro hzero
  have hball : (0 : ℝ≥0∞) < volume (Metric.ball (0 : Plane) 1) :=
    Metric.measure_ball_pos volume 0 one_pos
  have hbound : volume (Metric.ball (0 : Plane) 1) ≤ 0 := by
    calc volume (Metric.ball (0 : Plane) 1)
        = ∫⁻ z : Plane, Set.indicator (Metric.ball (0 : Plane) 1)
            (fun _ => (1 : ℝ≥0∞)) z ∂volume := by
          rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet, one_mul]
      _ ≤ ∫⁻ z : Plane, (edist (0 : Plane) z)⁻¹ * (edist (0 : Plane) z)⁻¹ ∂volume :=
          lintegral_mono hle
      _ = 0 := hzero
  exact absurd (le_antisymm hbound zero_le) hball.ne'

/-- The incoming integral at the origin vanishes as soon as the uncovered set is Lebesgue-null:
mass can only be sent from uncovered sources. -/
theorem lintegral_uncoveredRootTransport_incoming (e : Env)
    (he : volume ((envCoveredSet e)ᶜ) = 0) :
    (∫⁻ w : Plane, uncoveredRootTransport (e, w, 0) ∂volume) = 0 := by
  have hae : ∀ᵐ w : Plane ∂volume, uncoveredRootTransport (e, w, 0) = 0 := by
    refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ he)
    intro w hw
    rw [Set.mem_compl_iff]
    intro hmem
    exact hw (uncoveredRootTransport_of_mem e w 0 hmem)
  calc (∫⁻ w : Plane, uncoveredRootTransport (e, w, 0) ∂volume)
      = ∫⁻ _ : Plane, (0 : ℝ≥0∞) ∂volume := lintegral_congr_ae hae
    _ = 0 := lintegral_zero

/-- The outgoing integral from an uncovered origin is the full inverse square integral. -/
theorem lintegral_uncoveredRootTransport_outgoing (e : Env)
    (h0 : (0 : Plane) ∉ envCoveredSet e) :
    (∫⁻ z : Plane, uncoveredRootTransport (e, 0, z) ∂volume)
      = ∫⁻ z : Plane, (edist (0 : Plane) z)⁻¹ * (edist (0 : Plane) z)⁻¹ ∂volume :=
  lintegral_congr fun z => uncoveredRootTransport_of_notMem e 0 z h0

/-! ### The root is covered -/

/-- **The covering half of the manuscript's Lemma 2.4.**  Under spatial mass transport, if the
uncovered set of almost every environment is Lebesgue-null, then almost surely the origin lies in
some cell.

No clause of `ReflectedGMS.Geometry` is used: the nullity of the uncovered set enters only through
the explicit hypothesis `huncov`, which is what the covering clause supplies after it is weakened
from `⋃ v, cell v = univ` to nullity of the uncovered set. -/
theorem ae_zero_mem_iUnion_cell (ν : Measure Env)
    (hmt : MassTransport ν)
    (huncov : ∀ᵐ e : Env ∂ν, volume ((⋃ v, ((decode e).cell v : Set Plane))ᶜ) = 0) :
    ∀ᵐ e : Env ∂ν, (0 : Plane) ∈ ⋃ v, ((decode e).cell v : Set Plane) := by
  have hkey : (∫⁻ e : Env, ∫⁻ z : Plane, uncoveredRootTransport (e, 0, z) ∂volume ∂ν)
      = ∫⁻ e : Env, ∫⁻ z : Plane, uncoveredRootTransport (e, z, 0) ∂volume ∂ν :=
    hmt uncoveredRootTransportKernel
  have hincoming :
      (∫⁻ e : Env, ∫⁻ z : Plane, uncoveredRootTransport (e, z, 0) ∂volume ∂ν) = 0 := by
    have hae : ∀ᵐ e : Env ∂ν,
        (∫⁻ z : Plane, uncoveredRootTransport (e, z, 0) ∂volume) = 0 := by
      filter_upwards [huncov] with e he
      exact lintegral_uncoveredRootTransport_incoming e he
    calc (∫⁻ e : Env, ∫⁻ z : Plane, uncoveredRootTransport (e, z, 0) ∂volume ∂ν)
        = ∫⁻ _ : Env, (0 : ℝ≥0∞) ∂ν := lintegral_congr_ae hae
      _ = 0 := lintegral_zero
  have hzero : (∫⁻ e : Env, ∫⁻ z : Plane, uncoveredRootTransport (e, 0, z) ∂volume ∂ν) = 0 := by
    rw [hkey]
    exact hincoming
  have hmeasout : Measurable fun e : Env =>
      ∫⁻ z : Plane, uncoveredRootTransport (e, 0, z) ∂volume :=
    uncoveredRootTransportKernel.measurable_outgoing.lintegral_prod_right'
  have haeout := (lintegral_eq_zero_iff hmeasout).mp hzero
  filter_upwards [haeout] with e he
  by_contra h0
  have h0' : (0 : Plane) ∉ envCoveredSet e := h0
  have he0 : (∫⁻ z : Plane, uncoveredRootTransport (e, 0, z) ∂volume) = 0 := he
  rw [lintegral_uncoveredRootTransport_outgoing e h0'] at he0
  exact lintegral_invEdist_ne_zero he0

#print axioms ReflectedGMS.Spatial.ae_zero_mem_iUnion_cell

end ReflectedGMS.Spatial
