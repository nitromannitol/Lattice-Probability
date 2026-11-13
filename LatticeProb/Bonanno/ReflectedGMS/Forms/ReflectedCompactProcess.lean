/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ReflectedCompactProcess at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedCompactPaths
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedIdentification
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCompactSpace
import LatticeProb.Bonanno.ReflectedGMS.Forms.GlobalDyadicDensity
import LatticeProb.Bonanno.ReflectedGMS.Forms.DenseRightLimitExtension
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Sequences

/-! A single separately measurable compact-space process, defined from the
original path by supported sequential right limits independently of its start law.
Path regularity and association are established in the subsequent theorems. -/

-- Merged from `ReflectedGMS/Forms/MeasurableCadlagExtension.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_MeasurableCadlagExtension

/-!
# A measurable càdlàg extension from supported one-sided limits

Mathlib supplies both sequences approaching points in a closure and strong
measurability of sequential limits. Combining these with the supported-limit
adapter avoids a new stochastic regularization construction.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped NNReal

namespace ReflectedGMS

private theorem exists_supportedRightSequence
    (S : Set ℝ≥0) (hS : ∀ t, (𝓝[S ∩ Ioi t] t).NeBot) (t : ℝ≥0) :
    ∃ u : ℕ → ℝ≥0, (∀ n, u n ∈ S ∩ Ioi t) ∧ Tendsto u atTop (𝓝 t) :=
  mem_closure_iff_seq_limit.mp (mem_closure_iff_nhdsWithin_neBot.mpr (hS t))

/-- A deterministic sequence approaching each time from the supported right. -/
noncomputable def supportedRightSequence
    (S : Set ℝ≥0) (hS : ∀ t, (𝓝[S ∩ Ioi t] t).NeBot) (t : ℝ≥0) : ℕ → ℝ≥0 :=
  Classical.choose (exists_supportedRightSequence S hS t)

theorem supportedRightSequence_mem
    (S : Set ℝ≥0) (hS : ∀ t, (𝓝[S ∩ Ioi t] t).NeBot) (t : ℝ≥0) (n : ℕ) :
    supportedRightSequence S hS t n ∈ S ∩ Ioi t :=
  (Classical.choose_spec (exists_supportedRightSequence S hS t)).1 n

theorem tendsto_supportedRightSequence
    (S : Set ℝ≥0) (hS : ∀ t, (𝓝[S ∩ Ioi t] t).NeBot) (t : ℝ≥0) :
    Tendsto (supportedRightSequence S hS t) atTop (𝓝[S ∩ Ioi t] t) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (Classical.choose_spec (exists_supportedRightSequence S hS t)).2
    (Filter.Eventually.of_forall (supportedRightSequence_mem S hS t))

variable {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
  [T3Space E] [IsCompletelyMetrizableSpace E] [Nonempty E]

/-- The sequential right-limit extension is independent of any probability law. -/
noncomputable def supportedRightExtension
    (S : Set ℝ≥0) (hS : ∀ t, (𝓝[S ∩ Ioi t] t).NeBot)
    (f : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : E :=
  limUnder atTop (fun n => f (supportedRightSequence S hS t n) ω)

theorem stronglyMeasurable_supportedRightExtension
    (S : Set ℝ≥0) (hS : ∀ t, (𝓝[S ∩ Ioi t] t).NeBot)
    (f : ℝ≥0 → Ω → E) (hf : ∀ t, StronglyMeasurable (f t)) (t : ℝ≥0) :
    StronglyMeasurable (supportedRightExtension S hS f t) :=
  StronglyMeasurable.limUnder (fun n => hf (supportedRightSequence S hS t n))

theorem tendsto_supportedRightExtension
    (S : Set ℝ≥0) (hS : ∀ t, (𝓝[S ∩ Ioi t] t).NeBot)
    (f : ℝ≥0 → Ω → E) (ω : Ω) (t : ℝ≥0)
    (hr : ∃ r, Tendsto (fun s => f s ω) (𝓝[S ∩ Ioi t] t) (𝓝 r)) :
    Tendsto (fun s => f s ω) (𝓝[S ∩ Ioi t] t)
      (𝓝 (supportedRightExtension S hS f t ω)) := by
  obtain ⟨r, hr⟩ := hr
  have heq : supportedRightExtension S hS f t ω = r :=
    (hr.comp (tendsto_supportedRightSequence S hS t)).limUnder_eq
  rw [heq]
  exact hr

end ReflectedGMS

end Merged_MeasurableCadlagExtension

set_option autoImplicit false

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped NNReal

namespace ReflectedGMS

open ReflectedWalk

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- Embed an original path, using a fixed vertex at undefined times. -/
noncomputable def reflectedCompactSample (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (PF : ProcessFamily V) (default : V)
    (t : ℝ≥0) (ω : PF.Ω) : ResolventCompactSpace.Space G m hm :=
  ResolventCompactSpace.vertex G m hm ((PF.X t ω).getD default)

/-- The same supported right-limit construction is used under every starting law. -/
noncomputable def reflectedCompactProcess (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (PF : ProcessFamily V) (default : V) :
    ℝ≥0 → PF.Ω → ResolventCompactSpace.Space G m hm := by
  letI : Nonempty (ResolventCompactSpace.Space G m hm) :=
    ⟨ResolventCompactSpace.vertex G m hm default⟩
  exact supportedRightExtension globalDyadicSupport
    globalDyadicSupport_nhdsWithin_Ioi_neBot (reflectedCompactSample G m hm PF default)

theorem stronglyMeasurable_reflectedCompactSample (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (PF : ProcessFamily V) (default : V) (t : ℝ≥0) :
    StronglyMeasurable (reflectedCompactSample G m hm PF default t) := by
  let E := ResolventCompactSpace.Space G m hm
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have he : Measurable (fun q : Option V =>
      (ResolventCompactSpace.vertex G m hm (q.getD default) : E)) :=
    measurable_of_countable _
  exact (he.comp (PF.measurable_X t)).stronglyMeasurable

theorem stronglyMeasurable_reflectedCompactProcess (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (PF : ProcessFamily V) (default : V) (t : ℝ≥0) :
    StronglyMeasurable (reflectedCompactProcess G m hm PF default t) := by
  letI : Nonempty (ResolventCompactSpace.Space G m hm) :=
    ⟨ResolventCompactSpace.vertex G m hm default⟩
  exact stronglyMeasurable_supportedRightExtension globalDyadicSupport
    globalDyadicSupport_nhdsWithin_Ioi_neBot (reflectedCompactSample G m hm PF default)
    (stronglyMeasurable_reflectedCompactSample G m hm PF default) t

namespace ResolventCompactSpace

@[simp] theorem toOption_eq_some_iff (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (p : Space G m hm) (x : V) :
    toOption G m hm p = some x ↔ p = vertex G m hm x := by
  constructor
  · intro hp
    unfold toOption at hp
    split_ifs at hp with hmem
    · have hx : Classical.choose hmem = x := Option.some.inj hp
      rw [← hx]
      exact (Classical.choose_spec hmem).symm
  · rintro rfl
    exact toOption_vertex G m hm x

end ResolventCompactSpace

/-- The same separately measurable process has càdlàg paths and recovers the
original reflected path at every time under each starting law. -/
theorem reflectedCompactProcess_ae_cadlag_and_projection
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V) :
    ∀ᵐ ω ∂PF.P z,
      IsCadlag (fun t => reflectedCompactProcess G m hm PF default t ω) ∧
      ∀ t, ResolventCompactSpace.toOption G m hm
        (reflectedCompactProcess G m hm PF default t ω) = PF.X t ω := by
  letI : Nonempty (ResolventCompactSpace.Space G m hm) :=
    ⟨ResolventCompactSpace.vertex G m hm default⟩
  filter_upwards [reflected_ae_exists_cadlag_resolventCompact_lift
    h hG hm hmsum default z] with ω hω
  obtain ⟨Y, hcad, hY, hproj⟩ := hω
  have heq : ∀ t, reflectedCompactProcess G m hm PF default t ω = Y t := by
    intro t
    letI := globalDyadicSupport_nhdsWithin_Ioi_neBot t
    have hright := tendsto_supportedRightExtension globalDyadicSupport
      globalDyadicSupport_nhdsWithin_Ioi_neBot
      (reflectedCompactSample G m hm PF default) ω t ⟨Y t, hY t⟩
    exact tendsto_nhds_unique hright (hY t)
  constructor
  · simpa only [heq] using hcad
  · intro t
    rw [heq]
    exact hproj t

/-- At each deterministic time the compact process equals the embedded
original vertex almost surely; no claim of vertex membership at all times is made. -/
theorem reflectedCompactProcess_ae_eq_sample_at_time
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V) (t : ℝ≥0) :
    reflectedCompactProcess G m hm PF default t =ᵐ[PF.P z]
      reflectedCompactSample G m hm PF default t := by
  filter_upwards [reflectedCompactProcess_ae_cadlag_and_projection
    h hG hm hmsum default z, (h z).2.1 t] with ω hω hd
  obtain ⟨x, hx⟩ := hd.1
  have hp := (ResolventCompactSpace.toOption_eq_some_iff G m hm _ x).1
    ((hω.2 t).trans hx)
  simpa only [reflectedCompactSample, hx, Option.getD_some] using hp

end ReflectedGMS
