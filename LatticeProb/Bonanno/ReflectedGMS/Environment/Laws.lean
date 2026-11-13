/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.Laws at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Code
import LatticeProb.Bonanno.ReflectedGMS.Environment.Similarity
import LatticeProb.Bonanno.ReflectedGMS.MeasureTheory.SupportedLaw
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Full trace-measurable environment laws and physical similarity relations.
The relation uses actual transformed cells and unchanged conductances. It does
not assert existence or measurability of the canonical relabeling action. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace ReflectedGMS.EnvironmentLaws
open Code

/-- A physical similarity preserves the weighted cell graph after a bijective
relabeling of its active vertices. Labels themselves are not physical marks. -/
def IsSimilarityRelabel (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (relabel : Vertex e.val ≃ Vertex e'.val) : Prop :=
  (∀ v, (decode e').cell (relabel v) = transformCell s u hs ((decode e).cell v)) ∧
    (∀ v w, (decode e').graph.c (relabel v) (relabel w) = (decode e).graph.c v w)

/-- The physical similarity relation forgets only which bijection witnesses it. -/
def IsSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env) : Prop :=
  ∃ relabel : Vertex e.val ≃ Vertex e'.val, IsSimilarityRelabel s u hs e e' relabel

/-- The identity physical transformation is represented without adding marks. -/
theorem isSimilarity_refl (e : Env) : IsSimilarity 1 0 (by norm_num) e e := by
  refine ⟨Equiv.refl _, ?_, ?_⟩
  · intro v
    apply SetLike.coe_injective
    have hid : positiveSimilarity 1 (0 : Plane) = id := by
      funext z
      simp [positiveSimilarity]
    simp [coe_transformCell, hid]
  · intro v w
    rfl

/-- Nonnegative transport kernels on the full trace-measurable environment
space. No extension to the ambient code space is required. -/
structure MassTransportKernel where
  toFun : Env × Plane × Plane → ℝ≥0∞
  measurable_toFun : Measurable toFun
  covariant : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env),
    IsSimilarity s u hs e e' → ∀ w z : Plane,
      toFun (e', positiveSimilarity s u w, positiveSimilarity s u z) =
        ENNReal.ofReal ((s ^ 2)⁻¹) * toFun (e, w, z)

/-- Sending mass from the origin remains jointly measurable in environment
and destination, using the full trace sigma algebra. -/
theorem MassTransportKernel.measurable_outgoing (T : MassTransportKernel) :
    Measurable (fun ez : Env × Plane => T.toFun (ez.1, 0, ez.2)) :=
  T.measurable_toFun.comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

/-- Receiving mass at the origin is jointly measurable as well. -/
theorem MassTransportKernel.measurable_incoming (T : MassTransportKernel) :
    Measurable (fun ez : Env × Plane => T.toFun (ez.1, ez.2, 0)) :=
  T.measurable_toFun.comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

/-- The manuscript's degree-minus-two mass transport identity, with Lebesgue
area and nonnegative integrals, allowing either side to be infinite. -/
def MassTransport (ν : Measure Env) : Prop :=
  ∀ T : MassTransportKernel,
    (∫⁻ e, ∫⁻ z : Plane, T.toFun (e, 0, z) ∂volume ∂ν) =
      ∫⁻ e, ∫⁻ z : Plane, T.toFun (e, z, 0) ∂volume ∂ν

/-- Invariance concerns the environment alone, under every translation and
positive dilation, including the induced relabeling of cells. -/
def SimilarityInvariant (A : Set Env) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env),
    IsSimilarity s u hs e e' → (e ∈ A ↔ e' ∈ A)

/-- Every measurable invariant event in the trace sigma algebra has law zero
or one. There is no auxiliary random grid in this definition. -/
def EnvironmentErgodic (ν : Measure Env) : Prop :=
  ∀ A : Set Env, MeasurableSet A → SimilarityInvariant A → ν A = 0 ∨ ν A = 1

/-- Ambient almost-sure validity; the validity set need not be measurable. -/
def SupportedOnValid (P : Measure RawCode) : Prop := ∀ᵐ r ∂P, Valid r

/-- Actual lifted law on the trace-measurable valid subtype. -/
noncomputable def validLaw (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValid P) : Measure Env :=
  supportedLaw P {r | Valid r} hP

instance validLaw_isProbability (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValid P) : IsProbabilityMeasure (validLaw P hP) := by
  exact supportedLaw_isProbability P {r | Valid r} hP

theorem map_validLaw (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValid P) : (validLaw P hP).map Subtype.val = P :=
  map_supportedLaw P {r | Valid r} hP

/-- The lift is uniquely characterized by its ambient inclusion pushforward. -/
theorem validLaw_unique (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValid P) (ν : Measure Env)
    (hν : ν.map Subtype.val = P) : ν = validLaw P hP :=
  supportedLaw_unique P {r | Valid r} hP ν hν

/-- Public ambient-law mass transport assumption, tested against every full
trace-environment kernel after the supported-law lift. -/
def AmbientMassTransport (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValid P) : Prop := MassTransport (validLaw P hP)

/-- Public ambient-law ergodicity assumption; only the process theorem needs it. -/
def AmbientEnvironmentErgodic (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValid P) : Prop := EnvironmentErgodic (validLaw P hP)

end ReflectedGMS.EnvironmentLaws
