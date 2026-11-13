/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.ExcursionBoundedRange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.CountableTargetExcursion

/-!
# Bounded spatial range of a single excursion

`Recurrence/CountableTargetExcursion.lean` proves, for an arbitrary target `S ⊆ VG` and an
arbitrary finite-energy competitor `f` with `f(o) = 0` and `f ≡ 1` on `S`,

  `P_o[ the walk visits S before returning to o ] ≤ E(f)/π(o)`,

the event being the pathwise `visitsTargetBeforeReturn`, which uses **no** hitting time of
`S` and no attainment.

The spatial consumer (manuscript `r:prop:criterion`) applies this to the complements of
**spatial** balls: `rho v` is the spatial radius of the vertex `v` (for cell
representatives `z`, `rho = fun v => ‖z v‖`), and the targets are

  `farTarget rho R = {v | R < rho v}`,

which are *not* graph-distance balls and for which no spatial local finiteness is assumed.
The hypothesis supplied by the annular log-cutoff estimates is that these targets admit
competitors of arbitrarily small energy (`VanishingFarEnergy`).

The conclusion proved here is the **one-excursion** half of the criterion: almost surely
the spatial radius is bounded along the whole first excursion away from `o`, i.e. along
every time `t` at or after the departure time `σ_o = exitTime 𝓧.X o` such that the path has
not returned to `o` anywhere on `[σ_o, t]` (`MemFirstExcursion`).

No Borel–Cantelli argument is needed: the unbounded-range event
`excursionRangeUnbounded` is *contained* in `visitsTargetBeforeReturn 𝓧 o (farTarget rho R)`
for **every** `R` simultaneously (it is the intersection of those events over all real `R`),
so its outer measure is bounded by every one of the vanishing energy ratios and is therefore
zero.  The intersection is uncountable, but only monotonicity of the measure is used, so no
measurability of the event is required anywhere.

What is **not** proved here: the extension from the first excursion to every excursion
completed before a fixed time `T`.  That extension is not a formal consequence of this
statement — it needs the successive return times to `o` to be almost surely finite and to
diverge (through their positive holding times), which is a genuine additional input; see the
module-final remark.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ReflectedWalk ReflectedWalk.Theorem16
open scoped NNReal ENNReal

namespace ReflectedGMS.ExcursionBoundedRange

variable {V : Type*}

/-- The target above spatial radius `R`: the complement of the closed spatial ball of radius
`R` for the (finite-valued) radius function `rho`.  With `rho = fun v => ‖z v‖` for cell
representatives `z` this is the manuscript's complement of a spatial ball. -/
def farTarget (rho : V → ℝ) (R : ℝ) : Set V := {v | R < rho v}

theorem farTarget_antitone (rho : V → ℝ) {R R' : ℝ} (hRR' : R ≤ R') :
    farTarget rho R' ⊆ farTarget rho R :=
  fun _ hv => lt_of_le_of_lt hRR' hv

/-- **The one-excursion unbounded-range event.**  The spatial radius is unbounded along the
first excursion: for every level `R` the excursion reaches a vertex of spatial radius `> R`.
Equivalently, the intersection over all `R` of the arbitrary-target excursion events. -/
def excursionRangeUnbounded (𝓧 : ProcessFamily V) (o : V) (rho : V → ℝ) : Set 𝓧.Ω :=
  ⋂ R : ℝ, CountableTargetExcursion.visitsTargetBeforeReturn 𝓧 o (farTarget rho R)

theorem excursionRangeUnbounded_subset (𝓧 : ProcessFamily V) (o : V) (rho : V → ℝ) (R : ℝ) :
    excursionRangeUnbounded 𝓧 o rho ⊆
      CountableTargetExcursion.visitsTargetBeforeReturn 𝓧 o (farTarget rho R) :=
  Set.iInter_subset _ R

/-- **The vanishing-energy hypothesis.**  Arbitrarily small-energy competitors exist for the
complements of spatial balls: for every `ε > 0` there is a level `R` and a function `f` of
finite energy on the **full** finite-energy domain, vanishing at `o`, equal to `1` on all of
`{rho > R}`, with energy ratio `E(f)/π(o) < ε`.

This is the shape delivered by the annular logarithmic cutoff estimates; no decay, summable
speed, finite support, or finite-support closure is imposed on `f`. -/
def VanishingFarEnergy (G : ConductanceGraph V) (o : V) (rho : V → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∃ f : V → ℝ, G.HasFiniteEnergy f ∧ f o = 0 ∧
    (∀ y : V, R < rho y → f y = 1) ∧ G.Energy f / G.pi o < ε

/-- A competitor vanishing at `o` and equal to `1` on `{rho > R}` witnesses that the origin
is not in that target; the excursion bound therefore needs no separate hypothesis on
`rho o`. -/
theorem notMem_farTarget_of_competitor {rho : V → ℝ} {R : ℝ} {o : V} {f : V → ℝ}
    (hfo : f o = 0) (hfS : ∀ y : V, R < rho y → f y = 1) : o ∉ farTarget rho R := by
  intro ho
  have h1 : f o = 1 := hfS o ho
  rw [hfo] at h1
  exact zero_ne_one h1

/-- An energy family indexed by a sequence of levels whose energy ratios tend to `0`
supplies the vanishing-energy hypothesis.  This is the adapter for a cutoff family indexed
by the number of annuli. -/
theorem vanishingFarEnergy_of_tendsto {G : ConductanceGraph V} {o : V} {rho : V → ℝ}
    (R : ℕ → ℝ) (f : ℕ → V → ℝ) (hf : ∀ n, G.HasFiniteEnergy (f n))
    (hfo : ∀ n, f n o = 0) (hfR : ∀ n, ∀ y : V, R n < rho y → f n y = 1)
    (hE : Filter.Tendsto (fun n => G.Energy (f n) / G.pi o) Filter.atTop (nhds 0)) :
    VanishingFarEnergy G o rho := by
  intro ε hε
  obtain ⟨n, hn⟩ := (hE.eventually_lt_const hε).exists
  exact ⟨R n, f n, hf n, hfo n, hfR n, hn⟩

section Process

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}
  [Countable V]

/-- **The one-excursion unbounded-range event is null.**  Its (outer) measure is at most
`E(f)/π(o)` for every competitor supplied by `VanishingFarEnergy`, because the event is
contained in `visitsTargetBeforeReturn 𝓧 o (farTarget rho R)` for every level `R` at once.
Only monotonicity of the measure is used, so no measurability of the event is needed and no
Borel–Cantelli argument appears. -/
theorem measure_excursionRangeUnbounded_eq_zero (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) {o : V} {rho : V → ℝ}
    (hvan : VanishingFarEnergy G o rho) :
    𝓧.P o (excursionRangeUnbounded 𝓧 o rho) = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (zero_le)
  obtain ⟨R, f, hf, hfo, hfS, hlt⟩ := hvan (ε : ℝ) (by exact_mod_cast hε)
  calc
    𝓧.P o (excursionRangeUnbounded 𝓧 o rho)
        ≤ 𝓧.P o (CountableTargetExcursion.visitsTargetBeforeReturn 𝓧 o (farTarget rho R)) :=
      measure_mono (excursionRangeUnbounded_subset 𝓧 o rho R)
    _ ≤ ENNReal.ofReal (G.Energy f / G.pi o) :=
      CountableTargetExcursion.measure_visitsTargetBeforeReturn_le_ofReal_energy_div h hG
        (notMem_farTarget_of_competitor hfo hfS) hf hfo (fun y hy => hfS y hy)
    _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hlt.le
    _ = 0 + (ε : ℝ≥0∞) := by rw [ENNReal.ofReal_coe_nnreal, zero_add]

end Process

end ReflectedGMS.ExcursionBoundedRange
