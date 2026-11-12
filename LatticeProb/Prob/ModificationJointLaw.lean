import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Independence.Basic

/-!
# Joint laws of modifications

Let `X` and `Y` be stochastic processes indexed by an arbitrary set `T` such that `Y` is a modification of `X`:
`X t = Y t` almost surely for every `t`. If both are a.e. measurable for the product σ-algebra, then for every
a.e. measurable random variable `Z` the pairs `(Z, X)` and `(Z, Y)` have the same law. In particular independence of
`Z` from `X` transfers to `Y`.

The index set may be uncountable: the statement is about laws on the product σ-algebra, which are determined by the
finite dimensional distributions (`ProbabilityTheory.map_eq_of_forall_ae_eq`). The random variable `Z` is adjoined
as the coordinate `none` of a process indexed by `Option T` (`optionAdjoinJoin`).
-/

open MeasureTheory

namespace ProbabilityTheory

universe u v w

variable {T : Type u} {Ω : Type v} {β : Type w} {𝓧 : T → Type w} {mΩ : MeasurableSpace Ω}
  [mα : ∀ t, MeasurableSpace (𝓧 t)] [mβ : MeasurableSpace β] {P : Measure Ω}

/-- The state spaces of the process indexed by `Option T` that adjoins a random variable with values in `β`. -/
abbrev OptionAdjoin (β : Type w) (𝓧 : T → Type w) : Option T → Type w := fun o => o.elim β 𝓧

instance OptionAdjoin.instMeasurableSpace (β : Type w) (𝓧 : T → Type w) [MeasurableSpace β]
    [∀ t, MeasurableSpace (𝓧 t)] : ∀ o, MeasurableSpace (OptionAdjoin β 𝓧 o)
  | none => ‹MeasurableSpace β›
  | some t => ‹∀ t, MeasurableSpace (𝓧 t)› t

/-- The pair `(z, x)` as a function on `Option T`: `z` at `none` and `x t` at `some t`. -/
def optionAdjoinJoin (p : β × (∀ t, 𝓧 t)) : ∀ o, OptionAdjoin β 𝓧 o
  | none => p.1
  | some t => p.2 t

/-- The pair `(z, x)` recovered from a function on `Option T`. -/
def optionAdjoinSplit (w : ∀ o, OptionAdjoin β 𝓧 o) : β × (∀ t, 𝓧 t) :=
  (w none, fun t => w (some t))

lemma measurable_optionAdjoinJoin : Measurable (optionAdjoinJoin (β := β) (𝓧 := 𝓧)) := by
  refine measurable_pi_iff.mpr fun o => ?_
  cases o with
  | none => exact measurable_fst
  | some t => exact (measurable_pi_apply t).comp measurable_snd

lemma measurable_optionAdjoinSplit : Measurable (optionAdjoinSplit (β := β) (𝓧 := 𝓧)) :=
  (measurable_pi_apply none).prodMk (measurable_pi_iff.mpr fun t => measurable_pi_apply (some t))

/-- **Modifications have the same joint law with a third random variable.** If `X t = Y t` a.s. for every index `t`,
the processes are a.e. measurable for the product σ-algebra, and `Z` is a.e. measurable, then `(Z, X)` and `(Z, Y)`
have the same law. -/
theorem map_prod_eq_of_forall_ae_eq [IsFiniteMeasure P] {Z : Ω → β} {X Y : ∀ t, Ω → 𝓧 t}
    (hZ : AEMeasurable Z P) (hX : AEMeasurable (fun ω t => X t ω) P)
    (hY : AEMeasurable (fun ω t => Y t ω) P) (h : ∀ t, X t =ᵐ[P] Y t) :
    P.map (fun ω => (Z ω, fun t => X t ω)) = P.map (fun ω => (Z ω, fun t => Y t ω)) := by
  have hW : ∀ V : ∀ t, Ω → 𝓧 t, AEMeasurable (fun ω t => V t ω) P →
      AEMeasurable (fun ω => optionAdjoinJoin (Z ω, fun t => V t ω)) P := fun V hV =>
    measurable_optionAdjoinJoin.comp_aemeasurable (hZ.prodMk hV)
  have hWeq : P.map (fun ω => optionAdjoinJoin (Z ω, fun t => X t ω)) =
      P.map (fun ω => optionAdjoinJoin (Z ω, fun t => Y t ω)) := by
    refine map_eq_of_forall_ae_eq (X := fun o ω => optionAdjoinJoin (Z ω, fun t => X t ω) o)
      (Y := fun o ω => optionAdjoinJoin (Z ω, fun t => Y t ω) o) (hW X hX) (hW Y hY) ?_
    rintro (_ | t)
    · exact Filter.EventuallyEq.rfl
    · exact h t
  have e : ∀ V : ∀ t, Ω → 𝓧 t, (fun ω => (Z ω, fun t => V t ω)) =
      optionAdjoinSplit ∘ fun ω => optionAdjoinJoin (Z ω, fun t => V t ω) := fun V => rfl
  rw [e X, e Y, ← AEMeasurable.map_map_of_aemeasurable measurable_optionAdjoinSplit.aemeasurable (hW X hX),
    ← AEMeasurable.map_map_of_aemeasurable measurable_optionAdjoinSplit.aemeasurable (hW Y hY), hWeq]

/-- **Independence transfers to a modification.** If `X t = Y t` a.s. for every index `t`, the processes are a.e.
measurable for the product σ-algebra, `Z` is a.e. measurable and `Z` is independent of `X`, then `Z` is independent
of `Y`. -/
theorem IndepFun.of_forall_ae_eq [IsFiniteMeasure P] {Z : Ω → β} {X Y : ∀ t, Ω → 𝓧 t}
    (hZ : AEMeasurable Z P) (hX : AEMeasurable (fun ω t => X t ω) P)
    (hY : AEMeasurable (fun ω t => Y t ω) P) (h : ∀ t, X t =ᵐ[P] Y t)
    (hind : IndepFun Z (fun ω t => X t ω) P) : IndepFun Z (fun ω t => Y t ω) P := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hZ hY, ← map_prod_eq_of_forall_ae_eq hZ hX hY h,
    ← map_eq_of_forall_ae_eq hX hY h]
  exact (indepFun_iff_map_prod_eq_prod_map_map hZ hX).1 hind

end ProbabilityTheory
