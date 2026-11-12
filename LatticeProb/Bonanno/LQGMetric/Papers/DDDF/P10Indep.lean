/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P10Indep at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Independence.Basic
import Mathlib.Order.CompleteLattice.Finset

/-!
# Independence of processes passes to modifications (for DDDF Prop 10)

DDDF Lemma 6 (`l6_indep`) gives the independence of `φ_H` and `(φ_δ, φ_L)` as processes; DF's
proof of Props. 4.5–4.6 (arXiv:1809.02607, l. 543–549) averages over `φ_H` along a path chosen
from `(φ_δ, φ_L)`, which uses the continuous versions. `indepFun_modification`: if `X ⫫ Z` as
processes (product σ-algebras) and `X', Z'` are measurable modifications (`X' t = X t` a.s. for
each `t`), then `X' ⫫ Z'`. Proof: the σ-algebra of `X'` is the directed supremum over finite
index sets `I` of `σ(X'_t, t ∈ I)`; for finite `I` the restriction of `X'` is a.s. equal to that
of `X` (`IndepFun.congr`), and `indep_iSup_of_directed_le` concludes. Standard (own routine
step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric
namespace DDDF

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- One side: replace a process by a measurable modification. -/
lemma indepFun_modification_left {T β E : Type*} [mE : MeasurableSpace E] [mβ : MeasurableSpace β]
    {X X' : T → Ω → E} {G : Ω → β} (hX : ∀ t, Measurable (X t)) (hX' : ∀ t, Measurable (X' t))
    (hG : Measurable G) (h : ∀ t, X' t =ᵐ[P] X t)
    (hind : IndepFun (fun ω t => X t ω) G P) : IndepFun (fun ω t => X' t ω) G P := by
  classical
  rw [IndepFun_iff_Indep]
  have hcomap : MeasurableSpace.comap (fun ω t => X' t ω) MeasurableSpace.pi =
      ⨆ I : Finset T, ⨆ t ∈ I, MeasurableSpace.comap (X' t) mE := by
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, ← iSup_eq_iSup_finset]
    simp_rw [MeasurableSpace.comap_comp]
    rfl
  rw [hcomap]
  refine indep_iSup_of_directed_le (fun I => ?_) (fun I => iSup₂_le fun t _ => (hX' t).comap_le)
    hG.comap_le ?_
  · have hI : IndepFun (fun ω (i : I) => X' i ω) G P := by
      have h0 : IndepFun (fun ω (i : I) => X i ω) G P :=
        hind.comp (φ := fun (y : T → E) (i : I) => y i) (ψ := id)
          (measurable_pi_iff.2 fun i => measurable_pi_apply _) measurable_id
      refine h0.congr ?_ (Filter.EventuallyEq.refl _ _)
      have : ∀ᵐ ω ∂P, ∀ i : I, X i ω = X' i ω :=
        ae_all_iff.2 fun i => (h i).symm
      filter_upwards [this] with ω hω
      funext i; exact hω i
    rw [IndepFun_iff_Indep] at hI
    refine indep_of_indep_of_le_left hI (iSup₂_le fun t ht => ?_)
    have e : X' t = (fun y : I → E => y ⟨t, ht⟩) ∘ fun ω (i : I) => X' i ω := rfl
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  · intro I J
    refine ⟨I ∪ J, ?_, ?_⟩ <;>
      exact iSup₂_mono' fun t ht => ⟨t, by simp [ht], le_rfl⟩

/-- **Independence passes to measurable modifications.** -/
theorem indepFun_modification {T S E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂]
    {X X' : T → Ω → E₁} {Z Z' : S → Ω → E₂} (hX : ∀ t, Measurable (X t))
    (hX' : ∀ t, Measurable (X' t)) (hZ : ∀ s, Measurable (Z s)) (hZ' : ∀ s, Measurable (Z' s))
    (h1 : ∀ t, X' t =ᵐ[P] X t) (h2 : ∀ s, Z' s =ᵐ[P] Z s)
    (hind : IndepFun (fun ω t => X t ω) (fun ω s => Z s ω) P) :
    IndepFun (fun ω t => X' t ω) (fun ω s => Z' s ω) P := by
  have a := indepFun_modification_left hX hX' (measurable_pi_iff.2 hZ) h1 hind
  exact (indepFun_modification_left hZ hZ' (measurable_pi_iff.2 hX') h2 a.symm).symm

end DDDF
end LQGMetric
