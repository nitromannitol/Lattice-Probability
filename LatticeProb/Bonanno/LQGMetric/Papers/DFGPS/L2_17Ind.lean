/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Ind at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, Step 3: independence is preserved under convergence in law

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:1260: "Since independence is preserved
under convergence in law, we obtain from (eqn-internal-metric-ind) and
(eqn-internal-joint-law-conv) that `(h|_V, D_{h,W})` and `(h̊, D_{h−φ𝔥,W'})` are independent."

* `eq_prod_of_tendsto`: a weak limit of product probability measures on `S × T` is the product of
  its marginals (from mathlib's continuity of `ProbabilityMeasure.prod` and of push-forwards, and
  uniqueness of weak limits).
* `indepFun_of_tendsto_law`: if `Xₙ ⫫ Yₙ` and `(Xₙ, Yₙ) → (X, Y)` in law, then `X ⫫ Y`.

Spaces: second-countable pseudo-metrizable Borel spaces (all the state spaces of DFGPS §2 are
Polish). Proof: standard (e.g. Billingsley, *Convergence of Probability Measures*, 2nd ed.,
Thm 2.8, which characterizes weak convergence of product measures; not in `literature/`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace

namespace LQGMetric.DFGPS.L217

variable {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] [MeasurableSpace S]
  [MeasurableSpace T] [BorelSpace S] [BorelSpace T] [SecondCountableTopology S]
  [SecondCountableTopology T] [PseudoMetrizableSpace S] [PseudoMetrizableSpace T]

/-- the product of the two marginals of a probability measure on `S × T` -/
def prodMarg (ν : ProbabilityMeasure (S × T)) : ProbabilityMeasure (S × T) :=
  (ν.map Prod.fst).prod (ν.map Prod.snd)

theorem continuous_prodMarg : Continuous (prodMarg (S := S) (T := T)) := by
  unfold prodMarg
  exact ProbabilityMeasure.continuous_prod.comp
    ((ProbabilityMeasure.continuous_map continuous_fst).prodMk
      (ProbabilityMeasure.continuous_map continuous_snd))

/-- a weak limit of product measures is the product of its marginals -/
theorem eq_prodMarg_of_tendsto {ρ : ℕ → ProbabilityMeasure (S × T)}
    {ρ₀ : ProbabilityMeasure (S × T)} (hρ : Tendsto ρ atTop (𝓝 ρ₀))
    (hprod : ∀ n, ρ n = prodMarg (ρ n)) : ρ₀ = prodMarg ρ₀ :=
  tendsto_nhds_unique hρ (((continuous_prodMarg.tendsto ρ₀).comp hρ).congr fun n =>
    (hprod n).symm)

omit [TopologicalSpace S] [TopologicalSpace T] [BorelSpace S] [BorelSpace T]
  [SecondCountableTopology S] [SecondCountableTopology T] [PseudoMetrizableSpace S]
  [PseudoMetrizableSpace T] in
lemma map_fst_snd_pair {Ω₁ : Type*} [MeasurableSpace Ω₁] {Q : Measure Ω₁} {A : Ω₁ → S}
    {B : Ω₁ → T} (hA : AEMeasurable A Q) (hB : AEMeasurable B Q) :
    (Q.map fun ω => (A ω, B ω)).map Prod.fst = Q.map A ∧
      (Q.map fun ω => (A ω, B ω)).map Prod.snd = Q.map B := by
  refine ⟨?_, ?_⟩
  · rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hA.prodMk hB)]; rfl
  · rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable (hA.prodMk hB)]; rfl

/-- **Independence is preserved under convergence in law** (DFGPS T:1260). -/
theorem indepFun_of_tendsto_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Xn : ℕ → Ω → S} {Yn : ℕ → Ω → T} {X : Ω' → S} {Y : Ω' → T}
    (hXn : ∀ n, AEMeasurable (Xn n) P) (hYn : ∀ n, AEMeasurable (Yn n) P)
    (hX : AEMeasurable X P') (hY : AEMeasurable Y P')
    (hind : ∀ n, IndepFun (Xn n) (Yn n) P)
    {ρ : ℕ → ProbabilityMeasure (S × T)} {ρ₀ : ProbabilityMeasure (S × T)}
    (hρn : ∀ n, (ρ n : Measure (S × T)) = P.map fun ω => (Xn n ω, Yn n ω))
    (hρ₀ : (ρ₀ : Measure (S × T)) = P'.map fun ω => (X ω, Y ω))
    (hρ : Tendsto ρ atTop (𝓝 ρ₀)) : IndepFun X Y P' := by
  have hprod : ∀ n, ρ n = prodMarg (ρ n) := by
    intro n
    apply Subtype.ext
    change (ρ n : Measure (S × T)) =
      ((ρ n : Measure (S × T)).map Prod.fst).prod ((ρ n : Measure (S × T)).map Prod.snd)
    rw [hρn n, (map_fst_snd_pair (hXn n) (hYn n)).1, (map_fst_snd_pair (hXn n) (hYn n)).2]
    exact (indepFun_iff_map_prod_eq_prod_map_map (hXn n) (hYn n)).1 (hind n)
  have h₀ := congrArg (fun ν : ProbabilityMeasure (S × T) => (ν : Measure (S × T)))
    (eq_prodMarg_of_tendsto hρ hprod)
  change (ρ₀ : Measure (S × T)) =
    ((ρ₀ : Measure (S × T)).map Prod.fst).prod ((ρ₀ : Measure (S × T)).map Prod.snd) at h₀
  rw [hρ₀, (map_fst_snd_pair hX hY).1, (map_fst_snd_pair hX hY).2] at h₀
  exact (indepFun_iff_map_prod_eq_prod_map_map hX hY).2 h₀

end LQGMetric.DFGPS.L217
