/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.LocCI at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_19CI
import LatticeProb.Bonanno.LQGMetric.Meas.Internal

/-!
# LM §1–2 locality: conditional-independence toolkit (task P2-LMLOC)

Generic σ-algebra facts used in the proofs of LM Lemma 1.4 (`lem-jointly-local`, LM
`local-metrics-final.tex` l. 253–274) and LM Lemma 2.3 (`lem-local-equiv`, l. 523–549), on top of
the project's toolkit (`LQGMetric.CondIndepEv`, `condIndepEv_sup_of_condIndepEv` = SS13 Lemma 3.5
in conditional form, `DFGPS.L219.condIndepEv_transfer` = weak union up to null events).

* `condIndepEv_contraction`: `A ⟂ B | G` and `A ⟂ C | B ∨ G` give `A ⟂ B ∨ C | G` (the
  contraction property, Kallenberg, *Foundations of Modern Probability*, 2nd ed., Prop. 6.8;
  cited for the statement; LM l. 264–266 uses it: "the conditional law of `D₁(·,·;V)` given
  `(D₁(U∖V̄), D₂(U∖V̄), h)` is the same as … given `(D₁(U∖V̄), h)` … the same as … given `h|_V`").
* `condIndepEv_iSup_of_monotone`: an increasing sequence `Aₙ` with `Aₙ ⟂ B | G` for each `n`
  gives `⋁ₙ Aₙ ⟂ B | G` (LM l. 548: "Letting `W` increase to all of `V`").
* `chainSigma D W`: the Borel version `σ(chainInf D W)` of `σ(D(·,·;W))`, equal to it up to null
  events for an a.s. length metric (`famSigma_le_chainSigma`, `chainSigma_le_famSigma`).

Proofs: own elementary arguments (Markov form of conditional independence, π–λ theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip

section Generic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Contraction**: `A ⟂ B | G` and `A ⟂ C | B ∨ G` give `A ⟂ B ∨ C | G`. -/
theorem condIndepEv_contraction [IsProbabilityMeasure μ] {G A B C : MeasurableSpace Ω}
    (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ) (hC : C ≤ mΩ) (h1 : CondIndepEv G A B μ)
    (h2 : CondIndepEv (B ⊔ G) A C μ) : CondIndepEv G A (B ⊔ C) μ := by
  refine condIndepEv_of_condExp_sup_eq hG hA (sup_le hB hC) fun a ha => ?_
  have e : B ⊔ C ⊔ G = C ⊔ (B ⊔ G) := by
    rw [sup_assoc, sup_comm C G, ← sup_assoc, sup_comm _ C, ← sup_assoc, sup_comm C B]
  rw [e]
  exact (condExp_sup_eq_of_condIndepEv (sup_le hB hG) hC hA h2.symm ha).trans
    (condExp_sup_eq_of_condIndepEv hG hB hA h1.symm ha)

/-- **Increasing limits**: if `Aₙ ↑` and `Aₙ ⟂ B | G` for each `n`, then `⋁ₙ Aₙ ⟂ B | G`. -/
theorem condIndepEv_iSup_of_monotone [IsProbabilityMeasure μ] {G B : MeasurableSpace Ω}
    {A : ℕ → MeasurableSpace Ω} (hG : G ≤ mΩ) (hA : ∀ n, A n ≤ mΩ) (hB : B ≤ mΩ)
    (hmono : Monotone A) (h : ∀ n, CondIndepEv G (A n) B μ) :
    CondIndepEv G (⨆ n, A n) B μ := by
  refine CondIndepEv.symm (condIndepEv_of_condExp_sup_eq hG hB (iSup_le hA) fun b hb => ?_)
  set M : ℕ → MeasurableSpace Ω := fun n => A n ⊔ G with hMdef
  have hM : Monotone M := fun m n hmn => sup_le_sup_right (hmono hmn) _
  have hsup : (⨆ n, A n) ⊔ G = ⨆ n, M n := iSup_sup
  have hle : (⨆ n, A n) ⊔ G ≤ mΩ := sup_le (iSup_le hA) hG
  have hb0 := hB b hb
  refine (ae_eq_condExp_of_isPiSystem hle (p := ⋃ n, {s | MeasurableSet[M n] s}) ?_ ?_
    (integrable_indOne hb0) integrable_condExp (stronglyMeasurable_condExp.mono le_sup_right)
    (integral_condExp hG) ?_).symm
  · rw [hsup]; exact (MeasurableSpace.generateFrom_iUnion_measurableSet M).symm
  · exact isPiSystem_iUnion_of_monotone (fun n => {s | MeasurableSet[M n] s})
      (fun n => @MeasurableSpace.isPiSystem_measurableSet Ω (M n))
      (fun m n hmn s hs => hM hmn s hs)
  · intro s hs
    obtain ⟨n, hn⟩ := mem_iUnion.1 hs
    have hMn : M n ≤ mΩ := sup_le (hA n) hG
    have hk := condExp_sup_eq_of_condIndepEv hG (hA n) hB (h n) hb
    calc ∫ x in s, (μ⟦b | G⟧) x ∂μ = ∫ x in s, (μ⟦b | A n ⊔ G⟧) x ∂μ :=
          setIntegral_congr_ae (hMn s hn) (hk.mono fun x hx _ => hx.symm)
      _ = ∫ x in s, b.indicator (fun _ => (1 : ℝ)) x ∂μ :=
          setIntegral_condExp hMn (integrable_indOne hb0) hn

end Generic

section Chain

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- the Borel version `σ(chainInf D W)` of `σ(D(·,·;W))` -/
def chainSigma (D : Ω → ContMetric) (W : Set ℂ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (u v : ℂ) => (D ω).chainInf W u v) inferInstance

theorem measurable_chainFn {M : MeasurableSpace Ω} {D : Ω → ContMetric} (hD : Measurable[M] D)
    (W : Set ℂ) : Measurable[M] fun ω (u v : ℂ) => (D ω).chainInf W u v :=
  measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
    (ContMetric.measurable_chainInf W).comp (hD.prodMk (measurable_const.prodMk measurable_const))

theorem chainSigma_le_comap (D : Ω → ContMetric) (W : Set ℂ) :
    chainSigma D W ≤ MeasurableSpace.comap D inferInstance :=
  (measurable_chainFn (comap_measurable D) W).comap_le

theorem chainSigma_le {D : Ω → ContMetric} (hD : Measurable D) (W : Set ℂ) : chainSigma D W ≤ mΩ :=
  (chainSigma_le_comap D W).trans hD.comap_le

theorem famSigma_le_chainSigma {D : Ω → ContMetric} (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) {W : Set ℂ}
    (hW : IsOpen W) : famSigma (internalFam D) W ≤ aeClosure P (chainSigma D W) := by
  refine famSigma_le_aeClosure_of_measurable (comap_measurable _) ?_
  filter_upwards [hlen] with ω hω
  funext u v
  exact (D ω).internal_eq_chainInf hω hW u v

theorem chainSigma_le_famSigma {D : Ω → ContMetric} (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) {W : Set ℂ}
    (hW : IsOpen W) : chainSigma D W ≤ aeClosure P (famSigma (internalFam D) W) := by
  rintro s ⟨S, hS, rfl⟩
  refine ⟨(fun ω => internalFam D ω W) ⁻¹' S, ⟨S, hS, rfl⟩, ?_⟩
  filter_upwards [hlen] with ω hω
  have e : (fun u v => (D ω).chainInf W u v) = internalFam D ω W := by
    funext u v; exact ((D ω).internal_eq_chainInf hω hW u v).symm
  change ((fun u v => (D ω).chainInf W u v) ∈ S) = (internalFam D ω W ∈ S)
  rw [e]

end Chain

end LQGMetric.LM
