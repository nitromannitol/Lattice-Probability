/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasC1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Meas

/-!
# GM Lemma 4.6 (c): σ-algebra glue (task P2-E3b)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 4.6, last claim, and its proof, l. 1710–1716 ("on `Stab ∩ {P ∩ B_r(z) ≠ ∅}`, both
`(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` and the arc of `𝓘_k` which contains `P(t_k)` are a.s. determined by
`h|_{ℂ∖B_r(z)}` and the indicator …; the last statement of the lemma follows from the second
statement and Lemma 4.5").

* `gmTraceSigma M E μ`: the events whose trace on `E` is a.s. an event of `M` form a σ-algebra
  when `E ∈ M` (own elementary argument);
* `gm_trace_of_aeDet`: if `F` is a.s. determined by `A ⊔ σ(𝒢)` and the traces on `E` of the
  `A`-events and of the generators are a.s. in `M`, so are the traces of all `F`-events;
* `gm_L4_6c_of`: GM Lemma 4.6 (c) in the form of `gm_L4_7_pair`'s hypothesis `hL46`, from Lemma 4.5
  (E2b, `gm_L4_5_E2b`: `𝓕_k` is a.s. determined by `𝓕'_k = σ(𝓑^•_{t_k}, h|) ∨ σ(arc)`) and the
  two traced locality statements of GM's second claim (hypotheses `hA`, `hArc`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

set_option warn.classDefReducibility false

open MeasureTheory Filter Set MeasurableSpace
open LQGMetric.Blueprint

namespace LQGMetric.GM

section Generic
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- the events whose trace on `E` is a.s. an event of `M` -/
def gmTraceSigma (M : MeasurableSpace Ω) (E : Set Ω) (hE : MeasurableSet[M] E)
    (μ : Measure[mΩ] Ω) : MeasurableSpace Ω where
  MeasurableSet' s := ∃ t, MeasurableSet[M] t ∧ s ∩ E =ᵐ[μ] t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, by rw [empty_inter]⟩
  measurableSet_compl := fun s ⟨t, ht, hst⟩ => by
    refine ⟨E \ t, hE.diff ht, ?_⟩
    have e : sᶜ ∩ E = E \ (s ∩ E) := by
      ext x; simp only [mem_inter_iff, mem_compl_iff, mem_diff]; tauto
    rw [e]
    exact EventuallyEqSet.inter (EventuallyEq.refl _ E) (EventuallyEqSet.compl hst)
  measurableSet_iUnion := fun f hf => by
    choose t ht hft using hf
    refine ⟨⋃ i, t i, MeasurableSet.iUnion ht, ?_⟩
    rw [iUnion_inter]
    exact EventuallyEqSet.countable_iUnion hft

/-- traces on `E` of events of `F`, from `F ≈ A ⊔ σ(𝒢)` and the traces of `A` and `𝒢` -/
theorem gm_trace_of_aeDet {μ : Measure[mΩ] Ω} {F A M : MeasurableSpace Ω} {𝒢 : Set (Set Ω)}
    {E : Set Ω} (hE : MeasurableSet[M] E) (hF : AEDeterminedSigma F (A ⊔ generateFrom 𝒢) μ)
    (hA : ∀ a, MeasurableSet[A] a → ∃ t, MeasurableSet[M] t ∧ a ∩ E =ᵐ[μ] t)
    (h𝒢 : ∀ g ∈ 𝒢, ∃ t, MeasurableSet[M] t ∧ g ∩ E =ᵐ[μ] t) :
    ∀ s, MeasurableSet[F] s → ∃ t, MeasurableSet[M] t ∧ s ∩ E =ᵐ[μ] t := by
  have hle : A ⊔ generateFrom 𝒢 ≤ gmTraceSigma M E hE μ :=
    sup_le (fun a ha => hA a ha) (generateFrom_le fun g hg => h𝒢 g hg)
  intro s hs
  obtain ⟨u, hu, hsu⟩ := hF s hs
  obtain ⟨t, ht, hut⟩ := hle u hu
  exact ⟨t, ht, (hsu.inter (EventuallyEq.refl _ E)).trans hut⟩

end Generic

/-- **GM Lemma 4.6 (c)** (l. 1710–1716) in the form `gm_L4_7_pair` consumes: with
`E = Stab ∩ Hit`, every `𝓕_k`-event traced on `E` is a.s. an event of
`σ(h|_{ℂ∖B_ρ(z)}) ∨ σ(1_E)`. Inputs: GM Lemma 4.5 (E2b), and GM's second claim (traces on `E` of
the events of `σ(𝓑^•_{t_k}, h|)` and of the hit events of the arc of `𝓘_k` containing `P(t_k)`). -/
theorem gm_L4_6c_of {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {D : DistC → ContMetric}
    {h : Ω → DistC} {𝕫 𝕨 : ℂ} {η : Ω → C(unitInterval, ℂ)} {sk tk : Ω → ℝ}
    {G : MeasurableSpace Ω} {Stab Hit : Set Ω}
    (hE2b : AEDeterminedSigma (gmSigF D h 𝕫 𝕨 η sk tk) (gmSigF' D h 𝕫 𝕨 η sk tk) P)
    (hA : ∀ a, MeasurableSet[gmSigA D h 𝕫 tk] a →
      ∃ t, MeasurableSet[G ⊔ generateFrom {Stab ∩ Hit}] t ∧ a ∩ (Stab ∩ Hit) =ᵐ[P] t)
    (hArc : ∀ U : Set ℂ, IsOpen U → ∃ t, MeasurableSet[G ⊔ generateFrom {Stab ∩ Hit}] t ∧
      gmArcHit D h 𝕫 𝕨 η sk tk U ∩ (Stab ∩ Hit) =ᵐ[P] t) :
    ∀ F', MeasurableSet[gmSigF D h 𝕫 𝕨 η sk tk] F' →
      ∃ t, MeasurableSet[G ⊔ generateFrom {Stab ∩ Hit}] t ∧ F' ∩ (Stab ∩ Hit) =ᵐ[P] t := by
  have hE : MeasurableSet[G ⊔ generateFrom {Stab ∩ Hit}] (Stab ∩ Hit) :=
    le_sup_right (α := MeasurableSpace Ω) _ (measurableSet_generateFrom rfl)
  refine gm_trace_of_aeDet hE hE2b hA ?_
  rintro _ ⟨U, hU, rfl⟩
  exact hArc U hU

end LQGMetric.GM
