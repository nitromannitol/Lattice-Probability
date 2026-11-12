/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K5e at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114U1

/-!
# CONF Theorem 3.9, packet J6d: gluing over hull pieces with extra local information

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1559–1561 ("`𝓘_k` is determined by `(𝓑^•_{s_k}, h|_{𝓑^•_{s_k}})`"): on a hull piece
`{A^{(n)} = S}` the arcs are functions of the field on `int S` *and* of the sets `𝓑^•_{s_k}`,
`𝓑^•_τ` (events of `σ(A, h|_A) mod const`), not of the field alone.

* `t39k5_trace_sup`: on `{A^{(n)} = S}`, the trace of `σ(h|_{int S} mod const) ⊔ hullSigma0 h A n`
  lies in `hullSigma0 h A n`;
* **`t39k5_aeEventIn_hullSigma0_of_pieces`**: `conf36_aeEventIn_hullSigma0_of_pieces`
  (S3D114U1) with the piece events in `fieldSigma0On h (int S) ⊔ hullSigma0 h A n`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric.CONF

open Blueprint

variable {Ω : Type}

/-- the trace of `fieldSigma0On h (int S) ⊔ hullSigma0 h A n` on `{A^{(n)} = S}` lies in
`hullSigma0 h A n` -/
theorem t39k5_trace_sup (h : Ω → DistC) (A : Ω → Set ℂ) (n : ℕ) (S : Set ℂ) {F : Set Ω}
    (hF : MeasurableSet[fieldSigma0On h (interior S) ⊔ hullSigma0 h A n] F) :
    MeasurableSet[hullSigma0 h A n] ({ω | dyadicHull n (A ω) = S} ∩ F) := by
  set Q := {ω | dyadicHull n (A ω) = S}
  have hQF : ∀ F', MeasurableSet[fieldSigma0On h (interior S)] F' →
      MeasurableSet[hullSigma0 h A n] (Q ∩ F') := fun F' hF' =>
    (le_sup_right : _ ≤ hullSigma0 h A n) _
      (MeasurableSpace.measurableSet_generateFrom ⟨S, F', hF', rfl⟩)
  have hQ : MeasurableSet[hullSigma0 h A n] Q := by
    simpa using hQF univ MeasurableSet.univ
  let M : MeasurableSpace Ω :=
    { MeasurableSet' := fun F' => MeasurableSet[hullSigma0 h A n] (Q ∩ F')
      measurableSet_empty := by simp
      measurableSet_compl := fun F' hF' => by
        have : Q ∩ F'ᶜ = Q ∩ (Q ∩ F')ᶜ := by
          ext ω; simp only [mem_inter_iff, mem_compl_iff]; tauto
        rw [this]; exact hQ.inter hF'.compl
      measurableSet_iUnion := fun f hf => by
        rw [inter_iUnion]; exact MeasurableSet.iUnion hf }
  have hle : fieldSigma0On h (interior S) ⊔ hullSigma0 h A n ≤ M :=
    sup_le (fun F' hF' => hQF F' hF') (fun F' hF' => hQ.inter hF')
  exact hle F hF

/-- **gluing over hull pieces** with piece events in `σ(h|_{int S} mod const) ⊔ hullSigma0 h A n` -/
theorem t39k5_aeEventIn_hullSigma0_of_pieces [MeasurableSpace Ω] {P : Measure Ω} (h : Ω → DistC)
    (A : Ω → Set ℂ)
    (n : ℕ) {𝒮 : Set (Set ℂ)} (h𝒮 : 𝒮.Countable) (hA : ∀ᵐ ω ∂P, dyadicHull n (A ω) ∈ 𝒮)
    {E : Set Ω}
    (hE : ∀ S ∈ 𝒮, ∃ F, MeasurableSet[fieldSigma0On h (interior S) ⊔ hullSigma0 h A n] F ∧
      ∀ᵐ ω ∂P, dyadicHull n (A ω) = S → (ω ∈ E ↔ ω ∈ F)) :
    AEEventIn P (hullSigma0 h A n) E := by
  choose! F hFm hEF using hE
  refine ⟨⋃ S ∈ 𝒮, {ω | dyadicHull n (A ω) = S} ∩ F S, ?_, ?_⟩
  · exact MeasurableSet.biUnion h𝒮 fun S hS => t39k5_trace_sup h A n S (hFm S hS)
  · have hall : ∀ᵐ ω ∂P, ∀ S ∈ 𝒮, dyadicHull n (A ω) = S → (ω ∈ E ↔ ω ∈ F S) :=
      (ae_ball_iff h𝒮).2 hEF
    filter_upwards [hA, hall] with ω hω hω'
    apply propext
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_prop]
    constructor
    · exact fun hE => ⟨_, hω, rfl, (hω' _ hω rfl).1 hE⟩
    · rintro ⟨S, hS, hSω, hF⟩
      exact (hω' S hS hSω).2 hF

end LQGMetric.CONF
