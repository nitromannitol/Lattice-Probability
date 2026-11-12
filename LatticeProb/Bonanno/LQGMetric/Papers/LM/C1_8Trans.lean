/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.C1_8Trans at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.LocJoint
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L4_Trans
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3F
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc

/-!
# LM Corollary 1.8, step 0: joint locality only depends on the joint law (task P2-LMC18)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Corollary 1.8 (l. 323–332): the conditionally i.i.d. copy
`D̃` of `D` given `h` "is individually local" — LM use without comment that `(h, D̃)` has the law
of `(h, D)` and that locality (Def 1.2) is a property of that law. This file proves the latter:

* `c18_fieldSigmaClosed_comp`: `σ((g ∘ Ψ)|_K) = Ψ⁻¹ σ(g|_K)` for the germ σ-algebra of a closed
  set (a countable decreasing infimum commutes with `comap`, by a `limsup` of representatives);
* `c18_condIndepEv_comap`: conditional independence on the law pulls back
  (converse of `DFGPS.L217.condIndepEv_map`);
* `c18_isJointlyLocalFam_transfer`: if `Φ`, `Ψ` have the same law, joint locality of
  `(g ∘ Φ; J₁ ∘ Φ, J₂ ∘ Φ)` gives joint locality of `(g ∘ Ψ; J₁ ∘ Ψ, J₂ ∘ Ψ)`.

Own routine measure theory (LM give no argument; DEVIATIONS entry proposed in the report).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip

section Transfer

variable {Ω T : Type} [mΩ : MeasurableSpace Ω] [mT : MeasurableSpace T]

omit mΩ mT in
lemma c18_fieldSigma_comp (g : T → DistC) (Ψ : Ω → T) (V : TopologicalSpace.Opens ℂ) :
    fieldSigma (fun ω => g (Ψ ω)) V = (fieldSigma g V).comap Ψ := by
  unfold fieldSigma
  rw [MeasurableSpace.comap_comp]
  rfl

omit mΩ mT in
lemma c18_famSigma_comp (J : T → Set ℂ → ℂ → ℂ → ℝ≥0∞) (Ψ : Ω → T) (W : Set ℂ) :
    famSigma (fun ω => J (Ψ ω)) W = (famSigma J W).comap Ψ := by
  unfold famSigma
  rw [MeasurableSpace.comap_comp]
  rfl

omit mΩ mT in
lemma c18_nbhdO_mono {δ ε : ℝ} (h : δ ≤ ε) (K : Set ℂ) : nbhdO δ K ≤ nbhdO ε K :=
  fun _ hx => Metric.thickening_mono h K hx

omit mΩ mT in
/-- the germ σ-algebra of a set commutes with pulling back -/
lemma c18_fieldSigmaClosed_comp (g : T → DistC) (Ψ : Ω → T) (K : Set ℂ) :
    fieldSigmaClosed (fun ω => g (Ψ ω)) K = (fieldSigmaClosed g K).comap Ψ := by
  refine le_antisymm ?_ ?_
  · intro s hs
    have hs' : ∀ n : ℕ, MeasurableSet[(fieldSigma g (nbhdO (1 / ((n : ℝ) + 1)) K)).comap Ψ] s :=
      fun n => by
        rw [← c18_fieldSigma_comp]
        unfold fieldSigmaClosed at hs
        rw [MeasurableSpace.measurableSet_iInf] at hs
        have := hs (1 / ((n : ℝ) + 1))
        rw [MeasurableSpace.measurableSet_iInf] at this
        exact this (by positivity)
    choose S hS hSs using hs'
    refine ⟨⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), S n, ?_, ?_⟩
    · unfold fieldSigmaClosed
      rw [MeasurableSpace.measurableSet_iInf]
      intro ε
      rw [MeasurableSpace.measurableSet_iInf]
      intro hε
      obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
      have e : (⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), S n) =
          ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N + M ≤ n), S n := by
        ext x
        simp only [mem_iInter, mem_iUnion, exists_prop]
        constructor
        · intro hx N
          exact hx (N + M)
        · intro hx N
          obtain ⟨n, hn, hxn⟩ := hx N
          exact ⟨n, by omega, hxn⟩
      rw [e]
      refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
        MeasurableSet.iUnion fun hn => ?_
      refine GM.fieldSigma_mono g (c18_nbhdO_mono ?_ K) _ (hS n)
      have hMn : (M : ℝ) ≤ n := by exact_mod_cast (le_trans (Nat.le_add_left M N) hn)
      refine le_trans ?_ hM.le
      gcongr
    · ext x
      simp only [mem_preimage, mem_iInter, mem_iUnion, exists_prop]
      constructor
      · intro hx
        obtain ⟨n, _, hxn⟩ := hx 0
        rw [← hSs n]
        exact hxn
      · intro hx N
        exact ⟨N, le_rfl, by rw [← mem_preimage, hSs N]; exact hx⟩
  · unfold fieldSigmaClosed
    refine le_iInf₂ fun ε hε => ?_
    rw [c18_fieldSigma_comp]
    exact MeasurableSpace.comap_mono (iInf₂_le ε hε)

end Transfer

/-- conditional independence on the law pulls back (converse of `DFGPS.L217.condIndepEv_map`) -/
theorem c18_condIndepEv_comap {Ω T : Type*} {G A B : MeasurableSpace T} [mΩ : MeasurableSpace Ω]
    [mT : MeasurableSpace T] {ρ : Measure Ω} [IsProbabilityMeasure ρ] {π : Ω → T} (hπ : Measurable π) (hG : G ≤ mT) (hA : A ≤ mT) (hB : B ≤ mT)
    (h : CondIndepEv G A B (ρ.map π)) : CondIndepEv (G.comap π) (A.comap π) (B.comap π) ρ := by
  have : IsProbabilityMeasure (ρ.map π) :=
    (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
  rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have ha' := hA a ha
  have hb' := hB b hb
  have ind : ∀ s : Set T, (s.indicator fun _ => (1 : ℝ)) ∘ π =
      (π ⁻¹' s).indicator fun _ => (1 : ℝ) := fun s => by
    funext x; simp only [Function.comp, Set.indicator, Set.mem_preimage]; rfl
  have e : ∀ s : Set T, MeasurableSet s → ρ⟦π ⁻¹' s | G.comap π⟧ =ᵐ[ρ]
      (ρ.map π)⟦s | G⟧ ∘ π := fun s hs => by
    rw [← ind s]
    exact DFGPS.L217.condExp_comp_map hπ hG (integrable_indOne hs)
  have H := ae_of_ae_map hπ.aemeasurable (h a b ha hb)
  have e1 := e _ (ha'.inter hb')
  rw [Set.preimage_inter] at e1
  filter_upwards [H, e1, e _ ha', e _ hb'] with x hx h1 h2 h3
  simp only [Function.comp, Pi.mul_apply] at hx h1 h2 h3 ⊢
  rw [h1, h2, h3, hx]

section JointTransfer

variable {Ω Ω' T : Type} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [mT : MeasurableSpace T]

/-- **joint locality only depends on the law**: if `Φ` and `Ψ` have the same law, and the field
and the internal-metric families are functions of them, joint locality passes from `Φ` to `Ψ` -/
theorem c18_isJointlyLocalFam_transfer {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {Φ : Ω → T} {Ψ : Ω' → T} (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    (hlaw : P.map Φ = P'.map Ψ) {g : T → DistC} (hg : Measurable g)
    {J₁ J₂ : T → Set ℂ → ℂ → ℂ → ℝ≥0∞} (hJ₁ : ∀ W : Set ℂ, IsOpen W → Measurable fun t => J₁ t W)
    (hJ₂ : ∀ W : Set ℂ, IsOpen W → Measurable fun t => J₂ t W)
    (hI : IsJointlyLocalFam P (fun ω => g (Φ ω)) (fun ω => J₁ (Φ ω)) (fun ω => J₂ (Φ ω))) :
    IsJointlyLocalFam P' (fun ω => g (Ψ ω)) (fun ω => J₁ (Ψ ω)) (fun ω => J₂ (Ψ ω)) := by
  intro V
  have hO : IsOpen (closure (V : Set ℂ))ᶜ := isClosed_closure.isOpen_compl
  have hG : fieldSigma g V ≤ mT := fieldSigma_le hg V
  have hA : famSigma J₁ V ⊔ famSigma J₂ V ≤ mT :=
    sup_le (hJ₁ V V.isOpen).comap_le (hJ₂ V V.isOpen).comap_le
  have hB : fieldSigmaClosed g (V : Set ℂ)ᶜ ⊔ famSigma J₁ (closure (V : Set ℂ))ᶜ ⊔
      famSigma J₂ (closure (V : Set ℂ))ᶜ ≤ mT :=
    sup_le (sup_le (fieldSigmaClosed_le hg _) (hJ₁ _ hO).comap_le) (hJ₂ _ hO).comap_le
  have H := hI V
  simp only [c18_fieldSigma_comp, c18_fieldSigmaClosed_comp, c18_famSigma_comp,
    ← MeasurableSpace.comap_sup] at H
  have H2 := DFGPS.L217.condIndepEv_map hΦ hG hA hB H
  rw [hlaw] at H2
  have H3 := c18_condIndepEv_comap hΨ hG hA hB H2
  simp only [c18_fieldSigma_comp, c18_fieldSigmaClosed_comp, c18_famSigma_comp,
    ← MeasurableSpace.comap_sup]
  exact H3

end JointTransfer

end LQGMetric.LM
