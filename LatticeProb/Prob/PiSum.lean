/-
Two independent families side by side, and holding a parameter fixed.

Two things are needed to run an exploration against a process whose reads come
from two sources.  The first is that an independent family indexed by a
disjoint union is the product of the two families it restricts to, so that a
process which reads the first family at some of its steps and the second at the
others is still reading ONE independent family, indexed by the union.  The
second is that a parameter which the reads depend on, such as the configuration
that decides which particles ever depart, can be fixed before the exploration
is defined: if the law of the reads is the same for every value of the
parameter, then it is that law after the parameter is integrated out.
-/
import LatticeProb.Prob.Coordinate

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

section Sum

variable {ι ι' : Type*} {X : ι ⊕ ι' → Type*} [∀ i, MeasurableSpace (X i)]

/-- **A product over a disjoint union is a product of products, in the direction
that builds the family.** -/
theorem infinitePi_sum_symm (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] :
    ((Measure.infinitePi fun i : ι => μ (Sum.inl i)).prod
        (Measure.infinitePi fun i : ι' => μ (Sum.inr i))).map
        (Equiv.sumPiEquivProdPi X).symm
      = Measure.infinitePi μ := by
  classical
  have hmeas : Measurable ⇑(Equiv.sumPiEquivProdPi X).symm :=
    (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
  refine Measure.eq_infinitePi μ fun s t ht => ?_
  have hpre : (Equiv.sumPiEquivProdPi X).symm ⁻¹' Set.pi (↑s) t
      = (Set.pi (↑s.toLeft) fun a => t (Sum.inl a))
        ×ˢ (Set.pi (↑s.toRight) fun b => t (Sum.inr b)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
      Finset.mem_toLeft, Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun a ha => h (Sum.inl a) ha, fun b hb => h (Sum.inr b) hb⟩
    · rintro ⟨h1, h2⟩ (a | b) hi
      · exact h1 a hi
      · exact h2 b hi
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i), hpre,
    Measure.prod_prod, Measure.infinitePi_pi _ (fun a _ => ht (Sum.inl a)),
    Measure.infinitePi_pi _ (fun b _ => ht (Sum.inr b)),
    ← Finset.toLeft_disjSum_toRight (u := s), Finset.prod_disjSum]
  simp

/-- **A product over a disjoint union is a product of products.**  The two
halves of an independent family indexed by `ι ⊕ ι'` are independent families
indexed by `ι` and by `ι'`, and jointly they are the product. -/
theorem infinitePi_sum (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.infinitePi μ).map
        (fun ω => ((fun i : ι => ω (Sum.inl i)), fun i : ι' => ω (Sum.inr i)))
      = (Measure.infinitePi fun i : ι => μ (Sum.inl i)).prod
          (Measure.infinitePi fun i : ι' => μ (Sum.inr i)) := by
  have hfwd : Measurable
      (fun ω : Π i, X i => ((fun i : ι => ω (Sum.inl i)), fun i : ι' => ω (Sum.inr i))) :=
    (MeasurableEquiv.sumPiEquivProdPi X).measurable
  have hbwd : Measurable ⇑(Equiv.sumPiEquivProdPi X).symm :=
    (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
  conv_lhs => rw [← infinitePi_sum_symm μ]
  rw [Measure.map_map hfwd hbwd,
    show (fun ω : Π i, X i => ((fun i : ι => ω (Sum.inl i)), fun i : ι' => ω (Sum.inr i)))
        ∘ ⇑(Equiv.sumPiEquivProdPi X).symm = id from by ext p i <;> rfl,
    Measure.map_id]

end Sum

section Fubini

variable {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]

/-- **A parameter that does not change the law may be integrated out.**  If the
law of `F y` is the same measure `Q` for every value `y` of the parameter, then
the law of `F` on the product is `Q`.  This is what lets a construction whose
dependency structure is defined only once the parameter is fixed be run under
the parameter's own randomness. -/
theorem map_prod_of_forall_map (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Measure β) [IsProbabilityMeasure R] {Q : Measure γ}
    {F : Ω → β → γ} (hF : Measurable (Function.uncurry F))
    (h : ∀ y, R.map (F y) = Q) :
    (P.prod R).map (fun p => F p.1 p.2) = Q := by
  have hF' : Measurable fun p : Ω × β => F p.1 p.2 := hF
  ext s hs
  rw [Measure.map_apply hF' hs, Measure.prod_apply (hF' hs)]
  have hslice : ∀ y : Ω, R (Prod.mk y ⁻¹' ((fun p : Ω × β => F p.1 p.2) ⁻¹' s)) = Q s := by
    intro y
    have hFy : Measurable (F y) := hF.comp measurable_prodMk_left
    have hy : Prod.mk y ⁻¹' ((fun p : Ω × β => F p.1 p.2) ⁻¹' s) = F y ⁻¹' s := rfl
    rw [hy, ← Measure.map_apply hFy hs, h y]
  simp [hslice]

/-- The pair form: the parameter is kept, and the second component has law `Q`
conditionally on it. -/
theorem map_prod_pair_of_forall_map (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Measure β) [IsProbabilityMeasure R] {Q : Measure γ}
    {F : Ω → β → γ} (hF : Measurable (Function.uncurry F))
    (h : ∀ y, R.map (F y) = Q) :
    (P.prod R).map (fun p => (p.1, F p.1 p.2)) = P.prod Q := by
  have hF' : Measurable fun p : Ω × β => F p.1 p.2 := hF
  haveI : IsProbabilityMeasure Q := by
    obtain ⟨y⟩ := nonempty_of_isProbabilityMeasure P
    rw [← h y]
    exact Measure.isProbabilityMeasure_map (hF.comp measurable_prodMk_left).aemeasurable
  have hmeas : Measurable fun p : Ω × β => (p.1, F p.1 p.2) := measurable_fst.prodMk hF'
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hmeas (hs.prod ht)]
  have hpre : (fun p : Ω × β => (p.1, F p.1 p.2)) ⁻¹' (s ×ˢ t)
      = Prod.fst ⁻¹' s ∩ (fun p : Ω × β => F p.1 p.2) ⁻¹' t := rfl
  rw [hpre, Measure.prod_apply ((measurable_fst hs).inter (hF' ht))]
  have hslice : ∀ y : Ω,
      R (Prod.mk y ⁻¹' (Prod.fst ⁻¹' s ∩ (fun p : Ω × β => F p.1 p.2) ⁻¹' t))
        = Set.indicator s (fun _ => Q t) y := by
    intro y
    have hFy : Measurable (F y) := hF.comp measurable_prodMk_left
    by_cases hy : y ∈ s
    · have he : Prod.mk y ⁻¹' (Prod.fst ⁻¹' s ∩ (fun p : Ω × β => F p.1 p.2) ⁻¹' t)
          = F y ⁻¹' t := by
        ext b; simp [hy]
      rw [he, ← Measure.map_apply hFy ht, h y, Set.indicator_of_mem hy]
    · have he : Prod.mk y ⁻¹' (Prod.fst ⁻¹' s ∩ (fun p : Ω × β => F p.1 p.2) ⁻¹' t)
          = ∅ := by
        ext b; simp [hy]
      rw [he, measure_empty, Set.indicator_of_notMem hy]
  simp only [hslice]
  rw [lintegral_indicator hs, setLIntegral_const, mul_comm]

end Fubini

end LatticeProb

end
