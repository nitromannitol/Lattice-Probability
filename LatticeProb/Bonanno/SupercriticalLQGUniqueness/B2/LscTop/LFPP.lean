/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.LscTop.LFPP at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.LscTop.Limits
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.RescaledLFPP
import LatticeProb.Bonanno.LQGMetric.LFPP.ContMetric

 
























set_option autoImplicit false

noncomputable section

open Set Filter Topology TopologicalSpace MeasureTheory
open scoped ENNReal
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase

namespace SupercriticalLQGUniqueness.B2.LscTop

 

 
def ofContinuousMap (g : C(ℂ × ℂ, EReal)) : LSCFun :=
  ⟨g, g.continuous.lowerSemicontinuous⟩

 


theorem lfppDistance_eq_lfppD (ξ : ℝ) (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    lfppDistance ξ φ p = LQGMetric.LFPP.lfppD ξ φ p.1 p.2 :=
  le_antisymm (le_iInf fun P => iInf₂_le_of_le P.1 P.2.1 le_rfl)
    (le_iInf₂ fun P hP => iInf_le_of_le ⟨P, hP, fun _ _ => mem_univ _⟩ le_rfl)

 
theorem lfppDistance_ne_top (ξ : ℝ) (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) : lfppDistance ξ φ p ≠ ∞ := by
  rw [lfppDistance_eq_lfppD]
  exact LQGMetric.LFPP.lfppD_ne_top φ.continuous _ _

 
theorem continuous_lfppDistance (ξ : ℝ) (φ : C(ℂ, ℝ)) : Continuous (lfppDistance ξ φ) := by
  have h : lfppDistance ξ φ = fun p => ENNReal.ofReal (LQGMetric.LFPP.lfppDReal ξ φ p) := by
    funext p
    rw [LQGMetric.LFPP.lfppDReal, ← lfppDistance_eq_lfppD,
      ENNReal.ofReal_toReal (lfppDistance_ne_top ξ φ p)]
  rw [h]
  exact ENNReal.continuous_ofReal.comp (LQGMetric.LFPP.continuous_lfppDReal φ.continuous)

 
theorem continuous_rescaledLFPP (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    Continuous (rescaledLFPP ξ a φ) :=
  continuous_coe_ennreal_ereal.comp
    ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp (continuous_lfppDistance ξ φ))

 
def rescaledLFPPMap (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) : C(ℂ × ℂ, EReal) :=
  ⟨rescaledLFPP ξ a φ, continuous_rescaledLFPP ξ a φ⟩

 
def rescaledLFPPFun (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) : LSCFun :=
  ofContinuousMap (rescaledLFPPMap ξ a φ)

@[simp] theorem rescaledLFPPFun_val (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    (rescaledLFPPFun ξ a φ).1 = rescaledLFPP ξ a φ := rfl

 

variable {Ω : Type*} [MeasurableSpace Ω]

 

theorem measurable_of_continuous_apply [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {G : Ω → LSCFun} (hc : ∀ ω, Continuous (G ω).1)
    (hm : ∀ q, Measurable fun ω => (G ω).1 q) : Measurable G := by
  obtain ⟨B, S, -, -, hB, hSk, -, heq⟩ := exists_tests_eq_generateFrom
  have hborel : ‹MeasurableSpace LSCFun› = MeasurableSpace.generateFrom (Tests B S) := by
    rw [BorelSpace.measurable_eq (α := LSCFun)]
    exact borel_eq_generateFrom_of_subbasis heq
  rw [hborel]
  refine measurable_generateFrom ?_
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (ℂ × ℂ)
  rintro s (⟨⟨⟨U, hU⟩, r⟩, rfl⟩ | ⟨⟨⟨K, hK⟩, r⟩, rfl⟩)
  · have e : G ⁻¹' Hit U r = ⋃ q ∈ U ∩ D, {ω | (G ω).1 q < ((r : ℝ) : EReal)} := by
      ext ω
      simp only [mem_preimage, Hit, mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
      constructor
      · rintro ⟨q, hqU, hq⟩
        obtain ⟨x, hxD, hx⟩ := hDd.exists_mem_open
          ((hB.isOpen hU).inter ((hc ω).isOpen_preimage _ isOpen_Iio)) ⟨q, hqU, hq⟩
        exact ⟨x, ⟨hx.1, hxD⟩, hx.2⟩
      · rintro ⟨q, ⟨hqU, -⟩, hq⟩
        exact ⟨q, hqU, hq⟩
    rw [e]
    exact MeasurableSet.biUnion (hDc.mono inter_subset_right) fun q _ =>
      measurableSet_lt (hm q) measurable_const
  · obtain ⟨c, hcK, hcc, hKc⟩ := (IsSeparable.of_separableSpace K).exists_countable_dense_subset
    have e : G ⁻¹' Miss K r = ⋃ r' : ℚ, ⋃ (_ : r < r'),
        ⋂ q ∈ c, {ω | ((r' : ℝ) : EReal) ≤ (G ω).1 q} := by
      ext ω
      simp only [mem_preimage, Miss, mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
      constructor
      · intro h
        rcases K.eq_empty_or_nonempty with hKe | hne
        · refine ⟨r + 1, by linarith, fun q hq => ?_⟩
          exact absurd (hcK hq) (by rw [hKe]; exact notMem_empty q)
        obtain ⟨x₀, hx₀, hmin⟩ := (hSk K hK).exists_isMinOn hne (hc ω).continuousOn
        obtain ⟨r', h1, h2⟩ := EReal.exists_rat_btwn_of_lt (h x₀ hx₀)
        exact ⟨r', by exact_mod_cast h1, fun q hq => h2.le.trans (hmin (hcK hq))⟩
      · rintro ⟨r', hr', h⟩ q hq
        have hcl : IsClosed {x | ((r' : ℝ) : EReal) ≤ (G ω).1 x} :=
          isClosed_le continuous_const (hc ω)
        have hq' : q ∈ {x | ((r' : ℝ) : EReal) ≤ (G ω).1 x} :=
          hcl.closure_subset_iff.2 (fun x hx => h x hx) (hKc hq)
        exact lt_of_lt_of_le (by exact_mod_cast hr') hq'
    rw [e]
    exact MeasurableSet.iUnion fun r' => MeasurableSet.iUnion fun _ =>
      MeasurableSet.biInter hcc fun q _ => measurableSet_le measurable_const (hm q)

 
theorem measurable_segCost_comp {X : Ω → C(ℂ, ℝ)} (hX : ∀ z, Measurable fun ω => X ω z)
    (ξ : ℝ) (a b : ℂ) : Measurable fun ω => LQGMetric.LFPP.segCost ξ (X ω) a b := by
  have hseg : Continuous (LQGMetric.LFPP.segPath a b) := by
    unfold LQGMetric.LFPP.segPath
    fun_prop
  have hu : Measurable (Function.uncurry fun (z : ℂ) (ω : Ω) => X ω z) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => (X ω).continuous) hX
  have h2 : Measurable fun p : Ω × ℝ => X p.1 (LQGMetric.LFPP.segPath a b p.2) :=
    hu.comp ((hseg.measurable.comp measurable_snd).prodMk measurable_fst)
  have h3 : Measurable fun p : Ω × ℝ => ‖deriv (LQGMetric.LFPP.segPath a b) p.2‖ :=
    (measurable_deriv _).norm.comp measurable_snd
  have hj : Measurable fun p : Ω × ℝ => ENNReal.ofReal
      (Real.exp (ξ * X p.1 (LQGMetric.LFPP.segPath a b p.2)) *
        ‖deriv (LQGMetric.LFPP.segPath a b) p.2‖) :=
    ((h2.const_mul ξ).exp.mul h3).ennreal_ofReal
  show Measurable fun ω => ∫⁻ t in Icc (0 : ℝ) 1,
    ENNReal.ofReal (Real.exp (ξ * X ω (LQGMetric.LFPP.segPath a b t)) *
      ‖deriv (LQGMetric.LFPP.segPath a b) t‖)
  exact Measurable.lintegral_prod_right' (ν := volume.restrict (Icc (0 : ℝ) 1)) hj

 
theorem measurable_lfppDistance_comp {X : Ω → C(ℂ, ℝ)} (hX : ∀ z, Measurable fun ω => X ω z)
    (ξ : ℝ) (p : ℂ × ℂ) : Measurable fun ω => lfppDistance ξ (X ω) p := by
  have h : ∀ ω, lfppDistance ξ (X ω) p = ⨅ (N : ℕ) (q : Fin N → LQGMetric.LFPP.gaussRat),
      LQGMetric.LFPP.chainCost ξ (X ω) p.1 p.2 N q := fun ω => by
    rw [lfppDistance_eq_lfppD]
    exact LQGMetric.LFPP.lfppDOn_eq_iInf_chain (X ω).continuous convex_univ (subset_univ _)
      (fun x _ ρ hρ => LQGMetric.LFPP.gaussRat_dense x hρ) (mem_univ _) (mem_univ _)
  simp_rw [h]
  have := LQGMetric.LFPP.gaussRat_countable.to_subtype
  exact Measurable.iInf fun N => Measurable.iInf fun q =>
    Finset.measurable_sum _ fun i _ => measurable_segCost_comp hX ξ _ _

 

theorem measurable_rescaledLFPPFun_comp [MeasurableSpace LSCFun] [BorelSpace LSCFun] (ξ : ℝ)
    (a : Set.Ioi (0 : ℝ)) {X : Ω → C(ℂ, ℝ)} (hX : ∀ z, Measurable fun ω => X ω z) :
    Measurable fun ω => rescaledLFPPFun ξ a (X ω) :=
  measurable_of_continuous_apply (fun ω => continuous_rescaledLFPP ξ a (X ω)) fun q =>
    continuous_coe_ennreal_ereal.measurable.comp
      ((measurable_lfppDistance_comp hX ξ q).const_mul _)

 

end SupercriticalLQGUniqueness.B2.LscTop
