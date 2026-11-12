/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43CM at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.EventDefs
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# GM Lemma 5.4: the conditional Cameron–Martin comparison (task P2-M2N, WP-M2n)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.
Lemma 5.4 (`lem-E-frkE-compare`, l. 2792–2835) compares
`P[E_r ∩ {P ∩ B_{2r} ≠ ∅} | h|_{ℂ∖B_{3r}}]` with `Λ P[𝔈_r ∩ {P ∩ B_{2r} ≠ ∅} | h|_{ℂ∖B_{3r}}]`.
GM's proof: (5.6) the Radon–Nikodym derivative of the conditional law of `h − φ` w.r.t. that of
`h` is `M_h = exp(−(h,φ)_∇ − ½(φ,φ)_∇)`, which is `≤ Λ` on `𝔈_r` by (5.5); (5.7) the inclusion
`E_r ∩ {…} ⊂ 𝔈_r^φ ∩ {…}` (Prop 5.2 (B), (C)); combine.

Here the abstract core, for a sub-σ-algebra `m` whose events are shift invariant (every event of
`m` is `{pair0 h ∈ C}` for a measurable `C` invariant under `g ↦ g − φ`, `φ ∈ 𝓖`; this is the
case for the mean-zero pairings of `h` against test functions supported off `⋃ supp φ`), a random
`φ ∈ 𝓖` (`𝓖` finite) which is `m`-measurable, and the target event `{pair0 h ∈ C_T}`:

* `measure_subTest_le_cm` : `P[pair0 (h − φ) ∈ S] ≤ Λ P[pair0 h ∈ S]` if `M ≤ Λ` on `S`
  (unconditional Cameron–Martin `lawPair0_addFun_eq_withDensity`, task P2-FCM);
* `measure_inter_le_cm` : `P[B ∩ X] ≤ Λ P[B ∩ {pair0 h ∈ C_T}]` for `B ∈ m`, if a.s. on `X` the
  shifted field `h − φ` lies in `C_T` (GM (5.7)) — GM (5.6) with the random `φ` handled by the
  finite partition `{φ = φ_i}` (GM: "`φ` is determined by `h|_{ℂ∖B_{3r}}`");
* `condExp_le_cm` : the conditional form `Λ⁻¹ P[X | m] ≤ P[pair0 h ∈ C_T | m]` a.s. (= GM (5.4)).

The conditional law of GM is not used: integrating against events of `m` and the unconditional
Cameron–Martin formula suffice, since the events of `m` are unchanged by `h ↦ h − φ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric.GM

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

lemma testCont_neg_cm (φ : TestC) : testCont (-φ) = -testCont φ := by
  ext x; rfl

lemma subTest_eq_addFun_neg_cm (g : DistC) (φ : TestC) :
    subTest g φ = addFun g (testCont (-φ)) := by
  rw [subTest, testCont_neg_cm]

/-- GM (5.6), unconditional form: `P[pair0 (h − φ) ∈ S] ≤ Λ P[pair0 h ∈ S]` if the
Cameron–Martin density of `h − φ` is `≤ Λ` on `S`. -/
theorem measure_subTest_le_cm (hh : IsWholePlaneGFF h P) (φ : TestC)
    {S : Set (TestC0 → ℝ)} (hS : MeasurableSet S) {Λ : ℝ}
    (hΛ : ∀ ξ ∈ S, cmDensity (-φ) ξ ≤ Λ) :
    P {ω | pair0 (subTest (h ω) φ) ∈ S} ≤ ENNReal.ofReal Λ * P {ω | pair0 (h ω) ∈ S} := by
  have e1 : {ω | pair0 (subTest (h ω) φ) ∈ S} =
      (fun ω => pair0 (addFun (h ω) (testCont (-φ)))) ⁻¹' S := by
    ext ω; simp only [mem_setOf_eq, mem_preimage, subTest_eq_addFun_neg_cm]
  have e2 : {ω | pair0 (h ω) ∈ S} = (fun ω => pair0 (h ω)) ⁻¹' S := rfl
  rw [e1, e2, ← Measure.map_apply (measurable_pair0_addFun hh (-φ)) hS,
    ← Measure.map_apply (measurable_pair0_comp hh) hS]
  change lawPair0 (fun ω => addFun (h ω) (testCont (-φ))) P S ≤
    ENNReal.ofReal Λ * lawPair0 h P S
  rw [lawPair0_addFun_eq_withDensity hh, withDensity_apply _ hS]
  calc ∫⁻ ξ in S, ENNReal.ofReal (cmDensity (-φ) ξ) ∂(lawPair0 h P)
      ≤ ∫⁻ _ in S, ENNReal.ofReal Λ ∂(lawPair0 h P) :=
        setLIntegral_mono measurable_const fun ξ hξ => ENNReal.ofReal_le_ofReal (hΛ ξ hξ)
    _ = ENNReal.ofReal Λ * lawPair0 h P S := by
        rw [setLIntegral_const]

/-- GM (5.6)–(5.7) integrated over an event `B`: if `B ∩ {φc = φ} = {pair0 h ∈ C φ}` with
`C φ` invariant under `g ↦ g − φ`, the random `φc` takes values in the finite set `G`, a.s. on `X`
the field `h − φc` lies in `C_T`, and the density of `h − φ` is `≤ Λ` on `C_T`, then
`P[B ∩ X] ≤ Λ P[B ∩ {pair0 h ∈ C_T}]`. -/
theorem measure_inter_le_cm (hh : IsWholePlaneGFF h P) (G : Finset TestC) (φc : Ω → TestC)
    (hφcG : ∀ ω, φc ω ∈ G) (B : Set Ω) (C : TestC → Set (TestC0 → ℝ))
    (hC : ∀ φ ∈ G, MeasurableSet (C φ) ∧ B ∩ {ω | φc ω = φ} = (fun ω => pair0 (h ω)) ⁻¹' C φ ∧
      ∀ g : DistC, (pair0 (subTest g φ) ∈ C φ ↔ pair0 g ∈ C φ))
    {CT : Set (TestC0 → ℝ)} (hCT : MeasurableSet CT) {Λ : ℝ}
    (hΛ : ∀ φ ∈ G, ∀ ξ ∈ CT, cmDensity (-φ) ξ ≤ Λ) (X : Set Ω)
    (hX : ∀ᵐ ω ∂P, ω ∈ X → pair0 (subTest (h ω) (φc ω)) ∈ CT) :
    P (B ∩ X) ≤ ENNReal.ofReal Λ * P (B ∩ {ω | pair0 (h ω) ∈ CT}) := by
  have hp := measurable_pair0_comp hh
  -- the a.e. covering of `B ∩ X` by the shifted events
  have hcov : B ∩ X ≤ᵐ[P] (⋃ φ ∈ G, {ω | pair0 (subTest (h ω) φ) ∈ C φ ∩ CT} : Set Ω) := by
    filter_upwards [hX] with ω hω hmem
    obtain ⟨hB, hXω⟩ := hmem
    have hG := hφcG ω
    obtain ⟨-, hBe, hinv⟩ := hC (φc ω) hG
    have h1 : ω ∈ (fun ω => pair0 (h ω)) ⁻¹' C (φc ω) := by
      rw [← hBe]; exact ⟨hB, rfl⟩
    exact mem_biUnion hG ⟨(hinv (h ω)).2 h1, hω hXω⟩
  -- the partition of `B ∩ {pair0 h ∈ C_T}` by the value of `φc`
  have hpart : B ∩ {ω | pair0 (h ω) ∈ CT} =
      ⋃ φ ∈ G, (fun ω => pair0 (h ω)) ⁻¹' (C φ ∩ CT) := by
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion, mem_preimage, exists_prop]
    constructor
    · rintro ⟨hB, hT⟩
      refine ⟨φc ω, hφcG ω, ?_, hT⟩
      have : ω ∈ B ∩ {ω' | φc ω' = φc ω} := ⟨hB, rfl⟩
      rw [(hC (φc ω) (hφcG ω)).2.1] at this
      exact this
    · rintro ⟨φ, hφ, hCφ, hT⟩
      have : ω ∈ (fun ω => pair0 (h ω)) ⁻¹' C φ := hCφ
      rw [← (hC φ hφ).2.1] at this
      exact ⟨this.1, hT⟩
  have hdisj : (G : Set TestC).PairwiseDisjoint
      fun φ => (fun ω => pair0 (h ω)) ⁻¹' (C φ ∩ CT) := by
    intro φ hφ ψ hψ hne
    refine Set.disjoint_left.2 fun ω h1 h2 => hne ?_
    have a1 : ω ∈ (fun ω => pair0 (h ω)) ⁻¹' C φ := h1.1
    have a2 : ω ∈ (fun ω => pair0 (h ω)) ⁻¹' C ψ := h2.1
    rw [← (hC φ hφ).2.1] at a1
    rw [← (hC ψ hψ).2.1] at a2
    exact a1.2.symm.trans a2.2
  calc P (B ∩ X)
      ≤ P (⋃ φ ∈ G, {ω | pair0 (subTest (h ω) φ) ∈ C φ ∩ CT}) := measure_mono_ae hcov
    _ ≤ ∑ φ ∈ G, P {ω | pair0 (subTest (h ω) φ) ∈ C φ ∩ CT} := measure_biUnion_finset_le _ _
    _ ≤ ∑ φ ∈ G, ENNReal.ofReal Λ * P {ω | pair0 (h ω) ∈ C φ ∩ CT} := by
        refine Finset.sum_le_sum fun φ hφ => ?_
        exact measure_subTest_le_cm hh φ ((hC φ hφ).1.inter hCT)
          fun ξ hξ => hΛ φ hφ ξ hξ.2
    _ = ENNReal.ofReal Λ * P (B ∩ {ω | pair0 (h ω) ∈ CT}) := by
        rw [← Finset.mul_sum, hpart, measure_biUnion_finset hdisj
          fun φ _ => hp ((hC φ ‹_›).1.inter hCT)]
        rfl

/-- **GM Lemma 5.4, abstract form** (l. 2792–2835): with a sub-σ-algebra `m` whose events are of
the form `{pair0 h ∈ C}` with `C` invariant under `g ↦ g − φ` for `φ ∈ G`, an `m`-measurable
random `φc ∈ G` (`G` finite), the inclusion (5.7) a.s. on `X` and the Radon–Nikodym bound
`M ≤ Λ` on the target `C_T` ((5.5)), a.s. `Λ⁻¹ P[X | m] ≤ P[{pair0 h ∈ C_T} | m]`. -/
theorem condExp_le_cm (hh : IsWholePlaneGFF h P) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (G : Finset TestC) (φc : Ω → TestC) (hφcG : ∀ ω, φc ω ∈ G)
    (hφcm : ∀ φ ∈ G, MeasurableSet[m] {ω | φc ω = φ})
    (hinv : ∀ B, MeasurableSet[m] B → ∃ C : Set (TestC0 → ℝ), MeasurableSet C ∧
      B = (fun ω => pair0 (h ω)) ⁻¹' C ∧ ∀ φ ∈ G, ∀ g : DistC,
        (pair0 (subTest g φ) ∈ C ↔ pair0 g ∈ C))
    {CT : Set (TestC0 → ℝ)} (hCT : MeasurableSet CT) {Λ : ℝ} (hΛ0 : 0 < Λ)
    (hΛ : ∀ φ ∈ G, ∀ ξ ∈ CT, cmDensity (-φ) ξ ≤ Λ) {X : Set Ω} (hXm : MeasurableSet[mΩ] X)
    (hX : ∀ᵐ ω ∂P, ω ∈ X → pair0 (subTest (h ω) (φc ω)) ∈ CT) :
    (fun ω => Λ⁻¹ * (P[X.indicator (fun _ => (1 : ℝ)) | m]) ω) ≤ᵐ[P]
      P[{ω | pair0 (h ω) ∈ CT}.indicator (fun _ => (1 : ℝ)) | m] := by
  have hp := @measurable_pair0_comp Ω mΩ P h hh
  set T : Set Ω := {ω | pair0 (h ω) ∈ CT}
  have hTm : MeasurableSet[mΩ] T := hp hCT
  have hiX : Integrable (X.indicator fun _ => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hXm
  have hiT : Integrable (T.indicator fun _ => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hTm
  -- the measure inequality on events of `m`
  have key : ∀ s, MeasurableSet[m] s → P.real (s ∩ X) ≤ Λ * P.real (s ∩ T) := by
    intro s hs
    have hC : ∀ φ ∈ G, ∃ C : Set (TestC0 → ℝ), MeasurableSet C ∧
        s ∩ {ω | φc ω = φ} = (fun ω => pair0 (h ω)) ⁻¹' C ∧
        ∀ g : DistC, (pair0 (subTest g φ) ∈ C ↔ pair0 g ∈ C) := by
      intro φ hφ
      obtain ⟨C, hCm, hCe, hCi⟩ := hinv _ (hs.inter (hφcm φ hφ))
      exact ⟨C, hCm, hCe, hCi φ hφ⟩
    choose! C hC using hC
    have h1 := measure_inter_le_cm (mΩ := mΩ) hh G φc hφcG s C hC hCT hΛ X hX
    have hfin : ENNReal.ofReal Λ * P (s ∩ T) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    have h2 := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hΛ0.le] at h2
  have hsm1 : StronglyMeasurable[m] fun ω => Λ⁻¹ * (P[X.indicator (fun _ => (1 : ℝ)) | m]) ω :=
    stronglyMeasurable_condExp.const_mul _
  have hsm2 : StronglyMeasurable[m] (P[T.indicator (fun _ => (1 : ℝ)) | m]) :=
    stronglyMeasurable_condExp
  have hint1 : Integrable (fun ω => Λ⁻¹ * (P[X.indicator (fun _ => (1 : ℝ)) | m]) ω) P :=
    integrable_condExp.const_mul _
  refine ae_of_ae_trim hm (ae_le_of_forall_setIntegral_le (hint1.trim hm hsm1)
    (integrable_condExp.trim hm hsm2) fun s hs _ => ?_)
  rw [← setIntegral_trim hm hsm1 hs, ← setIntegral_trim hm hsm2 hs, integral_const_mul,
    setIntegral_condExp hm hiX hs, setIntegral_condExp hm hiT hs,
    setIntegral_indicator hXm, setIntegral_indicator hTm, setIntegral_const, setIntegral_const,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  have := key s hs
  rw [inv_mul_le_iff₀ hΛ0]
  exact this

end LQGMetric.GM
