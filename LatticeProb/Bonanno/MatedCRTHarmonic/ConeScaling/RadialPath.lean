/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeScaling.RadialPath at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.RadialLaw

/-!
# A measurable continuous version of the cone's radial path, independent of the GFF

For the cell model's cone data (`CellScaling.ConeRealization`: a whole-plane GFF `X`, Brownian motions
`B, B'` with `X ⊥ (B, B')`), the radial path `t ↦ coneRadial γ γ B B' t` (DMS Def 4.10,
Rem 4.4) involves the last zero of `B'_u + (Q − γ)u`, which is not a measurable functional of the path
for the product σ-algebra. Here we build (`exists_radialPath`) a **measurable** `C(ℝ, ℝ)`-valued
`W` with `W = coneRadial γ γ B B'` almost surely and `X ⊥ W`, by passing to continuous versions
`Bc, Bc' : Ω → C(ℝ≥0, ℝ)` (QuantumZipper's `WedgeRes.exists_good_version`) on which the last zero is
measurable (QuantumZipper's `WedgeMeas.measurable_lastZero`). Consequence: the independence of `X`
and the MoT cone process thattheorems take as a hypothesis (`indepFun_motConeRadial`).
Own measure-theoretic glue.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace MatedCRTHarmonic.ConeScaling

open MatedCRTHarmonic.CellScaling

/-! ### Continuity of the cone radial path -/

/-- The cone radial path is continuous as soon as `b, b'` are continuous, vanish at `0`, and the
zero set of the drifted path `c = coneDrift γ α b'` is bounded above. -/
theorem continuous_coneRadial_of {γ α : ℝ} {b b' : ℝ≥0 → ℝ} (hb : Continuous b) (hb0 : b 0 = 0)
    (hb' : Continuous b') (hb'0 : b' 0 = 0)
    (hbdd : BddAbove {s : ℝ | 0 ≤ s ∧ coneDrift γ α b' s = 0}) :
    Continuous (coneRadial γ α b b') := by
  set c := coneDrift γ α b' with hc
  have hcc : Continuous c :=
    (hb'.comp continuous_real_toNNReal).add (continuous_const.mul continuous_id)
  have hmem : lastZeroR c ∈ {s : ℝ | 0 ≤ s ∧ c s = 0} := by
    refine IsClosed.csSup_mem (isClosed_Ici.inter (isClosed_eq hcc continuous_const))
      ⟨0, le_refl _, by simp [hc, coneDrift, hb'0]⟩ hbdd
  have e : coneRadial γ α b b' = fun t =>
      if (0 : ℝ) ≤ t then b t.toNNReal + α * t else c (lastZeroR c - t) + lqgQ γ * t := by
    funext t; rfl
  rw [e]
  refine Continuous.if_le ((hb.comp continuous_real_toNNReal).add (continuous_const.mul
    continuous_id)) ((hcc.comp (continuous_const.sub continuous_id)).add
      (continuous_const.mul continuous_id)) continuous_const continuous_id fun t ht => ?_
  subst ht
  simp [hb0, hmem.2]

/-! ### The good set and the radial map on continuous path pairs -/

/-- The drifted path of a continuous path, as a function of the path. -/
lemma measurable_coneDrift_apply (γ α s : ℝ) :
    Measurable fun b' : C(ℝ≥0, ℝ) => coneDrift γ α b' s :=
  (ContinuousMap.measurable_eval _).add_const _

lemma continuous_coneDrift (γ α : ℝ) (b' : C(ℝ≥0, ℝ)) : Continuous (coneDrift γ α b') :=
  (b'.continuous.comp continuous_real_toNNReal).add (continuous_const.mul continuous_id)

/-- Pairs of continuous paths on which the cone radial path is continuous. -/
def radGood (γ α : ℝ) : Set (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) :=
  {p | p.1 0 = 0 ∧ p.2 0 = 0 ∧ BddAbove {s : ℝ | 0 ≤ s ∧ coneDrift γ α p.2 s = 0}}

theorem measurableSet_radGood (γ α : ℝ) : MeasurableSet (radGood γ α) := by
  have h1 : MeasurableSet {p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) | p.1 0 = 0} :=
    measurableSet_eq_fun ((ContinuousMap.measurable_eval 0).comp measurable_fst) measurable_const
  have h2 : MeasurableSet {p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) | p.2 0 = 0} :=
    measurableSet_eq_fun ((ContinuousMap.measurable_eval 0).comp measurable_snd) measurable_const
  have h3 : MeasurableSet {p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) |
      BddAbove {s : ℝ | 0 ≤ s ∧ coneDrift γ α p.2 s = 0}} := by
    simp_rw [QuantumZipper.WedgeMeas.bddAbove_zeros_iff]
    exact measurableSet_setOfPred.2 (Measurable.exists fun N => Measurable.forall fun n =>
      (QuantumZipper.WedgeMeas.measurable_zeroIn
        (f := fun (p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) s => coneDrift γ α p.2 s)
        (fun p => continuous_coneDrift γ α p.2)
        (fun s => (measurable_coneDrift_apply γ α s).comp measurable_snd)
        (by linarith)).not)
  exact h1.inter (h2.inter h3)

theorem continuous_coneRadial_of_mem {γ α : ℝ} {p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)}
    (hp : p ∈ radGood γ α) : Continuous (coneRadial γ α p.1 p.2) :=
  continuous_coneRadial_of p.1.continuous hp.1 p.2.continuous hp.2.1 hp.2.2

/-- Each value of the cone radial path is a measurable function of the pair of continuous paths. -/
theorem measurable_coneRadial_apply (γ α t : ℝ) :
    Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => coneRadial γ α p.1 p.2 t := by
  by_cases ht : 0 ≤ t
  · have e : (fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => coneRadial γ α p.1 p.2 t) =
        fun p => p.1 t.toNNReal + α * t := by
      funext p; simp only [coneRadial, ite_eq_left ht]
    rw [e]
    exact ((ContinuousMap.measurable_eval _).comp measurable_fst).add_const _
  · have hL : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => lastZeroR (coneDrift γ α p.2) :=
      QuantumZipper.WedgeMeas.measurable_lastZero
        (f := fun (p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) s => coneDrift γ α p.2 s)
        (fun p => continuous_coneDrift γ α p.2)
        (fun s => (measurable_coneDrift_apply γ α s).comp measurable_snd)
    have e : (fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => coneRadial γ α p.1 p.2 t) =
        fun p => p.2 (lastZeroR (coneDrift γ α p.2) - t).toNNReal +
          (lqgQ γ - α) * (lastZeroR (coneDrift γ α p.2) - t) + lqgQ γ * t := by
      funext p; simp only [coneRadial, ite_eq_right ht]; rfl
    rw [e]
    have hev : Measurable fun q : C(ℝ≥0, ℝ) × ℝ≥0 => q.1 q.2 := continuous_eval.measurable
    have hτ : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
        (lastZeroR (coneDrift γ α p.2) - t).toNNReal :=
      measurable_real_toNNReal.comp (hL.sub_const t)
    exact ((hev.comp (measurable_snd.prodMk hτ)).add ((hL.sub_const t).const_mul _)).add_const _

open Classical in
/-- The radial map on pairs of continuous paths (junk `0` off the good set). -/
def radMap (γ α : ℝ) (p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) : C(ℝ, ℝ) :=
  if hp : p ∈ radGood γ α then ⟨coneRadial γ α p.1 p.2, continuous_coneRadial_of_mem hp⟩ else 0

open Classical in
lemma radMap_apply (γ α : ℝ) (p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) (t : ℝ) :
    radMap γ α p t = if p ∈ radGood γ α then coneRadial γ α p.1 p.2 t else 0 := by
  unfold radMap
  split_ifs <;> rfl

theorem measurable_radMap (γ α : ℝ) : Measurable (radMap γ α) := by
  classical
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  simp_rw [radMap_apply]
  exact Measurable.ite (measurableSet_radGood γ α) (measurable_coneRadial_apply γ α t)
    measurable_const

/-! ### Independence through continuous versions -/

/-- Independence from a pair of continuous paths is independence from their underlying functions. -/
theorem indepFun_pair_continuousMap_of_coe {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} {f : Ω → β} {U V : Ω → C(ℝ≥0, ℝ)}
    (h : IndepFun f (fun ω => ((⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ))) P) :
    IndepFun f (fun ω => (U ω, V ω)) P := by
  have hc : Measurable fun f : C(ℝ≥0, ℝ) => (⇑f : ℝ≥0 → ℝ) :=
    measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval t
  have hσ : MeasurableSpace.comap (fun ω => (U ω, V ω))
        (inferInstance : MeasurableSpace (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) =
      MeasurableSpace.comap (fun ω => ((⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ)))
        (inferInstance : MeasurableSpace ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ))) := by
    apply le_antisymm
    · rw [← measurable_iff_comap_le]
      let _ : MeasurableSpace Ω := MeasurableSpace.comap
        (fun ω => ((⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ))) inferInstance
      have hm : Measurable fun ω => ((⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ)) :=
        comap_measurable _
      exact (ContinuousMap.measurable_iff_eval.2 fun t =>
          (measurable_pi_apply t).comp (measurable_fst.comp hm)).prodMk
        (ContinuousMap.measurable_iff_eval.2 fun t =>
          (measurable_pi_apply t).comp (measurable_snd.comp hm))
    · rw [← measurable_iff_comap_le]
      let _ : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => (U ω, V ω)) inferInstance
      have hm : Measurable fun ω => (U ω, V ω) := comap_measurable _
      exact ((hc.comp measurable_fst).prodMk (hc.comp measurable_snd)).comp hm
  unfold IndepFun Kernel.IndepFun at h ⊢
  rw [hσ]
  exact h

/-- A continuous measurable version of a Brownian motion (QuantumZipper's good version). -/
theorem exists_continuousMap_version {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ Bc : Ω → C(ℝ≥0, ℝ), Measurable Bc ∧ ∀ᵐ ω ∂P, ∀ t, Bc ω t = B t ω := by
  obtain ⟨B₀, hB₀m, hB₀c, hB₀⟩ := QuantumZipper.WedgeRes.exists_good_version hB
  exact ⟨fun ω => ⟨fun t => B₀ t ω, hB₀c ω⟩,
    ContinuousMap.measurable_iff_eval.2 fun t => hB₀m.of_uncurry_left, hB₀⟩

/-- **The radial path as an independent measurable continuous version**:
there is a measurable `W : Ω → C(ℝ, ℝ)` with `W = coneRadial γ γ B B'` a.s. and `X ⊥ W`. -/
theorem exists_radialPath {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {X : Ω → β} {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P) :
    ∃ W : Ω → C(ℝ, ℝ), Measurable W ∧ IndepFun X W P ∧
      ∀ᵐ ω ∂P, ∀ t, W ω t = coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t := by
  obtain ⟨Bc, hBcm, hBc⟩ := exists_continuousMap_version hB
  obtain ⟨Bc', hBc'm, hBc'⟩ := exists_continuousMap_version hB'
  have hpath : (fun ω => ((fun t => B t ω), (fun t => B' t ω))) =ᵐ[P]
      fun ω => ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ)) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hindC : IndepFun X (fun ω => (Bc ω, Bc' ω)) P :=
    indepFun_pair_continuousMap_of_coe (hind.congr (ae_eq_refl _) hpath)
  refine ⟨fun ω => radMap γ γ (Bc ω, Bc' ω), (measurable_radMap γ γ).comp (hBcm.prodMk hBc'm),
    hindC.comp measurable_id (measurable_radMap γ γ), ?_⟩
  filter_upwards [hBc, hBc', hB.eval_zero_ae_eq_zero, hB'.eval_zero_ae_eq_zero,
    ae_goodDrift hB' (lqgQ_sub_pos hγ hγ2)] with ω h1 h2 h3 h4 hdrift t
  have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B s ω := funext h1
  have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B' s ω := funext h2
  have hmem : (Bc ω, Bc' ω) ∈ radGood γ γ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]; exact h3
    · rw [h2]; exact h4
    · show BddAbove {s : ℝ | 0 ≤ s ∧ coneDrift γ γ (⇑(Bc' ω)) s = 0}
      rw [e2]; exact hdrift.bddAbove_zeroSet
  rw [radMap_apply, ite_eq_left hmem]
  simp only [e1, e2]

/-- **Independence of the GFF and the MoT cone process** (the hypothesis `hXA`
theorems), from the independence of `X` and the Brownian pair. -/
theorem indepFun_motConeRadial {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {X : Ω → β} {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P) :
    IndepFun X (fun ω t =>
      LQGCone.motConeRadial γ γ (fun s => B s ω) (fun s => B' s ω) t) P := by
  obtain ⟨W, hWm, hXW, hW⟩ := exists_radialPath hγ hγ2 hB hB' hind
  let G : C(ℝ, ℝ) → (ℝ → ℝ) := fun w t => w t - lqgQ γ * t
  have hG : Measurable G :=
    measurable_pi_iff.2 fun t => (ContinuousMap.measurable_eval t).sub_const _
  refine (hXW.comp measurable_id hG).congr (ae_eq_refl _) ?_
  filter_upwards [hW] with ω hω
  funext t
  simp only [Function.comp_apply, G, hω, LQGCone.motConeRadial]

end MatedCRTHarmonic.ConeScaling
