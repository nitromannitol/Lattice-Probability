/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.Markov at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.Reversal
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.StrongMarkov
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation

/-!
# W1: Markov wrappers for Brownian motion with drift

Node W1 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1), a step of the proof of L14
(`WilliamsDriftDecomposition`, `Proofs/LQG/WedgeTranslation.lean`).

For `Y = dpath σ μ b`: `t ↦ σ b_t + μ t`, a Brownian motion with drift `μ`, started at `0`, with
continuous paths:

* `markov_fixed` (blueprint, verbatim): the simple Markov property at a deterministic time `l`,
  in the integrated form
  `E[A(Y_{·∧l}) · G(Y_l)(Y_{l+·} - Y_l)] = E[A(Y_{·∧l}) · E[G(Y_l)(Y)]]` for measurable
  `A : (ℝ≥0 → ℝ) → ℝ≥0∞` and `G : ℝ → (ℝ≥0 → ℝ) → ℝ≥0∞`.

The route is the blueprint's: the simple Markov property at fixed times is
`IsPreBrownianReal.indepFun_shift` (mathlib: the future increment `b(l+·) - b l` is independent of
the past of `b` up to `l`), which transfers to `Y` because the future of `Y` is a deterministic
function of the future of `b`; the law of the restarted drift path is that of `dpath σ μ b` itself
(`map_smShift_dpath`, from `GermZeroOne.map_path_eq_of_isPreBrownianReal` + the structure of the
drift path). `lintegral_pair_eq` is the abstract factorization of an integral of a measurable
function of an independent pair, and `lintegral_mul_comp_pair` is its weighted form (used again
in W3/W4/W5, where a functional of the past multiplies a functional of the future).

Sources: Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. III §3 (Markov
property); Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*, GTM 274, Thm 2.20
(strong Markov property at a hitting time). The factorization lemmas are own elementary proofs
(Tonelli plus independence; no source states them in this form).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ}

/-! ## Measurability of the drift path, and the past filtration of `b` -/

theorem measurable_dpath (hb : GoodBM b P) (σ μ : ℝ) (t : ℝ≥0) :
    Measurable fun ω => dpath σ μ b ω t := by
  simp only [dpath]
  exact ((hb.meas t).const_mul σ).add_const (μ * (t : ℝ))

theorem measurable_dpath_path (hb : GoodBM b P) (σ μ : ℝ) :
    Measurable fun ω => (fun t : ℝ≥0 => dpath σ μ b ω t) :=
  measurable_pi_iff.2 (measurable_dpath hb σ μ)

/-- The past σ-algebra of `b` up to time `t` (the natural filtration of `b`). -/
def pastFilt (b : ℝ≥0 → Ω → ℝ) (hbm : ∀ t, Measurable (b t)) : Filtration ℝ≥0 mΩ where
  seq t := MeasurableSpace.comap (fun ω (r : Set.Iic t) => b r ω) MeasurableSpace.pi
  mono' s t hst := by
    refine Measurable.comap_le (WedgeTrans.meas_pi_of _ _ fun r => ?_)
    exact WedgeTrans.meas_comap_eval (fun ω (r : Set.Iic t) => b r ω)
      ⟨r.1, Set.mem_Iic.2 ((Set.mem_Iic.1 r.2).trans hst)⟩
  le' t := Measurable.comap_le (measurable_pi_iff.2 fun r => hbm r)

/-- **The restarted drift path has the law of the drift path.** With `Y = dpath σ μ b` the
process `u ↦ Y (l + u) - Y l` is a Brownian motion with drift `μ` started at `0` (the shift of
`b` is a Brownian motion, `IsPreBrownianReal.shift`), so its path law is that of `Y`. -/
theorem map_smShift_dpath (hb : GoodBM b P) (σ μ : ℝ) (l : ℝ≥0) :
    P.map (fun ω => fun u : ℝ≥0 => dpath σ μ b ω (l + u) - dpath σ μ b ω l) =
      P.map (fun ω => fun t : ℝ≥0 => dpath σ μ b ω t) := by
  have hbshift : IsPreBrownianReal (fun u ω => b (l + u) ω - b l ω) P := hb.pre.shift l
  have hm : ∀ u : ℝ≥0, Measurable fun ω => b (l + u) ω - b l ω :=
    fun u => (hb.meas (l + u)).sub (hb.meas l)
  have hlaw := GermZeroOne.map_path_eq_of_isPreBrownianReal hb.pre hbshift hb.meas hm
  set Ψ : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun w u => σ * w u + μ * (u : ℝ) with hΨ
  have hΨm : Measurable Ψ :=
    measurable_pi_iff.2 fun u => (measurable_const.mul (measurable_pi_apply u)).add_const _
  have hL : (fun ω => fun u : ℝ≥0 => dpath σ μ b ω (l + u) - dpath σ μ b ω l) =
      Ψ ∘ fun ω u => b (l + u) ω - b l ω := by
    funext ω u
    simp only [Function.comp_apply, hΨ, dpath, NNReal.coe_add]
    ring
  have hR : (fun ω => fun t : ℝ≥0 => dpath σ μ b ω t) = Ψ ∘ fun ω t => b t ω := by
    funext ω t
    simp only [Function.comp_apply, hΨ, dpath]
  calc P.map (fun ω => fun u : ℝ≥0 => dpath σ μ b ω (l + u) - dpath σ μ b ω l)
      = P.map (Ψ ∘ fun ω u => b (l + u) ω - b l ω) := by rw [hL]
    _ = (P.map (fun ω u => b (l + u) ω - b l ω)).map Ψ :=
        (Measure.map_map hΨm (measurable_pi_iff.2 hm)).symm
    _ = (P.map (fun ω t => b t ω)).map Ψ := by rw [hlaw]
    _ = P.map (Ψ ∘ fun ω t => b t ω) := Measure.map_map hΨm (measurable_pi_iff.2 hb.meas)
    _ = P.map (fun ω => fun t : ℝ≥0 => dpath σ μ b ω t) := by rw [hR]

/-! ## Factorization of an integral over an independent pair -/

/-- **Factorization under independence.** For independent random variables `f`, `g` and a
measurable `Φ`, `E[Φ (f, g)] = E[E[Φ (f, g')]]`, where the inner expectation is taken over an
independent copy `g'` of `g` (here represented by `g` again under `P`). -/
theorem lintegral_pair_eq [IsFiniteMeasure P] {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : Ω → α} {g : Ω → β} (hf : Measurable f) (hg : Measurable g) (hind : IndepFun f g P)
    {Φ : α → β → ℝ≥0∞} (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ ω, Φ (f ω) (g ω) ∂P = ∫⁻ ω, ∫⁻ ω', Φ (f ω) (g ω') ∂P ∂P := by
  haveI : IsFiniteMeasure (P.map g) := Measure.isFiniteMeasure_map P g
  have hΦm : Measurable fun p : α × β => Φ p.1 p.2 := hΦ
  have hpairm : Measurable fun ω => (f ω, g ω) := hf.prod hg
  have hmap := hind.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  have hinner : ∀ x : α, ∫⁻ y, Φ x y ∂(P.map g) = ∫⁻ ω', Φ x (g ω') ∂P := fun x =>
    lintegral_map' (μ := P) (g := g) (f := fun y => Φ x y)
      (hf := (hΦm.comp ((measurable_const : Measurable fun _ : β => x).prodMk measurable_id)).aemeasurable)
      (hg := hg.aemeasurable)
  have hΨm : AEMeasurable (fun x : α => ∫⁻ ω', Φ x (g ω') ∂P) (P.map f) :=
    (Measurable.lintegral_prod_right (ν := P) (f := fun x ω' => Φ x (g ω'))
      (hΦm.comp (measurable_fst.prodMk (hg.comp measurable_snd)))).aemeasurable
  have h1 : ∫⁻ ω, Φ (f ω) (g ω) ∂P = ∫⁻ p, Φ p.1 p.2 ∂(P.map fun ω => (f ω, g ω)) :=
    (lintegral_map' (μ := P) (g := fun ω => (f ω, g ω)) (f := fun p : α × β => Φ p.1 p.2)
      (hf := hΦm.aemeasurable) (hg := hpairm.aemeasurable)).symm
  have h2 : ∫⁻ p, Φ p.1 p.2 ∂(P.map fun ω => (f ω, g ω))
      = ∫⁻ x, ∫⁻ y, Φ x y ∂(P.map g) ∂(P.map f) := by
    rw [hmap, lintegral_prod _ hΦm.aemeasurable]
  have h3 : ∫⁻ x, ∫⁻ y, Φ x y ∂(P.map g) ∂(P.map f)
      = ∫⁻ x, ∫⁻ ω', Φ x (g ω') ∂P ∂(P.map f) := lintegral_congr fun x => hinner x
  have h4 : ∫⁻ x, ∫⁻ ω', Φ x (g ω') ∂P ∂(P.map f)
      = ∫⁻ ω, ∫⁻ ω', Φ (f ω) (g ω') ∂P ∂P :=
    lintegral_map' (μ := P) (g := f) (f := fun x => ∫⁻ ω', Φ x (g ω') ∂P)
      (hf := hΨm) (hg := hf.aemeasurable)
  exact h1.trans (h2.trans (h3.trans h4))

/-- **Weighted factorization.** If a pair-valued random variable `Ξ` is independent of `ζ`, then
`E[Ξ.1 · Φ (Ξ, ζ)] = E[Ξ.1 · E[Φ (Ξ, ζ')]]`: the weight may depend on the pair `(Ξ, ζ)` through
its first component only. -/
theorem lintegral_mul_comp_pair [IsFiniteMeasure P] {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] {Ξ : Ω → ℝ≥0∞ × β} (hΞ : Measurable Ξ) {ζ : Ω → γ} (hζ : Measurable ζ)
    (hind : Indep (MeasurableSpace.comap Ξ (inferInstance : MeasurableSpace (ℝ≥0∞ × β)))
      (MeasurableSpace.comap ζ (inferInstance : MeasurableSpace γ)) P)
    {Φ : ℝ≥0∞ × β → γ → ℝ≥0∞} (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ ω, (Ξ ω).1 * Φ (Ξ ω) (ζ ω) ∂P = ∫⁻ ω, (Ξ ω).1 * ∫⁻ ω', Φ (Ξ ω) (ζ ω') ∂P ∂P := by
  have hind' : IndepFun Ξ ζ P := by
    rw [IndepFun_iff_Indep]
    exact hind
  have hΦ' : Measurable (Function.uncurry fun (p : ℝ≥0∞ × β) (w : γ) => p.1 * Φ p w) :=
    (measurable_fst.fst).mul hΦ
  refine (lintegral_pair_eq hΞ hζ hind' hΦ').trans ?_
  refine lintegral_congr fun ω => ?_
  exact lintegral_const_mul (Ξ ω).1 (hΦ.comp
    ((measurable_const : Measurable fun _ : Ω => Ξ ω).prodMk hζ))

/-! ## W1: the simple Markov property at a fixed time -/

/-- **W1, simple Markov property at a fixed time** (blueprint `EXT_PP_BLUEPRINT.md` §A.1, W1,
`markov_fixed`). For `Y = dpath σ μ b`, the future increment `u ↦ Y_{l+u} - Y_l` is independent
of the stopped past `t ↦ Y_{min t l}` and has the law of `Y`.

Source: Revuz–Yor III (3.7) (Markov property of Brownian motion with drift); in mathlib the
future shift of a pre-Brownian motion is independent of the past
(`IsPreBrownianReal.indepFun_shift`). -/
theorem markov_fixed (hb : GoodBM b P) (σ μ : ℝ) (l : ℝ≥0)
    {A : (ℝ≥0 → ℝ) → ℝ≥0∞} {G : ℝ → (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hA : Measurable A) (hG : Measurable (Function.uncurry G)) :
    ∫⁻ ω, A (fun t => dpath σ μ b ω (min t l)) * G (dpath σ μ b ω l)
        (fun u => dpath σ μ b ω (l + u) - dpath σ μ b ω l) ∂P
      = ∫⁻ ω, A (fun t => dpath σ μ b ω (min t l))
          * ∫⁻ ω', G (dpath σ μ b ω l) (dpath σ μ b ω') ∂P ∂P := by
  haveI : IsProbabilityMeasure P := hb.pre.isGaussianProcess.isProbabilityMeasure
  have hle : pastFilt b hb.meas l ≤ mΩ := (pastFilt b hb.meas).le' l
  -- the stopped past and the value at `l` are measurable for the past of `b` up to `l`
  have hstopped : Measurable[pastFilt b hb.meas l]
      (fun ω => fun t : ℝ≥0 => dpath σ μ b ω (min t l)) := by
    refine WedgeTrans.meas_pi_of _ _ fun t => ?_
    exact ((WedgeTrans.meas_comap_eval (fun ω (r : Set.Iic l) => b r ω)
      ⟨min t l, Set.mem_Iic.2 (min_le_right t l)⟩).const_mul σ).add_const _
  have hYl : Measurable[pastFilt b hb.meas l] (fun ω => dpath σ μ b ω l) :=
    ((WedgeTrans.meas_comap_eval (fun ω (r : Set.Iic l) => b r ω)
      ⟨l, Set.mem_Iic.2 le_rfl⟩).const_mul σ).add_const _
  have hξ : Measurable[pastFilt b hb.meas l]
      (fun ω => A (fun t => dpath σ μ b ω (min t l))) := hA.comp hstopped
  have hpairm : Measurable[pastFilt b hb.meas l] (fun ω =>
      (A (fun t => dpath σ μ b ω (min t l)), dpath σ μ b ω l)) := hξ.prod hYl
  -- the same pair with the σ-algebra argument of `MeasurableSet` pinned, then made ambient
  have hpairAll : ∀ s : Set (ℝ≥0∞ × ℝ), MeasurableSet s →
      MeasurableSet[pastFilt b hb.meas l] ((fun ω =>
        (A (fun t => dpath σ μ b ω (min t l)), dpath σ μ b ω l)) ⁻¹' s) := hpairm
  have hpair : ∀ s : Set (ℝ≥0∞ × ℝ), MeasurableSet s →
      MeasurableSet[mΩ] ((fun ω =>
        (A (fun t => dpath σ μ b ω (min t l)), dpath σ μ b ω l)) ⁻¹' s) := by
    intro t ht
    exact hle _ (hpairAll t ht)
  have hinc : Measurable fun ω => (fun u : ℝ≥0 => dpath σ μ b ω (l + u) - dpath σ μ b ω l) :=
    measurable_pi_iff.2 fun u =>
      (measurable_dpath hb σ μ (l + u)).sub (measurable_dpath hb σ μ l)
  -- the future increment is independent of the past of `b` up to `l`
  have hInd : Indep (pastFilt b hb.meas l) (MeasurableSpace.comap
      (fun ω => fun u : ℝ≥0 => dpath σ μ b ω (l + u) - dpath σ μ b ω l) MeasurableSpace.pi) P := by
    have h1 : Indep (MeasurableSpace.comap (fun ω (r : Set.Iic l) => b r ω) MeasurableSpace.pi)
        (MeasurableSpace.comap (fun ω u => b (l + u) ω - b l ω) MeasurableSpace.pi) P :=
      ((IndepFun_iff_Indep _ _ _).mp (hb.pre.indepFun_shift l)).symm
    refine indep_of_indep_of_le_right h1 ?_
    refine Measurable.comap_le (WedgeTrans.meas_pi_of _ _ fun u => ?_)
    have hcoord := WedgeTrans.meas_comap_eval (fun ω u => b (l + u) ω - b l ω) u
    convert (hcoord.const_mul σ).add_const (μ * (u : ℝ)) using 1
    funext ω
    simp only [dpath, NNReal.coe_add]
    ring
  have hind : Indep (MeasurableSpace.comap (fun ω =>
        (A (fun t => dpath σ μ b ω (min t l)), dpath σ μ b ω l))
        (inferInstance : MeasurableSpace (ℝ≥0∞ × ℝ)))
      (MeasurableSpace.comap (fun ω => fun u : ℝ≥0 =>
        dpath σ μ b ω (l + u) - dpath σ μ b ω l) MeasurableSpace.pi) P :=
    indep_of_indep_of_le_left hInd (Measurable.comap_le hpairm)
  refine (lintegral_mul_comp_pair hpair hinc hind (Φ := fun (y : ℝ≥0∞ × ℝ) (w : ℝ≥0 → ℝ) =>
      G y.2 w) (hG.comp (measurable_fst.snd.prodMk measurable_snd))).trans ?_
  refine lintegral_congr fun ω => ?_
  congr 1
  exact lintegral_of_map_eq (map_smShift_dpath hb σ μ l)
    (hG.comp ((measurable_const : Measurable fun _ : ℝ≥0 → ℝ => dpath σ μ b ω l).prodMk
      measurable_id)) hinc (measurable_dpath_path hb σ μ)

end QuantumZipper.Williams
