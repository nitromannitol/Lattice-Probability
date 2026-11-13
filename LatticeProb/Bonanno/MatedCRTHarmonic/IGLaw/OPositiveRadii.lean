/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.OPositiveRadii at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OAffinePos
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.CurveLaws
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.ConeRealization
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Theorem44

/-!
# The positive-radius `igMap` clause `IGMapPositiveRadii` and the curve-scaling laws it gives

`IGMapPositiveRadii γ P hIG₀ U ηL` is, **verbatim**, the body of the frozen bundle field `igMap` with one added
clause (second conjunct): the imaginary-geometry map `Φ` ignores the radii `≤ 0` of its input,

`∀ K K' : ℝ → ℂ → ℝ, (∀ ρ : ℝ, 0 < ρ → K ρ = K' ρ) → Φ K = Φ K'`.

With this strengthening of `igMap`,
`hC.igMap : IGMapPositiveRadii γ P hIG₀ U ηL` by `exact`. Source-faithful: the IG flow lines, hence the curve, are
a function of the field (MS17 Thm 1.16; [18]), and the field is determined by its circle averages at
positive radii; the radius-`≤ 0` coordinates of LQGMetric's `circleAvg` are junk (`OCounter`, `ODiverge`).

From the frozen bundle plus this one hypothesis:
* `IsMatingOfTreesCoupling.map_affineReroot_of_igMapPositiveRadii`: `law(affineReroot z₀ s φ ηL) = law(ηL)` for all
  `z₀`, `s > 0`, `φ` (the imaginary-geometry covariance statement, dilation and translation parts);
* `IsMatingOfTreesCoupling.map_curveRescale_sq_of_igMapPositiveRadii`: `law(s⁻¹ ηL(s² ·)) = law(ηL)`;
* `IsMatingOfTreesCoupling.igcFixedAffineRerootInvariant_of_igMapPositiveRadii`: the named input
  `CellScaling.IGCFixedAffineRerootInvariant P ηL` (replacing the refuted full-input route);
* `IsMatingOfTreesCoupling.map_prod_curveRescale_sq_cones_of_igMapPositiveRadii`: for every measurable positive
  scale `S` of the complete cone tuple `V = (X, B, B', X₀, B₀, B₀')`,
  `law(V, S(V)⁻¹ ηL(S(V)² ·)) = law(V, ηL)` (the random-scale curve law of the cone scaling identity and [18] Thm 4.4).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace MatedCRTHarmonic.IGLaw

open LQGMetric MatedCRTHarmonic.MatedCRT

/-- **The amended `igMap` clause**: the body
of the frozen field `IsMatingOfTreesCoupling.igMap` with the added second conjunct "`Φ` ignores radii `≤ 0`". -/
def IGMapPositiveRadii (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hIG₀ : Ω → Field)
    (U : Ω → ℝ) (ηL : Ω → C(ℝ, ℂ)) : Prop :=
  ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
    (∀ K K' : ℝ → ℂ → ℝ, (∀ ρ : ℝ, 0 < ρ → K ρ = K' ρ) → Φ K = Φ K') ∧
    (∀ᵐ ω ∂P, ηL ω = Φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) ∧
    (∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (igPullback γ z₀ s φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) =
        affineReroot z₀ s φ (ηL ω)) ∧
    (∀ (V : Set ℂ), IsOpen V → Bornology.IsBounded V → ∀ δ : ℝ, 0 < δ →
      ∃ g : (ℝ → ℂ → ℝ) → (ℚ × ℚ → ℝ → ℂ), Measurable g ∧ ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ,
        ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ V →
          excursionSegment (ηL ω) V ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) =
            g (restrictCircles (thickening δ V)
              (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) q)

lemma posIn_eq_on_pos (K : ℝ → ℂ → ℝ) : ∀ ρ : ℝ, 0 < ρ → posIn K ρ = K ρ :=
  fun _ hρ => funext fun w => posIn_apply_of_pos hρ w K

section General

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hIG₀ : Ω → Field} {U : Ω → ℝ}
  {ηL : Ω → C(ℝ, ℂ)}

/-- The amended clause gives the positive-radius form `IGMapPos`. -/
theorem igMapPos_of_igMapPositiveRadii (hpos : IGMapPositiveRadii γ P hIG₀ U ηL) :
    IGMapPos γ P hIG₀ U ηL := by
  obtain ⟨Φ, hΦ, hign, hroot, hcc, -⟩ := hpos
  refine ⟨Φ, hΦ, ?_, fun z₀ s φ hs => ?_⟩
  · filter_upwards [hroot] with ω hω
    rw [hω]
    exact hign _ _ fun ρ hρ =>
      (posIn_eq_on_pos (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω) ρ hρ).symm
  · filter_upwards [hcc z₀ s φ hs] with ω hω
    rw [← hω]
    exact hign _ _ fun ρ hρ =>
      posIn_eq_on_pos (igPullback γ z₀ s φ (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω)) ρ hρ

end General

/-! ## The Brownian scaling action on curves and its random-scale law -/
/-- Joint measurability of `(r, c) ↦ r⁻¹ c(r² ·)` on positive scales. -/
theorem measurable_curveRescale_sq_pos :
    Measurable fun p : Set.Ioi (0 : ℝ) × C(ℝ, ℂ) => GMS4b.curveRescale p.1.1 (p.1.1 ^ 2) p.2 := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  have heval : Measurable fun q : C(ℝ, ℂ) × ℝ => q.1 q.2 := continuous_eval.measurable
  have hR : Measurable fun p : Set.Ioi (0 : ℝ) × C(ℝ, ℂ) => p.1.1 :=
    measurable_subtype_coe.comp measurable_fst
  have hc : Measurable fun p : Set.Ioi (0 : ℝ) × C(ℝ, ℂ) => p.2 (p.1.1 ^ 2 * t) :=
    heval.comp (measurable_snd.prodMk ((hR.pow_const 2).mul_const t))
  exact (Complex.measurable_ofReal.comp (measurable_inv.comp hR)).mul hc

/-- At a curve rooted at time `0`, `affineReroot 0 s 0` is the Brownian scaling action `c ↦ s⁻¹ c(s² ·)`. -/
theorem curveRescale_sq_eq_affineReroot {s : ℝ} (c : C(ℝ, ℂ)) (hroot : firstHit c 0 = 0) :
    GMS4b.curveRescale s (s ^ 2) c = affineReroot 0 s 0 c := by
  ext t
  simp [GMS4b.curveRescale_apply, affineReroot, hroot]

/-- **Random-scale curve law**: if `ηL`'s law is invariant under every fixed Brownian scaling and `V` is independent of
`ηL`, then for every measurable positive scale `S(V)`, `law(V, S(V)⁻¹ ηL(S(V)² ·)) = law(V, ηL)`. -/
theorem map_prod_curveRescale_sq_of_fixed {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] {V : Ω → β} {ηL : Ω → C(ℝ, ℂ)}
    (hη : Measurable ηL)
    (hfix : ∀ s : ℝ, 0 < s → P.map (fun ω => GMS4b.curveRescale s (s ^ 2) (ηL ω)) = P.map ηL)
    (hV : Measurable V) (hind : IndepFun V ηL P) {S : β → Set.Ioi (0 : ℝ)} (hS : Measurable S) :
    P.map (fun ω => (V ω, GMS4b.curveRescale (S (V ω)).1 ((S (V ω)).1 ^ 2) (ηL ω))) =
      P.map (fun ω => (V ω, ηL ω)) := by
  have hjoint : P.map (fun ω => (V ω, ηL ω)) = (P.map V).prod (P.map ηL) :=
    (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hη.aemeasurable).1 hind
  have : IsProbabilityMeasure (P.map V) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (P.map ηL) :=
    (Measure.isProbabilityMeasure_map_iff hη.aemeasurable).2 inferInstance
  have hgm : Measurable (Function.uncurry fun (v : β) (c : C(ℝ, ℂ)) =>
      GMS4b.curveRescale (S v).1 ((S v).1 ^ 2) c) :=
    measurable_curveRescale_sq_pos.comp ((hS.comp measurable_fst).prodMk measurable_snd)
  have hsec : ∀ v : β, (P.map ηL).map (fun c => GMS4b.curveRescale (S v).1 ((S v).1 ^ 2) c) =
      P.map ηL := by
    intro v
    have hm : Measurable fun c : C(ℝ, ℂ) => GMS4b.curveRescale (S v).1 ((S v).1 ^ 2) c :=
      hgm.comp measurable_prodMk_left
    rw [Measure.map_map hm hη]
    exact hfix (S v).1 (S v).2
  have hmp : MeasurePreserving
      (fun p : β × C(ℝ, ℂ) => (id p.1, GMS4b.curveRescale (S p.1).1 ((S p.1).1 ^ 2) p.2))
      ((P.map V).prod (P.map ηL)) ((P.map V).prod (P.map ηL)) :=
    MeasurePreserving.skew_product (MeasurePreserving.id _) hgm (ae_of_all _ hsec)
  have hpair : Measurable fun ω => (V ω, ηL ω) := hV.prodMk hη
  calc P.map (fun ω => (V ω, GMS4b.curveRescale (S (V ω)).1 ((S (V ω)).1 ^ 2) (ηL ω))) =
      (P.map (fun ω => (V ω, ηL ω))).map
        (fun p : β × C(ℝ, ℂ) => (id p.1, GMS4b.curveRescale (S p.1).1 ((S p.1).1 ^ 2) p.2)) :=
        (Measure.map_map hmp.measurable hpair).symm
    _ = ((P.map V).prod (P.map ηL)).map
        (fun p : β × C(ℝ, ℂ) => (id p.1, GMS4b.curveRescale (S p.1).1 ((S p.1).1 ^ 2) p.2)) := by
        rw [hjoint]
    _ = (P.map V).prod (P.map ηL) := hmp.map_eq
    _ = P.map (fun ω => (V ω, ηL ω)) := hjoint.symm

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
  {B B' B₀ B₀' : NNReal → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}

/-- **Affine invariance of the Lebesgue-parametrized whole-plane space-filling SLE** from the frozen bundle and the
amended clause: `law(affineReroot z₀ s φ ηL) = law(ηL)`. -/
theorem IsMatingOfTreesCoupling.map_affineReroot_of_igMapPositiveRadii
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hpos : IGMapPositiveRadii γ P hIG₀ U ηL) (z₀ : ℂ) {s : ℝ} (hs : 0 < s) (φ : ℝ) :
    P.map (fun ω => affineReroot z₀ s φ (ηL ω)) = P.map ηL :=
  IsMatingOfTreesCoupling.map_affineReroot_of_igMapPos hC (igMapPos_of_igMapPositiveRadii hpos)
    z₀ hs φ

/-- The root time of `ηL` is `0` almost surely. -/
theorem IsMatingOfTreesCoupling.ae_firstHit_zero_of_igMapPositiveRadii
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hpos : IGMapPositiveRadii γ P hIG₀ U ηL) : ∀ᵐ ω ∂P, firstHit (ηL ω) 0 = 0 :=
  IsMatingOfTreesCoupling.ae_firstHit_zero_of_igMapPos hC (igMapPos_of_igMapPositiveRadii hpos)

/-- **The fixed-scale curve law**: `law(s⁻¹ ηL(s² ·)) = law(ηL)` for every `s > 0`. -/
theorem IsMatingOfTreesCoupling.map_curveRescale_sq_of_igMapPositiveRadii
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hpos : IGMapPositiveRadii γ P hIG₀ U ηL) {s : ℝ} (hs : 0 < s) :
    P.map (fun ω => GMS4b.curveRescale s (s ^ 2) (ηL ω)) = P.map ηL := by
  rw [← IsMatingOfTreesCoupling.map_affineReroot_of_igMapPositiveRadii hC hpos 0 hs 0]
  refine Measure.map_congr ?_
  filter_upwards [IsMatingOfTreesCoupling.ae_firstHit_zero_of_igMapPositiveRadii hC hpos]
    with ω hω
  exact curveRescale_sq_eq_affineReroot (ηL ω) hω

/-- **The random-scale curve law with the cone data retained**: for every measurable positive scale `S` of the
complete cone tuple `V = (X, B, B', X₀, B₀, B₀')`, `law(V, S(V)⁻¹ ηL(S(V)² ·)) = law(V, ηL)`. -/
theorem IsMatingOfTreesCoupling.map_prod_curveRescale_sq_cones_of_igMapPositiveRadii
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hpos : IGMapPositiveRadii γ P hIG₀ U ηL)
    {S : Field × (NNReal → ℝ) × (NNReal → ℝ) × Field × (NNReal → ℝ) × (NNReal → ℝ) → Set.Ioi (0 : ℝ)}
    (hS : Measurable S)
    (hV : Measurable fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω,
      (fun t => B₀ t ω), (fun t => B₀' t ω))) :
    P.map (fun ω => ((X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω,
        (fun t => B₀ t ω), (fun t => B₀' t ω)),
      GMS4b.curveRescale (S (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω,
          (fun t => B₀ t ω), (fun t => B₀' t ω))).1
        ((S (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω,
          (fun t => B₀ t ω), (fun t => B₀' t ω))).1 ^ 2) (ηL ω))) =
      P.map (fun ω => ((X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω,
        (fun t => B₀ t ω), (fun t => B₀' t ω)), ηL ω)) := by
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  exact map_prod_curveRescale_sq_of_fixed hC.measurable_curves.1
    (fun _ hs => IsMatingOfTreesCoupling.map_curveRescale_sq_of_igMapPositiveRadii hC hpos hs) hV
    (IsMatingOfTreesCoupling.indepFun_ηL_coneData hC).symm hS

/-! ### Unconditional forms for the mating-of-trees bundle -/

/-- **The v4 bundle field `igMap` is `IGMapPositiveRadii`** (same body). -/
theorem IsMatingOfTreesCoupling.igMapPositiveRadii
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IGMapPositiveRadii γ P hIG₀ U ηL :=
  hC.igMap

/-- **Affine invariance of `law(ηL)`** (v4): `law(affineReroot z₀ s φ ηL) = law(ηL)` for all `z₀`, `s > 0`, `φ`. -/
theorem IsMatingOfTreesCoupling.map_affineReroot_ηL
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (z₀ : ℂ) {s : ℝ} (hs : 0 < s) (φ : ℝ) :
    P.map (fun ω => affineReroot z₀ s φ (ηL ω)) = P.map ηL :=
  IsMatingOfTreesCoupling.map_affineReroot_of_igMapPositiveRadii hC (IsMatingOfTreesCoupling.igMapPositiveRadii hC) z₀ hs φ

end Bundle

end MatedCRTHarmonic.IGLaw
