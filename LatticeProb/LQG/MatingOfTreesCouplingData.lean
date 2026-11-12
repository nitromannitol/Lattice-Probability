import LatticeProb.LQG.MatingOfTreesCouplingVersion
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.FieldDecomp
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.RadialPath
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.Lateral

/-!
# The data of a mating-of-trees coupling as a random element of a standard Borel space

A mating-of-trees coupling consists of three fields, four Brownian processes, a uniform variable,
three curves and a boundary-length pair. This file collects them into one data space
`CouplingData`: three distributions, four continuous paths on `[0, ∞)`, a real number, three
continuous curves in `ℂ` and a continuous path in `ℝ²`. It is a standard Borel space (a finite
product of standard Borel spaces: the space of distributions, and the Polish spaces of continuous
maps with the compact-open topology and their Borel σ-algebras).

* `IsCouplingData γ P V`: the coordinates of a random element `V` of the data space form a
  mating-of-trees coupling.
* `IsMatingOfTreesCoupling.exists_couplingData`: every mating-of-trees coupling is, up to a
  modification of its Brownian coordinates and of its uniform variable on a null set, given by a
  measurable random element of the data space.
* `CouplingData.coneTriple`: the γ-quantum cone field, the curve and the boundary-length pair,
  read off the data by a measurable map; on the set of pairs of paths for which the cone radial
  path is continuous it is the circle-average embedding of the cone.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The data space of a mating-of-trees coupling: the fields `(X, X₀, h^IG)`, the Brownian paths
`(B, B', B₀, B₀')`, the uniform variable `U`, the curves `(η_L, η, η₀)` and the boundary-length
pair. -/
abbrev CouplingData : Type :=
  (Field × Field × Field) × (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) × ℝ ×
    (C(ℝ, ℂ) × C(ℝ, ℂ) × C(ℝ, ℂ)) × Path2

/-- The data space of a mating-of-trees coupling is a standard Borel space. -/
theorem standardBorelSpace_couplingData : StandardBorelSpace CouplingData := by
  have : StandardBorelSpace C(ℝ≥0, ℝ) := inferInstance
  have : StandardBorelSpace C(ℝ, ℂ) := inferInstance
  have : StandardBorelSpace Path2 := inferInstance
  have : StandardBorelSpace Field := inferInstance
  infer_instance

attribute [instance] standardBorelSpace_couplingData

namespace CouplingData

/-- The whole-plane GFF `X` of the γ-quantum cone. -/
def X (v : CouplingData) : Field := v.1.1

/-- The whole-plane GFF `X₀` of the `0`-quantum cone. -/
def X₀ (v : CouplingData) : Field := v.1.2.1

/-- The imaginary-geometry field. -/
def hIG (v : CouplingData) : Field := v.1.2.2

/-- The first Brownian path of the γ-quantum cone. -/
def B (v : CouplingData) : C(ℝ≥0, ℝ) := v.2.1.1

/-- The second Brownian path of the γ-quantum cone. -/
def B' (v : CouplingData) : C(ℝ≥0, ℝ) := v.2.1.2.1

/-- The first Brownian path of the `0`-quantum cone. -/
def B₀ (v : CouplingData) : C(ℝ≥0, ℝ) := v.2.1.2.2.1

/-- The second Brownian path of the `0`-quantum cone. -/
def B₀' (v : CouplingData) : C(ℝ≥0, ℝ) := v.2.1.2.2.2

/-- The uniform variable. -/
def U (v : CouplingData) : ℝ := v.2.2.1

/-- The space-filling curve parametrized by Lebesgue measure. -/
def ηL (v : CouplingData) : C(ℝ, ℂ) := v.2.2.2.1.1

/-- The space-filling curve parametrized by the γ-LQG area of the γ-quantum cone. -/
def η (v : CouplingData) : C(ℝ, ℂ) := v.2.2.2.1.2.1

/-- The space-filling curve parametrized by the γ-LQG area of the `0`-quantum cone. -/
def η₀ (v : CouplingData) : C(ℝ, ℂ) := v.2.2.2.1.2.2

/-- The boundary-length pair. -/
def bm (v : CouplingData) : Path2 := v.2.2.2.2

/-- Assemble a point of the data space from its coordinates. -/
def mk (X X₀ hIG : Field) (B B' B₀ B₀' : C(ℝ≥0, ℝ)) (U : ℝ) (ηL η η₀ : C(ℝ, ℂ)) (bm : Path2) :
    CouplingData :=
  ((X, X₀, hIG), (B, B', B₀, B₀'), U, (ηL, η, η₀), bm)

theorem measurable_X : Measurable X := measurable_fst.comp measurable_fst

theorem measurable_X₀ : Measurable X₀ :=
  measurable_fst.comp (measurable_snd.comp measurable_fst)

theorem measurable_hIG : Measurable hIG :=
  measurable_snd.comp (measurable_snd.comp measurable_fst)

theorem measurable_B : Measurable B := measurable_fst.comp (measurable_fst.comp measurable_snd)

theorem measurable_B' : Measurable B' :=
  measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))

theorem measurable_B₀ : Measurable B₀ :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd)))

theorem measurable_B₀' : Measurable B₀' :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd)))

theorem measurable_U : Measurable U := measurable_fst.comp (measurable_snd.comp measurable_snd)

theorem measurable_ηL : Measurable ηL :=
  measurable_fst.comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))

theorem measurable_η : Measurable η :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

theorem measurable_η₀ : Measurable η₀ :=
  measurable_snd.comp (measurable_snd.comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

theorem measurable_bm : Measurable bm :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))

/-- Evaluation of a Brownian coordinate at a fixed time is measurable. -/
theorem measurable_eval_comp {f : CouplingData → C(ℝ≥0, ℝ)} (hf : Measurable f) (t : ℝ≥0) :
    Measurable fun v => f v t :=
  (ContinuousMap.measurable_eval t).comp hf

/-- The γ-quantum cone field, the γ-LQG-area-parametrized curve and the boundary-length pair read
off the data: the field is the lateral part of `X` plus the radial function built from the pair of
paths `(B, B')` (`ConeScaling.radMap`, which is the cone radial path on `ConeScaling.radGood` and
`0` elsewhere). -/
def coneTriple (γ : ℝ) (v : CouplingData) : Field × C(ℝ, ℂ) × Path2 :=
  (ConeScaling.fieldOf (CellScaling.lateralPart v.X) (ConeScaling.radMap γ γ (v.B, v.B')), v.η, v.bm)

theorem measurable_coneTriple (γ : ℝ) : Measurable (coneTriple γ) :=
  (ConeScaling.measurable_fieldOf.comp ((ConeScaling.measurable_lateralPart.comp measurable_X).prodMk
    ((ConeScaling.measurable_radMap γ γ).comp (measurable_B.prodMk measurable_B')))).prodMk
    (measurable_η.prodMk measurable_bm)

/-- On the set of pairs of paths for which the cone radial path is continuous, the field
coordinate of `coneTriple` is the circle-average embedding of the γ-quantum cone. -/
theorem coneTriple_fst_of_mem {γ : ℝ} {v : CouplingData}
    (hv : (v.B, v.B') ∈ ConeScaling.radGood γ γ) :
    (coneTriple γ v).1 = coneField v.X (coneRadial γ γ v.B v.B') := by
  classical
  have h := ConeScaling.coneFieldOf_eq_fieldOf γ v.X (b := v.B) (b' := v.B')
    (w := ConeScaling.radMap γ γ (v.B, v.B')) fun t => by
      simp only [ConeScaling.radMap_apply, hv, ↓reduceIte]
  exact h.symm

end CouplingData

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}

/-- The coordinates of a random element `V` of the data space form a mating-of-trees coupling. -/
def IsCouplingData (γ : ℝ) (P : Measure Ω) (V : Ω → CouplingData) : Prop :=
  IsMatingOfTreesCoupling γ P (fun ω => (V ω).X) (fun ω => (V ω).X₀) (fun ω => (V ω).hIG)
    (fun t ω => (V ω).B t) (fun t ω => (V ω).B' t) (fun t ω => (V ω).B₀ t)
    (fun t ω => (V ω).B₀' t) (fun ω => (V ω).U) (fun ω => (V ω).ηL) (fun ω => (V ω).η)
    (fun ω => (V ω).η₀) (fun ω => (V ω).bm)

variable {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The data of a mating-of-trees coupling.** A mating-of-trees coupling is given by a measurable
random element of the standard Borel data space: its fields, curves and boundary-length pair are
the coordinates of the data everywhere, and its Brownian processes and uniform variable almost
surely. -/
theorem IsMatingOfTreesCoupling.exists_couplingData
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ V : Ω → CouplingData, Measurable V ∧ IsCouplingData γ P V ∧
      (∀ ω, (V ω).X = X ω ∧ (V ω).X₀ = X₀ ω ∧ (V ω).hIG = hIG₀ ω ∧ (V ω).ηL = ηL ω ∧
        (V ω).η = η ω ∧ (V ω).η₀ = η₀ ω ∧ (V ω).bm = bm ω) ∧
      ∀ᵐ ω ∂P, (∀ t, (V ω).B t = B t ω) ∧ (∀ t, (V ω).B' t = B' t ω) ∧
        (∀ t, (V ω).B₀ t = B₀ t ω) ∧ (∀ t, (V ω).B₀' t = B₀' t ω) ∧ (V ω).U = U ω := by
  obtain ⟨Bn, Bn', B₀n, B₀n', Un, hCn, hc, hc', hc₀, hc₀', hm, hm', hm₀, hm₀', hUm, hae⟩ :=
    hC.exists_regular_version
  refine ⟨fun ω => CouplingData.mk (X ω) (X₀ ω) (hIG₀ ω) ⟨fun t => Bn t ω, hc ω⟩
      ⟨fun t => Bn' t ω, hc' ω⟩ ⟨fun t => B₀n t ω, hc₀ ω⟩ ⟨fun t => B₀n' t ω, hc₀' ω⟩ (Un ω)
      (ηL ω) (η ω) (η₀ ω) (bm ω), ?_, hCn, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      hae.mono fun _ h => h⟩
  have hX := hC.gff.measurable
  have hX₀ := hC.gff₀.measurable
  have hIG := hC.igField.1.1.measurable
  obtain ⟨hηL, hη, hη₀, hbm⟩ := hC.measurable_curves
  exact (hX.prodMk (hX₀.prodMk hIG)).prodMk
    (((measurable_continuousMap_of_forall hc hm).prodMk
      ((measurable_continuousMap_of_forall hc' hm').prodMk
        ((measurable_continuousMap_of_forall hc₀ hm₀).prodMk
          (measurable_continuousMap_of_forall hc₀' hm₀')))).prodMk
      (hUm.prodMk ((hηL.prodMk (hη.prodMk hη₀)).prodMk hbm)))

end MatedCRT

end MatedCRTHarmonic

end
