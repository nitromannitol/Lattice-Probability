/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.JointScalingOLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOClock
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTAffineReroot
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeAddConstLat

/-!
#  random dilation of an independent curve, and the joint law transfer

The
Lebesgue-parametrized whole-plane space-filling SLE `η_L` is independent of the cone data and its
law is invariant under each **fixed** dilation `c ↦ r⁻¹ c(r² ·)` (`dilCurve r`, which is the frozen
`affineReroot 0 r 0` on curves rooted at time `0`). The cone scale `R_b` is random, but a measurable
positive function of the cone data. Fubini (QuantumZipper's `F1.map_prod_mk_dep`) then shows that
the randomly dilated curve, jointly with the cone data, still has the law of `(data, η_L)`; together
with the field law `h_b =d h` ([14, Prop 4.13(i)]) this gives, for every measurable
functional `Ψ` of (field, curve):

  `P(Ψ(h_b, R_b⁻¹ η_L(R_b² ·)) ∈ T) = P(Ψ(h, η_L) ∈ T)` (`measure_dilCurve_indep_eq`).

SLE-free; the curve-law invariance and the independence are hypotheses here (supplied for the
mating-of-trees coupling in `JointScalingOMain`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

namespace JointScalingO

open LQGMetric

/-! ### The Brownian-type dilation of curves -/

/-- The dilation `t ↦ r⁻¹ c(r² t)` of a curve (space by `r⁻¹`, Lebesgue time by `r²`). -/
def dilCurve (r : ℝ) (c : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => ((r⁻¹ : ℝ) : ℂ) * c (r ^ 2 * t), by fun_prop⟩

theorem dilCurve_apply (r : ℝ) (c : C(ℝ, ℂ)) (t : ℝ) :
    dilCurve r c t = ((r⁻¹ : ℝ) : ℂ) * c (r ^ 2 * t) := rfl

theorem measurable_dilCurve : Measurable fun p : ℝ × C(ℝ, ℂ) => dilCurve p.1 p.2 := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  have hev : Measurable fun x : C(ℝ, ℂ) × ℝ => x.1 x.2 := continuous_eval.measurable
  have h1 : Measurable fun p : ℝ × C(ℝ, ℂ) => p.2 (p.1 ^ 2 * t) :=
    hev.comp (f := fun p : ℝ × C(ℝ, ℂ) => (p.2, p.1 ^ 2 * t))
      (measurable_snd.prodMk ((measurable_fst.pow_const 2).mul_const t))
  have h2 : Measurable fun p : ℝ × C(ℝ, ℂ) => ((p.1⁻¹ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp measurable_fst.inv
  exact h2.mul h1

/-- On a curve rooted at time `0`, the frozen `affineReroot 0 r 0` is the dilation `dilCurve r`. -/
theorem dilCurve_eq_affineReroot (r : ℝ) (c : C(ℝ, ℂ)) (h : MatedCRT.firstHit c 0 = 0) :
    dilCurve r c = MatedCRT.affineReroot 0 r 0 c := by
  ext t
  simp [dilCurve, MatedCRT.affineReroot, h]

/-! ### The law transfer -/

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {β α : Type*} [MeasurableSpace β] [MeasurableSpace α]

/-- **Random dilation of an independent curve, through a measurable functional** (the scaling argument
step 4). Let `V` (the cone data) be independent of the curve `η_L`, whose law is invariant under
every fixed dilation. Let `F₁ V`, `F₂ V` be two fields with the same law (`h_b` and `h`) and
`R = Rv V > 0` a measurable scale. Then for every measurable `Ψ` and `T`,
`P(Ψ(F₁ V, dilCurve (Rv V) η_L) ∈ T) = P(Ψ(F₂ V, η_L) ∈ T)`. -/
theorem measure_dilCurve_indep_eq {V : Ω → β} {ηL : Ω → C(ℝ, ℂ)}
    (hV : Measurable V) (hηL : Measurable ηL) (hind : IndepFun V ηL P)
    (hdil : ∀ r : ℝ, 0 < r → P.map (fun ω => dilCurve r (ηL ω)) = P.map ηL)
    {F₁ F₂ : β → DistC} (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hlaw : P.map (fun ω => F₁ (V ω)) = P.map (fun ω => F₂ (V ω)))
    {Rv : β → ℝ} (hRv : Measurable Rv) (hRpos : ∀ v, 0 < Rv v)
    {Ψ : DistC × C(ℝ, ℂ) → α} (hΨ : Measurable Ψ) {T : Set α} (hT : MeasurableSet T) :
    P {ω | Ψ (F₁ (V ω), dilCurve (Rv (V ω)) (ηL ω)) ∈ T} =
      P {ω | Ψ (F₂ (V ω), ηL ω) ∈ T} := by
  set μ := P.map V with hμ
  set ν := P.map ηL with hν
  have : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hηL.aemeasurable).2 inferInstance
  have hjoint : P.map (fun ω => (V ω, ηL ω)) = μ.prod ν :=
    (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hηL.aemeasurable).1 hind
  -- the dilation as a measurable function of (datum, curve)
  let g : β × C(ℝ, ℂ) → C(ℝ, ℂ) := fun p => dilCurve (Rv p.1) p.2
  have hg : Measurable g :=
    measurable_dilCurve.comp (f := fun p : β × C(ℝ, ℂ) => (Rv p.1, p.2))
      ((hRv.comp measurable_fst).prodMk measurable_snd)
  have hsec : ∀ v : β, ν.map (fun c => g (v, c)) = ν := by
    intro v
    have hgv : Measurable fun c => g (v, c) := hg.comp measurable_prodMk_left
    rw [hν, Measure.map_map hgv hηL]
    exact hdil (Rv v) (hRpos v)
  have hdep : (μ.prod ν).map (fun p => (p.1, g p)) = μ.prod ν :=
    QuantumZipper.F1.map_prod_mk_dep μ ν hg ν hsec
  -- the two functionals of (datum, curve)
  let G₁ : β × C(ℝ, ℂ) → α := fun p => Ψ (F₁ p.1, p.2)
  let G₂ : β × C(ℝ, ℂ) → α := fun p => Ψ (F₂ p.1, p.2)
  have hG₁ : Measurable G₁ := hΨ.comp (f := fun p : β × C(ℝ, ℂ) => (F₁ p.1, p.2))
    ((hF₁.comp measurable_fst).prodMk measurable_snd)
  have hG₂ : Measurable G₂ := hΨ.comp (f := fun p : β × C(ℝ, ℂ) => (F₂ p.1, p.2))
    ((hF₂.comp measurable_fst).prodMk measurable_snd)
  have hpair : Measurable fun ω => (V ω, ηL ω) := hV.prodMk hηL
  have hdm : Measurable fun p : β × C(ℝ, ℂ) => (p.1, g p) := measurable_fst.prodMk hg
  have hL : P {ω | Ψ (F₁ (V ω), dilCurve (Rv (V ω)) (ηL ω)) ∈ T} = (μ.prod ν) (G₁ ⁻¹' T) := by
    have e : {ω | Ψ (F₁ (V ω), dilCurve (Rv (V ω)) (ηL ω)) ∈ T} =
        (fun ω => (V ω, ηL ω)) ⁻¹' ((fun p : β × C(ℝ, ℂ) => (p.1, g p)) ⁻¹' (G₁ ⁻¹' T)) := rfl
    rw [e, ← Measure.map_apply hpair (hdm (hG₁ hT)), hjoint, ← Measure.map_apply hdm (hG₁ hT),
      hdep]
  have hR : P {ω | Ψ (F₂ (V ω), ηL ω) ∈ T} = (μ.prod ν) (G₂ ⁻¹' T) := by
    have e : {ω | Ψ (F₂ (V ω), ηL ω) ∈ T} = (fun ω => (V ω, ηL ω)) ⁻¹' (G₂ ⁻¹' T) := rfl
    rw [e, ← Measure.map_apply hpair (hG₂ hT), hjoint]
  have hF : μ.map F₁ = μ.map F₂ := by
    rw [hμ, Measure.map_map hF₁ hV, Measure.map_map hF₂ hV]
    exact hlaw
  have hmid : (μ.prod ν) (G₁ ⁻¹' T) = (μ.prod ν) (G₂ ⁻¹' T) := by
    have e₁ : G₁ ⁻¹' T = Prod.map F₁ id ⁻¹' (Ψ ⁻¹' T) := rfl
    have e₂ : G₂ ⁻¹' T = Prod.map F₂ id ⁻¹' (Ψ ⁻¹' T) := rfl
    rw [e₁, e₂, ← Measure.map_apply (hF₁.prodMap measurable_id) (hΨ hT),
      ← Measure.map_apply (hF₂.prodMap measurable_id) (hΨ hT),
      ← Measure.map_prod_map μ ν hF₁ measurable_id, ← Measure.map_prod_map μ ν hF₂ measurable_id,
      hF]
  rw [hL, hR, hmid]

end Law

end JointScalingO

end MatedCRTHarmonic.CellScaling
