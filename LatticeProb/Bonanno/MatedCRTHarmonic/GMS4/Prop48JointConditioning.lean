/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48JointConditioning at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA1A2
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.TupleIndep
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.Freeze
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA3Tuple
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine

/-!
# Joint local conditioning for [18] Proposition 4.8

The local observable in (4.22) depends on two independent whole-plane GFFs, `h` and `hIG`, and
on the two circle averages at the same radius. This file combines the two one-field versions of
[18] Lemma A.2 to condition jointly on that pair. The residual pair is independent of
the pair of circle averages, and the conditional expectation of every integrable measurable
local functional is its average over fresh residual samples with the observed averages frozen.

Source: [18, Proposition 4.8, especially (4.22), and Lemma 4.9]. Lemma A.2 is formalized in
`MatedCRTHarmonic.GMSAppA.LemmaA1A2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open LQGMetric LQGMetric.Blueprint

namespace MatedCRTHarmonic.GMS4

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The two independent fields, indexed for direct use with `GMSAppA.lemmaA3N`. -/
def prop48FieldFamily (h hIG : Ω → DistC) (i : Fin 2) : Ω → DistC :=
  if i = 0 then h else hIG

/-- The two fields in coordinates `w ↦ r w + z`, retaining their circle averages. -/
def prop48AffineFieldFamily (h hIG : Ω → DistC) (r : ℝ) (z : ℂ)
    (i : Fin 2) (ω : Ω) : DistC :=
  affineComp r z (prop48FieldFamily h hIG i ω)

/-- The circle in affine coordinates corresponding to the original unit circle still has
zero average. Its center is `-z/r` and its radius is `1/r`. -/
theorem prop48_affine_circle_normalized
    {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {h : Ω₀ → DistC} (hh : IsNormalizedWPGFF h P₀)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P₀,
      circleAvg (affineComp r z (h ω)) r⁻¹ (-(r⁻¹ : ℂ) * z) = 0 := by
  have hc := CircleAvg.ae_circleAvg_affineComp (hh.1.affineComp hr z)
    (inv_pos.mpr hr) (-(r⁻¹ : ℂ) * z)
  filter_upwards [hc, hh.2] with ω hω hn
  rw [← hω]
  have hcenter : (r : ℂ) * (-(r⁻¹ : ℂ) * z) + z = 0 := by
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    calc
      (r : ℂ) * (-(r⁻¹ : ℂ) * z) + z =
          z - z * ((r : ℂ) * (r : ℂ)⁻¹) := by ring
      _ = 0 := by rw [mul_inv_cancel₀ hrC]; ring
  rw [GM.affineComp_comp (inv_ne_zero hr.ne') hr.ne'
    (-(r⁻¹ : ℂ) * z) z (h ω)]
  simp only [mul_inv_cancel₀ hr.ne', hcenter, GM.affineComp_one_zero]
  exact hn

/-- If the rescaling radius stays inside the unit disk around `z`, the A.3 unit disk
in the rescaled coordinates lies inside the circle corresponding to the original unit circle. -/
theorem prop48_affine_unitBall_subset
    {r : ℝ} (hr : 0 < r) (z : ℂ) (hsmall : r + ‖z‖ < 1) :
    Metric.ball (0 : ℂ) 1 ⊆ Metric.ball (-(r⁻¹ : ℂ) * z) r⁻¹ := by
  apply Metric.ball_subset_ball'
  rw [dist_zero_left, norm_mul, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hr.le]
  change 1 + r⁻¹ * ‖z‖ ≤ r⁻¹
  rw [← one_div, le_div_iff₀ hr]
  calc
    (1 + 1 / r * ‖z‖) * r = r + ‖z‖ := by field_simp [hr.ne']
    _ ≤ 1 := hsmall.le

/-- Applying the same affine coordinate map to independent fields preserves independence. -/
theorem prop48_affine_fields_independent
    {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {h hIG : Ω₀ → DistC} (hind : IndepFun h hIG P₀)
    (r : ℝ) (z : ℂ) :
    IndepFun (fun ω => affineComp r z (h ω))
      (fun ω => affineComp r z (hIG ω)) P₀ :=
  hind.comp (measurable_affineComp r z) (measurable_affineComp r z)

/-- Two independent fields form a two-element independent family. -/
private theorem prop48_fieldFamily_iIndepFun
    {h hIG : Ω → DistC} [IsProbabilityMeasure P] (hind : IndepFun h hIG P) :
    iIndepFun (prop48FieldFamily h hIG) P := by
  classical
  rw [iIndepFun_iff]
  intro s E hE
  by_cases h0 : (0 : Fin 2) ∈ s
  · by_cases h1 : (1 : Fin 2) ∈ s
    · have hs : s = Finset.univ := Finset.eq_univ_iff_forall.mpr fun i => by
        fin_cases i <;> assumption
      subst s
      have hI : (⋂ i ∈ (Finset.univ : Finset (Fin 2)), E i) = E 0 ∩ E 1 := by
        ext ω
        simp
      have hprod : (∏ i ∈ (Finset.univ : Finset (Fin 2)), P (E i)) = P (E 0) * P (E 1) := by
        simp [Fin.prod_univ_succ]
      obtain ⟨A, hA, hAE⟩ := hE 0 (by simp)
      obtain ⟨B, hB, hBE⟩ := hE 1 (by simp)
      rw [hI, hprod]
      have hE0 : MeasurableSet[MeasurableSpace.comap h inferInstance] (E 0) := ⟨A, hA, hAE⟩
      have hE1 : MeasurableSet[MeasurableSpace.comap hIG inferInstance] (E 1) := by
        exact ⟨B, hB, hBE⟩
      have hdep := (IndepFun_iff h hIG P).1 hind (E 0) (E 1) hE0 hE1
      simpa [prop48FieldFamily] using hdep
    · have hs : s = {0} := by
        ext i
        fin_cases i <;> simp_all
      subst s
      simp

  · by_cases h1 : (1 : Fin 2) ∈ s
    · have hs : s = {1} := by
        ext i
        fin_cases i <;> simp_all
      subst s
      simp
    · have hs : s = ∅ := by
        ext i
        fin_cases i <;> simp_all
      subst s
      simp

/-- Appendix A.3 transported to the disk centered at `z` with radius `r`. The circle-average
sigma algebra in these coordinates is the pair of original averages at radius `r`; the exterior
sigma algebra is that of the original fields outside `B_r(z)`. The latter identifications are
proved separately, so this theorem retains the transformed-field notation explicitly. -/
theorem prop48_twoField_lemmaA3_affine
    {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {h hIG : Ω₀ → DistC}
    (hh : IsNormalizedWPGFF h P₀) (hhIG : IsNormalizedWPGFF hIG P₀)
    (hind : IndepFun h hIG P₀)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (hsmall : r + ‖z‖ < 1)
    {p p₀ s δ : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs : 0 < s)
    (hδ : 0 < δ) (hδa : δ ≤ GMSAppA.a3aN p p₀ 2)
    {X : Ω₀ → ℝ}
    {F : ((Fin 2 → DistOn (ballO 0 δ)) × (Fin 2 → ℝ)) → ℝ}
    (hF : Measurable F)
    (hX : X =ᵐ[P₀] fun ω => F (GMSAppA.obsN δ (prop48AffineFieldFamily h hIG r z) ω))
    (hXp₀ : ∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P₀ ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal
      |P₀[X | GMSAppA.extSigmaN (prop48AffineFieldFamily h hIG r z)] ω -
        P₀[X | GMSAppA.cSigmaN (prop48AffineFieldFamily h hIG r z)] ω| ^ p ∂P₀ ≤
      ENNReal.ofReal (GMSAppA.a3C p p₀) *
        (ENNReal.ofReal (δ ^ (s * p)) *
            ∫⁻ ω, ENNReal.ofReal |X ω| ^ p ∂P₀ +
          ENNReal.ofReal
              (Real.exp (-(GMSAppA.a3bN p p₀ 2 / δ ^ (1 - s)))) *
            (∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P₀) ^ (p / p₀)) := by
  have hfields : ∀ i : Fin 2,
      IsWholePlaneGFF (prop48AffineFieldFamily h hIG r z i) P₀ := by
    intro i
    fin_cases i
    · change IsWholePlaneGFF (fun ω => affineComp r z (h ω)) P₀
      exact hh.1.affineComp hr z
    · change IsWholePlaneGFF (fun ω => affineComp r z (hIG ω)) P₀
      exact hhIG.1.affineComp hr z
  have hind' : iIndepFun (prop48AffineFieldFamily h hIG r z) P₀ := by
    convert prop48_fieldFamily_iIndepFun (prop48_affine_fields_independent hind r z) using 1
    funext i ω
    fin_cases i <;> simp [prop48AffineFieldFamily, prop48FieldFamily]
  have hnorm : ∀ i : Fin 2, ∀ᵐ ω ∂P₀,
      circleAvg (prop48AffineFieldFamily h hIG r z i ω) r⁻¹ (-(r⁻¹ : ℂ) * z) = 0 := by
    intro i
    fin_cases i
    · simpa [prop48AffineFieldFamily, prop48FieldFamily] using
        prop48_affine_circle_normalized hh hr z
    · simpa [prop48AffineFieldFamily, prop48FieldFamily] using
        prop48_affine_circle_normalized hhIG hr z
  exact GMSAppA.lemmaA3N hp hpp₀ hs hfields hind'
    (prop48_affine_unitBall_subset hr z hsmall) hnorm hδ
    (by simpa using hδa) hF hX hXp₀

/-! ### Joint the analytic construction output

The named producer contract below records the joint form of Lemma A.2. It is proved by applying
`GMSAppA.condExp_comp_indep_of_integrable` to the pair of circle averages and the independent pair
of centered local fields, then pushing the residual-pair law through `Measure.map`. This is the
conditional input used in [18] Proposition 4.8 at and Lemma 4.9 at. -/

end MatedCRTHarmonic.GMS4
