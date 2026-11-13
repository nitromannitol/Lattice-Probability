/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.RationalAround at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.NestedAnnulus




 






set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated

 
abbrev RatData := ℚ × ℚ × ℚ × ℚ

 
def ValidRat : Type := {q : RatData // 0 < ((q.2.2.1 : ℚ) : ℝ) ∧ ((q.2.2.1 : ℚ) : ℝ) < ((q.2.2.2 : ℚ) : ℝ)}

instance : Countable ValidRat := by
  unfold ValidRat
  infer_instance

 
def ratCenter (q : RatData) : ℂ := ((q.1 : ℚ) : ℂ) + ((q.2.1 : ℚ) : ℂ) * Complex.I

 
def ratAnn (q : ValidRat) : EuclideanAnnulus :=
  ⟨(ratCenter q.1, (((q.1.2.2.1 : ℚ) : ℝ), ((q.1.2.2.2 : ℚ) : ℝ))), q.2⟩

 
def NestedIn (p : ℂ × ℝ × ℝ) (q : ValidRat) : Prop :=
  p.2.1 + dist p.1 (ratCenter q.1) < ((q.1.2.2.1 : ℚ) : ℝ) ∧
    ((q.1.2.2.2 : ℚ) : ℝ) < p.2.2 - dist p.1 (ratCenter q.1)

 
theorem exists_ratCenter_near (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℚ, dist z (((a : ℚ) : ℂ) + ((b : ℚ) : ℂ) * Complex.I) < ε := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show z.re - ε / 2 < z.re by linarith)
  obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show z.im - ε / 2 < z.im by linarith)
  refine ⟨a, b, ?_⟩
  rw [dist_comm, dist_eq_norm]
  have hre : |((((a : ℚ) : ℂ) + ((b : ℚ) : ℂ) * Complex.I) - z).re| < ε / 2 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, Complex.ratCast_re,
      Complex.ratCast_im]
    rw [abs_lt]
    constructor <;> linarith
  have him : |((((a : ℚ) : ℂ) + ((b : ℚ) : ℂ) * Complex.I) - z).im| < ε / 2 := by
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, Complex.ratCast_re, Complex.ratCast_im, zero_add, add_zero]
    rw [abs_lt]
    constructor <;> linarith
  calc ‖(((a : ℚ) : ℂ) + ((b : ℚ) : ℂ) * Complex.I) - z‖
      ≤ |((((a : ℚ) : ℂ) + ((b : ℚ) : ℂ) * Complex.I) - z).re| +
          |((((a : ℚ) : ℂ) + ((b : ℚ) : ℂ) * Complex.I) - z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ < ε / 2 + ε / 2 := add_lt_add hre him
    _ = ε := by ring

 

theorem aroundDist_eq_iInf_rational (D : LSCMetric) (A : EuclideanAnnulus) :
    aroundDist D A =
      ⨅ (q : ValidRat) (_ : NestedIn (A.center, A.innerRadius, A.outerRadius) q),
        aroundDist D (ratAnn q) := by
  apply le_antisymm
  · refine le_iInf fun q => le_iInf fun hq => ?_
    exact aroundDist_le_of_nested D A (ratAnn q) hq.1.le hq.2.le
  · refine le_of_forall_gt fun c hc => ?_
    have hc' := hc
    simp only [aroundDist, iInf_lt_iff] at hc'
    obtain ⟨P, a, b, hP, hA, hsep, hlen⟩ := hc'
    obtain ⟨η, hηpos, hη⟩ := admissible_of_close D A hP hA hsep
    have hAin : 0 < A.innerRadius := A.2.1
    have hAio : A.innerRadius < A.outerRadius := A.2.2
    set η₂ := min η ((A.outerRadius - A.innerRadius) / 2) with hη₂def
    have hgap : 0 < A.outerRadius - A.innerRadius := by linarith
    have hη₂pos : 0 < η₂ := lt_min hηpos (by linarith)
    have hη₂le : η₂ ≤ η := min_le_left _ _
    have hη₂le' : η₂ ≤ (A.outerRadius - A.innerRadius) / 2 := min_le_right _ _
    obtain ⟨qa, qb, hqab⟩ := exists_ratCenter_near A.center hη₂pos
    set x' : ℂ := ((qa : ℚ) : ℂ) + ((qb : ℚ) : ℂ) * Complex.I with hx'
    obtain ⟨ρ', hρ'₁, hρ'₂⟩ :=
      exists_rat_btwn (show A.innerRadius + dist A.center x' < A.innerRadius + η₂ by linarith)
    obtain ⟨σ', hσ'₁, hσ'₂⟩ :=
      exists_rat_btwn (show A.outerRadius - η₂ < A.outerRadius - dist A.center x' by linarith)
    have hdist0 : 0 ≤ dist A.center x' := dist_nonneg
    have hρ'pos : 0 < ((ρ' : ℚ) : ℝ) := by linarith
    have hρσ' : ((ρ' : ℚ) : ℝ) < ((σ' : ℚ) : ℝ) := by linarith
    let q : ValidRat := ⟨(qa, qb, ρ', σ'), hρ'pos, hρσ'⟩
    have hcenter : (ratAnn q).center = x' := rfl
    have hq : NestedIn (A.center, A.innerRadius, A.outerRadius) q :=
      ⟨by simpa [NestedIn, ratCenter] using hρ'₁, by simpa [NestedIn, ratCenter] using hσ'₂⟩
    have hadm := hη (ratAnn q) (by rw [hcenter]; linarith)
      (by rw [hcenter]; exact hρ'₁)
      (by change ((ρ' : ℚ) : ℝ) < A.innerRadius + η; linarith)
      (by change A.outerRadius - η < ((σ' : ℚ) : ℝ); linarith)
      (by rw [hcenter]; exact hσ'₂)
    have hle : aroundDist D (ratAnn q) ≤ D.len P a b := by
      unfold aroundDist
      exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hP <|
        iInf_le_of_le hadm.1 <| iInf_le_of_le hadm.2 le_rfl
    exact lt_of_le_of_lt ((iInf_le_of_le q (iInf_le_of_le hq le_rfl)).trans hle) hlen

 
def aroundRat (p : LSCMetric × (ℂ × ℝ × ℝ)) : ℝ≥0∞ :=
  ⨅ (q : ValidRat) (_ : NestedIn p.2 q), aroundDist p.1 (ratAnn q)

theorem aroundDist_eq_aroundRat (D : LSCMetric) (A : EuclideanAnnulus) :
    aroundDist D A = aroundRat (D, (A.center, A.innerRadius, A.outerRadius)) :=
  aroundDist_eq_iInf_rational D A

theorem isOpen_nestedIn (q : ValidRat) : IsOpen {p : ℂ × ℝ × ℝ | NestedIn p q} := by
  unfold NestedIn
  exact (isOpen_lt (continuous_snd.fst.add (continuous_fst.dist continuous_const))
    continuous_const).inter
    (isOpen_lt continuous_const (continuous_snd.snd.sub (continuous_fst.dist continuous_const)))

 
theorem measurable_aroundRat : Measurable aroundRat := by
  classical
  unfold aroundRat
  refine Measurable.iInf fun q => ?_
  have hset : MeasurableSet {p : LSCMetric × (ℂ × ℝ × ℝ) | NestedIn p.2 q} :=
    measurable_snd (isOpen_nestedIn q).measurableSet
  have hf : Measurable fun p : LSCMetric × (ℂ × ℝ × ℝ) => aroundDist p.1 (ratAnn q) :=
    (Toolkit.CountableBase.aroundBoundedAnnulus_borel (ratAnn q)).comp measurable_fst
  have heq : (fun p : LSCMetric × (ℂ × ℝ × ℝ) =>
      ⨅ (_ : NestedIn p.2 q), aroundDist p.1 (ratAnn q)) =
      fun p => if NestedIn p.2 q then aroundDist p.1 (ratAnn q) else ⊤ := by
    funext p
    exact iInf_eq_if _
  rw [heq]
  exact Measurable.ite hset hf measurable_const


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated
