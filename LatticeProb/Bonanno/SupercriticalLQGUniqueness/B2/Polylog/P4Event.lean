/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P4Event at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Costs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedProb
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.LscTop.Limits
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenHeat

 





















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP

 

lemma lfppD_eq_affine (ξ : ℝ) (φ : ℂ → ℝ) {b c : ℂ} (hc : c ≠ 0) (k : ℝ) {φ' : ℂ → ℝ}
    (hφ : ∀ x, φ' x = φ (b + c * x) + k) (z w : ℂ) :
    lfppD ξ φ' z w =
      ENNReal.ofReal (Real.exp (ξ * k) / ‖c‖) * lfppD ξ φ (b + c * z) (b + c * w) := by
  have h1 := DFGPS.lfppDOn_affine ξ φ (S := univ) (S' := univ) (b := b) (c := c) hc
    (fun _ => by simp) z w
  have h2 : lfppD ξ φ' z w = ENNReal.ofReal (Real.exp (ξ * k)) *
      lfppDOn ξ (fun x => φ (b + c * x)) univ z w := by
    have e : φ' = fun x => (fun x => φ (b + c * x)) x + k := funext hφ
    rw [e]
    unfold lfppD lfppDOn
    rw [ENNReal.mul_iInf_of_ne (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top]
    simp only [DFGPS.lfppLen_add_const]
  have hc' : (0 : ℝ) < ‖c‖ := norm_pos_iff.2 hc
  rw [h2, show lfppD ξ φ (b + c * z) (b + c * w) = lfppDOn ξ φ univ (b + c * z) (b + c * w) from rfl,
    h1, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hc'.ne']

 
theorem lfppMetric_affine (ξ : ℝ) (a a' : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} {b c : ℂ}
    (hc : c ≠ 0) (k : ℝ) (hφ : ∀ x, φ' x = φ (b + c * x) + k) (u v : ℂ) :
    Median.lfppMetric ξ a' φ' (u, v) =
      ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k) / ((a' : ℝ) * ‖c‖)) *
        Median.lfppMetric ξ a φ (b + c * u, b + c * v) := by
  have ha : (0 : ℝ) < a := a.2
  have ha' : (0 : ℝ) < a' := a'.2
  have hc' : (0 : ℝ) < ‖c‖ := norm_pos_iff.2 hc
  have he := Real.exp_pos (ξ * k)
  simp only [Median.lfppMetric_apply, LscTop.lfppDistance_eq_lfppD]
  rw [lfppD_eq_affine ξ φ hc k hφ, ← mul_assoc, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.2 ha'.le),
    ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg ha.le he.le) (mul_nonneg ha'.le hc'.le))]
  congr 2
  field_simp

 

 
def lfppScaleFactor (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε r : Set.Ioi (0 : ℝ)) : ℝ :=
  (r : ℝ) * (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2) (Set.mem_Ioi.mp r.2))⟩ : ℝ) /
    (m ε : ℝ)

lemma lfppScaleFactor_pos (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε r : Set.Ioi (0 : ℝ)) :
    0 < lfppScaleFactor m ε r := by
  unfold lfppScaleFactor
  have h1 : (0 : ℝ) < r := r.2
  have h2 : (0 : ℝ) < (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
    (Set.mem_Ioi.mp r.2))⟩ : ℝ) := (m _).2
  have h3 : (0 : ℝ) < (m ε : ℝ) := (m ε).2
  positivity

 
def plLocMetric (ξ q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε : ℝ)
    (hε : ε ∈ Ioo (0 : ℝ) 1) (g : DistC) : LSCMetric :=
  Median.lfppMetric ξ (m ⟨ε, hε.1⟩) (plMollifyC q ε hε g)

 
def normD (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (g : DistC) (z : ℂ)
    (r : Set.Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-(ξ * circleAvg g r z)))

 
def normL (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε : Set.Ioi (0 : ℝ)) (g : DistC)
    (z : ℂ) (r : Set.Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((lfppScaleFactor m ε r)⁻¹ * Real.exp (-(ξ * circleAvg g r z)))

lemma two_r_lt_three_r (r : Set.Ioi (0 : ℝ)) : 2 * (r : ℝ) < 3 * r := by
  have := r.2; simp only [mem_Ioi] at this; linarith

lemma two_r_pos (r : Set.Ioi (0 : ℝ)) : 0 < 2 * (r : ℝ) := by
  have := r.2; simp only [mem_Ioi] at this; linarith

 
def annAround (z : ℂ) (r : Set.Ioi (0 : ℝ)) : EuclideanAnnulus :=
  annAt z (2 * r) (3 * r) (two_r_pos r) (two_r_lt_three_r r)

 

def plEventLoc (ξ : ℝ) (D : DistC → LSCMetric) (c m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (q : ℝ) (z : ℂ) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (C : ℝ) :
    Set DistC :=
  {g | ENNReal.ofReal C⁻¹ ≤ normD ξ c g z r * acrossIn (D g) z r (2 * r) ∧
    normD ξ c g z r * aroundDist (D g) (annAround z r) ≤ ENNReal.ofReal C ∧
    ENNReal.ofReal C⁻¹ ≤ normL ξ m ⟨ε, hε.1⟩ g z r *
      acrossIn (plLocMetric ξ q m ε hε g) z r (2 * r) ∧
    normL ξ m ⟨ε, hε.1⟩ g z r * aroundDist (plLocMetric ξ q m ε hε g) (annAround z r) ≤
      ENNReal.ofReal C}

 

theorem measurable_plLocMetric (ξ q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε : ℝ)
    (hε : ε ∈ Ioo (0 : ℝ) 1) : Measurable (plLocMetric ξ q m ε hε) := by
  let _ : MeasurableSpace LSCFun := borel LSCFun
  have : BorelSpace LSCFun := ⟨rfl⟩
  refine LscTop.measurable_iff_toLSCFun.2 ?_
  have h1 := LscTop.measurable_rescaledLFPPFun_comp ξ (m ⟨ε, hε.1⟩)
    (X := fun g : DistC => plMollifyC q ε hε g) fun u =>
      measurable_const.mul (measurable_distOn_apply _)
  have e : (fun g => (plLocMetric ξ q m ε hε g).toLSCFun) =
      fun g => LscTop.rescaledLFPPFun ξ (m ⟨ε, hε.1⟩) (plMollifyC q ε hε g) :=
    funext fun g => Subtype.ext (by rw [plLocMetric, Median.lfppMetric_toLSCFun]; rfl)
  rw [e]
  exact h1

theorem measurable_normD (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (z : ℂ)
    (r : Set.Ioi (0 : ℝ)) : Measurable fun g => normD ξ c g z r :=
  (measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul (measurable_circleAvg_left (r : ℝ) z)).neg)).ennreal_ofReal

theorem measurable_normL (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε : Set.Ioi (0 : ℝ))
    (z : ℂ) (r : Set.Ioi (0 : ℝ)) : Measurable fun g => normL ξ m ε g z r :=
  (measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul (measurable_circleAvg_left (r : ℝ) z)).neg)).ennreal_ofReal

theorem measurableSet_plEventLoc (ξ : ℝ) {D : DistC → LSCMetric} (hD : Measurable D)
    (c m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : ℝ) (z : ℂ) (ε : ℝ)
    (hε : ε ∈ Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) (C : ℝ) :
    MeasurableSet (plEventLoc ξ D c m q z ε hε r C) := by
  have hA := (measurable_acrossIn z r (2 * r)).comp hD
  have hR := (Uniqueness.Toolkit.CountableBase.aroundBoundedAnnulus_borel (annAround z r)).comp hD
  have hL := measurable_plLocMetric ξ q m ε hε
  have hAL := (measurable_acrossIn z r (2 * r)).comp hL
  have hRL := (Uniqueness.Toolkit.CountableBase.aroundBoundedAnnulus_borel (annAround z r)).comp hL
  have hnD := measurable_normD ξ c z r
  have hnL := measurable_normL ξ m ⟨ε, hε.1⟩ z r
  have hc1 : Measurable fun _ : DistC => ENNReal.ofReal C⁻¹ := measurable_const
  have hc2 : Measurable fun _ : DistC => ENNReal.ofReal C := measurable_const
  have h := ((measurableSet_le hc1 (hnD.mul hA)).inter
    (measurableSet_le (hnD.mul hR) hc2)).inter
    (((measurableSet_le hc1 (hnL.mul hAL)).inter
    (measurableSet_le (hnL.mul hRL) hc2)))
  convert h using 1
  ext g
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

 

 


theorem ae_addConst_eq_mul_of_pfe {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P) {ξ : Set.Ioi (0 : ℝ)}
    {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : Iface.IsPfeWeakMetric ξ D c) (k : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ p : ℂ × ℂ,
      D (addConst (h ω) (k ω)) p = ENNReal.ofReal (Real.exp ((ξ : ℝ) * k ω)) * D (h ω) p := by
  filter_upwards [hD.2.2.2.1 P h hh, hD.2.1 P h hh] with ω hw hl p
  have hqw := congrFun (hw (ContinuousMap.const ℂ (k ω))) p
  change weylScale (ξ : ℝ) (ContinuousMap.const ℂ (k ω)) (D (h ω)) p =
    D (addConst (h ω) (k ω)) p at hqw
  exact hqw.symm.trans (Uniqueness.Positivity.Witnesses.weylScale_const (ξ : ℝ) (k ω) (D (h ω)) hl p)

lemma testTranslate_plTest (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (z u : ℂ) :
    testTranslate z (plTest q ε hε u) = plTest q ε hε (u + z) := by
  ext x
  show plTest q ε hε u (x - z) = plTest q ε hε (u + z) x
  rw [plTest_apply, plTest_apply]
  congr 1
  · congr 1; ring
  · unfold heatKernel
    congr 3
    rw [show u - (x - z) = u + z - x by ring]

 
theorem plMollify_translateDist (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (g : DistC) (z u : ℂ) :
    plMollify q ε hε (translateDist z g) u = plMollify q ε hε g (u + z) := by
  show (plZ q ε hε)⁻¹ * g (testTranslate z (plTest q ε hε u)) = (plZ q ε hε)⁻¹ * g (plTest q ε hε (u + z))
  rw [testTranslate_plTest]

 
def recenter (z : ℂ) (g : DistC) : DistC := addConst (translateDist z g) (-circleAvg g 1 z)

theorem plMollify_recenter (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (g : DistC) (z u : ℂ) :
    plMollify q ε hε (recenter z g) u = plMollify q ε hε g (z + 1 * u) + -circleAvg g 1 z := by
  rw [recenter, plMollify_addConst, plMollify_translateDist, one_mul, add_comm z u]

 
theorem plLocMetric_recenter (ξ q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε : ℝ)
    (hε : ε ∈ Ioo (0 : ℝ) 1) (g : DistC) (z : ℂ) (x y : ℂ) :
    plLocMetric ξ q m ε hε (recenter z g) (x, y) =
      ENNReal.ofReal (Real.exp (ξ * -circleAvg g 1 z)) * plLocMetric ξ q m ε hε g (x + z, y + z) := by
  unfold plLocMetric
  rw [lfppMetric_affine ξ (m ⟨ε, hε.1⟩) (m ⟨ε, hε.1⟩) (φ := plMollifyC q ε hε g)
    (φ' := plMollifyC q ε hε (recenter z g)) (b := z) (c := 1) one_ne_zero
    (-circleAvg g 1 z) (fun u => plMollify_recenter q ε hε g z u) x y]
  have hm := (m ⟨ε, hε.1⟩).2
  simp only [mem_Ioi] at hm
  rw [norm_one, mul_one, mul_div_cancel_left₀ _ hm.ne', one_mul, one_mul, add_comm z x,
    add_comm z y]

end SupercriticalLQGUniqueness.B2.Polylog
