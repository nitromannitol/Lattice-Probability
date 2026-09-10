/-
The splice average and the martingale decomposition of a covariance.

Taken into the library from the parking model's support files, where it was
developed: the splicing framework is generic (an arbitrary probability space
and a family of splicing maps measure preserving for two independent copies),
and every model that reveals randomness one coordinate at a time and bounds a
covariance by the increments of a filtration uses it.
-/
import Mathlib

open MeasureTheory

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The average of `F` over the second argument of a splicing map: the value of
`F` on the configuration that reads `ω` on the revealed part of the randomness
and an independent copy `η` on the rest. -/
def spInt (P : Measure Ω) (c : Ω → Ω → Ω) (F : Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ η, F (c ω η) ∂P

omit [IsProbabilityMeasure P] in
/-- Splicing carries an integrable functional to an integrable functional of the
pair. -/
theorem integrable_comp_splice {c : Ω → Ω → Ω}
    (hmp : MeasurePreserving (fun p : Ω × Ω => c p.1 p.2) (P.prod P) P)
    {F : Ω → ℝ} (hF : Integrable F P) :
    Integrable (fun p : Ω × Ω => F (c p.1 p.2)) (P.prod P) :=
  hmp.integrable_comp_of_integrable hF

/-- The splice average of an integrable functional is integrable. -/
theorem integrable_spInt {c : Ω → Ω → Ω}
    (hmp : MeasurePreserving (fun p : Ω × Ω => c p.1 p.2) (P.prod P) P)
    {F : Ω → ℝ} (hF : Integrable F P) :
    Integrable (spInt P c F) P :=
  (integrable_comp_splice hmp hF).integral_prod_left

/-- The splice average has the same mean as the functional. -/
theorem integral_spInt {c : Ω → Ω → Ω}
    (hmp : MeasurePreserving (fun p : Ω × Ω => c p.1 p.2) (P.prod P) P)
    {F : Ω → ℝ} (hF : Integrable F P) :
    ∫ ω, spInt P c F ω ∂P = ∫ ω, F ω ∂P := by
  have hmap := hmp.map_eq
  have hasm : AEStronglyMeasurable F
      (Measure.map (fun p : Ω × Ω => c p.1 p.2) (P.prod P)) := by
    rw [hmap]; exact hF.aestronglyMeasurable
  have h : ∫ p, F (c p.1 p.2) ∂(P.prod P) = ∫ ω, F ω ∂P := by
    rw [← integral_map hmp.measurable.aemeasurable hasm, hmap]
  rw [← h, integral_prod _ (integrable_comp_splice hmp hF)]
  rfl

/-- **The defining property of the splice average.**  Against a functional the
splicing does not change, the splice average and the functional itself have the
same integral.  Holding for every such multiplier is the statement that the
splice average is the conditional expectation on the revealed randomness. -/
theorem integral_mul_spInt {c : Ω → Ω → Ω}
    (hmp : MeasurePreserving (fun p : Ω × Ω => c p.1 p.2) (P.prod P) P)
    {F g : Ω → ℝ} (hg : ∀ ω η : Ω, g (c ω η) = g ω)
    (hgF : Integrable (fun ω => g ω * F ω) P) :
    ∫ ω, g ω * spInt P c F ω ∂P = ∫ ω, g ω * F ω ∂P := by
  have hkey : Integrable (fun p : Ω × Ω => g (c p.1 p.2) * F (c p.1 p.2)) (P.prod P) :=
    integrable_comp_splice hmp hgF
  have hrw : (fun p : Ω × Ω => g (c p.1 p.2) * F (c p.1 p.2))
      = fun p : Ω × Ω => g p.1 * F (c p.1 p.2) := by
    funext p; rw [hg]
  rw [hrw] at hkey
  have h1 : ∫ p, g p.1 * F (c p.1 p.2) ∂(P.prod P)
      = ∫ ω, g ω * spInt P c F ω ∂P := by
    rw [integral_prod _ hkey]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only []
      rw [integral_const_mul]
      rfl)
  have h2 : ∫ p, g (c p.1 p.2) * F (c p.1 p.2) ∂(P.prod P) = ∫ ω, g ω * F ω ∂P := by
    have hmap := hmp.map_eq
    have hasm : AEStronglyMeasurable (fun ω => g ω * F ω)
        (Measure.map (fun p : Ω × Ω => c p.1 p.2) (P.prod P)) := by
      rw [hmap]; exact hgF.aestronglyMeasurable
    rw [← integral_map hmp.measurable.aemeasurable hasm, hmap]
  rw [← h1, ← h2, hrw]

omit [IsProbabilityMeasure P] in
/-- The splice average of a measurable functional is measurable. -/
theorem measurable_spInt [SFinite P] {c : Ω → Ω → Ω}
    (hc : Measurable fun p : Ω × Ω => c p.1 p.2) {F : Ω → ℝ} (hF : Measurable F) :
    Measurable (spInt P c F) :=
  ((hF.comp hc).stronglyMeasurable.integral_prod_right' (ν := P)).measurable

/-- The splice average of a functional bounded by `B` is bounded by `B`. -/
theorem abs_spInt_le {c : Ω → Ω → Ω} {F : Ω → ℝ} {B : ℝ} (hF : ∀ ω, |F ω| ≤ B) (ω : Ω) :
    |spInt P c F ω| ≤ B := by
  have h : ∀ᵐ η ∂P, ‖F (c ω η)‖ ≤ B := Filter.Eventually.of_forall fun η => hF (c ω η)
  simpa [spInt, Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (μ := P) h

/-- **The exchange step.**  Against the average over the smaller part of the
randomness, enlarging the revealed part does not change the integral.  This is
what makes the increments of the filtration orthogonal. -/
theorem integral_spInt_mul_spInt {cS cT : Ω → Ω → Ω}
    (hS : MeasurePreserving (fun p : Ω × Ω => cS p.1 p.2) (P.prod P) P)
    (hT : MeasurePreserving (fun p : Ω × Ω => cT p.1 p.2) (P.prod P) P)
    (hSS : ∀ ω η η' : Ω, cS (cS ω η) η' = cS ω η')
    (hST : ∀ ω η η' : Ω, cS (cT ω η) η' = cS ω η')
    {F Z : Ω → ℝ} (hFm : Measurable F) (hFb : ∀ ω, |F ω| ≤ 1)
    (hZi : Integrable Z P) :
    ∫ ω, spInt P cT F ω * spInt P cS Z ω ∂P
      = ∫ ω, spInt P cS F ω * spInt P cS Z ω ∂P := by
  have hgT : ∀ ω η : Ω, spInt P cS Z (cT ω η) = spInt P cS Z ω := by
    intro ω η
    unfold spInt
    simp only [hST]
  have hgS : ∀ ω η : Ω, spInt P cS Z (cS ω η) = spInt P cS Z ω := by
    intro ω η
    unfold spInt
    simp only [hSS]
  have hgi : Integrable (spInt P cS Z) P := integrable_spInt hS hZi
  have hbound : ∀ᵐ ω ∂P, ‖F ω‖ ≤ 1 :=
    Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hFb ω
  have hgF : Integrable (fun ω => spInt P cS Z ω * F ω) P :=
    hgi.mul_bdd hFm.aestronglyMeasurable hbound
  have h1 : ∫ ω, spInt P cS Z ω * spInt P cT F ω ∂P = ∫ ω, spInt P cS Z ω * F ω ∂P :=
    integral_mul_spInt hT hgT hgF
  have h2 : ∫ ω, spInt P cS Z ω * spInt P cS F ω ∂P = ∫ ω, spInt P cS Z ω * F ω ∂P :=
    integral_mul_spInt hS hgS hgF
  calc ∫ ω, spInt P cT F ω * spInt P cS Z ω ∂P
      = ∫ ω, spInt P cS Z ω * spInt P cT F ω ∂P := by simp_rw [mul_comm]
    _ = ∫ ω, spInt P cS Z ω * F ω ∂P := h1
    _ = ∫ ω, spInt P cS Z ω * spInt P cS F ω ∂P := h2.symm
    _ = ∫ ω, spInt P cS F ω * spInt P cS Z ω ∂P := by simp_rw [mul_comm]

/-- **The exchange step, the other way round.**  Against the average of a
BOUNDED functional over the smaller part of the randomness, enlarging the
revealed part of an integrable functional does not change the integral. -/
theorem integral_spInt_mul_spInt' {cS cT : Ω → Ω → Ω}
    (hS : MeasurePreserving (fun p : Ω × Ω => cS p.1 p.2) (P.prod P) P)
    (hT : MeasurePreserving (fun p : Ω × Ω => cT p.1 p.2) (P.prod P) P)
    (hSS : ∀ ω η η' : Ω, cS (cS ω η) η' = cS ω η')
    (hST : ∀ ω η η' : Ω, cS (cT ω η) η' = cS ω η')
    {F Z : Ω → ℝ} (hFm : Measurable F) (hFb : ∀ ω, |F ω| ≤ 1)
    (hZi : Integrable Z P) :
    ∫ ω, spInt P cS F ω * spInt P cT Z ω ∂P
      = ∫ ω, spInt P cS F ω * spInt P cS Z ω ∂P := by
  have hgT : ∀ ω η : Ω, spInt P cS F (cT ω η) = spInt P cS F ω := by
    intro ω η
    unfold spInt
    simp only [hST]
  have hgS : ∀ ω η : Ω, spInt P cS F (cS ω η) = spInt P cS F ω := by
    intro ω η
    unfold spInt
    simp only [hSS]
  have hgm : Measurable (spInt P cS F) := measurable_spInt hS.measurable hFm
  have hbound : ∀ᵐ ω ∂P, ‖spInt P cS F ω‖ ≤ 1 :=
    Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using abs_spInt_le (P := P) (c := cS) hFb ω
  have hgZ : Integrable (fun ω => spInt P cS F ω * Z ω) P :=
    hZi.bdd_mul hgm.aestronglyMeasurable hbound
  have h1 : ∫ ω, spInt P cS F ω * spInt P cT Z ω ∂P = ∫ ω, spInt P cS F ω * Z ω ∂P :=
    integral_mul_spInt hT hgT hgZ
  have h2 : ∫ ω, spInt P cS F ω * spInt P cS Z ω ∂P = ∫ ω, spInt P cS F ω * Z ω ∂P :=
    integral_mul_spInt hS hgS hgZ
  rw [h1, h2]

/-- **One step of the martingale decomposition of a covariance.**  Revealing more
of the randomness raises the integral of the product of the two averages by
exactly the integral of the product of the two increments: the increments of the
two filtrations are orthogonal across the step. -/
theorem integral_spInt_step {cS cT : Ω → Ω → Ω}
    (hS : MeasurePreserving (fun p : Ω × Ω => cS p.1 p.2) (P.prod P) P)
    (hT : MeasurePreserving (fun p : Ω × Ω => cT p.1 p.2) (P.prod P) P)
    (hSS : ∀ ω η η' : Ω, cS (cS ω η) η' = cS ω η')
    (hST : ∀ ω η η' : Ω, cS (cT ω η) η' = cS ω η')
    {F Z : Ω → ℝ} (hFm : Measurable F) (hFb : ∀ ω, |F ω| ≤ 1)
    (hZi : Integrable Z P) :
    ∫ ω, (spInt P cT F ω - spInt P cS F ω) * (spInt P cT Z ω - spInt P cS Z ω) ∂P
      = (∫ ω, spInt P cT F ω * spInt P cT Z ω ∂P)
        - ∫ ω, spInt P cS F ω * spInt P cS Z ω ∂P := by
  have hTFm : Measurable (spInt P cT F) := measurable_spInt hT.measurable hFm
  have hSFm : Measurable (spInt P cS F) := measurable_spInt hS.measurable hFm
  have hTFb : ∀ᵐ ω ∂P, ‖spInt P cT F ω‖ ≤ 1 :=
    Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using abs_spInt_le (P := P) (c := cT) hFb ω
  have hSFb : ∀ᵐ ω ∂P, ‖spInt P cS F ω‖ ≤ 1 :=
    Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using abs_spInt_le (P := P) (c := cS) hFb ω
  have hTZ : Integrable (spInt P cT Z) P := integrable_spInt hT hZi
  have hSZ : Integrable (spInt P cS Z) P := integrable_spInt hS hZi
  have i11 : Integrable (fun ω => spInt P cT F ω * spInt P cT Z ω) P :=
    hTZ.bdd_mul hTFm.aestronglyMeasurable hTFb
  have i12 : Integrable (fun ω => spInt P cT F ω * spInt P cS Z ω) P :=
    hSZ.bdd_mul hTFm.aestronglyMeasurable hTFb
  have i21 : Integrable (fun ω => spInt P cS F ω * spInt P cT Z ω) P :=
    hTZ.bdd_mul hSFm.aestronglyMeasurable hSFb
  have i22 : Integrable (fun ω => spInt P cS F ω * spInt P cS Z ω) P :=
    hSZ.bdd_mul hSFm.aestronglyMeasurable hSFb
  have hexp : ∀ ω : Ω,
      (spInt P cT F ω - spInt P cS F ω) * (spInt P cT Z ω - spInt P cS Z ω)
        = spInt P cT F ω * spInt P cT Z ω - spInt P cT F ω * spInt P cS Z ω
          - spInt P cS F ω * spInt P cT Z ω + spInt P cS F ω * spInt P cS Z ω := by
    intro ω; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  have i1 : Integrable (fun ω => spInt P cT F ω * spInt P cT Z ω
      - spInt P cT F ω * spInt P cS Z ω) P := i11.sub i12
  have i2 : Integrable (fun ω => spInt P cT F ω * spInt P cT Z ω
      - spInt P cT F ω * spInt P cS Z ω - spInt P cS F ω * spInt P cT Z ω) P := i1.sub i21
  rw [integral_add i2 i22, integral_sub i1 i21, integral_sub i11 i12]
  rw [integral_spInt_mul_spInt hS hT hSS hST hFm hFb hZi]
  rw [integral_spInt_mul_spInt' hS hT hSS hST hFm hFb hZi]
  ring

/-- **The martingale decomposition along a finite filtration.**  The covariance
of the two averages over the last stage of the filtration exceeds the covariance
over the first stage by the sum, over the stages, of the integrals of the
products of the two increments. -/
theorem integral_spInt_telescope (c : ℕ → Ω → Ω → Ω)
    (hmp : ∀ i, MeasurePreserving (fun p : Ω × Ω => c i p.1 p.2) (P.prod P) P)
    (hidem : ∀ (i : ℕ) (ω η η' : Ω), c i (c i ω η) η' = c i ω η')
    (hstep : ∀ (i : ℕ) (ω η η' : Ω), c i (c (i + 1) ω η) η' = c i ω η')
    {F Z : Ω → ℝ} (hFm : Measurable F) (hFb : ∀ ω, |F ω| ≤ 1)
    (hZi : Integrable Z P) (n : ℕ) :
    (∫ ω, spInt P (c n) F ω * spInt P (c n) Z ω ∂P)
        - ∫ ω, spInt P (c 0) F ω * spInt P (c 0) Z ω ∂P
      = ∑ i ∈ Finset.range n,
          ∫ ω, (spInt P (c (i + 1)) F ω - spInt P (c i) F ω)
            * (spInt P (c (i + 1)) Z ω - spInt P (c i) Z ω) ∂P := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hstepm := integral_spInt_step (P := P) (cS := c m) (cT := c (m + 1))
        (hmp m) (hmp (m + 1)) (hidem m) (hstep m) hFm hFb hZi
      rw [hstepm]
      ring

/-- **The covariance as a sum over the stages of the filtration.**  When the
first stage reveals nothing and the last reveals everything, the martingale
decomposition is a decomposition of the covariance itself. -/
theorem cov_eq_sum_spInt (c : ℕ → Ω → Ω → Ω) (n : ℕ)
    (hmp : ∀ i, MeasurePreserving (fun p : Ω × Ω => c i p.1 p.2) (P.prod P) P)
    (hidem : ∀ (i : ℕ) (ω η η' : Ω), c i (c i ω η) η' = c i ω η')
    (hstep : ∀ (i : ℕ) (ω η η' : Ω), c i (c (i + 1) ω η) η' = c i ω η')
    {F Z : Ω → ℝ}
    (hF0 : ∀ ω : Ω, spInt P (c 0) F ω = ∫ η, F η ∂P)
    (hZ0 : ∀ ω : Ω, spInt P (c 0) Z ω = ∫ η, Z η ∂P)
    (hFn : ∀ ω : Ω, spInt P (c n) F ω = F ω) (hZn : ∀ ω : Ω, spInt P (c n) Z ω = Z ω)
    (hFm : Measurable F) (hFb : ∀ ω, |F ω| ≤ 1)
    (hZi : Integrable Z P) :
    (∫ ω, F ω * Z ω ∂P) - (∫ ω, F ω ∂P) * ∫ ω, Z ω ∂P
      = ∑ i ∈ Finset.range n,
          ∫ ω, (spInt P (c (i + 1)) F ω - spInt P (c i) F ω)
            * (spInt P (c (i + 1)) Z ω - spInt P (c i) Z ω) ∂P := by
  have hmain := integral_spInt_telescope (P := P) c hmp hidem hstep hFm hFb hZi n
  simp only [hF0, hZ0, hFn, hZn] at hmain
  rw [← hmain]
  simp

/-- **The covariance bound.**  When every increment of `Z` along the filtration
is at most one, the covariance is at most the sum of the mean absolute
increments of `F`.  This is the inequality Step 2 of `lem:product` applies with
the deletion bound `|D_i Z| ≤ 1`. -/
theorem abs_cov_le_sum_abs_spInt (c : ℕ → Ω → Ω → Ω) (n : ℕ)
    (hmp : ∀ i, MeasurePreserving (fun p : Ω × Ω => c i p.1 p.2) (P.prod P) P)
    (hidem : ∀ (i : ℕ) (ω η η' : Ω), c i (c i ω η) η' = c i ω η')
    (hstep : ∀ (i : ℕ) (ω η η' : Ω), c i (c (i + 1) ω η) η' = c i ω η')
    {F Z : Ω → ℝ}
    (hF0 : ∀ ω : Ω, spInt P (c 0) F ω = ∫ η, F η ∂P)
    (hZ0 : ∀ ω : Ω, spInt P (c 0) Z ω = ∫ η, Z η ∂P)
    (hFn : ∀ ω : Ω, spInt P (c n) F ω = F ω) (hZn : ∀ ω : Ω, spInt P (c n) Z ω = Z ω)
    (hFm : Measurable F) (hFb : ∀ ω, |F ω| ≤ 1)
    (hZi : Integrable Z P)
    (hDZ : ∀ i < n, ∀ᵐ ω ∂P, |spInt P (c (i + 1)) Z ω - spInt P (c i) Z ω| ≤ 1) :
    |(∫ ω, F ω * Z ω ∂P) - (∫ ω, F ω ∂P) * ∫ ω, Z ω ∂P|
      ≤ ∑ i ∈ Finset.range n,
          ∫ ω, |spInt P (c (i + 1)) F ω - spInt P (c i) F ω| ∂P := by
  have habs : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    simpa [sub_eq_add_neg] using abs_add_le x (-y)
  rw [cov_eq_sum_spInt (P := P) c n hmp hidem hstep hF0 hZ0 hFn hZn hFm hFb hZi]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hFim : Measurable (fun ω => spInt P (c (i + 1)) F ω - spInt P (c i) F ω) :=
    (measurable_spInt (hmp (i + 1)).measurable hFm).sub
      (measurable_spInt (hmp i).measurable hFm)
  have hFib : ∀ ω : Ω, |spInt P (c (i + 1)) F ω - spInt P (c i) F ω| ≤ 2 := by
    intro ω
    calc |spInt P (c (i + 1)) F ω - spInt P (c i) F ω|
        ≤ |spInt P (c (i + 1)) F ω| + |spInt P (c i) F ω| := habs _ _
      _ ≤ 1 + 1 :=
          add_le_add (abs_spInt_le (P := P) (c := c (i + 1)) hFb ω)
            (abs_spInt_le (P := P) (c := c i) hFb ω)
      _ = 2 := by norm_num
  have hFiInt : Integrable (fun ω => spInt P (c (i + 1)) F ω - spInt P (c i) F ω) P :=
    (integrable_const (2 : ℝ)).mono' hFim.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hFib ω)
  have hZinc : Integrable (fun ω => spInt P (c (i + 1)) Z ω - spInt P (c i) Z ω) P :=
    (integrable_spInt (hmp (i + 1)) hZi).sub (integrable_spInt (hmp i) hZi)
  have hprod : Integrable (fun ω =>
      (spInt P (c (i + 1)) F ω - spInt P (c i) F ω)
        * (spInt P (c (i + 1)) Z ω - spInt P (c i) Z ω)) P :=
    hZinc.bdd_mul hFim.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hFib ω)
  calc |∫ ω, (spInt P (c (i + 1)) F ω - spInt P (c i) F ω)
          * (spInt P (c (i + 1)) Z ω - spInt P (c i) Z ω) ∂P|
      ≤ ∫ ω, |(spInt P (c (i + 1)) F ω - spInt P (c i) F ω)
          * (spInt P (c (i + 1)) Z ω - spInt P (c i) Z ω)| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, |spInt P (c (i + 1)) F ω - spInt P (c i) F ω| ∂P := by
        refine integral_mono_ae hprod.abs hFiInt.abs ?_
        filter_upwards [hDZ i hin] with ω hω
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hω

omit [IsProbabilityMeasure P] in
/-- A splicing that keeps nothing averages over everything. -/
theorem spInt_of_snd {c : Ω → Ω → Ω} (hc : ∀ ω η : Ω, c ω η = η) (F : Ω → ℝ) (ω : Ω) :
    spInt P c F ω = ∫ η, F η ∂P := by
  unfold spInt
  simp only [hc]

/-- A splicing that keeps everything changes nothing. -/
theorem spInt_of_fst {c : Ω → Ω → Ω} (hc : ∀ ω η : Ω, c ω η = ω) (F : Ω → ℝ) (ω : Ω) :
    spInt P c F ω = F ω := by
  unfold spInt
  simp only [hc, integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- **The deletion bound on an increment.**  If a comparison functional `W`
does not see the randomness the step reveals and lies within one above `Z`, the
increment of the average of `Z` across the step is at most one. -/
theorem abs_spInt_sub_le_one {cS cT : Ω → Ω → Ω} {Z W : Ω → ℝ}
    (hW : ∀ ω η : Ω, W (cT ω η) = W (cS ω η))
    (hZW : ∀ ω : Ω, 0 ≤ W ω - Z ω) (hZW1 : ∀ ω : Ω, W ω - Z ω ≤ 1)
    (ω : Ω)
    (hZS : Integrable (fun η => Z (cS ω η)) P)
    (hZT : Integrable (fun η => Z (cT ω η)) P)
    (hWS : Integrable (fun η => W (cS ω η)) P)
    (hWT : Integrable (fun η => W (cT ω η)) P) :
    |spInt P cT Z ω - spInt P cS Z ω| ≤ 1 := by
  have key : ∀ c : Ω → Ω → Ω, Integrable (fun η => Z (c ω η)) P →
      Integrable (fun η => W (c ω η)) P →
      spInt P c Z ω - spInt P c W ω ∈ Set.Icc (-1 : ℝ) 0 := by
    intro c hZc hWc
    have hsub : spInt P c Z ω - spInt P c W ω = ∫ η, (Z (c ω η) - W (c ω η)) ∂P := by
      unfold spInt
      rw [integral_sub hZc hWc]
    constructor
    · rw [hsub]
      have hb : ∀ η : Ω, (-1 : ℝ) ≤ Z (c ω η) - W (c ω η) := by
        intro η; have := hZW1 (c ω η); linarith
      calc (-1 : ℝ) = ∫ _η : Ω, (-1 : ℝ) ∂P := by simp
        _ ≤ ∫ η, (Z (c ω η) - W (c ω η)) ∂P :=
            integral_mono (integrable_const _) (hZc.sub hWc) hb
    · rw [hsub]
      have hb : ∀ η : Ω, Z (c ω η) - W (c ω η) ≤ 0 := by
        intro η; have := hZW (c ω η); linarith
      calc ∫ η, (Z (c ω η) - W (c ω η)) ∂P ≤ ∫ _η : Ω, (0 : ℝ) ∂P :=
            integral_mono (hZc.sub hWc) (integrable_const _) hb
        _ = 0 := by simp
  have hWeq : spInt P cT W ω = spInt P cS W ω := by
    unfold spInt
    simp only [hW]
  obtain ⟨hT1, hT2⟩ := key cT hZT hWT
  obtain ⟨hS1, hS2⟩ := key cS hZS hWS
  rw [abs_le]
  constructor <;> linarith

/-- **The symmetrization bound on an increment.** -/
theorem integral_abs_spInt_sub_le {cS cT : Ω → Ω → Ω}
    (hS : MeasurePreserving (fun p : Ω × Ω => cS p.1 p.2) (P.prod P) P)
    (hT : MeasurePreserving (fun p : Ω × Ω => cT p.1 p.2) (P.prod P) P)
    {F V : Ω → ℝ}
    (hV : ∀ ω η : Ω, V (cT ω η) = V (cS ω η))
    (hFV : ∀ ω : Ω, 0 ≤ F ω - V ω)
    (hFi : Integrable F P) (hVi : Integrable V P)
    (hFS : ∀ ω : Ω, Integrable (fun η => F (cS ω η)) P)
    (hFT : ∀ ω : Ω, Integrable (fun η => F (cT ω η)) P)
    (hVS : ∀ ω : Ω, Integrable (fun η => V (cS ω η)) P)
    (hVT : ∀ ω : Ω, Integrable (fun η => V (cT ω η)) P) :
    ∫ ω, |spInt P cT F ω - spInt P cS F ω| ∂P ≤ 2 * ∫ ω, (F ω - V ω) ∂P := by
  have hGi : Integrable (fun ω => F ω - V ω) P := hFi.sub hVi
  have hsubS : ∀ ω : Ω,
      spInt P cS F ω - spInt P cS V ω = spInt P cS (fun x => F x - V x) ω := by
    intro ω
    unfold spInt
    rw [← integral_sub (hFS ω) (hVS ω)]
  have hsubT : ∀ ω : Ω,
      spInt P cT F ω - spInt P cT V ω = spInt P cT (fun x => F x - V x) ω := by
    intro ω
    unfold spInt
    rw [← integral_sub (hFT ω) (hVT ω)]
  have hVeq : ∀ ω : Ω, spInt P cT V ω = spInt P cS V ω := by
    intro ω
    unfold spInt
    simp only [hV]
  have hnonnegS : ∀ ω : Ω, 0 ≤ spInt P cS (fun x => F x - V x) ω := fun ω =>
    integral_nonneg fun η => hFV (cS ω η)
  have hnonnegT : ∀ ω : Ω, 0 ≤ spInt P cT (fun x => F x - V x) ω := fun ω =>
    integral_nonneg fun η => hFV (cT ω η)
  have hpt : ∀ ω : Ω, |spInt P cT F ω - spInt P cS F ω|
      ≤ spInt P cT (fun x => F x - V x) ω + spInt P cS (fun x => F x - V x) ω := by
    intro ω
    have h1 := hsubT ω
    have h2 := hsubS ω
    have h3 := hVeq ω
    have h4 := hnonnegT ω
    have h5 := hnonnegS ω
    rw [abs_le]
    constructor <;> linarith
  have hleft : Integrable (fun ω => |spInt P cT F ω - spInt P cS F ω|) P :=
    ((integrable_spInt hT hFi).sub (integrable_spInt hS hFi)).abs
  have hright : Integrable (fun ω => spInt P cT (fun x => F x - V x) ω
      + spInt P cS (fun x => F x - V x) ω) P :=
    (integrable_spInt hT hGi).add (integrable_spInt hS hGi)
  calc ∫ ω, |spInt P cT F ω - spInt P cS F ω| ∂P
      ≤ ∫ ω, (spInt P cT (fun x => F x - V x) ω
          + spInt P cS (fun x => F x - V x) ω) ∂P := integral_mono hleft hright hpt
    _ = (∫ ω, spInt P cT (fun x => F x - V x) ω ∂P)
          + ∫ ω, spInt P cS (fun x => F x - V x) ω ∂P :=
        integral_add (integrable_spInt hT hGi) (integrable_spInt hS hGi)
    _ = 2 * ∫ ω, (F ω - V ω) ∂P := by
        rw [integral_spInt hT hGi, integral_spInt hS hGi]; ring

/-- **The deletion bound almost everywhere.**  The sections of an integrable
functional along a measure preserving splicing are integrable for almost every
configuration, so the pointwise deletion bound holds almost everywhere. -/
theorem abs_spInt_sub_le_one_ae {cS cT : Ω → Ω → Ω}
    (hS : MeasurePreserving (fun p : Ω × Ω => cS p.1 p.2) (P.prod P) P)
    (hT : MeasurePreserving (fun p : Ω × Ω => cT p.1 p.2) (P.prod P) P)
    {Z W : Ω → ℝ}
    (hW : ∀ ω η : Ω, W (cT ω η) = W (cS ω η))
    (hZW : ∀ ω : Ω, 0 ≤ W ω - Z ω) (hZW1 : ∀ ω : Ω, W ω - Z ω ≤ 1)
    (hZi : Integrable Z P) (hWi : Integrable W P) :
    ∀ᵐ ω ∂P, |spInt P cT Z ω - spInt P cS Z ω| ≤ 1 := by
  have h1 := (integrable_comp_splice hS hZi).prod_right_ae
  have h2 := (integrable_comp_splice hT hZi).prod_right_ae
  have h3 := (integrable_comp_splice hS hWi).prod_right_ae
  have h4 := (integrable_comp_splice hT hWi).prod_right_ae
  filter_upwards [h1, h2, h3, h4] with ω k1 k2 k3 k4
  exact abs_spInt_sub_le_one hW hZW hZW1 ω k1 k2 k3 k4

/-- **The symmetrization bound for bounded functionals.**  For a functional
bounded by one, every integrability side condition of the symmetrization bound
follows from measurability. -/
theorem integral_abs_spInt_sub_le_of_bdd {cS cT : Ω → Ω → Ω}
    (hS : MeasurePreserving (fun p : Ω × Ω => cS p.1 p.2) (P.prod P) P)
    (hT : MeasurePreserving (fun p : Ω × Ω => cT p.1 p.2) (P.prod P) P)
    {F V : Ω → ℝ} (hFm : Measurable F) (hVm : Measurable V)
    (hFb : ∀ ω, |F ω| ≤ 1) (hVb : ∀ ω, |V ω| ≤ 1)
    (hV : ∀ ω η : Ω, V (cT ω η) = V (cS ω η)) (hFV : ∀ ω, 0 ≤ F ω - V ω) :
    ∫ ω, |spInt P cT F ω - spInt P cS F ω| ∂P ≤ 2 * ∫ ω, (F ω - V ω) ∂P := by
  have hsec : ∀ c : Ω → Ω → Ω, Measurable (fun p : Ω × Ω => c p.1 p.2) →
      ∀ ω : Ω, Measurable (fun η => c ω η) :=
    fun c hc ω => hc.comp (measurable_const.prodMk measurable_id)
  have hbdd : ∀ G : Ω → ℝ, Measurable G → (∀ ω, |G ω| ≤ 1) → Integrable G P := by
    intro G hGm hGb
    exact (integrable_const (1 : ℝ)).mono' hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hGb ω)
  exact integral_abs_spInt_sub_le hS hT hV hFV (hbdd F hFm hFb) (hbdd V hVm hVb)
    (fun ω => hbdd _ (hFm.comp (hsec cS hS.measurable ω)) (fun η => hFb _))
    (fun ω => hbdd _ (hFm.comp (hsec cT hT.measurable ω)) (fun η => hFb _))
    (fun ω => hbdd _ (hVm.comp (hsec cS hS.measurable ω)) (fun η => hVb _))
    (fun ω => hbdd _ (hVm.comp (hsec cT hT.measurable ω)) (fun η => hVb _))



theorem measurePreserving_pairSplice {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    (μB : Measure B) (μC : Measure C) [IsProbabilityMeasure μB] [IsProbabilityMeasure μC]
    {cB : B → B → B} {cC : C → C → C}
    (hB : MeasurePreserving (fun p : B × B => cB p.1 p.2) (μB.prod μB) μB)
    (hC : MeasurePreserving (fun p : C × C => cC p.1 p.2) (μC.prod μC) μC) :
    MeasurePreserving (fun p : (B × C) × (B × C) => (cB p.1.1 p.2.1, cC p.1.2 p.2.2))
      ((μB.prod μC).prod (μB.prod μC)) (μB.prod μC) := by
  -- the shuffle e : ((b1,c1),(b2,c2)) ↦ ((b1,b2),(c1,c2)) as a composition of
  -- assoc / swap maps, each measure preserving.
  have h1 : MeasurePreserving (fun p : (B × C) × (B × C) => (p.1.1, (p.1.2, (p.2.1, p.2.2))))
      ((μB.prod μC).prod (μB.prod μC)) (μB.prod (μC.prod (μB.prod μC))) :=
    measurePreserving_prodAssoc _ _ _
  have h2 : MeasurePreserving (Prod.map id (Prod.swap : C × (B × C) → (B × C) × C))
      (μB.prod (μC.prod (μB.prod μC))) (μB.prod ((μB.prod μC).prod μC)) := by
    refine MeasurePreserving.prod (MeasurePreserving.id _) ?_
    exact ⟨measurable_swap, Measure.prod_swap⟩
  have h3 : MeasurePreserving (Prod.map id (⇑(MeasurableEquiv.prodAssoc : (B × C) × C ≃ᵐ B × (C × C))))
      (μB.prod ((μB.prod μC).prod μC)) (μB.prod (μB.prod (μC.prod μC))) := by
    refine MeasurePreserving.prod (MeasurePreserving.id _) ?_
    exact measurePreserving_prodAssoc μB μC μC
  have h4 : MeasurePreserving (Prod.map id (Prod.map id (Prod.swap : C × C → C × C)))
      (μB.prod (μB.prod (μC.prod μC))) (μB.prod (μB.prod (μC.prod μC))) := by
    refine MeasurePreserving.prod (MeasurePreserving.id _) ?_
    refine MeasurePreserving.prod (MeasurePreserving.id _) ?_
    exact ⟨measurable_swap, Measure.prod_swap⟩
  have h5 : MeasurePreserving
      (⇑(MeasurableEquiv.prodAssoc : (B × B) × (C × C) ≃ᵐ B × (B × (C × C))).symm)
      (μB.prod (μB.prod (μC.prod μC))) ((μB.prod μB).prod (μC.prod μC)) :=
    MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc μB μB (μC.prod μC))
  have hcomp : MeasurePreserving
      (fun p : (B × C) × (B × C) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μB.prod μC).prod (μB.prod μC)) ((μB.prod μB).prod (μC.prod μC)) := by
    have t1 := h2.comp h1
    have t2 := h3.comp t1
    have t3 := h4.comp t2
    exact h5.comp t3
  -- finally compose with the componentwise splice
  have hfin : MeasurePreserving
      (fun p : (B × B) × (C × C) => (cB p.1.1 p.1.2, cC p.2.1 p.2.2))
      ((μB.prod μB).prod (μC.prod μC)) (μB.prod μC) := hB.prod hC
  exact hfin.comp hcomp

end LatticeProb

end
