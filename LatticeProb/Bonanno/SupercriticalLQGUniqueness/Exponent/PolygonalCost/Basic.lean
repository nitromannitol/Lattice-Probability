/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PolygonalCost.Basic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PolygonalCost.PaidLower
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenCountable
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.C8




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.PolygonalCost

open LQGMetric LQGMetric.LFPP

 
structure RatPolygon where
  edges : ℕ
  vertices : Fin (edges + 1) → ℚ × ℚ

instance : Countable RatPolygon := by
  let e : RatPolygon → Σ n : ℕ, Fin (n + 1) → ℚ × ℚ :=
    fun P => ⟨P.edges, P.vertices⟩
  have he : Function.Injective e := by
    intro P Q h
    cases P with
    | mk n v =>
      cases Q with
      | mk m w =>
        simp only [e, Sigma.mk.injEq] at h
        cases h.1
        cases h.2
        rfl
  exact he.countable

namespace RatPolygon

 
def vertex (P : RatPolygon) (j : ℕ) : ℂ :=
  let q := P.vertices ⟨min j P.edges, Nat.lt_succ_of_le (min_le_right j P.edges)⟩
  ((q.1 : ℝ) : ℂ) + ((q.2 : ℝ) : ℂ) * Complex.I

 
def path (P : RatPolygon) : ℝ → ℂ := Exponent.PolygonCofinality.polygonPath P.vertex P.edges

end RatPolygon

 
structure RatPolygonFamily where
  last : ℕ
  paths : Fin (last + 1) → RatPolygon

instance : Countable RatPolygonFamily := by
  let e : RatPolygonFamily → Σ n : ℕ, Fin (n + 1) → RatPolygon :=
    fun F => ⟨F.last, F.paths⟩
  have he : Function.Injective e := by
    intro F G h
    cases F with
    | mk n v =>
      cases G with
      | mk m w =>
        simp only [e, Sigma.mk.injEq] at h
        cases h.1
        cases h.2
        rfl
  exact he.countable

namespace RatPolygonFamily

 
def trace (F : RatPolygonFamily) : Set ℂ :=
  Exponent.PaidDuality.polygonPathsTrace (Finset.univ : Finset (Fin (F.last + 1)))
    (fun i => (F.paths i).vertex) (fun i => (F.paths i).edges)

 
def cost (F : RatPolygonFamily) (ξ : ℝ) (f : ℂ → ℝ) : ℝ≥0∞ :=
  ∑ i : Fin (F.last + 1), lfppLen ξ f (F.paths i).path

end RatPolygonFamily

 
def openSquareAnnulus : Set ℂ :=
  Exponent.PaidDuality.outerOpenSquare \ Exponent.PaidDuality.innerSquare

 
def RatPolygonFamily.Admitted (F : RatPolygonFamily) : Prop :=
  F.trace ⊆ openSquareAnnulus ∧
    LQGMetric.Disconnects F.trace Exponent.PaidDuality.innerSquare Exponent.PaidDuality.outerOpenSquareᶜ

 
def polyAnnularCost (ξ : ℝ) (f : ℂ → ℝ) : ℝ≥0∞ :=
  ⨅ (F : RatPolygonFamily) (_ : F.Admitted), F.cost ξ f

 

theorem rectLen_le_polyAnnularCost (k : Fin 4) (ξ : ℝ) (f : ℂ → ℝ) :
    DDDF.rectLen ξ f (Exponent.PaidDuality.centralRect k) ≤ polyAnnularCost ξ f := by
  unfold polyAnnularCost
  refine le_iInf fun F => le_iInf fun hF => ?_
  exact rectLen_le_polygon_family
    (Finset.univ : Finset (Fin (F.last + 1)))
    (fun i => (F.paths i).vertex) (fun i => (F.paths i).edges)
    hF.2 k ξ f

 

theorem measurable_ratPolygonFamily_cost {Ω : Type*} [MeasurableSpace Ω]
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) (F : RatPolygonFamily) (ξ : ℝ) :
    Measurable fun ω => F.cost ξ (fun x => Y x ω) := by
  unfold RatPolygonFamily.cost
  refine Finset.measurable_sum _ fun i hi => ?_
  have hpath : IsPiecewiseC1Path (F.paths i).path
      ((F.paths i).vertex 0) ((F.paths i).vertex (F.paths i).edges) :=
    (Exponent.PolygonCofinality.polygonPath_data (ξ := ξ) (f := fun _ => 0)
      (S := Set.univ) (convex_univ : Convex ℝ (Set.univ : Set ℂ))
      (F.paths i).vertex (F.paths i).edges (by simp)).1
  exact DDDF.measurable_lfppLen hYc hYm hpath.continuousOn

 
theorem measurable_polyAnnularCost {Ω : Type*} [MeasurableSpace Ω]
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) (ξ : ℝ) :
    Measurable fun ω => polyAnnularCost ξ (fun x => Y x ω) := by
  unfold polyAnnularCost
  refine Measurable.biInf _ (Set.to_countable _) fun F hF => ?_
  exact measurable_ratPolygonFamily_cost hYc hYm F ξ

 

theorem lintegral_polyAnnularCost_pow_ge_quantile {Ω : Type*}
    [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) (ξ : ℝ) (k : Fin 4)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) (j : ℕ) :
    (1 - p) * (ENNReal.ofReal (DDDF.ellQ ξ P Y (Exponent.PaidDuality.centralRect k) p)) ^ j ≤
      ∫⁻ ω, (polyAnnularCost ξ (fun x => Y x ω)) ^ j ∂P := by
  let R := Exponent.PaidDuality.centralRect k
  let q := DDDF.ellQ ξ P Y R p
  let E : Set Ω := {ω | q ≤ DDDF.lenObs ξ Y R ω}
  have hE : MeasurableSet E := by
    change MeasurableSet ((DDDF.lenObs ξ Y R) ⁻¹' Ici q)
    exact (DDDF.measurable_lenObs hYc hYm R) measurableSet_Ici
  have hprob : 1 - p ≤ P E := DDDF.prob_ge_ellQ hYc hYm R hp0 hp1
  have hwidth : 0 ≤ R.w ∧ 0 ≤ R.h := by
    fin_cases k <;> norm_num [R, Exponent.PaidDuality.centralRect]
  have hpoint : ∀ ω, E.indicator (fun _ => (ENNReal.ofReal q) ^ j) ω ≤
      (polyAnnularCost ξ (fun x => Y x ω)) ^ j := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      have hq : ENNReal.ofReal q ≤ polyAnnularCost ξ (fun x => Y x ω) := by
        calc
          ENNReal.ofReal q ≤ ENNReal.ofReal (DDDF.lenObs ξ Y R ω) :=
            ENNReal.ofReal_le_ofReal hω
          _ = DDDF.rectLen ξ (fun x => Y x ω) R :=
            DDDF.ofReal_lenObs hYc R hwidth.1 hwidth.2 ω
          _ ≤ polyAnnularCost ξ (fun x => Y x ω) :=
            rectLen_le_polyAnnularCost k ξ _
      exact pow_le_pow_left₀ bot_le hq j
    · rw [Set.indicator_of_notMem hω]
      exact bot_le
  calc
    (1 - p) * (ENNReal.ofReal q) ^ j ≤
        (ENNReal.ofReal q) ^ j * P E := by
      simpa only [mul_comm] using
        (mul_le_mul_left hprob ((ENNReal.ofReal q) ^ j))
    _ = ∫⁻ ω, E.indicator (fun _ => (ENNReal.ofReal q) ^ j) ω ∂P :=
      (MeasureTheory.lintegral_indicator_const hE _).symm
    _ ≤ ∫⁻ ω, (polyAnnularCost ξ (fun x => Y x ω)) ^ j ∂P :=
      MeasureTheory.lintegral_mono hpoint




end SupercriticalLQGUniqueness.Exponent.PolygonalCost
