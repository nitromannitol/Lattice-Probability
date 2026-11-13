/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.NestedAnnulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SLUMetricAPI2
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus




 






set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated

 
theorem mem_toSet_iff (A : EuclideanAnnulus) (y : ℂ) :
    y ∈ A.toSet ↔ A.innerRadius < dist y A.center ∧ dist y A.center < A.outerRadius := by
  have hr : A.innerRadius ≠ 0 := ne_of_gt A.2.1
  unfold EuclideanAnnulus.toSet
  rw [closure_ball A.center hr]
  simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le]
  exact and_comm

 
theorem toSet_subset_of_nested (A A' : EuclideanAnnulus)
    (hρ : A.innerRadius + dist A.center A'.center ≤ A'.innerRadius)
    (hσ : A'.outerRadius ≤ A.outerRadius - dist A.center A'.center) :
    A'.toSet ⊆ A.toSet := by
  intro y hy
  rw [mem_toSet_iff] at hy ⊢
  have h1 := dist_triangle y A'.center A.center
  have h2 := dist_triangle y A.center A'.center
  rw [dist_comm A'.center A.center] at h1
  constructor <;> linarith [hy.1, hy.2]

 

theorem disconnects_of_nested (K : Set ℂ) (A A' : EuclideanAnnulus)
    (hρ : A.innerRadius + dist A.center A'.center ≤ A'.innerRadius)
    (hσ : A'.outerRadius ≤ A.outerRadius - dist A.center A'.center)
    (hK : Disconnects K A'.innerBoundary A'.outerBoundary) :
    Disconnects K A.innerBoundary A.outerBoundary := by
  rintro ⟨S, hS, hSK, ⟨s₁, hs₁S, hs₁⟩, ⟨s₂, hs₂S, hs₂⟩⟩
  apply hK
  refine ⟨S, hS, hSK, ?_, ?_⟩
  · 
    have hpre : IsPreconnected ((fun y => dist y A'.center) '' S) :=
      hS.image _ (continuous_id.dist continuous_const).continuousOn
    have hs₁' : dist s₁ A'.center ≤ A'.innerRadius := by
      have h := dist_triangle s₁ A.center A'.center
      have hr : dist s₁ A.center = A.innerRadius := Metric.mem_sphere.mp hs₁
      linarith
    have hs₂' : A'.outerRadius ≤ dist s₂ A'.center := by
      have h := dist_triangle s₂ A'.center A.center
      have hr : dist s₂ A.center = A.outerRadius := Metric.mem_sphere.mp hs₂
      rw [dist_comm A'.center A.center] at h
      linarith
    have hmem := hpre.Icc_subset ⟨s₁, hs₁S, rfl⟩ ⟨s₂, hs₂S, rfl⟩
      ⟨hs₁', le_trans (le_of_lt A'.2.2) hs₂'⟩
    obtain ⟨y, hyS, hy⟩ := hmem
    exact ⟨y, hyS, Metric.mem_sphere.mpr hy⟩
  · have hpre : IsPreconnected ((fun y => dist y A'.center) '' S) :=
      hS.image _ (continuous_id.dist continuous_const).continuousOn
    have hs₁' : dist s₁ A'.center ≤ A'.innerRadius := by
      have h := dist_triangle s₁ A.center A'.center
      have hr : dist s₁ A.center = A.innerRadius := Metric.mem_sphere.mp hs₁
      linarith
    have hs₂' : A'.outerRadius ≤ dist s₂ A'.center := by
      have h := dist_triangle s₂ A'.center A.center
      have hr : dist s₂ A.center = A.outerRadius := Metric.mem_sphere.mp hs₂
      rw [dist_comm A'.center A.center] at h
      linarith
    have hmem := hpre.Icc_subset ⟨s₁, hs₁S, rfl⟩ ⟨s₂, hs₂S, rfl⟩
      ⟨le_trans hs₁' (le_of_lt A'.2.2), hs₂'⟩
    obtain ⟨y, hyS, hy⟩ := hmem
    exact ⟨y, hyS, Metric.mem_sphere.mpr hy⟩

 
theorem aroundDist_le_of_nested (D : LSCMetric) (A A' : EuclideanAnnulus)
    (hρ : A.innerRadius + dist A.center A'.center ≤ A'.innerRadius)
    (hσ : A'.outerRadius ≤ A.outerRadius - dist A.center A'.center) :
    aroundDist D A ≤ aroundDist D A' := by
  unfold aroundDist
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hA => le_iInf fun hsep => ?_
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hP <|
    iInf_le_of_le (fun t ht => toSet_subset_of_nested A A' hρ hσ (hA t ht)) <|
    iInf_le_of_le (disconnects_of_nested _ A A' hρ hσ hsep) le_rfl


 
def radialPath (c s : ℂ) (R : ℝ) (t : ℝ) : ℂ :=
  c + (((1 - t) + t * (R / ‖s - c‖) : ℝ) : ℂ) * (s - c)

theorem radialPath_zero (c s : ℂ) (R : ℝ) : radialPath c s R 0 = s := by
  simp [radialPath]

theorem continuous_radialPath (c s : ℂ) (R : ℝ) : Continuous (radialPath c s R) := by
  unfold radialPath
  fun_prop

theorem dist_radialPath (c s : ℂ) (hs : s ≠ c) (R t : ℝ) (hR : 0 ≤ R)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dist (radialPath c s R t) c = (1 - t) * ‖s - c‖ + t * R := by
  have hn : 0 < ‖s - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs)
  have hx : 0 ≤ (1 - t) + t * (R / ‖s - c‖) := by
    have : 0 ≤ t * (R / ‖s - c‖) := mul_nonneg ht0 (div_nonneg hR hn.le)
    linarith
  unfold radialPath
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx]
  field_simp

theorem radialPath_one_mem_sphere (c s : ℂ) (hs : s ≠ c) (R : ℝ) (hR : 0 ≤ R) :
    radialPath c s R 1 ∈ Metric.sphere c R := by
  rw [Metric.mem_sphere, dist_radialPath c s hs R 1 hR zero_le_one le_rfl]
  ring

theorem dist_radialPath_le_max (c s : ℂ) (hs : s ≠ c) (R t : ℝ) (hR : 0 ≤ R)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dist (radialPath c s R t) c ≤ max ‖s - c‖ R := by
  rw [dist_radialPath c s hs R t hR ht0 ht1]
  have h1 : ‖s - c‖ ≤ max ‖s - c‖ R := le_max_left _ _
  have h2 : R ≤ max ‖s - c‖ R := le_max_right _ _
  nlinarith

theorem min_le_dist_radialPath (c s : ℂ) (hs : s ≠ c) (R t : ℝ) (hR : 0 ≤ R)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    min ‖s - c‖ R ≤ dist (radialPath c s R t) c := by
  rw [dist_radialPath c s hs R t hR ht0 ht1]
  have h1 : min ‖s - c‖ R ≤ ‖s - c‖ := min_le_left _ _
  have h2 : min ‖s - c‖ R ≤ R := min_le_right _ _
  nlinarith

 

theorem admissible_of_close (D : LSCMetric) (A : EuclideanAnnulus) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hA : ∀ t ∈ Icc a b, P t ∈ A.toSet)
    (hsep : Disconnects (P '' Icc a b) A.innerBoundary A.outerBoundary) :
    ∃ η > 0, ∀ A' : EuclideanAnnulus, dist A.center A'.center < η →
      A.innerRadius + dist A.center A'.center < A'.innerRadius →
      A'.innerRadius < A.innerRadius + η →
      A.outerRadius - η < A'.outerRadius →
      A'.outerRadius < A.outerRadius - dist A.center A'.center →
      (∀ t ∈ Icc a b, P t ∈ A'.toSet) ∧
        Disconnects (P '' Icc a b) A'.innerBoundary A'.outerBoundary := by
  set c := A.center with hc
  set ρ := A.innerRadius with hρdef
  set σ := A.outerRadius with hσdef
  set K := P '' Icc a b with hKdef
  have hρpos : 0 < ρ := A.2.1
  
  have hmaps : MapsTo P (Icc a b) (Metric.closedBall c σ) := by
    intro t ht
    have := (mem_toSet_iff A (P t)).mp (hA t ht)
    exact Metric.mem_closedBall.mpr this.2.le
  have hcont : ContinuousOn P (Icc a b) :=
    hP.continuousOn_of_mapsTo (isCompact_closedBall c σ) hmaps
  have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn hcont
  have hKne : K.Nonempty := ⟨P a, a, ⟨le_rfl, hP.1⟩, rfl⟩
  have hfc : ContinuousOn (fun y : ℂ => dist y c) K :=
    (continuous_id.dist continuous_const).continuousOn
  obtain ⟨y₀, hy₀K, hmin⟩ := hKc.exists_isMinOn hKne hfc
  obtain ⟨y₁, hy₁K, hmax⟩ := hKc.exists_isMaxOn hKne hfc
  have hKA : ∀ y ∈ K, ρ < dist y c ∧ dist y c < σ := by
    rintro y ⟨t, ht, rfl⟩
    exact (mem_toSet_iff A (P t)).mp (hA t ht)
  set m₁ := dist y₀ c - ρ with hm₁
  set m₂ := σ - dist y₁ c with hm₂
  have hm₁pos : 0 < m₁ := by have := (hKA y₀ hy₀K).1; linarith
  have hm₂pos : 0 < m₂ := by have := (hKA y₁ hy₁K).2; linarith
  have hlow : ∀ y ∈ K, ρ + m₁ ≤ dist y c := by
    intro y hy
    have := hmin hy
    simp only [Set.mem_ofPred_eq] at this
    linarith
  have hhigh : ∀ y ∈ K, dist y c ≤ σ - m₂ := by
    intro y hy
    have := hmax hy
    simp only [Set.mem_ofPred_eq] at this
    linarith
  set η := min m₁ m₂ / 4 with hη
  have hηpos : 0 < η := by positivity
  have hη₁ : 4 * η ≤ m₁ := by
    have := min_le_left m₁ m₂
    linarith
  have hη₂ : 4 * η ≤ m₂ := by
    have := min_le_right m₁ m₂
    linarith
  refine ⟨η, hηpos, ?_⟩
  intro A' hcc hρ₁ hρ₂ hσ₁ hσ₂
  set c' := A'.center
  set ρ' := A'.innerRadius
  set σ' := A'.outerRadius
  have hdcc : 0 ≤ dist c c' := dist_nonneg
  constructor
  · intro t ht
    have hy : P t ∈ K := ⟨t, ht, rfl⟩
    have hl := hlow _ hy
    have hh := hhigh _ hy
    have t1 := dist_triangle (P t) c' c
    have t2 := dist_triangle (P t) c c'
    rw [dist_comm c' c] at t1
    rw [mem_toSet_iff]
    constructor <;> linarith
  · rintro ⟨S, hS, hSK, ⟨s₁, hs₁S, hs₁⟩, ⟨s₂, hs₂S, hs₂⟩⟩
    have hs₁r : dist s₁ c' = ρ' := Metric.mem_sphere.mp hs₁
    have hs₂r : dist s₂ c' = σ' := Metric.mem_sphere.mp hs₂
    have hs₁c : dist s₁ c ≤ ρ' + dist c c' := by
      have := dist_triangle s₁ c' c
      rw [dist_comm c' c] at this
      linarith
    have hs₁c' : ρ < dist s₁ c := by
      have := dist_triangle s₁ c c'
      linarith
    have hs₂c : σ' - dist c c' ≤ dist s₂ c := by
      have := dist_triangle s₂ c c'
      linarith
    have hs₁ne : s₁ ≠ c := by
      intro h
      rw [h, dist_self] at hs₁c'
      linarith
    have hs₂ne : s₂ ≠ c := by
      intro h
      have : dist s₂ c = 0 := by rw [h, dist_self]
      have hy₁ := hKA y₁ hy₁K
      linarith
    let γ₁ : Set ℂ := radialPath c s₁ ρ '' Icc 0 1
    let γ₂ : Set ℂ := radialPath c s₂ σ '' Icc 0 1
    have hγ₁pre : IsPreconnected γ₁ :=
      isPreconnected_Icc.image _ (continuous_radialPath c s₁ ρ).continuousOn
    have hγ₂pre : IsPreconnected γ₂ :=
      isPreconnected_Icc.image _ (continuous_radialPath c s₂ σ).continuousOn
    have hs₁γ : s₁ ∈ γ₁ := ⟨0, ⟨le_rfl, zero_le_one⟩, radialPath_zero c s₁ ρ⟩
    have hs₂γ : s₂ ∈ γ₂ := ⟨0, ⟨le_rfl, zero_le_one⟩, radialPath_zero c s₂ σ⟩
    have hσpos : 0 < σ := lt_trans hρpos A.2.2
    have hγ₁K : γ₁ ⊆ Kᶜ := by
      rintro y ⟨t, ht, rfl⟩ hyK
      have hle := dist_radialPath_le_max c s₁ hs₁ne ρ t hρpos.le ht.1 ht.2
      have hl := hlow _ hyK
      have hnorm : ‖s₁ - c‖ = dist s₁ c := (dist_eq_norm s₁ c).symm
      have hmax : max ‖s₁ - c‖ ρ < ρ + m₁ := by
        rw [hnorm]
        apply max_lt <;> linarith
      linarith
    have hγ₂K : γ₂ ⊆ Kᶜ := by
      rintro y ⟨t, ht, rfl⟩ hyK
      have hge := min_le_dist_radialPath c s₂ hs₂ne σ t hσpos.le ht.1 ht.2
      have hh := hhigh _ hyK
      have hnorm : ‖s₂ - c‖ = dist s₂ c := (dist_eq_norm s₂ c).symm
      have hmin' : σ - m₂ < min ‖s₂ - c‖ σ := by
        rw [hnorm]
        apply lt_min <;> linarith
      linarith
    apply hsep
    refine ⟨S ∪ γ₁ ∪ γ₂, ?_, ?_, ?_, ?_⟩
    · exact (hS.union s₁ hs₁S hs₁γ hγ₁pre).union s₂ (Or.inl hs₂S) hs₂γ hγ₂pre
    · intro y hy
      rcases hy with (hy | hy) | hy
      · exact hSK hy
      · exact hγ₁K hy
      · exact hγ₂K hy
    · exact ⟨radialPath c s₁ ρ 1, Or.inl (Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩),
        radialPath_one_mem_sphere c s₁ hs₁ne ρ hρpos.le⟩
    · exact ⟨radialPath c s₂ σ 1, Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩,
        radialPath_one_mem_sphere c s₂ hs₂ne σ hσpos.le⟩



end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated
