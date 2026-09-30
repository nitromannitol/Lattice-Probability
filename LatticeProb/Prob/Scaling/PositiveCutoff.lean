/- A bounded Lipschitz cutoff detecting uniform positivity on a set.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.BoundedFunctionalLift

open Set MeasureTheory
noncomputable section
namespace LatticeProb.Scaling.PositiveCutoff
variable {E : Type*}

/-- The defect from positivity at threshold δ, clipped to the unit interval. -/
def defect (δ x : ℝ) : ℝ := min 1 (max 0 (1 - x / δ))

/-- A Lipschitz cutoff that is `1` where `f ≥ δ` throughout `K` and `0` as soon as `f` dips to
`≤ 0` somewhere on `K`, built from the worst-case defect over `K`. -/
def cutoff (K : Set E) (δ : ℝ) (f : E → ℝ) : ℝ := 1 - ⨆ p ∈ K, defect δ (f p)

/-- The defect is nonnegative. -/
theorem defect_nonneg (δ x : ℝ) : 0 ≤ defect δ x := le_min zero_le_one (le_max_left _ _)
/-- The defect is at most `1`. -/
theorem defect_le_one (δ x : ℝ) : defect δ x ≤ 1 := min_le_left _ _

/-- Any value of a function uniformly bounded on `K` is at most the supremum over `K`. -/
theorem le_biSup {K : Set E} {f : E → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ p ∈ K, f p ≤ M) {p : E} (hp : p ∈ K) : f p ≤ ⨆ q ∈ K, f q := by
  have hbdd : BddAbove (range fun q : E => ⨆ _ : q ∈ K, f q) :=
    ⟨M, by rintro _ ⟨q, rfl⟩; exact Real.iSup_le (fun hq => hb q hq) hM⟩
  calc
    f p = ⨆ _ : p ∈ K, f p := (ciSup_pos (f := fun _ : p ∈ K => f p) hp).symm
    _ ≤ _ := le_ciSup hbdd p

/-- The cutoff is nonnegative. -/
theorem cutoff_nonneg (K : Set E) (δ : ℝ) (f : E → ℝ) : 0 ≤ cutoff K δ f :=
  sub_nonneg.mpr (Real.iSup_le (fun p => Real.iSup_le (fun _ => defect_le_one δ (f p)) zero_le_one) zero_le_one)

/-- The cutoff is at most `1`. -/
theorem cutoff_le_one (K : Set E) (δ : ℝ) (f : E → ℝ) : cutoff K δ f ≤ 1 := by
  have hn : 0 ≤ ⨆ p ∈ K, defect δ (f p) :=
    Real.iSup_nonneg fun p => Real.iSup_nonneg fun _ => defect_nonneg δ (f p)
  unfold cutoff
  linarith

/-- The cutoff vanishes as soon as `f` is nonpositive somewhere on `K`. -/
theorem cutoff_eq_zero {K : Set E} {δ : ℝ} (hδ : 0 < δ) {f : E → ℝ}
    {p : E} (hp : p ∈ K) (hf : f p ≤ 0) : cutoff K δ f = 0 := by
  have hd : defect δ (f p) = 1 := by
    unfold defect
    rw [min_eq_left]
    exact (show (1 : ℝ) ≤ 1 - f p / δ by have := div_nonpos_of_nonpos_of_nonneg hf hδ.le; linarith).trans (le_max_right _ _)
  have hle := le_biSup (K := K) zero_le_one (fun p _ => defect_le_one δ (f p)) hp
  rw [hd] at hle
  have := cutoff_nonneg K δ f
  unfold cutoff at *
  linarith

/-- A nonzero cutoff detects strict positivity of `f` throughout `K`. -/
theorem positive_of_cutoff_ne_zero {K : Set E} {δ : ℝ} (hδ : 0 < δ) {f : E → ℝ}
    (hf : cutoff K δ f ≠ 0) : ∀ p ∈ K, 0 < f p := by
  intro p hp
  by_contra hn
  exact hf (cutoff_eq_zero hδ hp (le_of_not_gt hn))

/-- The cutoff equals `1` once `f` is at least `δ` throughout `K`. -/
theorem cutoff_eq_one {K : Set E} {δ : ℝ} (hδ : 0 < δ) {f : E → ℝ}
    (hf : ∀ p ∈ K, δ ≤ f p) : cutoff K δ f = 1 := by
  have hz : ∀ p ∈ K, defect δ (f p) = 0 := by
    intro p hp
    have hdiv : 1 ≤ f p / δ := (le_div_iff₀ hδ).mpr (by simpa using hf p hp)
    simp [defect, max_eq_left (show 1 - f p / δ ≤ 0 by linarith)]
  have he : (⨆ p ∈ K, defect δ (f p)) = 0 := by
    apply le_antisymm
    · exact Real.iSup_le (fun p => Real.iSup_le (fun hp => (hz p hp).le) le_rfl) le_rfl
    · exact Real.iSup_nonneg fun p => Real.iSup_nonneg fun _ => defect_nonneg δ (f p)
  simp [cutoff, he]

/-- The defect is `1/δ`-Lipschitz. -/
theorem abs_defect_sub_le {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    |defect δ x - defect δ y| ≤ |x - y| / δ := by
  have hmax : |max 0 (1 - x / δ) - max 0 (1 - y / δ)| ≤ |(1 - x / δ) - (1 - y / δ)| :=
    by simpa only [max_comm] using abs_max_sub_max_le_abs (1 - x / δ) (1 - y / δ) 0
  have hmin : |defect δ x - defect δ y| ≤
      |max 0 (1 - x / δ) - max 0 (1 - y / δ)| := by
    have hl : LipschitzWith 1 (fun z : ℝ => min 1 z) := LipschitzWith.id.const_min 1
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, defect] using
      hl.dist_le_mul (max 0 (1 - x / δ)) (max 0 (1 - y / δ))
  have he : |(1 - x / δ) - (1 - y / δ)| = |x - y| / δ := by
    rw [show (1 - x / δ) - (1 - y / δ) = -(x - y) / δ by ring,
      abs_div, abs_neg, abs_of_pos hδ]
  exact hmin.trans (he ▸ hmax)

/-- The cutoff is `1/δ`-Lipschitz for the sup distance on `K`. -/
theorem abs_cutoff_sub_le {K : Set E} {δ r : ℝ} (hδ : 0 < δ) (hr : 0 ≤ r)
    {f g : E → ℝ} (hfg : ∀ p ∈ K, |f p - g p| ≤ r) :
    |cutoff K δ f - cutoff K δ g| ≤ r / δ := by
  have hsup (v w : E → ℝ) (hvw : ∀ p ∈ K, |v p - w p| ≤ r) :
      (⨆ p ∈ K, defect δ (v p)) ≤ (⨆ p ∈ K, defect δ (w p)) + r / δ := by
    have hn : 0 ≤ (⨆ p ∈ K, defect δ (w p)) + r / δ := add_nonneg
      (Real.iSup_nonneg fun p => Real.iSup_nonneg fun _ => defect_nonneg δ (w p)) (div_nonneg hr hδ.le)
    apply Real.iSup_le _ hn
    intro p
    apply Real.iSup_le _ hn
    intro hp
    have ha := (abs_defect_sub_le hδ (v p) (w p)).trans (div_le_div_of_nonneg_right (hvw p hp) hδ.le)
    have hb := le_biSup (K := K) zero_le_one (fun q _ => defect_le_one δ (w q)) hp
    linarith [le_of_abs_le ha]
  have h1 := hsup f g hfg
  have h2 := hsup g f (fun p hp => by rw [abs_sub_comm]; exact hfg p hp)
  rw [abs_le]
  unfold cutoff
  constructor <;> linarith

/-- Countably indexed fields have measurable positivity cutoffs even without continuous paths. -/
theorem measurable_cutoff_countable {I Ω : Type*} [Countable I] [MeasurableSpace Ω]
    (K : Set E) (q : E → I) (δ : ℝ) (v : Ω → I → ℝ)
    (hv : ∀ i, Measurable fun ω => v ω i) :
    Measurable (fun ω => cutoff K δ (fun p => v ω (q p))) := by
  have he : ∀ ω, (⨆ p ∈ K, defect δ (v ω (q p))) = ⨆ i ∈ q '' K, defect δ (v ω i) := by
    intro ω
    apply le_antisymm
    · apply Real.iSup_le _ (Real.iSup_nonneg fun i => Real.iSup_nonneg fun _ => defect_nonneg _ _)
      intro p
      apply Real.iSup_le _ (Real.iSup_nonneg fun i => Real.iSup_nonneg fun _ => defect_nonneg _ _)
      intro hp
      exact le_biSup zero_le_one (fun i _ => defect_le_one _ _) ⟨p, hp, rfl⟩
    · apply Real.iSup_le _ (Real.iSup_nonneg fun p => Real.iSup_nonneg fun _ => defect_nonneg _ _)
      intro i
      apply Real.iSup_le _ (Real.iSup_nonneg fun p => Real.iSup_nonneg fun _ => defect_nonneg _ _)
      rintro ⟨p, hp, rfl⟩
      exact le_biSup (K := K) (f := fun p => defect δ (v ω (q p)))
        zero_le_one (fun p _ => defect_le_one _ _) hp
  simp_rw [cutoff, he]
  apply Measurable.const_sub
  apply Measurable.iSup
  intro i
  apply Measurable.iSup
  intro _
  exact measurable_const.min (measurable_const.max (measurable_const.sub ((hv i).div_const δ)))

/-- On a compact set where a continuous function is everywhere strictly positive, the cutoff
reaches `1` at some small enough scale `1/(n+1)`. -/
theorem exists_cutoff_eq_one [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContinuousOn f K) (hpos : ∀ p ∈ K, 0 < f p) :
    ∃ n : ℕ, cutoff K (1 / ((n : ℝ) + 1)) f = 1 := by
  rcases K.eq_empty_or_nonempty with he | hn
  · exact ⟨0, cutoff_eq_one (by positivity) (by simp [he])⟩
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hn hf
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hpos p hp)
  exact ⟨n, cutoff_eq_one (by positivity) (fun q hq => hn.le.trans (hmin hq))⟩

/-- For continuous paths, a countable dense subset suffices to read the cutoff. -/
theorem measurable_cutoff_continuous {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [SecondCountableTopology E]
    (K : Set E) (δ : ℝ) (f : Ω → E → ℝ)
    (hc : ∀ ω, Continuous (f ω)) (hm : ∀ p, Measurable fun ω => f ω p) :
    Measurable (fun ω => cutoff K δ (f ω)) := by
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense K
  have he : ∀ ω, (⨆ p ∈ K, defect δ (f ω p)) = ⨆ q ∈ D, defect δ (f ω q.1) := by
    intro ω
    have hr : 0 ≤ ⨆ q ∈ D, defect δ (f ω q.1) :=
      Real.iSup_nonneg fun q => Real.iSup_nonneg fun _ => defect_nonneg _ _
    have hl : 0 ≤ ⨆ p ∈ K, defect δ (f ω p) :=
      Real.iSup_nonneg fun p => Real.iSup_nonneg fun _ => defect_nonneg _ _
    apply le_antisymm
    · apply Real.iSup_le _ hr
      intro p
      apply Real.iSup_le _ hr
      intro hp
      have hcont : Continuous (fun q : K => defect δ (f ω q.1)) :=
        continuous_const.min (continuous_const.max
          (continuous_const.sub (((hc ω).comp continuous_subtype_val).div_const δ)))
      exact closure_minimal (fun q hq => le_biSup (K := D)
        (f := fun q => defect δ (f ω q.1)) zero_le_one (fun q _ => defect_le_one _ _) hq)
        (isClosed_le hcont continuous_const) (hdense ⟨p, hp⟩)
    · apply Real.iSup_le _ hl
      intro q
      apply Real.iSup_le _ hl
      intro _
      exact le_biSup (K := K) (f := fun p => defect δ (f ω p))
        zero_le_one (fun p _ => defect_le_one _ _) q.2
  simp_rw [cutoff, he]
  exact (Measurable.biSup D hD (fun q _ => measurable_const.min
    (measurable_const.max (measurable_const.sub ((hm q.1).div_const δ))))).const_sub 1

end LatticeProb.Scaling.PositiveCutoff
