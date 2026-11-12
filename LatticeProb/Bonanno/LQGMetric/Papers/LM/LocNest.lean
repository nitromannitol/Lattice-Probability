/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.LocNest at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.LocEquiv

/-!
# `D(·,·;W₁)` is a Borel function of `D(·,·;W₂)` for `W₁ ⊆ W₂` (task P2-LMLOC)

LM (arXiv:1905.00379, `local-metrics-final.tex`) l. 545: "The metric `D(·,·;U∖V̄)` is equal to the
internal metric of `D(·,·;U∖W̄)` on `U∖V̄`, so is determined by `D(·,·;U∖W̄)`." The identity of
metrics is `MetricGeometry.internalEDist_internalSpace`; here we prove the "determined by" part:
for a continuous length metric `D` and open `W₁ ⊆ W₂`, `D(·,·;W₁) = Ψ(D(·,·;W₂))` for a Borel
map `Ψ` of `[0,∞]^{ℂ×ℂ}` (`internal_eq_nestInf`), hence `LocInternalNest`.

`Ψ(ρ)(u, v)` is a chain formula as in `ContMetric.chainInf` (LM S-int (a), `Meas/Internal.lean`):
the infimum over chains `u, q₁, …, q_k, v` with `q_i` in the dense sequence of `ℂ` of the sums
of the admissible steps `ρ(x, y)` with `ρ(x, y) < inf_{z ∈ T} ρ(x, z)`, `T` a countable dense
subset of `W₂ ∖ W₁`. Comparison with the chain formula for `D(·,·;W₁)`
(`ContMetric.internal_eq_chainInf`): a step admissible for `D` is admissible for `ρ = D(·,·;W₂)`
with the same value (locality, `internalEDist_eq_edist_of_ball_subset`), and an admissible
`ρ`-step is `≥ D(x, y; W₁)`, since a near-`ρ`-geodesic from `x` cannot reach `W₂ ∖ W₁`.
Own elementary proof (no source gives the measurability; DEVIATIONS entry proposed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal unitInterval

namespace LQGMetric.LM

open Blueprint GM.Bilip MetricGeometry

/-- a countable dense subset of `W₂ ∖ W₁` -/
def nestT (W₁ W₂ : Set ℂ) : Set ℂ :=
  Subtype.val '' Classical.choose (TopologicalSpace.exists_countable_dense (W₂ \ W₁ : Set ℂ))

theorem nestT_countable (W₁ W₂ : Set ℂ) : (nestT W₁ W₂).Countable :=
  (Classical.choose_spec (TopologicalSpace.exists_countable_dense (W₂ \ W₁ : Set ℂ))).1.image _

theorem nestT_subset (W₁ W₂ : Set ℂ) : nestT W₁ W₂ ⊆ W₂ \ W₁ := by
  rintro _ ⟨z, -, rfl⟩; exact z.2

theorem subset_closure_nestT (W₁ W₂ : Set ℂ) : W₂ \ W₁ ⊆ closure (nestT W₁ W₂) := by
  intro z hz
  have hd := (Classical.choose_spec (TopologicalSpace.exists_countable_dense
    (W₂ \ W₁ : Set ℂ))).2
  have : (⟨z, hz⟩ : (W₂ \ W₁ : Set ℂ)) ∈ closure (Classical.choose
      (TopologicalSpace.exists_countable_dense (W₂ \ W₁ : Set ℂ))) := hd.closure_eq ▸ mem_univ _
  exact closure_mono (subset_refl _) (mem_closure_image continuous_subtype_val.continuousAt this)

variable (W₁ W₂ : Set ℂ)

/-- `inf_{z ∈ T} ρ(x, z)` -/
def nestBd (ρ : ℂ → ℂ → ℝ≥0∞) (x : ℂ) : ℝ≥0∞ := ⨅ z ∈ nestT W₁ W₂, ρ x z

/-- an admissible step -/
def nestStep (ρ : ℂ → ℂ → ℝ≥0∞) (x y : ℂ) : ℝ≥0∞ :=
  if ρ x y < nestBd W₁ W₂ ρ x then ρ x y else ⊤

/-- the value of the chain `x, l, y` -/
def nestVal (ρ : ℂ → ℂ → ℝ≥0∞) : ℂ → List ℂ → ℂ → ℝ≥0∞
  | x, [], y => nestStep W₁ W₂ ρ x y
  | x, q :: l, y => nestStep W₁ W₂ ρ x q + nestVal ρ q l y

/-- `Ψ(ρ)(u, v)` -/
def nestInf (ρ : ℂ → ℂ → ℝ≥0∞) (u v : ℂ) : ℝ≥0∞ :=
  ⨅ l : List ℕ, nestVal W₁ W₂ ρ u (l.map (TopologicalSpace.denseSeq ℂ)) v

theorem measurable_nestEval (x y : ℂ) : Measurable fun ρ : ℂ → ℂ → ℝ≥0∞ => ρ x y :=
  (measurable_pi_apply y).comp (measurable_pi_apply x)

theorem measurable_nestStep (x y : ℂ) :
    Measurable fun ρ : ℂ → ℂ → ℝ≥0∞ => nestStep W₁ W₂ ρ x y := by
  have hb : Measurable fun ρ : ℂ → ℂ → ℝ≥0∞ => nestBd W₁ W₂ ρ x :=
    Measurable.biInf _ (nestT_countable W₁ W₂) fun z _ => measurable_nestEval x z
  exact Measurable.ite (measurableSet_lt (measurable_nestEval x y) hb) (measurable_nestEval x y)
    measurable_const

theorem measurable_nestVal (l : List ℂ) :
    ∀ x y : ℂ, Measurable fun ρ : ℂ → ℂ → ℝ≥0∞ => nestVal W₁ W₂ ρ x l y := by
  induction l with
  | nil => exact fun x y => measurable_nestStep W₁ W₂ x y
  | cons q l ih => exact fun x y => (measurable_nestStep W₁ W₂ x q).add (ih q y)

theorem measurable_nestInf :
    Measurable fun (ρ : ℂ → ℂ → ℝ≥0∞) (u v : ℂ) => nestInf W₁ W₂ ρ u v :=
  measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
    Measurable.iInf fun _ => measurable_nestVal W₁ W₂ _ u v

variable {W₁ W₂}

/-- the distance from the start of a path in `Y` to any of its points is at most its length -/
theorem internalEDist_le_pathLength_apply {X : Type*} [PseudoEMetricSpace X] {Y : Set X}
    {a b : X} (γ : Path a b) (hγ : ∀ t, γ t ∈ Y) (t : I) :
    internalEDist Y a (γ t) ≤ pathLength γ := by
  have h0 : γ.extend 0 = a := Path.extend_zero γ
  have ht : γ.extend (t : ℝ) = γ t := Path.extend_extends' γ t
  have hmaps : MapsTo γ.extend (Icc 0 (t : ℝ)) Y := fun s hs => by
    rw [Path.extend_apply γ ⟨hs.1, hs.2.trans t.2.2⟩]; exact hγ _
  have h1 := internalEDist_le_curveLength t.2.1 γ.continuous_extend.continuousOn hmaps
  rw [h0, ht] at h1
  exact h1.trans (eVariationOn.mono _ (Icc_subset_Icc le_rfl t.2.2))

/-- a step admissible for `D` on `W₁` is admissible for `ρ = D(·,·;W₂)`, with the same value -/
theorem nestStep_le_chainStep (D : ContMetric) (hD : D.IsLength) (hW : W₁ ⊆ W₂) (x y : ℂ) :
    nestStep W₁ W₂ (D.internal W₂) x y ≤ D.chainStep W₁ x y := by
  unfold ContMetric.chainStep
  split_ifs with h
  · have hball : Metric.eball (D.pt x) (D.bdDist W₁ x) ⊆ D.pt '' W₁ := by
      intro y' hy'
      by_contra hc
      have h1 := Metric.infEDist_le_edist_of_mem (x := D.pt x) (show y' ∈ (D.pt '' W₁)ᶜ from hc)
      rw [Metric.mem_eball, edist_comm] at hy'
      exact absurd (hy'.trans_le h1) (lt_irrefl _)
    have he : D.internal W₂ x y = edist (D.pt x) (D.pt y) :=
      internalEDist_eq_edist_of_ball_subset hD (hball.trans (image_mono hW)) h
    have hbd : D.bdDist W₁ x ≤ nestBd W₁ W₂ (D.internal W₂) x := by
      refine le_iInf₂ fun z hz => ?_
      refine (Metric.infEDist_le_edist_of_mem ?_).trans (edist_le_internalEDist _ _ _)
      exact D.mem_compl_image_pt.2 (nestT_subset W₁ W₂ hz).2
    unfold nestStep
    rw [if_pos (show D.internal W₂ x y < _ from he ▸ h.trans_le hbd), he]
  · exact le_top

/-- an admissible `ρ`-step bounds `D(x, y; W₁)` -/
theorem internal_le_nestStep (D : ContMetric) (hD : D.IsLength) (hW₂ : IsOpen W₂) (x y : ℂ) :
    D.internal W₁ x y ≤ nestStep W₁ W₂ (D.internal W₂) x y := by
  unfold nestStep
  split_ifs with h
  swap; · exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨δ, hδ, hδb⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 h
  have hlt : D.internal W₂ x y < D.internal W₂ x y + (min ε δ : NNReal) :=
    ENNReal.lt_add_right (h.trans_le le_top).ne (by exact_mod_cast (lt_min hε hδ).ne')
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 (show internalEDist (D.pt '' W₂) (D.pt x) (D.pt y) < _ from hlt)
  have hLb : pathLength γ.1 < nestBd W₁ W₂ (D.internal W₂) x := by
    refine hγ.trans_le ((add_le_add le_rfl ?_).trans hδb.le)
    exact_mod_cast min_le_right _ _
  -- the path stays in `W₁`
  have hin : ∀ t, γ.1 t ∈ D.pt '' W₁ := by
    intro t
    by_contra hnot
    set z := γ.1 t
    have hz2 : z ∈ D.pt '' W₂ := γ.2 t
    have hxz : internalEDist (D.pt '' W₂) (D.pt x) z ≤ pathLength γ.1 :=
      internalEDist_le_pathLength_apply γ.1 γ.2 t
    obtain ⟨η, hη, hηb⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hLb
    obtain ⟨s, hs, hsW⟩ := EMetric.isOpen_iff.1 (D.isOpen_image_pt hW₂) z hz2
    have hz' : D.unpt z ∈ W₂ \ W₁ :=
      ⟨D.mem_image_pt.1 (by simpa using hz2), fun h' => hnot (by simpa using D.mem_image_pt.2 h')⟩
    have hO : IsOpen {w : ℂ | edist z (D.pt w) < min s η} :=
      isOpen_lt (continuous_const.edist D.continuous_pt) continuous_const
    obtain ⟨w, hwO, hwT⟩ := mem_closure_iff.1 (subset_closure_nestT W₁ W₂ hz') _ hO
      (by simpa using lt_min hs (show (0 : ℝ≥0∞) < η by exact_mod_cast hη))
    have hwO' : edist z (D.pt w) < min s η := hwO
    have hzw : internalEDist (D.pt '' W₂) z (D.pt w) = edist z (D.pt w) :=
      internalEDist_eq_edist_of_ball_subset hD hsW (hwO'.trans_le (min_le_left _ _))
    have h1 : D.internal W₂ x w < nestBd W₁ W₂ (D.internal W₂) x := by
      refine ((internalEDist_triangle _ _ z _).trans_lt ?_).trans hηb
      rw [hzw]
      exact ENNReal.add_lt_add_of_le_of_lt (hxz.trans_lt (hLb.trans_le le_top)).ne hxz
        (hwO'.trans_le (min_le_right _ _))
    have h2 : nestBd W₁ W₂ (D.internal W₂) x ≤ D.internal W₂ x w := iInf₂_le w hwT
    exact absurd (h2.trans_lt h1) (lt_irrefl _)
  refine (internalEDist_le_pathLength γ.1 hin).trans (hγ.le.trans (add_le_add le_rfl ?_))
  exact_mod_cast min_le_left _ _

theorem nestVal_le_chainVal (D : ContMetric) (hD : D.IsLength) (hW : W₁ ⊆ W₂) (l : List ℂ) :
    ∀ x y : ℂ, nestVal W₁ W₂ (D.internal W₂) x l y ≤ D.chainVal W₁ x l y := by
  induction l with
  | nil => exact fun x y => nestStep_le_chainStep D hD hW x y
  | cons q l ih =>
    intro x y
    exact add_le_add (nestStep_le_chainStep D hD hW x q) (ih q y)

theorem internal_le_nestVal (D : ContMetric) (hD : D.IsLength) (hW₂ : IsOpen W₂) (l : List ℂ) :
    ∀ x y : ℂ, D.internal W₁ x y ≤ nestVal W₁ W₂ (D.internal W₂) x l y := by
  induction l with
  | nil => exact fun x y => internal_le_nestStep D hD hW₂ x y
  | cons q l ih =>
    intro x y
    exact (internalEDist_triangle _ _ (D.pt q) _).trans
      (add_le_add (internal_le_nestStep D hD hW₂ x q) (ih q y))

/-- **`D(·,·;W₁) = Ψ(D(·,·;W₂))`** for a continuous length metric and open `W₁ ⊆ W₂` -/
theorem internal_eq_nestInf (D : ContMetric) (hD : D.IsLength) (hW₁ : IsOpen W₁)
    (hW₂ : IsOpen W₂) (hW : W₁ ⊆ W₂) (u v : ℂ) :
    D.internal W₁ u v = nestInf W₁ W₂ (D.internal W₂) u v := by
  refine le_antisymm (le_iInf fun l => internal_le_nestVal D hD hW₂ _ u v) ?_
  rw [D.internal_eq_chainInf hD hW₁]
  exact iInf_mono fun l => nestVal_le_chainVal D hD hW _ u v

/-- **LM l. 545**: `LocInternalNest` -/
theorem locInternalNest : LocInternalNest := by
  intro Ω _ P D _ hlen W₁ W₂ hW₁ hW₂ hW
  refine famSigma_le_aeClosure_of_measurable ((measurable_nestInf W₁ W₂).comp
    (comap_measurable fun ω => internalFam D ω W₂)) ?_
  filter_upwards [hlen] with ω hω
  funext u v
  exact internal_eq_nestInf (D ω) hω hW₁ hW₂ hW u v

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **LM Lemma 2.3, (2) ⟺ (3)**, unconditionally -/
theorem locForm2_iff_form3 {h : Ω → DistC} {D : Ω → ContMetric} (hm : Measurable h)
    (hD : Measurable D) (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) :
    (∀ V, LocForm2 P h D V) ↔ ∀ V, LocForm3 P h D V :=
  ⟨fun h2 V => locForm3_of_form2 hm hD hlen V (h2 V),
    fun h3 V => locForm2_of_form3 locInternalNest hm hD hlen h3 V⟩

/-- **LM Lemma 2.3, (3) ⟹ (1)**, unconditionally (the direction DFGPS use at T:1140) -/
theorem isLocalMetric_of_form3 {h : Ω → DistC} {D : Ω → ContMetric} (hm : Measurable h)
    (hD : Measurable D) (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) (h3 : ∀ V, LocForm3 P h D V) :
    IsLocalMetric P h D :=
  isLocalMetric_of_form2 hD hlen ((locForm2_iff_form3 hm hD hlen).2 h3)

end LQGMetric.LM
