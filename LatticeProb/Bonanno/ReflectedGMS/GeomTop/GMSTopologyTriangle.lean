/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.GMSTopologyTriangle at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.CoordsMeasurable
import Mathlib.Util.AssertNoSorry

/-!
# Triangle inequalities for `d_sing` and `d^CC`

Two ingredients of Proposition 2.5 (manuscript `work/geomtop/manuscript-text.txt:433-456`) that the
manuscript takes for granted (Lemma 2.2, lines 336-352):

* `GMSTopology.dSing_triangle`: `d_sing(H₁,H₃) ≤ d_sing(H₁,H₂) + d_sing(H₂,H₃)` for **all** cell
  configurations.  Pointwise, the distance (2.1) of finite restrictions satisfies the triangle
  inequality because matchings compose (`restrictionDist_triangle`); integrating needs the
  measurability of the integrand in the radius, which is the manuscript's remark (lines 356-360)
  that `r ↦ P_N(H,U_{q,r})` is a finite step function: the cell sets increase with `r`, and before
  the cap only a chain of at most `N + 1` finite sets occurs (`measurable_integrand`).  A lower
  Lebesgue integral is not subadditive for non-measurable integrands, so this is genuinely needed.
* `GMSTopology.dCC_triangle`: the same for GMS's metric `d^CC`, whenever the first pair has
  finite restrictions to every ball (e.g. two GMS configurations); here the integrand is a function
  of a chain of finite sets, which has countably many members.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace ReflectedGMS.GeomTop

open GMS

namespace GMSTopology

/-! ### A measurability criterion on the real line -/

/-- A function on `ℝ` that is constant on the fibres of a monotone map with countable range is
measurable: the fibres are order-connected, hence measurable, and there are countably many. -/
theorem measurable_of_monotone_of_countable_range {α β : Type*} [PartialOrder α]
    [MeasurableSpace β] {φ : ℝ → α} (hφ : Monotone φ) (hrange : (range φ).Countable)
    {h : ℝ → β} (hh : ∀ r r', φ r = φ r' → h r = h r') : Measurable h := by
  intro s _
  have hfib : ∀ x, MeasurableSet (φ ⁻¹' {x}) := by
    intro x
    refine Set.OrdConnected.measurableSet ⟨fun a ha b hb c hc => ?_⟩
    simp only [mem_preimage, mem_singleton_iff] at ha hb ⊢
    exact le_antisymm (hb ▸ hφ hc.2) (ha ▸ hφ hc.1)
  have heq : h ⁻¹' s = ⋃ x ∈ φ '' (h ⁻¹' s), φ ⁻¹' {x} := by
    ext r
    simp only [mem_preimage, mem_iUnion, mem_image, mem_singleton_iff, exists_prop]
    constructor
    · intro hr
      exact ⟨φ r, ⟨r, hr, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨r', hr', rfl⟩, hx⟩
      rw [hh r r' hx]
      exact hr'
  rw [heq]
  exact MeasurableSet.biUnion (hrange.mono (image_subset_range _ _)) fun x _ => hfib x

/-- In an increasing family of sets, the finite members are determined by their cardinality. -/
theorem injOn_ncard_of_monotone {α : Type*} {S : ℝ → Set α} (hS : Monotone S) :
    InjOn Set.ncard {T | ∃ r, S r = T ∧ T.Finite} := by
  rintro _ ⟨r₁, rfl, h₁⟩ _ ⟨r₂, rfl, h₂⟩ hn
  rcases le_total r₁ r₂ with h | h
  · exact Set.eq_of_subset_of_ncard_le (hS h) hn.symm.le h₂
  · exact (Set.eq_of_subset_of_ncard_le (hS h) hn.le h₁).symm

/-- An increasing family of finite sets has countably many members. -/
theorem countable_range_of_monotone {α : Type*} {S : ℝ → Set α} (hS : Monotone S)
    (hfin : ∀ r, (S r).Finite) : (range S).Countable := by
  refine countable_iff_exists_injOn.2 ⟨Set.ncard, (injOn_ncard_of_monotone hS).mono ?_⟩
  rintro _ ⟨r, rfl⟩
  exact ⟨r, rfl, hfin r⟩

/-! ### Restrictions to windows -/

theorem restrict_mono (H : CellConfig) {W W' : Set Plane} (h : W ⊆ W') :
    H.restrict W ⊆ H.restrict W' := fun _ hK => ⟨hK.1, hK.2.mono (inter_subset_inter_right _ h)⟩

theorem window_mono (q : RatTuple) {r r' : ℝ} (h : r ≤ r') : window q r ⊆ window q r' :=
  iUnion₂_mono fun _ _ => ball_subset_ball h

theorem restrictConfig_congr {H : CellConfig} {W W' : Set Plane}
    (h : H.restrict W = H.restrict W') :
    CellConfigOps.restrictConfig H W = CellConfigOps.restrictConfig H W' := by
  unfold CellConfigOps.restrictConfig
  rw [h]

/-- The restriction to a window, cut off at `n` cells (`⊤` beyond the cutoff). -/
noncomputable def cutRestrict (H : CellConfig) (n : ℕ) (W : Set Plane) : WithTop (Set Cell) :=
  open Classical in
  if (H.restrict W).encard ≤ n then ((H.restrict W : Set Cell) : WithTop (Set Cell)) else ⊤

theorem capped_eq_of_cutRestrict_eq {H : CellConfig} {n : ℕ} {W W' : Set Plane}
    (h : cutRestrict H n W = cutRestrict H n W') :
    CellConfigOps.capped H n W = CellConfigOps.capped H n W' := by
  unfold cutRestrict at h
  unfold CellConfigOps.capped
  by_cases h₁ : (H.restrict W).encard ≤ n <;> by_cases h₂ : (H.restrict W').encard ≤ n
  · rw [if_pos h₁, if_pos h₂] at h
    rw [if_pos h₁, if_pos h₂, restrictConfig_congr (WithTop.coe_injective h)]
  · rw [if_pos h₁, if_neg h₂] at h
    exact absurd h WithTop.coe_ne_top
  · rw [if_neg h₁, if_pos h₂] at h
    exact absurd h.symm WithTop.coe_ne_top
  · rw [if_neg h₁, if_neg h₂]

theorem monotone_cutRestrict (H : CellConfig) (n : ℕ) (q : RatTuple) :
    Monotone fun r => cutRestrict H n (window q r) := by
  intro r r' hrr'
  have hsub := restrict_mono H (window_mono q hrr')
  simp only [cutRestrict]
  by_cases h₁ : (H.restrict (window q r)).encard ≤ n <;>
    by_cases h₂ : (H.restrict (window q r')).encard ≤ n
  · rw [if_pos h₁, if_pos h₂]
    exact WithTop.coe_le_coe.2 hsub
  · rw [if_pos h₁, if_neg h₂]
    exact le_top
  · exact absurd ((encard_le_encard hsub).trans h₂) h₁
  · rw [if_neg h₁, if_neg h₂]

theorem countable_range_cutRestrict (H : CellConfig) (n : ℕ) (q : RatTuple) :
    (range fun r => cutRestrict H n (window q r)).Countable := by
  have hT : {T : Set Cell | ∃ r, H.restrict (window q r) = T ∧ T.Finite ∧ T.encard ≤ n}.Finite := by
    refine Set.Finite.of_finite_image (f := Set.ncard) ((finite_Iic n).subset ?_) ?_
    · rintro _ ⟨T, ⟨r, rfl, hfin, hle⟩, rfl⟩
      rw [mem_Iic, ← Nat.cast_le (α := ℕ∞), hfin.cast_ncard_eq]
      exact hle
    · refine (injOn_ncard_of_monotone (fun r r' h => restrict_mono H (window_mono q h))).mono ?_
      rintro _ ⟨r, rfl, hfin, -⟩
      exact ⟨r, rfl, hfin⟩
  refine ((hT.image ((↑) : Set Cell → WithTop (Set Cell))).insert ⊤).countable.mono ?_
  rintro _ ⟨r, rfl⟩
  simp only [cutRestrict]
  by_cases h : (H.restrict (window q r)).encard ≤ n
  · rw [if_pos h]
    exact mem_insert_of_mem _ ⟨_, ⟨r, rfl, finite_of_encard_le_coe h, h⟩, rfl⟩
  · rw [if_neg h]
    exact mem_insert _ _

/-- **Measurability of the integrand of `d_sing`** in the radius, for arbitrary configurations
(manuscript lines 356-360). -/
theorem measurable_integrand (H H' : CellConfig) (j N : ℕ) :
    Measurable (CoordsMeasurable.integrand H H' j N) := by
  unfold CoordsMeasurable.integrand
  refine (Real.measurable_exp.comp measurable_neg).ennreal_ofReal.mul ?_
  refine measurable_of_monotone_of_countable_range
    (φ := fun r => (cutRestrict H (N + 1) (window (ratTuple j) r),
      cutRestrict H' (N + 1) (window (ratTuple j) r)))
    ((monotone_cutRestrict H (N + 1) _).prodMk (monotone_cutRestrict H' (N + 1) _))
    (((countable_range_cutRestrict H (N + 1) (ratTuple j)).prod
      (countable_range_cutRestrict H' (N + 1) (ratTuple j))).mono ?_) ?_
  · rintro _ ⟨r, rfl⟩
    exact ⟨⟨r, rfl⟩, ⟨r, rfl⟩⟩
  · intro r r' h
    simp only [Prod.mk.injEq] at h
    simp only [capped_eq_of_cutRestrict_eq h.1, capped_eq_of_cutRestrict_eq h.2]

/-! ### Composition of matchings -/

theorem mapCell_trans (f g : Plane ≃ₜ Plane) (K : Cell) :
    CellConfig.mapCell (f.trans g) K = CellConfig.mapCell g (CellConfig.mapCell f K) :=
  TopologicalSpace.NonemptyCompacts.ext (by
    simp only [CellConfig.coe_mapCell_eq_image, image_image]; rfl)

theorem mapCell_symm_trans (f g : Plane ≃ₜ Plane) (K : Cell) :
    CellConfig.mapCell (f.trans g).symm K =
      CellConfig.mapCell f.symm (CellConfig.mapCell g.symm K) :=
  TopologicalSpace.NonemptyCompacts.ext (by
    simp only [CellConfig.coe_mapCell_eq_image, image_image]; rfl)

theorem matchesWhole_trans {F G F'' : CellConfig} {f g : Plane ≃ₜ Plane}
    (hf : MatchesWhole F G f) (hg : MatchesWhole G F'' g) : MatchesWhole F F'' (f.trans g) := by
  refine ⟨fun K hK => ?_, fun K hK => ?_, fun K hK K' hK' => ?_⟩
  · rw [mapCell_trans]
    exact hg.1 _ (hf.1 K hK)
  · rw [mapCell_symm_trans]
    exact hf.2.1 _ (hg.2.1 K hK)
  · rw [mapCell_trans, mapCell_trans]
    exact (hf.2.2 K hK K' hK').trans (hg.2.2 _ (hf.1 K hK) _ (hf.1 K' hK'))

theorem wholeDistortion_trans_le {F G F'' : CellConfig} {f g : Plane ≃ₜ Plane}
    (hf : MatchesWhole F G f) :
    wholeDistortion F F'' (f.trans g) ≤ wholeDistortion F G f + wholeDistortion G F'' g := by
  unfold wholeDistortion
  have h1 : (⨆ z : Plane, edist ((f.trans g) z) z) ≤
      (⨆ z : Plane, edist (f z) z) + ⨆ z : Plane, edist (g z) z := by
    refine iSup_le fun z => ?_
    calc edist ((f.trans g) z) z ≤ edist (g (f z)) (f z) + edist (f z) z := edist_triangle _ _ _
      _ ≤ (⨆ z : Plane, edist (g z) z) + ⨆ z : Plane, edist (f z) z :=
          add_le_add (le_iSup (fun w => edist (g w) w) (f z)) (le_iSup (fun w => edist (f w) w) z)
      _ = _ := add_comm _ _
  have h2 : (⨆ (K ∈ F.cells) (K' ∈ F.cells) (_ : F.Adj K K'),
      ENNReal.ofReal |F.c K K' - F''.c (CellConfig.mapCell (f.trans g) K)
        (CellConfig.mapCell (f.trans g) K')|) ≤
      (⨆ (K ∈ F.cells) (K' ∈ F.cells) (_ : F.Adj K K'),
        ENNReal.ofReal |F.c K K' - G.c (CellConfig.mapCell f K) (CellConfig.mapCell f K')|) +
      ⨆ (K ∈ G.cells) (K' ∈ G.cells) (_ : G.Adj K K'),
        ENNReal.ofReal |G.c K K' - F''.c (CellConfig.mapCell g K) (CellConfig.mapCell g K')| := by
    refine iSup₂_le fun K hK => iSup₂_le fun K' hK' => iSup_le fun hadj => ?_
    rw [mapCell_trans, mapCell_trans]
    refine (ENNReal.ofReal_le_ofReal (abs_sub_le _
      (G.c (CellConfig.mapCell f K) (CellConfig.mapCell f K')) _)).trans
      (ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_))
    · exact le_iSup₂_of_le K hK (le_iSup₂_of_le K' hK' (le_iSup_of_le hadj le_rfl))
    · exact le_iSup₂_of_le (CellConfig.mapCell f K) (hf.1 K hK)
        (le_iSup₂_of_le (CellConfig.mapCell f K') (hf.1 K' hK')
          (le_iSup_of_le ((hf.2.2 K hK K' hK').1 hadj) le_rfl))
  exact (add_le_add h1 h2).trans_eq (add_add_add_comm _ _ _ _)

theorem min_le_min_add_min (e : ℝ≥0∞) {x a b : ℝ≥0∞} (h : x ≤ a + b) :
    min e x ≤ min e a + min e b := by
  rcases le_total e a with ha | ha
  · exact (min_le_left _ _).trans (by rw [min_eq_left ha]; exact le_self_add)
  rcases le_total e b with hb | hb
  · exact (min_le_left _ _).trans (by rw [min_eq_left hb]; exact le_add_self)
  rw [min_eq_right ha, min_eq_right hb]
  exact (min_le_right _ _).trans h

/-- **The triangle inequality for the distance (2.1)** of finite restrictions, with `†`. -/
theorem restrictionDist_triangle (o₁ o₂ o₃ : Option CellConfig) :
    restrictionDist o₁ o₃ ≤ restrictionDist o₁ o₂ + restrictionDist o₂ o₃ := by
  rcases o₁ with _ | F <;> rcases o₂ with _ | G <;> rcases o₃ with _ | F''
  · exact zero_le
  · simp only [restrictionDist, zero_add, le_refl]
  · exact zero_le
  · simp only [restrictionDist]
    exact le_self_add
  · simp only [restrictionDist, add_zero, le_refl]
  · simp only [restrictionDist]
    exact (min_le_left _ _).trans le_self_add
  · simp only [restrictionDist]
    exact le_add_self
  · simp only [restrictionDist]
    refine min_le_min_add_min 1 (ENNReal.le_iInf₂_add_iInf₂ fun f hf g hg => ?_)
    exact (iInf₂_le (f.trans g) (matchesWhole_trans hf hg)).trans (wholeDistortion_trans_le hf)

/-- **The triangle inequality for `d_sing`**, for arbitrary cell configurations. -/
theorem dSing_triangle (H₁ H₂ H₃ : CellConfig) : dSing H₁ H₃ ≤ dSing H₁ H₂ + dSing H₂ H₃ := by
  have hterm : ∀ j N, ∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H₁ H₃ j N r ≤
      (∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H₁ H₂ j N r) +
        ∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H₂ H₃ j N r := by
    intro j N
    rw [← lintegral_add_left (measurable_integrand H₁ H₂ j N)]
    refine lintegral_mono fun r => ?_
    unfold CoordsMeasurable.integrand
    rw [← mul_add]
    gcongr
    exact restrictionDist_triangle _ _ _
  calc dSing H₁ H₃ = ∑' (j : ℕ) (N : ℕ), (2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) *
        ∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H₁ H₃ j N r := rfl
    _ ≤ ∑' (j : ℕ) (N : ℕ), ((2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) *
          (∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H₁ H₂ j N r) +
        (2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) *
          ∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H₂ H₃ j N r) := by
        refine ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun N => ?_
        rw [← mul_add]
        gcongr
        exact hterm j N
    _ = dSing H₁ H₂ + dSing H₂ H₃ := by
        simp only [ENNReal.tsum_add]
        rfl

/-! ### The triangle inequality for `d^CC` -/

/-- The integrand of GMS's metric `d^CC`. -/
noncomputable def dCCIntegrand (H H' : CellConfig) (r : ℝ) : ℝ≥0∞ :=
  min (ENNReal.ofReal (Real.exp (-r)))
    (⨅ (f : Plane ≃ₜ Plane) (_ : CellConfig.AdmissibleAt H H' r f), CellConfig.distortion H H' r f)

theorem dCC_eq (H H' : CellConfig) :
    CellConfig.dCC H H' = ∫⁻ r in Ioi (0 : ℝ), dCCIntegrand H H' r := rfl

/-- The integrand of `d^CC` is measurable when both configurations have finite restrictions to
every ball: it depends on the radius only through the increasing pair of these restrictions. -/
theorem measurable_dCCIntegrand {H H' : CellConfig}
    (hH : ∀ r : ℝ, (H.restrict (ball (0 : Plane) r)).Finite)
    (hH' : ∀ r : ℝ, (H'.restrict (ball (0 : Plane) r)).Finite) :
    Measurable (dCCIntegrand H H') := by
  have hS : Monotone fun r : ℝ => H.restrict (ball (0 : Plane) r) := fun r r' h =>
    restrict_mono H (ball_subset_ball h)
  have hS' : Monotone fun r : ℝ => H'.restrict (ball (0 : Plane) r) := fun r r' h =>
    restrict_mono H' (ball_subset_ball h)
  unfold dCCIntegrand
  refine (Real.measurable_exp.comp measurable_neg).ennreal_ofReal.min ?_
  refine measurable_of_monotone_of_countable_range
    (φ := fun r => (H.restrict (ball (0 : Plane) r), H'.restrict (ball (0 : Plane) r)))
    (hS.prodMk hS')
    (((countable_range_of_monotone hS hH).prod (countable_range_of_monotone hS' hH')).mono ?_) ?_
  · rintro _ ⟨r, rfl⟩
    exact ⟨⟨r, rfl⟩, ⟨r, rfl⟩⟩
  · intro r r' h
    simp only [Prod.mk.injEq] at h
    have hA : ∀ f, CellConfig.AdmissibleAt H H' r f = CellConfig.AdmissibleAt H H' r' f := by
      intro f
      unfold CellConfig.AdmissibleAt
      rw [h.1, h.2]
    have hD : ∀ f, CellConfig.distortion H H' r f = CellConfig.distortion H H' r' f := by
      intro f
      unfold CellConfig.distortion
      rw [h.1]
    simp only [hA, hD]

theorem admissibleAt_trans {H₁ H₂ H₃ : CellConfig} {r : ℝ} {f g : Plane ≃ₜ Plane}
    (hf : CellConfig.AdmissibleAt H₁ H₂ r f) (hg : CellConfig.AdmissibleAt H₂ H₃ r g) :
    CellConfig.AdmissibleAt H₁ H₃ r (f.trans g) := by
  refine ⟨fun K hK => ?_, fun K hK => ?_, fun K hK K' hK' hadj => ?_,
    fun K hK K' hK' hadj => ?_⟩
  · rw [mapCell_trans]
    exact hg.1 _ (hf.1 K hK)
  · rw [mapCell_symm_trans]
    exact hf.2.1 _ (hg.2.1 K hK)
  · rw [mapCell_trans, mapCell_trans]
    exact hg.2.2.1 _ (hf.1 K hK) _ (hf.1 K' hK') (hf.2.2.1 K hK K' hK' hadj)
  · rw [mapCell_symm_trans, mapCell_symm_trans]
    exact hf.2.2.2 _ (hg.2.1 K hK) _ (hg.2.1 K' hK') (hg.2.2.2 K hK K' hK' hadj)

theorem distortion_trans_le {H₁ H₂ H₃ : CellConfig} {r : ℝ} {f g : Plane ≃ₜ Plane}
    (hf : CellConfig.AdmissibleAt H₁ H₂ r f) :
    CellConfig.distortion H₁ H₃ r (f.trans g) ≤
      CellConfig.distortion H₁ H₂ r f + CellConfig.distortion H₂ H₃ r g := by
  unfold CellConfig.distortion
  have h1 : (⨆ z : Plane, edist z ((f.trans g) z)) ≤
      (⨆ z : Plane, edist z (f z)) + ⨆ z : Plane, edist z (g z) := by
    refine iSup_le fun z => ?_
    calc edist z ((f.trans g) z) ≤ edist z (f z) + edist (f z) (g (f z)) := edist_triangle _ _ _
      _ ≤ _ := add_le_add (le_iSup (fun w => edist w (f w)) z)
          (le_iSup (fun w => edist w (g w)) (f z))
  have h2 : (⨆ (K ∈ H₁.restrict (ball (0 : Plane) r)) (K' ∈ H₁.restrict (ball (0 : Plane) r))
      (_ : H₁.Adj K K'), ENNReal.ofReal |H₁.c K K' - H₃.c (CellConfig.mapCell (f.trans g) K)
        (CellConfig.mapCell (f.trans g) K')|) ≤
      (⨆ (K ∈ H₁.restrict (ball (0 : Plane) r)) (K' ∈ H₁.restrict (ball (0 : Plane) r))
        (_ : H₁.Adj K K'),
        ENNReal.ofReal |H₁.c K K' - H₂.c (CellConfig.mapCell f K) (CellConfig.mapCell f K')|) +
      ⨆ (K ∈ H₂.restrict (ball (0 : Plane) r)) (K' ∈ H₂.restrict (ball (0 : Plane) r))
        (_ : H₂.Adj K K'),
        ENNReal.ofReal |H₂.c K K' - H₃.c (CellConfig.mapCell g K) (CellConfig.mapCell g K')| := by
    refine iSup₂_le fun K hK => iSup₂_le fun K' hK' => iSup_le fun hadj => ?_
    rw [mapCell_trans, mapCell_trans]
    refine (ENNReal.ofReal_le_ofReal (abs_sub_le _
      (H₂.c (CellConfig.mapCell f K) (CellConfig.mapCell f K')) _)).trans
      (ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_))
    · exact le_iSup₂_of_le K hK (le_iSup₂_of_le K' hK' (le_iSup_of_le hadj le_rfl))
    · exact le_iSup₂_of_le (CellConfig.mapCell f K) (hf.1 K hK)
        (le_iSup₂_of_le (CellConfig.mapCell f K') (hf.1 K' hK')
          (le_iSup_of_le (hf.2.2.1 K hK K' hK' hadj) le_rfl))
  exact (add_le_add h1 h2).trans_eq (add_add_add_comm _ _ _ _)

theorem dCCIntegrand_triangle (H₁ H₂ H₃ : CellConfig) (r : ℝ) :
    dCCIntegrand H₁ H₃ r ≤ dCCIntegrand H₁ H₂ r + dCCIntegrand H₂ H₃ r := by
  unfold dCCIntegrand
  refine min_le_min_add_min _ (ENNReal.le_iInf₂_add_iInf₂ fun f hf g hg => ?_)
  exact (iInf₂_le (f.trans g) (admissibleAt_trans hf hg)).trans (distortion_trans_le hf)

/-- **The triangle inequality for `d^CC`**, when the first two configurations have finite
restrictions to every ball. -/
theorem dCC_triangle {H₁ H₂ : CellConfig}
    (h₁ : ∀ r : ℝ, (H₁.restrict (ball (0 : Plane) r)).Finite)
    (h₂ : ∀ r : ℝ, (H₂.restrict (ball (0 : Plane) r)).Finite) (H₃ : CellConfig) :
    CellConfig.dCC H₁ H₃ ≤ CellConfig.dCC H₁ H₂ + CellConfig.dCC H₂ H₃ := by
  rw [dCC_eq, dCC_eq, dCC_eq, ← lintegral_add_left (measurable_dCCIntegrand h₁ h₂)]
  exact lintegral_mono fun r => dCCIntegrand_triangle H₁ H₂ H₃ r

end GMSTopology

end ReflectedGMS.GeomTop

assert_no_sorry ReflectedGMS.GeomTop.GMSTopology.dSing_triangle
assert_no_sorry ReflectedGMS.GeomTop.GMSTopology.dCC_triangle
assert_no_sorry ReflectedGMS.GeomTop.GMSTopology.measurable_integrand
#print axioms ReflectedGMS.GeomTop.GMSTopology.dSing_triangle
#print axioms ReflectedGMS.GeomTop.GMSTopology.dCC_triangle
