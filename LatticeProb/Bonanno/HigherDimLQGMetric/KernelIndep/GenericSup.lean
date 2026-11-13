/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.GenericSup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.Version
import LatticeProb.Bonanno.HigherDimLFPP.Field.SupBounds

/-!
# Gaussian supremum bound for general white-noise vector families

The finite-grid argument is a port of `HigherDimLFPP.SupB.integral_iSup_finset_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN IsWhiteNoise)

private theorem vecIntegral_iSup_finset_le {d : ℕ} [NeZero d] {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    (hW : IsWhiteNoise P W) (v : Rd d → WN d) {X : Rd d → Ω → ℝ}
    (hX : ∀ z, X z =ᵐ[P] W (v z)) {a : ℝ} (ha : 0 < a)
    {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ z w, ‖v z - v w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    {V : ℝ} (hV : 0 < V) (hvV : ∀ z, ‖v z‖ ^ 2 ≤ V)
    (x₀ : Rd d) {R : ℝ} (hR : 0 ≤ R)
    {ℓ : ℝ} (hℓ : d * Real.log (2 * R / a + 1) ≤ ℓ)
    {s : ℝ} (hs : s * s = 1)
    (F : Finset (Rd d)) (hF : ∀ z ∈ F, z ∈ HigherDimLFPP.Osc.box x₀ R)
    (hGF : HigherDimLFPP.Osc.grid x₀ R a ⊆ F) :
    ∫ ω, (⨆ z : F, s * X z ω) ∂P ≤ HigherDimLFPP.SupB.supMean d L V ℓ := by
  classical
  have hval : ∫ ω, (⨆ z : F, s * X z ω) ∂P =
      LQGDimension.gaussianExpectedMax F (fun z w => ⟪v z, v w⟫) 0 := by
    have h := hW.integral_iSup_eq_gaussianExpectedMax F (fun z => s • v z) 0
    have hae : ∀ᵐ ω ∂P, ∀ z : F, s * X z ω = W (s • v z) ω + (0 : Rd d → ℝ) z := by
      refine ae_all_iff.2 fun z => ?_
      filter_upwards [hW.smul_ae s (v z), hX (z : Rd d)] with ω h1 h2
      rw [h1, h2, Pi.zero_apply, add_zero]
    have hC : (fun z w : Rd d => ⟪s • v z, s • v w⟫) = fun z w => ⟪v z, v w⟫ := by
      funext z w
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, hs, one_mul]
    rw [hC] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp only [hω]
  obtain ⟨u, hu, hEq⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F
    (fun z w => ⟪v z, v w⟫) (LQGDimension.posSemidef_gramOn F v)
  rw [hval, hEq]
  set G := HigherDimLFPP.Osc.grid x₀ R a with hGdef
  have hG : G.Nonempty := Finset.card_pos.1 (HigherDimLFPP.Osc.one_le_card_grid x₀ R a)
  have hgr : ∀ z ∈ F, HigherDimLFPP.Osc.gridOf x₀ R a z ∈ G ∧
      ‖z - HigherDimLFPP.Osc.gridOf x₀ R a z‖ ≤ √(d : ℝ) * a :=
    fun z hz => ⟨HigherDimLFPP.Osc.gridOf_mem_grid x₀ ha (hF z hz),
      HigherDimLFPP.Osc.norm_sub_gridOf_le x₀ ha (hF z hz)⟩
  have hu' : ∀ g ∈ G, ‖u g‖ ^ 2 ≤ V := by
    intro g hg
    rw [← real_inner_self_eq_norm_sq, hu g (hGF hg) g (hGF hg), real_inner_self_eq_norm_sq]
    exact hvV g
  have hinc : ∀ z ∈ F, ∀ w ∈ F,
      ‖u z - u w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2 := by
    intro z hz w hw
    have e : ‖u z - u w‖ ^ 2 = ‖v z - v w‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq (v z),
        ← real_inner_self_eq_norm_sq (v w), hu z hz z hz, hu z hz w hw, hu w hw w hw]
    rw [e]
    exact hL z w
  have hlogN : Real.log G.card ≤ ℓ :=
    (HigherDimLFPP.SupB.log_card_grid_le x₀ hR ha).trans hℓ
  have hlog0 : 0 ≤ Real.log G.card := Real.log_nonneg (by exact_mod_cast hG.card_pos)
  set lam := √(1 + ℓ) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 (by linarith)
  have hlam2 : lam ^ 2 = 1 + ℓ := Real.sq_sqrt (by linarith)
  have hN : Real.log G.card ≤ lam ^ 2 := by rw [hlam2]; linarith
  set c₁ : ℝ := V / 2 with hc₁
  set c₂ : ℝ := π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8 with hc₂
  have hc₁0 : 0 < c₁ := by positivity
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hc₂0 : 0 < c₂ := by positivity
  have hmain := HigherDimLFPP.SupB.vecExpectedMax_le_grid hGF hG
    (HigherDimLFPP.Osc.gridOf x₀ R a) ha (Real.sqrt_nonneg _) hL0.le hgr u hu' hinc
    (l₁ := lam / √c₁) (l₂ := lam / √c₂) (by positivity) (by positivity)
  have h1 := HigherDimLFPP.SupB.softmax_opt hc₁0 hlam0 hN
  have h2 := HigherDimLFPP.SupB.softmax_opt hc₂0 hlam0 hN
  refine hmain.trans ?_
  unfold HigherDimLFPP.SupB.supMean
  rw [← hlam, ← hc₁, ← hc₂]
  linarith

/-- A generic Borell tail on a box for a continuous version of an isonormal vector family. -/
theorem vecSup_tail {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WN d → Ω → ℝ}
    (hW : IsWhiteNoise P W) (v : Rd d → WN d) {L V a : ℝ}
    (ha : 0 < a) (hL : 0 < L) (hV : 0 < V)
    (hvV : ∀ z, ‖v z‖ ^ 2 ≤ V)
    (hvL : ∀ z w, ‖v z - v w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    {X : Rd d → Ω → ℝ} (hXc : ∀ ω, Continuous fun z => X z ω)
    (_hXm : ∀ z, Measurable (X z)) (hX : ∀ z, X z =ᵐ[P] W (v z))
    (x₀ : Rd d) {R : ℝ} (hR : 0 ≤ R) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | HigherDimLFPP.SupB.supMean d L V (d * Real.log (2 * R / a + 1)) + u ≤
        ⨆ z : HigherDimLFPP.Osc.box x₀ R, |X z ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * V))) := by
  classical
  have := hW.isProbabilityMeasure
  set B : Set (Rd d) := HigherDimLFPP.Osc.box x₀ R with hB
  have : CompactSpace B := isCompact_iff_compactSpace.1
    (HigherDimLFPP.Osc.isCompact_box x₀ R)
  have hx₀ : x₀ ∈ B := fun i => by simpa only [sub_self, abs_zero] using hR
  have : Nonempty B := ⟨⟨x₀, hx₀⟩⟩
  set M := HigherDimLFPP.SupB.supMean d L V (d * Real.log (2 * R / a + 1)) with hM
  have hXi : ∀ z, Integrable (X z) P := fun z => by
    have hm : MemLp (X z) 2 P :=
      (hW.memLp (v z) 2 ENNReal.ofNat_ne_top).ae_eq (hX z).symm
    exact hm.integrable one_le_two
  have hfin : ∀ s : ℝ, s * s = 1 → ∀ (n : ℕ) (t : Fin (n + 1) → B),
      ∫ ω, (⨆ i, s * X (t i) ω) ∂P ≤ M := by
    intro s hs n t
    set F : Finset (Rd d) := (Finset.univ.image fun i => (t i : Rd d)) ∪
      HigherDimLFPP.Osc.grid x₀ R a with hF
    have hFB : ∀ z ∈ F, z ∈ B := by
      intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact (t i).2
      · exact HigherDimLFPP.Osc.grid_subset_box x₀ hR ha hz
    have hGF : HigherDimLFPP.Osc.grid x₀ R a ⊆ F := Finset.subset_union_right
    have : Nonempty F := ⟨⟨t 0, Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ 0))⟩⟩
    have hint1 : Integrable (fun ω => ⨆ i, s * X (t i) ω) P :=
      HigherDimLFPP.SupB.integrable_iSup_of_finite fun i => (hXi _).const_mul s
    have hint2 : Integrable (fun ω => ⨆ z : F, s * X z ω) P :=
      HigherDimLFPP.SupB.integrable_iSup_of_finite fun z => (hXi _).const_mul s
    have hpt : ∀ ω, (⨆ i, s * X (t i) ω) ≤ ⨆ z : F, s * X z ω := fun ω =>
      ciSup_le fun i => le_ciSup (f := fun z : F => s * X z ω) (Finite.bddAbove_range _)
        ⟨t i, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
    exact (integral_mono hint1 hint2 hpt).trans
      (vecIntegral_iSup_finset_le hW v hX ha hL hvL hV hvV x₀ hR le_rfl hs F hFB hGF)
  set Y : B → Ω → ℝ := fun z ω => X z ω with hY
  have hYg : IsGaussianProcess Y P :=
    ((hW.isGaussianProcess_comp v).congr fun z => (hX z).symm).comp_right Subtype.val
  have hY0 : ∀ z, ∫ ω, Y z ω ∂P = 0 := fun z => by
    rw [integral_congr_ae (hX z)]
    exact hW.integral_eq_zero _
  have hYc : ∀ ω, Continuous fun z => Y z ω := fun ω =>
    (hXc ω).comp continuous_subtype_val
  obtain ⟨hint, hMle⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hYg hYc
    (C := M) fun n t => by simpa only [one_mul] using hfin 1 (one_mul 1) n t
  obtain ⟨hint', hMle'⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous
    (LQGMetric.SupTail.isGaussianProcess_neg hYg) (fun ω => (hYc ω).neg) (C := M)
    fun n t => by simpa only [neg_one_mul] using hfin (-1) (by norm_num) n t
  have hvar : ∀ z : B, Var[Y z; P] ≤ √V ^ 2 := fun z => by
    rw [Real.sq_sqrt hV.le, show Y z = X z from rfl,
      ((hW.hasLaw_single (v z)).congr (hX z)).variance_eq,
      variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)]
    exact hvV z
  have htail := LQGMetric.SupTail.tail_iSup_abs_le hYg hY0 hYc hint hint'
    hMle hMle' hvar hu
  rw [Real.sq_sqrt hV.le] at htail
  calc P {ω | M + u ≤ ⨆ z : B, |X z ω|}
      = ENNReal.ofReal (P.real {ω | M + u ≤ ⨆ z : B, |X z ω|}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * V))) :=
      ENNReal.ofReal_le_ofReal htail

end HigherDimLQGMetric
