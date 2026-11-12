/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3EtaB1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta9D

/-!
# `M^W ≤ c · M̃_{γ,δ,η}` from a density comparison (P2-DZZETA2, step (2), limit part)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` (eq-M-tilde-B-bound), l. 1116–1119):
`M_γ(B̃) ≤ e^{2αγ√L log L} δ² s^{−2} M̃_{γ,ε²s,η}(B̃)` on `{M_{γ,s}(B) ≤ δ²} ∩ Ẽ_{δ,α}`. DZZ state it
without proof; it follows from the pointwise comparison of the approximating densities and the
definitions of both measures as limits ((eq-def-M-eta) l. 1209–1213, (eq-def-tilde-M) l. 677–683).
This file is the limit step (upper direction; own glue):

* `wickQArea_le_of_open`: for an open `U ⊆ (0,1)²` of finite measure, vague convergence, the density
  comparison `wickDensC ≤ c · etaDens` for large `n` and `etaApprox → etaChaos` give
  `M^W(U) ≤ c M̃(U)` (portmanteau for open sets, `eventually_lt_of_open`);
* `ae_wickQArea_le_of_closed`: for a closed `F ⊆ 𝕍`, a.s., for every `c ≥ 0`, if the comparison holds
  on the open neighbourhoods `U_m = F^{1/(m+1)} ∩ (0,1)²` for large `m`, then `M^W(F) ≤ c M̃(F)`
  (`M^W(∂𝕍) = 0`, `M̃(U_m ∖ F) → 0` a.s. as in `ae_etaChaos_le_iSup_inner`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4 SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Limit step of (eq-M-tilde-B-bound)** on an open `U ⊆ (0,1)²` (deterministic). -/
theorem wickQArea_le_of_open (hW : IsWhiteNoise P W) {γ δ c : ℝ} {ω : Ω}
    (hv : IsVagueLimitOn openSquare (fun n => wickMeasC hW γ n ω) (wickQArea γ W ω))
    {U : Set ℂ} (hU : IsOpen U) (hUS : U ⊆ openSquare)
    (hd : ∀ᶠ n in atTop, ∀ᵐ z ∂(volume.restrict U),
      wickDensC hW γ n z ω ≤ ENNReal.ofReal c * etaDens W γ δ n z ω)
    (ht : Tendsto (fun n => etaApprox W γ δ n U ω) atTop (𝓝 (etaChaos W γ δ U ω))) :
    wickQArea γ W ω U ≤ ENNReal.ofReal c * etaChaos W γ δ U ω := by
  by_contra hlt
  push Not at hlt
  obtain ⟨b, hb1, hb2⟩ := exists_between hlt
  have h1 := eventually_lt_of_open hv (fun n K' hK' _ => wickMeasC_lt_top hW γ n ω hK') hU
    hUS hb2
  have ht' : Tendsto (fun n => ENNReal.ofReal c * etaApprox W γ δ n U ω) atTop
      (𝓝 (ENNReal.ofReal c * etaChaos W γ δ U ω)) :=
    ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top)
  have h2 := (tendsto_order.1 ht').2 b hb1
  obtain ⟨n, hn1, hn2, hn3⟩ := (h1.and (h2.and hd)).exists
  have hle : wickMeasC hW γ n ω U ≤ ENNReal.ofReal c * etaApprox W γ δ n U ω := by
    rw [etaApprox, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, wickMeasC,
      withDensity_apply _ hU.measurableSet]
    exact lintegral_mono_ae hn3
  exact absurd ((hn1.trans_le hle).trans hn2) (lt_irrefl _)

/-- the open neighbourhoods `F^{1/(m+1)} ∩ (0,1)²` -/
def nbhdSq (F : Set ℂ) (m : ℕ) : Set ℂ := thickening (1 / ((m : ℝ) + 1)) F ∩ openSquare

lemma isOpen_nbhdSq (F : Set ℂ) (m : ℕ) : IsOpen (nbhdSq F m) :=
  isOpen_thickening.inter isOpen_openSquare

lemma nbhdSq_antitone (F : Set ℂ) : Antitone (nbhdSq F) := by
  intro m m' h
  refine inter_subset_inter_left _ (thickening_mono ?_ F)
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)

lemma etaChaos_mono (γ δ : ℝ) {A B : Set ℂ} (h : A ⊆ B) (ω : Ω) :
    etaChaos W γ δ A ω ≤ etaChaos W γ δ B ω :=
  liminf_le_liminf (Eventually.of_forall fun _ => lintegral_mono_set h)

/-- **no mass of `M̃` outside a closed `F`, in the limit**: a.s. `M̃(U_m ∖ F) → 0` -/
lemma ae_tendsto_etaChaos_nbhdSq_diff (hW : IsWhiteNoise P W) (γ δ : ℝ) {F : Set ℂ}
    (hF : IsClosed F) :
    ∀ᵐ ω ∂P, Tendsto (fun m => etaChaos W γ δ (nbhdSq F m \ F) ω) atTop (𝓝 0) := by
  set D : ℕ → Set ℂ := fun m => nbhdSq F m \ F with hD
  have hDm : ∀ m, MeasurableSet (D m) := fun m =>
    (isOpen_nbhdSq F m).measurableSet.diff hF.measurableSet
  have hDa : Antitone D := fun m m' h => diff_subset_diff_left (nbhdSq_antitone F h)
  have hfin : ∀ m, volume (D m) ≠ ⊤ := fun m =>
    (volume_lt_top_of_subset_dzzV ((diff_subset.trans inter_subset_right).trans
      openSquare_subset_dzzV)).ne
  have hDvol : ⨅ m, volume (D m) = 0 := by
    rw [← hDa.measure_iInter (fun m => (hDm m).nullMeasurableSet) ⟨0, hfin 0⟩]
    have : (⋂ m, D m) = ∅ := by
      refine eq_empty_of_forall_notMem fun z hz => ?_
      simp only [mem_iInter, hD, nbhdSq, mem_diff, mem_inter_iff] at hz
      refine (hz 0).2 ?_
      rw [← hF.closure_eq, Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨w, hw, hdw⟩ := Metric.mem_thickening_iff.1 (hz m).1.1
      exact ⟨w, hw, hdw.trans hm⟩
    rw [this, measure_empty]
  have hY : ∀ᵐ ω ∂P, ⨅ m, etaChaos W γ δ (D m) ω = 0 := by
    have hm : Measurable fun ω => ⨅ m, etaChaos W γ δ (D m) ω :=
      Measurable.iInf fun m => measurable_etaChaos hW γ δ (D m)
    refine (lintegral_eq_zero_iff hm).1 (le_antisymm ?_ zero_le)
    rw [← hDvol]
    refine le_iInf fun m => ?_
    exact (lintegral_mono fun ω => iInf_le _ m).trans (lintegral_etaChaos_le hW γ δ (hDm m))
  filter_upwards [hY] with ω hω
  have hanti : Antitone fun m => etaChaos W γ δ (D m) ω :=
    fun m m' h => etaChaos_mono γ δ (hDa h) ω
  rw [← hω]
  exact tendsto_atTop_iInf hanti

/-- **(eq-M-tilde-B-bound), limit step** for a closed `F ⊆ 𝕍`: a.s., for every `c`, the density
comparison on the neighbourhoods `U_m` (large `m`) gives `M^W(F) ≤ c M̃(F)`. -/
theorem ae_wickQArea_le_of_closed (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (δ : ℝ) {F : Set ℂ} (hF : IsClosed F) (hFV : F ⊆ dzzV) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, (∀ᶠ m in atTop, ∀ᶠ n in atTop, ∀ᵐ z ∂(volume.restrict (nbhdSq F m)),
      wickDensC hW γ n z ω ≤ ENNReal.ofReal c * etaDens W γ δ n z ω) →
      wickQArea γ W ω F ≤ ENNReal.ofReal c * etaChaos W γ δ F ω := by
  have hfin : ∀ {A : Set ℂ}, A ⊆ dzzV → volume A ≠ ⊤ := fun hA =>
    (volume_lt_top_of_subset_dzzV hA).ne
  have hUV : ∀ m, nbhdSq F m ⊆ dzzV := fun m => inter_subset_right.trans openSquare_subset_dzzV
  have hT : ∀ᵐ ω ∂P, ∀ m, Tendsto (fun n => etaApprox W γ δ n (nbhdSq F m) ω) atTop
      (𝓝 (etaChaos W γ δ (nbhdSq F m) ω)) := ae_all_iff.2 fun m =>
    ae_tendsto_etaApprox hW γ δ (isOpen_nbhdSq F m).measurableSet (hfin (hUV m))
  have hT1 : ∀ᵐ ω ∂P, ∀ m, Tendsto (fun n => etaApprox W γ δ n (nbhdSq F m \ F) ω) atTop
      (𝓝 (etaChaos W γ δ (nbhdSq F m \ F) ω)) := ae_all_iff.2 fun m =>
    ae_tendsto_etaApprox hW γ δ ((isOpen_nbhdSq F m).measurableSet.diff hF.measurableSet)
      (hfin (diff_subset.trans (hUV m)))
  have hT2 : ∀ᵐ ω ∂P, ∀ m, Tendsto (fun n => etaApprox W γ δ n (nbhdSq F m ∩ F) ω) atTop
      (𝓝 (etaChaos W γ δ (nbhdSq F m ∩ F) ω)) := ae_all_iff.2 fun m =>
    ae_tendsto_etaApprox hW γ δ ((isOpen_nbhdSq F m).measurableSet.inter hF.measurableSet)
      (hfin (inter_subset_right.trans hFV))
  filter_upwards [ae_isVagueLimitOn_wickMeasC hW hγ hγ2, hT, hT1, hT2,
    ae_tendsto_etaChaos_nbhdSq_diff hW γ δ hF] with ω hv hT hT1 hT2 hY c hd
  -- `M̃(U_m) = M̃(U_m ∩ F) + M̃(U_m ∖ F) ≤ M̃(F) + M̃(U_m ∖ F)`
  have hsplit : ∀ m, etaChaos W γ δ (nbhdSq F m) ω ≤
      etaChaos W γ δ F ω + etaChaos W γ δ (nbhdSq F m \ F) ω := by
    intro m
    have e : etaChaos W γ δ (nbhdSq F m) ω =
        etaChaos W γ δ (nbhdSq F m ∩ F) ω + etaChaos W γ δ (nbhdSq F m \ F) ω := by
      refine tendsto_nhds_unique (hT m) ?_
      have e' : (fun n => etaApprox W γ δ n (nbhdSq F m) ω) = fun n =>
          etaApprox W γ δ n (nbhdSq F m ∩ F) ω + etaApprox W γ δ n (nbhdSq F m \ F) ω := by
        funext n
        exact (lintegral_inter_add_diff _ _ hF.measurableSet).symm
      rw [e']
      exact (hT2 m).add (hT1 m)
    rw [e]
    exact add_le_add_left (etaChaos_mono γ δ inter_subset_right ω) _
  -- `M^W(F) ≤ M^W(U_m)` (`M^W` does not charge `∂𝕍`)
  have hFU : ∀ m, wickQArea γ W ω F ≤ wickQArea γ W ω (nbhdSq F m) := by
    intro m
    have h0 : wickQArea γ W ω openSquareᶜ = 0 := hv.1
    calc wickQArea γ W ω F ≤ wickQArea γ W ω (F ∩ openSquare ∪ openSquareᶜ) :=
          measure_mono fun z hz => by
            by_cases h : z ∈ openSquare
            · exact Or.inl ⟨hz, h⟩
            · exact Or.inr h
      _ ≤ wickQArea γ W ω (F ∩ openSquare) + wickQArea γ W ω openSquareᶜ := measure_union_le _ _
      _ = wickQArea γ W ω (F ∩ openSquare) := by rw [h0, add_zero]
      _ ≤ wickQArea γ W ω (nbhdSq F m) := measure_mono fun z hz =>
          ⟨self_subset_thickening (by positivity) F hz.1, hz.2⟩
  have hlim : Tendsto (fun m => ENNReal.ofReal c *
      (etaChaos W γ δ F ω + etaChaos W γ δ (nbhdSq F m \ F) ω)) atTop
      (𝓝 (ENNReal.ofReal c * etaChaos W γ δ F ω)) := by
    have := ENNReal.Tendsto.const_mul
      ((tendsto_const_nhds (x := etaChaos W γ δ F ω)).add hY) (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal c)
    simpa using this
  refine ge_of_tendsto hlim ?_
  filter_upwards [hd] with m hm
  exact (hFU m).trans ((wickQArea_le_of_open hW hv (isOpen_nbhdSq F m) inter_subset_right hm
    (hT m)).trans (mul_le_mul_right (hsplit m) _))

end DZZ
end LQGMetric
