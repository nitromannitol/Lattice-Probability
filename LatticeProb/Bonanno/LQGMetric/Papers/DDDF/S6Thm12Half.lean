/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm12Half at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm12

/-!
# DDDF Theorem 1 (2) for `D = (−1,2)²`: tightness over `δ ∈ (0,1/2)` (task P2-DDDF6e, O9)

DDDF = arXiv:1904.08021, `tightness.tex` l. 160–161, 1497–1498 (Theorem 1 (2) as a corollary of
Prop 29 and Theorem 1 (1)); see `S6Thm12` for the argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF
namespace S6Thm

open WhiteNoise Blueprint DFGPS HeatSq

local notation "SQ" => C(closedUnitSquare × closedUnitSquare, ℝ)

/-- **DDDF Theorem 1 (2)** for `D = (−1,2)²` (the domain DFGPS uses), tightness of the laws for
`δ ∈ (0,1/2)`, from Theorem 1 (1) and Prop 29 on the square. -/
theorem s6_thm12_tight_half (h11 : DDDFThm1_1) (h29 : DDDFProp29Sq) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (W' : WNSpace → Ω' → ℝ)
    (hW' : IsWhiteNoise P' W') {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ)
    (hX : IsZBGFFProcessExt (sqOpens (-1) 3) Xh P) (Y : ℝ → ℂ → Ω → ℝ)
    (hY : ∀ δ ∈ Ioo (0 : ℝ) 1,
      IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) (δ / 2) x)) (Y δ) P) :
    IsTightMeasureSet {μ | ∃ δ ∈ Ioo (0 : ℝ) (1 / 2), μ = P.map fun ω =>
      sqMetricC (xiGamma γ) (lambdaDelta (xiGamma γ) W' P' (Real.sqrt δ)) (fun x => Y δ x ω)} := by
  have := hW'.isProbabilityMeasure
  set ξ := xiGamma γ with hξ
  have hhalf : ∀ δ ∈ Ioo (0 : ℝ) (1 / 2), δ ∈ Ioo (0 : ℝ) 1 := fun δ hδ =>
    ⟨hδ.1, hδ.2.trans (by norm_num)⟩
  have hr : ∀ δ ∈ Ioo (0 : ℝ) 1, Real.sqrt δ ∈ Ioo (0 : ℝ) 1 := fun δ hδ =>
    ⟨Real.sqrt_pos.2 hδ.1, (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hδ.2)⟩
  obtain ⟨-, hT, -⟩ := h11 γ hγ hγ2 P' W' hW'
  -- the laws of Theorem 1 (1) vanish on the diagonal
  have hdiag : ∀ μ ∈ {μ | ∃ δ ∈ Ioo (0 : ℝ) 1, μ = P'.map fun ω => sqMetricC ξ
      (lambdaDelta ξ W' P' δ) (fun x => phiVer W' P' δ 1 x ω)},
      μ {d : SQ | ¬ ∀ x, d (x, x) = 0} = 0 := by
    rintro μ ⟨δ, hδ, rfl⟩
    have hφ := isPhiVersion_phiVer hW' hδ.1 hδ.2.le
    refine measure_mono_null (t := (pmetSet closedUnitSquare)ᶜ) (fun d hd h => hd h.1) ?_
    rw [Measure.map_apply (measurable_sqMetric_path hφ.cont hφ.meas _ _)
      (isClosed_pmetSet _).isOpen_compl.measurableSet]
    convert measure_empty (μ := P')
    ext ω
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact pmet_sq (lambdaDelta_nonneg hW' ξ hδ.1 hδ.2.le) (hφ.cont ω)
  have hU : IsOpen (sqOpen (-1 / 2) 2) := isOpen_sqOpen _ _
  have hUc : closure (sqOpen (-1 / 2) 2) ⊆ ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) :
      Set ℂ) := fun z hz => by
    obtain ⟨h1, h2, h3, h4⟩ := closure_sqOpen_subset _ _ hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hKU : closedUnitSquare ⊆ sqOpen (-1 / 2) 2 :=
    fun z ⟨h1, h2, h3, h4⟩ => ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨C, c, -, hc, hcpl⟩ := h29 (sqOpen (-1 / 2) 2) hU (isBounded_sqOpen _ _).isCompact_closure
    hUc
  have : ConnectedSpace closedUnitSquare := isConnected_iff_connectedSpace.1
    (DFGPS.convex_closedUnitSquare.isConnected ⟨0, by simp [closedUnitSquare]⟩)
  refine LFPP.isTightMeasureSet_of_modulus _ ?_ ?_
  · rintro μ ⟨δ, hδ, rfl⟩
    have hYδ := hY δ (hhalf δ hδ)
    have hms : MeasurableSet (pmetSet closedUnitSquare)ᶜ :=
      (isClosed_pmetSet _).isOpen_compl.measurableSet
    have e : {d : SQ | ¬ ((∀ x, d (x, x) = 0) ∧ ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z))} =
        (pmetSet closedUnitSquare)ᶜ := rfl
    rw [e, Measure.map_apply (measurable_sqMetric_path hYδ.1 hYδ.2.1 _ _) hms]
    convert measure_empty (μ := P)
    ext ω
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact pmet_sq (lambdaDelta_nonneg hW' ξ (hr δ (hhalf δ hδ)).1 (hr δ (hhalf δ hδ)).2.le)
      (hYδ.1 ω)
  · intro ζ hζ
    obtain ⟨x, hx0, hxζ⟩ := exists_gauss_tail_le (C := C) hc (half_pos hζ)
    set M : ℝ := Real.exp (|ξ| * x)
    have hM : 0 < M := Real.exp_pos _
    set ζ₁ : ℝ := min (ζ / 2) (ζ / M)
    have hζ₁ : 0 < ζ₁ := lt_min (half_pos hζ) (div_pos hζ hM)
    obtain ⟨η, hη, hmod⟩ := modulus_of_tight hT hdiag hζ₁
    refine ⟨η, hη, ?_⟩
    rintro μ ⟨δ, hδ, rfl⟩
    have hδ1 := hhalf δ hδ
    obtain ⟨Ωn, _, Pn, Xn, Wn, Yn, hPn, hXn, hWn, hYn, htail⟩ := hcpl δ hδ
    have hYt := hY δ hδ1
    have hφ := isPhiVersion_phiVer hWn (hr δ hδ1).1 (hr δ hδ1).2.le
    have hφ' := isPhiVersion_phiVer hW' (hr δ hδ1).1 (hr δ hδ1).2.le
    set lam := lambdaDelta ξ W' P' (Real.sqrt δ) with hlam
    have hlam0 : 0 ≤ lam := lambdaDelta_nonneg hW' ξ (hr δ hδ1).1 (hr δ hδ1).2.le
    set A : Ωn → SQ := fun ω => sqFun ξ lam (pathC Yn hYn.1 ω) with hA
    set B : Ωn → SQ := fun ω =>
      sqFun ξ lam (pathC (phiVer Wn Pn (Real.sqrt δ) 1) hφ.cont ω) with hB
    have hAm : Measurable A := (measurable_sqFun _ _).comp (measurable_pathC hYn.1 hYn.2.1)
    have hBm : Measurable B := (measurable_sqFun _ _).comp (measurable_pathC hφ.cont hφ.meas)
    have hνA : (P.map fun ω => sqMetricC ξ lam (fun x => Y δ x ω)) = Pn.map A := by
      change P.map (fun ω => sqFun ξ lam (pathC (Y δ) hYt.1 ω)) = _
      rw [map_comp_pathC hYt.1 hYt.2.1 (measurable_sqFun _ _),
        map_comp_pathC hYn.1 hYn.2.1 (measurable_sqFun _ _), map_pathC_heat_eq hX hXn hYt hYn]
    have hαB : (P'.map fun ω => sqMetricC ξ lam (fun x => phiVer W' P' (Real.sqrt δ) 1 x ω)) =
        Pn.map B := by
      change P'.map (fun ω => sqFun ξ lam (pathC (phiVer W' P' (Real.sqrt δ) 1) hφ'.cont ω)) = _
      rw [map_comp_pathC hφ'.cont hφ'.meas (measurable_sqFun _ _),
        map_comp_pathC hφ.cont hφ.meas (measurable_sqFun _ _),
        map_pathC_phiVer_eq hW' hWn (hr δ hδ1).1 (hr δ hδ1).2.le]
    set E : Set Ωn := {ω | (⨆ z ∈ sqOpen (-1 / 2) 2, ENNReal.ofReal
      |phiVer Wn Pn (Real.sqrt δ) 1 z ω - Yn z ω|) < ENNReal.ofReal x} with hE
    have hdomE : ∀ ω ∈ E, ∀ p, A ω p ≤ M * B ω p := by
      intro ω hω p
      refine sqMetricC_le_of_abs_sub_le hlam0 (hYn.1 ω) (hφ.cont ω) (fun z hz => ?_) p
      have hle : ENNReal.ofReal |phiVer Wn Pn (Real.sqrt δ) 1 z ω - Yn z ω| ≤
          ⨆ z ∈ sqOpen (-1 / 2) 2, ENNReal.ofReal |phiVer Wn Pn (Real.sqrt δ) 1 z ω - Yn z ω| :=
        le_iSup₂ (f := fun z (_ : z ∈ sqOpen (-1 / 2) 2) =>
          ENNReal.ofReal |phiVer Wn Pn (Real.sqrt δ) 1 z ω - Yn z ω|) z (hKU hz)
      rw [abs_sub_comm]
      exact ((ENNReal.ofReal_lt_ofReal_iff hx0).1 (hle.trans_lt hω)).le
    have hEc : Pn Eᶜ ≤ ENNReal.ofReal (ζ / 2) := by
      have e : Eᶜ = {ω | ENNReal.ofReal x ≤
          ⨆ z ∈ sqOpen (-1 / 2) 2, ENNReal.ofReal
            |phiVer Wn Pn (Real.sqrt δ) 1 z ω - Yn z ω|} := by
        ext ω; simp [hE, not_lt]
      rw [e]
      exact (htail x hx0.le).trans (ENNReal.ofReal_le_ofReal hxζ)
    have hmodB : (Pn.map B) (modBad η (ζ / M)) ≤ ENNReal.ofReal (ζ / 2) := by
      rw [← hαB]
      refine (measure_mono fun d hd => ?_).trans ((hmod _ ⟨Real.sqrt δ, hr δ hδ1, rfl⟩).trans
        (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
      simp only [modBad, mem_ofPred_eq, not_forall, not_le] at hd ⊢
      obtain ⟨z, w, hzw, hlt⟩ := hd
      exact ⟨z, w, hzw, lt_of_le_of_lt (min_le_right _ _) hlt⟩
    change (P.map fun ω => sqMetricC ξ lam (fun x => Y δ x ω)) (modBad η ζ) ≤ _
    rw [hνA]
    calc (Pn.map A) (modBad η ζ) ≤ (Pn.map B) (modBad η (ζ / M)) + Pn Eᶜ :=
          map_mod_le_of_le_on hAm hBm hM hdomE η ζ
      _ ≤ ENNReal.ofReal (ζ / 2) + ENNReal.ofReal (ζ / 2) := add_le_add hmodB hEc
      _ = ENNReal.ofReal ζ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end S6Thm
end DDDF
end LQGMetric
