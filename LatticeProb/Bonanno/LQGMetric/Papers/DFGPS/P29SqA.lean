/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P29SqA at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenRatio
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Sq

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS zero-boundary step with DDDF Proposition 29 on the square only (P2-DDDFP29b)

Primed copies of `zb_lim_posOffDiag` (L2_8GffPos), `zb_step` (L2_8GffZB), `unitSq_setup`
(L2_8FinSetup), `aEps_lambda_W`, `aEpsDF_ratio_bdd` (L2_8GenRatio) taking
`DDDF.DDDFProp29Sq` (DDDF Prop 29 for `D = (−1,2)²` only) in place of `Blueprint.DDDFProp29`.
DFGPS (T:877–881) applies DDDF Proposition 29 only to that domain; the proofs are verbatim
except that `zb_lim_posOffDiag'` takes `D = sqOpens (-1) 3` as a hypothesis. Wiring only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP HeatSq WhiteNoise DDDF

/-- **Positivity of the limits for the zero-boundary GFF** (DFGPS T:879–881 via DDDF §6.1):
along `δ_n → 0`, every limit in law of `λ_{√δ_n}⁻¹ e^{ξ p_{δ_n/2} * h̊} ds` on `[0,1]²` (the
metrics of `Blueprint.DDDFThm1_2`) is a.s. positive off the diagonal. -/
theorem zb_lim_posOffDiag' (h11 : DDDFThm1_1) (h29 : DDDFProp29Sq) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (W' : WNSpace → Ω' → ℝ)
    (hW' : IsWhiteNoise P' W') (D : TopologicalSpace.Opens ℂ)
    (hD : Bornology.IsBounded (D : Set ℂ)) (hDsq : D = sqOpens (-1) 3) (U : Set ℂ)
    (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (hUD : closure U ⊆ (D : Set ℂ)) (hKU : closedUnitSquare ⊆ U)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xh : BddOn (D : Set ℂ) → Ω → ℝ) (hX : IsZBGFFProcessExt D Xh P) (Y : ℝ → ℂ → Ω → ℝ)
    (hY : ∀ δ ∈ Ioo (0 : ℝ) 1, IsContVersion (fun x => Xh (heatBdd D (δ / 2) x)) (Y δ) P)
    (δn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ))
    (μ : ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ))
    (hν : ∀ n, δn n ∈ Ioo (0 : ℝ) 1 ∧ (ν n : Measure _) = P.map fun ω =>
      sqMetricC (xiGamma γ) (lambdaDelta (xiGamma γ) W' P' (Real.sqrt (δn n)))
        (fun x => Y (δn n) x ω))
    (hδ : Tendsto δn atTop (𝓝 0)) (hμ : Tendsto ν atTop (𝓝 μ)) :
    ∀ᵐ d ∂(μ : Measure C(closedUnitSquare × closedUnitSquare, ℝ)), IsPosOffDiag d := by
  have := hW'.isProbabilityMeasure
  set ξ := xiGamma γ with hξ
  have hr : ∀ n, Real.sqrt (δn n) ∈ Ioo (0 : ℝ) 1 := fun n =>
    ⟨Real.sqrt_pos.2 (hν n).1.1, (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact (hν n).1.2)⟩
  obtain ⟨-, hT, hL⟩ := h11 γ hγ hγ2 P' W' hW'
  set α : ℕ → ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ) := fun n =>
    ⟨P'.map fun ω => sqMetricC ξ (lambdaDelta ξ W' P' (Real.sqrt (δn n)))
      (fun x => phiVer W' P' (Real.sqrt (δn n)) 1 x ω), inferInstance⟩ with hαdef
  refine ae_posOffDiag_of_dominated hμ (α := α) ?_ ?_ ?_
  · refine isCompact_closure_of_isTightMeasureSet (hT.subset ?_)
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨_, hr n, rfl⟩
  · intro ψ lam hψ hlim
    have hr0 : Tendsto (fun n => Real.sqrt (δn (ψ n))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp (hδ.comp hψ.tendsto_atTop)
      rw [Real.sqrt_zero] at this
      exact this
    filter_upwards [hL (fun n => Real.sqrt (δn (ψ n))) (α ∘ ψ) lam (fun n => ⟨hr _, rfl⟩)
      hr0 hlim] with d hd
    exact isPosOffDiag_of_isBiHolderSq hd
  · intro r _ ζ hζ
    subst hDsq
    obtain ⟨C, c, -, hc, hcpl⟩ := h29 U hU hUc hUD
    obtain ⟨x, hx0, hxζ⟩ := exists_gauss_tail_le (C := C) hc hζ
    refine ⟨Real.exp (|ξ| * x), Real.exp_pos _, fun η _ => ?_⟩
    filter_upwards [hδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
    set t := δn n with htdef
    have ht : t ∈ Ioo (0 : ℝ) 1 := (hν n).1
    obtain ⟨Ωn, _, Pn, Xn, Wn, Yn, hPn, hXn, hWn, hYn, htail⟩ := hcpl t ⟨ht.1, hn⟩
    have hYt := hY t ht
    have hφ := isPhiVersion_phiVer hWn (hr n).1 (hr n).2.le
    have hφ' := isPhiVersion_phiVer hW' (hr n).1 (hr n).2.le
    set lam := lambdaDelta ξ W' P' (Real.sqrt t) with hlam
    have hlam0 : 0 ≤ lam := lambdaDelta_nonneg hW' ξ (hr n).1 (hr n).2.le
    set A : Ωn → C(closedUnitSquare × closedUnitSquare, ℝ) := fun ω =>
      sqFun ξ lam (pathC Yn hYn.1 ω) with hA
    set B : Ωn → C(closedUnitSquare × closedUnitSquare, ℝ) := fun ω =>
      sqFun ξ lam (pathC (phiVer Wn Pn (Real.sqrt t) 1) hφ.cont ω) with hB
    have hAm : Measurable A := (measurable_sqFun _ _).comp (measurable_pathC hYn.1 hYn.2.1)
    have hBm : Measurable B := (measurable_sqFun _ _).comp (measurable_pathC hφ.cont hφ.meas)
    have hνA : (ν n : Measure C(closedUnitSquare × closedUnitSquare, ℝ)) = Pn.map A := by
      rw [(hν n).2]
      change P.map (fun ω => sqFun ξ lam (pathC (Y t) hYt.1 ω)) = _
      rw [map_comp_pathC hYt.1 hYt.2.1 (measurable_sqFun _ _),
        map_comp_pathC hYn.1 hYn.2.1 (measurable_sqFun _ _), map_pathC_heat_eq hX hXn hYt hYn]
    have hαB : (α n : Measure C(closedUnitSquare × closedUnitSquare, ℝ)) = Pn.map B := by
      change P'.map (fun ω => sqFun ξ lam (pathC (phiVer W' P' (Real.sqrt t) 1) hφ'.cont ω)) = _
      rw [map_comp_pathC hφ'.cont hφ'.meas (measurable_sqFun _ _),
        map_comp_pathC hφ.cont hφ.meas (measurable_sqFun _ _),
        map_pathC_phiVer_eq hW' hWn (hr n).1 (hr n).2.le]
    set E : Set Ωn := {ω | (⨆ z ∈ U, ENNReal.ofReal
      |phiVer Wn Pn (Real.sqrt t) 1 z ω - Yn z ω|) < ENNReal.ofReal x} with hE
    have hdomE : ∀ ω ∈ E, ∀ p, B ω p ≤ Real.exp (|ξ| * x) * A ω p := by
      intro ω hω p
      refine sqMetricC_le_of_abs_sub_le hlam0 (hφ.cont ω) (hYn.1 ω) (fun z hz => ?_) p
      have hle : ENNReal.ofReal |phiVer Wn Pn (Real.sqrt t) 1 z ω - Yn z ω| ≤
          ⨆ z ∈ U, ENNReal.ofReal |phiVer Wn Pn (Real.sqrt t) 1 z ω - Yn z ω| :=
        le_iSup₂ (f := fun z (_ : z ∈ U) =>
          ENNReal.ofReal |phiVer Wn Pn (Real.sqrt t) 1 z ω - Yn z ω|) z (hKU hz)
      exact ((ENNReal.ofReal_lt_ofReal_iff hx0).1 (hle.trans_lt hω)).le
    have hEc : Pn Eᶜ ≤ ENNReal.ofReal ζ := by
      have e : Eᶜ = {ω | ENNReal.ofReal x ≤
          ⨆ z ∈ U, ENNReal.ofReal |phiVer Wn Pn (Real.sqrt t) 1 z ω - Yn z ω|} := by
        ext ω; simp [hE, not_lt]
      rw [e]
      exact (htail x hx0.le).trans (ENNReal.ofReal_le_ofReal hxζ)
    rw [hνA, hαB]
    exact (map_smallSet_le_of_le_on hAm.aemeasurable hBm.aemeasurable (Real.exp_pos _) hdomE
      r η).trans (add_le_add_right hEc _)


end LQGMetric.DFGPS
