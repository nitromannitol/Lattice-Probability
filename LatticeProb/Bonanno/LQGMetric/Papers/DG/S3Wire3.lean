/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3Wire3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3Wire1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3Wire2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18S6
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11R6
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19R6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Reg
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM9

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Wiring of the DG chain: DG Thm 1.5, (1.5b), Prop 3.21 from DG L3.7, DG P3.16 and DZZ
(task P2-DGWIRE)

Sources: Ding–Gwynne arXiv:1807.01072 (DG), Ding–Zeitouni–Zhang arXiv:1807.00422 (DZZ).

* `wire_dgInputs_of_dzz` — the `𝕍`-scale DG L3.11 (both orientations) / L3.19 inputs for
  `μ_ĥ = muHat … p18_hK0` on `[1/6,5/6]² = p39Box p18c0 (1/3) (1/6)` from DZZ L5.3 / L6.1 in
  the DG form (`DZZL53Whp`, `DZZL61Whp` at `μIn`), with `χ = chiDZZ γ`, `d_γ = 2/χ`
  (`dgLem311Scaled_of_input`, `l311LevelInput_muHat'`, …; S3L11R6, S3L19R6).
* `wire_dgThm1_5_of`, `wire_dgThm1_5KU_of`, `wire_dgProp3_21_of` — `DG.DGThm1_5`,
  `Blueprint.DGThm1_5KU`, `Blueprint.DGProp3_21` from `Blueprint.DGLem3_7`,
  `Blueprint.DGProp3_16` and those DZZ inputs (through S3Wire1/S3Wire2, which take L3.19 on
  `[1/6,5/6]²`; the original chain `dgThm1_5_of_inputs` asks for L3.19 on `[1/12,11/12]²`,
  which `μ_ĥ` does not satisfy, see S3Wire1).
* **`DZZInputsDG`** — the DZZ-level statements that remain: DZZ L5.3 (upper half) and L6.1
  (lower half, `α = 5/8`) at `μIn`, DZZ Prop 3.17 at `μIn` and, for pairs inside `K^ξ`, at the
  walled measures `μIn|_K` of the walls `K ∈ dgWalls` (`DZZProp317Walls`, DEC-123 §2; P-317K-ADAPT
  replaced the false walled `DZZProp317` over all pairs); `dzzInputsDGForm_of` turns them into the
  DG-form inputs through S5Adapt (`dzzL53Whp_dzzMuIn_of_upper` with `hreg` from
  `ae_wickQArea_reg`, `dzzL61Whp_of_lower`).
* **`dzzInputsDG_of_nodes`** — `DZZInputsDG` from the DZZ nodes: L5.3 upper half, L6.1 lower
  half, the `D'`-concentration `DZZConcApprox` (through `dzzProp317_dzzMuIn_ofConc`, S3CM9) and
  `DZZProp317Walls … dgWalls`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint WhiteNoise

/-- the DZZ inputs in the form used by DG (DG:1206, DG:1627): DZZ L5.3 and L6.1 w.h.p. at `μIn` -/
def DZZInputsDGForm : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      DZZL53Whp P (DZZ.dzzMuIn γ W) (chiDZZ γ) ∧
      DZZL61Whp P (DZZ.dzzMuIn γ W) (5 / 8) (chiDZZ γ) l319U

/-- **`DZZInputsDG`**: the DZZ-level statements used by the DG chain, for every white noise and
`γ ∈ (0,2)`, at `χ = chiDZZ γ`:
* the upper half of DZZ Lemma 5.3 (`DZZLem53Upper`, DZZ l. 2290–2297) at `μIn`;
* the lower half of DZZ Lemma 6.1 (`DZZLem61Lower`, DZZ l. 2588–2597) at `μIn`, `α = 5/8`;
* DZZ Proposition 3.17 (`DZZProp317`, l. 1505–1517) for all small `ξ` at `μIn`, and its walled
  form (DZZ Remark 5.2, l. 2281–2284) for the pairs inside `K^ξ` at every wall `K ∈ dgWalls`
  (`DZZProp317Walls`, DEC-123 §2). -/
def DZZInputsDG : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      DZZ.DZZLem53Upper P (DZZ.dzzMuIn γ W) (chiDZZ γ) ∧
      DZZ.DZZLem61Lower P (DZZ.dzzMuIn γ W) (5 / 8) (chiDZZ γ) ∧
      ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ (∀ ξ, 0 < ξ → ξ < ξ₀ → DZZ.DZZProp317 P (DZZ.dzzMuIn γ W) ξ) ∧
        ∀ ξ, 0 < ξ → ξ < ξ₀ → DZZ.DZZProp317Walls P (DZZ.dzzMuIn γ W) ξ DZZ.dgWalls

lemma l319U_mem_dzzVbar : l319U ∈ DZZ.dzzVbar := by
  simp only [DZZ.dzzVbar, DZZ.sqBox, mem_ofPred_eq, l319U, sub_self, abs_zero]
  norm_num

/-- `DZZInputsDG` gives the DG-form DZZ inputs (S5Adapt) -/
theorem dzzInputsDGForm_of (h : DZZInputsDG) : DZZInputsDGForm := by
  intro Ω _ P W hW γ hγ hγ2
  obtain ⟨h53, h61, ξ₀, hξ₀, h317, h317w⟩ := h P W hW γ hγ hγ2
  exact ⟨DZZ.dzzL53Whp_dzzMuIn_of_upper hξ₀ h53
      (fun u hu v hv huv ξ hξ hξ' =>
        DZZ.dzzProp317In_tildeBox_of_walls (h317w ξ hξ hξ') hu hv huv)
      (DZZ.ae_wickQArea_reg hW hγ hγ2),
    DZZ.dzzL61Whp_of_lower (by norm_num) (by norm_num) hξ₀ l319U_mem_dzzVbar h61 h317⟩

lemma wire_box16_sub :
    p39Box p18c0 (1 / 3) (1 / 6) ⊆ Icc (1 / 6 : ℝ) (5 / 6) ×ℂ Icc (1 / 6 : ℝ) (5 / 6) := by
  intro x hx
  simp only [p39Box, p18c0, Complex.mem_reProdIm, mem_Icc] at hx ⊢
  norm_num at hx ⊢
  exact hx

/-- **the `𝕍`-scale DG L3.11 / L3.19 inputs for `μ_ĥ`** on `[1/6,5/6]²` from the DZZ inputs -/
theorem wire_dgInputs_of_dzz (hD : DZZInputsDGForm) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (γ : ℝ) (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    DGLem311Scaled P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
        (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)) ∧
      DGLem311ScaledV P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
        (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)) ∧
      DGLem319Scaled P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
        (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨h53, h61⟩ := hD P W hW γ hγ hγ2
  have hd : 1 ≤ 2 / chiDZZ γ := one_le_dGamma chiLeTwo hγ hγ2
  have hχ : 0 < chiDZZ γ := chiDZZ_pos γ
  exact ⟨dgLem311Scaled_of_input hd
      (l311LevelInput_muHat' hW hγ hγ2 p18_hK0 hχ hd h53 wire_box16_sub),
    dgLem311ScaledV_of_input hd
      (l311LevelInputV_muHat' hW hγ hγ2 p18_hK0 hχ hd h53 wire_box16_sub),
    dgLem319Scaled_of_input hd (l319LevelInput_muHat hW hγ hγ2 p18_hK0 hχ h61 wire_box16_sub)⟩

/-- `R18P322` from DG L3.7 and the DZZ inputs -/
theorem wire_r18P322 (h37 : Blueprint.DGLem3_7) (hD : DZZInputsDGForm) : R18P322 := by
  obtain ⟨Ω, _, P, W, W', hz, hc, hcp, hW', h37'⟩ := dgLem37V_exists_box h37
  refine wire_r18P322_of ⟨Ω, _, P, W, W', hz, hc, hcp, hW', h37', fun δ hδ ω => ?_,
    fun δ hδ x hx => ?_⟩ (fun P W hW γ hγ hγ2 => (wire_dgInputs_of_dzz hD P W hW γ hγ hγ2).1)
    (fun P W hW γ hγ hγ2 => (wire_dgInputs_of_dzz hD P W hW γ hγ hγ2).2.1)
    (fun P W hW γ hγ hγ2 => (wire_dgInputs_of_dzz hD P W hW γ hγ hγ2).2.2)
  · rw [p18Half_eq_sqHalf]; exact hcp.2.2.2.1 δ hδ ω
  · rw [p18Half_eq_sqHalf] at hx; exact hcp.2.2.2.2 δ hδ x hx

/-- **`Blueprint.DGProp3_21`** (DG Prop 3.21) from DG L3.7 and the DZZ inputs -/
theorem wire_dgProp3_21_of (h37 : Blueprint.DGLem3_7) (hD : DZZInputsDGForm) :
    Blueprint.DGProp3_21 :=
  dgProp3_21_of (dgProp3_18Sq_of_ref (dgProp3_18SqRef_of_unit (r18Unit_of (wire_r18P322 h37 hD))))

/-- `DGP317Show` for every white noise from the DZZ inputs -/
theorem wire_dgP317Show (hD : DZZInputsDGForm) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    DGP317Show P W γ :=
  wire_dgP317Show_of_muHat hγ (one_le_dGamma chiLeTwo hγ hγ2)
    (fun P W hW => wire_dgInputs_of_dzz hD P W hW γ hγ hγ2) hW

/-- `DGProp3_15` from DG P3.16 and the DZZ inputs -/
theorem wire_dgProp3_15_of (h316 : Blueprint.DGProp3_16) (hD : DZZInputsDGForm) : DGProp3_15 :=
  dgProp3_15_of (dgProp3_17Sq_of h316 fun P W hW γ hγ hγ2 => wire_dgP317Show hD P W hW γ hγ hγ2)

/-- **`DG.DGThm1_5`** (DG Thm 1.5) from DG L3.7, DG P3.16 and the DZZ inputs -/
theorem wire_dgThm1_5_of (h37 : Blueprint.DGLem3_7) (h316 : Blueprint.DGProp3_16)
    (hD : DZZInputsDGForm) : DGThm1_5 :=
  dgThm1_5_of (wire_dgProp3_15_of h316 hD) (wire_dgProp3_21_of h37 hD)

/-- **`Blueprint.DGThm1_5KU`** (DG (1.5b)) from DG L3.7, DG P3.16 and the DZZ inputs -/
theorem wire_dgThm1_5KU_of (h37 : Blueprint.DGLem3_7) (h316 : Blueprint.DGProp3_16)
    (hD : DZZInputsDGForm) : DGThm1_5KU :=
  dgThm1_5KU_of (wire_dgProp3_15_of h316 hD) (wire_dgProp3_21_of h37 hD)

end LQGMetric.DG
