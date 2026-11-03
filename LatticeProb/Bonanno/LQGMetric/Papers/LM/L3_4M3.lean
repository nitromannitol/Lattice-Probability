/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4M3 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M1
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LM Lemma 3.1, canonical nesting: the Gaussian-space picture (task P2-LM34c)

Source: MQ arXiv:1812.03913 `lqg_geodesics.tex`, proof of Prop 4.3 (l. 693–700), and the
Markov property LM arXiv:1905.00379 Lemma 2.1 in its Gaussian-space form (GMSh
arXiv:1807.07511 Lemma 2.2; `Field/Markov*.lean`): the zero-boundary part of
`Y_k = lmScaled h (r_k)` on `B_1` is the orthogonal projection onto
`K_k = cmIso_{Y_k}(H₀¹(B_1))`, and `K_{k+1} ⊆ K_k` (scaling, `range_cmIso_lmScaled`).

Vectors (all in the Gaussian space of `h`): `pv k φ = [⟨Y_k, φ⟩]`, `z k φ = P_{K_k}`-part
(`extVec`), `a k φ = pv k φ − z k φ` (harmonic part), `κ_j` the vector of
`h_{r_{j+1}}(0) − h_{r_j}(0)`, and the increments
`δ_0 φ = a_0 φ`, `δ_{j+1} φ = ρ⁻² z_j(φ(·/ρ)) − z_{j+1} φ − (∫φ) P_{K_j} κ_j`
(`ρ = r_{j+1}/r_j`). Main facts: `δ_{j+1} ∈ K_j`, `δ_i ⊥ K_i`, hence
`δ_{j+1} ⊥ δ_i` (`i ≤ j`) and `δ_j ⊥ pv_j − δ_j` (MQ: `D_{j+1}` is the harmonic part of the
zero-boundary field `h̊^{r_j}`, independent of `𝓕_{r_j}`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric.LM

open Blueprint QuantumZipper QuantumZipper.K3 MarkovZB MarkovExt MarkovGauss MarkovNorm

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- `⟨lmScaled h (r c), φ⟩ = c⁻² ⟨lmScaled h r, φ(·/c)⟩ − (h_{rc}(0) − h_r(0)) ∫ φ` -/
lemma lmScaled_mul_apply (h : Ω → DistC) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) (φ : TestC)
    (ω : Ω) :
    lmScaled h (r * c) ω φ = (c ^ 2)⁻¹ * lmScaled h r ω (testAffinePull c 0 φ) -
      (circleAvg (h ω) (r * c) 0 - circleAvg (h ω) r 0) * ∫ x, φ x := by
  simp only [lmScaled, recentre]
  rw [GFFInv.affineComp_apply, GFFInv.affineComp_apply, GFFInv.addConst_apply,
    GFFInv.addConst_apply, GFFInv.integral_testAffinePull φ (mul_pos hr hc),
    GFFInv.integral_testAffinePull _ hr, GFFInv.integral_testAffinePull φ hc,
    testAffinePull_mul hr.ne' hc.ne']
  field_simp
  ring

lemma lmScaled_apply_of_mean_zero (h : Ω → DistC) {r : ℝ} (hr : 0 < r) (ψ : TestC0) (ω : Ω) :
    lmScaled h r ω ψ.1 = (r ^ 2)⁻¹ * h ω (GFFInv.pull0 r 0 hr ψ).1 := by
  simp only [lmScaled, recentre]
  rw [GFFInv.affineComp_apply, GFFInv.addConst_apply, GFFInv.integral_testAffinePull _ hr,
    ψ.2, mul_zero, zero_mul, add_zero]
  rfl

/-- the Gaussian space of `lmScaled h r` lies in that of `h` -/
lemma gaussSpace_lmScaled_le (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) :
    gaussSpace (pairProc (lmScaled h r)) (memLp_pair (isWholePlaneGFF_lmScaled hh hr)) ≤
      gaussSpace (pairProc h) (memLp_pair hh) := by
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
    (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨ψ, rfl⟩
  have e : (memLp_pair (isWholePlaneGFF_lmScaled hh hr) ψ).toLp (pairProc (lmScaled h r) ψ) =
      (r ^ 2)⁻¹ • (memLp_pair hh (GFFInv.pull0 r 0 hr ψ)).toLp
        (pairProc h (GFFInv.pull0 r 0 hr ψ)) := by
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ω => ?_)
    simp only [pairProc, Pi.smul_apply, smul_eq_mul]
    exact lmScaled_apply_of_mean_zero h hr ψ ω
  show (memLp_pair (isWholePlaneGFF_lmScaled hh hr) ψ).toLp (pairProc (lmScaled h r) ψ) ∈ _
  rw [e]
  exact Submodule.smul_mem _ _ (toLp_mem_gaussSpace (memLp_pair hh) _)

lemma ratio_pos {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (j : ℕ) : 0 < r (j + 1) / r j :=
  div_pos (hr (j + 1)) (hr j)

variable (hh : IsNormalizedWPGFF h P) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
include hh hr

/-- `Y_k = lmScaled h (r_k)` is a normalized whole-plane GFF -/
lemma nY (k : ℕ) : IsNormalizedWPGFF (lmScaled h (r k)) P :=
  isNormalizedWPGFF_lmScaled hh.1 (hr k)

/-- `pv k φ = [⟨Y_k, φ⟩]` -/
def nPV (k : ℕ) (φ : TestC) : Lp ℝ 2 P := pairVec (nY hh hr k) φ

/-- the zero-boundary part `[⟨h̊_k, φ⟩]` of `Y_k` on `B_1` -/
def nZ (k : ℕ) (φ : TestC) : Lp ℝ 2 P :=
  extVec (nY hh hr k).1 (ballO 0 1) (((ballO (0 : ℂ) 1 : Opens ℂ) : Set ℂ).indicator φ)

/-- the harmonic part `[⟨G_k, φ⟩] = pv − z` -/
def nA (k : ℕ) (φ : TestC) : Lp ℝ 2 P := nPV hh hr k φ - nZ hh hr k φ

/-- `K_k = cmIso_{Y_k}(H₀¹(B_1))` -/
def nK (k : ℕ) : Submodule ℝ (Lp ℝ 2 P) :=
  LinearMap.range (cmIso (nY hh hr k).1 (ballO 0 1)).toLinearMap

lemma completeSpace_nK (k : ℕ) : CompleteSpace (nK hh hr k) := by
  have hcl : IsClosed (Set.range (cmIso (nY hh hr k).1 (ballO 0 1))) :=
    (cmIso (nY hh hr k).1 (ballO 0 1)).isometry.isClosedEmbedding.isClosed_range
  exact hcl.completeSpace_coe

/-- the orthogonal projection onto `K_k` -/
def nProj (k : ℕ) (v : Lp ℝ 2 P) : Lp ℝ 2 P :=
  haveI := completeSpace_nK hh hr k
  (nK hh hr k).starProjection v

lemma nProj_mem (k : ℕ) (v : Lp ℝ 2 P) : nProj hh hr k v ∈ nK hh hr k := by
  haveI := completeSpace_nK hh hr k
  exact (nK hh hr k).starProjection_apply_mem v

lemma inner_sub_nProj (k : ℕ) (v w : Lp ℝ 2 P) (hw : w ∈ nK hh hr k) :
    ⟪v - nProj hh hr k v, w⟫ = 0 := by
  haveI := completeSpace_nK hh hr k
  have h1 := (nK hh hr k).sub_starProjection_mem_orthogonal v
  exact (Submodule.mem_orthogonal' _ _).1 h1 w hw

lemma nZ_mem (k : ℕ) (φ : TestC) : nZ hh hr k φ ∈ nK hh hr k :=
  LinearMap.mem_range_self _ _

lemma nK_le_gauss (k : ℕ) : nK hh hr k ≤ gaussSpace (pairProc h) (memLp_pair hh.1) := by
  rintro _ ⟨v, rfl⟩
  exact gaussSpace_lmScaled_le hh.1 (hr k) (cmIso_mem_gaussSpace _ _ v)

lemma nPV_mem (k : ℕ) (φ : TestC) :
    nPV hh hr k φ ∈ gaussSpace (pairProc h) (memLp_pair hh.1) :=
  gaussSpace_lmScaled_le hh.1 (hr k) (pairVec_mem_gaussSpace (nY hh hr k) φ)

/-- the projection identity: `a k φ ⊥ K_k` -/
lemma inner_nA (k : ℕ) (φ : TestC) (w : Lp ℝ 2 P) (hw : w ∈ nK hh hr k) :
    ⟪nA hh hr k φ, w⟫ = 0 := by
  obtain ⟨v, rfl⟩ := hw
  have hb : Bornology.IsBounded ((ballO (0 : ℂ) 1 : Opens ℂ) : Set ℂ) := by
    simpa [ballO] using (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) 1))
  exact inner_pairVec_sub_extVec (nY hh hr k) (disjoint_ballO_sphere le_rfl) hb φ v

/-- `K_{j+1} ⊆ K_j` -/
lemma nK_succ_le (hA : Antitone r) (j : ℕ) : nK hh hr (j + 1) ≤ nK hh hr j := by
  have hc := ratio_pos hr j
  have hc1 : r (j + 1) / r j ≤ 1 := (div_le_one (hr j)).2 (hA (Nat.le_succ j))
  have e : r (j + 1) = r j * (r (j + 1) / r j) := by field_simp [(hr j).ne']
  have hR := range_cmIso_lmScaled hh.1 (hr j) hc
  rintro _ ⟨v, rfl⟩
  have h1 : cmIso (nY hh hr (j + 1)).1 (ballO 0 1) v ∈
      Set.range (cmIso (isWholePlaneGFF_lmScaled hh.1 (mul_pos (hr j) hc)) (ballO 0 1)) := by
    have : ∀ (s : ℝ) (hs : 0 < s), s = r j * (r (j + 1) / r j) →
        cmIso (isWholePlaneGFF_lmScaled hh.1 hs) (ballO 0 1) v ∈
        Set.range (cmIso (isWholePlaneGFF_lmScaled hh.1 (mul_pos (hr j) hc)) (ballO 0 1)) := by
      rintro s hs rfl; exact ⟨v, rfl⟩
    exact this _ (hr (j + 1)) e
  rw [hR] at h1
  obtain ⟨u, hu⟩ := h1
  have h2 := MarkovGermVer.cmIso_mem_range_of_le (isWholePlaneGFF_lmScaled hh.1 (hr j))
    (U := ballO 0 (r (j + 1) / r j)) (V := ballO 0 1) (fun x hx => by
      have := (mem_ballO_iff x _).1 hx
      exact (mem_ballO_iff x 1).2 (lt_of_lt_of_le this hc1)) u
  obtain ⟨w, hw⟩ := h2
  refine ⟨w, ?_⟩
  change cmIso _ (ballO 0 1) w = cmIso _ (ballO 0 1) v
  exact hw.trans hu

lemma nK_anti (hA : Antitone r) {i j : ℕ} (hij : i ≤ j) : nK hh hr j ≤ nK hh hr i := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact (nK_succ_le hh hr hA _).trans ih

end LQGMetric.LM
