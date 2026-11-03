/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer2D at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2C

/-!
# Germ measurability of the harmonic part, bounded `V` (task P2-MKD2)

* `mem_range_cmIso_of_orth` (node (b) of `handoff/P2-MKD.md`): a whole-plane Dirichlet pairing
  orthogonal to `S(B_ε(ℂ∖V))` is a Dirichlet pairing on `V` (bounded `V`). From the core estimate
  `exists_zsSub_approx` with the cutoffs `θ` (`= 0` where `d ≤ ε/4`, `= 1` where `d ≥ ε/2`) and
  `ζ` (`= 1` where `ε/4 ≤ d ≤ ε/2`, supported in `ε/8 < d < 3ε/4`), `d = dist(·, ℂ∖V)`, the Schur
  bound `logCov_self_le_schur`, density of `∇C_c^∞(ℂ)` and the closed range of `cmIso hh V`.
* `exists_germ_version_harm_of_bdd`: leaf (D) for bounded `V` (with `pair_mem_range_cmIso_top`
  and `exists_germ_version_harm_of_dirichlet`).

Sources: Sheffield math/0312099 §2.6 (Thm 2.17); Miller–Sheffield IG4 (arXiv:1302.4738)
Prop. 2.8; Berestycki–Powell arXiv:2404.16642 Thm 1.52, Lemma 1.53.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovGermVer

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm Blueprint QuantumZipper
  QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the bump `ζ` of the germ step -/
lemma exists_zeta (V : Set ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ζ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧
      (∀ x, ζ x ≠ 0 → ε / 8 < dV V x ∧ dV V x < 3 * ε / 4) ∧
      (∀ x, ε / 4 ≤ dV V x → dV V x ≤ ε / 2 → ζ x = 1) := by
  have hc := continuous_dV V
  obtain ⟨ζ, hs, hr, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (s := {x | ε / 8 < dV V x} ∩ {x | dV V x < 3 * ε / 4})
    (t := {x | ε / 4 ≤ dV V x} ∩ {x | dV V x ≤ ε / 2})
    ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))
    ((isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const))
    (fun x hx => by
      obtain ⟨h1, h2⟩ := hx
      simp only [mem_setOf_eq] at h1 h2
      exact ⟨show ε / 8 < dV V x by linarith, show dV V x < 3 * ε / 4 by linarith⟩)
  refine ⟨ζ, hs, fun x => hr (mem_range_self x), fun x hx => ?_,
    fun x ha hb => (h1 x).1 ⟨ha, hb⟩⟩
  have : x ∈ Function.support ζ := hx
  rw [hsupp] at this; exact this

/-- **Node (b), the germ step**: a whole-plane Dirichlet pairing orthogonal to
`S(B_ε(ℂ∖V))` is a Dirichlet pairing on `V` (bounded `V`). -/
theorem mem_range_cmIso_of_orth (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hVb : Bornology.IsBounded (V : Set ℂ)) {ε : ℝ} (hε : 0 < ε)
    (v : gradClosure ((⊤ : Opens ℂ) : Set ℂ) (zeroSpace ((⊤ : Opens ℂ) : Set ℂ)))
    (hv : ∀ u ∈ germSpan hh.1 (nbhdO ε (V : Set ℂ)ᶜ), ⟪u, cmIso hh.1 ⊤ v⟫ = 0) :
    cmIso hh.1 ⊤ v ∈ Set.range (cmIso hh.1 V) := by
  set O : Set ℂ := (nbhdO ε (V : Set ℂ)ᶜ : Set ℂ) with hO
  have hc := continuous_dV (V : Set ℂ)
  obtain ⟨θ, hθs, hθ01, hθ0, hθ1⟩ := exists_dcut (V : Set ℂ) (a := ε / 4) (b := ε / 2)
    (by linarith)
  obtain ⟨hθc, -, hθV⟩ := tsupport_sub_of_dV hVb (by positivity) hθ0
  obtain ⟨ζ, hζs, hζ01, hζ0, hζ1⟩ := exists_zeta (V : Set ℂ) hε
  obtain ⟨hζc, -, hζV⟩ := tsupport_sub_of_dV hVb (by positivity : (0 : ℝ) < ε / 8)
    fun x hx => (hζ0 x hx).1
  have hζO : tsupport ζ ⊆ O := by
    refine (closure_minimal (fun x hx => (hζ0 x hx).2.le) (isClosed_le hc continuous_const)).trans
      fun x hx => mem_nbhdO_of_dV hVb (lt_of_le_of_lt hx (by linarith))
  set C : Set ℂ := {x | dV V x ≤ ε / 2}
  have hCc : IsClosed C := isClosed_le hc continuous_const
  have hCO : C ⊆ O := fun x hx => mem_nbhdO_of_dV hVb (lt_of_le_of_lt hx (by linarith))
  have hθC : ∀ x, x ∉ C → θ =ᶠ[𝓝 x] fun _ => 1 := fun x hx => by
    filter_upwards [(isOpen_lt continuous_const hc).mem_nhds
      (show ε / 2 < dV V x from not_le.1 hx)] with y hy
    exact hθ1 y (le_of_lt hy)
  obtain ⟨K, hK⟩ := (hθc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((smooth_le hθs 1).continuous_fderiv one_ne_zero)
  have hζθ : ∀ x, fderiv ℝ θ x ≠ 0 → ζ x = 1 := fun x hx => by
    obtain ⟨h1, h2⟩ := dcut_fderiv_ne_zero hθ0 hθ1 hx
    exact hζ1 x h1 h2
  obtain ⟨R, hR⟩ := hVb.subset_closedBall (0 : ℂ)
  set R' := max R 0
  set Lc := 2 * (2 * R' * (Real.pi * (2 * R') ^ 2) + logBallConst)
  have hLc : 0 ≤ Lc := by have := logBallConst_nonneg; positivity
  have hSchur : ∀ p : ℂ → ℝ, Continuous p → (∀ x, ζ x = 0 → p x = 0) →
      logCov p p ≤ Lc * ∫ x, p x ^ 2 := fun p hp hpζ =>
    logCov_self_le_schur (le_max_right R 0) hp fun x hx => hpζ x (by
      by_contra hne
      have hxV : x ∈ (V : Set ℂ) := hζV (subset_tsupport _ hne)
      have := mem_closedBall_zero_iff.1 (hR hxV)
      linarith [le_max_left R 0])
  have hw : ∀ ψ : TestC0, tsupport (ψ.1 : ℂ → ℝ) ⊆ O →
      ⟪(memLp_pair hh.1 ψ).toLp (pairProc h ψ), cmIso hh.1 ⊤ v⟫ = 0 := fun ψ hψ =>
    hv _ (toLp_mem_germSpan hh.1 ψ hψ)
  have hcl : IsClosed (Set.range (cmIso hh.1 V)) :=
    (cmIso hh.1 V).isometry.isClosedEmbedding.isClosed_range
  rw [← hcl.closure_eq, Metric.mem_closure_iff]
  intro δ hδ
  set s := Real.sqrt (2 + K ^ 2 * Lc)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set η := δ / (1 + s)
  have hη : 0 < η := by positivity
  obtain ⟨f, hf⟩ := Metric.denseRange_iff.1 (denseRange_gradLin ⊤) v η hη
  obtain ⟨k, hk⟩ := exists_zsSub_approx hh.1 hθs hθ01 hθc hθV hζs hζ01 hζc hζO hCc hCO hθC hK
    hζθ hLc hSchur (cmIso hh.1 ⊤ v) hw f
  refine ⟨cmIso hh.1 V (gradLin V k), ⟨_, rfl⟩, ?_⟩
  rw [cmIso_gradLin]
  set e := ‖cmLin hh.1 ⊤ f - cmIso hh.1 ⊤ v‖
  have he : e < η := by
    change ‖cmLin hh.1 ⊤ f - cmIso hh.1 ⊤ v‖ < η
    rw [← cmIso_gradLin, ← map_sub, LinearIsometry.norm_map, ← dist_eq_norm, dist_comm]
    exact hf
  have hk' : ‖cmLin hh.1 ⊤ f - cmLin hh.1 V k‖ ≤ e * s := by
    rw [← Real.sqrt_sq (norm_nonneg (cmLin hh.1 ⊤ f - cmLin hh.1 V k)),
      ← Real.sqrt_sq (mul_nonneg (norm_nonneg _) hs0), mul_pow,
      Real.sq_sqrt (by positivity)]
    exact Real.sqrt_le_sqrt hk
  rw [dist_eq_norm]
  have htri := norm_sub_le_norm_sub_add_norm_sub (cmIso hh.1 ⊤ v) (cmLin hh.1 ⊤ f)
    (cmLin hh.1 V k)
  have he' : ‖cmIso hh.1 ⊤ v - cmLin hh.1 ⊤ f‖ = e := norm_sub_rev _ _
  have hηδ : η * (1 + s) = δ := div_mul_cancel₀ δ (by positivity)
  have : e * (1 + s) < η * (1 + s) := mul_lt_mul_of_pos_right he (by positivity)
  nlinarith

/-- **Leaf (D) for bounded `V`**: the harmonic part `h(φ) − h̊(φ 1_V)` has a version
measurable for the germ `σ(h|_{ℂ∖V})`. -/
theorem exists_germ_version_harm_of_bdd (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    (hV : Disjoint (V : Set ℂ) (sphere 0 1)) (hVb : Bornology.IsBounded (V : Set ℂ))
    (φ : TestC) :
    ∃ G : Ω → ℝ, Measurable[fieldSigmaClosed h (V : Set ℂ)ᶜ] G ∧
      (fun ω => h ω φ - zbExt hh.1 V φ ω) =ᵐ[P] G :=
  exists_germ_version_harm_of_dirichlet hh hV hVb (pair_mem_range_cmIso_top hh.1)
    (fun _ hε v hv => mem_range_cmIso_of_orth hh hVb hε v hv) φ

end MarkovGermVer
end LQGMetric
