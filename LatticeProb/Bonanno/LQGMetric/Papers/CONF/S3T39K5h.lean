/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K5h at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39KBb
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K5c
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K5e

/-!
# CONF Theorem 3.9, packet J6d: the arc hit events are local (C:1559–1561), modulo measurability

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1559–1561 ("`𝓘_k` is determined by `(𝓑^•_{s_k}, h|_{𝓑^•_{s_k}})`", with `h` modulo additive
constants, C:1154).

**`t39k5_hit_aeEventIn`**: for a radius `s ≥ 0` and `0 < τ' ≤ s` (a.s., bounded `𝓑^•_s`), if the
hit events of `𝓑^•_{τ'}` are a.s. events of `σ(𝓑^•_s, h|) mod const` and `σ(𝓑^•_s, h|) mod const`
is a sub-σ-algebra, then every hit event of the arc `I^{(s)} = t39gArc D_h z₀ s (arcs ∂𝓑^•_{τ'})`
is a.s. an event of `σ(𝓑^•_s, h|) mod const`, for open `U` and arcs `arcs Γ ⊆ Γ` with
`effrosSigma ⊗ Borel`-measurable membership (DEC-132 N4: the former input `hB`, universal
measurability of the saturated sets `t39k5B`, is no longer needed).
Proof: gluing over hull pieces (`t39k5_aeEventIn_hullSigma0_of_pieces`), on a piece `S` a circle
`∂B_r(z) ⊆ int S` and `t39k5_piece_sat` for `(h − h_r(z), (pattern 𝓑^•_s, pattern 𝓑^•_{τ'}))`
with the analytic saturated set `t39k9Ban` (universally measurable: `t39k9_Ban_umeas`, S3T39K9a;
saturated: `t39k9_Ban_sat`, S3T39KBb), identified a.s. with the hit event by `t39k9_mem_Ban_iff`
and the a.s. agreement of `t39gArc` with GM's `confPts`/`arcOf` relation
(`t39k5_hit_iff_arcOf`, from CONF L2.4) for the GFF `h − h_r(z)` (`D_{h−h_r(z)} = e^{−ξh_r(z)} D_h`,
`ae_dist_norm`, `t39k5_gArc_smul`). The event changes only on a `P`-null set; `AEEventIn` is
a.s.-invariant (DEC-132 §1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter TopologicalSpace

namespace LQGMetric.CONF

open Blueprint LocalEvent GM

/-- `D_{h − h_r(z)} = e^{−ξ h_r(z)} D_h` a.s., as continuous metrics -/
theorem t39k5_ae_smul {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, D (addConst (h ω) (-circleAvg (h ω) r z)) =
      (D (h ω)).smul (Real.exp (-(xiGamma γ * circleAvg (h ω) r z))) (Real.exp_pos _) := by
  filter_upwards [ae_dist_norm hD P h hh hr z] with ω hω
  refine Subtype.ext (ContinuousMap.ext fun p => ?_)
  show (D (addConst (h ω) (-circleAvg (h ω) r z))).1 p =
    Real.exp (-(xiGamma γ * circleAvg (h ω) r z)) * (D (h ω)).1 p
  rw [hω p.1 p.2, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- **the hit events of the arcs `I^{(s)}` are a.s. `σ(𝓑^•_s, h|) mod const`-events** -/
theorem t39k5_hit_aeEventIn (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) (s τ' : Ω → ℝ) (arcs : Set ℂ → Set ℂ) (U : Set ℂ)
    (hgood : ∀ᵐ ω ∂P, 0 < τ' ω ∧ τ' ω ≤ s ω ∧
      Bornology.IsBounded (filledBall (D (h ω)) z₀ (s ω)))
    (hK' : ∀ V : Set ℂ, IsOpen V →
      AEEventIn P (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s ω)))
        {ω | (filledBall (D (h ω)) z₀ (τ' ω) ∩ V).Nonempty})
    (hle : localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s ω)) ≤ mΩ)
    (hU : IsOpen U) (harcs : ∀ Γ : Set ℂ, IsClosed Γ → arcs Γ ⊆ Γ)
    (harcsM : MeasurableSet[@Prod.instMeasurableSpace (Set ℂ) ℂ effrosSigma inferInstance]
      {p : Set ℂ × ℂ | p.2 ∈ arcs p.1}) :
    AEEventIn P (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s ω)))
      {ω | (t39gArc (D (h ω)) z₀ (s ω) (arcs (frontier (filledBall (D (h ω)) z₀ (τ' ω)))) ∩
        U).Nonempty} := by
  classical
  set K : Ω → Set ℂ := fun ω => filledBall (D (h ω)) z₀ (s ω) with hKdef
  have hKc : ∀ ω, IsClosed (K ω) := fun ω => gm_filledBall_isClosed _ _ _
  obtain ⟨v, hv, hvK'⟩ := t39k5_pat_version (m := localSigma0 h K)
    (fun ω => filledBall (D (h ω)) z₀ (τ' ω)) hK'
  have hpatK : Measurable[localSigma0 h K] fun ω => t39k5Pat (K ω) := by
    refine @measurable_pi_iff Ω ℕ (fun _ => Bool) (localSigma0 h K) _ _ |>.2 fun j => ?_
    refine @measurable_to_bool Ω (localSigma0 h K) _ ?_
    have : (fun ω => t39k5Pat (K ω) j) ⁻¹' {true} =
        {ω | (K ω ∩ ball (t39jBc j) (2 * t39jBr j)).Nonempty} := by
      ext ω; simp [t39k5Pat]
    rw [this]
    exact (le_iInf fun _ => le_sup_left : setSigma K ≤ localSigma0 h K) _
      (MeasurableSpace.measurableSet_generateFrom ⟨_, isOpen_ball, rfl⟩)
  set Z : Ω → (ℕ → Bool) × (ℕ → Bool) := fun ω => (t39k5Pat (K ω), v ω) with hZdef
  have hZG : Measurable[localSigma0 h K] Z := Measurable.prodMk (m := localSigma0 h K) hpatK hv
  have hZ : Measurable Z := hZG.mono hle le_rfl
  refine t39j_aeEventIn_localSigma0 h hKc fun n => ?_
  refine t39k5_aeEventIn_hullSigma0_of_pieces h K n (conf36HullShapes_countable n)
    (hgood.mono fun ω hω => conf36_hull_mem_shapes (Or.inl hω.2.2) n) fun S _ => ?_
  by_cases hSi : (interior S).Nonempty
  · obtain ⟨z, hz⟩ := hSi
    obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
    set A : Opens ℂ := ⟨interior S, isOpen_interior⟩
    have hsph : sphere z (ε / 2) ⊆ A := fun w hw => hεS (by
      rw [mem_sphere] at hw; rw [mem_ball]; linarith)
    have hr : (0 : ℝ) < ε / 2 := half_pos hε
    have hm : Measurable fun ω => -circleAvg (h ω) (ε / 2) z :=
      ((measurable_circleAvg_left (ε / 2) z).comp hh.measurable).neg
    have hlen := ae_mem_lenSet h38 hγ hγ2 hD P _ (hh.addConst hm)
    set B' := (D ⁻¹' lenSet) ×ˢ (univ : Set ((ℕ → Bool) × (ℕ → Bool))) ∩ t39k9Ban D z₀ A arcs U
    have hsat : ∀ g₁ g₂ : DistC, D g₁ ∈ lenSet → D g₂ ∈ lenSet →
        (D g₁).internal A = (D g₂).internal A → ∀ ζ, (g₁, ζ) ∈ B' → (g₂, ζ) ∈ B' :=
      fun g₁ g₂ h1 h2 he ζ hB₁ =>
        ⟨⟨h2, trivial⟩, t39k9_Ban_sat D z₀ A arcs U g₁ g₂ h1 h2 he ζ hB₁.2⟩
    obtain ⟨F, hF, hEF⟩ := t39k5_piece_sat hD (localSigma0 h K) hh hr hsph hZG hZ hlen
      (t39k9_Ban_umeas hD.measurable z₀ A harcsM hU.measurableSet _ (Measure.isFiniteMeasure_map _ _)) hsat
    refine ⟨F, (sup_le_sup_left (iInf_le _ n) _ : fieldSigma0On h (interior S) ⊔
      localSigma0 h K ≤ _) _ hF, ?_⟩
    filter_upwards [hEF, hgood, hvK', t39k5_ae_smul hD hh hr z, hlen,
      t39k5_hit_iff_arcOf h38 hγ hγ2 hD P _ (hh.addConst hm) z₀] with ω hω hg hv' hsm hl hia hS
    rw [← Iff.of_eq hω]
    have hKA : K ω ⊆ (A : Set ℂ) := by
      show K ω ⊆ interior S
      rw [← hS]; exact subset_interior_dyadicHull n _
    have hC := Real.exp_pos (-(xiGamma γ * circleAvg (h ω) (ε / 2) z))
    have key0 := t39k9_mem_Ban_iff D hC hg.1 hg.2.1 hg.2.2 A.isOpen hKA arcs U hsm
    have key : (addConst (h ω) (-circleAvg (h ω) (ε / 2) z), (t39k5Pat (K ω), t39k5Pat (filledBall (D (h ω)) z₀ (τ' ω)))) ∈
        t39k9Ban D z₀ A arcs U ↔ (t39gArc (D (h ω)) z₀ (s ω)
          (arcs (frontier (filledBall (D (h ω)) z₀ (τ' ω)))) ∩ U).Nonempty := by
      rw [key0, ← hia _ _ (mul_pos hC hg.1) (mul_le_mul_of_nonneg_left hg.2.1 hC.le) _
        (harcs _ isClosed_frontier) U, hsm, t39k5_filledBall_smul, t39k5_gArc_smul]
    show _ ↔ (_, Z ω) ∈ B'
    rw [hZdef]
    simp only
    rw [← hv']
    exact ⟨fun hE => ⟨⟨hl, trivial⟩, key.2 hE⟩, fun hB => key.1 hB.2⟩
  · refine ⟨∅, @MeasurableSet.empty _ (fieldSigma0On h (interior S) ⊔ hullSigma0 h K n), ?_⟩
    filter_upwards [hgood] with ω hω hS
    exfalso
    exact hSi ⟨z₀, (hS ▸ subset_interior_dyadicHull n (K ω))
      (jo_mem_filledBall_self (hω.1.trans_le hω.2.1))⟩

end LQGMetric.CONF
