/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108M5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M4

/-!
# CONF Lemma 3.3, Step 3: `E^U_r(z)` as a frozen chain event (bridging step (c))

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, the event `E^U_r(z)` (CONF (3.6), C:1132–1144,
`confEU`) in Step 3 of Lemma 3.3 (C:1236–1243): "`1_{F_r(z)}` depends also on `h|_{ℂ∖U}`, but we
can still view it as a function of `h̊^U` when we condition on a fixed realization of
`h|_{ℂ∖U}`". Bridging step (c) of `handoff/P2-CONFFKG.md`.

Conditions 1 and 3 of `E^U` are events of `h|_{ℂ∖U}` (C:1238); here this enters as a hypothesis:
a `recSigma`-measurable event `B` a.e. equal to "condition 1 and condition 3". Condition 2 is
`diam(S; D_h(·,·; 𝔸_{2r,5r})) ≤ (c/100) 𝔠_r e^{ξ h_r(z)}` for the squares `S`. With
`h = recField + h_ρ(w)` (Axiom III with constants: `D_h = e^{ξ h_ρ(w)} D_{recField}`) and
`h_r(z) − h_ρ(w) = recField_r(z)` it reads `diam(S; D_{recField}) ≤ (c/100) 𝔠_r e^{ξ recField_r(z)}`,
a diameter event of the field `recField = G + X` with an outside-measurable threshold. The squares
are replaced by countable subsets with the same internal diameter for every length metric
(continuity of internal metrics, LM Lemma 1.1, `continuousOn_internal`).

* `exists_countable_internalDiam_eq`: own elementary argument (density plus continuity);
* **`confEU_ae_eq_chain`**: `E^U =ᵐ {(toSig ω, X ω) ∈ frozenChainEv …}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

lemma internal_eq_top_of_notMem_m5 (D : ContMetric) {V : Set ℂ} {u : ℂ} (hu : u ∉ V) (v : ℂ) :
    D.internal V u v = ⊤ :=
  MetricGeometry.internalEDist_eq_top_of_notMem_left (by rw [D.mem_image_pt]; exact hu)

/-- for every `A` there is a countable `A₀ ⊆ A` with the same internal diameter for every length
metric (own elementary argument: density plus continuity of internal metrics) -/
lemma exists_countable_internalDiam_eq (A : Set ℂ) {V : Set ℂ} (hV : IsOpen V) :
    ∃ A₀ ⊆ A, A₀.Countable ∧
      ∀ D : ContMetric, D.IsLength → internalDiam D A V = internalDiam D A₀ V := by
  by_cases hAV : A ⊆ V
  · obtain ⟨A₀, hA₀A, hc, hd⟩ := (IsSeparable.of_separableSpace A).exists_countable_dense_subset
    refine ⟨A₀, hA₀A, hc, fun D hD => le_antisymm ?_ ?_⟩
    · refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
      have hcl : (u, v) ∈ closure (A₀ ×ˢ A₀) := by
        rw [closure_prod_eq]; exact ⟨hd hu, hd hv⟩
      have hcont := D.continuousOn_internal hD hV
      have hcw : ContinuousWithinAt (fun p : ℂ × ℂ => D.internal V p.1 p.2) (A₀ ×ˢ A₀) (u, v) :=
        (hcont (u, v) ⟨hAV hu, hAV hv⟩).mono
          (prod_mono (hA₀A.trans hAV) (hA₀A.trans hAV))
      exact hcw.closure_le hcl continuousWithinAt_const fun p hp =>
        le_iSup₂_of_le p.1 hp.1 (le_iSup₂_of_le p.2 hp.2 le_rfl)
    · exact iSup₂_mono' fun u hu => ⟨u, hA₀A hu, iSup₂_mono' fun v hv => ⟨v, hA₀A hv, le_rfl⟩⟩
  · obtain ⟨u₀, hu₀A, hu₀V⟩ := not_subset.1 hAV
    refine ⟨{u₀}, singleton_subset_iff.2 hu₀A, countable_singleton _, fun D _ => ?_⟩
    have h1 : internalDiam D A V = ⊤ := eq_top_iff.2 <| by
      rw [← internal_eq_top_of_notMem_m5 D hu₀V u₀]
      exact le_iSup₂_of_le u₀ hu₀A (le_iSup₂_of_le u₀ hu₀A le_rfl)
    have h2 : internalDiam D {u₀} V = ⊤ := eq_top_iff.2 <| by
      rw [← internal_eq_top_of_notMem_m5 D hu₀V u₀]
      exact le_iSup₂_of_le u₀ rfl (le_iSup₂_of_le u₀ rfl le_rfl)
    rw [h1, h2]

lemma internalDiam_smulPos_m5 {C : ℝ} (hC : 0 < C) (D : ContMetric) (A V : Set ℂ) :
    internalDiam (D.smulPos C hC) A V = ENNReal.ofReal C * internalDiam D A V := by
  simp only [internalDiam, ContMetric.internal_smulPos, ENNReal.mul_iSup]

/-- the outside-measurable threshold of condition 2 of `E^U`, `(c/100) 𝔠_r e^{ξ recField_r(z)}` -/
def euThr (ξ : ℝ) (cc : ℝ → ℝ) (p : CONFParams) {Ω : Type} (h : Ω → DistC) (ρ : ℝ) (w : ℂ)
    (r : ℝ) (z : ℂ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (p.c / 100 * cc r * Real.exp (ξ * circleAvg (recField h ρ w ω) r z))

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`E^U` as a frozen chain event** (CONF C:1236–1243, bridging step (c)): given a
`recSigma`-measurable event `B` a.e. equal to conditions 1 and 3 of `E^U`, `E^U` is a.e. the event
`{(toSig ω, X ω) ∈ frozenChainEv D (G ∘ val) (· ∈ B) S A₀ 𝔸_{2r,5r} T}` with countable `A₀ k`. -/
theorem confEU_ae_eq_chain {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (p : CONFParams)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (T : Finset (ℤ × ℤ)) (ρ : ℝ) (w : ℂ) {X G : Ω → DistC}
    (hXG : ∀ ω, X ω = recField h ρ w ω - G ω) {B : Set Ω}
    (hB13 : {ω | ENNReal.ofReal (p.c * scaleFac (xiGamma γ) c (h ω) r z) ≤
        setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r)) ∧
        ∀ u ∈ innerPart (confU r p.δ z T) (p.δ * r / 4),
          |harmPart P h (confU r p.δ z T) ω u - circleAvg (h ω) r z| ≤ p.A} =ᵐ[P] B) :
    ∃ A₀ : ℤ × ℤ → Set ℂ, (∀ k, (A₀ k).Countable) ∧
      (∀ k, ∀ D' : ContMetric, D'.IsLength →
        internalDiam D' (confSq (p.δ * r) z k) (annulus z (2 * r) (5 * r)) =
          internalDiam D' (A₀ k) (annulus z (2 * r) (5 * r))) ∧
      confEU (xiGamma γ) c D P h p r z T =ᵐ[P]
        {ω | (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ) ω, X ω) ∈
          frozenChainEv D (fun v => G v.val) (fun v => v.val ∈ B)
            (confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))) A₀
            (fun _ => (annulus z (2 * r) (5 * r) : Set ℂ))
            (fun v _ => euThr (xiGamma γ) c p h ρ w r z v.val)} := by
  set ξ := xiGamma γ with hξ
  set ann : Set ℂ := (annulus z (2 * r) (5 * r) : Set ℂ) with hann
  have hannO : IsOpen ann := (annulus z (2 * r) (5 * r)).isOpen
  choose A₀ hA₀A hA₀c hA₀ using fun k : ℤ × ℤ =>
    exists_countable_internalDiam_eq (confSq (p.δ * r) z k) hannO
  refine ⟨A₀, hA₀c, hA₀, ?_⟩
  have hrec := isWholePlaneGFF_recField hh ρ w
  have hpc := GM.Tight.isGFFPlusCont_of_wp hrec
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [eventuallyEqSet_iff.1 hB13, hD.length P _ hpc, hD.weyl P _ hpc,
    CircleAvg.ae_circleAvg_addConst hh z hr] with ω hBω hl hw hca
  set a := circleAvg (h ω) ρ w with ha
  have eGX : G ω + X ω = recField h ρ w ω := by rw [hXG ω]; abel
  -- `D_h = e^{ξ h_ρ(w)} D_{recField}`
  have e3 : D (h ω) = (D (recField h ρ w ω)).smulPos (Real.exp (ξ * a)) (Real.exp_pos _) := by
    have hk : addConst (recField h ρ w ω) a = h ω := p2_addConst_addConst_neg (h ω) a
    apply Subtype.ext
    ext q
    show (D (h ω)).1 (q.1, q.2) = _
    rw [← hk, dist_addConst_of_weyl hl hw a]; rfl
  have hcz : circleAvg (h ω) r z = circleAvg (recField h ρ w ω) r z + a := by
    rw [recField, hca]; ring
  have hthr : ENNReal.ofReal (p.c / 100 * scaleFac ξ c (h ω) r z) =
      ENNReal.ofReal (Real.exp (ξ * a)) * euThr ξ c p h ρ w r z ω := by
    rw [euThr, ← ENNReal.ofReal_mul (Real.exp_pos _).le, scaleFac, hcz]
    congr 1
    rw [mul_add, Real.exp_add]; ring
  have hE0 : ENNReal.ofReal (Real.exp (ξ * a)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have key : ∀ k, internalDiam (D (h ω)) (confSq (p.δ * r) z k) ann ≤
        ENNReal.ofReal (p.c / 100 * scaleFac ξ c (h ω) r z) ↔
      chainDiam (D (G ω + X ω)) (A₀ k) ann ≤ euThr ξ c p h ρ w r z ω := fun k => by
    rw [e3, internalDiam_smulPos_m5, hthr, ENNReal.mul_le_mul_iff_right hE0 ENNReal.ofReal_ne_top,
      eGX, chainDiam_eq_internalDiam hl _ hannO, hA₀ k _ hl]
  simp only [confEU, frozenChainEv, mem_ofPred_eq, toSig]
  rw [← hBω]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, fun k hk => (key k).1 (h2 k hk)⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, fun k hk => (key k).2 (h2 k hk), h3⟩

end LQGMetric.CONF
