/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate5Meas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4L47kG
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc

/-!
# Inputs of `T4_2PairOne` (DEC-89, packet C): events, far test function, a.s. geodesic facts

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Thm 4.2 (l. 2437–2441) and
Lemma 4.21 (l. 2361–2398), which treat `{𝒵^E_k ≠ ∅}`, `{𝒵^𝔈_k ≠ ∅}` as events; GM.S1.1 (l. 647,
existence of geodesics) and the boundedness of `D_h`-balls (DFGPS Lemma 3.8, bounded compactness);
D79 (far normalization `h(ψ₀) = 0`).

* `gm_measurableSet_zkE_zkF`: `{𝒵^E_k ≠ ∅}` and `{𝒵^𝔈_k ≠ ∅}` are events on a complete space (the
  argument of `gm_h47_k_core`, Iterate4L47kC.lean, extracted);
* `gm_exists_farTest`: a mass-one test function supported outside `B_ρ(0)`;
* `gm_ae_len_bdd_geod`: a.s. `D_h` is a length metric with bounded balls and geodesics from `𝕫`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- `{𝒵^E_k ≠ ∅}` and `{𝒵^𝔈_k ≠ ∅}` are events (GM l. 2361–2398) -/
theorem gm_measurableSet_zkE_zkF [P.IsComplete] (h38 : DFGPSLem3_8) (hC24 : CONFLem2_4)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) {𝕫 𝕨 : ℂ}
    (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 𝕫 𝕨 (sel 𝕫 𝕨 (h ω)) ∧ UniqueGeod (D (h ω)) 𝕫 𝕨)
    {𝕣 ε β : ℝ} (k : ℕ) (hε : 0 < ε) (h𝕣 : 0 < 𝕣) (hlam3 : 1 < R.lam 3)
    (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC)
    (hE2 : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma
      (fun ω => addConst (h ω) (-circleAvg (h ω) (R.lam 4 * r) z))
      (annulus z (R.lam 0 * r) (R.lam 3 * r))) (h ⁻¹' R.E r z))
    (hEf2 : ∀ (z : ℂ), ∀ r ∈ p4Rads R 𝕣 ε, AEEventIn P (fieldSigma h (ballO z (R.lam 3 * r)) ⊔
      MeasurableSpace.comap (fun ω => stopLastExit (sel 𝕫 𝕨 (h ω)) (Metric.ball z (R.lam 3 * r)))
        inferInstance) (h ⁻¹' Ef r z 𝕫 𝕨)) :
    MeasurableSet {ω | (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty} ∧
      MeasurableSet {ω | (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω).Nonempty} := by
  set η : Ω → C(unitInterval, ℂ) := fun ω => sel 𝕫 𝕨 (h ω) with hηdef
  have he : 0 < ε * 𝕣 := mul_pos hε h𝕣
  have ha : 0 < R.lam 3 * ε * 𝕣 := by rw [mul_assoc]; exact mul_pos (by linarith) he
  have hηm : Measurable η := gm_measurable_geod_of_complete hD hh hη
  let Hit : ℂ → ℝ → Set Ω := fun z r => {ω | (range (η ω) ∩ Metric.ball z (R.lam 1 * r)).Nonempty}
  have hHitm : ∀ z r, MeasurableSet (Hit z r) := fun z r => gm_measurableSet_hit hηm isOpen_ball
  have hStabm : ∀ z r, MeasurableSet (gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3) R.ν
      (p4Rads R 𝕣 ε) z r) := fun z r =>
    gm_measurableSet_stabEv h38 hC24 hC27 hC14 hγ hγ2 hD hh (gm_avoidRelAn 𝕫 z r) hε ha
  let A : ℂ × ℝ → Set Ω := fun i => {ω | i ∈ zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω}
  let B : ℂ × ℝ → Set Ω := fun i => {ω | i ∈ zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω}
  have eA : ∀ i : ℂ × ℝ, A i = h ⁻¹' R.E i.2 i.1 ∩ gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0)
      (R.lam 3) R.ν (p4Rads R 𝕣 ε) i.1 i.2 ∩ Hit i.1 i.2 := fun i => by
    ext ω; simp only [A, Hit, zkE, gmStabEv, mem_inter_iff, mem_setOf_eq, mem_preimage]; tauto
  have eB : ∀ i : ℂ × ℝ, B i = h ⁻¹' Ef i.2 i.1 𝕫 𝕨 ∩ gmStabEv D h 𝕫 R.ℓ 𝕣 ε β k (R.lam 0)
      (R.lam 3) R.ν (p4Rads R 𝕣 ε) i.1 i.2 ∩ Hit i.1 i.2 := fun i => by
    ext ω; simp only [B, Hit, zkF, gmStabEv, mem_inter_iff, mem_setOf_eq, mem_preimage]; tauto
  have hA0 : ∀ i : ℂ × ℝ, i.2 ∉ p4Rads R 𝕣 ε → A i = ∅ := fun i hi => by
    ext ω; simp only [A, mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, -, hr, -⟩, -⟩; exact hi hr
  have hB0 : ∀ i : ℂ × ℝ, i.2 ∉ p4Rads R 𝕣 ε → B i = ∅ := fun i hi => by
    ext ω; simp only [B, mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, -, hr, -⟩, -⟩; exact hi hr
  have hAm : ∀ i, MeasurableSet (A i) := fun i => by
    by_cases hi : i.2 ∈ p4Rads R 𝕣 ε
    · rw [eA]
      exact ((gm_measurableSet_E_of_cond2 hh (hE2 i.1 i.2 hi)).inter (hStabm _ _)).inter
        (hHitm _ _)
    · rw [hA0 i hi]; exact MeasurableSet.empty
  have hBm : ∀ i, MeasurableSet (B i) := fun i => by
    by_cases hi : i.2 ∈ p4Rads R 𝕣 ε
    · rw [eB]
      exact ((gm_measurableSet_Ef_of_cond2 hD hh hη (hEf2 i.1 i.2 hi)).inter (hStabm _ _)).inter
        (hHitm _ _)
    · rw [hB0 i hi]; exact MeasurableSet.empty
  constructor
  · have e : {ω | (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty} = ⋃ (ab : ℤ × ℤ) (n : ℕ),
        A (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab, R.rr 𝕣 ε n) := by
      ext ω
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨p, hp⟩
        obtain ⟨⟨a, b, hab⟩, n, hn⟩ := gm_zkE_pairs D sel h R 𝕫 𝕨 𝕣 ε β k ω p hp
        refine ⟨(a, b), n, ?_⟩
        have : p = (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) (a, b), R.rr 𝕣 ε n) :=
          Prod.ext hab hn.symm
        rw [← this]; exact hp
      · rintro ⟨ab, n, hm⟩; exact ⟨_, hm⟩
    rw [e]; exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => hAm _
  · have e : {ω | (zkF D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω).Nonempty} = ⋃ (ab : ℤ × ℤ) (n : ℕ),
        B (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab, R.rr 𝕣 ε n) := by
      ext ω
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨p, hp⟩
        obtain ⟨⟨a, b, hab⟩, n, hn⟩ := gm_zkF_pairs D sel h R Ef 𝕫 𝕨 𝕣 ε β k ω p hp
        refine ⟨(a, b), n, ?_⟩
        have : p = (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) (a, b), R.rr 𝕣 ε n) :=
          Prod.ext hab hn.symm
        rw [← this]; exact hp
      · rintro ⟨ab, n, hm⟩; exact ⟨_, hm⟩
    rw [e]; exact MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => hBm _

/-- a mass-one test function supported outside `B_ρ(0)` (the `ψ₀` of D79) -/
theorem gm_exists_farTest (ρ : ℝ) :
    ∃ ψ₀ : TestC, ∫ x, ψ₀ x = 1 ∧ tsupport (ψ₀ : ℂ → ℝ) ⊆ (Metric.ball (0 : ℂ) ρ)ᶜ := by
  refine ⟨bumpTest 0 ((|ρ| + 2 : ℝ) : ℂ), GFFLaw.integral_bumpTest _ _, ?_⟩
  rw [tsupport_bumpTest, pow_zero]
  intro x hx hxb
  rw [mem_closedBall, dist_eq_norm] at hx
  rw [mem_ball, dist_zero_right] at hxb
  have h1 := norm_sub_norm_le ((|ρ| + 2 : ℝ) : ℂ) x
  rw [norm_sub_rev] at h1
  have h2 : ‖((|ρ| + 2 : ℝ) : ℂ)‖ = |ρ| + 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have := le_abs_self ρ
  linarith

/-- a.s. `D_h` is a length metric with bounded balls, and every point is joined to `𝕫` by a
geodesic (GM.S1.1, l. 647; boundedness of balls from bounded compactness, DFGPS Lemma 3.8) -/
theorem gm_ae_len_bdd_geod (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) :
    ∀ᵐ ω ∂P, (D (h ω)).IsLength ∧ (∀ s, Bornology.IsBounded (ballM (D (h ω)) 𝕫 s)) ∧
      ∀ y, ∃ Q : ℝ → ℂ, IsGeodesicL (D (h ω)) Q ((D (h ω)).1 (𝕫, y)) 𝕫 y := by
  filter_upwards [gm_S1_1_bcpt h38 hγ hγ2 hD P h hh, gm_S1_1 h38 hγ hγ2 hD P h hh,
    hD.length P h (Tight.isGFFPlusCont_of_wp hh)] with ω hc hg hL
  refine ⟨hL, fun s => ?_, fun y => ?_⟩
  · set d := D (h ω)
    have hcl : IsClosed {x : ℂ | d.1 (𝕫, x) ≤ s} :=
      isClosed_le (d.1.continuous.comp (Continuous.prodMk continuous_const continuous_id))
        continuous_const
    refine (hc _ hcl ⟨2 * s, fun u hu v hv => ?_⟩).isBounded.subset fun x (hx : d.1 (𝕫, x) < s) =>
      (show d.1 (𝕫, x) ≤ s from hx.le)
    have h1 := d.2.triangle u 𝕫 v
    have h2 := d.2.symm u 𝕫
    simp only [mem_setOf_eq] at hu hv
    linarith
  · by_cases hy : 𝕫 = y
    · subst hy
      refine ⟨fun _ => 𝕫, ?_⟩
      rw [(D (h ω)).2.self_eq_zero 𝕫]
      refine ⟨le_rfl, rfl, rfl, fun s hs t ht => ?_⟩
      rw [(D (h ω)).2.self_eq_zero 𝕫, le_antisymm hs.2 hs.1, le_antisymm ht.2 ht.1, sub_zero,
        abs_zero]
    · obtain ⟨η, hη⟩ := hg 𝕫 y
      exact ⟨_, gm_geodL_isGeodesicL hη hy⟩

end LQGMetric.GM
