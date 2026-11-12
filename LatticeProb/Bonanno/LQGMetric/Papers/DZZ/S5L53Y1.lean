/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53Y1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Q1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53K1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcI2L
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53H1

/-!
# DZZ Lemma 5.3 part 1, R1: the per-pair far bound for the proxy (P2-DZZ53Y, packet P-131F)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2474 (eq-scaling-invariance-
approximate) and l. 2490–2502: for `z, z' ∈ ∂𝖡`,
`P(log D̃^{ν_𝖡}_{δδ̃}(z,z') ≥ E log D̃_{δ̃}(u,v) + L^{0.97}) ≤ O(K⁻⁴)`, from the scaling coupling of
the proxy on `𝕍̃_{z,z'}` with the field on `𝕍̃_{u,v}` and the `(u,v)`-step (Cor 3.9 + P3.17,
`l53_uv_far`, S5L53G6). Route of decision D131 §3 (P-131F) with the proxy of the §9 amendment
(`proxyMass W γ m c_B S = c_B · M̃_{γ,2^{-m},η}` on the rational balls inside `S`, S5L53K1).

* **`prob_l53FarQ_proxyMass_eq`**: the probability of a far event of the proxy does not depend on
  the white noise (canonical white noise `wnCanon`, `wnLaw_eq`, S3ConcI2L; the proxy is a function
  of `wnPath W` by `rfl`).
  Own elementary glue (DZZ use equality in law implicitly), as `prob_ballMassQ_dzzMuIn_eq`.
* `lgdRat_smul`, `wallMass_smul`, `lgdRat_anti`, `wallMass_proxyMass`: deterministic LGD facts
  for mass maps (copies of `lgdDZZ_smul`, `lgdDZZ_antitone` for `lgdRat`).
* `FineSimCoupleQ`: the conclusion of P-131S, verbatim that of `fineChaos_sim_couple` (S5L53X4).
* **`l53_far_pair_couple`**: one coupling step (as `l53h_tail`, S5L53H1).
* **`l53_uv_step`**: from `¬ D^{(u,v)}_{δ₁} ≤ e^T` to `T < log D_{δ'}` for `δ' ≤ δ₁`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent

/-! ### The proxy is a function of the white-noise vector -/

section Law


variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}

/-- **the probability of a far event of the proxy does not depend on the white noise** (the proxy
is a function of `wnPath W` by `rfl`; `wnLaw_eq`, S3ConcI2L) -/
theorem prob_l53FarQ_proxyMass_eq (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') (γ : ℝ)
    (m : ℕ) (cB : ℝ≥0∞) (S : Set ℂ) (δ T : ℝ) (z z' : ℂ) :
    P {ω | l53FarQ (proxyMass W γ m cB S) δ T ω z z'} =
      P' {ω | l53FarQ (proxyMass W' γ m cB S) δ T ω z z'} := by
  set E : Set WNCanon := {w | l53FarQ (proxyMass wnCanon γ m cB S) δ T w z z'}
  have hE : MeasurableSet E :=
    measurableSet_l53FarQ_pair (measurable_proxyMass (isWhiteNoise_wnCanon hW) γ m cB S) δ T z z'
  have e1 := measure_path_eq_wnLaw hW hE
  have e2 := measure_path_eq_wnLaw hW' hE
  rw [wnLaw_eq hW hW'] at e1
  exact e1.trans e2.symm

end Law

/-! ### Deterministic LGD facts for mass maps -/

/-- copy of `lgdDZZ_smul` for `lgdRat` -/
lemma lgdRat_smul (m : ℚ × ℚ → ℚ → ℝ≥0∞) {κ : ℝ} (hκ : 0 < κ) (δ : ℝ) (A B : Set ℂ) :
    lgdRat (fun c q => ENNReal.ofReal κ * m c q) δ A B = lgdRat m (δ / Real.sqrt κ) A B := by
  simp only [lgdRat, ratAdm, smul_mass_le_iff hκ]

/-- the wall commutes with a positive constant factor -/
lemma wallMass_smul (K : Set ℂ) (m : ℚ × ℚ → ℚ → ℝ≥0∞) {κ : ℝ} (hκ : 0 < κ) :
    wallMass K (fun c q => ENNReal.ofReal κ * m c q) =
      fun c q => ENNReal.ofReal κ * wallMass K m c q := by
  funext c q
  simp only [wallMass]
  rw [mul_add]
  rcases eq_or_ne (volume (Metric.ball (ratPt c) (q : ℝ) ∩ Kᶜ)) 0 with h | h
  · simp [h]
  · rw [ENNReal.top_mul h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hκ).ne']

/-- copy of `lgdDZZ_antitone` for `lgdRat` -/
lemma lgdRat_anti (m : ℚ × ℚ → ℚ → ℝ≥0∞) {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ')
    (A B : Set ℂ) : lgdRat m δ' A B ≤ lgdRat m δ A B := by
  unfold lgdRat
  refine iInf_mono fun N => iInf_mono' fun hN => ⟨?_, le_rfl⟩
  obtain ⟨c, q, hcov, hi⟩ := hN
  refine ⟨c, q, hcov, fun i => ⟨(hi i).1, (hi i).2.trans (ENNReal.ofReal_le_ofReal ?_)⟩⟩
  exact pow_le_pow_left₀ hδ hδδ' 2

/-- inside the region `S`, the walled proxy is `c_B ·` the walled η-chaos -/
lemma wallMass_proxyMass {Ω : Type*} (W : WNSpace → Ω → ℝ) (γ : ℝ) (m : ℕ) (cB : ℝ≥0∞)
    {S K : Set ℂ} (hK : IsClosed K) (hKS : K ⊆ S) (ω : Ω) :
    wallMass K (proxyMass W γ m cB S ω) = wallMass K (fun c q => cB * fineMass W γ m ω c q) := by
  funext c q
  refine le_antisymm (wallMass_le_of_ball hK (fun c q h => ?_) c q)
    (wallMass_le_of_ball hK (fun c q h => ?_) c q)
  · exact (proxyMass_of_subset γ m cB ω (h.trans hKS)).le
  · exact (proxyMass_of_subset γ m cB ω (h.trans hKS)).ge

/-! ### The coupling hypothesis (P-131S) and one coupling step -/

/-- **The conclusion of P-131S**, verbatim the conclusion of `fineChaos_sim_couple`
(S5L53X4, P2-DZZ53X; DEC-131-IF S/F-1, S/F-2, S/F-4): DZZ (eq-scaling-invariance-approximate)
l. 2474, upper half, through one coupling (lem-scaling-coupling, l. 611–624), for
`2^{-m} ≤ ‖a‖`, with tail `C ρ² e^{−λ²/(C(log ρ + 1))}`, `ρ = ‖a‖ 2^m`. -/
def FineSimCoupleQ (γ ξ : ℝ) (K : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (a : ℂ), 0 < ‖a‖ → ‖a‖ ≤ 1 → ∀ b : ℂ, simMap a b '' K ⊆ dzzVXi ξ →
    ∀ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ‖a‖ →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W₁ W₂ : WNSpace → Ω' → ℝ),
      IsWhiteNoise P' W₁ ∧ IsWhiteNoise P' W₂ ∧ ∀ lam : ℝ, 0 ≤ lam →
      P'.real {ω | ¬ ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ →
        lgdRat (wallMass (simMap a b '' K) (fineMass W₂ γ m ω))
            (‖a‖ * δ * Real.exp lam * (‖a‖ * 2 ^ m) ^ (γ ^ 2 / 4))
            {simMap a b x} {simMap a b y} ≤
          lgdDZZ (dzzWall K (dzzMuIn γ W₁ ω)) δ x y} ≤
        C * (‖a‖ * 2 ^ m) ^ 2 * Real.exp (-lam ^ 2 / (C * (Real.log (‖a‖ * 2 ^ m) + 1)))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **One coupling step for the proxy** (DZZ l. 2474 and 2490–2492; pattern of `l53h_tail`,
S5L53H1): the far probability of `(θu, θv)` for `proxyMass` at `δ₂` is at most the coupling tail
plus the probability that `D^{𝕍̃_{u,v}}_{δ₁}(u,v) > e^T` for `μIn`, if
`‖a‖ δ₁ e^λ (‖a‖ 2^m)^{γ²/4} ≤ δ₂/√κ`. -/
theorem l53_far_pair_couple (hW : IsWhiteNoise P W) {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {u v : ℂ} {C : ℝ}
    (hcpl : ∀ (a : ℂ), 0 < ‖a‖ → ‖a‖ ≤ 1 → ∀ b : ℂ, simMap a b '' tildeBox u v ⊆ dzzVXi ξ →
      ∀ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ ‖a‖ →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W₁ W₂ : WNSpace → Ω' → ℝ),
        IsWhiteNoise P' W₁ ∧ IsWhiteNoise P' W₂ ∧ ∀ lam : ℝ, 0 ≤ lam →
        P'.real {ω | ¬ ∀ x ∈ tildeBox u v, ∀ y ∈ tildeBox u v, ∀ δ : ℝ, 0 < δ →
          lgdRat (wallMass (simMap a b '' tildeBox u v) (fineMass W₂ γ m ω))
              (‖a‖ * δ * Real.exp lam * (‖a‖ * 2 ^ m) ^ (γ ^ 2 / 4))
              {simMap a b x} {simMap a b y} ≤
            lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W₁ ω)) δ x y} ≤
          C * (‖a‖ * 2 ^ m) ^ 2 * Real.exp (-lam ^ 2 / (C * (Real.log (‖a‖ * 2 ^ m) + 1))))
    (hu : u ∈ tildeBox u v) (hv : v ∈ tildeBox u v)
    {a b : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ ≤ 1) (hKV : simMap a b '' tildeBox u v ⊆ dzzVXi ξ)
    (m : ℕ) (hm : (2 : ℝ)⁻¹ ^ m ≤ ‖a‖) {κ : ℝ} (hκ : 0 < κ) {S : Set ℂ}
    (hS : tildeBox (simMap a b u) (simMap a b v) ⊆ S) {lam δ₁ δ₂ : ℝ} (hlam : 0 ≤ lam)
    (hδ₁ : 0 < δ₁)
    (hthr : ‖a‖ * δ₁ * Real.exp lam * (‖a‖ * (2 : ℝ) ^ m) ^ (γ ^ 2 / 4) ≤ δ₂ / Real.sqrt κ)
    (T : ℝ) :
    P {ω | l53FarQ (proxyMass W γ m (ENNReal.ofReal κ) S) δ₂ T ω (simMap a b u) (simMap a b v)} ≤
      ENNReal.ofReal (C * (‖a‖ * 2 ^ m) ^ 2 *
          Real.exp (-lam ^ 2 / (C * (Real.log (‖a‖ * 2 ^ m) + 1)))) +
        P {ω | ¬ lgdLeExp (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ₁ T u v} := by
  have ha : a ≠ 0 := norm_pos_iff.1 ha0
  obtain ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, hcp⟩ := hcpl a ha0 ha1 b hKV m hm
  have := hW₂.isProbabilityMeasure
  rw [prob_l53FarQ_proxyMass_eq hW hW₂]
  have tr : P {ω | ¬ lgdLeExp (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ₁ T u v} =
      P' {ω | ¬ lgdLeExp (dzzWall (tildeBox u v) (dzzMuIn γ W₁ ω)) δ₁ T u v} := by
    have e := wsim_prob_lgdMinSet_wall_eq hW hW₁ hγ hγ2 (tildeBox u v) δ₁ {u} {v}
      {n : ℕ∞ | ¬ (n ≠ ⊤ ∧ (n.toNat : ℝ) ≤ Real.exp T)}
    simp only [lgdMinSet_singleton, mem_ofPred_eq] at e
    exact e
  rw [tr]
  refine l53h_tail_aux (hcp lam hlam) fun ω hω hA => ?_
  simp only [mem_ofPred_eq, not_not] at hω hA ⊢
  intro hle
  apply hA
  have hK' := simMap_image_tildeBox ha b u v
  have hcmp := hω u hu v hv δ₁ hδ₁
  rw [hK'] at hcmp
  have hpos : 0 ≤ ‖a‖ * δ₁ * Real.exp lam * (‖a‖ * (2 : ℝ) ^ m) ^ (γ ^ 2 / 4) := by positivity
  have hchain : lgdRat (wallMass (tildeBox (simMap a b u) (simMap a b v))
      (proxyMass W₂ γ m (ENNReal.ofReal κ) S ω)) δ₂ {simMap a b u} {simMap a b v} ≤
      lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W₁ ω)) δ₁ u v := by
    rw [wallMass_proxyMass W₂ γ m _ (isClosed_tildeBox _ _) hS ω,
      wallMass_smul _ _ hκ, lgdRat_smul _ hκ]
    exact (lgdRat_anti _ hpos hthr _ _).trans hcmp
  exact ⟨ne_top_of_le_ne_top hle.1 hchain,
    le_trans (by exact_mod_cast ENat.toNat_le_toNat hchain hle.1) hle.2⟩

/-- **The `(u,v)` side**: off `{T < log D_{δ'}(u,v)}` and a.s. `D_{δ'} < ∞`, the LGD at any
`δ₁ ≥ δ'` is `≤ e^T`. -/
theorem l53_uv_step {μ : Ω → Measure ℂ} {δ' δ₁ T : ℝ} (hδ' : 0 ≤ δ') (hδ : δ' ≤ δ₁) {u v : ℂ}
    (hfin : ∀ᵐ ω ∂P, lgdDZZ (μ ω) δ' u v < ⊤) :
    P {ω | ¬ lgdLeExp (μ ω) δ₁ T u v} ≤ P {ω | T < logMinLGD (μ ω) δ' {u} {v}} := by
  refine measure_mono_ae ?_
  filter_upwards [hfin] with ω hω hbad
  change ¬ lgdLeExp (μ ω) δ₁ T u v at hbad
  by_contra hT
  push Not at hT
  apply hbad
  have hle := lgdDZZ_antitone (μ ω) hδ' hδ u v
  refine ⟨ne_top_of_le_ne_top hω.ne hle, ?_⟩
  have h1 : ((lgdDZZ (μ ω) δ₁ u v).toNat : ℝ) ≤ ((lgdDZZ (μ ω) δ' u v).toNat : ℝ) := by
    exact_mod_cast ENat.toNat_le_toNat hle hω.ne
  refine h1.trans ?_
  rw [logMinLGD, lgdMinSet_singleton] at hT
  rcases Nat.eq_zero_or_pos (lgdDZZ (μ ω) δ' u v).toNat with h0 | h0
  · rw [h0, Nat.cast_zero]; exact (Real.exp_pos T).le
  · have h0' : (0 : ℝ) < ((lgdDZZ (μ ω) δ' u v).toNat : ℝ) := by exact_mod_cast h0
    rw [← Real.exp_log h0']
    exact Real.exp_le_exp.2 hT

end DZZ
end LQGMetric
