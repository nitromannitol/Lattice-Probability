/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53N4F2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53N4F3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53UFC1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53FN3

/-!
# DZZ Lemma 5.3 part 1, node 4: the part of `L53HbadBParts` (P2-DZZ53N4F)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2516–2522 (`u`, `v` desirable) and
the count l. 2414 (`P(𝒟ᶜ) ≤ e^{−L^{0.22}}`), on the selected chain `𝒞 = l53Chain … ω`
(AUDIT-2026-10-03-N rows N6 (ii), N7, N12).

* **`l53_node4_part`**: for `u ≠ v ∈ 𝕍̄` and large `k`, `1 ≤ l ≤ k`, the first conjunct of
  `L53HbadBParts` (S5L53HB2), i.e. `L53Node4At` (S5L53FN3, verbatim):
  `P(l53E4 ∩ cellSizeEvent ∩ ¬(u, v clauses of 𝒞)) ≤ e^{−L^{0.22}}/2`. It combines
  - FN1's `l53fn_node4` (`l53uf_uv_bound` with `Adm ω c := c = 𝒞(ω)`, `ε := ε*²`);
  - FN2's `l53fn_hbad` (Markov with the cut-off and the per-point far bound `2K⁻⁴`, UF1);
  - G-A1 `l53_side_ratio` (S5L53GA1) for the end-box interfaces;
  - `l53n4_dom` (S5L53N4F1) for the domination of the proxy `l53fnM` on `E`;
  - the numerics: UF4's `l53uf_numerics` at `α' = 2α* + 1` with `Z = ε*⁻² = 4^{n_{ε*}}`
    (copy of the body of UF5's `l53UVBadBox_node4`, with `ε*` replaced by `ε*²`).
  The inputs of the far bound are discharged: `h317` by `dzzProp317Walls_dzzMuIn` (S5WallSim6E)
  at UFC's `ξ` (`l53ufc_xi`, S5L53UFC1), `hcpl` by `l53ufc_cpl` (`fineChaos_sim_couple`, S5L53X4),
  and `hcor` is not needed (`l53n4_hbad`, S5L53N4F3, via YC's `l53_uv_far'`).
* **`l53Node4PartAll_holds`**: `L53Node4PartAll` (S5L53FN3), with no hypothesis.

Own elementary bookkeeping.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent DyBox

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Node 4 of DZZ Lemma 5.3 part 1 at the selected chain** (DZZ l. 2516–2522): the first
conjunct of `L53HbadBParts` for large `k`. -/
theorem l53_node4_part (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {αs : ℝ} (hαs : 0 < αs) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) :
    ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k → L53Node4At hW γ αs u v k l := by
  have := hW.isProbabilityMeasure
  obtain ⟨ξ, hξ, hξ1, hξC, h2ξ⟩ := l53ufc_xi γ huv
  obtain ⟨L₀, hL₀⟩ := l53n4_hbad hW hγ hγ2 αs (dzzProp317Walls_dzzMuIn hW hγ hγ2 hξ hξ1 hξC) hξ
    (by linarith) hu hv huv h2ξ (l53ufc_cpl hγ hγ2 hu hv huv)
  obtain ⟨kd, hkd⟩ := l53n4_dom hW hγ hγ2 hαs hu hv huv
  have hvu : 0 < ‖v - u‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm huv))
  have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hLk : Tendsto (fun k : ℕ => (k : ℝ) * Real.log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hl2
  have ev1 := hLk.eventually
    (l53uf_numerics (2 * αs + 1) (max (dzzCmc γ) 0) ‖v - u‖ (by positivity) (le_max_right _ _)
      hvu)
  have ev2 := hLk.eventually (eventually_ge_atTop (max L₀ 3))
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1
    (((ev1.and ev2).and (l53uf_ev_hs γ hvu)).and (eventually_ge_atTop kd))
  refine ⟨k₁, fun k l hk _ hlk => ?_⟩
  obtain ⟨⟨⟨⟨hL1, hg1, hnum⟩, hkL⟩, hs⟩, hkd'⟩ := hk₁ k hk
  set L : ℝ := (k : ℝ) * Real.log 2 with hL
  have hL3 : 3 ≤ L := le_trans (le_max_right _ _) hkL
  have hLL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hkL
  set Ns := epsStarN αs ((2 : ℝ)⁻¹ ^ k) with hNs
  set Z : ℝ := (2 : ℝ) ^ (2 * Ns) with hZdef
  have hlogδ : Real.log ((2 : ℝ)⁻¹ ^ k)⁻¹ = L := by
    rw [inv_pow, inv_inv, Real.log_pow]
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hsq : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hX0 : 0 ≤ αs * Real.sqrt L * Real.log L := by positivity
  have h4 := four_pow_epsStarN_le αs ((2 : ℝ)⁻¹ ^ k) (by rw [hlogδ]; exact hX0)
  rw [hlogδ, ← hNs] at h4
  have hZ : Z ≤ 2 * Real.exp ((2 * αs + 1) * Real.sqrt L * Real.log L) := by
    have e4 : (4 : ℝ) ^ Ns = Z := by
      rw [hZdef, pow_mul]; norm_num
    have h2 : Real.log 2 ≤ Real.sqrt L * Real.log L := by
      have := Real.log_two_lt_d9; nlinarith
    have h2' : (2 : ℝ) ≤ Real.exp (Real.sqrt L * Real.log L) := by
      rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]; exact Real.exp_le_exp.2 h2
    have e : Real.exp ((2 * αs + 1) * Real.sqrt L * Real.log L) =
        Real.exp (2 * (αs * Real.sqrt L * Real.log L)) * Real.exp (Real.sqrt L * Real.log L) := by
      rw [← Real.exp_add]; ring_nf
    rw [← e4, e]
    have := mul_le_mul_of_nonneg_left h2' (Real.exp_pos (2 * (αs * Real.sqrt L * Real.log L))).le
    linarith
  set N : ℕ := ⌊(k : ℝ) * dzzCmc γ⌋₊ + 2 * Ns with hN
  have hNr : ((N + 1 : ℕ) : ℝ) ≤ L / Real.log 2 * max (dzzCmc γ) 0 + 2 * Z + 1 := by
    have hfl : (⌊(k : ℝ) * dzzCmc γ⌋₊ : ℝ) ≤ (k : ℝ) * max (dzzCmc γ) 0 := by
      rcases le_total 0 ((k : ℝ) * dzzCmc γ) with h | h
      · exact (Nat.floor_le h).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
      · rw [Nat.floor_of_nonpos h, Nat.cast_zero]; positivity
    have hk' : L / Real.log 2 = k := by rw [hL]; field_simp
    have hNsZ : ((2 * Ns : ℕ) : ℝ) ≤ Z := by
      rw [hZdef]; exact_mod_cast (Nat.lt_two_pow_self).le
    have hZ0 : 0 ≤ Z := by positivity
    rw [hk', hN]; push_cast at hNsZ ⊢; linarith
  obtain ⟨hg2, hfin⟩ := hnum Z ((N + 1 : ℕ) : ℝ) (by positivity) hZ (by positivity) hNr
  unfold L53Node4At
  refine (l53fn_node4 hW (l53fnM W γ αs k)
    (fun b c q => measurable_proxyMass hW γ _ _ _ c q) (l53uf_hN γ αs k) hs
    (fun n _ w hw h12 => hL₀ k l hLL₀ hlk hg1 hg2 n w hw h12)
    (fun ω c hQ i hi => l53_side_ratio hQ i hi)
    (fun ω hω b hb _ => hkd k hkd' _ ω hω b hb)).trans ?_
  have he : 800 / epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 = 800 * Z := by
    rw [epsStar, ← pow_mul, inv_pow, div_inv_eq_mul, hZdef, mul_comm Ns 2]
  rw [he]
  have hA : ENNReal.ofReal (800 * Z) *
      ENNReal.ofReal (2 * ((2 : ℝ) ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4) =
      ENNReal.ofReal (800 * Z * (2 * ((2 : ℝ) ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4)) :=
    (ENNReal.ofReal_mul (by positivity)).symm
  have hB : (2 : ℝ≥0∞) * ((N + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (2 * ((N + 1 : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
  rw [hA, hB, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.exp_pos (-L ^ (0.23 : ℝ))
  linarith

/-- **`L53Node4PartAll`** (S5L53FN3): the node-4 part of `L53HbadBParts` for every white noise,
`γ ∈ (0, 2)`, `α* > 0` and pair `u ≠ v ∈ 𝕍̄`. -/
theorem l53Node4PartAll_holds : L53Node4PartAll :=
  fun P _ hW _ hγ hγ2 _ hαs _ hu _ hv huv => l53_node4_part (P := P) hW hγ hγ2 hαs hu hv huv

end DZZ
end LQGMetric
