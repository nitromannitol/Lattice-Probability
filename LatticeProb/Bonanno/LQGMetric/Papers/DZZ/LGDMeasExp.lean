/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.LGDMeasExp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.LGDMeasQ
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L12Lower

/-!
# DZZ Lemma 2.12, lower half, expectation form (P2-LGDMEAS)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 2.12 (lem-obvious-bounds),
l. 740–759: `c − o(1) < E log D_{γ,δ}(u,v) / log δ⁻¹`. DZZ's proof (l. 748): "it suffices to show
that `D_{γ,δ}(u,v) ≥ δ^{-c}` with high probability" — that is `dzz_lemma212_lower_whp`
(`S2L12Lower.lean`, under the hypothesis `BallMassLowerTail`). The passage to expectations is
`log D ≥ 0` (`one_le_lgdDZZ`, junk `log 0 = 0`) and Markov's inequality
`E log D ≥ c log δ⁻¹ · P(D ≥ δ^{-c})`, which needs ω-measurability of `D` (`LGDMeas.lean`).

* `dzz_lemma212_lower_exp`: the bound for `∫⁻ ofReal (log D)` (no integrability needed);
* `dzz_lemma212_lower_exp_integral`: the Bochner-integral form `c − ε ≤ E log D / log δ⁻¹`
  when `log D` is integrable;
* `dzz_lemma212_lower_exp_qArea`: the LQG measure on `𝕍` (ball masses a.e.-measurable by
  `aemeasurable_qAreaMeasureOn_ball'`).

Formal hypothesis `hfin` (a.s. `D_δ(u,v) < ∞`): `Real.log (D.toNat)` is the junk `0` when
`D = ∞`, so the expectation bound needs a.s. finiteness, which DZZ use implicitly (l. 121). It
follows from `lgdDZZ_lt_top_openSquare` once `μ ω` is a.s. atomless and locally finite on `𝕍`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology QuantumZipper
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **DZZ Lemma 2.12, lower half, expectation form** (`∫⁻` version) -/
theorem dzz_lemma212_lower_exp {μ : Ω → Measure ℂ} {u v : ℂ} (hu : u ∈ openSquare)
    (huv : u ≠ v) (hμ : ∀ c r, AEMeasurable (fun ω => μ ω (Metric.ball c r)) P)
    (hfin : ∀ δ : ℝ, 0 < δ → ∀ᵐ ω ∂P, lgdDZZ (μ ω) δ u v ≠ ⊤)
    (hT : ∀ K : Set ℂ, IsCompact K → K ⊆ openSquare → BallMassLowerTail P μ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal ((c - ε) * Real.log δ⁻¹) ≤
        ∫⁻ ω, ENNReal.ofReal (Real.log ((lgdDZZ (μ ω) δ u v).toNat : ℝ)) ∂P := by
  obtain ⟨c, hc, hlim⟩ := dzz_lemma212_lower_whp hu huv hT
  refine ⟨c, hc, fun ε hε => ?_⟩
  have h1 := (tendsto_order.1 hlim).2 (ENNReal.ofReal (ε / c))
    (ENNReal.ofReal_pos.2 (div_pos hε hc))
  filter_upwards [h1, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with δ hδ hδI
  obtain ⟨hδ0, hδ1⟩ := hδI
  set L := Real.log δ⁻¹ with hLdef
  have hL : 0 < L := by rw [hLdef, Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  set D : Ω → ℕ∞ := fun ω => lgdDZZ (μ ω) δ u v with hD
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.log ((D ω).toNat : ℝ)) with hf
  set S : Set Ω := {ω | ((⌈δ ^ (-c)⌉₊ : ℕ) : ℕ∞) ≤ D ω ∧ D ω ≠ ⊤} with hS
  -- on `S`, `log D ≥ c log δ⁻¹`
  have hSf : S ⊆ {ω | ENNReal.ofReal (c * L) ≤ f ω} := by
    rintro ω ⟨h1, h2⟩
    simp only [mem_ofPred_eq, hf]
    refine ENNReal.ofReal_le_ofReal ?_
    induction hk : D ω using ENat.recTopCoe with
    | top => exact absurd hk h2
    | coe k =>
      rw [hk] at h1
      have hk' : ⌈δ ^ (-c)⌉₊ ≤ k := by exact_mod_cast h1
      have hpos : 0 < δ ^ (-c) := Real.rpow_pos_of_pos hδ0 _
      have h3 : δ ^ (-c) ≤ (k : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hk')
      have h4 : c * L = Real.log (δ ^ (-c)) := by
        rw [Real.log_rpow hδ0, hLdef, Real.log_inv]; ring
      rw [h4, ENat.toNat_natCast]
      exact Real.log_le_log hpos h3
  -- `P(S) ≥ 1 − ε/c`
  have hSc : Sᶜ ⊆ {ω | D ω < ((⌈δ ^ (-c)⌉₊ : ℕ) : ℕ∞)} ∪ {ω | D ω = ⊤} := by
    intro ω hω
    simp only [hS, mem_compl_iff, mem_ofPred_eq, not_and_or, not_le, not_not] at hω
    rcases hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  have htop : P {ω | D ω = ⊤} = 0 := by
    have := hfin δ hδ0
    rw [ae_iff] at this
    simpa [hD] using this
  have hPSc : P Sᶜ ≤ ENNReal.ofReal (ε / c) :=
    ((measure_mono hSc).trans ((measure_union_le _ _).trans (by rw [htop, add_zero]))).trans
      hδ.le
  have hPS : ENNReal.ofReal (1 - ε / c) ≤ P S := by
    rw [ENNReal.ofReal_sub _ (div_pos hε hc).le, ENNReal.ofReal_one, tsub_le_iff_right]
    calc (1 : ℝ≥0∞) = P (S ∪ Sᶜ) := by rw [union_compl_self, measure_univ]
      _ ≤ P S + P Sᶜ := measure_union_le _ _
      _ ≤ P S + ENNReal.ofReal (ε / c) := add_le_add le_rfl hPSc
  have hfm : AEMeasurable f P := ENNReal.measurable_ofReal.comp_aemeasurable
    (aemeasurable_log_lgdDZZ hμ δ u v)
  calc ENNReal.ofReal ((c - ε) * L) = ENNReal.ofReal (c * L) * ENNReal.ofReal (1 - ε / c) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal (c * L) * P {ω | ENNReal.ofReal (c * L) ≤ f ω} :=
        by gcongr; exact hPS.trans (measure_mono hSf)
    _ ≤ ∫⁻ ω, f ω ∂P := mul_meas_ge_le_lintegral₀ hfm _

/-- **DZZ Lemma 2.12, lower half, expectation form** (Bochner version, DZZ's
`c − o(1) ≤ E log D / log δ⁻¹`), assuming `log D` integrable for small `δ` -/
theorem dzz_lemma212_lower_exp_integral {μ : Ω → Measure ℂ} {u v : ℂ} (hu : u ∈ openSquare)
    (huv : u ≠ v) (hμ : ∀ c r, AEMeasurable (fun ω => μ ω (Metric.ball c r)) P)
    (hfin : ∀ δ : ℝ, 0 < δ → ∀ᵐ ω ∂P, lgdDZZ (μ ω) δ u v ≠ ⊤)
    (hint : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Integrable (fun ω => Real.log ((lgdDZZ (μ ω) δ u v).toNat : ℝ)) P)
    (hT : ∀ K : Set ℂ, IsCompact K → K ⊆ openSquare → BallMassLowerTail P μ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      c - ε ≤ (∫ ω, Real.log ((lgdDZZ (μ ω) δ u v).toNat : ℝ) ∂P) / Real.log δ⁻¹ := by
  obtain ⟨c, hc, h⟩ := dzz_lemma212_lower_exp hu huv hμ hfin hT
  refine ⟨c, hc, fun ε hε => ?_⟩
  filter_upwards [h ε hε, hint, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)]
    with δ hδ hi hδI
  obtain ⟨hδ0, hδ1⟩ := hδI
  have hL : 0 < Real.log δ⁻¹ := by rw [Real.log_inv]; linarith [Real.log_neg hδ0 hδ1]
  have hnn : 0 ≤ᵐ[P] fun ω => Real.log ((lgdDZZ (μ ω) δ u v).toNat : ℝ) :=
    ae_of_all _ fun ω => Real.log_natCast_nonneg _
  rw [le_div_iff₀ hL, integral_eq_lintegral_of_nonneg_ae hnn hi.aestronglyMeasurable]
  rw [← ENNReal.ofReal_le_iff_le_toReal]
  · exact hδ
  · exact hi.lintegral_lt_top.ne

end DZZ
end LQGMetric
