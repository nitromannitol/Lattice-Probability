/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.TraceMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TraceInterp
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TraceGrid
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.BMModulus

/-!
# EXT-RS nodes TR2 (almost sure form) and TR4: existence of the SLE trace for `κ < 8`

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §3, nodes TR2 and TR4.
Sources: A. Kemppainen, *Schramm–Loewner Evolution*, SpringerBriefs Math. Phys. 24 (2017),
Thm 5.2 (p. 76), proved on pp. 111–112 ((6.16)–(6.19)); S. Rohde, O. Schramm, *Basic properties
of SLE*, Ann. Math. 161 (2005), Thm 3.6 (p. 15) and Thm 5.1 (p. 20); G. Lawler, *Conformally
Invariant Processes in the Plane*, AMS 2005, Thm 7.4 (p. 157).

* `ae_radial_bound` (TR2): for `0 < κ < 8` there is a deterministic `δ > 0` such that a.s.,
  for every `N`, `‖(f̂_t)'(iy)‖ ≤ C y^{δ−1}` on `[0,N] × (0,1]`. Proof: TR1
  (`ae_grid_bound_le_eight`, with `θ = θ₀/2`) for (6.16), the Hölder form of the Brownian modulus
  (`bm_holder`, exponent `a = 1/2 − θ/(8A)`) for (6.17), and the deterministic interpolation
  `tr2_interp` ((6.18)); `δ = θ/2`. Kemppainen's subpower factor `ψ(1/y)` is replaced by the
  polynomial loss `y^{−θ/2}` (blueprint TR2 allows this).
* `ae_sleTrace_good` (TR4): TR2 and TR3 (`trace_of_radialBound`, Kemppainen (6.19)).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper.RS

open UnzipInvariance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Kemppainen's `θ₀ = (κ/16 + 4/κ − 1)/(κ/16 + 4/κ + 1) = (κ−8)²/(κ+8)²` lies in `(0,1)` for
`0 < κ < 8`. -/
theorem rsTheta0_mem {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < (κ / 16 + 4 / κ - 1) / (κ / 16 + 4 / κ + 1) ∧
    (κ / 16 + 4 / κ - 1) / (κ / 16 + 4 / κ + 1) < 1 := by
  have hA : (κ / 16 + 4 / κ - 1) / (κ / 16 + 4 / κ + 1) = (κ - 8) ^ 2 / (κ + 8) ^ 2 := by
    field_simp
    ring
  rw [hA]
  have h1 : 0 < (κ - 8) ^ 2 := by nlinarith
  have h2 : 0 < (κ + 8) ^ 2 := by positivity
  refine ⟨div_pos h1 h2, (div_lt_one h2).2 (by nlinarith)⟩

/-- The Hölder bound of `B` transported to the driver `W = √κ B`. -/
theorem drive_holder_of {κ : ℝ} {ω : Ω} {N : ℕ} {a C : ℝ}
    (h : ∀ t : ℝ≥0, t ≤ (N : ℝ≥0) → ∀ s : ℝ≥0, 0 < s → s ≤ 1 / 2 →
      |B (t + s) ω - B t ω| ≤ C * (s : ℝ) ^ a) :
    ∀ t₀ s : ℝ, 0 ≤ t₀ → t₀ ≤ N → 0 < s → s ≤ 1 / 2 →
      |drive κ B ω (t₀ + s) - drive κ B ω t₀| ≤ (Real.sqrt κ * |C|) * s ^ a := by
  intro t₀ s ht0 ht0N hs hs12
  have hT : t₀.toNNReal ≤ (N : ℝ≥0) := by
    rw [Real.toNNReal_le_iff_le_coe]; simpa using ht0N
  have hS : s.toNNReal ≤ 1 / 2 := by
    rw [Real.toNNReal_le_iff_le_coe]; simpa using hs12
  have hb := h t₀.toNNReal hT s.toNNReal (Real.toNNReal_pos.2 hs) hS
  rw [Real.coe_toNNReal s hs.le] at hb
  simp only [drive]
  rw [Real.toNNReal_add ht0 hs.le, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg κ),
    mul_assoc]
  refine mul_le_mul_of_nonneg_left (hb.trans ?_) (Real.sqrt_nonneg κ)
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hs.le a)

/-- **TR2 (EXT-RS), almost sure radial derivative bound; Kemppainen (6.18), p. 112.** -/
theorem ae_radial_bound (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ δ > (0 : ℝ), ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) N,
      ∀ y ∈ Ioc (0 : ℝ) 1,
        ‖deriv (fwdMapInv (drive κ B ω) t) ((y : ℂ) * Complex.I)‖ ≤ C * y ^ (δ - 1) := by
  obtain ⟨A, hA1, hA⟩ := tr2_interp
  obtain ⟨hθ0, hθ01⟩ := rsTheta0_mem hκ hκ8
  set θ₀ := (κ / 16 + 4 / κ - 1) / (κ / 16 + 4 / κ + 1) with hθ₀
  set θ := θ₀ / 2 with hθdef
  have hθ : 0 < θ := by positivity
  have hθlt : θ < θ₀ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  set a := 1 / 2 - θ / (8 * A) with hadef
  have hA0 : 0 < A := by linarith
  have hq : θ / (8 * A) ≤ θ / 8 := div_le_div_of_nonneg_left hθ.le (by norm_num) (by linarith)
  have hq0 : 0 < θ / (8 * A) := by positivity
  have ha0 : 0 < a := by linarith
  have halt : a < 1 / 2 := by linarith
  refine ⟨θ / 2, by positivity, ?_⟩
  filter_upwards [ae_all_iff.2 fun N : ℕ => ae_grid_bound_le_eight hB hκ hκ8.le hθ hθlt N,
    bm_holder hB halt, hB.cont, hB.eval_zero_ae_eq_zero] with ω hgrid hhol hc h0
  intro N
  obtain ⟨Cg, hCg⟩ := hgrid N
  obtain ⟨Ch, hCh⟩ := hhol (N : ℝ≥0)
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  refine ⟨2 * A ^ 3 * max Cg 0 * (1 + (Real.sqrt κ * |Ch|) ^ 2) ^ A, by positivity,
    fun t ht y hy => ?_⟩
  have hgrid' : ∀ n k : ℕ, (k : ℝ) / 4 ^ n ≤ N →
      ‖deriv (fwdMapInv (drive κ B ω) ((k : ℝ) / 4 ^ n)) (Complex.I / 2 ^ n)‖ ≤
        max Cg 0 * 2 ^ ((n : ℝ) * (1 - θ)) := fun n k hk =>
    (hCg n k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by norm_num) _))
  have h := hA (drive κ B ω) hW hW0 N θ a (max Cg 0) (Real.sqrt κ * |Ch|) hθ hθ1 ha0 halt.le
    (le_max_right _ _) (by positivity) hgrid' (drive_holder_of hCh) t ht y hy
  have hexp : θ - 1 - (2 - 4 * a) * A = θ / 2 - 1 := by
    rw [hadef]; field_simp; ring
  rwa [hexp] at h

/-- **TR4 (EXT-RS): the SLE trace exists for `κ < 8`.** Kemppainen Thm 5.2 (p. 76, proved on
pp. 111–112); RS Thm 3.6 (p. 15), Thm 5.1 (p. 20); Lawler Thm 7.4 (p. 157). There is a
deterministic `δ > 0` such that almost surely `η = sleTrace κ B ω` satisfies `η 0 = 0`, is
continuous on `[0,∞)`, and `‖f̂_t(iy) − η(t)‖ ≤ C_N y^δ` for `t ∈ [0,N]`, `y ∈ (0,1]`. -/
theorem ae_sleTrace_good (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ δ > (0 : ℝ), ∀ᵐ ω ∂P, sleTrace κ B ω 0 = 0 ∧ ContinuousOn (sleTrace κ B ω) (Ici 0) ∧
      ∀ N : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) N, ∀ y ∈ Ioc (0 : ℝ) 1,
        ‖fwdMapInv (drive κ B ω) t (y * Complex.I) - sleTrace κ B ω t‖ ≤ C * y ^ δ := by
  obtain ⟨δ, hδ, h⟩ := ae_radial_bound hB hκ hκ8
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [h, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hc h0
  set W := drive κ B ω with hWdef
  have hW : Continuous W := drive_continuous hc
  have hW0 : W 0 = 0 := drive_zero h0
  have key : ∀ N : ℕ,
      (∀ t ∈ Icc 0 (N : ℝ), Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (trace W t))) ∧
      (∀ t ∈ Icc 0 (N : ℝ), ∀ y ∈ Ioc (0 : ℝ) 1,
        ‖fwdMapInv W t (y * Complex.I) - trace W t‖ ≤ (Classical.choose (hω N)) / δ * y ^ δ) ∧
      ContinuousOn (trace W) (Icc 0 (N : ℝ)) := fun N =>
    trace_of_radialBound hδ (Classical.choose_spec (hω N)).1 hW hW0
      (Classical.choose_spec (hω N)).2
  refine ⟨?_, ?_, fun N => ⟨_, (key N).2.1⟩⟩
  · -- `η 0 = 0`: `f̂_0 = id` on `ℍ`
    have ht := (key 0).1 0 ⟨le_rfl, by simp⟩
    have hid : ∀ y : ℝ, 0 < y → fwdMapInv W 0 (y * Complex.I) = y * Complex.I := by
      intro y hy
      have hyH : (y : ℂ) * Complex.I ∈ H := mul_I_mem_H hy
      rw [fwdMapInv_eq_revMap_timeRev W hW hW0 le_rfl hyH]
      have hVc : Continuous fun r : ℝ => W (0 - r) - W 0 := by fun_prop
      obtain ⟨u, hu⟩ := exists_isReverseSol _ hVc _ hyH 0 le_rfl
      rw [revMap_eq _ hVc _ le_rfl le_rfl hu, (hu.2 0 ⟨le_rfl, le_rfl⟩).2]
      simp
    have ht2 : Tendsto (fun y : ℝ => fwdMapInv W 0 (y * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 ((0 : ℝ) * Complex.I)) := by
      refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun y hy => (hid y hy).symm) ?_
      exact ((Complex.continuous_ofReal.mul continuous_const).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have := tendsto_nhds_unique ht ht2
    simpa [sleTrace, hWdef] using this
  · intro t ht
    have hlt : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil t]
    have hc := (key (⌈t⌉₊ + 1)).2.2 t ⟨ht, hlt.le⟩
    refine hc.mono_of_mem_nhdsWithin ?_
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds hlt)

end QuantumZipper.RS
