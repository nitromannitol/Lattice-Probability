/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.TraceMeas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TraceMain
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun

/-!
# EXT-RS node TR6: a measurable, continuous version of the SLE trace

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §3, node **TR6** (task RS-TR6-NR).

## Main results (namespace `QuantumZipper.RS`)

* `tendsto_fwdMapInv_of_rpow_bound`: a bound `‖f̂_t(iy) − p‖ ≤ C y^δ` on `y ∈ (0,1]` gives
  `f̂_t(iy) → p` as `y ↓ 0`.
* `measurable_fwdMapInv_drive`: for a measurable Brownian path version with continuous paths and
  `B 0 = 0` everywhere, `ω ↦ f̂_t(w)` is measurable (P3(e) `fwdMapInv_drive_eq_revMap_revBM`
  plus `ReverseFlow.measurable_revMap_drive`).
* `exists_measurable_sleTrace` (**TR6**): for `0 < κ < 8` there is `η̃ : Ω → ℝ → ℂ`, jointly
  measurable in `(ω, t)` (hence also measurable into the product σ-algebra), continuous in `t`
  for every `ω`, with `η̃ ω = sleTrace κ B ω` on `[0,∞)` almost surely.

## Proof

Replace `B` by a version `B''` that is measurable, continuous with `B'' 0 = 0` for every `ω`
(`CharFun.exists_good_version`), which has the same drive a.s. Apply TR4
(`ae_sleTrace_good`) to `B''` and let `G` be a measurable full-measure set of good `ω`
(complement of `toMeasurable` of the bad set). On `G`, `η̃ ω t = sleTrace κ B'' ω (max t 0)` is
the pointwise limit of `f̂_{max t 0}(i/(n+1))`, which is continuous in `t` and measurable in `ω`,
hence jointly measurable (`measurable_uncurry_of_continuous_of_measurable`); off `G`, `η̃ = 0`.

Sources: Kemppainen, *Schramm–Loewner Evolution*, Thm 5.2 (p. 76) and the proof on pp. 111–112
(the trace as a uniform limit of `f̂_t(iy)`); Rohde–Schramm, *Basic properties of SLE*,
Thm 5.1 (p. 20). The measurable-version bookkeeping is an own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RS

/-- A Hölder-type radial bound gives the radial limit. -/
theorem tendsto_fwdMapInv_of_rpow_bound {W : ℝ → ℝ} {t : ℝ} {p : ℂ} {C δ : ℝ} (hδ : 0 < δ)
    (h : ∀ y ∈ Ioc (0 : ℝ) 1, ‖fwdMapInv W t (y * Complex.I) - p‖ ≤ C * y ^ δ) :
    Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 p) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun y : ℝ => C * y ^ δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun y : ℝ => y ^ δ) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ δ)) :=
      (Real.continuousAt_rpow_const 0 δ (Or.inr hδ.le)).tendsto
    rw [Real.zero_rpow hδ.ne'] at hc
    simpa using (hc.mono_left nhdsWithin_le_nhds).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with y hy using h y hy

/-- A function continuous on every `[0,N]` is continuous on `[0,∞)`. -/
theorem continuousOn_Ici_of_Icc {f : ℝ → ℂ} (hf : ∀ N : ℝ, 0 ≤ N → ContinuousOn f (Icc 0 N)) :
    ContinuousOn f (Ici 0) := by
  intro x hx
  refine ((hf (x + 1) (by simp at hx; linarith)) x ⟨hx, by linarith⟩).mono_of_mem_nhdsWithin ?_
  have : Iio (x + 1) ∈ 𝓝 x := Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds this] with z hz1 hz2
  exact ⟨hz1, le_of_lt hz2⟩

theorem continuous_comp_max_zero {f : ℝ → ℂ} (hf : ContinuousOn f (Ici 0)) :
    Continuous fun t : ℝ => f (max t 0) :=
  hf.comp_continuous (continuous_id.max continuous_const) fun t => le_max_right t 0

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Measurability of `ω ↦ f̂_t(w)` for a measurable version with continuous paths and `B 0 = 0`
for every `ω`. -/
theorem measurable_fwdMapInv_drive (hBm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (B · ω)) (h0 : ∀ ω, B 0 ω = 0) (κ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {w : ℂ} (hw : 0 < w.im) : Measurable fun ω => fwdMapInv (drive κ B ω) t w := by
  have heq : (fun ω => fwdMapInv (drive κ B ω) t w) =
      fun ω => revMap (drive κ (UnzipInvariance.revBM B t.toNNReal) ω) t w :=
    funext fun ω => fwdMapInv_drive_eq_revMap_revBM κ B ht (hc ω) (h0 ω) hw
  rw [heq]
  refine ReverseFlow.measurable_revMap_drive κ _ (fun s => ?_) (fun ω => ?_) w hw ht
  · simp only [UnzipInvariance.revBM]
    exact ((hBm _).add (hBm _)).sub ((hBm _).const_smul _)
  · simp only [UnzipInvariance.revBM_apply]
    have h1 : Continuous fun s : ℝ≥0 => B (t.toNNReal - s) ω :=
      (hc ω).comp (continuous_const.sub continuous_id)
    have h2 : Continuous fun s : ℝ≥0 => B (max s t.toNNReal) ω :=
      (hc ω).comp (continuous_id.max continuous_const)
    exact (h1.add h2).sub continuous_const

/-- **TR6 (EXT-RS): a measurable continuous version of the SLE trace.** For `0 < κ < 8` there
is `η̃ : Ω → ℝ → ℂ`, jointly measurable in `(ω, t)` and measurable into the product σ-algebra,
continuous in `t` for every `ω`, with `η̃ ω = sleTrace κ B ω` on `[0,∞)` almost surely. -/
theorem exists_measurable_sleTrace (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ)
    (hκ8 : κ < 8) :
    ∃ η : Ω → ℝ → ℂ, Measurable (Function.uncurry η) ∧ Measurable η ∧
      (∀ ω, Continuous (η ω)) ∧ ∀ᵐ ω ∂P, EqOn (η ω) (sleTrace κ B ω) (Ici 0) := by
  obtain ⟨B'', hB''m, hB''c, hB''0, hae⟩ : ∃ B'' : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B'' t)) ∧
      (∀ ω, Continuous (B'' · ω)) ∧ (∀ ω, B'' 0 ω = 0) ∧ ∀ᵐ ω ∂P, ∀ t, B'' t ω = B t ω := by
    obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
    refine ⟨fun t ω => B' t ω - B' 0 ω, fun t => (hB'm t).sub (hB'm 0),
      fun ω => (hB'c ω).sub continuous_const, fun ω => sub_self _, ?_⟩
    filter_upwards [hB'eq, hB.eval_zero_ae_eq_zero] with ω h h0 t
    simp [h, h0]
  have hB''br : IsBrownianReal B'' P :=
    ⟨hB.toIsPreBrownianReal.congr fun t => hae.mono fun ω h => (h t).symm, ae_of_all _ hB''c⟩
  obtain ⟨δ, hδ, hgood⟩ := ae_sleTrace_good hB''br hκ hκ8
  obtain ⟨G, hGm, hG, hGae⟩ : ∃ G : Set Ω, MeasurableSet G ∧
      (∀ ω ∈ G, ContinuousOn (sleTrace κ B'' ω) (Ici 0) ∧
        ∀ N : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) N, ∀ y ∈ Ioc (0 : ℝ) 1,
          ‖fwdMapInv (drive κ B'' ω) t (y * Complex.I) - sleTrace κ B'' ω t‖ ≤ C * y ^ δ) ∧
      ∀ᵐ ω ∂P, ω ∈ G := by
    obtain ⟨S, hS, hSm, hSp⟩ :=
      (hgood.mono fun ω h => And.intro h.2.1 h.2.2).exists_measurable_mem
    exact ⟨S, hSm, hSp, hS⟩
  -- the approximants and the limit, in the `(t, ω)` orientation
  obtain ⟨y, hy0, hyT⟩ : ∃ y : ℕ → ℝ, (∀ n, 0 < y n) ∧ Tendsto y atTop (𝓝[>] 0) :=
    ⟨fun n => 1 / ((n : ℝ) + 1), fun n => by positivity,
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ → Ω → ℂ, ∀ n t, F n t = G.indicator
      (fun ω => fwdMapInv (drive κ B'' ω) (max t 0) ((y n : ℂ) * Complex.I)) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → Ω → ℂ, ∀ t, g t =
      G.indicator (fun ω => sleTrace κ B'' ω (max t 0)) := ⟨_, fun _ => rfl⟩
  have hFm : ∀ n, Measurable (Function.uncurry (F n)) := by
    intro n
    refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun t => ?_)
    · by_cases hω : ω ∈ G
      · simp only [hF, indicator_of_mem hω]
        refine continuous_comp_max_zero (f := fun t => fwdMapInv (drive κ B'' ω) t _)
          (continuousOn_Ici_of_Icc fun N hN => ?_)
        exact continuousOn_fwdMapInv_mul_I (drive_continuous (hB''c ω))
          (by simp [drive, hB''0]) (hy0 n) hN
      · simp only [hF, indicator_of_notMem hω]
        exact continuous_const
    · rw [hF]
      exact (measurable_fwdMapInv_drive hB''m hB''c hB''0 κ (le_max_right t 0)
        (by simpa using hy0 n)).indicator hGm
  have hlim : Tendsto (fun n => Function.uncurry (F n)) atTop (𝓝 (Function.uncurry g)) := by
    rw [tendsto_pi_nhds]
    rintro ⟨t, ω⟩
    by_cases hω : ω ∈ G
    · simp only [Function.uncurry_apply_pair, hF, hg, indicator_of_mem hω]
      obtain ⟨C, hC⟩ := (hG ω hω).2 ⌈max t 0⌉₊
      have hmem : max t 0 ∈ Icc (0 : ℝ) ⌈max t 0⌉₊ := ⟨le_max_right _ _, Nat.le_ceil _⟩
      exact (tendsto_fwdMapInv_of_rpow_bound hδ (hC _ hmem)).comp hyT
    · simp only [Function.uncurry_apply_pair, hF, hg, indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hgm : Measurable (Function.uncurry g) := measurable_of_tendsto_metrizable hFm hlim
  refine ⟨fun ω t => g t ω, hgm.comp measurable_swap, ?_, fun ω => ?_, ?_⟩
  · exact measurable_pi_iff.2 fun t => hgm.comp (measurable_const.prodMk measurable_id)
  · by_cases hω : ω ∈ G
    · simp only [hg, indicator_of_mem hω]
      exact continuous_comp_max_zero (hG ω hω).1
    · simp only [hg, indicator_of_notMem hω]
      exact continuous_const
  · filter_upwards [hGae, hae] with ω hω h t ht
    have hdr : drive κ B'' ω = drive κ B ω := by funext s; simp [drive, h]
    simp only [hg, indicator_of_mem hω, max_eq_left (show (0 : ℝ) ≤ t from ht)]
    simp only [sleTrace, hdr]

end RS
end QuantumZipper
