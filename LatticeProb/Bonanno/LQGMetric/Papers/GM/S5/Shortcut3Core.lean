/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut3Core at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2Out
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes55Det
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLength

/-!
# GM Lemma 5.11, entry step: the first hitting time of `cl B_{3r}(0)` (decision D83 (a))

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M3, decision D83 packet P2, steps 1–3 of the proof plan in `decisions/DEC-83.md` §3).

GM (l. 3477–3486) assume that the `D_{h−φ}`-geodesic `P^φ` runs from the `𝕩'`-side to the
`𝕪'`-side of `U ∪ 𝒲`. Decision D83 (a) repairs this with the first hitting time `τ₁` of
`cl B_{3r}(0)` by `P^φ`: before `τ₁` the path lies where `φ = 0`, so `D_h(𝕫, P^φ(τ₁)) ≤
D_{h−φ}(𝕫, P^φ(τ₁))` (`dist_le_weyl_of_geod_m2m3`), and `P^φ(τ₁)` cannot be near `𝕪'` by condition
(4) and the inequality of Lemma 5.12 (`gm_L5_12_sum`, GM l. 3391–3401).

* `revPath01`, `isGeod01_rev_m2m3`, `uniqueGeodIn_symm_m2m3`: time reversal of geodesics;
* `isGeod01_sub_m2m3`: initial pieces of geodesics are geodesics;
* `dist_le_weyl_of_geod_m2m3`: Weyl locality along a `D'`-geodesic outside the support of `f`
  (own elementary argument from `internal_eq_of_eq_const`);
* `gm_L5_12_sum`: `D(𝕫,𝕩') + 2Δ' + D(𝕨,𝕪') ≤ D(𝕫,𝕨)` (the inequality inside GM's proof of
  Lemma 5.12, l. 3395–3399; copy of the corresponding part of `gm_L5_12`);
* `entry_first_hit_m2m3`: the abstract first-hitting-time argument of D83 (a).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the time reversal of a path on `[0,1]` -/
def revPath01 (η : C(unitInterval, ℂ)) : C(unitInterval, ℂ) :=
  η.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩

lemma revPath01_apply (η : C(unitInterval, ℂ)) (t : unitInterval) :
    revPath01 η t = η (unitInterval.symm t) := rfl

lemma revPath01_rev (η : C(unitInterval, ℂ)) : revPath01 (revPath01 η) = η := by
  ext t; simp [revPath01_apply]

lemma range_revPath01 (η : C(unitInterval, ℂ)) : range (revPath01 η) = range η := by
  ext p; constructor
  · rintro ⟨t, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨t, rfl⟩; exact ⟨unitInterval.symm t, by simp [revPath01_apply]⟩

/-- the reversal of a geodesic `u → v` is a geodesic `v → u` -/
lemma isGeod01_rev_m2m3 {D : ContMetric} {u v : ℂ} {η : C(unitInterval, ℂ)}
    (h : IsGeod01 D u v η) : IsGeod01 D v u (revPath01 η) := by
  refine ⟨by simp [revPath01_apply, h.2.1], by simp [revPath01_apply, h.1], fun s t => ?_⟩
  rw [revPath01_apply, revPath01_apply, h.2.2, unitInterval.coe_symm_eq,
    unitInterval.coe_symm_eq, dist_comm_m2m D u v]
  congr 1
  rw [abs_sub_comm]; ring_nf

/-- `UniqueGeodIn` is symmetric in its end points -/
lemma uniqueGeodIn_symm_m2m3 {D : ContMetric} {u v : ℂ} {S : Set ℂ}
    (h : UniqueGeodIn D u v S) : UniqueGeodIn D v u S := by
  obtain ⟨⟨η, hη, huniq⟩, hin⟩ := h
  refine ⟨⟨revPath01 η, isGeod01_rev_m2m3 hη, fun ζ hζ => ?_⟩, fun ζ hζ => ?_⟩
  · rw [← revPath01_rev ζ, huniq _ (isGeod01_rev_m2m3 hζ)]
  · rw [← range_revPath01 ζ]; exact hin _ (isGeod01_rev_m2m3 hζ)

/-- `s ↦ τ s` on `[0,1]` -/
def mulMap01 (τ : unitInterval) : C(unitInterval, unitInterval) :=
  ⟨fun s => ⟨τ * s, unitInterval.mul_mem τ.2 s.2⟩, by fun_prop⟩

/-- the initial piece `η|_{[0,τ]}` of a geodesic, run at speed `τ`, is a geodesic -/
lemma isGeod01_sub_m2m3 {D : ContMetric} {u v : ℂ} {η : C(unitInterval, ℂ)}
    (h : IsGeod01 D u v η) (τ : unitInterval) : IsGeod01 D u (η τ) (η.comp (mulMap01 τ)) := by
  have e0 : (mulMap01 τ 0) = 0 := Subtype.ext (by simp [mulMap01])
  have e1 : (mulMap01 τ 1) = τ := Subtype.ext (by simp [mulMap01])
  have hτ : D.1 (u, η τ) = τ * D.1 (u, v) := by
    rw [← h.1, h.2.2, h.1]; simp [abs_of_nonneg τ.2.1]
  refine ⟨by simp [e0, h.1], by simp [e1], fun s t => ?_⟩
  simp only [ContinuousMap.comp_apply]
  rw [h.2.2, hτ]
  show |(τ : ℝ) * t - τ * s| * _ = _
  rw [← mul_sub, abs_mul, abs_of_nonneg τ.2.1]; ring

/-- **Weyl locality along a geodesic** (own elementary argument): if `D' = e^{ξ f}·D`, `ξ f = 0`
on the open set `V`, and the `D'`-geodesic `η` from `z` to `b` lies in `V` before time `1`, then
`D(z, b) ≤ D'(z, b)`. -/
lemma dist_le_weyl_of_geod_m2m3 {D D' : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hD' : ∀ x y : ℂ, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y) {V : Set ℂ}
    (hV : IsOpen V) (hf : ∀ x ∈ V, ξ * f x = 0) {z b : ℂ} {η : C(unitInterval, ℂ)}
    (hη : IsGeod01 D' z b η) (hin : ∀ t : unitInterval, t < 1 → η t ∈ V) :
    D.1 (z, b) ≤ D'.1 (z, b) := by
  -- for `τ < 1`: `D(z, η τ) ≤ D(z, η τ; V) = D'(z, η τ; V) ≤ D'(z, η τ) = τ D'(z,b)`
  have key : ∀ τ : unitInterval, τ < 1 → D.1 (z, η τ) ≤ τ * D'.1 (z, b) := by
    intro τ hτ
    have hg := isGeod01_sub_m2m3 hη τ
    have hr : range (η.comp (mulMap01 τ)) ⊆ V := by
      rintro _ ⟨s, rfl⟩
      refine hin _ (lt_of_le_of_lt ?_ hτ)
      show (τ : ℝ) * s ≤ τ
      exact mul_le_of_le_one_right τ.2.1 s.2.2
    have h1 := internal_le_of_isGeod01 hg hr
    rw [internal_eq_of_eq_const D' hD' hV hf, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h1
    have h2 := (ofReal_le_internal_m2m D V z (η τ)).trans h1
    have hτd : D'.1 (z, η τ) = τ * D'.1 (z, b) := by
      rw [← hη.1, hη.2.2, hη.1]; simp [abs_of_nonneg τ.2.1]
    rw [← hτd]
    exact (ENNReal.ofReal_le_ofReal_iff (nonneg_m2m _ _ _)).1 h2
  -- pass to the limit `τ → 1`
  have hc : Continuous fun τ : unitInterval => D.1 (z, η τ) - τ * D'.1 (z, b) :=
    (D.1.continuous.comp (continuous_const.prodMk η.continuous)).sub
      (continuous_subtype_val.mul continuous_const)
  have hcl : IsClosed {τ : unitInterval | D.1 (z, η τ) - τ * D'.1 (z, b) ≤ 0} :=
    isClosed_le hc continuous_const
  have hsub : {τ : unitInterval | τ < 1} ⊆ {τ : unitInterval | D.1 (z, η τ) - τ * D'.1 (z, b) ≤ 0} :=
    fun τ hτ => by simp only [mem_ofPred_eq]; linarith [key τ hτ]
  have hdense : (1 : unitInterval) ∈ closure {τ : unitInterval | τ < 1} := by
    rw [mem_closure_iff_seq_limit]
    refine ⟨fun n => ⟨1 - 1 / ((n : ℝ) + 2), ?_, ?_⟩, fun n => ?_, ?_⟩
    · have : 1 / ((n : ℝ) + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      linarith
    · have : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
      linarith
    · show (⟨1 - 1 / ((n : ℝ) + 2), _⟩ : unitInterval) < 1
      rw [← Subtype.coe_lt_coe]
      show 1 - 1 / ((n : ℝ) + 2) < 1
      have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      linarith
    · rw [tendsto_subtype_rng]
      show Filter.Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) Filter.atTop (nhds 1)
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
      have h' : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
        refine h.congr fun n => ?_
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]; ring_nf
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h'
  have h1 := hcl.closure_subset_iff.2 hsub hdense
  simp only [mem_ofPred_eq, Set.Icc.coe_one, one_mul] at h1
  rw [hη.2.1] at h1
  linarith

end LQGMetric.GM
