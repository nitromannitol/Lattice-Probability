/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.WeylUpper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylLower
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLength

/-!
# LFPP Weyl identity, second half: `D^{φ+ψ} ≤ e^{ξψ}·D^φ`, and the identity

Task P2-LFPP, item 3 (DFGPS.S5). Let `Q : [0, L] → ℂ` be parametrized by `D^φ`-length. On a fine
partition `t_i` of `[0, L]`, a near-optimal `D^φ`-path between `Q(t_i)` and `Q(t_{i+1})` stays in
a small ball `B(Q(t_i), r)` (its cost is below `m r`, `m = min e^{ξφ}`; `le_lfppLen_of_path`),
where `ξψ ≤ ξψ(Q(t_i)) + ω`; hence `D^{φ+ψ}(Q(t_i), Q(t_{i+1})) ≤ e^{ξψ(Q(t_i)) + ω}(1 + ω)
(t_{i+1} - t_i)`. Summing and letting `ω → 0` gives `D^{φ+ψ}(z, w) ≤ ∫₀^L e^{ξψ(Q(t))} dt`.
Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

open MetricGeometry

variable {ξ : ℝ} {φ : ℂ → ℝ}

/-- **Localization**: if near-optimal `D^φ`-paths from `x` to `y` cannot leave `B(x, r)`, then
`D^{φ+ψ}(x, y) ≤ e^c (D^φ(x, y) + δ')` when `ξψ ≤ c` on `B(x, r)`. -/
theorem lfppD_add_le_local (hφ : Continuous φ) (ψ : ℂ → ℝ) {x y : ℂ} {r m c δ' : ℝ}
    (hr : 0 < r) (hm : 0 ≤ m) (hmE : ∀ u ∈ Metric.closedBall x r, m ≤ Real.exp (ξ * φ u))
    (hc : ∀ u ∈ Metric.closedBall x r, ξ * ψ u ≤ c) (hδ' : 0 < δ')
    (hsmall : lfppD ξ φ x y + ENNReal.ofReal δ' ≤ ENNReal.ofReal (m * r)) :
    lfppD ξ (fun u => φ u + ψ u) x y ≤
      ENNReal.ofReal (Real.exp c) * (lfppD ξ φ x y + ENNReal.ofReal δ') := by
  have hlt : lfppD ξ φ x y < lfppD ξ φ x y + ENNReal.ofReal δ' :=
    ENNReal.lt_add_right (lfppD_ne_top hφ x y) (by simpa using hδ')
  obtain ⟨P', hPlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨P, hP, _⟩ := P'
  change lfppLen ξ φ P < _ at hPlt
  have hin : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ Metric.closedBall x r := by
    intro t ht
    by_contra hout
    rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hout
    have ht0 : 0 < t := by
      rcases ht.1.lt_or_eq with h | h
      · exact h
      · rw [← h, hP.source, sub_self, norm_zero] at hout; linarith
    have h1 := le_lfppLen_of_path (ξ := ξ) (φ := φ)
      (isPiecewiseC1Path_subPath hP le_rfl ht0 ht.2) hr hm (by rw [hP.source]; exact hmE)
    rw [lfppLen_subPath P ht0, hP.source, min_eq_left hout.le] at h1
    have h2 : ∫⁻ s in Icc 0 t, lenDens ξ φ P s ≤ lfppLen ξ φ P :=
      lintegral_mono_set (Icc_subset_Icc le_rfl ht.2)
    exact absurd ((h1.trans h2).trans_lt (hPlt.trans_le hsmall)) (lt_irrefl _)
  calc lfppD ξ (fun u => φ u + ψ u) x y ≤ lfppLen ξ (fun u => φ u + ψ u) P :=
        lfppDOn_le hP fun _ _ => mem_univ _
    _ ≤ ∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.exp c) * lenDens ξ φ P s := by
        rw [lfppLen_eq]
        refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        rw [lenDens_add]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hc _ (hin s hs)))) le_rfl
    _ = ENNReal.ofReal (Real.exp c) * lfppLen ξ φ P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp c) * (lfppD ξ φ x y + ENNReal.ofReal δ') :=
        mul_le_mul' le_rfl hPlt.le

/-- **`D^{φ+ψ} ≤ e^{ξψ}·D^φ`.** -/
theorem lfppD_le_weylScale (hφ : Continuous φ) (ψ : C(ℂ, ℝ)) (z w : ℂ) :
    lfppD ξ (fun u => φ u + ψ u) z w ≤ weylScale ξ ψ (lfppContMetric ξ φ hφ) z w := by
  set D := lfppContMetric ξ φ hφ
  refine le_iInf fun L => le_iInf fun Q => le_iInf fun hL => le_iInf fun hc =>
    le_iInf fun hu => le_iInf fun h0 => le_iInf fun hL1 => ?_
  set I := ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * ψ (Q t)))
  rcases hL.lt_or_eq with hLpos | hL0
  swap
  · subst hL0
    obtain rfl : z = w := h0.symm.trans hL1
    exact (lfppDOn_self (ξ := ξ) (φ := fun u => φ u + ψ u) convex_univ (mem_univ z)).le.trans
      zero_le
  have key : ∀ ω : ℝ, 0 < ω → lfppD ξ (fun u => φ u + ψ u) z w ≤
      ENNReal.ofReal ((1 + ω) * Real.exp (2 * ω)) * I := by
    intro ω hω
    have hQc : ContinuousOn Q (Icc 0 L) := (continuous_weylToC D).comp_continuousOn hc
    set E : ℂ → ℝ := fun x => Real.exp (ξ * φ x)
    have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul hφ)
    set K := Q '' Icc 0 L
    have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hQc
    set K' := Metric.cthickening 1 K
    have hK' : IsCompact K' := hK.cthickening
    have hKK' : K ⊆ K' := Metric.self_subset_cthickening K
    have hQK : ∀ t ∈ Icc 0 L, Q t ∈ K := fun t ht => mem_image_of_mem Q ht
    obtain ⟨x0, -, hx0⟩ := hK'.exists_isMinOn ⟨Q 0, hKK' (hQK 0 ⟨le_rfl, hL⟩)⟩ hE.continuousOn
    set m := E x0
    have hm : 0 < m := Real.exp_pos _
    obtain ⟨η, hη, hηψ⟩ := Metric.uniformContinuousOn_iff.1
      (hK'.uniformContinuousOn_of_continuous (f := fun x => ξ * ψ x)
        (continuous_const.mul ψ.continuous).continuousOn) ω hω
    set r := min (η / 2) 1
    have hr : 0 < r := lt_min (by positivity) one_pos
    obtain ⟨τ, hτ, hτQ⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hQc) (η / 2) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min (div_pos hτ hLpos)
      (div_pos (mul_pos hm hr) (mul_pos (by linarith : (0 : ℝ) < 1 + ω) hLpos)))
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    set Δ := L / ((N : ℝ) + 1)
    have hΔ : 0 < Δ := by positivity
    have hΔτ : Δ < τ := by
      have := (hN.trans_le (min_le_left _ _))
      rw [lt_div_iff₀ hLpos] at this
      simp only [Δ]; rw [div_eq_mul_one_div, mul_comm]; exact this
    have hΔr : (1 + ω) * Δ ≤ m * r := by
      have := (hN.trans_le (min_le_right _ _))
      rw [lt_div_iff₀ (by positivity)] at this
      have e : (1 + ω) * Δ = 1 / ((N : ℝ) + 1) * ((1 + ω) * L) := by simp only [Δ]; ring
      rw [e]; exact this.le
    set t : ℕ → ℝ := fun i => L * (i / ((N : ℝ) + 1))
    have ht_mono : Monotone t := fun i j hij => by simp only [t]; gcongr
    have ht_mem : ∀ i, i ≤ N + 1 → t i ∈ Icc (0 : ℝ) L := fun i hi => by
      refine ⟨by positivity, ?_⟩
      have : (i : ℝ) / ((N : ℝ) + 1) ≤ 1 := by rw [div_le_one hN1]; exact_mod_cast hi
      simp only [t]; nlinarith
    have ht0 : t 0 = 0 := by simp [t]
    have ht1 : t (N + 1) = L := by simp only [t]; push_cast; rw [div_self hN1.ne', mul_one]
    have ht_step : ∀ i, t (i + 1) - t i = Δ := fun i => by simp only [t, Δ]; push_cast; ring
    have hchain := le_sum_of_triangle (lfppD ξ (fun u => φ u + ψ u))
      (fun x => lfppDOn_self convex_univ (mem_univ x)) lfppDOn_triangle (fun i => Q (t i)) (N + 1)
    simp only [ht0, ht1, h0, hL1] at hchain
    refine hchain.trans ?_
    have hpiece : ∀ i, i ≤ N → lfppD ξ (fun u => φ u + ψ u) (Q (t i)) (Q (t (i + 1))) ≤
        ∫⁻ s in Ioc (t i) (t (i + 1)), ENNReal.ofReal ((1 + ω) * Real.exp (2 * ω)) *
          ENNReal.ofReal (Real.exp (ξ * ψ (Q s))) := by
      intro i hi
      have hti := ht_mem i (by omega)
      have hti1 := ht_mem (i + 1) (by omega)
      have hmono := ht_mono (Nat.le_succ i)
      set x := Q (t i)
      have hxK := hQK _ hti
      have hD : lfppD ξ φ x (Q (t (i + 1))) ≤ ENNReal.ofReal Δ := by
        rw [← edist_lfppContMetric hφ, ← ht_step i]
        have h1 := eVariationOn.edist_le (D.pt ∘ Q) (s := Icc 0 L ∩ Icc (t i) (t (i + 1)))
          ⟨hti, le_rfl, hmono⟩ ⟨hti1, hmono, le_rfl⟩
        rw [hu hti hti1, NNReal.coe_one, one_mul] at h1
        exact h1
      have hsmall : lfppD ξ φ x (Q (t (i + 1))) + ENNReal.ofReal (ω * Δ) ≤
          ENNReal.ofReal (m * r) := by
        refine (add_le_add hD le_rfl).trans ?_
        rw [← ENNReal.ofReal_add hΔ.le (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      have hball : ∀ u ∈ Metric.closedBall x r, u ∈ K' := fun u hu =>
        Metric.mem_cthickening_of_dist_le u x 1 K hxK (hu.trans (min_le_right _ _))
      have hloc := lfppD_add_le_local (ξ := ξ) hφ ψ hr hm.le
        (fun u hu => hx0 (hball u hu)) (c := ξ * ψ x + ω) (fun u hu => by
          have := hηψ u (hball u hu) x (hKK' hxK)
            ((Metric.mem_closedBall.1 hu).trans_lt ((min_le_left _ _).trans_lt (by linarith)))
          rw [Real.dist_eq, abs_lt] at this
          linarith) (by positivity : (0 : ℝ) < ω * Δ) hsmall
      refine hloc.trans ?_
      have hD' : lfppD ξ φ x (Q (t (i + 1))) + ENNReal.ofReal (ω * Δ) ≤
          ENNReal.ofReal ((1 + ω) * Δ) := by
        refine (add_le_add hD le_rfl).trans ?_
        rw [← ENNReal.ofReal_add hΔ.le (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      refine (mul_le_mul' le_rfl hD').trans ?_
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      have hvol : ENNReal.ofReal (Real.exp (ξ * ψ x + ω) * ((1 + ω) * Δ)) =
          ∫⁻ _ in Ioc (t i) (t (i + 1)), ENNReal.ofReal (Real.exp (ξ * ψ x + ω) * (1 + ω)) := by
        rw [setLIntegral_const, Real.volume_Ioc, ht_step i,
          ← ENNReal.ofReal_mul (by positivity)]
        ring_nf
      rw [hvol]
      refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
      have hsI : s ∈ Icc 0 L := ⟨hti.1.trans hs.1.le, hs.2.trans hti1.2⟩
      have hQs : dist (Q s) x < η / 2 := by
        refine hτQ s hsI _ hti ?_
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
        linarith [hs.2, ht_step i]
      have := hηψ _ (hKK' (hQK s hsI)) x (hKK' hxK) (by linarith)
      rw [Real.dist_eq, abs_lt] at this
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp : Real.exp (ξ * ψ x + ω) ≤ Real.exp (2 * ω) * Real.exp (ξ * ψ (Q s)) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
      nlinarith [Real.exp_pos (ξ * ψ x + ω)]
    refine (Finset.sum_le_sum fun i hi =>
      hpiece i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).trans ?_
    rw [sum_setLIntegral_Ioc _ t ht_mono, ht0, ht1,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (lintegral_mono_set Ioc_subset_Icc_self)
  have hT : Tendsto (fun ω : ℝ => ENNReal.ofReal ((1 + ω) * Real.exp (2 * ω)) * I) (𝓝[>] 0)
      (𝓝 I) := by
    have hc' : Continuous fun ω : ℝ => ENNReal.ofReal ((1 + ω) * Real.exp (2 * ω)) :=
      ENNReal.continuous_ofReal.comp ((continuous_const.add continuous_id).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    have h1 : Tendsto (fun ω : ℝ => ENNReal.ofReal ((1 + ω) * Real.exp (2 * ω))) (𝓝[>] 0)
        (𝓝 1) := by
      simpa using (hc'.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
  exact ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ω hω => key ω hω)

/-- **DFGPS.S5 (deterministic form): the LFPP Weyl identity** `D^{φ+ψ} = e^{ξψ}·D^φ` for
continuous `φ`, `ψ`. -/
theorem lfppD_add_eq_weylScale (hφ : Continuous φ) (ψ : C(ℂ, ℝ)) (z w : ℂ) :
    lfppD ξ (fun u => φ u + ψ u) z w = weylScale ξ ψ (lfppContMetric ξ φ hφ) z w :=
  le_antisymm (lfppD_le_weylScale hφ ψ z w) (weylScale_le_lfppD hφ ψ z w)

end LFPP
end LQGMetric
