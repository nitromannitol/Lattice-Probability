/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightE2Core at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightE
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightGauss
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightEvent
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSScaling
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# GM S2.4e at centre 0 for a normalized field (task P2-TIGHT)

GM (arXiv:1905.00383v3) l. 1434 and l. 3605: "By Axiom V (tightness across scales), there is some
large bounded open set `U` …" such that geodesics between points of `B_r(z)` stay in `rU + z`.
Decision D-A3 (`decisions/DEC-A.md` (c), S2.4e): this does **not** follow from Axiom V alone and
is proved from DFGPS Thm 1.5 (`Blueprint.DFGPSScaling`) and LM Lemma 3.1
(`Blueprint.LMLem3_1a`), explicit hypotheses here.

`gm_S2_4e_normalized`: `∀ β > 0 ∃ R > 1` such that for every normalized whole-plane GFF and
`r > 0`, with probability `> 1 − β` some `M` has `D_h(u, v) < M` on `B̄_{2r}(0)²` and
`M < D_h(x, y)` for `x ∈ B̄_{2r}(0)`, `y ∈ ∂B_{Rr}(0)`.

Proof (D-A3): radii `r_k = 8^{K−k} r`; the events of `exists_crossing_event` have probability
`≥ p` (LM's `p` for `a = 1`, `b = 3/4`), so LM L3.1 gives a good `k ≤ K − m` off probability
`c₀ e^{−K}`; there `D_h(x, y) ≥ s 𝔠_{r_k} e^{ξ h_{r_k}(0)}` (`le_of_forall_internal_crossing`);
DFGPS T1.5 with `ζ = ξQ/2` gives `𝔠_{r_k} ≥ 8^{jκ} 𝔠_r` (`j = K − k`, `κ = ξQ/2`); the Gaussian
union bound (`prob_exists_circleAvg_inc_le`) gives `h_{8^j r}(0) − h_r(0) > −κ j log 8/(2ξ)`; and
`gm_S2_4b'` gives `D_h < S 𝔠_r e^{ξ h_r(0)}` on `B̄_{2r}`. Own argument; DEVIATIONS DA5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric
namespace GM
namespace Tight

open Blueprint

lemma exists_good_of_count {Ω : Type} (E : ℕ → Set Ω) {K m : ℕ} (hmK : m ≤ K) (ω : Ω)
    (h : (m : ℝ) < countOcc E K ω) : ∃ k, 1 ≤ k ∧ k + m ≤ K ∧ ω ∈ E k := by
  classical
  by_contra hcon
  push Not at hcon
  have : countOcc E K ω ≤ m := by
    unfold countOcc
    calc _ ≤ (Finset.Ioc (K - m) K).card := Finset.card_le_card (fun k hk => by
            simp only [Finset.mem_filter, Finset.mem_Icc] at hk
            refine Finset.mem_Ioc.2 ⟨?_, hk.1.2⟩
            by_contra h'
            exact hcon k hk.1.1 (by omega) hk.2)
      _ = m := by simp only [Nat.card_Ioc]; omega
  exact absurd h (not_lt.2 (by exact_mod_cast this))

lemma final_ineq_S24e {s S cr cρ ar aρ ξ κ L j m : ℝ} (hs : 0 < s) (hcr : 0 < cr)
    (hξ : 0 < ξ) (hκL : 0 ≤ κ * L) (hjm : m ≤ j)
    (hc : cr ≤ Real.exp (-(j * L) * κ) * cρ)
    (ha : -(κ * L / (2 * ξ) * j) < aρ - ar)
    (hm : S < s * Real.exp (κ * L / 2 * m)) :
    S * cr * Real.exp (ξ * ar) < s * cρ * Real.exp (ξ * aρ) := by
  have h1 : cr * Real.exp (κ * L * j) ≤ cρ := by
    have := mul_le_mul_of_nonneg_right hc (Real.exp_pos (κ * L * j)).le
    have e : Real.exp (-(j * L) * κ) * cρ * Real.exp (κ * L * j) = cρ := by
      rw [mul_comm (Real.exp _) cρ, mul_assoc, ← Real.exp_add,
        show -(j * L) * κ + κ * L * j = 0 by ring, Real.exp_zero, mul_one]
    rwa [e] at this
  have h2 : ξ * ar - κ * L / 2 * j < ξ * aρ := by
    have := mul_lt_mul_of_pos_left ha hξ
    have e : ξ * (κ * L / (2 * ξ) * j) = κ * L / 2 * j := by field_simp
    rw [mul_sub, mul_neg, e] at this
    linarith
  have h3 : Real.exp (κ * L / 2 * m) ≤ Real.exp (κ * L / 2 * j) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hjm (by positivity))
  have hcp : 0 < cρ := lt_of_lt_of_le (by positivity) h1
  calc S * cr * Real.exp (ξ * ar)
      < s * Real.exp (κ * L / 2 * m) * cr * Real.exp (ξ * ar) :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hm hcr) (Real.exp_pos _)
    _ ≤ s * Real.exp (κ * L / 2 * j) * cr * Real.exp (ξ * ar) := by gcongr
    _ = s * (cr * Real.exp (κ * L * j)) * Real.exp (ξ * ar - κ * L / 2 * j) := by
        rw [Real.exp_sub, show κ * L * j = κ * L / 2 * j + κ * L / 2 * j by ring, Real.exp_add]
        field_simp
    _ ≤ s * cρ * Real.exp (ξ * ar - κ * L / 2 * j) := by gcongr
    _ < s * cρ * Real.exp (ξ * aρ) :=
        mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 h2) (by positivity)

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- **GM.S2.4e** at centre `0`, for a normalized whole-plane GFF. -/
theorem gm_S2_4e_normalized (hT15 : DFGPSScaling) (hL31 : LMLem3_1a) (hγ0 : 0 < γ)
    (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c) {β : ℝ≥0∞} (hβ : 0 < β) :
    ∃ R : ℝ, 1 < R ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ r : ℝ, 0 < r →
      P {ω | ¬ ∃ M : ℝ, (∀ u ∈ closedBall (0 : ℂ) (2 * r), ∀ v ∈ closedBall (0 : ℂ) (2 * r),
          (D (h ω)).1 (u, v) < M) ∧
        ∀ x ∈ closedBall (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (R * r),
          M < (D (h ω)).1 (x, y)} < β := by
  set ξ := xiGamma γ with hξdef
  have hξ : 0 < ξ := xiGamma_pos hγ0
  have hQ : 0 < Q γ := by unfold Q; positivity
  set κ := ξ * Q γ / 2 with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨δ₀, hδ₀, hscal⟩ := hT15 γ hγ0 hγ2 D c hD κ hκ
  obtain ⟨p, c₀, hp0, hp1, hc₀, hLM⟩ := hL31 (1 / 8) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) 1 one_pos (3 / 4) (by norm_num) (by norm_num)
  obtain ⟨s, hs, Hev⟩ := exists_crossing_event hD (ε := ENNReal.ofReal (1 - p))
    (ENNReal.ofReal_pos.2 (by linarith))
  have hβ1 : min β 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set β₀ : ℝ := (min β 1).toReal with hβ₀def
  have hβ₀ : 0 < β₀ := ENNReal.toReal_pos (ne_of_gt (lt_min hβ one_pos)) hβ1
  have hβ4 : 0 < β₀ / 4 := by linarith
  have hβ₀β : ENNReal.ofReal β₀ ≤ β := by
    rw [hβ₀def, ENNReal.ofReal_toReal hβ1]; exact min_le_left _ _
  obtain ⟨S, hS, HS⟩ := gm_S2_4b' hD (isCompact_closedBall (0 : ℂ) 2)
    (ε := ENNReal.ofReal (β₀ / 4)) (ENNReal.ofReal_pos.2 hβ4)
  set L := Real.log 8 with hLdef
  have hL : 0 < L := Real.log_pos (by norm_num)
  set aG := κ * L / (2 * ξ) with haG
  set lam := aG ^ 2 / (2 * L) with hlamdef
  have hlam : 0 < lam := by positivity
  set q := Real.exp (-lam) with hqdef
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hqdef]; exact (Real.exp_lt_exp.2 (by linarith : -lam < 0)).trans_eq Real.exp_zero
  have ev1 : ∀ᶠ m : ℕ in atTop, (1 / 8 : ℝ) ^ m < δ₀ :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      (gt_mem_nhds hδ₀)
  have ev3 : ∀ᶠ m : ℕ in atTop, q ^ m / (1 - q) < β₀ / 4 := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).div_const (1 - q)
    rw [zero_div] at this
    exact this.eventually (gt_mem_nhds hβ4)
  obtain ⟨m, hm1, hm3, hmge, hm2⟩ := (ev1.and (ev3.and ((eventually_ge_atTop 1).and
    (eventually_ge_atTop ⌈S / (s * (κ * L / 2))⌉₊)))).exists
  have hmS : S < s * Real.exp (κ * L / 2 * m) := by
    have h1 : S / (s * (κ * L / 2)) ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm2)
    have h2 : S ≤ s * (κ * L / 2) * m := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    have h3 := Real.add_one_le_exp (κ * L / 2 * m)
    nlinarith
  have evK : ∀ᶠ K : ℕ in atTop, c₀ * Real.exp (-1 * K) < β₀ / 4 := by
    have : Tendsto (fun K : ℕ => c₀ * Real.exp (-1 * (K : ℝ))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul c₀
      simpa [Function.comp_def, neg_one_mul] using this
    exact this.eventually (gt_mem_nhds hβ4)
  obtain ⟨K, hK1, hK2⟩ := (evK.and (eventually_ge_atTop (4 * m + 1))).exists
  refine ⟨8 ^ K, one_lt_pow₀ (by norm_num) (by omega), ?_⟩
  intro Ω _ P _ h hh r hr
  have hwp := hh.1
  set rr : ℕ → ℝ := fun k => 8 ^ K * r / 8 ^ k with hrrdef
  have hrr : ∀ k, 0 < rr k := fun k => by positivity
  choose E hEm hEc hEae using fun k => Hev P h hwp (rr k) (hrr k)
  have hAI : AnnulusIterHyp h (1 / 8) (1 / 2) rr E := by
    refine ⟨hrr, fun a b hab => ?_, fun k => le_of_eq ?_, hEm⟩
    · show 8 ^ K * r / 8 ^ b ≤ 8 ^ K * r / 8 ^ a
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by norm_num) hab)
    · show 8 ^ K * r / 8 ^ (k + 1) / (8 ^ K * r / 8 ^ k) = 1 / 8
      have h8 : (8 : ℝ) ^ k ≠ 0 := by positivity
      rw [pow_succ]
      field_simp
  have hEp : ∀ k, ENNReal.ofReal p ≤ P (E k) := fun k => by
    have h1 : (1 : ℝ≥0∞) ≤ P (E k) + P (E k)ᶜ := by
      rw [← measure_univ (μ := P)]
      exact (measure_mono (union_compl_self (E k)).symm.subset).trans (measure_union_le _ _)
    have h2 : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
      rw [← ENNReal.ofReal_add hp0.le (by linarith)]; simp
    rw [← h2] at h1
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1
      (h1.trans (add_le_add le_rfl (hEc k).le))
  have hB2 := hLM P h hh rr E hAI hEp K
  have hB3 := prob_exists_circleAvg_inc_le hwp hr 0 (a := aG) (by positivity) hmge K
  have hsum : ∑ k ∈ Finset.Ico m K, ENNReal.ofReal (Real.exp (-(aG ^ 2 * k) / (2 * L))) ≤
      ENNReal.ofReal (β₀ / 4) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ∀ k : ℕ, Real.exp (-(aG ^ 2 * k) / (2 * L)) = q ^ k := fun k => by
      rw [hqdef, ← Real.exp_nat_mul]; congr 1; rw [hlamdef]; ring
    simp only [e]
    exact (geom_sum_Ico_le_of_lt_one hq0 hq1).trans hm3.le
  have HB1 := HS P h hwp r hr 0
  have hlen := hD.length P h (isGFFPlusCont_of_wp hwp)
  have hEall := ae_all_iff.2 hEae
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  calc _ ≤ P (({ω | ¬ ∀ u ∈ closedBall (0 : ℂ) 2, ∀ v ∈ closedBall (0 : ℂ) 2,
          (D (h ω)).1 ((r : ℂ) * u + 0, (r : ℂ) * v + 0) <
            S * c r * Real.exp (xiGamma γ * circleAvg (h ω) r 0)} ∪
        {ω | (countOcc E K ω : ℝ) < 3 / 4 * K}) ∪
        {ω | ∃ k ∈ Finset.Ico m K,
          circleAvg (h ω) (8 ^ k * r) 0 - circleAvg (h ω) r 0 ≤ -(aG * k)}) := by
        refine measure_mono_ae ?_
        filter_upwards [hlen, hEall] with ω hlω hEω hbad
        by_contra hcon
        have g1 : ∀ u ∈ closedBall (0 : ℂ) 2, ∀ v ∈ closedBall (0 : ℂ) 2,
            (D (h ω)).1 ((r : ℂ) * u + 0, (r : ℂ) * v + 0) <
              S * c r * Real.exp (xiGamma γ * circleAvg (h ω) r 0) := by
          by_contra hc; exact hcon (Or.inl (Or.inl hc))
        have g2 : ¬ ((countOcc E K ω : ℝ) < 3 / 4 * K) := fun hc => hcon (Or.inl (Or.inr hc))
        have g3 : ∀ k ∈ Finset.Ico m K,
            -(aG * k) < circleAvg (h ω) (8 ^ k * r) 0 - circleAvg (h ω) r 0 := fun k hk => by
          by_contra hc; push Not at hc; exact hcon (Or.inr ⟨k, hk, hc⟩)
        apply hbad
        have hmK : (m : ℝ) < countOcc E K ω := by
          have : (4 * m + 1 : ℝ) ≤ K := by exact_mod_cast hK2
          push Not at g2; linarith
        obtain ⟨k, hk1, hkm, hkE⟩ := exists_good_of_count E (by omega : m ≤ K) ω hmK
        set j := K - k with hjdef
        have hjm : m ≤ j := by omega
        have hjK : j < K := by omega
        have hρ : rr k = 8 ^ j * r := by
          show 8 ^ K * r / 8 ^ k = 8 ^ (K - k) * r
          rw [pow_sub₀ (8 : ℝ) (by norm_num) (by omega : k ≤ K)]; ring
        have h8j : (8 : ℝ) ≤ 8 ^ j := by
          calc (8 : ℝ) = 8 ^ 1 := (pow_one 8).symm
            _ ≤ 8 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
        have h8K : (8 : ℝ) ^ j ≤ 8 ^ K := pow_le_pow_right₀ (by norm_num) hjK.le
        refine ⟨S * c r * Real.exp (xiGamma γ * circleAvg (h ω) r 0), ?_, ?_⟩
        · intro u hu v hv
          have hn : ∀ w : ℂ, w ∈ closedBall (0 : ℂ) (2 * r) → w / r ∈ closedBall (0 : ℂ) 2 :=
            fun w hw => by
              rw [mem_closedBall, dist_zero_right] at hw ⊢
              rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
                div_le_iff₀ hr]; linarith
          have := g1 _ (hn u hu) _ (hn v hv)
          rwa [show (r : ℂ) * (u / r) + 0 = u by field_simp; ring,
            show (r : ℂ) * (v / r) + 0 = v by field_simp; ring] at this
        · intro x hx y hy
          have hcross := hEω k hkE
          have hU : {w : ℂ | rr k / 4 ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ 3 * rr k / 8} ⊆
              (annulus 0 (1 / 8 * rr k) (1 / 2 * rr k) : Set ℂ) := fun w hw => by
            have := hrr k
            show 1 / 8 * rr k < ‖w - 0‖ ∧ ‖w - 0‖ < 1 / 2 * rr k
            constructor <;> linarith [hw.1, hw.2]
          have hx' : ‖x - 0‖ ≤ rr k / 4 := by
            rw [mem_closedBall, dist_eq_norm] at hx
            rw [hρ]; nlinarith
          have hy' : 3 * rr k / 8 ≤ ‖y - 0‖ := by
            rw [mem_sphere, dist_eq_norm] at hy
            rw [hy, hρ]; nlinarith
          have hlow := le_of_forall_internal_crossing hlω (by linarith [hrr k]) hU hx' hy'
            (fun u hu v hv => hcross u hu v hv)
          refine lt_of_lt_of_le ?_ hlow
          -- DFGPS scaling
          set δ : ℝ := ((8 : ℝ) ^ j)⁻¹ with hδdef
          have hδpos : 0 < δ := by positivity
          have hδlt : δ < δ₀ := by
            calc δ ≤ ((8 : ℝ) ^ m)⁻¹ :=
                  inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hjm)
              _ = (1 / 8 : ℝ) ^ m := by rw [one_div, inv_pow]
              _ < δ₀ := hm1
          have hsc := (hscal δ ⟨hδpos, hδlt⟩ (rr k) (hrr k)).2
          have hδr : δ * rr k = r := by rw [hρ, hδdef]; field_simp
          rw [hδr, show ξ * Q γ - κ = κ by rw [hκdef]; ring,
            div_le_iff₀ (hD.tightness.1 _ (hrr k)),
            Real.rpow_def_of_pos hδpos, hδdef, Real.log_inv, Real.log_pow] at hsc
          have hg := g3 j (Finset.mem_Ico.2 ⟨hjm, hjK⟩)
          rw [← hρ] at hg
          exact final_ineq_S24e (j := (j : ℝ)) (m := (m : ℝ)) hs (hD.tightness.1 r hr) hξ
            (by positivity) (by exact_mod_cast hjm) (by rw [← hLdef] at hsc; convert hsc using 3)
            (by rw [haG] at hg; exact hg) hmS
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_union_le _ _) le_rfl
    _ < ENNReal.ofReal (β₀ / 4) + ENNReal.ofReal (β₀ / 4) + ENNReal.ofReal (β₀ / 4) := by
        refine ENNReal.add_lt_add_of_lt_of_le (measure_ne_top _ _)
          (ENNReal.add_lt_add_of_lt_of_le (measure_ne_top _ _) HB1
            (hB2.trans (ENNReal.ofReal_le_ofReal ?_))) (hB3.trans hsum)
        simpa [neg_one_mul] using hK1.le
    _ ≤ β := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hβ₀β

end Tight
end GM
end LQGMetric
