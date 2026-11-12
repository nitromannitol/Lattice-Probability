/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28Low2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28Up2

/-!
# DDDF Prop 28, Part 2 Step 2, for the family `δ ∈ (0,1)` (task P2-DDDF6f)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1474–1490 (Part 2, Step 2), for the family
`δ = 2^{-n-r}` (l. 1648): pairs at distance `≤ δ`. For such `x, x'` every path in `[0,1]²` has
weight `≥ e^{−ξ sup |φ_δ|}` and length `≥ |x − x'|`, `|x − x'|^{1−α} ≥ 2^{n(α−1)}` (`α ≥ 1`),
and `λ_δ ≤ e^{C} λ_n ≤ C' 2^{-n(1−ξQ−ζ)}` ((6.98), (5.78)); so the event forces
`sup |φ_δ| ≥ C_F√6 + 2(n+1) log 2 + m`, of probability `≤ e^{-2m}`
(`S6P28.phiVer_sup_tail_unif`).

`lower_small`: for `α ≥ 1`, `α > ξ(q + 2)` and `ε > 0` there is `c > 0` with
`P(∃ x, x' ∈ [0,1]², |x − x'| ≤ δ, d_δ(x,x') < c |x − x'|^α) ≤ ε` for all `δ ∈ (0,1)`.
(`α ≥ 1` is DDDF's `α > 1`, l. 1481, derived there from `1 − ξQ ≤ 2ξ`; a hypothesis here,
harmless since (LowerHolder) is only needed for some `α`.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF
namespace S6P28

open WhiteNoise SupTail Blueprint LFPP

/-- `d_f(x,y) ≥ e^{−ξ M} |x − y|` on `[0,1]²` if `|f| ≤ M` there (`ξ ≥ 0`) -/
lemma lenMetricOn_ge_exp {ξ M : ℝ} (hξ : 0 ≤ ξ) {f : ℂ → ℝ}
    (hM : ∀ x ∈ closedUnitSquare, |f x| ≤ M) {z w : ℂ} (hz : z ∈ closedUnitSquare)
    (hw : w ∈ closedUnitSquare) :
    Real.exp (-(ξ * M)) * ‖w - z‖ ≤ lenMetricOn ξ f closedUnitSquare z w := by
  simp only [lenMetricOn, DFGPS.crossLenIn_singleton]
  have hfin : lfppDOn ξ f closedUnitSquare z w ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lfppDOn_le_of_bound_on (B := Real.exp (ξ * M)) DFGPS.convex_closedUnitSquare hz hw
        fun x hx => Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM x hx)) hξ))
  refine (ENNReal.ofReal_le_iff_le_toReal hfin).1 (le_iInf fun P => ?_)
  have := lfppLen_ge (ξ := ξ) (f := f) P.2.1 (M := M) fun t ht => hM _ (P.2.2 t ht)
  rwa [abs_of_nonneg hξ] at this

/-- `λ_K ≤ C' 2^{-K(1 − ξq − ζ)}` from (5.78) -/
lemma lambdaN_upper_of_578 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ξ q : ℝ} (h578 : S6Eq5_78 ξ q W P) {ζ : ℝ}
    (hζ : 0 < ζ) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ K : ℕ,
      lambdaN ξ W P K ≤ C' * Real.exp (-(Real.log 2) * (1 - ξ * q - ζ) * K) := by
  obtain ⟨K₀, hK₀⟩ := h578 ζ hζ
  set g : ℕ → ℝ := fun K => Real.exp (-(Real.log 2) * (1 - ξ * q - ζ) * K)
  have hg : ∀ K, 0 < g K := fun K => Real.exp_pos _
  have ht : ∀ K, 0 ≤ lambdaN ξ W P K / g K := fun K =>
    div_nonneg (lambdaN_pos hW K).le (hg K).le
  have hS : 0 ≤ ∑ K ∈ Finset.range K₀, lambdaN ξ W P K / g K :=
    Finset.sum_nonneg fun K _ => ht K
  refine ⟨1 + ∑ K ∈ Finset.range K₀, lambdaN ξ W P K / g K, by linarith, fun K => ?_⟩
  rcases lt_or_ge K K₀ with hK | hK
  · have h1 : lambdaN ξ W P K / g K ≤ ∑ K ∈ Finset.range K₀, lambdaN ξ W P K / g K :=
      Finset.single_le_sum (fun K _ => ht K) (Finset.mem_range.2 hK)
    have h2 := (div_le_iff₀ (hg K)).1 (h1.trans (le_add_of_nonneg_left zero_le_one))
    exact h2
  · have h1 := hK₀ K hK
    have e : (2 : ℝ) ^ (-((K : ℝ) * (1 - ξ * q - ζ))) = g K := by
      rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; ring
    rw [e] at h1
    calc lambdaN ξ W P K ≤ g K := h1
      _ ≤ (1 + ∑ K ∈ Finset.range K₀, lambdaN ξ W P K / g K) * g K :=
        le_mul_of_one_le_left (hg K).le (le_add_of_nonneg_right hS)

/-- **DDDF Prop 28, Part 2 Step 2 for the family** (l. 1474–1490, 1648): small pairs. -/
theorem lower_small {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {ξ q : ℝ} (hξ : 0 < ξ) (h578 : S6Eq5_78 ξ q W P)
    (h698 : S6Eq6_98 ξ W P) {α : ℝ} (hα1 : 1 ≤ α) (hα : ξ * (q + 2) < α) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ δ ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ x y : closedUnitSquare, ‖(x : ℂ) - y‖ ≤ δ ∧ (lambdaDelta ξ W P δ)⁻¹ *
        lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y < c * ‖(x : ℂ) - y‖ ^ α}
        ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hP := hW.isProbabilityMeasure
  set ζ := (α - ξ * (q + 2)) / 2 with hζ_def
  have hζ : 0 < ζ := by rw [hζ_def]; linarith
  obtain ⟨C', hC', hlam⟩ := lambdaN_upper_of_578 hW h578 hζ
  obtain ⟨C0, hC0⟩ := h698
  set m := |Real.log ε| / 2 with hm_def
  have hm : 0 ≤ m := by positivity
  have hεm : Real.exp (-(2 * m)) ≤ ε := by
    calc Real.exp (-(2 * m)) = Real.exp (-|Real.log ε|) := by congr 1; rw [hm_def]; ring
      _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.2 (neg_abs_le _)
      _ = ε := Real.exp_log hε
  set T := ferniqueCF * Real.sqrt 6 + 2 * Real.log 2 + m with hT_def
  refine ⟨Real.exp (-C0 - ξ * T) / C', by positivity, fun δ hδ => ?_⟩
  obtain ⟨n, r, hr0, hr1, hδr⟩ := S6.exists_split hδ.1 hδ.2
  obtain ⟨hδa, hδb⟩ := split_bounds n hr0 hr1
  rw [← hδr] at hδa hδb
  have hY := isPhiVersion_phiVer hW hδ.1 hδ.2.le
  set L := Real.log 2 with hL_def
  have hL : 0 < L := Real.log_pos (by norm_num)
  set Λ := Real.exp C0 * (C' * Real.exp (-L * (1 - ξ * q - ζ) * n)) with hΛ_def
  have hΛ : lambdaDelta ξ W P δ ≤ Λ := by
    rw [hδr]
    exact (hC0 n r hr0 hr1).2.trans (mul_le_mul_of_nonneg_left (hlam n) (Real.exp_pos _).le)
  have hlam0 : 0 < lambdaDelta ξ W P δ := by
    rw [hδr]
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) (lambdaN_pos hW n)) (hC0 n r hr0 hr1).1
  have hΛ0 : 0 < Λ := hlam0.trans_le hΛ
  set S' := T + 2 * n * L with hS'_def
  have hsub : {ω | ∃ x y : closedUnitSquare, ‖(x : ℂ) - y‖ ≤ δ ∧ (lambdaDelta ξ W P δ)⁻¹ *
        lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y <
          Real.exp (-C0 - ξ * T) / C' * ‖(x : ℂ) - y‖ ^ α}
      ⊆ {ω | ferniqueCF * Real.sqrt 6 + (2 * (n + 1) * Real.log 2 + m) ≤
        ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|} := by
    rintro ω ⟨x, y, hxy, hlt⟩
    by_contra hcon
    simp only [mem_ofPred_eq, not_le] at hcon
    have hbdd : BddAbove (range fun v : ferniqueBox 0 1 => |phiVer W P δ 1 v ω|) := by
      have := (isCompact_ferniqueBox 0 1).bddAbove_image
        (continuous_abs.comp (hY.cont ω)).continuousOn
      rwa [Set.image_eq_range] at this
    have hM : ∀ z ∈ closedUnitSquare, |phiVer W P δ 1 z ω| ≤ S' := fun z hz => by
      have := le_ciSup hbdd ⟨z, closedUnitSquare_sub_box hz⟩
      rw [hS'_def, hT_def]
      have e : ferniqueCF * Real.sqrt 6 + (2 * (n + 1) * Real.log 2 + m) =
          ferniqueCF * Real.sqrt 6 + 2 * L + m + 2 * n * L := by rw [hL_def]; ring
      rw [e] at hcon
      exact this.trans hcon.le
    have hlen := lenMetricOn_ge_exp hξ.le hM x.2 y.2
    rw [norm_sub_rev] at hlen
    set a := ‖(x : ℂ) - y‖ with ha_def
    have ha0 : 0 ≤ a := norm_nonneg _
    have h4 : ((2 : ℝ) ^ n)⁻¹ ^ (1 - α) = Real.exp (-(n * L * (1 - α))) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_inv, Real.log_pow, hL_def]; congr 1
      ring
    have hpow : a ^ α * Real.exp (-(n * L * (1 - α))) ≤ a := by
      rcases ha0.eq_or_lt with h | h
      · rw [← h, Real.zero_rpow (by linarith), zero_mul]
      · have e : a = a ^ α * a ^ (1 - α) := by rw [← Real.rpow_add h]; simp
        have h2 : δ ^ (1 - α) ≤ a ^ (1 - α) := Real.rpow_le_rpow_of_nonpos h hxy (by linarith)
        have h3 : ((2 : ℝ) ^ n)⁻¹ ^ (1 - α) ≤ δ ^ (1 - α) :=
          Real.rpow_le_rpow_of_nonpos hδ.1 hδb (by linarith)
        calc a ^ α * Real.exp (-(n * L * (1 - α))) ≤ a ^ α * a ^ (1 - α) := by
              gcongr; exact h4.symm.le.trans (h3.trans h2)
          _ = a := e.symm
    have hE : -(ξ * S') + -(n * L * (1 - α)) - (C0 + -L * (1 - ξ * q - ζ) * n) =
        -C0 - ξ * T + ζ * n * L := by
      rw [hS'_def, hζ_def]; ring
    have hid : Real.exp (-C0 - ξ * T) / C' * a ^ α * Real.exp (ζ * n * L) =
        Λ⁻¹ * (Real.exp (-(ξ * S')) * (a ^ α * Real.exp (-(n * L * (1 - α))))) := by
      have key : Real.exp (-(ξ * S')) * Real.exp (-(n * L * (1 - α))) =
          Real.exp (-C0 - ξ * T) * Real.exp (ζ * n * L) *
            (Real.exp C0 * Real.exp (-L * (1 - ξ * q - ζ) * n)) := by
        simp only [← Real.exp_add]; congr 1; linear_combination hE
      have e1 : Real.exp C0 ≠ 0 := (Real.exp_pos _).ne'
      have e2 : Real.exp (-L * (1 - ξ * q - ζ) * n) ≠ 0 := (Real.exp_pos _).ne'
      symm
      calc Λ⁻¹ * (Real.exp (-(ξ * S')) * (a ^ α * Real.exp (-(n * L * (1 - α)))))
          = (Real.exp (-(ξ * S')) * Real.exp (-(n * L * (1 - α)))) * a ^ α /
              (Real.exp C0 * (C' * Real.exp (-L * (1 - ξ * q - ζ) * n))) := by
            rw [hΛ_def, div_eq_mul_inv]; ring
        _ = Real.exp (-C0 - ξ * T) * Real.exp (ζ * n * L) *
              (Real.exp C0 * Real.exp (-L * (1 - ξ * q - ζ) * n)) * a ^ α /
              (Real.exp C0 * (C' * Real.exp (-L * (1 - ξ * q - ζ) * n))) := by rw [key]
        _ = Real.exp (-C0 - ξ * T) / C' * a ^ α * Real.exp (ζ * n * L) := by
            field_simp
    have hexp : 1 ≤ Real.exp (ζ * n * L) := Real.one_le_exp (by positivity)
    have hc0 : 0 ≤ Real.exp (-C0 - ξ * T) / C' * a ^ α := by positivity
    have key : Real.exp (-C0 - ξ * T) / C' * a ^ α ≤ (lambdaDelta ξ W P δ)⁻¹ *
        lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y := by
      calc Real.exp (-C0 - ξ * T) / C' * a ^ α
          ≤ Real.exp (-C0 - ξ * T) / C' * a ^ α * Real.exp (ζ * n * L) :=
            le_mul_of_one_le_right hc0 hexp
        _ = Λ⁻¹ * (Real.exp (-(ξ * S')) * (a ^ α * Real.exp (-(n * L * (1 - α))))) := hid
        _ ≤ Λ⁻¹ * (Real.exp (-(ξ * S')) * a) := by gcongr
        _ ≤ (lambdaDelta ξ W P δ)⁻¹ * (Real.exp (-(ξ * S')) * a) := by
            gcongr
        _ ≤ _ := by gcongr
    exact absurd hlt (not_lt.2 key)
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal
    ((phiVer_sup_tail_unif hW n hδa hδb hδ.2 hm).trans hεm)

end S6P28
end DDDF
end LQGMetric
