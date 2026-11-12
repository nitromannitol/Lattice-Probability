/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_6Thm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_6Main

/-!
# LM Theorem 1.6 from LM Lemma 4.2: the assembly (task P2-LM16)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.6, l. 828–882. See `T1_6Main` for the
departures (no measurable path selection; countable dense set instead of `ℚ²`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-- LM l. 838–880 for one sample: a path `γ` of `D`-length `≤ D(z₁,z₂) + δ` inside
`cl B_R(0)` and the event `F^ε` for `K = cl B_R(0)` give
`D̃(x, y) ≤ C (D(z₁,z₂) + δ)` for some `x ∈ cl B_{2ε}(z₁)`, `y ∈ cl B_{2ε}(z₂)`. -/
theorem lm_bound_of_cover {D D' : ContMetric} {C ε δ R : ℝ} (hC : 0 < C) (hε : 0 < ε) (hδ : 0 ≤ δ)
    {z₁ z₂ : ℂ} (γ : Path (D.pt z₁) (D.pt z₂))
    (hγ : MetricGeometry.pathLength γ ≤ edist (D.pt z₁) (D.pt z₂) + ENNReal.ofReal δ)
    (hR : ∀ t, ‖D.unpt (γ t)‖ ≤ R) (hcov : lmCoverE D D' C ε (closedBall 0 R)) :
    ∃ x y, ‖x - z₁‖ ≤ 2 * ε ∧ ‖y - z₂‖ ≤ 2 * ε ∧ D'.1 (x, y) ≤ C * (D.1 (z₁, z₂) + δ) := by
  set P : ℝ → ℂ := fun t => D.unpt (γ.extend t) with hPdef
  have hPc : ContinuousOn P (Icc 0 1) :=
    ((ContMetric.continuous_unpt D).comp γ.continuous_extend).continuousOn
  have hP0 : P 0 = z₁ := by simp [hPdef]
  have hP1 : P 1 = z₂ := by simp [hPdef]
  have hcomp : D.pt ∘ P = γ.extend := rfl
  set L := MetricGeometry.curveLength (D.pt ∘ P) with hL
  have hLfin : L 0 1 ≠ ⊤ := by
    have : L 0 1 = MetricGeometry.pathLength γ := by rw [hL, hcomp]; rfl
    rw [this]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨edist_ne_top _ _, ENNReal.ofReal_ne_top⟩) hγ
  let ℓ : ℝ → ℝ := fun s => (L 0 s).toReal
  have hfin : ∀ a b, 0 ≤ a → b ≤ 1 → L a b ≠ ⊤ := fun a b ha hb =>
    ne_top_of_le_ne_top hLfin (MetricGeometry.curveLength_mono _ ha hb)
  have hsub : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → (L a b).toReal = ℓ b - ℓ a := by
    intro a b ha hab hb
    have hadd := MetricGeometry.curveLength_add (D.pt ∘ P) ha hab
    have : ℓ b = (L 0 a).toReal + (L a b).toReal := by
      simp only [ℓ, hL]; rw [← hadd, ENNReal.toReal_add (hfin 0 a le_rfl (hab.trans hb))
        (hfin a b ha hb)]
    linarith
  have hℓ : MonotoneOn ℓ (Icc 0 1) := by
    intro a ha b hb hab
    have := hsub a b ha.1 hab hb.2
    linarith [ENNReal.toReal_nonneg (a := L a b)]
  have hmemK : ∀ s, P s ∈ closedBall (0 : ℂ) R := by
    intro s
    rw [mem_closedBall, dist_zero_right]
    have := hR (projIcc 0 1 zero_le_one s)
    simpa [hPdef, Path.extend, IccExtend] using this
  obtain ⟨x, y, hx, hy, hxy⟩ := lm_chain_det D' hC.le (ρ := ε ^ 2) (by positivity) P hPc ℓ hℓ
    (fun w r => 0 < r ∧ lmGoodE D D' C w r)
    (by
      intro s _
      obtain ⟨k, w, h1, h2, -, -, h5, h6⟩ := hcov (P s) (hmemK s)
      exact ⟨w, _, h1, h2, h5, by positivity, h6⟩)
    (by
      intro w r ⟨hr, hE⟩ a ha b hb hab ha' hb' u hu v hv
      have hf : ContinuousOn (fun t => ‖P t - w‖) (Icc a b) :=
        ((hPc.mono (Icc_subset_Icc ha.1 hb.2)).sub continuousOn_const).norm
      obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hab hf
        (show r / 2 ∈ Icc ‖P a - w‖ ‖P b - w‖ from ⟨ha'.le, by rw [hb']; linarith⟩)
      have hb1 := lmGoodE_bound hC.le hr hE (q₁ := P s) (q₂ := P b)
        (by rw [mem_sphere, dist_eq_norm]; exact hfs)
        (by rw [mem_sphere, dist_eq_norm]; exact hb') hu hv
      have hed : ENNReal.ofReal (D.1 (P s, P b)) ≤ L s b :=
        (edist_dist (D.pt (P s)) (D.pt (P b))).symm.le.trans
          (MetricGeometry.edist_le_curveLength (D.pt ∘ P) hs.2)
      have hsb : D.1 (P s, P b) ≤ (L s b).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal (hfin s b (ha.1.trans hs.1) hb.2)).1 hed
      have hmono : (L s b).toReal ≤ (L a b).toReal :=
        ENNReal.toReal_mono (hfin a b ha.1 hb.2) (MetricGeometry.curveLength_mono _ hs.1 le_rfl)
      rw [hsub a b ha.1 hab hb.2] at hmono
      calc D'.1 (u, v) ≤ C * D.1 (P s, P b) := hb1
        _ ≤ C * (ℓ b - ℓ a) := mul_le_mul_of_nonneg_left (hsb.trans hmono) hC.le)
  refine ⟨x, y, hP0 ▸ hx, hP1 ▸ hy, hxy.trans (mul_le_mul_of_nonneg_left ?_ hC.le)⟩
  have h01 : ℓ 1 - ℓ 0 = (L 0 1).toReal := by
    simp only [ℓ, hL, MetricGeometry.curveLength_self, ENNReal.toReal_zero, sub_zero]
  rw [h01]
  have hD0 : 0 ≤ D.1 (z₁, z₂) := (dist_nonneg : 0 ≤ dist (D.pt z₁) (D.pt z₂))
  have hle : L 0 1 ≤ ENNReal.ofReal (D.1 (z₁, z₂) + δ) := by
    rw [ENNReal.ofReal_add hD0 hδ]
    calc L 0 1 = MetricGeometry.pathLength γ := by rw [hL, hcomp]; rfl
      _ ≤ _ := hγ
      _ = _ := by rw [edist_dist]; rfl
  exact ENNReal.toReal_le_of_le_ofReal (by linarith) hle

/-- **LM Theorem 1.6 from LM Lemma 4.2** (LM l. 828–882). -/
theorem lmThm1_6_of {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h42 : LMLem4_2 p) : LMThm1_6 := by
  refine ⟨p, hp0, hp1, ?_⟩
  intro ξ Ω _ P _ h D D' hh hxi C hC hyp
  -- fixed `z₁, z₂` (LM l. 828–834)
  have hfix : ∀ z₁ z₂ : ℂ, ∀ᵐ ω ∂P, (D' ω).1 (z₁, z₂) ≤ C * (D ω).1 (z₁, z₂) := by
    intro z₁ z₂
    let G : ℕ → ℕ → ℕ → Set Ω := fun n R m => {ω |
      (∃ γ : Path ((D ω).pt z₁) ((D ω).pt z₂), MetricGeometry.pathLength γ ≤
        edist ((D ω).pt z₁) ((D ω).pt z₂) + ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧
        ∀ t, ‖(D ω).unpt (γ t)‖ ≤ R) ∧
      (∀ x, ‖x - z₁‖ ≤ 1 / (m + 1 : ℝ) → (D' ω).1 (z₁, x) ≤ 1 / (n + 1 : ℝ)) ∧
      (∀ y, ‖y - z₂‖ ≤ 1 / (m + 1 : ℝ) → (D' ω).1 (y, z₂) ≤ 1 / (n + 1 : ℝ)) ∧
      C * (D ω).1 (z₁, z₂) + (C + 2) * (1 / (n + 1 : ℝ)) < (D' ω).1 (z₁, z₂)}
    have hG : ∀ n R m, P (G n R m) = 0 := by
      intro n R m
      have hT := h42 ξ P h D D' hh hxi C hC hyp (closedBall 0 R) (isCompact_closedBall _ _)
      have hη : (0 : ℝ) < 1 / (m + 1 : ℝ) / 2 := by positivity
      refine le_antisymm (ge_of_tendsto hT ?_) zero_le
      filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
      refine measure_mono fun ω hω => ?_
      obtain ⟨⟨γ, hγ, hR⟩, h1, h2, hbad⟩ := hω
      intro hcov
      obtain ⟨x, y, hx, hy, hxy⟩ := lm_bound_of_cover hC hε.1 (by positivity) γ hγ hR hcov
      have hx' := h1 x (by linarith [hε.2])
      have hy' := h2 y (by linarith [hε.2])
      have t1 := (D' ω).2.triangle z₁ x z₂
      have t2 := (D' ω).2.triangle x y z₂
      nlinarith
    have hall : ∀ᵐ ω ∂P, ∀ n R m, ω ∉ G n R m := by
      simp only [ae_all_iff]
      exact fun n R m => measure_eq_zero_iff_ae_notMem.1 (hG n R m)
    filter_upwards [hxi.1.2.2.1, hall] with ω hlen hnot
    by_contra hbad
    push_neg at hbad
    obtain ⟨n, hn⟩ := exists_nat_gt ((C + 2) / ((D' ω).1 (z₁, z₂) - C * (D ω).1 (z₁, z₂)))
    have hgap : 0 < (D' ω).1 (z₁, z₂) - C * (D ω).1 (z₁, z₂) := by linarith
    have hδ : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    obtain ⟨γ, hγ⟩ := hlen.1 ((D ω).pt z₁) ((D ω).pt z₂) _ hδ
    have hcpt : IsCompact (range fun t => (D ω).unpt (γ t)) :=
      isCompact_range ((ContMetric.continuous_unpt _).comp γ.continuous)
    obtain ⟨R0, hR0⟩ := (isBounded_iff_forall_norm_le.1 hcpt.isBounded)
    obtain ⟨R, hR⟩ := exists_nat_ge R0
    have hc1 : Continuous fun x => (D' ω).1 (z₁, x) :=
      (D' ω).1.continuous.comp (continuous_const.prodMk continuous_id)
    have hc2 : Continuous fun y => (D' ω).1 (y, z₂) :=
      (D' ω).1.continuous.comp (continuous_id.prodMk continuous_const)
    obtain ⟨η1, hη1, hη1'⟩ := Metric.continuousAt_iff.1 hc1.continuousAt _ hδ
    obtain ⟨η2, hη2, hη2'⟩ := Metric.continuousAt_iff.1 hc2.continuousAt _ hδ
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / min η1 η2)
    have hmη : 1 / (m + 1 : ℝ) < min η1 η2 := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (lt_min hη1 hη2)] at hm
      nlinarith [lt_min hη1 hη2]
    refine hnot n R m ⟨⟨γ, hγ, fun t => (hR0 _ ⟨t, rfl⟩).trans hR⟩, ?_, ?_, ?_⟩
    · intro x hx
      have := hη1' (x := x) (by rw [dist_eq_norm]; linarith [min_le_left η1 η2])
      rw [(D' ω).2.self_eq_zero, Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans this.le
    · intro y hy
      have := hη2' (x := y) (by rw [dist_eq_norm]; linarith [min_le_right η1 η2])
      rw [(D' ω).2.self_eq_zero, Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans this.le
    · rw [div_lt_iff₀ hgap] at hn
      have : (C + 2) * (1 / (n + 1 : ℝ)) < (D' ω).1 (z₁, z₂) - C * (D ω).1 (z₁, z₂) := by
        rw [mul_one_div, div_lt_iff₀ (by positivity)]; nlinarith
      linarith
  -- all `z, w` by continuity (LM l. 832–834)
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable (Q × Q) := by haveI := hQc.to_subtype; infer_instance
  have hQ : ∀ᵐ ω ∂P, ∀ q : Q × Q, (D' ω).1 (q.1, q.2) ≤ C * (D ω).1 (q.1, q.2) :=
    ae_all_iff.2 fun q => hfix q.1 q.2
  filter_upwards [hQ] with ω hω z w
  have hcl : IsClosed {x : ℂ × ℂ | (D' ω).1 x ≤ C * (D ω).1 x} :=
    isClosed_le (D' ω).1.continuous (continuous_const.mul (D ω).1.continuous)
  have hsub : (Q ×ˢ Q : Set (ℂ × ℂ)) ⊆ {x : ℂ × ℂ | (D' ω).1 x ≤ C * (D ω).1 x} :=
    fun x hx => hω (⟨x.1, hx.1⟩, ⟨x.2, hx.2⟩)
  have := closure_minimal hsub hcl
  rw [(hQd.prod hQd).closure_eq] at this
  exact this (mem_univ (z, w))

end LQGMetric.LM
