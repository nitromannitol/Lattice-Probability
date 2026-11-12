/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_6Cross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_6Chain
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.IntermediateValue

/-!
# LM Theorem 1.6: the crossing times along a path (task P2-LM16)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.6, l. 844–880. `lm_chain_det` is the
deterministic content of l. 844–880: if every point of a path `P : [0,1] → ℂ` lies in a ball
`B_{r/2}(w)` with `r ∈ [ρ, ε]` and `(w, r)` good, where good means that whenever `P` crosses
`A_{r/2, r}(w)` between times `a ≤ b` all points of `∂B_r(w)` are `D̃`-within `C (ℓ(b) − ℓ(a))`
(LM (4.3), l. 852–856, with `ℓ` the `D`-length of `P|_{[0,·]}`), then
`D̃(cl B_{2ε}(P 0), cl B_{2ε}(P 1)) ≤ C (ℓ(1) − ℓ(0))`.

The times `t_j` (LM l. 844–847) are built by recursion; the recursion stops after finitely
many steps since each step moves `P` by at least `ρ/2` and `P` is uniformly continuous.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.LM

/-- **LM Theorem 1.6, deterministic step** (LM l. 844–880). -/
theorem lm_chain_det (D' : ContMetric) {C ε ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (P : ℝ → ℂ) (hPc : ContinuousOn P (Icc 0 1)) (ℓ : ℝ → ℝ) (hℓ : MonotoneOn ℓ (Icc 0 1))
    (good : ℂ → ℝ → Prop)
    (hcov : ∀ s ∈ Icc (0 : ℝ) 1, ∃ w r, ρ ≤ r ∧ r ≤ ε ∧ ‖P s - w‖ < r / 2 ∧ good w r)
    (hgood : ∀ w r, good w r → ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b →
      ‖P a - w‖ < r / 2 → ‖P b - w‖ = r →
      ∀ u ∈ sphere w r, ∀ v ∈ sphere w r, D'.1 (u, v) ≤ C * (ℓ b - ℓ a)) :
    ∃ x y, ‖x - P 0‖ ≤ 2 * ε ∧ ‖y - P 1‖ ≤ 2 * ε ∧ D'.1 (x, y) ≤ C * (ℓ 1 - ℓ 0) := by
  classical
  choose! W R hρR hRε hin hg using hcov
  -- the exit predicate and the next crossing time
  let Ex : ℝ → Prop := fun s => ∃ t ∈ Icc s 1, R s ≤ ‖P t - W s‖
  have hivt : ∀ s ∈ Icc (0 : ℝ) 1, Ex s → ∃ t ∈ Icc s 1, ‖P t - W s‖ = R s := by
    intro s hs ⟨t₁, ht₁, hR⟩
    have hsub : Icc s t₁ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs.1 ht₁.2
    have hf : ContinuousOn (fun t => ‖P t - W s‖) (Icc s t₁) :=
      ((hPc.mono hsub).sub continuousOn_const).norm
    have hmem : R s ∈ Icc ‖P s - W s‖ ‖P t₁ - W s‖ :=
      ⟨by linarith [hin s hs, hρR s hs], hR⟩
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc ht₁.1 hf hmem
    exact ⟨t, ⟨ht.1, ht.2.trans ht₁.2⟩, hft⟩
  let nx : ℝ → ℝ := fun s =>
    if h : s ∈ Icc (0 : ℝ) 1 ∧ Ex s then Classical.choose (hivt s h.1 h.2) else s
  have hnx : ∀ s ∈ Icc (0 : ℝ) 1, nx s ∈ Icc s 1 ∧ (Ex s → ‖P (nx s) - W s‖ = R s) := by
    intro s hs
    by_cases h : Ex s
    · have hh : s ∈ Icc (0 : ℝ) 1 ∧ Ex s := ⟨hs, h⟩
      have := Classical.choose_spec (hivt s hs h)
      simp only [nx, dif_pos hh]
      exact ⟨this.1, fun _ => this.2⟩
    · have hh : ¬ (s ∈ Icc (0 : ℝ) 1 ∧ Ex s) := fun h' => h h'.2
      simp only [nx, dif_neg hh]
      exact ⟨⟨le_rfl, hs.2⟩, fun h' => absurd h' h⟩
  let S : ℕ → ℝ := fun n => nx^[n] 0
  have hS0 : S 0 = 0 := rfl
  have hSs : ∀ n, S (n + 1) = nx (S n) := fun n => Function.iterate_succ_apply' nx n 0
  have hSI : ∀ n, S n ∈ Icc (0 : ℝ) 1 := by
    intro n
    induction n with
    | zero => exact ⟨le_rfl, zero_le_one⟩
    | succ n ih =>
      rw [hSs]; have := (hnx _ ih).1; exact ⟨ih.1.trans this.1, this.2⟩
  have hSle : ∀ n, S n ≤ S (n + 1) := fun n => by rw [hSs]; exact (hnx _ (hSI n)).1.1
  have hSmono : Monotone S := monotone_nat_of_le_succ hSle
  -- uniform continuity: each exit step takes parameter time at least `η`
  obtain ⟨η, hη, hηP⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hPc) (ρ / 2) (by linarith)
  have hstep : ∀ n, Ex (S n) → S n + η ≤ S (n + 1) := by
    intro n hE
    by_contra hlt
    push_neg at hlt
    have h1 := (hnx _ (hSI n)).2 hE
    rw [← hSs] at h1
    have hd : dist (S (n + 1)) (S n) < η := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hSle n])]; linarith
    have hP := hηP _ (hSI (n + 1)) _ (hSI n) hd
    rw [dist_eq_norm] at hP
    have h2 := hin _ (hSI n)
    have h3 := hρR _ (hSI n)
    have : ‖P (S (n + 1)) - W (S n)‖ ≤ ‖P (S (n + 1)) - P (S n)‖ + ‖P (S n) - W (S n)‖ := by
      calc ‖P (S (n + 1)) - W (S n)‖ = ‖(P (S (n + 1)) - P (S n)) + (P (S n) - W (S n))‖ := by
            congr 1; ring
        _ ≤ _ := norm_add_le _ _
    linarith
  have hstop : ∃ n, ¬ Ex (S n) := by
    by_contra hall
    push_neg at hall
    have hlin : ∀ n : ℕ, (n : ℝ) * η ≤ S n := by
      intro n
      induction n with
      | zero => simp [hS0]
      | succ n ih => push_cast; linarith [hstep n (hall n)]
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / η)
    have := hlin n
    have h1 : 1 < (n : ℝ) * η := by rwa [div_lt_iff₀ hη] at hn
    linarith [(hSI n).2]
  let J := Nat.find hstop
  have hJ : ¬ Ex (S J) := Nat.find_spec hstop
  have hbefore : ∀ i < J, Ex (S i) := fun i hi => by
    have := Nat.find_min hstop hi; push_neg at this; exact this
  -- the chain data
  have hT : Monotone (fun n => ℓ (S n)) :=
    monotone_nat_of_le_succ fun n => hℓ (hSI n) (hSI (n + 1)) (hSle n)
  have hin' : ∀ i, 1 ≤ i → i ≤ J → ‖P (S (i - 1)) - W (S (i - 1))‖ < R (S (i - 1)) / 2 :=
    fun i _ _ => hin _ (hSI _)
  have hon' : ∀ i, 1 ≤ i → i ≤ J → ‖P (S i) - W (S (i - 1))‖ = R (S (i - 1)) := by
    intro i hi1 hiJ
    have he : i = (i - 1) + 1 := by omega
    have h := (hnx _ (hSI (i - 1))).2 (hbefore (i - 1) (by omega))
    rw [← hSs, ← he] at h
    exact h
  have hr' : ∀ i, 0 < R (S (i - 1)) := fun i => lt_of_lt_of_le hρ (hρR _ (hSI _))
  have hdiam : ∀ i, 1 ≤ i → i ≤ J → ∀ u ∈ sphere (W (S (i - 1))) (R (S (i - 1))),
      ∀ v ∈ sphere (W (S (i - 1))) (R (S (i - 1))),
      D'.1 (u, v) ≤ C * (ℓ (S i) - ℓ (S (i - 1))) := by
    intro i hi1 hiJ
    exact hgood _ _ (hg _ (hSI _)) _ (hSI _) _ (hSI _) (hSmono (Nat.sub_le i 1))
      (hin' i hi1 hiJ) (hon' i hi1 hiJ)
  -- the endpoint
  have hend : ‖P (S J) - P 1‖ ≤ 2 * ε := by
    have h1 : ‖P 1 - W (S J)‖ < R (S J) := by
      by_contra hc; push_neg at hc; exact hJ ⟨1, ⟨(hSI J).2, le_rfl⟩, hc⟩
    have h2 := hin _ (hSI J)
    have h3 := hRε _ (hSI J)
    calc ‖P (S J) - P 1‖ = ‖(P (S J) - W (S J)) - (P 1 - W (S J))‖ := by congr 1; ring
      _ ≤ ‖P (S J) - W (S J)‖ + ‖P 1 - W (S J)‖ := norm_sub_le _ _
      _ ≤ 2 * ε := by linarith [hρR _ (hSI J), hρ]
  have hℓ1 : ℓ (S J) - ℓ (S 0) ≤ ℓ 1 - ℓ 0 := by
    rw [hS0]; linarith [hℓ (hSI J) ⟨zero_le_one, le_rfl⟩ (hSI J).2]
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · refine ⟨P (S J), P (S J), ?_, hend, ?_⟩
    · rw [hJ0, hS0, sub_self, norm_zero]
      linarith [hRε _ (hSI 0), hρR _ (hSI 0), hρ]
    · rw [D'.2.self_eq_zero]
      exact mul_nonneg hC (by linarith [hℓ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one])
  · obtain ⟨x, hx, hxu⟩ := chain_main D' hC (fun n => P (S n)) (fun j => W (S (j - 1)))
      (fun j => R (S (j - 1))) (fun n => ℓ (S n)) J hT hin' hon' hr'
      (fun i => hRε _ (hSI _)) hdiam J hJ0 le_rfl (P (S J))
      (by rw [mem_sphere, dist_eq_norm]; exact hon' J hJ0 le_rfl)
    refine ⟨x, P (S J), by simpa [hS0] using hx, hend, ?_⟩
    calc D'.1 (x, P (S J)) ≤ C * (ℓ (S J) - ℓ (S 0)) := hxu
      _ ≤ C * (ℓ 1 - ℓ 0) := mul_le_mul_of_nonneg_left hℓ1 hC

end LQGMetric.LM
