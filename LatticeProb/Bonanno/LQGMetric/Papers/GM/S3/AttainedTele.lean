/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.AttainedTele at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedShortcut

/-!
# GM §3.3: the telescoping bound (3.17) along a `D`-geodesic
(task P2-M2F, WP-M2f, row 8 of `blueprint/M2.md`)

GM = Gwynne–Miller, arXiv:1905.00383v3, proof of Proposition 3.6, Steps 2–3 (l. 1440–1488).

Deterministic core of GM's Steps 2–3. GM defines times `t_0 = 0 < t_1 < …` (`t_j` = first exit
of a good ball `B_{r_j}(w_j)` with `P(t_{j−1}) ∈ B_{r_j/2}(w_j)`, `s_j` = last visit of
`∂B_{αr_j}(w_j)` before `t_j`), shows (3.14) `D̃(P(s_j), P(t_j)) ≤ C'(t_j − s_j)`,
`D̃(P(t_{j−1}), P(s_j)) ≤ C_*(s_j − t_{j−1})`, (3.16) `s_j − t_{j−1} ≤ A/(A+1)(t_j − t_{j−1})`, and
sums (3.17). We run the same recursion as an induction on the number of steps:

* `tele_step`: one step `a = t_{j−1} ↦ t = t_j` (with `s = s_j`):
  `D̃(P(a), P(t)) ≤ (C' + A/(A+1)(C_* − C'))(t − a)` and `|P(t) − P(a)| ≥ r/2`;
* `tele_core`: the sum (3.17) from `a₀` to `b₀`: every step advances by at least the
  uniform-continuity modulus `δ₀` of `P` at Euclidean scale `r_min/2`, so finitely many steps
  reach `b₀`; the last, incomplete step (when `P(b₀)` is already in the good ball) costs at
  most `C_* ω`, where `ω` bounds `b₀ − a = D(P(a), P(b₀))` for such `a`. (GM handles the two ends
  through `J̲`, `J̄` and (3.15), (3.18); we keep the end errors explicit as `ω`.)

The comparison input (3.14) enters as the hypothesis `hcomp` (from condition 1 of `𝖤_r(w)` and
GM.S3.7, for a sub-path staying in the closed annulus).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

section Tele

variable (D D' : ContMetric) {P : ℝ → ℂ} {L : ℝ}

/-- one step of GM's recursion (l. 1440–1477, (3.14), (3.16)) -/
theorem tele_step (hP : ContinuousOn P (Icc 0 L))
    (hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s|)
    {α A Cs C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hCC : C' ≤ Cs)
    (hratio : ∀ x y, D'.1 (x, y) ≤ Cs * D.1 (x, y))
    {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hround : ∃ (a' b' : ℝ) (G : ℝ → ℂ),
      Disconnects (G '' Icc a' b') (sphere w (α * r)) (sphere w r) ∧
      D.len G a' b' ≤ ENNReal.ofReal A * setDist D (sphere w (α * r)) (sphere w r))
    (hcomp : ∀ s t, 0 ≤ s → s ≤ t → t ≤ L → P s ∈ sphere w (α * r) → P t ∈ sphere w r →
      (∀ u ∈ Icc s t, P u ∈ closedBall w r ∧ P u ∉ ball w (α * r)) →
      D'.1 (P s, P t) ≤ C' * (t - s))
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hbL : b ≤ L)
    (hPa : P a ∈ ball w (r / 2)) (hPb : P b ∉ ball w r) (h0 : P 0 ∉ ball w r)
    (hL : P L ∉ ball w r) :
    ∃ t ∈ Ioc a b, r / 2 ≤ ‖P t - P a‖ ∧
      D'.1 (P a, P t) ≤ (C' + A / (A + 1) * (Cs - C')) * (t - a) := by
  have hPc : ContinuousOn P (Icc a b) := hP.mono (Icc_subset_Icc ha0 hbL)
  -- the exit time `t`
  set T := Icc a b ∩ P ⁻¹' (ball w r)ᶜ with hT
  have hTc : IsClosed T := hPc.preimage_isClosed_of_isClosed isClosed_Icc isOpen_ball.isClosed_compl
  have hTne : T.Nonempty := ⟨b, ⟨hab, le_rfl⟩, hPb⟩
  have hTb : BddBelow T := ⟨a, fun u hu => hu.1.1⟩
  set t := sInf T with ht
  have htT : t ∈ T := hTc.csInf_mem hTne hTb
  have hat : a < t := by
    rcases eq_or_lt_of_le htT.1.1 with h | h
    · exact absurd (h ▸ hPa : P t ∈ ball w (r / 2)) fun h' =>
        htT.2 (ball_subset_ball (by linarith) h')
    · exact h
  have hbefore : ∀ u ∈ Ico a t, P u ∈ ball w r := fun u hu => by
    by_contra hn
    exact absurd (csInf_le hTb ⟨⟨hu.1, by linarith [hu.2, htT.1.2]⟩, hn⟩) (not_le.2 hu.2)
  have hPt_cl : P t ∈ closedBall w r := by
    have hS : IsClosed (Icc a t ∩ P ⁻¹' closedBall w r) :=
      (hPc.mono (Icc_subset_Icc le_rfl htT.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_closedBall
    have hsub : Icc a t ⊆ Icc a t ∩ P ⁻¹' closedBall w r := by
      have := closure_minimal (s := Ico a t) (t := Icc a t ∩ P ⁻¹' closedBall w r) (fun u hu => ⟨Ico_subset_Icc_self hu,
        ball_subset_closedBall (hbefore u hu)⟩) hS
      rwa [closure_Ico hat.ne] at this
    exact (hsub ⟨hat.le, le_rfl⟩).2
  have hPt : P t ∈ sphere w r := by
    have h1 := mem_closedBall.1 hPt_cl
    have h2 : ¬ dist (P t) w < r := htT.2
    exact mem_sphere.2 (le_antisymm h1 (not_lt.1 h2))
  -- the last visit `s` of `cl B_{αr}(w)` before `t`
  have hαr : α * r < r := by nlinarith
  have hr2 : r / 2 < α * r := by nlinarith
  set S := Icc a t ∩ P ⁻¹' closedBall w (α * r) with hSdef
  have hSc : IsClosed S :=
    (hPc.mono (Icc_subset_Icc le_rfl htT.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_closedBall
  have hSne : S.Nonempty := ⟨a, ⟨le_rfl, hat.le⟩, ball_subset_closedBall
    (ball_subset_ball hr2.le hPa)⟩
  have hSb : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  set s := sSup S with hs
  have hsS : s ∈ S := hSc.csSup_mem hSne hSb
  have hst : s < t := by
    rcases eq_or_lt_of_le hsS.1.2 with h | h
    · have := mem_closedBall.1 hsS.2
      rw [h, mem_sphere.1 hPt] at this
      linarith
    · exact h
  have has : a ≤ s := le_csSup hSb ⟨⟨le_rfl, hat.le⟩, ball_subset_closedBall
    (ball_subset_ball hr2.le hPa)⟩
  have hafter : ∀ u ∈ Ioc s t, P u ∉ closedBall w (α * r) := fun u hu hn =>
    absurd (le_csSup hSb ⟨⟨by linarith [hu.1], hu.2⟩, hn⟩) (not_le.2 hu.1)
  have hPs_out : P s ∉ ball w (α * r) := by
    have hS' : IsClosed (Icc s t ∩ P ⁻¹' (ball w (α * r))ᶜ) :=
      (hPc.mono (Icc_subset_Icc has htT.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
        isOpen_ball.isClosed_compl
    have hsub : Icc s t ⊆ Icc s t ∩ P ⁻¹' (ball w (α * r))ᶜ := by
      have := closure_minimal (s := Ioc s t) (t := Icc s t ∩ P ⁻¹' (ball w (α * r))ᶜ) (fun u hu => ⟨Ioc_subset_Icc_self hu,
        fun h' => hafter u hu (ball_subset_closedBall h')⟩) hS'
      rwa [closure_Ioc hst.ne] at this
    exact (hsub ⟨le_rfl, hst.le⟩).2
  have hPs : P s ∈ sphere w (α * r) :=
    mem_sphere.2 (le_antisymm (mem_closedBall.1 hsS.2) (not_lt.1 hPs_out))
  -- (3.16)
  obtain ⟨a', b', G, hGd, hGl⟩ := hround
  have h316 := gm_S3_8 D hP hgeo (by linarith) hα1.le hA hGd hGl ha0 has hst.le
    (htT.1.2.trans hbL) h0 (ball_subset_closedBall (ball_subset_ball hr2.le hPa)) hPs hPt hL
  -- (3.14)
  have hann : ∀ u ∈ Icc s t, P u ∈ closedBall w r ∧ P u ∉ ball w (α * r) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h]; exact ⟨hbefore s ⟨has, hst⟩ |> ball_subset_closedBall, hPs_out⟩
    · refine ⟨?_, fun h' => hafter u ⟨h, hu.2⟩ (ball_subset_closedBall h')⟩
      rcases eq_or_lt_of_le hu.2 with h2 | h2
      · rw [h2]; exact hPt_cl
      · exact ball_subset_closedBall (hbefore u ⟨by linarith, h2⟩)
  have hc1 := hcomp s t (ha0.trans has) hst.le (htT.1.2.trans hbL) hPs hPt hann
  have hc2 : D'.1 (P a, P s) ≤ Cs * (s - a) := by
    rw [← abs_of_nonneg (by linarith : 0 ≤ s - a), ← hgeo a ⟨ha0, by linarith [htT.1.2]⟩ s
      ⟨by linarith, by linarith [htT.1.2]⟩]
    exact hratio _ _
  refine ⟨t, ⟨hat, htT.1.2⟩, ?_, ?_⟩
  · have h1 := mem_sphere.1 hPt
    have h2 := mem_ball.1 hPa
    rw [dist_eq_norm] at h1 h2
    have := norm_sub_norm_le (P t - w) (P a - w)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  · have htri := D'.2.triangle (P a) (P s) (P t)
    have hA1 : 0 < A + 1 := by linarith
    have key : (A + 1) * (s - a) ≤ A * (t - a) := by nlinarith
    have hfrac : s - a ≤ A / (A + 1) * (t - a) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hA1]; linarith
    nlinarith

/-- **GM (3.17)** (l. 1480–1488), deterministic form: along a `D`-geodesic `P`, if every
`P(a)`, `a ∈ [a₀, b₀]`, lies in `B_{r/2}(w)` for a good ball (radius `≥ r_min`, with a short
disconnecting loop and the comparison (3.14)) not containing `P(0)`, `P(L)`, then
`D̃(P(a₀), P(b₀)) ≤ (C' + A/(A+1)(C_* − C'))(b₀ − a₀) + C_* ω`, where `ω` bounds `b₀ − a` whenever
`P(b₀)` already lies in the good ball of `P(a)`. -/
theorem tele_core (hP : ContinuousOn P (Icc 0 L))
    (hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s|)
    {α A Cs C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hC0 : 0 ≤ C')
    (hCC : C' ≤ Cs) (hratio : ∀ x y, D'.1 (x, y) ≤ Cs * D.1 (x, y))
    (Good : ℂ → ℝ → Prop) {rmin : ℝ} (hrmin : 0 < rmin) (hgr : ∀ w r, Good w r → rmin ≤ r)
    (hround : ∀ w r, Good w r → ∃ (a' b' : ℝ) (G : ℝ → ℂ),
      Disconnects (G '' Icc a' b') (sphere w (α * r)) (sphere w r) ∧
      D.len G a' b' ≤ ENNReal.ofReal A * setDist D (sphere w (α * r)) (sphere w r))
    (hcomp : ∀ w r, Good w r → ∀ s t, 0 ≤ s → s ≤ t → t ≤ L → P s ∈ sphere w (α * r) →
      P t ∈ sphere w r → (∀ u ∈ Icc s t, P u ∈ closedBall w r ∧ P u ∉ ball w (α * r)) →
      D'.1 (P s, P t) ≤ C' * (t - s))
    {a₀ b₀ ω : ℝ} (ha₀ : 0 ≤ a₀) (hab : a₀ ≤ b₀) (hbL : b₀ ≤ L) (hω : 0 ≤ ω)
    (hcov : ∀ a ∈ Icc a₀ b₀, ∃ w r, Good w r ∧ P a ∈ ball w (r / 2))
    (hfar : ∀ a ∈ Icc a₀ b₀, ∀ w r, Good w r → P a ∈ ball w (r / 2) →
      P 0 ∉ ball w r ∧ P L ∉ ball w r)
    (hnear : ∀ a ∈ Icc a₀ b₀, ∀ w r, Good w r → P a ∈ ball w (r / 2) → P b₀ ∈ ball w r →
      b₀ - a ≤ ω) :
    D'.1 (P a₀, P b₀) ≤ (C' + A / (A + 1) * (Cs - C')) * (b₀ - a₀) + Cs * ω := by
  set K := C' + A / (A + 1) * (Cs - C') with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ A / (A + 1) := div_nonneg hA (by linarith)
    nlinarith
  have hCs0 : 0 ≤ Cs := hC0.trans hCC
  -- uniform continuity of `P` on `[0, L]`
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hP) (rmin / 2) (by linarith)
  have main : ∀ n : ℕ, ∀ a ∈ Icc a₀ b₀, b₀ - a ≤ n * δ₀ →
      D'.1 (P a, P b₀) ≤ K * (b₀ - a) + Cs * ω := by
    intro n
    induction n with
    | zero =>
      intro a ha hn
      have : a = b₀ := le_antisymm ha.2 (by simp at hn; linarith)
      rw [this, D'.2.self_eq_zero]
      nlinarith
    | succ n ih =>
      intro a ha hn
      obtain ⟨w, r, hg, hPa⟩ := hcov a ha
      have hr : 0 < r := hrmin.trans_le (hgr w r hg)
      by_cases hb : P b₀ ∈ ball w r
      · have h1 := hnear a ha w r hg hPa hb
        have h2 : D'.1 (P a, P b₀) ≤ Cs * (b₀ - a) := by
          rw [← abs_of_nonneg (by linarith [ha.2] : 0 ≤ b₀ - a), ← hgeo a
            ⟨ha₀.trans ha.1, by linarith [ha.2]⟩ b₀ ⟨by linarith, hbL⟩]
          exact hratio _ _
        have : 0 ≤ K * (b₀ - a) := mul_nonneg hK0 (by linarith [ha.2])
        nlinarith
      · obtain ⟨h0, hL⟩ := hfar a ha w r hg hPa
        obtain ⟨t, ht, hdist, hstep⟩ := tele_step D D' hP hgeo hα hα1 hA hCC hratio hr
          (hround w r hg) (hcomp w r hg) (ha₀.trans ha.1) ha.2 hbL hPa hb h0 hL
        have htδ : δ₀ ≤ t - a := by
          by_contra hlt
          push Not at hlt
          have := hδ t ⟨by linarith [ha.1, ht.1], by linarith [ht.2]⟩ a
            ⟨ha₀.trans ha.1, by linarith [ha.2]⟩ (by
              rw [Real.dist_eq, abs_of_pos (by linarith [ht.1])]; exact hlt)
          rw [dist_eq_norm] at this
          linarith [hgr w r hg]
        have hIH := ih t ⟨by linarith [ha.1, ht.1], ht.2⟩ (by push_cast at hn; nlinarith)
        have htri := D'.2.triangle (P a) (P t) (P b₀)
        nlinarith
  obtain ⟨n, hn⟩ := exists_nat_ge ((b₀ - a₀) / δ₀)
  exact main n a₀ ⟨le_rfl, hab⟩ (by rwa [div_le_iff₀ hδ₀] at hn)

end Tele

end LQGMetric.GM
