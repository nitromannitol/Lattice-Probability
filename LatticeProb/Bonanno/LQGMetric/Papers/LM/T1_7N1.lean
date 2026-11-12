/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7N1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7D1
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC

/-!
# LM Theorem 1.7, packet P-NEAR (DEC-107 §2, §3(ii)–(iii)): deterministic bounds

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7, Step 2 (l. 1030–1055) and Step 3
(l. 1075–1081), as repaired by decision D107 (`decisions/DEC-107.md` §2, §3(ii)–(iii)).

* `t17_replace` (LM l. 1079–1080, the replacement argument: "by replacing the segment of `P`
  between the first and last points of `cl S` hit by `P`, we could find a path from `z` to `w` of
  `D`-length smaller"): for a path `P` in `Y` and `s ≤ u`,
  `len(P|[s,u]) + D(P 0, P 1; Y) ≤ len(P) + D(P s, P u; Y)` (triangle inequality of the internal
  metric; no near-geodesic of `D(·,·;Y)` is needed).
* `t17_local_modulus` (DEC-107 §2): for a length metric `D` and `R < R'` there is, for every
  `κ > 0`, an `r > 0` with `D(a, b; B_{R'}) ≤ κ` whenever `‖a‖ ≤ R`, `‖a − b‖ < r` (locality
  `internalEDist_eq_edist_of_ball_subset` with the positive `D`-distance from `cl B_R` to
  `∂B_{R'}`, and uniform continuity of `D` on `cl B_{R'}²`). This is `ω_n(ε√2) → 0`.
* `t17_near_bound` (DEC-107 §3(iii)): for a path `P ⊂ cl B_R` with
  `len(P; D) ≤ D(z,w;B_R) + ε'`, every sub-path between times `s ≤ u` with `‖P s − P u‖ < r`
  has `len(P|[s,u]) + D(z,w;B_{R'}) ≤ D(z,w;B_R) + ε' + κ`, i.e.
  `len(P|[s,u]) ≤ η + ε' + κ` with `η = D(z,w;B_R) − D(z,w;B_{R'})`. Since `len(P∩S;D)` is
  at most the length of `P` between its first and last hits of `cl S` (`t17_first_last_hit`), this
  is the bound `sup_S len(P∩S;D) ≤ η_n + ε³ + ω_n(ε√2)` of DEC-107 §2 (sharper than the stated
  `η_n + 2ε³ + ω_n(ε√2) + 2δ`: the triangle inequality replaces the auxiliary near-geodesic).
* `t17_sum_replace` (LM (5.12)–(5.16), l. 1042–1055): if the lengths `ℓ'` of the pieces of a path
  for `D^S` agree with the `D`-lengths `ℓ` except on `S`, where `ℓ'_S ≤ C² ℓ_S`, then
  `∑ ℓ' ≤ ∑ ℓ + (C² − 1) ℓ_S`; with `t17_posPart_le` this gives `A(S) ≤ b₁(S)` and
  `A(S) ≤ b₂(S)` (`t17_A_le_b1`, `t17_A_le_b2`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open MetricGeometry

/-! ## The replacement argument -/

/-- **LM l. 1079–1080** (replacement of the segment `P|[s,u]`): `len(P|[s,u]) + D(P 0, P 1; Y) ≤
len(P|[a,b]) + D(P s, P u; Y)` for a curve `P` in `Y`. -/
theorem t17_replace {X : Type*} [PseudoEMetricSpace X] {Y : Set X} {P : ℝ → X} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) (hY : MapsTo P (Icc a b) Y) {s u : ℝ} (hs : a ≤ s)
    (hsu : s ≤ u) (hu : u ≤ b) :
    curveLength P s u + internalEDist Y (P a) (P b) ≤
      curveLength P a b + internalEDist Y (P s) (P u) := by
  have h1 : internalEDist Y (P a) (P s) ≤ curveLength P a s :=
    internalEDist_le_curveLength hs (hP.mono (Icc_subset_Icc le_rfl (hsu.trans hu)))
      (hY.mono_left (Icc_subset_Icc le_rfl (hsu.trans hu)))
  have h2 : internalEDist Y (P u) (P b) ≤ curveLength P u b :=
    internalEDist_le_curveLength hu (hP.mono (Icc_subset_Icc (hs.trans hsu) le_rfl))
      (hY.mono_left (Icc_subset_Icc (hs.trans hsu) le_rfl))
  have htri : internalEDist Y (P a) (P b) ≤
      curveLength P a s + internalEDist Y (P s) (P u) + curveLength P u b :=
    (internalEDist_triangle Y _ (P u) _).trans (add_le_add ((internalEDist_triangle Y _ (P s) _).trans
      (add_le_add h1 le_rfl)) h2)
  have hadd : curveLength P a b = curveLength P a s + curveLength P s u + curveLength P u b := by
    rw [curveLength_add P hs hsu, curveLength_add P (hs.trans hsu) hu]
  calc curveLength P s u + internalEDist Y (P a) (P b)
      ≤ curveLength P s u + (curveLength P a s + internalEDist Y (P s) (P u) +
          curveLength P u b) := add_le_add le_rfl htri
    _ = curveLength P a b + internalEDist Y (P s) (P u) := by rw [hadd]; ring

/-! ## Locality and the modulus `ω_n` -/

/-- **DEC-107 §2**: for a length metric `D` and `0 ≤ R < R'`, for every `κ > 0` there is `r > 0`
such that `D(a, b; B_{R'}(0)) ≤ κ` whenever `‖a‖ ≤ R` and `‖a − b‖ < r`. -/
theorem t17_local_modulus {d : ContMetric} (hd : d.IsLength) {R R' : ℝ} (hRR' : R < R')
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ r > 0, ∀ a b : ℂ, ‖a‖ ≤ R → ‖a - b‖ < r →
      d.internal (Metric.ball 0 R') a b ≤ ENNReal.ofReal κ := by
  by_cases hR : R < 0
  · exact ⟨1, one_pos, fun a b ha _ => absurd (ha.trans_lt hR) (not_lt.2 (norm_nonneg a))⟩
  have hne : (Metric.closedBall (0 : ℂ) R).Nonempty := ⟨0, Metric.mem_closedBall_self (not_lt.1 hR)⟩
  -- positive `D`-distance from `cl B_R` to the complement of `B_{R'}`
  set Z : Set d.Space := (d.pt '' Metric.ball (0 : ℂ) R')ᶜ with hZ
  have hZc : IsClosed Z := (d.isOpen_image_pt Metric.isOpen_ball).isClosed_compl
  have hpos : ∀ a ∈ Metric.closedBall (0 : ℂ) R, 0 < Metric.infEDist (d.pt a) Z := by
    intro a ha
    rw [Metric.infEDist_pos_iff_notMem_closure, hZc.closure_eq, hZ, notMem_compl_iff]
    exact d.mem_image_pt.2 (Metric.mem_ball.2 (by
      simpa using (Metric.mem_closedBall.1 ha).trans_lt hRR'))
  have hcont : ContinuousOn (fun a => Metric.infEDist (d.pt a) Z) (Metric.closedBall 0 R) :=
    (Metric.continuous_infEDist.comp d.continuous_pt).continuousOn
  obtain ⟨a₀, ha₀, hmin⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMinOn hne hcont
  obtain ⟨ρ, -, hρ0, hρ⟩ := ENNReal.lt_iff_exists_real_btwn.1 (hpos a₀ ha₀)
  have hρpos : 0 < ρ := ENNReal.ofReal_pos.1 hρ0
  -- uniform continuity of `D` on `cl B_{R'} × cl B_{R'}`
  have huc := ((isCompact_closedBall (0 : ℂ) R').prod
    (isCompact_closedBall (0 : ℂ) R')).uniformContinuousOn_of_continuous d.1.continuous.continuousOn
  obtain ⟨δ, hδ, hδd⟩ := Metric.uniformContinuousOn_iff.1 huc (min κ ρ) (lt_min hκ hρpos)
  refine ⟨min δ (R' - R), lt_min hδ (by linarith), fun a b ha hab => ?_⟩
  have hab' : ‖a - b‖ < R' - R := hab.trans_le (min_le_right _ _)
  have haR : ‖a‖ ≤ R' := by linarith
  have hbR : ‖b‖ ≤ R' := by
    have := norm_sub_norm_le b a
    rw [norm_sub_rev] at this
    linarith
  have hdab : d.1 (a, b) < min κ ρ := by
    have h := hδd (a, a) ⟨by simpa using haR, by simpa using haR⟩ (a, b)
      ⟨by simpa using haR, by simpa using hbR⟩ (by
        rw [Prod.dist_eq, dist_self, dist_eq_norm]
        exact (max_eq_right (norm_nonneg _)).trans_lt (hab.trans_le (min_le_left _ _)))
    rwa [d.2.self_eq_zero a, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg (ContMetric.nonneg d a b)] at h
  have hball : Metric.eball (d.pt a) (ENNReal.ofReal ρ) ⊆ d.pt '' Metric.ball 0 R' := by
    intro x hx
    by_contra hxn
    have h1 : Metric.infEDist (d.pt a) Z ≤ edist (d.pt a) x := Metric.infEDist_le_edist_of_mem hxn
    have h2 : Metric.infEDist (d.pt a₀) Z ≤ Metric.infEDist (d.pt a) Z :=
      hmin (Metric.mem_closedBall.2 (by simpa using ha))
    have h3 : edist x (d.pt a) < ENNReal.ofReal ρ := Metric.mem_eball.1 hx
    rw [edist_comm] at h3
    exact absurd (hρ.trans_le (h2.trans h1)) (not_lt.2 h3.le)
  have hxy : edist (d.pt a) (d.pt b) < ENNReal.ofReal ρ := by
    rw [ContMetric.edist_pt]
    exact (ENNReal.ofReal_lt_ofReal_iff hρpos).2 (hdab.trans_le (min_le_right _ _))
  unfold ContMetric.internal
  rw [internalEDist_eq_edist_of_ball_subset hd hball hxy, ContMetric.edist_pt]
  exact ENNReal.ofReal_le_ofReal (hdab.le.trans (min_le_left _ _))

/-- **DEC-107 §2, §3(iii)** (LM l. 1079–1081, repaired): for a length metric `D` and `R < R'`,
for every `κ > 0` there is `r > 0` (depending only on `D, R, R', κ`) such that for every curve `P`
on `[a,b]` in `cl B_R(0)` with `len(P; D) ≤ D(P a, P b; B_R) + ε'` and all `a ≤ s ≤ u ≤ b` with
`‖P s − P u‖ < r`: `len(P|[s,u]; D) + D(P a, P b; B_{R'}) ≤ D(P a, P b; B_R) + ε' + κ`. -/
theorem t17_near_bound {d : ContMetric} (hd : d.IsLength) {R R' : ℝ} (hRR' : R < R') {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ r > 0, ∀ (a b : ℝ) (P : ℝ → ℂ), ContinuousOn P (Icc a b) →
      MapsTo P (Icc a b) (Metric.closedBall 0 R) →
      ∀ ε' : ℝ≥0∞, d.len P a b ≤ d.internal (Metric.ball 0 R) (P a) (P b) + ε' →
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ b → ‖P s - P u‖ < r →
        d.len P s u + d.internal (Metric.ball 0 R') (P a) (P b) ≤
          d.internal (Metric.ball 0 R) (P a) (P b) + ε' + ENNReal.ofReal κ := by
  obtain ⟨r, hr, hmod⟩ := t17_local_modulus hd hRR' hκ
  refine ⟨r, hr, fun a b P hP hPm ε' hnear s u hs hsu hu hsu' => ?_⟩
  have hY : MapsTo (d.pt ∘ P) (Icc a b) (d.pt '' Metric.ball 0 R') := fun t ht =>
    ⟨P t, Metric.mem_ball.2 ((Metric.mem_closedBall.1 (hPm ht)).trans_lt hRR'), rfl⟩
  have h := t17_replace (X := d.Space) (P := d.pt ∘ P) (d.continuous_pt.comp_continuousOn hP) hY
    hs hsu hu
  have hPs : ‖P s‖ ≤ R := by simpa using Metric.mem_closedBall.1 (hPm ⟨hs, hsu.trans hu⟩)
  have hm := hmod (P s) (P u) hPs hsu'
  calc d.len P s u + d.internal (Metric.ball 0 R') (P a) (P b)
      ≤ d.len P a b + d.internal (Metric.ball 0 R') (P s) (P u) := h
    _ ≤ d.internal (Metric.ball 0 R) (P a) (P b) + ε' + ENNReal.ofReal κ := add_le_add hnear hm

/-- first and last hits of a closed set `K` by a curve on `[0,1]` -/
theorem t17_first_last_hit {P : ℝ → ℂ} {a b : ℝ} (hP : ContinuousOn P (Icc a b)) {K : Set ℂ}
    (hK : IsClosed K) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hPt₀ : P t₀ ∈ K) :
    ∃ s u : ℝ, a ≤ s ∧ s ≤ u ∧ u ≤ b ∧ P s ∈ K ∧ P u ∈ K ∧
      ∀ t ∈ Icc a b, P t ∈ K → s ≤ t ∧ t ≤ u := by
  have hT : IsClosed (Icc a b ∩ P ⁻¹' K) := hP.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hc : IsCompact (Icc a b ∩ P ⁻¹' K) := isCompact_Icc.of_isClosed_subset hT
    inter_subset_left
  have hn : (Icc a b ∩ P ⁻¹' K).Nonempty := ⟨t₀, ht₀, hPt₀⟩
  obtain ⟨hs1, hs2⟩ := hc.sInf_mem hn
  obtain ⟨hu1, hu2⟩ := hc.sSup_mem hn
  refine ⟨_, _, hs1.1, csInf_le_csSup hn hc.bddBelow hc.bddAbove, hu1.2, hs2, hu2,
    fun t ht hPt => ⟨csInf_le hc.bddBelow ⟨ht, hPt⟩, le_csSup hc.bddAbove ⟨ht, hPt⟩⟩⟩

/-! ## LM (5.12)–(5.16): the resampled length -/

/-- **LM (5.12)–(5.16)**, the sum step: `∑ ℓ' ≤ ∑ ℓ + (c − 1) ℓ_S` if `ℓ' = ℓ` off `S` and
`ℓ'_S ≤ c ℓ_S`. -/
theorem t17_sum_replace {ι : Type*} [DecidableEq ι] (s : Finset ι) {S : ι} (hS : S ∈ s)
    (ℓ ℓ' : ι → ℝ) {c : ℝ} (hne : ∀ i ∈ s, i ≠ S → ℓ' i = ℓ i) (hSl : ℓ' S ≤ c * ℓ S) :
    ∑ i ∈ s, ℓ' i ≤ ∑ i ∈ s, ℓ i + (c - 1) * ℓ S := by
  rw [← Finset.add_sum_erase s ℓ' hS, ← Finset.add_sum_erase s ℓ hS,
    Finset.sum_congr rfl fun i hi => hne i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)]
  linarith

/-- **LM (5.16)** in the form of DEC-107 §3(ii)–(iii): with `D^S(z,w;B_n) ≤ len(P; D^S) = ∑ ℓ'`,
`len(P; D) = ∑ ℓ ≤ G + e` (`G = D(z,w;B_{n−1})` for `P`, giving `b₁`; `G = D(z,w;B_n)` for `P'`,
giving `b₂`) and `F = D(z,w;B_n)`: `A(S) = (D^S(z,w;B_n) − F)_+ ≤ G − F + e + (c − 1) ℓ_S`. -/
theorem t17_A_le_b {ι : Type*} [DecidableEq ι] (s : Finset ι) {S : ι} (hS : S ∈ s)
    (ℓ ℓ' : ι → ℝ) {c DS F G e : ℝ} (hne : ∀ i ∈ s, i ≠ S → ℓ' i = ℓ i) (hSl : ℓ' S ≤ c * ℓ S)
    (hDS : DS ≤ ∑ i ∈ s, ℓ' i) (hlen : ∑ i ∈ s, ℓ i ≤ G + e)
    (hb : 0 ≤ G - F + e + (c - 1) * ℓ S) :
    max (DS - F) 0 ≤ G - F + e + (c - 1) * ℓ S :=
  t17_posPart_le (by linarith [t17_sum_replace s hS ℓ ℓ' hne hSl]) hb

end LQGMetric.LM
