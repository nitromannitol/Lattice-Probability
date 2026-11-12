/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L214P2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G2
import LatticeProb.Bonanno.LQGMetric.Topo.ArcDisconnectMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF (3.21)–(3.21′) at a fixed `ω` (decision D120 §2.2, packet J2)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1576–1590: on condition 1 of `𝓔_𝕣(a)` (`B_{a𝕣}(z₀) ⊆ 𝓑^•_s`) and `𝓑^•_s ⊆ B_{3𝕣}(z₀)`,
Lemma 2.15 (`confL215_filledBall`, S3L214P2) with `r₁ = a𝕣`, `r₂ = 3𝕣`, `C = ε𝕣 n^{1/2}/2`
gives at most `324 A a⁻² ε⁻² + N₀ ≤ 324 A a⁻² n^{1/2} + N₀ ≤ n/4` bad arcs (`ε ≥ n^{-1/4}`,
(3.19), `t39gExp_bounds`), for `n ≥ N₁(a)`; the disconnecting set of diameter `≤ ε𝕣/2` is
replaced by an open ball `B_ρ(x)`, `x ∈ ∂𝓑^•_s`, `ρ = 3ε𝕣/4 < ε𝕣` (`exists_frontier_ball_disconnects`).

* **`t39j_badArcs_le`**: DEC-120 §2.2.
-/

noncomputable section

open MeasureTheory Set Metric Filter Function
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

open Classical in
/-- **(3.21′), core count** (C:1576–1590): for `n ≥ N₁` at most `n/4` of the nonempty `J i` are
not disconnected from `∞` by a bounded set of diameter `≤ ε𝕣/2` (Lemma 2.15; `N₁ ≥ 16`, so that
`ε = 2^{-t39gExp n} ≤ 1/2`). -/
theorem t39j_badY_le {a : ℝ} (ha : 0 < a) : ∃ N₁ : ℕ, 16 ≤ N₁ ∧
    ∀ {D : ContMetric} {z₀ : ℂ} {R s : ℝ}, 0 < R → 0 < s → D.IsLength →
      Bornology.IsBounded (ballM D z₀ s) → ball z₀ (a * R) ⊆ filledBall D z₀ s →
      filledBall D z₀ s ⊆ ball z₀ (3 * R) →
      ∀ {ι : Type} [Fintype ι] (J : ι → Set ℂ), (∀ i, J i ⊆ frontier (filledBall D z₀ s)) →
        (∀ i, (J i).Nonempty → IsPreconnected (J i)) → Pairwise (Disjoint on J) →
        N₁ ≤ (Finset.univ.filter fun i => (J i).Nonempty).card →
        4 * (Finset.univ.filter fun i => (J i).Nonempty ∧ ¬ ∃ Y : Set ℂ, Bornology.IsBounded Y ∧
            Metric.diam Y ≤ (2 : ℝ)⁻¹ ^ t39gExp (Finset.univ.filter fun i =>
              (J i).Nonempty).card * R / 2 ∧
            DisconnectsFromInfty (filledBall D z₀ s) Y (J i)).card ≤
          (Finset.univ.filter fun i => (J i).Nonempty).card := by
  obtain ⟨A, N₀, hA, hN₀, hL215⟩ := confL215_filledBall
  set M : ℝ := 1296 * A / a ^ 2 + 4 * N₀ + 1 with hM
  have hM1 : 1 ≤ M := by have : 0 ≤ 1296 * A / a ^ 2 := by positivity
                         linarith
  refine ⟨max (⌈M ^ 2⌉₊ + 1) 16, le_max_right _ _, ?_⟩
  intro D z₀ R s hR hs hL hbd hK1 hK2 ι _ J hJf hJc hJd hN
  set K := filledBall D z₀ s with hK
  set S := Finset.univ.filter fun i => (J i).Nonempty with hS
  set m : ℕ := S.card with hm
  set n : ℝ := (m : ℝ) with hn
  have hN' := (le_max_left (⌈M ^ 2⌉₊ + 1) 16).trans hN
  have hm1 : 1 ≤ m := by omega
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hm1
  have hn0 : 0 < n := by linarith
  set ε : ℝ := (2 : ℝ)⁻¹ ^ t39gExp m with hε
  obtain ⟨hεw, -⟩ := t39gExp_bounds hm1
  rw [← hn, ← hε] at hεw
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  clear_value ε
  -- `p = n^{1/2}`, `q = n^{-1/2} = p⁻¹`, `w = n^{-1/4}`, `w² = q`
  set p : ℝ := Real.sqrt n with hp
  have hp0 : 0 < p := Real.sqrt_pos.2 hn0
  have hpp : p * p = n := Real.mul_self_sqrt hn0.le
  set q : ℝ := n ^ (-(1 / 2 : ℝ)) with hq
  have hqp : q = p⁻¹ := by rw [hq, Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow]
  set w : ℝ := n ^ (-(1 / 4 : ℝ)) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hn0 _
  have hwq : w ^ 2 = q := by
    rw [hw, hq, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hεq : q ≤ ε ^ 2 := by rw [← hwq]; exact pow_le_pow_left₀ hw0.le hεw 2
  have hq0 : 0 < q := by rw [hqp]; positivity
  -- Lemma 2.15 with `C = ε R / (2 q)`
  set C : ℝ := ε * R / (2 * q) with hC
  have hC0 : 0 < C := by positivity
  have hCq : C * q = ε * R / 2 := by rw [hC]; field_simp
  have hCr : C * (S.card : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 * R := by
    rw [← hm, ← hn, ← hq, hCq]; nlinarith
  have hpc : ∀ i ∈ S, IsPreconnected (J i) := fun i hi => hJc i (Finset.mem_filter.1 hi).2
  have hdS : (S : Set ι).PairwiseDisjoint J := fun i _ j _ hij => hJd hij
  set PY : ι → Prop := fun i => ∃ Y : Set ℂ, Bornology.IsBounded Y ∧
    Metric.diam Y ≤ ε * R / 2 ∧ DisconnectsFromInfty K Y (J i) with hPY
  set G := S.filter PY with hG
  set NG := S.filter fun i => ¬ PY i with hNG
  set B := Finset.univ.filter fun i => (J i).Nonempty ∧ ¬ PY i with hB
  set T : ℝ := A * (3 * R) ^ 4 / ((a * R) ^ 2 * C ^ 2) with hTdef
  have hgood : (1 - T) * n - N₀ ≤ (G.card : ℝ) := by
    have h := hL215 hs hL hbd (by positivity) hK1 hK2 S J (fun i _ => hJf i)
      (fun i hi => (Finset.mem_filter.1 hi).2) hpc hdS C hC0 hCr
    rw [← hm, ← hn, ← hq, hCq] at h
    exact h
  have hbad : B ⊆ NG := fun i hi => Finset.mem_filter.2
    ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2.1⟩,
      (Finset.mem_filter.1 hi).2.2⟩
  have hsplit : (G.card : ℝ) + (NG.card : ℝ) = n := by
    rw [hn, hm]; exact_mod_cast Finset.card_filter_add_card_filter_not _
  have hb : (B.card : ℝ) ≤ NG.card := by exact_mod_cast Finset.card_le_card hbad
  -- `A r₂⁴/(r₁² C²) · n ≤ 324 A a⁻² p`
  have hT : T * n ≤ 324 * A / a ^ 2 * p := by
    have e : T * n = 324 * A / a ^ 2 * (q ^ 2 / ε ^ 2) * n := by
      rw [hTdef, hC]; field_simp; ring
    have hqn : q * n = p := by rw [hqp, ← hpp]; field_simp
    rw [e]
    have h1 : q ^ 2 / ε ^ 2 ≤ q := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc 324 * A / a ^ 2 * (q ^ 2 / ε ^ 2) * n ≤ 324 * A / a ^ 2 * q * n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hn0.le
      _ = 324 * A / a ^ 2 * p := by rw [mul_assoc, hqn]
  -- `p ≥ M`
  have hpM : M ≤ p := by
    have h1 : M ^ 2 ≤ n := by
      have : (⌈M ^ 2⌉₊ : ℝ) ≤ n := by rw [hn]; exact_mod_cast (by omega : ⌈M ^ 2⌉₊ ≤ m)
      exact (Nat.le_ceil _).trans this
    rw [hp]; exact Real.le_sqrt_of_sq_le h1
  have hfinal : 4 * (324 * A / a ^ 2 * p + N₀) ≤ n := by
    rw [← hpp]
    have e1 : M * p = 1296 * A / a ^ 2 * p + 4 * N₀ * p + p := by rw [hM]; ring
    have h1 : M * p ≤ p * p := mul_le_mul_of_nonneg_right hpM hp0.le
    have h2 : 4 * N₀ * 1 ≤ 4 * N₀ * p :=
      mul_le_mul_of_nonneg_left (hM1.trans hpM) (by positivity)
    have e2 : 4 * (324 * A / a ^ 2 * p + N₀) = 1296 * A / a ^ 2 * p + 4 * N₀ * 1 := by ring
    linarith
  have hTn : (1 - T) * n = n - T * n := by ring
  have : ((4 * B.card : ℕ) : ℝ) ≤ (m : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-! ## The centres `x_{k,i}` and the events `Act k i` (C:1467, 1586) -/

/-- the lexicographically smallest point (`re`, then `im`) of a set; a deterministic selection,
measurable in the hit σ-algebra for random compact sets (the construction of
`GM.p412f_meas_select`) -/
def t39jLexMin (F : Set ℂ) : ℂ :=
  ⟨sInf (Complex.re '' F), sInf (Complex.im '' (F ∩ {z | z.re = sInf (Complex.re '' F)}))⟩

theorem t39jLexMin_mem {F : Set ℂ} (hF : IsCompact F) (hne : F.Nonempty) : t39jLexMin F ∈ F := by
  have h1 : sInf (Complex.re '' F) ∈ Complex.re '' F :=
    (hF.image Complex.continuous_re).sInf_mem (hne.image _)
  have hF₁c : IsCompact (F ∩ {z | z.re = sInf (Complex.re '' F)}) :=
    hF.inter_right (isClosed_eq Complex.continuous_re continuous_const)
  have hF₁n : (F ∩ {z | z.re = sInf (Complex.re '' F)}).Nonempty := by
    obtain ⟨z, hz, hzr⟩ := h1; exact ⟨z, hz, hzr⟩
  obtain ⟨z, ⟨hzF, hzr⟩, hzi⟩ := (hF₁c.image Complex.continuous_im).sInf_mem (hF₁n.image _)
  have : t39jLexMin F = z := Complex.ext hzr.symm hzi.symm
  rw [this]; exact hzF

/-- closure of the centres `c ∈ ∂K` with `B̄_r(c)` disconnecting `J` from `∞` in `ℂ ∖ K` -/
def t39jCtrSet (K J : Set ℂ) (r : ℝ) : Set ℂ :=
  closure {c | c ∈ frontier K ∧ DisconnectsFromInfty K (closedBall c r) J}

open Classical in
/-- **the centre `x_{k,i}`** (C:1586): the lexicographically smallest point of `t39jCtrSet`, or
of `∂K` if there is none -/
def t39jCtr (K J : Set ℂ) (r : ℝ) : ℂ :=
  t39jLexMin (if (t39jCtrSet K J r).Nonempty then t39jCtrSet K J r else frontier K)

theorem t39jCtrSet_subset (K J : Set ℂ) (r : ℝ) : t39jCtrSet K J r ⊆ frontier K :=
  closure_minimal (fun _ hc => hc.1) isClosed_frontier

theorem t39j_isCompact_frontier {K : Set ℂ} (hKb : Bornology.IsBounded K) :
    IsCompact (frontier K) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hKb.closure.subset frontier_subset_closure)

theorem t39j_isCompact_ctrSet {K : Set ℂ} (hKb : Bornology.IsBounded K) (J : Set ℂ) (r : ℝ) :
    IsCompact (t39jCtrSet K J r) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure
    ((t39j_isCompact_frontier hKb).isBounded.subset (t39jCtrSet_subset K J r))

theorem t39jCtr_mem {K : Set ℂ} (hKb : Bornology.IsBounded K) (hne : (frontier K).Nonempty)
    (J : Set ℂ) (r : ℝ) : t39jCtr K J r ∈ frontier K := by
  unfold t39jCtr
  split_ifs with h
  · exact t39jCtrSet_subset K J r (t39jLexMin_mem (t39j_isCompact_ctrSet hKb J r) h)
  · exact t39jLexMin_mem (t39j_isCompact_frontier hKb) hne

/-- if some `B̄_r(c)`, `c ∈ ∂K`, disconnects `J`, then so does `B_ρ(x)` for the selected centre
and every `ρ > r` -/
theorem t39jCtr_good {K J : Set ℂ} (hKb : Bornology.IsBounded K) {r ρ : ℝ}
    (hc : ∃ c ∈ frontier K, DisconnectsFromInfty K (closedBall c r) J) (hρ : r < ρ) :
    DisconnectsFromInfty K (ball (t39jCtr K J r) ρ) J := by
  obtain ⟨c, hc1, hc2⟩ := hc
  have hne : (t39jCtrSet K J r).Nonempty := ⟨c, subset_closure ⟨hc1, hc2⟩⟩
  have hmem : t39jCtr K J r ∈ t39jCtrSet K J r := by
    unfold t39jCtr
    split_ifs
    exact t39jLexMin_mem (t39j_isCompact_ctrSet hKb J r) hne
  obtain ⟨c', ⟨-, hc'⟩, hd⟩ := Metric.mem_closure_iff.1 hmem (ρ - r) (by linarith)
  refine hc'.mono fun w hw => ?_
  rw [mem_ball]; rw [mem_closedBall] at hw
  linarith [dist_triangle w c' (t39jCtr K J r), dist_comm (t39jCtr K J r) c']

/-- **the event `Act k i` at one `ω`** (C:1586): `ε = 2^{-t39gExp n} ≤ 1/2`, `J ≠ ∅`, and the
selected centre `x = t39jCtr K J (ε𝕣/2)` gives a ball `B_ρ(x)`, `ρ < ε𝕣`, disconnecting `J` from
`∞` in `ℂ ∖ K` -/
def t39jGoodAct (K J : Set ℂ) (n : ℕ) (R : ℝ) : Prop :=
  1 ≤ t39gExp n ∧ J.Nonempty ∧ t39jCtr K J ((2 : ℝ)⁻¹ ^ t39gExp n * R / 2) ∈ frontier K ∧
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < (2 : ℝ)⁻¹ ^ t39gExp n * R ∧
      DisconnectsFromInfty K (ball (t39jCtr K J ((2 : ℝ)⁻¹ ^ t39gExp n * R / 2)) ρ) J

theorem t39j_one_le_exp {n : ℕ} (hn : 16 ≤ n) : 1 ≤ t39gExp n := by
  unfold t39gExp
  have : 4 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  omega

open Classical in
/-- **(3.21′) for the selected centres** (C:1576–1590) at one `ω`: for `n ≥ N₁` at most `n/4`
of the nonempty `J i` are not `t39jGoodAct` -/
theorem t39j_star_at {a : ℝ} (ha : 0 < a) : ∃ N₁ : ℕ,
    ∀ {D : ContMetric} {z₀ : ℂ} {R s : ℝ}, 0 < R → 0 < s → D.IsLength →
      Bornology.IsBounded (ballM D z₀ s) → ball z₀ (a * R) ⊆ filledBall D z₀ s →
      filledBall D z₀ s ⊆ ball z₀ (3 * R) →
      ∀ {ι : Type} [Fintype ι] (J : ι → Set ℂ), (∀ i, J i ⊆ frontier (filledBall D z₀ s)) →
        (∀ i, (J i).Nonempty → IsPreconnected (J i)) → Pairwise (Disjoint on J) →
        N₁ ≤ (Finset.univ.filter fun i => (J i).Nonempty).card →
        4 * (Finset.univ.filter fun i => (J i).Nonempty ∧ ¬ t39jGoodAct (filledBall D z₀ s) (J i)
            (Finset.univ.filter fun i => (J i).Nonempty).card R).card ≤
          (Finset.univ.filter fun i => (J i).Nonempty).card := by
  obtain ⟨N₁, h16, hN₁⟩ := t39j_badY_le ha
  refine ⟨N₁, ?_⟩
  intro D z₀ R s hR hs hL hbd hK1 hK2 ι _ J hJf hJc hJd hN
  refine le_trans (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_))
    (hN₁ hR hs hL hbd hK1 hK2 J hJf hJc hJd hN)
  intro i hi
  obtain ⟨-, hne, hno⟩ := Finset.mem_filter.1 hi
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hne, ?_⟩
  rintro ⟨Y, hYb, hYd, hY⟩
  set m := (Finset.univ.filter fun i => (J i).Nonempty).card with hm
  set ε : ℝ := (2 : ℝ)⁻¹ ^ t39gExp m with hε
  have hε0 : 0 < ε := by positivity
  have hKb : Bornology.IsBounded (filledBall D z₀ s) :=
    isBounded_ball.subset hK2
  obtain ⟨c, hc, hcd⟩ := exists_frontier_closedBall_disconnects (jb_isClosed_filledBall hbd)
    (hJf i) hne hYb hYd hY
  have hfne : (frontier (filledBall D z₀ s)).Nonempty := ⟨c, hc⟩
  refine hno ⟨t39j_one_le_exp (h16.trans hN), hne, t39jCtr_mem hKb hfne _ _,
    3 * (ε * R) / 4, by positivity, by nlinarith [mul_pos hε0 hR], ?_⟩
  exact t39jCtr_good hKb ⟨c, hc, hcd⟩ (by nlinarith [mul_pos hε0 hR])

end CONF
end LQGMetric
