/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P22Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P22Det

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.22, deterministic core, part 3: the square-crossing induction

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Proposition 3.22
(DG:1739–1771), run on the ball-chain polygon `q 0 = z, …, q m = w` of
`exists_chain_of_dgLGD_le` (see `S3P22Det.lean` for the reading of the hypotheses).

DG's inductive definition of `t_j, S_j` (DG:1752–1756) becomes an induction on the remaining
number of chain balls: from a point `x` of the ball `B_{l−1}`, in a cell `S_i ∋ x`, let `l'` be
the first chain vertex `q_{l'}` (`l' ≥ l`) outside `interior S_i(1)`; the segment from the
previous vertex to `q_{l'}` (inside the ball `B_{l'−1}`) crosses `∂S_i(1)` at `y`
("`P` travels across the annulus `S_j(1) ∖ S_j`", DG:1759). Then `l' > l` (the ball has diameter
`< δ_ε ≤ |x − y|`: DG's use of the second condition of (eqn-lfpp-lower-event), DG:1763–1765),
`D^ε(x,y) ≤ l' − l + 1 ≤ 2(l' − l)` (balls `B_{l−1}, …, B_{l'−1}`, DG's double counting) and
(eqn-square-dist) bounds `exp(ξ max_{S_i(1)} φ) ≤ D^ε(x,y)/L`; the segment `[x,y] ⊆ S_i(1)`
contributes `≤ A D^ε(x,y)/L` to the LFPP length (eqn-lfpp-upper-path). Summing gives
(eqn-lfpp-upper-sum) with constant `2` in place of DG's `3`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open LQGDimension.PolygonRiemannAux

/-- The ω-wise event of DG's proof of Prop. 3.22 (eqn-lfpp-lower-event), with abstract cells
`S i ⊆ interior (T i)` (DG: the squares `S` of side `δ_ε` and `S(1)`). -/
structure DGP322Hyp {ι : Type*} (μ : Measure ℂ) (ε : ℝ) (U : Set ℂ) (S T : ι → Set ℂ)
    (a A L ξ Mx : ℝ) (φ : ℂ → ℝ) : Prop where
  convex : Convex ℝ (closure U)
  cont : Continuous φ
  xi_nonneg : 0 ≤ ξ
  L_pos : 0 < L
  A_nonneg : 0 ≤ A
  cell : ∀ x ∈ closure U, ∃ i, x ∈ S i
  sub : ∀ i, S i ⊆ interior (T i)
  conv : ∀ i, Convex ℝ (T i)
  closed : ∀ i, IsClosed (T i)
  sep : ∀ i, ∀ x ∈ S i, ∀ y ∈ frontier (T i), a ≤ ‖x - y‖
  diam : ∀ i, ∀ x ∈ T i, ∀ y ∈ T i, ‖x - y‖ ≤ A
  max : ∀ i, ∀ v ∈ T i, φ v ≤ Mx
  cross : ∀ i, ∀ x ∈ S i, ∀ y ∈ frontier (T i), ∀ v ∈ T i,
    ENNReal.ofReal (L * Real.exp (ξ * φ v)) ≤ (dgLGD μ ε U x y : ℝ≥0∞)
  mass : ∀ c ∈ closure U, ENNReal.ofReal ε < μ (ball c (a / 2))

variable {ι : Type*} {μ : Measure ℂ} {ε : ℝ} {U : Set ℂ} {S T : ι → Set ℂ}
  {a A L ξ Mx : ℝ} {φ : ℂ → ℝ}

/-- admissible balls have radius `≤ a/2` -/
lemma DGP322Hyp.radius_le (H : DGP322Hyp μ ε U S T a A L ξ Mx φ) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : ball c ρ ⊆ closure U) (hm : μ (ball c ρ) ≤ ENNReal.ofReal ε) : ρ ≤ a / 2 := by
  by_contra hlt
  push Not at hlt
  have hc : c ∈ closure U := hsub (mem_ball_self hρ)
  have := (H.mass c hc).trans_le ((measure_mono (ball_subset_ball hlt.le)).trans hm)
  exact lt_irrefl _ this

/-- the polygon property carried by the induction -/
def P322Good (U : Set ℂ) (ξ : ℝ) (φ : ℂ → ℝ) (A L Mx : ℝ) (m : ℕ) (w x : ℂ) (l : ℕ) : Prop :=
  ∃ (n : ℕ) (V : ℕ → ℂ) (K : ℕ → ℝ), 0 < n ∧ V 0 = x ∧ V n = w ∧ (∀ i ≤ n, V i ∈ closure U) ∧
    (∀ i < n, ∀ s ∈ Icc (0 : ℝ) 1, Real.exp (ξ * φ (segAff V i s)) ≤ K i) ∧
    ∑ i ∈ Finset.range n, ‖V (i + 1) - V i‖ * K i ≤
      A * (2 * ((m : ℝ) + 1 - l) / L + Real.exp (ξ * Mx))

/-- **The crossing induction** (DG:1752–1767). -/
theorem p322_good (H : DGP322Hyp μ ε U S T a A L ξ Mx φ) {m : ℕ} {q c : ℕ → ℂ} {ρ : ℕ → ℝ}
    (hch : ∀ i < m, (0 < ρ i ∧ ball (c i) (ρ i) ⊆ closure U ∧
        μ (ball (c i) (ρ i)) ≤ ENNReal.ofReal ε) ∧
        q i ∈ ball (c i) (ρ i) ∧ q (i + 1) ∈ ball (c i) (ρ i)) :
    ∀ k l : ℕ, ∀ x : ℂ, m - l = k → 1 ≤ l → l ≤ m → x ∈ ball (c (l - 1)) (ρ (l - 1)) →
      P322Good U ξ φ A L Mx m (q m) x l := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro l x hk hl1 hlm hx
  have hxU : x ∈ closure U := (hch (l - 1) (by omega)).1.2.1 hx
  obtain ⟨i, hxi⟩ := H.cell x hxU
  have hxT : x ∈ T i := interior_subset (H.sub i hxi)
  have hqmU : q m ∈ closure U := by
    have h := (hch (m - 1) (by omega)).2.2
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
    exact (hch (m - 1) (by omega)).1.2.1 h
  have hlR : (l : ℝ) ≤ m := by exact_mod_cast hlm
  have hLpos := H.L_pos
  have hA := H.A_nonneg
  by_cases hex : ∃ j, l ≤ j ∧ j ≤ m ∧ q j ∉ interior (T i)
  · -- a crossing of `∂T i`
    set l' := Nat.find hex with hl'def
    have hl' : l ≤ l' ∧ l' ≤ m ∧ q l' ∉ interior (T i) := Nat.find_spec hex
    have hmin : ∀ j, l ≤ j → j < l' → q j ∈ interior (T i) := fun j hj hjl => by
      by_contra hc
      exact Nat.find_min hex hjl ⟨hj, by omega, hc⟩
    have hl'1 : 1 ≤ l' := by omega
    have hql' : q l' ∈ ball (c (l' - 1)) (ρ (l' - 1)) := by
      have h := (hch (l' - 1) (by omega)).2.2
      rwa [Nat.sub_add_cancel hl'1] at h
    have hprev : ∃ p, p ∈ interior (T i) ∧ p ∈ ball (c (l' - 1)) (ρ (l' - 1)) ∧
        (l' = l → p = x) := by
      by_cases he : l' = l
      · refine ⟨x, H.sub i hxi, ?_, fun _ => rfl⟩
        rw [he]; exact hx
      · refine ⟨q (l' - 1), hmin _ (by omega) (by omega), (hch (l' - 1) (by omega)).2.1,
          fun h => absurd h he⟩
    obtain ⟨p, hpint, hpball, hpx⟩ := hprev
    obtain ⟨y, hyseg, hyfr⟩ := exists_segment_frontier (H.closed i) hpint hl'.2.2
    have hyball : y ∈ ball (c (l' - 1)) (ρ (l' - 1)) :=
      (convex_ball _ _).segment_subset hpball hql' hyseg
    have hyT : y ∈ T i := by
      have := frontier_subset_closure hyfr
      rwa [(H.closed i).closure_eq] at this
    have hsep := H.sep i x hxi y hyfr
    have hll' : l < l' := by
      rcases hl'.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have hx' : x ∈ ball (c (l' - 1)) (ρ (l' - 1)) := by rw [← h]; exact hx
        have h1 := norm_sub_lt_of_mem_ball hx' hyball
        have hb := hch (l' - 1) (by omega)
        have h2 := H.radius_le hb.1.1 hb.1.2.1 hb.1.2.2
        linarith
    -- `D^ε(x, y) ≤ l' − l + 1`: the chain `x, q l, …, q (l'−1), y`
    have hD : dgLGD μ ε U x y ≤ ((l' - l + 1 : ℕ) : ℕ∞) := by
      let v : ℕ → ℂ := fun j => if j = 0 then x else if j = l' - l + 1 then y else q (l - 1 + j)
      have hv0 : v 0 = x := by simp [v]
      have hvn : v (l' - l + 1) = y := by simp [v]
      rw [← hv0, ← hvn]
      refine dgLGD_le_chain v (fun j => c (l - 1 + j)) (fun j => ρ (l - 1 + j)) (l' - l + 1)
        (by omega) (fun j hj => (hch (l - 1 + j) (by omega)).1) (fun j hj => ⟨?_, ?_⟩)
      · by_cases hj0 : j = 0
        · subst hj0; simpa [v] using hx
        · have hb := (hch (l - 1 + j) (by omega)).2.1
          simp only [v, hj0, if_false, show j ≠ l' - l + 1 by omega]
          exact hb
      · by_cases hjl : j + 1 = l' - l + 1
        · simp only [v, hjl, show l' - l + 1 ≠ 0 by omega, if_false, if_true]
          have : l - 1 + j = l' - 1 := by omega
          rw [this]; exact hyball
        · have hb := (hch (l - 1 + j) (by omega)).2.2
          simp only [v, show j + 1 ≠ 0 by omega, hjl, if_false]
          rwa [show l - 1 + (j + 1) = l - 1 + j + 1 by omega]
    set Kc : ℝ := ((l' - l + 1 : ℕ) : ℝ) / L with hKc
    have hK0 : ∀ v ∈ T i, Real.exp (ξ * φ v) ≤ Kc := by
      intro v hv
      have h1 : ENNReal.ofReal (L * Real.exp (ξ * φ v)) ≤ ENNReal.ofReal ((l' - l + 1 : ℕ) : ℝ) := by
        refine (H.cross i x hxi y hyfr v hv).trans ?_
        rw [ENNReal.ofReal_natCast]
        exact_mod_cast hD
      have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
      rw [hKc, le_div_iff₀ hLpos]
      linarith
    obtain ⟨n, V, K, hn, hV0, hVn, hVU, hVK, hsum⟩ :=
      IH (m - l') (by omega) l' y rfl hl'1 hl'.2.1 hyball
    refine ⟨n + 1, fun j => if j = 0 then x else V (j - 1),
      fun j => if j = 0 then Kc else K (j - 1), by omega, by simp, by simpa using hVn, ?_, ?_, ?_⟩
    · intro j hj
      rcases j with _ | j
      · simpa using hxU
      · simpa using hVU j (by omega)
    · intro j hj s hs
      rcases j with _ | j
      · have hseg := segAff_mem_segment (fun j => if j = 0 then x else V (j - 1)) 0 hs
        simp only [if_true, show (0 + 1 = 0) = False by simp, if_false, Nat.add_sub_cancel,
          hV0] at hseg ⊢
        exact hK0 _ ((H.conv i).segment_subset hxT hyT hseg)
      · have := hVK j (by omega) s hs
        simpa [segAff] using this
    · rw [Finset.sum_range_succ']
      simp only [show ∀ j : ℕ, (j + 1 + 1 = 0) = False from fun j => by simp,
        show ∀ j : ℕ, (j + 1 = 0) = False from fun j => by simp, if_false, if_true,
        Nat.add_sub_cancel, show (0 + 1 = 0) = False by simp, hV0]
      have hcast : ((l' - l + 1 : ℕ) : ℝ) = (l' : ℝ) - l + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hl'.1, Nat.cast_one]
      have hll'R : (l : ℝ) + 1 ≤ l' := by exact_mod_cast hll'
      have hxy : ‖y - x‖ ≤ A := H.diam i y hyT x hxT
      have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
      have hstep : ‖y - x‖ * Kc ≤ A * (2 * ((l' : ℝ) - l) / L) := by
        calc ‖y - x‖ * Kc ≤ A * Kc := mul_le_mul_of_nonneg_right hxy hKc0
          _ ≤ A * (2 * ((l' : ℝ) - l) / L) := by
            apply mul_le_mul_of_nonneg_left _ hA
            rw [hKc, hcast]
            exact div_le_div_of_nonneg_right (by linarith) hLpos.le
      calc (∑ j ∈ Finset.range n, ‖V (j + 1) - V j‖ * K j) + ‖y - x‖ * Kc
          ≤ A * (2 * ((m : ℝ) + 1 - l') / L + Real.exp (ξ * Mx)) +
              A * (2 * ((l' : ℝ) - l) / L) := add_le_add hsum hstep
        _ = A * (2 * ((m : ℝ) + 1 - l) / L + Real.exp (ξ * Mx)) := by ring
  · -- no crossing: `w ∈ T i`, one segment
    push Not at hex
    have hwT : q m ∈ T i := interior_subset (hex m hlm le_rfl)
    refine ⟨1, fun j => if j = 0 then x else q m, fun _ => Real.exp (ξ * Mx), one_pos, by simp,
      by simp, ?_, ?_, ?_⟩
    · intro j hj
      by_cases hj0 : j = 0
      · simpa [hj0] using hxU
      · simpa [hj0] using hqmU
    · intro j hj s hs
      have hj0 : j = 0 := by omega
      subst hj0
      have hseg := segAff_mem_segment (fun j => if j = 0 then x else q m) 0 hs
      simp only [if_true, show (0 + 1 = 0) = False by simp, if_false] at hseg ⊢
      have hv := H.max i _ ((H.conv i).segment_subset hxT hwT hseg)
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hv H.xi_nonneg)
    · simp only [Finset.range_one, Finset.sum_singleton, if_true,
        show (0 + 1 = 0) = False by simp, if_false]
      have hxy : ‖q m - x‖ ≤ A := H.diam i _ hwT _ hxT
      have h2 : 0 ≤ A * (2 * ((m : ℝ) + 1 - l) / L) := by
        apply mul_nonneg hA; apply div_nonneg _ hLpos.le; linarith
      calc ‖q m - x‖ * Real.exp (ξ * Mx) ≤ A * Real.exp (ξ * Mx) :=
            mul_le_mul_of_nonneg_right hxy (Real.exp_pos _).le
        _ ≤ A * (2 * ((m : ℝ) + 1 - l) / L + Real.exp (ξ * Mx)) := by nlinarith

/-- **DG Proposition 3.22, deterministic core** (DG:1739–1771): on the event of
(eqn-lfpp-lower-event) (abstract cells, `DGP322Hyp`), if `D^ε(z,w;U) ≤ N` then
`D^{LFPP}_φ(z,w;Ū) ≤ A (2N/L + e^{ξ Mx})`. -/
theorem dg_prop322_det (H : DGP322Hyp μ ε U S T a A L ξ Mx φ) {z w : ℂ} {N : ℕ}
    (hN : dgLGD μ ε U z w ≤ N) :
    dgLFPP ξ φ (closure U) z w ≤ A * (2 * N / L + Real.exp (ξ * Mx)) := by
  obtain ⟨m, q, c, ρ, hm, hmN, hq0, hqm, hch⟩ := exists_chain_of_dgLGD_le hN
  have hz : z ∈ ball (c (1 - 1)) (ρ (1 - 1)) := by simpa [hq0] using (hch 0 hm).2.1
  obtain ⟨n, V, K, hn, hV0, hVn, hVU, hVK, hsum⟩ :=
    p322_good H hch (m - 1) 1 z rfl le_rfl hm hz
  have h := dgLFPP_le_poly_convex V n hn H.cont ξ H.convex hVU K hVK
  rw [hV0, hVn, hqm] at h
  refine h.trans (hsum.trans ?_)
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  apply mul_le_mul_of_nonneg_left _ H.A_nonneg
  have : 2 * ((m : ℝ) + 1 - (1 : ℕ)) / L ≤ 2 * N / L := by
    apply div_le_div_of_nonneg_right _ H.L_pos.le
    push_cast; linarith
  linarith

end DG
end LQGMetric
