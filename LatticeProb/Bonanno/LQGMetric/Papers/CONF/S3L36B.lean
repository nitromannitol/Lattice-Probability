/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L36B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36A

/-!
# CONF Lemma 3.6, Step 2: the bound (3.21) from the square chains

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6, Step 2 (C:1392–1398), as corrected
by decision D108 (b) (`decisions/DEC-108.md` §1.2): CONF's path claim C:1208 is replaced by the
square-chain claims `CONFFatChainA K`, `CONFFatChainB K` and the event (3.9′) `confFatEv`.

* `conf36_sqAdj_inter` : edge-adjacent grid squares meet;
* `conf36_chain_internal` : along a chain of `m + 1` squares of internal diameter `≤ B` in `V`,
  any point of the first square is at internal distance `≤ (m+1)B` in `V` from any point of the
  last one;
* `conf36_near_removed` : **(3.21) before the first-hit step** (C:1392–1396): if `T` is the set of
  squares of `𝒮^z_{δρ}(𝔸_{3ρ,4ρ}(z))` meeting a set `𝓑` (`T ≠ ∅`), every square has internal
  diameter `≤ B` in `𝔸_{2ρ,5ρ}(z)` (condition 2 of `E^U_ρ(z)`) and (3.9′) holds with bound `B`,
  then every `u ∈ 𝔸_{3ρ,4ρ}(z)` is at internal distance `≤ (2K+3)B` in `𝔸_{2ρ,5ρ}(z)` from a point
  of `𝓑` (D108: `(2K+4)(c/100)` with `B = (c/100)𝔠_ρe^{ξh_ρ(z)}`).
* `conf36_hnear` : the hypothesis `hnear` of `conf36_geod_kill` from the above for
  `𝓑 = 𝓑^•_τ`, `(2K+3)B < a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

theorem conf36_internal_le_diam (D : ContMetric) {A V : Set ℂ} {x y : ℂ} (hx : x ∈ A)
    (hy : y ∈ A) : D.internal V x y ≤ internalDiam D A V :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)

/-- edge-adjacent grid squares meet -/
theorem conf36_sqAdj_inter {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) {k k' : ℤ × ℤ} (h : SqAdj k k') :
    (confSq ε z k ∩ confSq ε z k').Nonempty := by
  unfold SqAdj at h
  have h1 : -1 ≤ k'.1 - k.1 ∧ k'.1 - k.1 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (k'.2 - k.2)]
  have h2 : -1 ≤ k'.2 - k.2 ∧ k'.2 - k.2 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (k'.1 - k.1)]
  set a : ℤ := max k.1 k'.1
  set b : ℤ := max k.2 k'.2
  have ha1 : (k.1 : ℝ) ≤ a := by exact_mod_cast le_max_left _ _
  have ha2 : (k'.1 : ℝ) ≤ a := by exact_mod_cast le_max_right _ _
  have hb1 : (k.2 : ℝ) ≤ b := by exact_mod_cast le_max_left _ _
  have hb2 : (k'.2 : ℝ) ≤ b := by exact_mod_cast le_max_right _ _
  have ha3 : (a : ℝ) ≤ k.1 + 1 := by exact_mod_cast max_le (by omega) (by omega)
  have ha4 : (a : ℝ) ≤ k'.1 + 1 := by exact_mod_cast max_le (by omega) (by omega)
  have hb3 : (b : ℝ) ≤ k.2 + 1 := by exact_mod_cast max_le (by omega) (by omega)
  have hb4 : (b : ℝ) ≤ k'.2 + 1 := by exact_mod_cast max_le (by omega) (by omega)
  refine ⟨⟨z.re + a * ε, z.im + b * ε⟩, ?_, ?_⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [] <;> nlinarith

/-- chain bound: internal distances along a chain of squares -/
theorem conf36_chain_internal (d : ContMetric) {ε r B : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B) {z : ℂ}
    {V : Set ℂ}
    (hsq : ∀ k ∈ confSqIdx ε z (annulus z (3 * r) (4 * r)),
      internalDiam d (confSq ε z k) V ≤ ENNReal.ofReal B)
    {m : ℕ} {k : ℕ → ℤ × ℤ} (hk : ∀ i ≤ m, k i ∈ confSqIdx ε z (annulus z (3 * r) (4 * r)))
    (hadj : ∀ i < m, SqAdj (k i) (k (i + 1))) {p : ℂ} (hp : p ∈ confSq ε z (k 0)) :
    ∀ i ≤ m, ∀ q ∈ confSq ε z (k i), d.internal V p q ≤ ENNReal.ofReal ((i + 1) * B) := by
  intro i
  induction i with
  | zero =>
    intro _ q hq
    simpa using (conf36_internal_le_diam d hp hq).trans (hsq _ (hk 0 (Nat.zero_le _)))
  | succ i ih =>
    intro hi q hq
    obtain ⟨w, hw1, hw2⟩ := conf36_sqAdj_inter hε z (hadj i (by omega))
    have e1 := ih (by omega) w hw1
    have e2 : d.internal V w q ≤ ENNReal.ofReal B :=
      (conf36_internal_le_diam d hw2 hq).trans (hsq _ (hk (i + 1) hi))
    calc d.internal V p q ≤ d.internal V p w + d.internal V w q :=
          MetricGeometry.internalEDist_triangle _ _ _ _
      _ ≤ ENNReal.ofReal ((i + 1) * B) + ENNReal.ofReal B := add_le_add e1 e2
      _ = ENNReal.ofReal ((((i + 1 : ℕ) : ℝ) + 1) * B) := by
          rw [← ENNReal.ofReal_add (by positivity) hB]; congr 1; push_cast; ring

/-- the end point of a chain from a square containing `p`: the bound `(K+1)B` -/
theorem conf36_sqChain_bound (d : ContMetric) {ε r B : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B) {z : ℂ}
    {V : Set ℂ} {K : ℕ}
    (hsq : ∀ k ∈ confSqIdx ε z (annulus z (3 * r) (4 * r)),
      internalDiam d (confSq ε z k) V ≤ ENNReal.ofReal B)
    {k₀ : ℤ × ℤ} {S : Set (ℤ × ℤ)} (hch : SqChain ε z r K k₀ S) {p : ℂ}
    (hp : p ∈ confSq ε z k₀) :
    ∃ k' ∈ S, ∀ q ∈ confSq ε z k', d.internal V p q ≤ ENNReal.ofReal ((K + 1) * B) := by
  obtain ⟨m, k, hmK, hk0, hk, hadj, hkm⟩ := hch
  refine ⟨k m, hkm, fun q hq => ?_⟩
  refine (conf36_chain_internal d hε hB hsq hk hadj (hk0 ▸ hp) m le_rfl q hq).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have : (m : ℝ) ≤ K := by exact_mod_cast hmK
  nlinarith

end LQGMetric.CONF
