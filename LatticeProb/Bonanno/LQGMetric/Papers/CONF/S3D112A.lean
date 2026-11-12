/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36In
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36B
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36C

/-!
# D112: the true form of CONF Lemma 3.3 consumed by Lemma 3.6 — the grid-component event `fatG`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex` (C:line). Decision D112
(`decisions/DEC-112.md`): CONF's event `G^U` (3.9) (C:1205) and D108's (3.9′) `confFatEv` are
both false as inputs to Lemma 3.3 ("pocket" configurations, P2-CONF33W handoff, verified in
DEC-112 §1), and the per-Euclidean-component repair needs a hard circle-sliver analysis. Instead,
the small-diameter event is stated on the **grid graph of full squares**: a square of
`𝒮^z_{δr}(𝔸_{3r,4r}(z))` is *full* if it meets the closed annulus `3r+2δr ≤ |u−z| ≤ 4r−2δr`
(so it lies in `𝔸_{3r,4r}(z)`); the free squares are the full non-removed ones; `C` ranges over
the edge-adjacency components of the free squares; `K_C` is the finite set of centres of `C` and
`W_C` the open `δr/4`-neighbourhood of the spine (segments between centres of adjacent squares of
`C`), so that `K_C ⊆ W_C ⊆ U_{δr/4}` with `W_C` open, bounded and connected. The event is

  `fatG p d s r z T := ∀ C, sup_{u,v ∈ K_C} d(u, v; W_C) ≤ (c/100) s`,  `s = 𝔠_r e^{ξh_r(z)}`.

Lemma 3.6 consumes it through `L36Input` (S3L36In): `L36Step2Input p (fatG p)` (deterministic,
this file: from the two elementary grid claims `CONFChainFull 4` and `CONFFullConn`) and
`L33Gen γ D c p (fatG p)` (Lemma 3.3 for `fatG`, the probabilistic part, D108 P2–P4 with the
family `(K_C, W_C)`).

* `CONFChainFull K`: from any square containing a point of `𝔸_{3r,4r}(z)` there is a chain of at
  most `K+1` edge-adjacent squares of `𝒮^z_{δr}(𝔸_{3r,4r}(z))` to a full square (walk `≤ 4`
  squares in the axis direction closest to the radial direction towards `|u − z| = 3.5r`).
* `CONFFullConn`: the full squares are connected in the grid graph (they are the squares meeting
  a connected set, the closed annulus).
* `fatG_comp_reach` (proved): every grid component of the free squares has a square joined by a
  chain of `≤ 5` squares to a removed square (`T ≠ ∅`).
* `l36Step2Input_fatG` (proved): **(3.21)** `L36Step2Input p (fatG p)` from the two claims
  (CONF C:1392–1396, with the bound `(2·4+3)(c/100) < c`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-! ## Full squares, free squares, grid components, spines -/

/-- the centre `z + ε(k₁ + 1/2, k₂ + 1/2)` of the square `confSq ε z k` -/
def confCtr (ε : ℝ) (z : ℂ) (k : ℤ × ℤ) : ℂ :=
  ⟨z.re + (k.1 + 1 / 2) * ε, z.im + (k.2 + 1 / 2) * ε⟩

/-- the closed annulus `3r + 2ε ≤ |u − z| ≤ 4r − 2ε` -/
def confMidAnn (z : ℂ) (r ε : ℝ) : Set ℂ := {u | 3 * r + 2 * ε ≤ ‖u - z‖ ∧ ‖u - z‖ ≤ 4 * r - 2 * ε}

/-- **full squares**: the squares of side `ε` meeting the closed annulus `confMidAnn z r ε` -/
def confFull (ε : ℝ) (z : ℂ) (r : ℝ) : Set (ℤ × ℤ) := confSqIdx ε z (confMidAnn z r ε)

/-- **free squares**: full and not removed -/
def confFree (ε : ℝ) (z : ℂ) (r : ℝ) (T : Finset (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  confFull ε z r \ ↑T

/-- the edge-adjacency relation of the grid graph on the index set `F` -/
def confGridRel (F : Set (ℤ × ℤ)) (k k' : ℤ × ℤ) : Prop := SqAdj k k' ∧ k ∈ F ∧ k' ∈ F

/-- the grid component of `k` in `F` -/
def confComp (F : Set (ℤ × ℤ)) (k : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {k' | Relation.ReflTransGen (confGridRel F) k k'}

/-- the centres of the squares of `C` -/
def confCtrs (ε : ℝ) (z : ℂ) (C : Set (ℤ × ℤ)) : Set ℂ := confCtr ε z '' C

/-- the spine of `C`: the segments between the centres of edge-adjacent squares of `C` (and the
centres themselves) -/
def confSpine (ε : ℝ) (z : ℂ) (C : Set (ℤ × ℤ)) : Set ℂ :=
  ⋃ k ∈ C, ⋃ k' ∈ C, ⋃ (_ : k = k' ∨ SqAdj k k'), segment ℝ (confCtr ε z k) (confCtr ε z k')

/-- the open `ε/4`-neighbourhood of the spine of `C` (the domain of the internal metric) -/
def confFatW (ε : ℝ) (z : ℂ) (C : Set (ℤ × ℤ)) : Set ℂ := thickening (ε / 4) (confSpine ε z C)

/-- **the small-diameter event of D112** (`G^U` of CONF (3.9), C:1205, in the grid-component
form): for every grid component `C` of the free squares of `U = confU r δ z T`, the centres of
`C` have internal diameter `≤ (c/100) s` in `W_C` -/
def fatG (p : CONFParams) (d : ContMetric) (s r : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) : Prop :=
  ∀ k ∈ confFree (p.δ * r) z r T,
    internalDiam d (confCtrs (p.δ * r) z (confComp (confFree (p.δ * r) z r T) k))
      (confFatW (p.δ * r) z (confComp (confFree (p.δ * r) z r T) k)) ≤
      ENNReal.ofReal (p.c / 100 * s)

/-! ## The two open grid claims (D112 packet G1) -/

/-- **Chain to a full square**: for `δ < 1/8`, every square `k₀` containing a point `u` of
`𝔸_{3r,4r}(z)` is joined by a chain of at most `K + 1` edge-adjacent squares of
`𝒮^z_{δr}(𝔸_{3r,4r}(z))` to a full square. (Proof idea, `K = 4`: let `d` be the axis direction
with `⟨d, (u − z)/|u − z|⟩ ≥ 1/√2` pointing towards `|u − z| = 3.5r`; the squares `k₀ + jd`,
`j ≤ 4`, contain `u + jδr d`, whose modulus moves by between `δr/2` and `δr` per step, so it
stays in `(3r, 4r)` and reaches `[3r + 2δr, 4r − 2δr]` by `j = 4` since `8δr < r`.) -/
def CONFChainFull (K : ℕ) : Prop :=
  ∀ δ r : ℝ, 0 < δ → δ < 1 / 8 → 0 < r → ∀ (z : ℂ), ∀ u ∈ (annulus z (3 * r) (4 * r) : Set ℂ),
    ∀ k₀ : ℤ × ℤ, u ∈ confSq (δ * r) z k₀ → SqChain (δ * r) z r K k₀ (confFull (δ * r) z r)

/-- **Connectivity of the full squares** in the grid graph (the squares meeting a connected set
are grid-connected: if `C ⊊ M` is a union of components, `X ∩ ⋃_C S` and `X ∩ ⋃_{M∖C} S` are
disjoint closed sets covering the connected set `X` — two squares sharing only a corner `p ∈ X`
are joined through the other two squares at `p`). -/
def CONFFullConn : Prop :=
  ∀ δ r : ℝ, 0 < δ → δ < 1 / 8 → 0 < r → ∀ (z : ℂ), ∀ k ∈ confFull (δ * r) z r,
    ∀ k' ∈ confFull (δ * r) z r, Relation.ReflTransGen (confGridRel (confFull (δ * r) z r)) k k'

/-! ## Elementary facts -/

theorem sqAdj_symm {k k' : ℤ × ℤ} (h : SqAdj k k') : SqAdj k' k := by
  unfold SqAdj at *; nlinarith

theorem confCtr_mem {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) (k : ℤ × ℤ) : confCtr ε z k ∈ confSq ε z k := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [confCtr] <;> nlinarith

theorem confFull_subset_idx {ε r : ℝ} (hε : 0 < ε) (z : ℂ) :
    confFull ε z r ⊆ confSqIdx ε z (annulus z (3 * r) (4 * r)) := by
  rintro k ⟨u, hu1, hu2⟩
  exact ⟨u, hu1, by constructor <;> linarith [hu2.1, hu2.2]⟩

theorem confFree_subset_full {ε r : ℝ} {z : ℂ} {T : Finset (ℤ × ℤ)} :
    confFree ε z r T ⊆ confFull ε z r := fun _ h => h.1

theorem confComp_subset {F : Set (ℤ × ℤ)} {k : ℤ × ℤ} (hk : k ∈ F) : confComp F k ⊆ F := by
  intro k' hk'
  induction hk' with
  | refl => exact hk
  | tail _ h ih => exact h.2.2

theorem confCtr_dist_le {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) {k k' : ℤ × ℤ} (h : k = k' ∨ SqAdj k k') :
    dist (confCtr ε z k) (confCtr ε z k') ≤ ε := by
  rcases h with rfl | h
  · simp [hε]
  · unfold SqAdj at h
    have h1 : -1 ≤ k'.1 - k.1 ∧ k'.1 - k.1 ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (k'.2 - k.2)]
    have h2 : -1 ≤ k'.2 - k.2 ∧ k'.2 - k.2 ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (k'.1 - k.1)]
    have hab : |k'.1 - k.1| + |k'.2 - k.2| = 1 := by
      have ha : k'.1 - k.1 = -1 ∨ k'.1 - k.1 = 0 ∨ k'.1 - k.1 = 1 := by omega
      have hb : k'.2 - k.2 = -1 ∨ k'.2 - k.2 = 0 ∨ k'.2 - k.2 = 1 := by omega
      rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb] at h ⊢ <;>
        (try norm_num at h) <;> norm_num
    have hab' : |(k'.1 - k.1 : ℝ)| + |(k'.2 - k.2 : ℝ)| = 1 := by exact_mod_cast hab
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : (confCtr ε z k - confCtr ε z k').re = -((k'.1 - k.1 : ℝ) * ε) := by
      simp [confCtr]; ring
    have e2 : (confCtr ε z k - confCtr ε z k').im = -((k'.2 - k.2 : ℝ) * ε) := by
      simp [confCtr]; ring
    rw [e1, e2, abs_neg, abs_neg, abs_mul, abs_mul, abs_of_nonneg hε, ← add_mul, hab', one_mul]

/-- `W_C ⊆ 𝔸_{2r,5r}(z)` for `C` a set of full squares, `8ε ≤ r` -/
theorem confFatW_subset_annulus {ε r : ℝ} (hε : 0 < ε) (hεr : 8 * ε ≤ r) (z : ℂ)
    {C : Set (ℤ × ℤ)} (hC : C ⊆ confFull ε z r) :
    confFatW ε z C ⊆ (annulus z (2 * r) (5 * r) : Set ℂ) := by
  intro p hp
  obtain ⟨q₁, hq₁, hd⟩ := Metric.mem_thickening_iff.1 hp
  simp only [confSpine, mem_iUnion] at hq₁
  obtain ⟨k, hk, k', hk', hkk', hq₁⟩ := hq₁
  obtain ⟨q₂, hq₂sq, hq₂ann⟩ := hC hk
  have d1 : dist q₁ (confCtr ε z k) ≤ ε := by
    have hcc : ‖confCtr ε z k' - confCtr ε z k‖ ≤ ε := by
      rw [← dist_eq_norm, dist_comm]; exact confCtr_dist_le hε.le z hkk'
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hq₁
    have hb1 : b ≤ 1 := by linarith
    have hab' : a = 1 - b := by linarith
    subst hab'
    rw [dist_eq_norm, show (1 - b) • confCtr ε z k + b • confCtr ε z k' - confCtr ε z k =
        b • (confCtr ε z k' - confCtr ε z k) by rw [sub_smul, one_smul, smul_sub]; abel,
      norm_smul, Real.norm_of_nonneg hb]
    calc b * ‖confCtr ε z k' - confCtr ε z k‖ ≤ 1 * ε :=
          mul_le_mul hb1 hcc (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε
  have d2 : dist (confCtr ε z k) q₂ ≤ 2 * ε := by
    obtain ⟨c1, c2, c3, c4⟩ := confCtr_mem hε.le z k
    obtain ⟨q1, q2, q3, q4⟩ := hq₂sq
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im]
    have h1 : |(confCtr ε z k).re - q₂.re| ≤ ε := abs_le.2 ⟨by linarith, by linarith⟩
    have h2 : |(confCtr ε z k).im - q₂.im| ≤ ε := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have d3 : dist p q₂ < 4 * ε := by
    calc dist p q₂ ≤ dist p q₁ + dist q₁ (confCtr ε z k) + dist (confCtr ε z k) q₂ :=
          dist_triangle4 _ _ _ _
      _ < ε / 4 + ε + 2 * ε := by linarith
      _ ≤ 4 * ε := by linarith
  have h1 : ‖q₂ - z‖ - ‖p - z‖ ≤ dist p q₂ := by
    rw [dist_comm, dist_eq_norm]; linarith [norm_sub_le_norm_sub_add_norm_sub q₂ p z]
  have h2 : ‖p - z‖ - ‖q₂ - z‖ ≤ dist p q₂ := by
    rw [dist_eq_norm]; linarith [norm_sub_le_norm_sub_add_norm_sub p q₂ z]
  constructor <;> linarith [hq₂ann.1, hq₂ann.2]

/-! ## Every grid component of the free squares reaches a removed square -/

/-- along a path of full squares from a free square `k`, either the end point is in the component
of `k` or some square of the component is edge-adjacent to a removed full square -/
theorem confComp_or_adjT {ε r : ℝ} {z : ℂ} {T : Finset (ℤ × ℤ)} {k b : ℤ × ℤ}
    (hk : k ∈ confFree ε z r T) (hp : Relation.ReflTransGen (confGridRel (confFull ε z r)) k b) :
    b ∈ confComp (confFree ε z r T) k ∨
      ∃ k'' ∈ confComp (confFree ε z r T) k, ∃ t' ∈ T, t' ∈ confFull ε z r ∧ SqAdj k'' t' := by
  induction hp with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail b b' _ h ih =>
    rcases ih with hb | hb
    · by_cases hb' : b' ∈ T
      · exact Or.inr ⟨b, hb, b', hb', h.2.2, h.1⟩
      · exact Or.inl (Relation.ReflTransGen.tail hb ⟨h.1, confComp_subset hk hb, ⟨h.2.2, hb'⟩⟩)
    · exact Or.inr hb

/-- **every grid component of the free squares reaches a removed square** by a chain of at most
`K + 1 ≤ 5` squares (`T ≠ ∅`) -/
theorem fatG_comp_reach (hA : CONFChainFull 4) (hC : CONFFullConn) {δ r : ℝ} (hδ : 0 < δ)
    (hδ8 : δ < 1 / 8) (hr : 0 < r) (z : ℂ) {T : Finset (ℤ × ℤ)}
    (hT : ∀ k ∈ T, k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r))) (hTne : T.Nonempty)
    {k : ℤ × ℤ} (hk : k ∈ confFree (δ * r) z r T) :
    ∃ k' ∈ confComp (confFree (δ * r) z r T) k, SqChain (δ * r) z r 4 k' ↑T := by
  classical
  obtain ⟨t, ht⟩ := hTne
  obtain ⟨q, hqt, hqA⟩ := hT t ht
  obtain ⟨m, s, hm, hs0, hsI, hadj, hsm⟩ := hA δ r hδ hδ8 hr z q hqA t hqt
  have hpath := hC δ r hδ hδ8 hr z k hk.1 (s m) hsm
  rcases confComp_or_adjT hk hpath with hsm' | ⟨k'', hk'', t', ht', ht'F, hadj'⟩
  · -- reversed chain from `s m` back to the last removed square of the chain
    have hsmT : s m ∉ T := (confComp_subset hk hsm').2
    set j := Nat.findGreatest (fun j => s j ∈ T) m with hj
    have hjT : s j ∈ T := Nat.findGreatest_spec (P := fun j => s j ∈ T) (Nat.zero_le m)
      (by rw [hs0]; exact ht)
    have hjm : j ≤ m := Nat.findGreatest_le m
    have hjlt : j < m := lt_of_le_of_ne hjm (by intro h; exact hsmT (h ▸ hjT))
    refine ⟨s m, hsm', m - j, fun i => s (m - i), by omega, by simp, ?_, ?_, ?_⟩
    · intro i _; exact hsI _ (Nat.sub_le _ _)
    · intro i hi
      have := hadj (m - (i + 1)) (by omega)
      rw [show m - (i + 1) + 1 = m - i by omega] at this
      exact sqAdj_symm this
    · simpa [Nat.sub_sub_self hjm] using hjT
  · refine ⟨k'', hk'', 1, fun i => if i = 0 then k'' else t', by norm_num, by simp, ?_, ?_, ?_⟩
    · intro i hi
      interval_cases i
      · simpa using confFull_subset_idx (by positivity) z (confFree_subset_full
          (confComp_subset hk hk''))
      · simpa using confFull_subset_idx (by positivity) z ht'F
    · intro i hi; interval_cases i; simpa using hadj'
    · simpa using ht'

/-! ## (3.21): the Step 2 input of Lemma 3.6 for `fatG` -/

/-- **CONF (3.21) before the first-hit step** (C:1392–1396) for the event `fatG`: every point of
`𝔸_{3r,4r}(z)` is at internal distance `< c s` in `𝔸_{2r,5r}(z)` from the set `𝓑` whose meeting
squares are the removed ones (bound `(2·4 + 3)(c/100) s`) -/
theorem l36Step2Input_fatG (hA : CONFChainFull 4) (hC : CONFFullConn) {p : CONFParams}
    (hc : 0 < p.c) (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) : L36Step2Input p (fatG p) := by
  intro d s r z T 𝓑 hs hr hT hTB _ hTne hsq hfat u hu
  set ε := p.δ * r with hε
  set B := p.c / 100 * s with hB
  have hε0 : 0 < ε := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hεr : 8 * ε ≤ r := by rw [hε]; nlinarith
  have hfin : ENNReal.ofReal ((2 * (4 : ℕ) + 3) * B) < ENNReal.ofReal (p.c * s) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), hB]; push_cast
    nlinarith [mul_pos hc hs]
  by_cases huU : u ∈ confU r p.δ z T
  · obtain ⟨k₀, hk₀⟩ : ∃ k₀, u ∈ confSq ε z k₀ := ⟨_, conf36_mem_confSq hε0 z u⟩
    obtain ⟨k', hk'F, hk'b⟩ := conf36_sqChain_bound d hε0.le hB0 hsq
      (hA p.δ r hδ hδ8 hr z u hu k₀ hk₀) hk₀
    by_cases hk'T : k' ∈ T
    · obtain ⟨b, hb1, hb2⟩ := hTB k' hk'T
      refine ⟨b, hb2, (hk'b b hb1).trans_lt (lt_of_le_of_lt ?_ hfin)⟩
      apply ENNReal.ofReal_le_ofReal; push_cast; nlinarith
    · have hk'free : k' ∈ confFree ε z r T := ⟨hk'F, hk'T⟩
      obtain ⟨k'', hk'', hch⟩ := fatG_comp_reach hA hC hδ hδ8 hr z hT hTne hk'free
      obtain ⟨k₃, hk₃T, hk₃b⟩ := conf36_sqChain_bound d hε0.le hB0 hsq hch (confCtr_mem hε0.le z k'')
      obtain ⟨b, hb1, hb2⟩ := hTB k₃ hk₃T
      refine ⟨b, hb2, lt_of_le_of_lt ?_ hfin⟩
      have e1 := hk'b _ (confCtr_mem hε0.le z k')
      have e2 : d.internal (annulus z (2 * r) (5 * r)) (confCtr ε z k') (confCtr ε z k'') ≤
          ENNReal.ofReal B := by
        have m1 : confCtr ε z k' ∈ confCtrs ε z (confComp (confFree ε z r T) k') :=
          ⟨k', Relation.ReflTransGen.refl, rfl⟩
        have m2 : confCtr ε z k'' ∈ confCtrs ε z (confComp (confFree ε z r T) k') :=
          ⟨k'', hk'', rfl⟩
        refine (MetricGeometry.internalEDist_anti (image_mono (confFatW_subset_annulus hε0 hεr z
          (confFree_subset_full.trans' (confComp_subset hk'free)))) _ _).trans ?_
        exact (conf36_internal_le_diam d m1 m2).trans (hfat k' hk'free)
      have e3 := hk₃b b hb1
      calc d.internal (annulus z (2 * r) (5 * r)) u b
          ≤ d.internal (annulus z (2 * r) (5 * r)) u (confCtr ε z k') +
            d.internal (annulus z (2 * r) (5 * r)) (confCtr ε z k') b :=
            MetricGeometry.internalEDist_triangle _ _ _ _
        _ ≤ d.internal (annulus z (2 * r) (5 * r)) u (confCtr ε z k') +
            (d.internal (annulus z (2 * r) (5 * r)) (confCtr ε z k') (confCtr ε z k'') +
              d.internal (annulus z (2 * r) (5 * r)) (confCtr ε z k'') b) :=
            add_le_add le_rfl (MetricGeometry.internalEDist_triangle _ _ _ _)
        _ ≤ ENNReal.ofReal (((4 : ℕ) + 1) * B) +
            (ENNReal.ofReal B + ENNReal.ofReal (((4 : ℕ) + 1) * B)) :=
            add_le_add e1 (add_le_add e2 e3)
        _ = ENNReal.ofReal ((2 * (4 : ℕ) + 3) * B) := by
            rw [← ENNReal.ofReal_add hB0 (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
            congr 1; push_cast; ring
  · have hmem : u ∈ ⋃ k ∈ T, confSq ε z k := by
      by_contra hn; exact huU ⟨hu, hn⟩
    obtain ⟨k, hkT, huk⟩ := mem_iUnion₂.1 hmem
    obtain ⟨b, hb1, hb2⟩ := hTB k hkT
    refine ⟨b, hb2, ((conf36_internal_le_diam d huk hb1).trans (hsq k (hT k hkT))).trans_lt
      (lt_of_le_of_lt ?_ hfin)⟩
    apply ENNReal.ofReal_le_ofReal; push_cast; nlinarith

end LQGMetric.CONF
