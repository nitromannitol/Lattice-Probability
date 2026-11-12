/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Meas.LocalEventRandom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStop
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc

/-!
# Local events of a random local set: the dyadic-hull reduction (task P2-E2R)

GM (arXiv:1905.00383, `uniqueness-final.tex` l. 1654) uses that objects defined through the
internal metric of `D_h` on the random set `𝓑^•_{t_k}` are determined by
`σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})`. With decision D32's
`localSigma h A = ⨅ₙ hullSigma h A n` (`hullSigma h A n` = `σ(A)` together with the events
`{A^{(n)} = S} ∩ F`, `F ∈ σ(h|_{int S})`) this reduces, by a countable partition over the dyadic
hulls, to the fixed-open-set statement (`LocalEvent.aeEventIn_of_saturated`). This file proves
the reduction (handoff/P2-LOCMEAS.md, "Random-set case"):

* dyadic combinatorics: a level-`m` square meets `A` iff it lies in the hull `A^{(m)}`
  (`meets_iff_subset_hull`, via the centre of the square); `A^{(n+1)} ⊆ A^{(n)}` and
  `A^{(n+1)}` determines `A^{(n)}` (`hull_succ_subset`, `hull_eq_of_hull_succ_eq`);
* `measurableSet_hull_eq`: `{A^{(m)} = S} ∈ σ(A)` for a random closed set (Effros step
  `GM.gm_setSigma_hit_closed`);
* `hullSigma_anti`: `n ↦ hullSigma h A n` is antitone, so a.s.-determination by every
  `hullSigma h A n` gives a.s.-determination by `localSigma h A` (`aeEventIn_localSigma`, the
  liminf of the witnesses, as in `GM.gm_aeEventIn_fieldSigmaClosed`);
* `aeEventIn_localSigma_of_pieces`: for an a.s. bounded random closed set, an event which on each
  `{A^{(n)} = S}` (`S` a finite union of level-`n` squares) is a.s. a `σ(h|_{int S})`-event is
  a.s. a `σ(A, h|_A)`-event;
* (`LocalEventRandom2`: Lusin separation on each piece, countable codes.)

Standard measure theory; no paper proof to follow (own elementary arguments, DEVIATIONS entry
proposed in handoff/P2-E2R.md).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open LQGMetric.Blueprint

namespace LQGMetric.LocalEvent

/-! ## Dyadic combinatorics -/

/-- the centre of the level-`m` square `dyadicSq m k` -/
def sqCenter (m : ℕ) (k : ℤ × ℤ) : ℂ := ⟨(k.1 + 1 / 2) / 2 ^ m, (k.2 + 1 / 2) / 2 ^ m⟩

lemma int_eq_of_half {a b : ℤ} (h1 : (a : ℝ) ≤ b + 1 / 2) (h2 : (b : ℝ) + 1 / 2 ≤ a + 1) :
    a = b := by
  have i1 : a < b + 1 := by exact_mod_cast (show (a : ℝ) < b + 1 by linarith)
  have i2 : b < a + 1 := by exact_mod_cast (show (b : ℝ) < a + 1 by linarith)
  omega

lemma sqCenter_mem_iff (m : ℕ) (k k' : ℤ × ℤ) : sqCenter m k ∈ dyadicSq m k' ↔ k' = k := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  simp only [dyadicSq, sqCenter, mem_ofPred_eq, div_le_div_iff_of_pos_right hp]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact Prod.ext (int_eq_of_half h1 h2) (int_eq_of_half h3 h4)
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma isClosed_dyadicSq (m : ℕ) (k : ℤ × ℤ) : IsClosed (dyadicSq m k) := by
  have e : dyadicSq m k = {x : ℂ | (k.1 : ℝ) / 2 ^ m ≤ x.re} ∩ {x : ℂ | x.re ≤ (k.1 + 1) / 2 ^ m} ∩
      ({x : ℂ | (k.2 : ℝ) / 2 ^ m ≤ x.im} ∩ {x : ℂ | x.im ≤ (k.2 + 1) / 2 ^ m}) := by
    ext x
    simp only [dyadicSq, mem_ofPred_eq, mem_inter_iff]
    tauto
  rw [e]
  exact ((isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le Complex.continuous_im continuous_const))

/-- a level-`m` square meets `A` iff it is contained in the hull `A^{(m)}` -/
lemma meets_iff_subset_hull (m : ℕ) (k : ℤ × ℤ) (A : Set ℂ) :
    (dyadicSq m k ∩ A).Nonempty ↔ dyadicSq m k ⊆ dyadicHull m A := by
  constructor
  · intro hk x hx
    simp only [dyadicHull, mem_iUnion]
    exact ⟨k, hk, hx⟩
  · intro hsub
    have hc := hsub ((sqCenter_mem_iff m k k).2 rfl)
    simp only [dyadicHull, mem_iUnion] at hc
    obtain ⟨k', hk', hc'⟩ := hc
    rwa [(sqCenter_mem_iff m k k').1 hc'] at hk'

lemma hull_eq_iff (m : ℕ) (A B : Set ℂ) :
    dyadicHull m A = dyadicHull m B ↔
      ∀ k, ((dyadicSq m k ∩ A).Nonempty ↔ (dyadicSq m k ∩ B).Nonempty) := by
  constructor
  · intro h k
    rw [meets_iff_subset_hull, meets_iff_subset_hull, h]
  · intro h
    ext x
    simp only [dyadicHull, mem_iUnion]
    exact exists_congr fun k => ⟨fun ⟨hk, hx⟩ => ⟨(h k).1 hk, hx⟩, fun ⟨hk, hx⟩ => ⟨(h k).2 hk, hx⟩⟩

/-- the parent index of a level-`n+1` square -/
def sqParent (k : ℤ × ℤ) : ℤ × ℤ := (k.1 / 2, k.2 / 2)

lemma aux_parent (a : ℤ) (n : ℕ) (x : ℝ) (h1 : (a : ℝ) / 2 ^ (n + 1) ≤ x)
    (h2 : x ≤ (a + 1) / 2 ^ (n + 1)) :
    (((a / 2 : ℤ) : ℝ)) / 2 ^ n ≤ x ∧ x ≤ (((a / 2 : ℤ) : ℝ) + 1) / 2 ^ n := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have e : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [e, div_le_iff₀ (by positivity)] at h1
  rw [e, le_div_iff₀ (by positivity)] at h2
  have i1 : (((2 * (a / 2) : ℤ)) : ℝ) ≤ a := by exact_mod_cast (by omega : 2 * (a / 2) ≤ a)
  have i2 : (a : ℝ) + 1 ≤ ((2 * (a / 2) + 2 : ℤ) : ℝ) := by
    exact_mod_cast (by omega : a + 1 ≤ 2 * (a / 2) + 2)
  push_cast at i1 i2
  constructor
  · rw [div_le_iff₀ hp]; nlinarith
  · rw [le_div_iff₀ hp]; nlinarith

lemma aux_child (b : ℤ) (n : ℕ) (x : ℝ) (h1 : (b : ℝ) / 2 ^ n ≤ x) (h2 : x ≤ (b + 1) / 2 ^ n) :
    ∃ a : ℤ, a / 2 = b ∧ (a : ℝ) / 2 ^ (n + 1) ≤ x ∧ x ≤ (a + 1) / 2 ^ (n + 1) := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have e : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [div_le_iff₀ hp] at h1
  rw [le_div_iff₀ hp] at h2
  by_cases hx : x * (2 * 2 ^ n) ≤ 2 * b + 1
  · refine ⟨2 * b, by omega, ?_, ?_⟩
    · rw [e, div_le_iff₀ (by positivity)]; push_cast; nlinarith
    · rw [e, le_div_iff₀ (by positivity)]; push_cast; linarith
  · refine ⟨2 * b + 1, by omega, ?_, ?_⟩
    · rw [e, div_le_iff₀ (by positivity)]; push_cast; linarith
    · rw [e, le_div_iff₀ (by positivity)]; push_cast; nlinarith

lemma sq_succ_subset (n : ℕ) (k : ℤ × ℤ) : dyadicSq (n + 1) k ⊆ dyadicSq n (sqParent k) := by
  intro x hx
  simp only [dyadicSq, mem_ofPred_eq] at hx ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨a1, a2⟩ := aux_parent k.1 n x.re h1 h2
  obtain ⟨b1, b2⟩ := aux_parent k.2 n x.im h3 h4
  exact ⟨a1, a2, b1, b2⟩

lemma exists_child (n : ℕ) (k : ℤ × ℤ) {x : ℂ} (hx : x ∈ dyadicSq n k) :
    ∃ k', sqParent k' = k ∧ x ∈ dyadicSq (n + 1) k' := by
  simp only [dyadicSq, mem_ofPred_eq] at hx
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨a, ha, a1, a2⟩ := aux_child k.1 n x.re h1 h2
  obtain ⟨b, hb, b1, b2⟩ := aux_child k.2 n x.im h3 h4
  exact ⟨(a, b), by simp [sqParent, ha, hb], a1, a2, b1, b2⟩

/-- a level-`n` square meets `A` iff one of its children meets `A` -/
lemma meets_iff_child (n : ℕ) (k : ℤ × ℤ) (A : Set ℂ) :
    (dyadicSq n k ∩ A).Nonempty ↔ ∃ k', sqParent k' = k ∧ (dyadicSq (n + 1) k' ∩ A).Nonempty := by
  constructor
  · rintro ⟨x, hxQ, hxA⟩
    obtain ⟨k', hk', hx'⟩ := exists_child n k hxQ
    exact ⟨k', hk', x, hx', hxA⟩
  · rintro ⟨k', rfl, x, hx, hxA⟩
    exact ⟨x, sq_succ_subset n k' hx, hxA⟩

lemma hull_succ_subset (n : ℕ) (A : Set ℂ) : dyadicHull (n + 1) A ⊆ dyadicHull n A := by
  intro x hx
  simp only [dyadicHull, mem_iUnion] at hx ⊢
  obtain ⟨k, hk, hxk⟩ := hx
  exact ⟨sqParent k, (meets_iff_child n _ A).2 ⟨k, rfl, hk⟩, sq_succ_subset n k hxk⟩

/-- `A^{(n+1)}` determines `A^{(n)}` -/
lemma hull_eq_of_hull_succ_eq {n : ℕ} {A B : Set ℂ}
    (h : dyadicHull (n + 1) A = dyadicHull (n + 1) B) : dyadicHull n A = dyadicHull n B := by
  rw [hull_eq_iff] at h ⊢
  intro k
  rw [meets_iff_child, meets_iff_child]
  exact exists_congr fun k' => and_congr_right fun _ => h k'

/-! ## Hull events and the antitone hull σ-algebras -/

section Sigma
variable {Ω : Type}

/-- `{A^{(m)} = S} ∈ σ(A)` for a random closed set `A` -/
theorem measurableSet_hull_eq {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω)) (m : ℕ) (S : Set ℂ) :
    MeasurableSet[setSigma A] {ω | dyadicHull m (A ω) = S} := by
  classical
  by_cases hS : ∃ B, dyadicHull m B = S
  · obtain ⟨B, rfl⟩ := hS
    have e : {ω | dyadicHull m (A ω) = dyadicHull m B} =
        ⋂ k, {ω | (dyadicSq m k ∩ A ω).Nonempty ↔ (dyadicSq m k ∩ B).Nonempty} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, hull_eq_iff]
    rw [e]
    refine MeasurableSet.iInter fun k => ?_
    have hk : MeasurableSet[setSigma A] {ω | (A ω ∩ dyadicSq m k).Nonempty} :=
      GM.gm_setSigma_hit_closed hA (isClosed_dyadicSq m k)
    by_cases hb : (dyadicSq m k ∩ B).Nonempty
    all_goals rw [inter_comm (dyadicSq m k) B] at hb
    · convert hk using 1
      ext ω
      simp only [mem_ofPred_eq, hb, iff_true, inter_comm]
    · convert hk.compl using 1
      ext ω
      simp only [mem_ofPred_eq, hb, iff_false, mem_compl_iff, inter_comm]
  · convert (MeasurableSet.empty : MeasurableSet[setSigma A] (∅ : Set Ω)) using 1
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact fun h => hS ⟨_, h⟩

/-- `n ↦ σ(A, h|_{int A^{(n)}})` is antitone (one step) -/
theorem hullSigma_succ_le (h : Ω → DistC) {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω)) (n : ℕ) :
    hullSigma h A (n + 1) ≤ hullSigma h A n := by
  refine sup_le le_sup_left (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨S', F, hF, rfl⟩
  by_cases hne : ∃ ω₀, dyadicHull (n + 1) (A ω₀) = S'
  · obtain ⟨ω₀, hω₀⟩ := hne
    set S := dyadicHull n (A ω₀)
    have key : {ω | dyadicHull (n + 1) (A ω) = S'} ∩ F =
        ({ω | dyadicHull n (A ω) = S} ∩ F) ∩ {ω | dyadicHull (n + 1) (A ω) = S'} := by
      ext ω
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hull_eq_of_hull_succ_eq (h1.trans hω₀.symm), h2⟩, h1⟩
      · rintro ⟨⟨_, h2⟩, h1⟩
        exact ⟨h1, h2⟩
    rw [key]
    refine MeasurableSet.inter ?_ ?_
    · have hsub : interior S' ⊆ interior S :=
        interior_mono (hω₀ ▸ hull_succ_subset n (A ω₀))
      have hF' := GM.fieldSigma_mono h (V := toOpens (interior S') isOpen_interior)
        (W := toOpens (interior S) isOpen_interior) hsub F hF
      exact (le_sup_right : _ ≤ hullSigma h A n) _
        (MeasurableSpace.measurableSet_generateFrom ⟨S, F, hF', rfl⟩)
    · exact (le_sup_left : _ ≤ hullSigma h A n) _ (measurableSet_hull_eq hA (n + 1) S')
  · convert (MeasurableSet.empty : MeasurableSet[hullSigma h A n] (∅ : Set Ω)) using 1
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact fun h1 => absurd ⟨ω, h1⟩ hne

theorem hullSigma_anti (h : Ω → DistC) {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω)) :
    Antitone (hullSigma h A) :=
  antitone_nat_of_succ_le (hullSigma_succ_le h hA)

/-- a.s.-determination by every `hullSigma h A n` gives a.s.-determination by `localSigma h A` -/
theorem aeEventIn_localSigma [MeasurableSpace Ω] {P : Measure Ω} (h : Ω → DistC)
    {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω)) {E : Set Ω}
    (hE : ∀ n, AEEventIn P (hullSigma h A n) E) : AEEventIn P (localSigma h A) E := by
  choose F hFm hEF using hE
  refine ⟨⋃ N, ⋂ n, ⋂ (_ : N ≤ n), F n, ?_, ?_⟩
  · rw [localSigma, MeasurableSpace.measurableSet_iInf]
    intro M
    have heq : (⋃ N, ⋂ n, ⋂ (_ : N ≤ n), F n) = ⋃ N, ⋂ n, ⋂ (_ : max N M ≤ n), F n := by
      ext ω
      simp only [mem_iUnion, mem_iInter]
      constructor
      · rintro ⟨N, hN⟩
        exact ⟨N, fun n hn => hN n ((le_max_left N M).trans hn)⟩
      · rintro ⟨N, hN⟩
        exact ⟨max N M, hN⟩
    rw [heq]
    exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
      MeasurableSet.iInter fun hn => hullSigma_anti h hA ((le_max_right N M).trans hn) _ (hFm n)
  · have hall : ∀ᵐ ω ∂P, ∀ n, (ω ∈ E ↔ ω ∈ F n) := by
      rw [ae_all_iff]
      intro n
      filter_upwards [hEF n] with ω hω
      exact Iff.of_eq hω
    filter_upwards [hall] with ω hω
    apply propext
    simp only [mem_iUnion, mem_iInter]
    constructor
    · intro hE
      exact ⟨0, fun n _ => (hω n).1 hE⟩
    · rintro ⟨N, hN⟩
      exact (hω N).2 (hN N le_rfl)

/-! ## Gluing over the hull partition and countable codes -/

/-- the finite union of the level-`n` squares with indices in `s` -/
def hullFin (n : ℕ) (s : Finset (ℤ × ℤ)) : Set ℂ := ⋃ k ∈ s, dyadicSq n k

lemma finite_meets_of_bounded {A : Set ℂ} (hA : Bornology.IsBounded A) (n : ℕ) :
    {k : ℤ × ℤ | (dyadicSq n k ∩ A).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := hA.subset_closedBall 0
  set N : ℤ := ⌈R * 2 ^ n⌉ + 1
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  refine ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).subset ?_
  rintro k ⟨x, hxQ, hxA⟩
  have hx := hR hxA
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have hre := (abs_le.1 ((Complex.abs_re_le_norm x).trans hx))
  have him := (abs_le.1 ((Complex.abs_im_le_norm x).trans hx))
  simp only [dyadicSq, mem_ofPred_eq, div_le_iff₀ hp, le_div_iff₀ hp] at hxQ
  obtain ⟨h1, h2, h3, h4⟩ := hxQ
  have hc := Int.le_ceil (R * 2 ^ n)
  have b1 : (k.1 : ℝ) ≤ ⌈R * 2 ^ n⌉ := by nlinarith
  have b2 : -(k.1 : ℝ) ≤ ⌈R * 2 ^ n⌉ + 1 := by nlinarith
  have b3 : (k.2 : ℝ) ≤ ⌈R * 2 ^ n⌉ := by nlinarith
  have b4 : -(k.2 : ℝ) ≤ ⌈R * 2 ^ n⌉ + 1 := by nlinarith
  have c1 : k.1 ≤ ⌈R * 2 ^ n⌉ := by exact_mod_cast b1
  have c2 : -k.1 ≤ ⌈R * 2 ^ n⌉ + 1 := by exact_mod_cast b2
  have c3 : k.2 ≤ ⌈R * 2 ^ n⌉ := by exact_mod_cast b3
  have c4 : -k.2 ≤ ⌈R * 2 ^ n⌉ + 1 := by exact_mod_cast b4
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

lemma exists_hullFin_of_bounded {A : Set ℂ} (hA : Bornology.IsBounded A) (n : ℕ) :
    ∃ s, dyadicHull n A = hullFin n s := by
  classical
  refine ⟨(finite_meets_of_bounded hA n).toFinset, ?_⟩
  ext x
  simp only [dyadicHull, hullFin, mem_iUnion, Set.Finite.mem_toFinset, mem_ofPred_eq, exists_prop]

/-- every point lies in a level-`n` square -/
lemma exists_sq_mem (n : ℕ) (y : ℂ) : ∃ k, y ∈ dyadicSq n k := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  refine ⟨(⌊y.re * 2 ^ n⌋, ⌊y.im * 2 ^ n⌋), ?_⟩
  simp only [dyadicSq, mem_ofPred_eq, div_le_iff₀ hp, le_div_iff₀ hp]
  exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le, Int.floor_le _, (Int.lt_floor_add_one _).le⟩

/-- a set lies in the interior of its dyadic hull (the squares form a locally finite cover) -/
lemma subset_interior_dyadicHull (n : ℕ) (A : Set ℂ) : A ⊆ interior (dyadicHull n A) := by
  classical
  intro x hx
  have hlf : LocallyFinite (fun k : ℤ × ℤ => dyadicSq n k) := by
    intro y
    refine ⟨Metric.ball y 1, Metric.ball_mem_nhds y one_pos, ?_⟩
    simpa only [inter_comm] using finite_meets_of_bounded Metric.isBounded_ball n
  set f : ℤ × ℤ → Set ℂ := fun k => if x ∈ dyadicSq n k then ∅ else dyadicSq n k
  have hf : LocallyFinite f := hlf.subset fun k => by
    by_cases h : x ∈ dyadicSq n k <;> simp [f, h]
  have hC : IsClosed (⋃ k, f k) := hf.isClosed_iUnion fun k => by
    by_cases h : x ∈ dyadicSq n k
    · simp [f, h]
    · simpa [f, h] using isClosed_dyadicSq n k
  rw [mem_interior]
  refine ⟨(⋃ k, f k)ᶜ, ?_, hC.isOpen_compl, ?_⟩
  · intro y hy
    obtain ⟨k, hk⟩ := exists_sq_mem n y
    have hxk : x ∈ dyadicSq n k := by
      by_contra hxk
      exact hy (mem_iUnion.2 ⟨k, by simpa [f, hxk] using hk⟩)
    simp only [dyadicHull, mem_iUnion]
    exact ⟨k, ⟨x, hxk, hx⟩, hk⟩
  · simp only [mem_compl_iff, mem_iUnion, not_exists]
    intro k
    by_cases h : x ∈ dyadicSq n k <;> simp [f, h]

/-- **Gluing over the hull partition** (level `n`): an event which on each `{A^{(n)} = S}`, `S` a
finite union of level-`n` squares, a.s. agrees with a `σ(h|_{int S})`-event, is a.s. a
`σ(A, h|_{int A^{(n)}})`-event (`A` a.s. bounded). -/
theorem aeEventIn_hullSigma_of_pieces [MeasurableSpace Ω] {P : Measure Ω} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hb : ∀ᵐ ω ∂P, Bornology.IsBounded (A ω)) (n : ℕ) {E : Set Ω}
    (hE : ∀ s : Finset (ℤ × ℤ), ∃ F, MeasurableSet[fieldSigma h
      (toOpens (interior (hullFin n s)) isOpen_interior)] F ∧
      ∀ᵐ ω ∂P, dyadicHull n (A ω) = hullFin n s → (ω ∈ E ↔ ω ∈ F)) :
    AEEventIn P (hullSigma h A n) E := by
  choose F hFm hEF using hE
  refine ⟨⋃ s, {ω | dyadicHull n (A ω) = hullFin n s} ∩ F s, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun s => (le_sup_right : _ ≤ hullSigma h A n) _
      (MeasurableSpace.measurableSet_generateFrom ⟨hullFin n s, F s, hFm s, rfl⟩)
  · filter_upwards [hb, ae_all_iff.2 hEF] with ω hbω hω
    obtain ⟨s, hs⟩ := exists_hullFin_of_bounded hbω n
    apply propext
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · exact fun hE => ⟨s, hs, (hω s hs).1 hE⟩
    · rintro ⟨s', hs', hF'⟩
      exact (hω s' hs').2 hF'

/-- **Random-set version of `aeEventIn_of_saturated`, reduction step**: for an a.s. bounded
random closed set `A`, an event which on each `{A^{(n)} = S}` a.s. agrees with a
`σ(h|_{int S})`-event is a.s. a `σ(A, h|_A)`-event (`localSigma`, D32). -/
theorem aeEventIn_localSigma_of_pieces [MeasurableSpace Ω] {P : Measure Ω} (h : Ω → DistC)
    {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω)) (hb : ∀ᵐ ω ∂P, Bornology.IsBounded (A ω))
    {E : Set Ω}
    (hE : ∀ (n : ℕ) (s : Finset (ℤ × ℤ)), ∃ F, MeasurableSet[fieldSigma h
      (toOpens (interior (hullFin n s)) isOpen_interior)] F ∧
      ∀ᵐ ω ∂P, dyadicHull n (A ω) = hullFin n s → (ω ∈ E ↔ ω ∈ F)) :
    AEEventIn P (localSigma h A) E :=
  aeEventIn_localSigma h hA fun n => aeEventIn_hullSigma_of_pieces h A hb n (hE n)


end Sigma

end LQGMetric.LocalEvent
