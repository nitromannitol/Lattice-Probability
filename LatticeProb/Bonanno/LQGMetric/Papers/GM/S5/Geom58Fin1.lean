/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58Fin1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Data

/-!
# GM Lemma 5.8: the junction data of `U_r^{x,y}` at `z_k` (task P2-M2L58b)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 3, condition 2 (l. 3110–3126).

For the data `D : L58Data` and `k < m`, `L58Data.junction` gives `L58Junction` for
`U = U_r^{x,y}`, `V = V_{ρr}(z_k)` with GM's `W_k(x)` (the squares of `V_j`, `j < k`, and of the
paths `P_i`, `i ≤ k`) and `W_k(y)` (the squares of `V_j`, `k < j`, and of `P_i`, `k < i`), here as
closed square unions `sqU (XF k)`, `sqU (YF k)`. GM: "`W_k(x)` and `W_k(y)` lie at Euclidean
distance at least `ρr/2` from each other and from `B_{ρr}(z_k)`" (l. 3115–3117); the junction
clause (decision D69) is `junction_left`/`junction_right`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

namespace L58Data

variable (D : L58Data)

/-- the squares of GM's `W_k(x)` -/
def XF (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range k).biUnion D.F ∪ (Finset.range (k + 1)).biUnion D.Q

/-- the squares of GM's `W_k(y)` -/
def YF (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Ioo k D.m).biUnion D.F ∪ (Finset.Ioc k D.m).biUnion D.Q

/-- the closed union of a finite set of squares -/
def sqU (T : Finset (ℤ × ℤ)) : Set ℂ := ⋃ g ∈ T, gridSquare D.s g

lemma mem_sqU {T : Finset (ℤ × ℤ)} {w : ℂ} :
    w ∈ D.sqU T ↔ ∃ g ∈ T, w ∈ gridSquare D.s g := by
  unfold sqU; rw [mem_iUnion₂]; simp only [exists_prop]

lemma isClosed_sqU (T : Finset (ℤ × ℤ)) : IsClosed (D.sqU T) :=
  isClosed_biUnion_finset (fun g _ => isClosed_gridSquare _ g)

lemma mem_G_F {j : ℕ} (hj : j < D.m) {g : ℤ × ℤ} (hg : g ∈ D.F j) : g ∈ D.G :=
  Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, hg⟩)

lemma mem_G_Q {i : ℕ} (hi : i ≤ D.m) {g : ℤ × ℤ} (hg : g ∈ D.Q i) : g ∈ D.G :=
  Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le hi), hg⟩)

lemma of_mem_G {w : ℂ} (h : w ∈ D.sqU D.G) :
    (∃ j < D.m, ∃ g ∈ D.F j, w ∈ gridSquare D.s g) ∨
      (∃ i ≤ D.m, ∃ g ∈ D.Q i, w ∈ gridSquare D.s g) := by
  obtain ⟨g, hg, hw⟩ := D.mem_sqU.1 h
  rcases Finset.mem_union.1 hg with h1 | h1
  · obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.1 h1
    exact Or.inl ⟨j, Finset.mem_range.1 hj, g, hgj, hw⟩
  · obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.1 h1
    exact Or.inr ⟨i, Nat.lt_succ_iff.1 (Finset.mem_range.1 hi), g, hgi, hw⟩

lemma of_mem_XF {k : ℕ} {w : ℂ} (h : w ∈ D.sqU (D.XF k)) :
    (∃ j < k, ∃ g ∈ D.F j, w ∈ gridSquare D.s g) ∨
      (∃ i ≤ k, ∃ g ∈ D.Q i, w ∈ gridSquare D.s g) := by
  obtain ⟨g, hg, hw⟩ := D.mem_sqU.1 h
  rcases Finset.mem_union.1 hg with h1 | h1
  · obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.1 h1
    exact Or.inl ⟨j, Finset.mem_range.1 hj, g, hgj, hw⟩
  · obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.1 h1
    exact Or.inr ⟨i, Nat.lt_succ_iff.1 (Finset.mem_range.1 hi), g, hgi, hw⟩

lemma of_mem_YF {k : ℕ} {w : ℂ} (h : w ∈ D.sqU (D.YF k)) :
    (∃ j, k < j ∧ j < D.m ∧ ∃ g ∈ D.F j, w ∈ gridSquare D.s g) ∨
      (∃ i, k < i ∧ i ≤ D.m ∧ ∃ g ∈ D.Q i, w ∈ gridSquare D.s g) := by
  obtain ⟨g, hg, hw⟩ := D.mem_sqU.1 h
  rcases Finset.mem_union.1 hg with h1 | h1
  · obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.1 h1
    obtain ⟨a, b⟩ := Finset.mem_Ioo.1 hj
    exact Or.inl ⟨j, a, b, g, hgj, hw⟩
  · obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.1 h1
    obtain ⟨a, b⟩ := Finset.mem_Ioc.1 hi
    exact Or.inr ⟨i, a, b, g, hgi, hw⟩

lemma mem_Vs {j : ℕ} {p : ℂ} (hp : p ∈ D.Vs j) : ∃ g ∈ D.F j, p ∈ gridSquare D.s g := by
  have := D.Vs_subset_sq j hp
  rw [mem_iUnion₂] at this
  obtain ⟨g, hg, h⟩ := this
  exact ⟨g, hg, h⟩

/-! ## Distances -/

lemma Q_near {i : ℕ} (hi : i ≤ D.m) {g : ℤ × ℤ} (hg : g ∈ D.Q i) {p : ℂ}
    (hp : p ∈ gridSquare D.s g) : ∃ c ∈ D.P i, c ∈ gridSquare D.s g ∧ dist p c ≤ 2 * D.s := by
  obtain ⟨c, hcS, hcP⟩ := (D.hQ i hi g).1 hg
  exact ⟨c, hcP, hcS, dist_le_of_mem_sq hp hcS⟩

lemma F_far {j j' : ℕ} (hj : j < D.m) (hj' : j' < D.m) (hne : j ≠ j') {g : ℤ × ℤ}
    (hg : g ∈ D.F j) {p : ℂ} (hp : p ∈ gridSquare D.s g) :
    6 * D.R - 2 * D.s ≤ dist p (D.zs j') := by
  have h1 := D.dist_le_of_F hj hg hp
  have h2 := D.zsep j hj j' hj' hne
  linarith [dist_triangle (D.zs j) p (D.zs j'), dist_comm p (D.zs j)]

lemma Q_far {i : ℕ} (hi : i ≤ D.m) {j : ℕ} (hj : j < D.m) {g : ℤ × ℤ} (hg : g ∈ D.Q i)
    {p : ℂ} (hp : p ∈ gridSquare D.s g) : 2 * D.R - 2 * D.s ≤ dist p (D.zs j) := by
  obtain ⟨c, hc, -, hpc⟩ := D.Q_near hi hg hp
  have := D.P_far hi hj hc
  linarith [dist_triangle c p (D.zs j), dist_comm p c]

lemma Q_far3 {i : ℕ} (hi : i ≤ D.m) {j : ℕ} (hj : j < D.m) (h1 : i ≠ j) (h2 : i ≠ j + 1)
    {g : ℤ × ℤ} (hg : g ∈ D.Q i) {p : ℂ} (hp : p ∈ gridSquare D.s g) :
    3 * D.R - 2 * D.s ≤ dist p (D.zs j) := by
  obtain ⟨c, hc, -, hpc⟩ := D.Q_near hi hg hp
  have : 3 * D.R ≤ dist c (D.zs j) := by
    by_contra hlt
    push Not at hlt
    rcases D.hPstub i hi j hj c hc hlt with ⟨h, -⟩ | ⟨h, -⟩
    · exact h1 h
    · exact h2 h
  linarith [dist_triangle c p (D.zs j), dist_comm p c]

lemma far_ball {z : ℂ} {ρ : ℝ} {g : ℤ × ℤ} (h : ∀ p ∈ gridSquare D.s g, ρ + 2 * D.s ≤ dist p z) :
    ∀ v p, p ∈ gridSquare D.s g → dist v p < 2 * D.s → v ∉ ball z ρ := by
  intro v p hp hv hvB
  rw [mem_ball] at hvB
  linarith [h p hp, dist_triangle p v z, dist_comm v p]

/-! ## Squares in components -/

lemma sq_mem_comp {B : Set ℂ} {t : ℂ} {g : ℤ × ℤ} (hgG : g ∈ D.G) {K : Set ℂ}
    (hK : IsPreconnected K) (hKUB : K ⊆ D.U \ B) (hKt : K ⊆ connectedComponentIn (D.U \ B) t)
    {c : ℂ} (hcK : c ∈ K) (hcS : c ∈ gridSquare D.s g)
    (hfar : ∀ v p, p ∈ gridSquare D.s g → dist v p < 2 * D.s → v ∉ B)
    {w : ℂ} (hwU : w ∈ D.U) (hwS : w ∈ gridSquare D.s g) :
    w ∈ connectedComponentIn (D.U \ B) t := by
  have h := mem_comp_of_square D.isOpen_U D.hs (openSq_subset_interior hgG) hK hKUB hcK hcK hcS
    (fun v hv => hfar v c hcS hv) hwU hwS (fun v hv => hfar v w hwS hv)
  rw [connectedComponentIn_eq (hKt hcK)]; exact h

lemma Fsq_mem_comp {B : Set ℂ} {t : ℂ} {j : ℕ} (hj : j < D.m)
    (hVt : D.Vs j ⊆ connectedComponentIn (D.U \ B) t) (hVB : Disjoint (D.Vs j) B)
    {g : ℤ × ℤ} (hg : g ∈ D.F j)
    (hfar : ∀ v p, p ∈ gridSquare D.s g → dist v p < 2 * D.s → v ∉ B)
    {w : ℂ} (hwU : w ∈ D.U) (hwS : w ∈ gridSquare D.s g) :
    w ∈ connectedComponentIn (D.U \ B) t := by
  obtain ⟨c, hc, -⟩ := exists_openSq_near D.hs hwS one_pos
  have hcV : c ∈ D.Vs j := openSq_subset_interior hg hc
  exact D.sq_mem_comp (D.mem_G_F hj hg) (D.hFc j hj)
    (fun v hv => ⟨D.Vs_subset_U hj hv, Set.disjoint_left.1 hVB hv⟩) hVt hcV
    (openSq_subset _ _ hc) hfar hwU hwS

lemma Qsq_mem_comp {B : Set ℂ} {t : ℂ} {i : ℕ} (hi : i ≤ D.m)
    (hPt : D.P i ⊆ connectedComponentIn (D.U \ B) t) (hPB : Disjoint (D.P i) B)
    {g : ℤ × ℤ} (hg : g ∈ D.Q i)
    (hfar : ∀ v p, p ∈ gridSquare D.s g → dist v p < 2 * D.s → v ∉ B)
    {w : ℂ} (hwU : w ∈ D.U) (hwS : w ∈ gridSquare D.s g) :
    w ∈ connectedComponentIn (D.U \ B) t := by
  obtain ⟨c, hcS, hcP⟩ := (D.hQ i hi g).1 hg
  exact D.sq_mem_comp (D.mem_G_Q hi hg) (D.hPc i hi)
    (fun v hv => ⟨D.P_subset_U hi hv, Set.disjoint_left.1 hPB hv⟩) hPt hcP hcS hfar hwU hwS

/-! ## The junction -/

/-- **GM l. 3110–3126**: the junction data of `U_r^{x,y}` at `z_k` -/
theorem junction {k : ℕ} (hk : k < D.m) {x y : ℂ} (hx : x ∈ D.P 0) (hy : y ∈ D.P D.m) :
    L58Junction D.U (D.Vs k) (D.zs k) x y D.R D.s := by
  have hR := D.hR
  have hs := D.hs
  have hsR := D.hsR
  have hFfar : ∀ j < D.m, j ≠ k → ∀ g ∈ D.F j, ∀ p ∈ gridSquare D.s g,
      17 / 10 * D.R + 2 * D.s ≤ dist p (D.zs k) := fun j hj hjk g hg p hp => by
    have := D.F_far hj hk hjk hg hp; linarith
  have hQfar : ∀ i ≤ D.m, ∀ g ∈ D.Q i, ∀ p ∈ gridSquare D.s g,
      17 / 10 * D.R + 2 * D.s ≤ dist p (D.zs k) := fun i hi g hg p hp => by
    have := D.Q_far hi hk hg hp; linarith
  have hPB : ∀ i ≤ D.m, Disjoint (D.P i) (ball (D.zs k) (17 / 10 * D.R)) := fun i hi =>
    Set.disjoint_left.2 fun p hp hpB => by
      have := D.P_far hi hk hp; rw [mem_ball] at hpB; linarith
  have hVB : ∀ j < D.m, j ≠ k → Disjoint (D.Vs j) (ball (D.zs k) (17 / 10 * D.R)) :=
    fun j hj hjk => Set.disjoint_left.2 fun p hp hpB => by
      obtain ⟨g, hg, hpg⟩ := D.mem_Vs hp
      have := hFfar j hj hjk g hg p hpg; rw [mem_ball] at hpB; linarith
  have chainL := D.chain_left hk hPB (fun j hj => hVB j (by omega) (by omega))
  have chainR := D.chain_right hk hPB (fun j hj hkj => hVB j hj (by omega))
  refine ⟨D.sqU (D.XF k), D.sqU (D.YF k), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `U ⊆ V ∪ X ∪ Y`
    intro w hw
    by_cases hV : w ∈ D.Vs k
    · exact Or.inl (Or.inl hV)
    have hcov : D.sqU D.G ⊆ D.sqU (D.F k) ∪ (D.sqU (D.XF k) ∪ D.sqU (D.YF k)) := by
      intro p hp
      rcases D.of_mem_G hp with ⟨j, hj, g, hg, hpg⟩ | ⟨i, hi, g, hg, hpg⟩
      · rcases lt_trichotomy j k with h | rfl | h
        · exact Or.inr (Or.inl (D.mem_sqU.2 ⟨g, Finset.mem_union_left _
            (Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 h, hg⟩), hpg⟩))
        · exact Or.inl (D.mem_sqU.2 ⟨g, hg, hpg⟩)
        · exact Or.inr (Or.inr (D.mem_sqU.2 ⟨g, Finset.mem_union_left _
            (Finset.mem_biUnion.2 ⟨j, Finset.mem_Ioo.2 ⟨h, hj⟩, hg⟩), hpg⟩))
      · by_cases h : i ≤ k
        · exact Or.inr (Or.inl (D.mem_sqU.2 ⟨g, Finset.mem_union_right _
            (Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le h), hg⟩), hpg⟩))
        · exact Or.inr (Or.inr (D.mem_sqU.2 ⟨g, Finset.mem_union_right _
            (Finset.mem_biUnion.2 ⟨i, Finset.mem_Ioc.2 ⟨by omega, hi⟩, hg⟩), hpg⟩))
    have hw' : w ∈ interior (D.sqU (D.F k) ∪ (D.sqU (D.XF k) ∪ D.sqU (D.YF k))) :=
      interior_mono hcov hw
    rcases mem_of_mem_interior_union' ((D.isClosed_sqU _).union (D.isClosed_sqU _)) hw' hV
      with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · refine Set.disjoint_left.2 fun p hp hpB => ?_
    rw [mem_ball] at hpB
    rcases D.of_mem_XF hp with ⟨j, hj, g, hg, hpg⟩ | ⟨i, hi, g, hg, hpg⟩
    · have := hFfar j (by omega) (by omega) g hg p hpg; linarith
    · have := hQfar i (by omega) g hg p hpg; linarith
  · refine Set.disjoint_left.2 fun p hp hpB => ?_
    rw [mem_ball] at hpB
    rcases D.of_mem_YF hp with ⟨j, hj, hjm, g, hg, hpg⟩ | ⟨i, hi, him, g, hg, hpg⟩
    · have := hFfar j hjm (by omega) g hg p hpg; linarith
    · have := hQfar i him g hg p hpg; linarith
  · exact D.mem_sqU.2 ⟨gIdx D.s x, Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨0, Finset.mem_range.2 (by omega),
        (D.hQ 0 (Nat.zero_le _) _).2 ⟨x, mem_gridSquare_gIdx D.hs x, hx⟩⟩),
      mem_gridSquare_gIdx D.hs x⟩
  · exact D.mem_sqU.2 ⟨gIdx D.s y, Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨D.m, Finset.mem_Ioc.2 ⟨hk, le_rfl⟩,
        (D.hQ D.m le_rfl _).2 ⟨y, mem_gridSquare_gIdx D.hs y, hy⟩⟩),
      mem_gridSquare_gIdx D.hs y⟩
  · intro w hwU hwX
    rcases D.of_mem_XF hwX with ⟨j, hj, g, hg, hwg⟩ | ⟨i, hi, g, hg, hwg⟩
    · exact D.Fsq_mem_comp (by omega) ((chainL k le_rfl).2 j (by omega) hj)
        (hVB j (by omega) (by omega)) hg (D.far_ball (hFfar j (by omega) (by omega) g hg)) hwU hwg
    · have hP := (chainL (k - i) (by omega)).1
      rw [show k - (k - i) = i by omega] at hP
      exact D.Qsq_mem_comp (by omega) hP (hPB i (by omega)) hg
        (D.far_ball (hQfar i (by omega) g hg)) hwU hwg
  · intro w hwU hwY
    rcases D.of_mem_YF hwY with ⟨j, hkj, hjm, g, hg, hwg⟩ | ⟨i, hki, him, g, hg, hwg⟩
    · exact D.Fsq_mem_comp hjm ((chainR (D.m - k - 1) (by omega)).2 j hkj (by omega))
        (hVB j hjm (by omega)) hg (D.far_ball (hFfar j hjm (by omega) g hg)) hwU hwg
    · have hP := (chainR (i - k - 1) (by omega)).1
      rw [show k + 1 + (i - k - 1) = i by omega] at hP
      exact D.Qsq_mem_comp him hP (hPB i him) hg (D.far_ball (hQfar i him g hg)) hwU hwg
  · intro p hp q hq
    rcases D.of_mem_XF hp with ⟨j, hj, g, hg, hpg⟩ | ⟨i, hi, g, hg, hpg⟩ <;>
      rcases D.of_mem_YF hq with ⟨j', hj', hj'm, g', hg', hqg⟩ | ⟨i', hi', hi'm, g', hg', hqg⟩
    · have h1 := D.F_far hj'm (show j < D.m by omega) (by omega) hg' hqg
      have h2 := D.dist_le_of_F (show j < D.m by omega) hg hpg
      linarith [dist_triangle q p (D.zs j), dist_comm p q]
    · have h1 := D.Q_far3 hi'm (show j < D.m by omega) (by omega) (by omega) hg' hqg
      have h2 := D.dist_le_of_F (show j < D.m by omega) hg hpg
      linarith [dist_triangle q p (D.zs j), dist_comm p q]
    · have h1 := D.Q_far3 (show i ≤ D.m by omega) hj'm (by omega) (by omega) hg hpg
      have h2 := D.dist_le_of_F hj'm hg' hqg
      linarith [dist_triangle p q (D.zs j')]
    · obtain ⟨c, hc, -, hpc⟩ := D.Q_near (show i ≤ D.m by omega) hg hpg
      obtain ⟨c', hc', -, hqc⟩ := D.Q_near hi'm hg' hqg
      have := D.hPsep i (by omega) i' hi'm (by omega) c hc c' hc'
      linarith [dist_triangle c p c', dist_triangle p q c', dist_comm c p]
  · intro p hp q hq hpq
    have hqz := D.dist_le_of_Vs hk hq
    rcases D.of_mem_XF hp with ⟨j, hj, g, hg, hpg⟩ | ⟨i, hi, g, hg, hpg⟩
    · have := D.F_far (show j < D.m by omega) hk (by omega) hg hpg
      exfalso; linarith [dist_triangle p q (D.zs k)]
    · obtain ⟨c, hcP, hcS, hpc⟩ := D.Q_near (show i ≤ D.m by omega) hg hpg
      have hcz : dist c (D.zs k) < 3 * D.R := by
        linarith [dist_triangle c p (D.zs k), dist_triangle p q (D.zs k), dist_comm c p]
      rcases D.hPstub i (by omega) k hk c hcP hcz with ⟨-, him, hre⟩ | ⟨hik, -, -⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hcS
        exact junction_left D.hs D.hsR (D.hF k hk) (D.hFl k hk) (by linarith)
          (by rw [← him]; exact a3) (by rw [← him]; exact a4) hpg hq hpq
      · omega
  · intro p hp q hq hpq
    have hqz := D.dist_le_of_Vs hk hq
    rcases D.of_mem_YF hp with ⟨j, hkj, hjm, g, hg, hpg⟩ | ⟨i, hki, him, g, hg, hpg⟩
    · have := D.F_far hjm hk (by omega) hg hpg
      exfalso; linarith [dist_triangle p q (D.zs k)]
    · obtain ⟨c, hcP, hcS, hpc⟩ := D.Q_near him hg hpg
      have hcz : dist c (D.zs k) < 3 * D.R := by
        linarith [dist_triangle c p (D.zs k), dist_triangle p q (D.zs k), dist_comm c p]
      rcases D.hPstub i him k hk c hcP hcz with ⟨hik, -, -⟩ | ⟨-, him', hre⟩
      · omega
      · obtain ⟨a1, a2, a3, a4⟩ := hcS
        exact junction_right D.hs D.hsR (D.hF k hk) (D.hFr k hk) (by linarith)
          (by rw [← him']; exact a3) (by rw [← him']; exact a4) hpg hq hpq

end L58Data

end LQGMetric.GM
