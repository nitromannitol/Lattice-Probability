import LatticeProb.Prob.Percolation.LatticeBoxGeometry

/-! # First exits from finite walks -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

/-- A walk starting in a set and ending outside has an inside prefix ending at an exit edge. -/
theorem walk_exists_first_exit {V : Type*} (G : SimpleGraph V) (A : Set V)
    {v w : V} (p : G.Walk v w) (hv : v ∈ A) (hw : w ∉ A) :
    ∃ y z : V, ∃ q : G.Walk v y,
      G.Adj y z ∧ z ∉ A ∧ (∀ x ∈ q.support, x ∈ A) ∧ q.support <+: p.support := by
  classical
  induction p with
  | nil => exact (hw hv).elim
  | @cons v u w h p ih =>
    by_cases hu : u ∈ A
    · obtain ⟨y, z, q, hyz, hz, hq, hsub⟩ := ih hu hw
      refine ⟨y, z, q.cons h, hyz, hz, ?_, ?_⟩
      · intro x hx
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hv
        · exact hq x hx
      · simp only [SimpleGraph.Walk.support_cons]
        exact List.cons_prefix_cons.mpr ⟨rfl, hsub⟩
    · refine ⟨v, u, .nil, h, hu, ?_, ?_⟩
      · intro x hx
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
        subst x
        exact hv
      · simp only [SimpleGraph.Walk.support_nil, SimpleGraph.Walk.support_cons]
        exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩

/-- A unit step out of a clamped interval reaches an exitable face at distance at
least the radius from the original point. -/
theorem clamped_interval_exit_distance (l u v h y z : ℤ)
    (hh : 0 ≤ h) (hw : l + 2 * h ≤ u) (hl : l ≤ v) (hu : v ≤ u)
    (hy : |y - max (l + h) (min v (u - h))| ≤ h)
    (hz : h < |z - max (l + h) (min v (u - h))|)
    (hzl : l ≤ z) (hzu : z ≤ u) (hstep : |y - z| ≤ 1) :
    |y - max (l + h) (min v (u - h))| = h ∧ h ≤ |v - y| := by
  have hc := integer_clamp_bounds l u v h hh hw hl hu
  dsimp only at hc
  rw [abs_le] at hy hstep
  rw [lt_abs] at hz
  rcases hz with hz | hz
  · have hm := hc.2.2.2.2 (by omega)
    constructor
    · rw [abs_of_nonneg (by omega : 0 ≤ y - max (l + h) (min v (u - h)))]
      omega
    · rw [abs_of_nonpos (by omega : v - y ≤ 0)]
      omega
  · have hm := hc.2.2.2.1 (by omega)
    constructor
    · rw [abs_of_nonpos (by omega : y - max (l + h) (min v (u - h)) ≤ 0)]
      omega
    · rw [abs_of_nonneg (by omega : 0 ≤ v - y)]
      omega

/-- An exiting open walk has an inside prefix whose endpoint is at least one radius
from its starting vertex in an actual coordinate. -/
theorem clamped_box_first_exit {d : ℕ} (ω : Configuration d) (l u v : Vertex d)
    (h : ℤ) (hh : 0 < h) (hw : ∀ i, l i + 2 * h ≤ u i)
    (hv : ∀ i, l i ≤ v i ∧ v i ≤ u i)
    (w : {z : Vertex d // ∀ i, l i ≤ z i ∧ z i ≤ u i})
    (p : ((openGraph ω).induce {z : Vertex d | ∀ i, l i ≤ z i ∧ z i ≤ u i}).Walk
      ⟨v, hv⟩ w)
    (hout : ¬ ∀ i, |w.val i - boxCenterClamp l u v h i| ≤ h) :
    ∃ y : {z : Vertex d // ∀ i, l i ≤ z i ∧ z i ≤ u i},
    ∃ q : ((openGraph ω).induce {z : Vertex d | ∀ i, l i ≤ z i ∧ z i ≤ u i}).Walk
      ⟨v, hv⟩ y,
      (∀ x ∈ q.support, ∀ i, |x.val i - boxCenterClamp l u v h i| ≤ h) ∧
      q.support <+: p.support ∧ q.support ⊆ p.support ∧ ∃ i,
        |y.val i - boxCenterClamp l u v h i| = h ∧ h ≤ |v i - y.val i| := by
  classical
  let A : Set {z : Vertex d // ∀ i, l i ≤ z i ∧ z i ≤ u i} :=
    {z | ∀ i, |z.val i - boxCenterClamp l u v h i| ≤ h}
  have hvA : (⟨v, hv⟩ : {z : Vertex d // ∀ i, l i ≤ z i ∧ z i ≤ u i}) ∈ A := by
    intro i
    exact ((boxCenterClamp_spec l u v h (le_of_lt hh) hw hv).1 i).2.2.1
  obtain ⟨y, z, q, hyz, hz, hq, hsub⟩ :=
    walk_exists_first_exit _ A p hvA hout
  change ¬ ∀ i, |z.val i - boxCenterClamp l u v h i| ≤ h at hz
  push Not at hz
  obtain ⟨i, hi⟩ := hz
  have hadj : (nearestNeighborGraph d).Adj y.val z.val := openGraph_le ω hyz
  obtain ⟨j, hj⟩ := Graph.Zd.adj_iff.mp hadj
  have hstep : |y.val i - z.val i| ≤ 1 := by
    rcases hj with hj | hj
    all_goals
      rw [hj]
      by_cases hij : i = j
      · subst i
        simp [LatticeProb.unit]
      · simp [LatticeProb.unit, Pi.single_eq_of_ne hij]
  have hd := clamped_interval_exit_distance (l i) (u i) (v i) h (y.val i) (z.val i)
    (le_of_lt hh) (hw i) (hv i).1 (hv i).2 (hq y q.end_mem_support i) hi
    (z.property i).1 (z.property i).2 hstep
  exact ⟨y, q, hq, hsub, hsub.subset, i, hd.1, hd.2⟩

/-- A first-exit prefix attaches its starting point to the actual projected crossing
component at a scale divisible by eight. -/
theorem ap_first_exit_attaches {d : ℕ} (ω : Configuration d) (l u v : Vertex d)
    (N : {n : ℕ // 0 < n}) (hdiv : N.val % 8 = 0)
    (hw : ∀ i, l i + 2 * ((5 * (N.val : ℤ)) / 4) ≤ u i)
    (hv : ∀ i, l i ≤ v i ∧ v i ≤ u i)
    (w : {z : Vertex d // ∀ i, l i ≤ z i ∧ z i ≤ u i})
    (p : ((openGraph ω).induce {z : Vertex d | ∀ i, l i ≤ z i ∧ z i ≤ u i}).Walk
      ⟨v, hv⟩ w)
    (hout : w.val ∉ apOuter (boxCenterClamp l u v ((5 * (N.val : ℤ)) / 4)) N)
    (hp : apProjectedProperty (boxCenterClamp l u v ((5 * (N.val : ℤ)) / 4)) N
      ((openGraph ω).induce
        (apOuter (boxCenterClamp l u v ((5 * (N.val : ℤ)) / 4)) N : Set (Vertex d)))) :
    ∃ C : ((openGraph ω).induce
      (apOuter (boxCenterClamp l u v ((5 * (N.val : ℤ)) / 4)) N :
        Set (Vertex d))).ConnectedComponent,
      latticeCubeComponentCrosses
        (fun i => (boxCenterClamp l u v ((5 * (N.val : ℤ)) / 4) i : ℝ))
        ⟨5 * (N.val : ℝ) / 4, by
          simp only [Set.mem_Ioi]
          have hn : (0 : ℝ) < N.val := by exact_mod_cast N.property
          positivity⟩ _ C ∧
      ∃ hvB : v ∈ apOuter (boxCenterClamp l u v ((5 * (N.val : ℤ)) / 4)) N,
      (⟨v, hvB⟩ : {z : Vertex d // z ∈
        apOuter (boxCenterClamp l u v ((5 * (N.val : ℤ)) / 4)) N}) ∈ C.supp ∧
      ∃ y, ∃ q : ((openGraph ω).induce
        {z : Vertex d | ∀ i, l i ≤ z i ∧ z i ≤ u i}).Walk ⟨v, hv⟩ y,
        q.support <+: p.support ∧ q.support ⊆ p.support ∧
        (∀ x ∈ q.support, ∀ i,
          |x.val i - boxCenterClamp l u v ((5 * (N.val : ℤ)) / 4) i| ≤
            (5 * (N.val : ℤ)) / 4) ∧
        ∃ i, |y.val i - boxCenterClamp l u v ((5 * (N.val : ℤ)) / 4) i| =
          (5 * (N.val : ℤ)) / 4 ∧
          (N.val : ℝ) / 2 < |(v i : ℝ) - (y.val i : ℝ)| := by
  classical
  let h : ℤ := 5 * (N.val : ℤ) / 4
  let c := boxCenterClamp l u v h
  have hn8 : (N.val : ℤ) % 8 = 0 := by exact_mod_cast hdiv
  have hN : (0 : ℤ) < N.val := by exact_mod_cast N.property
  have hh : 0 < h := by dsimp [h]; omega
  have hfour : 4 * h = 5 * (N.val : ℤ) := by dsimp [h]; omega
  have hreal : (h : ℝ) = 5 * (N.val : ℝ) / 4 := by
    have hc : (4 : ℝ) * h = 5 * (N.val : ℝ) := by exact_mod_cast hfour
    linarith
  have hiff (x : Vertex d) : x ∈ apOuter c N ↔ ∀ i, |x i - c i| ≤ h := by
    rw [mem_apOuter_iff]
    constructor <;> intro hx i
    · have hi := hx i
      rw [← hreal] at hi
      exact_mod_cast hi
    · have hi := hx i
      have hi' : |(x i : ℝ) - (c i : ℝ)| ≤ (h : ℝ) := by exact_mod_cast hi
      simpa only [hreal] using hi'
  have hout' : ¬ ∀ i, |w.val i - c i| ≤ h := by
    intro hwB
    exact hout ((hiff w.val).mpr hwB)
  obtain ⟨y, q, hq, hpref, hsub, i, hface, hd⟩ :=
    clamped_box_first_exit ω l u v h hh hw hv w p hout'
  have hvB : v ∈ apOuter c N := (hiff v).mpr
    (fun i => ((boxCenterClamp_spec l u v h (le_of_lt hh) hw hv).1 i).2.2.1)
  let G := (openGraph ω).induce {z : Vertex d | ∀ i, l i ≤ z i ∧ z i ≤ u i}
  let f : G →g openGraph ω := (SimpleGraph.Embedding.induce _).toHom
  let qa := q.map f
  have hqa : ∀ z ∈ qa.support, z ∈ (apOuter c N : Set (Vertex d)) := by
    intro z hz
    change z ∈ (q.map f).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact (hiff x.val).mpr (hq x hx)
  let qb := qa.induce (apOuter c N : Set (Vertex d)) hqa
  have hwide : ∃ x ∈ qb.support, ∃ z ∈ qb.support, ∃ j : Fin d,
      (N.val : ℝ) / 2 < |(x.val j : ℝ) - (z.val j : ℝ)| := by
    refine ⟨_, qb.start_mem_support, _, qb.end_mem_support, i, ?_⟩
    change (N.val : ℝ) / 2 < |(v i : ℝ) - (y.val i : ℝ)|
    have hd' : (h : ℝ) ≤ |(v i : ℝ) - (y.val i : ℝ)| := by exact_mod_cast hd
    have hn : (0 : ℝ) < N.val := by exact_mod_cast N.property
    rw [hreal] at hd'
    linarith
  obtain ⟨C, hcross, _, hatt, _⟩ := hp
  exact ⟨C, hcross, hvB, hatt _ _ qb hwide, y, q, hpref, hsub, hq, i, hface, by
    have hd' : (h : ℝ) ≤ |(v i : ℝ) - (y.val i : ℝ)| := by exact_mod_cast hd
    have hn : (0 : ℝ) < N.val := by exact_mod_cast N.property
    rw [hreal] at hd'
    linarith⟩

end LatticeProb.Percolation
