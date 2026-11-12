/-
# Polygonal access chains to a frontier point

Let `K ⊆ ℂ` be compact and locally connected, `C` a connected component of `Kᶜ` and `a` a frontier point
of `C`. There are finite polygonal chains `σ 0, σ 1, …` inside `C`, each ending where the next one starts,
with chains two or more steps apart disjoint, the first vertex of `σ 0` off `σ 1`, and `σ n` eventually
inside every ball around `a`.

The chain `σ n` runs inside a component `V n` of `C ∩ ball a (r n)` accumulating at `a`; the next radius
is at most half the previous one and is chosen after `σ (n - 1)` is built, so that the ball of that
radius misses `σ (n - 1)`.
-/
import LatticeProb.Topology.BoundaryAccess
import LatticeProb.Topology.PolygonalChain

open Set Metric

namespace LatticeProb.Topology

/-- **One access step.** Let `K ⊆ ℂ` be compact and locally connected, `C` a component of `Kᶜ`, `V` a
component of `C ∩ ball a ρ` accumulating at `a`, `c ∈ V`, and `P` a closed set missing `a`. There is a
radius `ρ' ≤ ρ / 2` whose ball around `a` misses `P`, a component `V'` of `C ∩ ball a ρ'` accumulating at
`a`, and a finite polygonal chain inside `V` from `c` to a point of `V'`. -/
theorem exists_access_chain_step {K : Set ℂ} (hK : IsCompact K) (hlc : IsLocallyConnectedSet K)
    {C : Set ℂ} (hC : C ∈ connectedComponentsIn Kᶜ) {a : ℂ} {ρ : ℝ} {V : Set ℂ}
    (hV : V ∈ connectedComponentsIn (C ∩ ball a ρ)) (haV : a ∈ closure V) {c : ℂ} (hc : c ∈ V)
    {P : Set ℂ} (hP : IsClosed P) (haP : a ∉ P) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ / 2 ∧ Disjoint (ball a ρ') P ∧
      ∃ V' ∈ connectedComponentsIn (C ∩ ball a ρ'), a ∈ closure V' ∧
      ∃ vs : List ℂ, ∃ hv : vs ≠ [], polygonalChain vs ⊆ V ∧ vs.head hv = c ∧
        vs.getLast hv ∈ V' := by
  have hCo : IsOpen C := isOpen_of_mem_connectedComponentsIn_compl hK.isClosed hC
  have hVsub : V ⊆ C ∩ ball a ρ := subset_of_mem_connectedComponentsIn hV
  have hρ : 0 < ρ := pos_of_mem_ball (hVsub hc).2
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.1 hP.isOpen_compl a haP
  have hρ' : 0 < min (ρ / 2) ε := lt_min (half_pos hρ) hε0
  obtain ⟨V', hV', haV'⟩ := exists_mem_connectedComponentsIn_inter_ball_mem_closure hK hlc hC
    (hVsub.trans inter_subset_left) haV hρ'
  obtain ⟨c', hc'V', hc'V⟩ := closure_nonempty_iff.1 ⟨a, haV'⟩
  have hVo : IsOpen V := by
    obtain ⟨x, -, rfl⟩ := hV
    exact (hCo.inter isOpen_ball).connectedComponentIn
  obtain ⟨vs, hv, hvs, hvh, hvl⟩ := exists_polygonal_chain_of_isPreconnected hVo
    (isConnected_of_mem_connectedComponentsIn hV).isPreconnected hc hc'V
  refine ⟨min (ρ / 2) ε, hρ', min_le_left _ _,
    Set.disjoint_left.2 fun x hx => hε (ball_subset_ball (min_le_right _ _) hx), V', hV',
    closure_mono inter_subset_left haV', vs, hv, hvs, hvh, ?_⟩
  rw [hvl]
  exact hc'V'

/-- The data carried along the access recursion: a component `s.2.1` of `C ∩ ball a s.1` accumulating
at `a`, a point `s.2.2.1` of it, and a closed set `s.2.2.2` missing `a`. -/
private abbrev AccessState (C : Set ℂ) (a : ℂ) (s : ℝ × Set ℂ × ℂ × Set ℂ) : Prop :=
  s.2.1 ∈ connectedComponentsIn (C ∩ ball a s.1) ∧ a ∈ closure s.2.1 ∧ s.2.2.1 ∈ s.2.1 ∧
    IsClosed s.2.2.2 ∧ a ∉ s.2.2.2

/-- **Polygonal access chains.** Let `K ⊆ ℂ` be compact and locally connected, `C` a component of `Kᶜ`
and `a ∈ frontier C`. There are finite polygonal chains `σ n` inside `C`, each ending where the next one
starts, with chains two or more steps apart disjoint, the first vertex of `σ 0` off `σ 1`, and `σ n`
inside any given ball around `a` for all large `n`. -/
theorem exists_access_chains {K : Set ℂ} (hK : IsCompact K) (hlc : IsLocallyConnectedSet K)
    {C : Set ℂ} (hC : C ∈ connectedComponentsIn Kᶜ) {a : ℂ} (ha : a ∈ frontier C) :
    ∃ σ : ℕ → List ℂ, ∃ hσ : ∀ n, σ n ≠ [],
      (∀ n, (σ n).getLast (hσ n) = (σ (n + 1)).head (hσ (n + 1))) ∧
      (∀ n m, n + 2 ≤ m → Disjoint (polygonalChain (σ n)) (polygonalChain (σ m))) ∧
      (σ 0).head (hσ 0) ∉ polygonalChain (σ 1) ∧ (∀ n, polygonalChain (σ n) ⊆ C) ∧
      ∀ ε > 0, ∃ N, ∀ n, N ≤ n → polygonalChain (σ n) ⊆ ball a ε := by
  have hCo : IsOpen C := isOpen_of_mem_connectedComponentsIn_compl hK.isClosed hC
  have haC : a ∉ C := by
    rw [hCo.frontier_eq] at ha
    exact ha.2
  have step : ∀ s : {s // AccessState C a s}, ∃ t : {s // AccessState C a s}, ∃ vs : List ℂ,
      ∃ hv : vs ≠ [], polygonalChain vs ⊆ s.1.2.1 ∧ vs.head hv = s.1.2.2.1 ∧
        vs.getLast hv = t.1.2.2.1 ∧ t.1.2.2.2 = polygonalChain vs ∧ t.1.1 ≤ s.1.1 / 2 ∧
        Disjoint (ball a t.1.1) s.1.2.2.2 := by
    rintro ⟨⟨ρ, V, c, P⟩, hV, haV, hc, hP, haP⟩
    obtain ⟨ρ', -, hρ', hdisj, V', hV', haV', vs, hv, hvV, hvh, hvl⟩ :=
      exists_access_chain_step hK hlc hC hV haV hc hP haP
    have hVC : V ⊆ C := (subset_of_mem_connectedComponentsIn hV).trans inter_subset_left
    exact ⟨⟨(ρ', V', vs.getLast hv, polygonalChain vs), hV', haV', hvl,
      (isCompact_polygonal_chain vs).isClosed, fun h => haC (hVC (hvV h))⟩, vs, hv, hvV, hvh, rfl,
      rfl, hρ', hdisj⟩
  obtain ⟨V0, hV0, haV0⟩ := exists_mem_connectedComponentsIn_inter_ball_mem_closure hK hlc hC
    subset_rfl (frontier_subset_closure ha) one_pos
  obtain ⟨c0, hc0V, hc0C⟩ := closure_nonempty_iff.1 ⟨a, haV0⟩
  obtain ⟨s0, hs0P, hs0ρ⟩ : ∃ s0 : {s // AccessState C a s}, s0.1.2.2.2 = {s0.1.2.2.1} ∧
      s0.1.1 = 1 :=
    ⟨⟨(1, V0, c0, {c0}), hV0, closure_mono inter_subset_left haV0, hc0V, isClosed_singleton,
      fun h => haC ((mem_singleton_iff.1 h) ▸ hc0C)⟩, rfl, rfl⟩
  choose T vs hv hvV hvh hvl hTP hTρ hTdisj using step
  let z : ℕ → {s // AccessState C a s} := fun n =>
    Nat.rec (motive := fun _ => {s // AccessState C a s}) s0 (fun _ s => T s) n
  have hsub : ∀ n, polygonalChain (vs (z n)) ⊆ C ∩ ball a (z n).1.1 := fun n =>
    (hvV (z n)).trans (subset_of_mem_connectedComponentsIn (z n).2.1)
  have hρpos : ∀ n, 0 < (z n).1.1 := fun n =>
    pos_of_mem_ball (subset_of_mem_connectedComponentsIn (z n).2.1 (z n).2.2.2.1).2
  have hρle : ∀ n, (z (n + 1)).1.1 ≤ (z n).1.1 / 2 := fun n => hTρ (z n)
  have hanti : Antitone fun n => (z n).1.1 := antitone_nat_of_succ_le fun n => by
    have h1 := hρle n
    have h2 := hρpos n
    linarith
  have hgeom : ∀ n, (z n).1.1 ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      change s0.1.1 ≤ (1 / 2 : ℝ) ^ 0
      rw [hs0ρ, pow_zero]
    | succ k ih =>
      rw [pow_succ]
      linarith [hρle k]
  refine ⟨fun n => vs (z n), fun n => hv (z n), fun n => (hvl (z n)).trans (hvh (z (n + 1))).symm,
    ?_, ?_, fun n => (hsub n).trans inter_subset_left, ?_⟩
  · intro n m hnm
    have h2 : (z (n + 1)).1.2.2.2 = polygonalChain (vs (z n)) := hTP (z n)
    have h1 := hTdisj (z (n + 1))
    rw [h2] at h1
    exact Disjoint.mono_right (fun x hx => ball_subset_ball (hanti hnm) (hsub m hx).2) h1.symm
  · intro h
    have hd := hTdisj (z 0)
    have hP0 : (z 0).1.2.2.2 = {(z 0).1.2.2.1} := hs0P
    rw [hP0] at hd
    exact Set.disjoint_left.1 hd (hsub 1 h).2 (hvh (z 0))
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨N, fun n hn x hx =>
      ball_subset_ball ((hanti hn).trans ((hgeom N).trans hN.le)) (hsub n hx).2⟩

end LatticeProb.Topology
