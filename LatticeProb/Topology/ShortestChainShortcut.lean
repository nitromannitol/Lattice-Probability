import LatticeProb.Topology.ShortestBasisChain

/-! # Shortcuts in shortest directed chains -/

set_option autoImplicit false

namespace LatticeProb

/-- A shortest duplicate-free directed chain in a set has no edge skipping a
nonempty segment. The initial and terminal vertices are fixed. -/
theorem not_rel_of_shortest_nodup_isChain {ι : Type*} {r : ι → ι → Prop}
    {s : Set ι} {x z b : ι} {p q t : List ι}
    (hq : q ≠ [])
    (hnd : (x :: (p ++ q ++ b :: t)).Nodup)
    (hch : (x :: (p ++ q ++ b :: t)).IsChain r)
    (hs : ∀ v ∈ x :: (p ++ q ++ b :: t), v ∈ s)
    (hl : (x :: (p ++ q ++ b :: t)).getLast
      (List.cons_ne_nil _ _) = z)
    (hmin : ∀ k : List ι, (x :: k).Nodup → (x :: k).IsChain r →
      (∀ v ∈ x :: k, v ∈ s) → (x :: k).getLast (List.cons_ne_nil _ _) = z →
      (p ++ q ++ b :: t).length ≤ k.length) :
    ¬ r ((x :: p).getLast (List.cons_ne_nil _ _)) b := by
  intro hrel
  have hsub : List.Sublist (x :: (p ++ b :: t)) (x :: (p ++ q ++ b :: t)) := by
    simpa only [List.append_assoc] using
      ((List.sublist_append_right q (b :: t)).append_left p).cons_cons x
  have hpre : (x :: p).IsChain r := by
    apply List.IsChain.left_of_append (l₂ := q ++ b :: t)
    simpa only [List.cons_append, List.append_assoc] using hch
  have hsuf : (b :: t).IsChain r := by
    have ht : (q ++ b :: t).IsChain r := by
      apply List.IsChain.right_of_append (l₁ := x :: p)
      simpa only [List.cons_append, List.append_assoc] using hch
    exact ht.right_of_append
  have hnew : (x :: (p ++ b :: t)).IsChain r := by
    have hj : ∀ a ∈ (x :: p).getLast?, ∀ c ∈ (b :: t).head?, r a c := by
      intro a ha c hc
      simp only [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _),
        Option.mem_def, List.head?_cons, Option.some.injEq] at ha hc
      subst a
      subst c
      exact hrel
    simpa only [List.cons_append] using hpre.append hsuf hj
  have hlast : (x :: (p ++ b :: t)).getLast (List.cons_ne_nil _ _) = z := by
    have heq : (x :: (p ++ b :: t)).getLast? =
        (x :: (p ++ q ++ b :: t)).getLast? := by
      change ((x :: p) ++ b :: t).getLast? = ((x :: (p ++ q)) ++ b :: t).getLast?
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil b t),
        List.getLast?_append_of_ne_nil _ (List.cons_ne_nil b t)]
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _),
      List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hl] at heq
    exact Option.some.inj heq
  have hm := hmin (p ++ b :: t) (hnd.sublist hsub) hnew
    (fun v hv => hs v (hsub.subset hv)) hlast
  have hpos : 0 < q.length := List.length_pos_of_ne_nil hq
  simp only [List.length_append, List.length_cons] at hm
  omega

end LatticeProb
