/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12T6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12T5

/-!
# DZZ Lemma 3.12, one-step claim: `𝖢_{i,1}` and `𝖢_{i,2}` (P2-DZZ312S)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1443–1446 and 1468–1470: `u, v ∉ 𝖢_large`,
so `𝒞_i` enters `𝖢_large` before `𝖢` and leaves it after `𝖢`; the enclosure `𝒞_{i,cross}` of `𝖢`
meets `[𝖢_enter, 𝖢)` at `𝖢_{i,1}` and `(𝖢, 𝖢_exit]` at `𝖢_{i,2}`. With common cells
(`exists_mem_enc_of_chain`) and the last/first such cells:

* `exists_last_split`, `exists_first_split`: last/first element of a list with a property;
* **`exists_enc_split`**: `l = A ++ x :: (M ++ y :: B)` with `x, y` cells of the enclosure, `𝖢 ∈ M`
  and no cell of `M` in the enclosure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma exists_last_split {P : DyBox → Prop} :
    ∀ L : List DyBox, (∃ c ∈ L, P c) → ∃ A x B, L = A ++ x :: B ∧ P x ∧ ∀ c ∈ B, ¬ P c
  | [], h => by simp at h
  | a :: L', h => by
    by_cases h' : ∃ c ∈ L', P c
    · obtain ⟨A, x, B, rfl, hx, hB⟩ := exists_last_split L' h'
      exact ⟨a :: A, x, B, rfl, hx, hB⟩
    · push Not at h'
      obtain ⟨c, hc, hPc⟩ := h
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨[], c, L', rfl, hPc, h'⟩
      · exact absurd hPc (h' c hc)

lemma exists_first_split {P : DyBox → Prop} :
    ∀ L : List DyBox, (∃ c ∈ L, P c) → ∃ A x B, L = A ++ x :: B ∧ P x ∧ ∀ c ∈ A, ¬ P c
  | [], h => by simp at h
  | a :: L', h => by
    by_cases ha : P a
    · exact ⟨[], a, L', rfl, ha, by simp⟩
    · obtain ⟨c, hc, hPc⟩ := h
      rcases List.mem_cons.1 hc with rfl | hc
      · exact absurd hPc ha
      · obtain ⟨A, x, B, rfl, hx, hA⟩ := exists_first_split L' ⟨c, hc, hPc⟩
        refine ⟨a :: A, x, B, rfl, hx, fun d hd => ?_⟩
        rcases List.mem_cons.1 hd with rfl | hd
        · exact ha
        · exact hA d hd

lemma not_mem_enc_self {C : DyBox} {E : List DyBox}
    (hE : ∀ c ∈ E, (c.closedBox ∩ (C.largeBox \ C.closedBox)).Nonempty) : C ∉ E := by
  intro hC
  obtain ⟨z, hz1, -, hz2⟩ := hE C hC
  exact hz2 hz1

lemma mem_largeBox_of_mem_self {C : DyBox} {z : ℂ} (hz : z ∈ C.closedBox) : z ∈ C.largeBox := by
  have a1 := abs_re_sub_center_le hz; have a2 := abs_im_sub_center_le hz
  have s0 := side_pos' C
  exact ⟨by linarith, by linarith⟩

/-- **`𝖢_{i,1}`, `𝖢_{i,2}`** (DZZ l. 1468–1470): the last cell of the enclosure before `𝖢` and the
first one after `𝖢` in the chain. -/
theorem exists_enc_split {N : ℕ} (hN : ∀ b, IsCell m δ b → b.n ≤ N) {ε : ℝ} (hε1 : ε ≤ 1)
    {u v : ℂ} (hgu : IsGoodPoint m δ ε u) (hgv : IsGoodPoint m δ ε v) {l : List DyBox}
    (hj : JoinsCells m δ u v l) (hch : l.IsChain Neighbour) {C : DyBox}
    (hC : C ∈ l312Bad ε l) (hCN : C.n + 1 ≤ N) {E : List DyBox}
    (hEc : ∀ c ∈ E, IsCell m δ c ∧ (c.closedBox ∩ (C.largeBox \ C.closedBox)).Nonempty)
    (henc : EnclosesBox C {c | c ∈ E}) :
    ∃ A M B : List DyBox, ∃ x y : DyBox, l = A ++ x :: (M ++ y :: B) ∧ C ∈ M ∧ x ∈ E ∧ y ∈ E ∧
      ∀ c ∈ M, c ∉ E := by
  obtain ⟨hne, hcells, hhead, hlast⟩ := hj
  have hCE : C ∉ E := not_mem_enc_self fun c hc => (hEc c hc).2
  have hE : ∀ c ∈ E, IsCell m δ c := fun c hc => (hEc c hc).1
  have huC := not_mem_largeBox_of_bad hε1 hcells hch hC hgu
  have hvC := not_mem_largeBox_of_bad hε1 hcells hch hC hgv
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem (mem_of_mem_l312Bad hC)
  -- the part before `𝖢`
  have h1 : ∃ c ∈ l₁, c ∈ E := by
    set L := C :: l₁.reverse
    have hLne : L ≠ [] := by simp [L]
    have hchL : L.IsChain Neighbour := by
      have hinf : l₁ ++ [C] <:+: l₁ ++ C :: l₂ := by
        simpa using (List.prefix_append (l₁ ++ [C]) l₂).isInfix
      have h0 : (l₁ ++ [C]).reverse.IsChain Neighbour :=
        List.isChain_reverse.2 ((hch.infix hinf).imp fun a b h => Neighbour.symm h)
      simpa [L, List.reverse_append] using h0
    cases l₁ with
    | nil =>
      exfalso; apply huC
      simp only [List.nil_append, List.head_cons] at hhead
      rw [← hhead.2]
      exact mem_largeBox_of_mem_self (mem_closedBox_boxAt hhead.1)
    | cons a t =>
      have hlastL : L.getLast hLne = a := by simp [L]
      obtain ⟨c, hcL, hcE⟩ := exists_mem_enc_of_chain hN hCN hE henc hLne hchL
        (fun c hc => hcells c (by simp [L] at hc ⊢; tauto)) rfl (w := u)
        (by rw [hlastL]; simpa using hhead) huC
      refine ⟨c, ?_, hcE⟩
      simp only [L, List.mem_cons, List.mem_reverse] at hcL
      rcases hcL with rfl | hcL
      · exact absurd hcE hCE
      · simpa using hcL
  -- the part after `𝖢`
  have h2 : ∃ c ∈ l₂, c ∈ E := by
    set L := C :: l₂
    have hLne : L ≠ [] := by simp [L]
    have hchL : L.IsChain Neighbour := hch.infix (List.suffix_append _ _).isInfix
    have hlastL : L.getLast hLne = (l₁ ++ C :: l₂).getLast hne := by
      simp only [L]; rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil C l₂)]
    obtain ⟨c, hcL, hcE⟩ := exists_mem_enc_of_chain hN hCN hE henc hLne hchL
      (fun c hc => hcells c (by simp [L] at hc ⊢; tauto)) rfl (w := v)
      (by rw [hlastL]; exact hlast) hvC
    refine ⟨c, ?_, hcE⟩
    rcases List.mem_cons.1 hcL with rfl | hcL
    · exact absurd hcE hCE
    · exact hcL
  obtain ⟨A, x, M₁, rfl, hx, hM₁⟩ := exists_last_split (P := fun c => c ∈ E) l₁ h1
  obtain ⟨M₂, y, B, rfl, hy, hM₂⟩ := exists_first_split (P := fun c => c ∈ E) l₂ h2
  refine ⟨A, M₁ ++ C :: M₂, B, x, y, by simp, by simp, hx, hy, fun c hc => ?_⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact hM₁ c hc
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact hCE
    · exact hM₂ c hc

/-- The cell graph restricted to the cells of a list. -/
def encGraph (m : DyBox → ℝ) (δ : ℝ) (E : List DyBox) : SimpleGraph DyBox where
  Adj a b := (cellGraph m δ).Adj a b ∧ a ∈ E ∧ b ∈ E
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => (cellGraph m δ).loopless.irrefl _ h.1⟩

lemma encGraph_reachable_head {E : List DyBox}
    (hch : E.IsChain (fun c c' => c = c' ∨ Neighbour c c')) (hE : ∀ c ∈ E, IsCell m δ c)
    (hne : E ≠ []) : ∀ c ∈ E, (encGraph m δ E).Reachable (E.head hne) c := by
  induction E with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hct
    · rfl
    · cases t with
      | nil => simp at hct
      | cons b t' =>
        rw [List.isChain_cons_cons] at hch
        have hab : (encGraph m δ (a :: b :: t')).Reachable a b := by
          rcases hch.1 with e | hN
          · rw [e]
          · exact SimpleGraph.Adj.reachable
              ⟨⟨hE a (by simp), hE b (by simp), hN⟩, by simp, by simp⟩
        have hrec := ih hch.2 (fun d hd => hE d (List.mem_cons_of_mem _ hd)) (by simp) c hct
        have hmono : (encGraph m δ (b :: t')) ≤ (encGraph m δ (a :: b :: t')) :=
          fun d e h => ⟨h.1, List.mem_cons_of_mem _ h.2.1, List.mem_cons_of_mem _ h.2.2⟩
        exact hab.trans (hrec.mono hmono)

lemma encGraph_support_sub {E : List DyBox} {a : DyBox} (ha : a ∈ E) :
    ∀ {b : DyBox} (p : (encGraph m δ E).Walk a b), ∀ c ∈ p.support, c ∈ E := by
  intro b p
  induction p with
  | nil => intro c hc; simp at hc; rw [hc]; exact ha
  | cons h q ih =>
    intro c hc
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact h.2.1
    · exact ih h.2.2 c hc

lemma list_eq_head_mid_last {L : List DyBox} {x y : DyBox} (hne : L ≠ []) (hh : L.head hne = x)
    (hl : L.getLast hne = y) (hxy : x ≠ y) : L = x :: (L.tail.dropLast ++ [y]) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.head_cons] at hh
  subst hh
  have ht : t ≠ [] := by rintro rfl; exact hxy hl
  rw [List.getLast_cons ht] at hl
  simp only [List.tail_cons, List.cons.injEq, true_and]
  rw [← hl, List.dropLast_append_getLast ht]

/-- **A loop-free segment of an enclosure** joining two of its cells (the segments of
`𝒞_{i,cross}` in DZZ l. 1470–1477). -/
theorem exists_enc_path {E : List DyBox}
    (hch : E.IsChain (fun c c' => c = c' ∨ Neighbour c c')) (hE : ∀ c ∈ E, IsCell m δ c)
    {x y : DyBox} (hx : x ∈ E) (hy : y ∈ E) (hxy : x ≠ y) :
    ∃ R : List DyBox, (x :: R ++ [y]).IsChain Neighbour ∧ (x :: R ++ [y]).Nodup ∧
      ∀ c ∈ R, c ∈ E := by
  have hne : E ≠ [] := List.ne_nil_of_mem hx
  have hr := (encGraph_reachable_head hch hE hne x hx).symm.trans
    (encGraph_reachable_head hch hE hne y hy)
  obtain ⟨p₀⟩ := hr
  set p := p₀.bypass
  have hpath := p₀.bypass_isPath
  have hsupp : ∀ c ∈ p.support, c ∈ E := encGraph_support_sub hx p
  have hdec : p.support = x :: (p.support.tail.dropLast ++ [y]) :=
    list_eq_head_mid_last (by simp) (SimpleGraph.Walk.head_support p)
      (SimpleGraph.Walk.getLast_support p) hxy
  refine ⟨p.support.tail.dropLast, ?_, ?_, fun c hc => hsupp c ?_⟩
  · rw [List.cons_append, ← hdec]
    exact (SimpleGraph.Walk.isChain_adj_support p).imp fun a b h => h.1.2.2
  · rw [List.cons_append, ← hdec]; exact hpath.support_nodup
  · rw [hdec]; simp [hc]

end DZZ
end LQGMetric
