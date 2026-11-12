/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.AnnulusMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.Annulus

/-!
# Good enclosures in a square annulus of boxes

`perc_annulus_enclosure`: in the annulus `n ≤ ‖z‖_∞ ≤ N` (`1 ≤ n ≤ N`), if each of the four
rectangles `annRect n N d` has a long-way crossing by a `4`-path of sites of `G`, there is a
`4`-connected set `U ⊆ G` of annulus sites ("good enclosure") that every `*`-path from the hole
`‖z‖_∞ < n` to the outside `‖z‖_∞ > N` meets.

This is the enclosure used by Ding–Zhang–Zeitouni (arXiv:1807.00422, proof of Lemma 3.7,
`LBM_LGDarXiv.tex` lines 1009–1016: "an open enclosure of `B`, i.e., a sequence of neighboring
boxes … enclosing `B`"; the union of enclosures along the cells of a path then contains a path)
and, as circuits in annuli built from rectangle crossings, by Ding–Dunlap (arXiv:1812.06921,
proof of Prop. 4.2, Fig. 4: "circuits around `𝔸_{ω_j}` … joined together") and DDDF
(arXiv:1904.08021 Prop. 4.18 step 1, Fig. 3, four `3 × 1` rectangles around a square).

Route: DZZ derive the enclosure from a direct annulus duality ("by duality, there exists a
sequence of [closed] boxes joining `∂B` and `∂B_large`"). We instead glue the long-way
crossings of the four rectangles (the standard construction of circuits from rectangle
crossings, e.g. Grimmett, *Percolation*, 2nd ed., §11.7, and DDLGD Fig. 4): adjacent crossings
meet by `annRect_meet`, and a `*`-path from the hole to the outside contains a short-way
crossing of one rectangle (last entry into `{annDir d ≥ n}` before the exit through side `d`),
which meets that rectangle's long-way crossing. The failure event is then contained in the
union of the four "no long-way crossing" events, each bounded by `perc_peierls`
(DEVIATIONS: rectangle route instead of DZZ's annulus duality; same bound up to constants).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

namespace PercAnn

lemma rtg_end_mem {S : Set (ℤ × ℤ)} {adj : ℤ × ℤ → ℤ × ℤ → Prop} {a b : ℤ × ℤ}
    (h : Relation.ReflTransGen (PercStepIn S adj) a b) (ha : a ∈ S) : b ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ hs _ => exact hs.2.1

/-- Every site of a path inside `S ⊆ W` is reachable from its start inside `W`. -/
lemma rtg_reach {S W : Set (ℤ × ℤ)} (hSW : ∀ z, z ∈ S → z ∈ W) {a b : ℤ × ℤ}
    (h : Relation.ReflTransGen (PercStepIn S PercAdj4) a b) :
    Relation.ReflTransGen
      (PercStepIn {z | z ∈ S ∧ Relation.ReflTransGen (PercStepIn W PercAdj4) a z} PercAdj4) a b := by
  have key : Relation.ReflTransGen (PercStepIn W PercAdj4) a b ∧ Relation.ReflTransGen
      (PercStepIn {z | z ∈ S ∧ Relation.ReflTransGen (PercStepIn W PercAdj4) a z} PercAdj4) a b := by
    induction h with
    | refl => exact ⟨.refl, .refl⟩
    | @tail c z _ hs ih =>
      have hcz : Relation.ReflTransGen (PercStepIn W PercAdj4) a z :=
        ih.1.tail ⟨hSW c hs.1, hSW z hs.2.1, hs.2.2⟩
      exact ⟨hcz, ih.2.tail ⟨⟨hs.1, ih.1⟩, ⟨hs.2.1, hcz⟩, hs.2.2⟩⟩
  exact key.2

lemma annBox_dir {N : ℤ} {z : ℤ × ℤ} (h : annBox N z) (d : PercDir) : annDir d z ≤ N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases d <;> simp only [annDir] <;> omega

lemma exists_dir_of_not_annBox {N : ℤ} {z : ℤ × ℤ} (h : ¬ annBox N z) :
    ∃ d, N < annDir d z := by
  by_contra hc
  push Not at hc
  have h1 := hc .T
  have h2 := hc .B
  have h3 := hc .R
  have h4 := hc .L
  simp only [annDir] at h1 h2 h3 h4
  exact h ⟨by omega, h3, by omega, h1⟩

/-- A `*`-path from the hole to the outside contains a short-way crossing of a rectangle. -/
lemma ann_exit (n N : ℤ) (hnN : n ≤ N) (Γ : Set (ℤ × ℤ)) {s e : ℤ × ℤ}
    (hs : -n < s.1 ∧ s.1 < n ∧ -n < s.2 ∧ s.2 < n) (he : ¬ annBox N e)
    (hse : Relation.ReflTransGen (PercStepIn Γ PercAdjK) s e) :
    ∃ d c e', annDir d c = n ∧ annDir d e' = N ∧ c ∈ annRect n N d ∧ c ∈ Γ ∧
      Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ Γ} PercAdjK) c e' := by
  have key : (annBox N e ∧ ∀ d, annDir d e ≤ n ∨ ∃ c, annDir d c = n ∧ c ∈ annRect n N d ∧
      c ∈ Γ ∧ Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ Γ} PercAdjK) c e) ∨
      ∃ d c e', annDir d c = n ∧ annDir d e' = N ∧ c ∈ annRect n N d ∧ c ∈ Γ ∧
        Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ Γ} PercAdjK) c e' := by
    clear he
    induction hse with
    | refl =>
      refine Or.inl ⟨⟨by omega, by omega, by omega, by omega⟩, fun d => Or.inl ?_⟩
      cases d <;> simp only [annDir] <;> omega
    | @tail z z' _ hst ih =>
      rcases ih with ⟨hbox, hd⟩ | hr
      · have hadj := hst.2.2
        by_cases hb' : annBox N z'
        · refine Or.inl ⟨hb', fun d => ?_⟩
          have hdd := annDir_adjK d hadj
          by_cases hz' : annDir d z' ≤ n
          · exact Or.inl hz'
          · have hz'X : z' ∈ annRect n N d := ⟨hb', by omega⟩
            rcases hd d with h | ⟨c, hc, hcX, hcΓ, hcz⟩
            · have hzX : z ∈ annRect n N d := ⟨hbox, by omega⟩
              exact Or.inr ⟨z, by omega, hzX, hst.1,
                Relation.ReflTransGen.single ⟨⟨hzX, hst.1⟩, ⟨hz'X, hst.2.1⟩, hadj⟩⟩
            · have hzX := rtg_end_mem hcz ⟨hcX, hcΓ⟩
              exact Or.inr ⟨c, hc, hcX, hcΓ, hcz.tail ⟨hzX, ⟨hz'X, hst.2.1⟩, hadj⟩⟩
        · obtain ⟨d, hd'⟩ := exists_dir_of_not_annBox hb'
          have hdd := annDir_adjK d hadj
          have hzN := annBox_dir hbox d
          rcases hd d with h | ⟨c, hc, hcX, hcΓ, hcz⟩
          · exact Or.inr ⟨d, z, z, by omega, by omega, ⟨hbox, by omega⟩, hst.1, .refl⟩
          · exact Or.inr ⟨d, c, z, hc, by omega, hcX, hcΓ, hcz⟩
      · exact Or.inr hr
  rcases key with ⟨hb, -⟩ | hr
  · exact absurd hb he
  · exact hr

end PercAnn

open PercAnn in
/-- **Good enclosure** of a square annulus from long-way crossings of its four rectangles. -/
theorem perc_annulus_enclosure (n N : ℤ) (hn : 1 ≤ n) (hnN : n ≤ N) (G : Set (ℤ × ℤ))
    (hcross : ∀ d, ∃ a b, annLong d a = -N ∧ annLong d b = N ∧ a ∈ annRect n N d ∧ a ∈ G ∧
      Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ G} PercAdj4) a b) :
    ∃ U : Set (ℤ × ℤ), (∀ z ∈ U, z ∈ G ∧ ∃ d, z ∈ annRect n N d) ∧ U.Nonempty ∧
      (∀ x ∈ U, ∀ y ∈ U, Relation.ReflTransGen (PercStepIn U PercAdj4) x y) ∧
      (∀ (Γ : Set (ℤ × ℤ)) (s e : ℤ × ℤ), (-n < s.1 ∧ s.1 < n ∧ -n < s.2 ∧ s.2 < n) →
        ¬ annBox N e → Relation.ReflTransGen (PercStepIn Γ PercAdjK) s e → ∃ z ∈ U, z ∈ Γ) := by
  set W : Set (ℤ × ℤ) := {z | (∃ d, z ∈ annRect n N d) ∧ z ∈ G} with hW
  have hXW : ∀ d, ∀ z, z ∈ {z | z ∈ annRect n N d ∧ z ∈ G} → z ∈ W :=
    fun d z hz => ⟨⟨d, hz.1⟩, hz.2⟩
  obtain ⟨aT, bT, haT, hbT, haTX, haTG, hTp⟩ := hcross .T
  set U : Set (ℤ × ℤ) := {z | Relation.ReflTransGen (PercStepIn W PercAdj4) aT z} with hU
  have hUW : ∀ z ∈ U, z ∈ W := fun z hz => rtg_end_mem hz ⟨⟨.T, haTX⟩, haTG⟩
  have hUclosed : ∀ x y, x ∈ U → Relation.ReflTransGen (PercStepIn W PercAdj4) x y → y ∈ U :=
    fun x y hx hxy => hx.trans hxy
  have hsymm4 : ∀ x y, PercAdj4 x y → PercAdj4 y x := fun x y h => percAdj4_symm h
  -- a crossing starting in `U` lies in `U`
  have hin : ∀ d a b, a ∈ U →
      Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ G} PercAdj4) a b →
      Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ U} PercAdj4) a b := by
    intro d a b ha h
    exact percStepIn_mono (S' := {z | z ∈ annRect n N d ∧ z ∈ U})
      (fun z hz => ⟨hz.1.1, hUclosed a z ha hz.2⟩) (fun _ _ h => h)
      (rtg_reach (hXW d) h)
  -- corners: the R and L crossings meet the T crossing
  have hside : ∀ d, (d = .R ∨ d = .L) → ∀ a b, annLong d a = -N → annLong d b = N →
      a ∈ annRect n N d → a ∈ G →
      Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ G} PercAdj4) a b →
      a ∈ U := by
    intro d hd a b ha hb haX haG hab
    have hba := percStepIn_rev hsymm4 hab
    have hbX := rtg_end_mem hab ⟨haX, haG⟩
    obtain ⟨c, hc, hbc⟩ := perc_first_reach (annDir .T)
      (fun x y h => annDir_adjK .T (percAdjK_of_adj4 h)) n hba
      (by rcases hd with rfl | rfl <;> simp only [annDir, annLong] at hb ⊢ <;> omega)
      (by rcases hd with rfl | rfl <;> simp only [annDir, annLong] at ha ⊢ <;> omega)
    have hbc' := rtg_reach (W := W) (fun z hz => hXW d z hz.1) hbc
    obtain ⟨w, -, hwU, hwC⟩ := annRect_meet n N .T U
      {z | Relation.ReflTransGen (PercStepIn W PercAdj4) b z}
      ⟨aT, bT, haT, hbT, haTX, .refl, hin .T aT bT .refl hTp⟩
      ⟨b, c, by rcases hd with rfl | rfl <;> simp only [annDir, annLong] at hb ⊢ <;> omega, hc,
        ⟨hbX.1.1, by rcases hd with rfl | rfl <;> simp only [annDir, annLong] at hb ⊢ <;> omega⟩,
        .refl,
        percStepIn_mono (S' := {z | z ∈ annRect n N .T ∧
          z ∈ {z | Relation.ReflTransGen (PercStepIn W PercAdj4) b z}})
          (fun z hz => ⟨⟨hz.1.1.1.1, hz.1.2⟩, hz.2⟩)
          (fun _ _ h => percAdjK_of_adj4 h) hbc'⟩
    have hbU : b ∈ U := hUclosed w b hwU (percStepIn_rev hsymm4 hwC)
    exact hUclosed b a hbU (percStepIn_mono (hXW d) (fun _ _ h => h) hba)
  have hU' : ∀ d, ∃ a b, annLong d a = -N ∧ annLong d b = N ∧ a ∈ annRect n N d ∧ a ∈ U ∧
      Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N d ∧ z ∈ U} PercAdj4) a b := by
    have hL : ∃ a b, annLong .L a = -N ∧ annLong .L b = N ∧ a ∈ annRect n N .L ∧ a ∈ U ∧
        Relation.ReflTransGen (PercStepIn {z | z ∈ annRect n N .L ∧ z ∈ U} PercAdj4) a b := by
      obtain ⟨a, b, ha, hb, haX, haG, hab⟩ := hcross .L
      have haU := hside .L (Or.inr rfl) a b ha hb haX haG hab
      exact ⟨a, b, ha, hb, haX, haU, hin .L a b haU hab⟩
    intro d
    cases d with
    | T => exact ⟨aT, bT, haT, hbT, haTX, .refl, hin .T aT bT .refl hTp⟩
    | R =>
      obtain ⟨a, b, ha, hb, haX, haG, hab⟩ := hcross .R
      have haU := hside .R (Or.inl rfl) a b ha hb haX haG hab
      exact ⟨a, b, ha, hb, haX, haU, hin .R a b haU hab⟩
    | L => exact hL
    | B =>
      obtain ⟨a, b, ha, hb, haX, haG, hab⟩ := hcross .B
      obtain ⟨aL, bL, haL, hbL, haLX, haLU, hLp⟩ := hL
      obtain ⟨c, hc, hac⟩ := perc_first_reach (annDir .B)
        (fun x y h => annDir_adjK .B (percAdjK_of_adj4 h)) n hLp
        (by simp only [annDir, annLong] at haL ⊢; omega)
        (by simp only [annDir, annLong] at hbL ⊢; omega)
      obtain ⟨w, -, hwA, hwU⟩ := annRect_meet n N .B
        {z | Relation.ReflTransGen (PercStepIn W PercAdj4) a z} U
        ⟨a, b, ha, hb, haX, .refl, percStepIn_mono (S' := {z | z ∈ annRect n N .B ∧
          z ∈ {z | Relation.ReflTransGen (PercStepIn W PercAdj4) a z}}) (fun z hz => ⟨hz.1.1, hz.2⟩)
          (fun _ _ h => h) (rtg_reach (hXW .B) hab)⟩
        ⟨aL, c, by simp only [annDir, annLong] at haL ⊢; omega, hc,
          ⟨haLX.1, by simp only [annDir, annLong] at haL ⊢; omega⟩, haLU,
          percStepIn_mono (S' := {z | z ∈ annRect n N .B ∧ z ∈ U})
            (fun z hz => ⟨⟨hz.1.1.1, hz.2⟩, hz.1.2⟩)
            (fun _ _ h => percAdjK_of_adj4 h) hac⟩
      have haU : a ∈ U := hUclosed w a hwU (percStepIn_rev hsymm4 hwA)
      exact ⟨a, b, ha, hb, haX, haU, hin .B a b haU hab⟩
  refine ⟨U, fun z hz => ⟨(hUW z hz).2, (hUW z hz).1⟩, ⟨aT, .refl⟩, ?_, ?_⟩
  · -- `U` is `4`-connected
    have hconn : ∀ z ∈ U, Relation.ReflTransGen (PercStepIn U PercAdj4) aT z := by
      intro z hz
      have := rtg_reach (S := W) (W := W) (fun _ h => h) hz
      exact percStepIn_mono (fun y hy => hy.2) (fun _ _ h => h) this
    intro x hx y hy
    exact (percStepIn_rev hsymm4 (hconn x hx)).trans (hconn y hy)
  · -- `U` meets every `*`-path from the hole to the outside
    intro Γ s e hs he hse
    obtain ⟨d, c, e', hc, he', hcX, hcΓ, hce⟩ := ann_exit n N hnN Γ hs he hse
    obtain ⟨a, b, ha, hb, haX, haU, hab⟩ := hU' d
    obtain ⟨z, -, hzU, hzΓ⟩ := annRect_meet n N d U Γ ⟨a, b, ha, hb, haX, haU, hab⟩
      ⟨e', c, he', hc, rtg_end_mem hce ⟨hcX, hcΓ⟩ |>.1, (rtg_end_mem hce ⟨hcX, hcΓ⟩).2,
        percStepIn_rev (fun x y h => by simp only [PercAdjK] at h ⊢; omega) hce⟩
    exact ⟨z, hzU, hzΓ⟩


end LQGMetric
