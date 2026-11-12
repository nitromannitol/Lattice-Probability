/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.AnnulusClipMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusClip

/-!
# Peierls bound for good enclosures of a square annulus clipped to a rectangle

`perc_annulus_peierls_clip` (decision D72): the analogue of `perc_annulus_peierls` for the
annulus `n ≤ ‖z‖_∞ ≤ N` clipped to the rectangle `R = annClip ext`, when in each axis `R`
reaches past the annulus on at least one side (`hTB`, `hRL`; DZZ's `m ≥ 1`, arXiv:1807.00422,
`LBM_LGDarXiv.tex` l. 1009–1016, where the enclosure "separates `B` from `𝕍 ∩ ∂B_large` in `𝕍`").

Route (as for `perc_annulus_enclosure`: Grimmett, *Percolation*, 2nd ed., §11.7, circuits from
rectangle crossings): for every *active* side `d` (`N < ext d`) the side rectangle clipped to `R`
is `clipRect n N d (clipLo N ext d) (clipHi N ext d)`; its long-way good crossing exists outside
an event of probability `≤ (2N+1)(8θ)^(N-n+1)` (`perc_clipRect_peierls`). Every active vertical
side meets every active horizontal side in a corner (`clip_corner`), so, since one side of each
axis is active, the active crossings lie in one `4`-cluster `U` of `G ∩ R ∩ annulus`; a `*`-path
in `R` from the hole to the outside crosses some active side rectangle the short way
(`PercClip.ann_exit_clip`) and so meets `U` (`clipRect_meet`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

namespace LQGMetric

namespace PercClip

/-- The side of `R` bounding the long coordinate of side `d` from below. -/
def clipLoDir : PercDir → PercDir
  | .T => .L
  | .B => .L
  | .R => .B
  | .L => .B

/-- The side of `R` bounding the long coordinate of side `d` from above. -/
def clipHiDir : PercDir → PercDir
  | .T => .R
  | .B => .R
  | .R => .T
  | .L => .T

/-- Lower end of the long coordinate of the side rectangle `d` clipped to `R`. -/
def clipLo (N : ℤ) (ext : PercDir → ℤ) (d : PercDir) : ℤ := max (-N) (-ext (clipLoDir d))

/-- Upper end of the long coordinate of the side rectangle `d` clipped to `R`. -/
def clipHi (N : ℤ) (ext : PercDir → ℤ) (d : PercDir) : ℤ := min N (ext (clipHiDir d))

/-- The clipped side rectangle of side `d`. -/
abbrev clipX (n N : ℤ) (ext : PercDir → ℤ) (d : PercDir) : Set (ℤ × ℤ) :=
  clipRect n N d (clipLo N ext d) (clipHi N ext d)

lemma clipX_sub {n N : ℤ} (hn : 0 ≤ n) (hnN : n ≤ N) {ext : PercDir → ℤ} (hext : ∀ d, -n ≤ ext d) {d : PercDir}
    (hd : N < ext d) {z : ℤ × ℤ} (hz : z ∈ clipX n N ext d) :
    annClip ext z ∧ z ∈ annRect n N d := by
  have h1 := hext .T; have h2 := hext .B; have h3 := hext .R; have h4 := hext .L
  obtain ⟨z1, z2, z3, z4⟩ := hz
  refine ⟨fun d' => ?_, ?_⟩ <;> cases d <;> (try cases d') <;>
    simp only [clipLo, clipHi, clipLoDir, clipHiDir, annLong, annDir, annRect, annBox,
      Set.mem_ofPred_eq] at z1 z2 z3 z4 hd ⊢ <;> omega

lemma mem_clipX {n N : ℤ} {ext : PercDir → ℤ} {d : PercDir} {z : ℤ × ℤ}
    (hz : z ∈ annRect n N d) (hR : annClip ext z) : z ∈ clipX n N ext d := by
  obtain ⟨⟨b1, b2, b3, b4⟩, h⟩ := hz
  have r1 := hR .T; have r2 := hR .B; have r3 := hR .R; have r4 := hR .L
  cases d <;> simp only [clipX, clipRect, clipLo, clipHi, clipLoDir, clipHiDir, annLong, annDir,
    Set.mem_ofPred_eq] at h r1 r2 r3 r4 ⊢ <;> omega

/-- The part of a perpendicular active clipped rectangle beyond level `n` of side `d` lies in
the clipped rectangle of `d`. -/
lemma clipX_corner_sub {n N : ℤ} (hn : 0 ≤ n) (hnN : n ≤ N) {ext : PercDir → ℤ} (hext : ∀ d, -n ≤ ext d)
    {d e : PercDir} (hd : d = .T ∨ d = .B) (he : e = .R ∨ e = .L) (hda : N < ext d)
    (hea : N < ext e) {z : ℤ × ℤ} (hz : z ∈ clipX n N ext e) (hzd : n ≤ annDir d z) :
    z ∈ clipX n N ext d := by
  have h1 := hext .T; have h2 := hext .B; have h3 := hext .R; have h4 := hext .L
  obtain ⟨z1, z2, z3, z4⟩ := hz
  rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;>
    simp only [clipX, clipRect, clipLo, clipHi, clipLoDir, clipHiDir, annLong, annDir,
      Set.mem_ofPred_eq] at z1 z2 z3 z4 hzd hda hea ⊢ <;> omega

/-- A long-way crossing of an active horizontal clipped rectangle `e` contains, from one of its
points on the far side of the vertical active side `d`, a short-way crossing of the corner. -/
lemma clip_corner_short {n N : ℤ} (hn : 0 ≤ n) (hnN : n ≤ N) {ext : PercDir → ℤ} (hext : ∀ d, -n ≤ ext d)
    {d e : PercDir} (hd : d = .T ∨ d = .B) (he : e = .R ∨ e = .L) (hda : N < ext d)
    (S : Set (ℤ × ℤ)) {a b : ℤ × ℤ} (ha : annLong e a = clipLo N ext e)
    (hb : annLong e b = clipHi N ext e) (hab : Relation.ReflTransGen (PercStepIn S PercAdj4) a b) :
    ∃ p, annDir d p = N ∧ Relation.ReflTransGen (PercStepIn S PercAdj4) a p ∧ ∃ c,
      annDir d c = n ∧ Relation.ReflTransGen (PercStepIn {z | z ∈ S ∧ n ≤ annDir d z} PercAdj4) p c := by
  have h1 := hext .T; have h2 := hext .B; have h3 := hext .R; have h4 := hext .L
  have hs4 : ∀ x y, PercAdj4 x y → PercAdj4 y x := fun x y h => percAdj4_symm h
  have hlev := fun (d : PercDir) x y (h : PercAdj4 x y) => annDir_adjK d (percAdjK_of_adj4 h)
  rcases hd with rfl | rfl
  · -- `p = b`
    have hbN : annDir .T b = N := by
      rcases he with rfl | rfl <;> simp only [clipHi, clipHiDir, annLong, annDir] at hb hda ⊢ <;>
        omega
    have han : annDir .T a ≤ n := by
      rcases he with rfl | rfl <;> simp only [clipLo, clipLoDir, annLong, annDir] at ha ⊢ <;>
        omega
    exact ⟨b, hbN, hab, perc_first_reach (annDir .T) (hlev .T) n (percStepIn_rev hs4 hab)
      (by omega) han⟩
  · -- `p = a`
    have haN : annDir .B a = N := by
      rcases he with rfl | rfl <;> simp only [clipLo, clipLoDir, annLong, annDir] at ha hda ⊢ <;>
        omega
    have hbn : annDir .B b ≤ n := by
      rcases he with rfl | rfl <;> simp only [clipHi, clipHiDir, annLong, annDir] at hb ⊢ <;>
        omega
    exact ⟨a, haN, .refl, perc_first_reach (annDir .B) (hlev .B) n hab (by omega) hbn⟩

open PercAnn in
/-- Corner: the long-way crossings of an active vertical side `d` and an active horizontal side
`e` (clipped to `R`) lie in one `4`-cluster of `W ⊇ G ∩ (active clipped rectangles)`. -/
lemma clip_corner {n N : ℤ} (hn : 0 ≤ n) (hnN : n ≤ N) {ext : PercDir → ℤ}
    (hext : ∀ d, -n ≤ ext d) {d e : PercDir} (hd : d = .T ∨ d = .B) (he : e = .R ∨ e = .L)
    (hda : N < ext d) (hea : N < ext e) (G W : Set (ℤ × ℤ))
    (hXW : ∀ d', N < ext d' → ∀ z, z ∈ {z | z ∈ clipX n N ext d' ∧ z ∈ G} → z ∈ W)
    {ad bd ae be : ℤ × ℤ} (had : annLong d ad = clipLo N ext d) (hbd : annLong d bd = clipHi N ext d)
    (hadX : ad ∈ clipX n N ext d)
    (hpd : Relation.ReflTransGen (PercStepIn {z | z ∈ clipX n N ext d ∧ z ∈ G} PercAdj4) ad bd)
    (hae : annLong e ae = clipLo N ext e) (hbe : annLong e be = clipHi N ext e)
    (haeX : ae ∈ clipX n N ext e) (haeG : ae ∈ G)
    (hpe : Relation.ReflTransGen (PercStepIn {z | z ∈ clipX n N ext e ∧ z ∈ G} PercAdj4) ae be) :
    Relation.ReflTransGen (PercStepIn W PercAdj4) ad ae := by
  have hs4 : ∀ x y, PercAdj4 x y → PercAdj4 y x := fun x y h => percAdj4_symm h
  obtain ⟨p, hpN, hap, c, hc, hpc⟩ := clip_corner_short hn hnN hext hd he hda _ hae hbe hpe
  have hpS := rtg_end_mem hap ⟨haeX, haeG⟩
  have hpX : p ∈ clipX n N ext d := clipX_corner_sub hn hnN hext hd he hda hea hpS.1 (by omega)
  have hshort := rtg_reach (W := W) (fun z hz => hXW e hea z hz.1) hpc
  have hlong := rtg_reach (W := W) (hXW d hda) hpd
  obtain ⟨w, -, hwA, hwC⟩ := clipRect_meet n N d _ _
    {z | Relation.ReflTransGen (PercStepIn W PercAdj4) ad z}
    {z | Relation.ReflTransGen (PercStepIn W PercAdj4) p z}
    ⟨ad, bd, had, hbd, hadX, .refl, percStepIn_mono (S' := {z | z ∈ clipX n N ext d ∧
      z ∈ {z | Relation.ReflTransGen (PercStepIn W PercAdj4) ad z}}) (fun z hz => ⟨hz.1.1, hz.2⟩)
      (fun _ _ h => h) hlong⟩
    ⟨p, c, hpN, hc, hpX, .refl, percStepIn_mono (S' := {z | z ∈ clipX n N ext d ∧
      z ∈ {z | Relation.ReflTransGen (PercStepIn W PercAdj4) p z}})
      (fun z hz => ⟨clipX_corner_sub hn hnN hext hd he hda hea hz.1.1.1 hz.1.2, hz.2⟩)
      (fun _ _ h => percAdjK_of_adj4 h) hshort⟩
  exact hwA.trans ((percStepIn_rev hs4 hwC).trans
    (percStepIn_mono (hXW e hea) (fun _ _ h => h) (percStepIn_rev hs4 hap)))

end PercClip

open PercClip PercAnn in
/-- **Good enclosure** of a square annulus clipped to `R` from the long-way crossings of the
active clipped side rectangles. -/
theorem perc_annulus_enclosure_clip (n N : ℤ) (hn : 1 ≤ n) (hnN : n ≤ N) (ext : PercDir → ℤ)
    (hext : ∀ d, -n ≤ ext d) (hTB : N < ext .T ∨ N < ext .B) (hRL : N < ext .R ∨ N < ext .L)
    (G : Set (ℤ × ℤ))
    (hcross : ∀ d, N < ext d → PercClipCross n N d (clipLo N ext d) (clipHi N ext d) G) :
    PercEnclosureClip n N ext G := by
  have hn0 : 0 ≤ n := by omega
  have hs4 : ∀ x y, PercAdj4 x y → PercAdj4 y x := fun x y h => percAdj4_symm h
  set W : Set (ℤ × ℤ) := {z | (∃ d, N < ext d ∧ z ∈ clipX n N ext d) ∧ z ∈ G} with hW
  have hXW : ∀ d', N < ext d' → ∀ z, z ∈ {z | z ∈ clipX n N ext d' ∧ z ∈ G} → z ∈ W :=
    fun d' hd' z hz => ⟨⟨d', hd', hz.1⟩, hz.2⟩
  obtain ⟨d0, hd0, hd0a⟩ : ∃ d0 : PercDir, (d0 = .T ∨ d0 = .B) ∧ N < ext d0 := by
    rcases hTB with h | h
    · exact ⟨.T, Or.inl rfl, h⟩
    · exact ⟨.B, Or.inr rfl, h⟩
  obtain ⟨e0, he0, he0a⟩ : ∃ e0 : PercDir, (e0 = .R ∨ e0 = .L) ∧ N < ext e0 := by
    rcases hRL with h | h
    · exact ⟨.R, Or.inl rfl, h⟩
    · exact ⟨.L, Or.inr rfl, h⟩
  obtain ⟨a0, b0, ha0, hb0, ha0X, ha0G, hp0⟩ := hcross d0 hd0a
  obtain ⟨ae, be, hae, hbe, haeX, haeG, hpe⟩ := hcross e0 he0a
  set U : Set (ℤ × ℤ) := {z | Relation.ReflTransGen (PercStepIn W PercAdj4) a0 z} with hU
  have hUW : ∀ z ∈ U, z ∈ W := fun z hz => rtg_end_mem hz ⟨⟨d0, hd0a, ha0X⟩, ha0G⟩
  have hUclosed : ∀ x y, x ∈ U → Relation.ReflTransGen (PercStepIn W PercAdj4) x y → y ∈ U :=
    fun x y hx hxy => hx.trans hxy
  have h0e : a0 ∈ U → ae ∈ U := fun h => hUclosed a0 ae h
    (clip_corner hn0 hnN hext hd0 he0 hd0a he0a G W hXW ha0 hb0 ha0X hp0 hae hbe haeX haeG hpe)
  have haeU : ae ∈ U := h0e .refl
  -- every active crossing starts in `U`
  have hstart : ∀ d, N < ext d → ∀ a b, annLong d a = clipLo N ext d →
      annLong d b = clipHi N ext d → a ∈ clipX n N ext d → a ∈ G →
      Relation.ReflTransGen (PercStepIn {z | z ∈ clipX n N ext d ∧ z ∈ G} PercAdj4) a b →
      a ∈ U := by
    intro d hda a b ha hb haX haG hab
    have hvert : (d = .T ∨ d = .B) → a ∈ U := fun hd => hUclosed ae a haeU
      (percStepIn_rev hs4 (clip_corner hn0 hnN hext hd he0 hda he0a G W hXW ha hb haX hab hae
        hbe haeX haeG hpe))
    have hhor : (d = .R ∨ d = .L) → a ∈ U := fun hd => hUclosed a0 a .refl
      (clip_corner hn0 hnN hext hd0 hd hd0a hda G W hXW ha0 hb0 ha0X hp0 ha hb haX haG hab)
    cases d
    · exact hvert (Or.inl rfl)
    · exact hvert (Or.inr rfl)
    · exact hhor (Or.inl rfl)
    · exact hhor (Or.inr rfl)
  have hin : ∀ d, N < ext d → ∀ a b, a ∈ U →
      Relation.ReflTransGen (PercStepIn {z | z ∈ clipX n N ext d ∧ z ∈ G} PercAdj4) a b →
      Relation.ReflTransGen (PercStepIn {z | z ∈ clipX n N ext d ∧ z ∈ U} PercAdj4) a b :=
    fun d hda a b ha h => percStepIn_mono (S' := {z | z ∈ clipX n N ext d ∧ z ∈ U})
      (fun z hz => ⟨hz.1.1, hUclosed a z ha hz.2⟩) (fun _ _ h => h) (rtg_reach (hXW d hda) h)
  refine ⟨U, fun z hz => ?_, ⟨a0, .refl⟩, ?_, ?_⟩
  · obtain ⟨⟨d, hda, hzX⟩, hzG⟩ := hUW z hz
    obtain ⟨h1, h2⟩ := clipX_sub hn0 hnN hext hda hzX
    exact ⟨hzG, h1, d, h2⟩
  · -- `U` is `4`-connected
    have hconn : ∀ z ∈ U, Relation.ReflTransGen (PercStepIn U PercAdj4) a0 z := by
      intro z hz
      have := rtg_reach (S := W) (W := W) (fun _ h => h) hz
      exact percStepIn_mono (fun y hy => hy.2) (fun _ _ h => h) this
    intro x hx y hy
    exact (percStepIn_rev hs4 (hconn x hx)).trans (hconn y hy)
  · -- `U` meets every `*`-path in `R` from the hole to the outside
    intro Γ s e hΓ hs he hse
    obtain ⟨d, c, e', hda, hc, he', hcX, hcΓ, hce⟩ := ann_exit_clip n N hnN ext Γ hΓ hs he hse
    obtain ⟨a, b, ha, hb, haX, haG, hab⟩ := hcross d hda
    have haU := hstart d hda a b ha hb haX haG hab
    have he'm := rtg_end_mem hce ⟨hcX, hcΓ⟩
    obtain ⟨z, -, hzU, hzΓ⟩ := clipRect_meet n N d _ _ U Γ
      ⟨a, b, ha, hb, haX, haU, hin d hda a b haU hab⟩
      ⟨e', c, he', hc, mem_clipX he'm.1 (hΓ e' he'm.2), he'm.2,
        percStepIn_rev (fun x y h => by simp only [PercAdjK] at h ⊢; omega)
          (percStepIn_mono (S' := {z | z ∈ clipX n N ext d ∧ z ∈ Γ})
            (fun z hz => ⟨mem_clipX hz.1 (hΓ z hz.2), hz.2⟩) (fun _ _ h => h)
            hce)⟩
    exact ⟨z, hzU, hzΓ⟩

end LQGMetric
