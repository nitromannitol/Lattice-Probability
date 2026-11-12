/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.BlockConstructionAux4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.BlockConstructionAux3

/-!
# Node `B57`, auxiliary file 4: the recursive block rule

* `amin`: argmin over `Fin (K+1)` with the least index as tie-break (measurable selection).
* `DT K M k`: decision trees of depth `k` (a choice of profile at the root, and a depth-`k-1`
  tree in each of the `M` children).  Finite, with the discrete σ-algebra.
* `BParams`: the data `ξ, δ, ρ, M, N` and the profile enumeration `fe : Fin (K+1) → (ℝ → ℝ)`.
* `sim a i`: the edge similarity `T^{f_a}_i` (as `(α, β)`), `rr a i = |α|` its ratio;
  `tau a i`: its action `(a, b, z) ↦ (r a, r b, T z)` on triples.
* `Lsim k` (composite similarities), `S k` (Riemann points), `Qs k` (triples used at depth `k`).
* `polyOf k d`: the polygon of a decision tree; `dec k Y`: the rule (driven by the field
  `Y : Tri → ℝ`), which at depth `k+1` minimises `blockCost` over the root band with the
  deterministic expected occupation `Mw k` of the depth-`k` rule, then recurses in the children
  with the transformed field `Y ∘ tau a i`.
* Geometric invariants: endpoints, edges are `(L 0, L 1)` with `L ∈ Lsim k`, Riemann points in
  `S k`, edge lengths `≤ (2/M)^k`, tube bound, cardinality bounds.
* Triple invariants, locality and measurability of the rule.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension.BlockCons

open Blueprint.Draft

/-! ## Argmin with a fixed tie-breaking rule -/

theorem amin_ne {K : ℕ} (g : Fin (K + 1) → ℝ) :
    (Finset.univ.filter fun a => ∀ b, g a ≤ g b).Nonempty := by
  obtain ⟨a, -, ha⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
  exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun b => ha b (Finset.mem_univ _)⟩⟩

/-- The least minimiser. -/
def amin {K : ℕ} (g : Fin (K + 1) → ℝ) : Fin (K + 1) :=
  (Finset.univ.filter fun a => ∀ b, g a ≤ g b).min' (amin_ne g)

theorem amin_le {K : ℕ} (g : Fin (K + 1) → ℝ) (b : Fin (K + 1)) : g (amin g) ≤ g b :=
  (Finset.mem_filter.1 (Finset.min'_mem _ (amin_ne g))).2 b

theorem amin_eq_iff {K : ℕ} (g : Fin (K + 1) → ℝ) (a : Fin (K + 1)) :
    amin g = a ↔ (∀ b, g a ≤ g b) ∧ ∀ b, (∀ c, g b ≤ g c) → a ≤ b := by
  constructor
  · rintro rfl
    exact ⟨amin_le g, fun b hb => Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩)
    · exact h2 _ (amin_le g)

theorem iInf_eq_amin {K : ℕ} (g : Fin (K + 1) → ℝ) : ⨅ a, g a = g (amin g) :=
  le_antisymm (ciInf_le (Finite.bddBelow_range g) _) (le_ciInf (amin_le g))

theorem measurableSet_amin_eq {α : Type*} [MeasurableSpace α] {K : ℕ} (G : Fin (K + 1) → α → ℝ)
    (hG : ∀ a, Measurable (G a)) (a0 : Fin (K + 1)) :
    MeasurableSet {x | amin (fun a => G a x) = a0} := by
  have hset : ∀ b, MeasurableSet {x | ∀ c, G b x ≤ G c x} := by
    intro b
    have : {x | ∀ c, G b x ≤ G c x} = ⋂ c, {x | G b x ≤ G c x} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun c => measurableSet_le (hG b) (hG c)
  have : {x | amin (fun a => G a x) = a0} =
      {x | ∀ c, G a0 x ≤ G c x} ∩ ⋂ b, ({x | ∀ c, G b x ≤ G c x}ᶜ ∪ {_x | a0 ≤ b}) := by
    ext x
    simp only [mem_setOf_eq, amin_eq_iff, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun b => ?_⟩
      by_cases hb : ∀ c, G b x ≤ G c x
      · exact Or.inr (h2 b hb)
      · exact Or.inl hb
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun b hb => (h2 b).resolve_left (not_not.2 hb)⟩
  rw [this]
  refine (hset a0).inter (MeasurableSet.iInter fun b => (hset b).compl.union ?_)
  by_cases h : a0 ≤ b
  · simp [h]
  · simp [h]

/-! ## Decision trees -/

/-- Decision trees of depth `k`. -/
def DT (K M : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Fin (K + 1) × (Fin M → DT K M k)

instance instFintypeDT (K M : ℕ) : ∀ k, Fintype (DT K M k)
  | 0 => (inferInstance : Fintype Unit)
  | k + 1 => by
    haveI := instFintypeDT K M k
    exact (inferInstance : Fintype (Fin (K + 1) × (Fin M → DT K M k)))

instance instMeasurableSpaceDT (K M k : ℕ) : MeasurableSpace (DT K M k) := ⊤

instance (K M k : ℕ) : MeasurableSingletonClass (DT K M k) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The depth-0 tree. -/
def DT.leaf {K M : ℕ} : DT K M 0 := ()

def DT.mk {K M k : ℕ} (a : Fin (K + 1)) (c : Fin M → DT K M k) : DT K M (k + 1) := (a, c)

def DT.fst {K M k : ℕ} (d : DT K M (k + 1)) : Fin (K + 1) :=
  (d : Fin (K + 1) × (Fin M → DT K M k)).1

def DT.snd {K M k : ℕ} (d : DT K M (k + 1)) : Fin M → DT K M k :=
  (d : Fin (K + 1) × (Fin M → DT K M k)).2

@[simp] theorem DT.fst_mk {K M k : ℕ} (a : Fin (K + 1)) (c : Fin M → DT K M k) :
    (DT.mk a c).fst = a := rfl

@[simp] theorem DT.snd_mk {K M k : ℕ} (a : Fin (K + 1)) (c : Fin M → DT K M k) :
    (DT.mk a c).snd = c := rfl

theorem DT.eta {K M k : ℕ} (d : DT K M (k + 1)) : DT.mk d.fst d.snd = d := rfl

theorem DT.ext_iff' {K M k : ℕ} (d d' : DT K M (k + 1)) :
    d = d' ↔ d.fst = d'.fst ∧ d.snd = d'.snd := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← DT.eta d, ← DT.eta d', h1, h2]

/-! ## Parameters -/

/-- Data of the block construction. -/
structure BParams where
  ξ : ℝ
  δ : ℝ
  ρ : ℝ
  M : ℕ
  N : ℕ
  K : ℕ
  fe : Fin (K + 1) → ℝ → ℝ

namespace BParams

variable (P : BParams)

/-- The edge similarity `T^{f_a}_i`. -/
def sim (a : Fin (P.K + 1)) (i : ℕ) : ℂ × ℂ :=
  (pVert P.M P.δ (P.fe a) (i + 1) - pVert P.M P.δ (P.fe a) i, pVert P.M P.δ (P.fe a) i)

/-- Its ratio. -/
def rr (a : Fin (P.K + 1)) (i : ℕ) : ℝ := ‖(P.sim a i).1‖

theorem edgeSim_eq (a : Fin (P.K + 1)) (i : ℕ) (z : ℂ) :
    edgeSim P.M P.δ (P.fe a) i z = app (P.sim a i) z := by
  simp only [edgeSim, app, sim]; ring

theorem app_sim_sub (a : Fin (P.K + 1)) (i : ℕ) (z w : ℂ) :
    ‖app (P.sim a i) z - app (P.sim a i) w‖ = P.rr a i * ‖z - w‖ := by
  rw [app_sub, norm_mul, rr]

/-- `ε_k = ρ M^{-k}`. -/
def eps (k : ℕ) : ℝ := P.ρ * ((P.M : ℝ)⁻¹) ^ k

/-- Lower end `4ρ/M` of the root band. -/
def top : ℝ := 4 * P.ρ / P.M

/-- Action of the child similarity on triples. -/
def tau (a : Fin (P.K + 1)) (i : ℕ) (q : Tri) : Tri :=
  (P.rr a i * q.1, P.rr a i * q.2.1, app (P.sim a i) q.2.2)

/-- Composite similarities of depth `k`. -/
def Lsim : ℕ → Finset (ℂ × ℂ)
  | 0 => {(1, 0)}
  | k + 1 => Finset.univ.biUnion fun a => (Finset.range P.M).biUnion fun i =>
      (Lsim k).image (comp (P.sim a i))

/-- The Riemann points of depth `k`. -/
def S (k : ℕ) : Finset ℂ :=
  (P.Lsim k ×ˢ Finset.range P.N).image fun Lq => app Lq.1 (((Lq.2 : ℝ) / P.N : ℝ) : ℂ)

/-- Root-band triples at depth `k+1`. -/
def XS (k : ℕ) : Finset Tri := (P.S (k + 1)).image fun p => (P.top, P.ρ, p)

/-- Triples used at depth `k`. -/
def Qs : ℕ → Finset Tri
  | 0 => (P.S 0).image fun p => (P.eps 0, P.ρ, p)
  | k + 1 => P.XS k ∪
      (Finset.univ.biUnion fun a => (Finset.range P.M).biUnion fun i =>
        ((Qs k).image (P.tau a i) ∪
          (P.S k).image (fun p => (P.rr a i * P.ρ, P.top, app (P.sim a i) p))) ∪
          (P.S k).image (fun p => (P.eps (k + 1), P.rr a i * P.eps k, app (P.sim a i) p))) ∪
      (P.S (k + 1)).image (fun p => (P.eps (k + 1), P.ρ, p))

/-- The polygon of a decision tree. -/
def polyOf : (k : ℕ) → DT P.K P.M k → List ℂ
  | 0, _ => [0, 1]
  | k + 1, d => glueFn P.M fun i => (polyOf k (d.snd i)).map (app (P.sim d.fst i))

/-- Expected weighted occupation at depth `k` of a rule `R`. -/
def occW (k : ℕ) (R : (Tri → ℝ) → DT P.K P.M k) (p : ℂ) : ℝ :=
  ∫ Y, rcW P.N (P.polyOf k (R Y)) (dlt p fun z => Real.exp (P.ξ * Y (P.eps k, P.ρ, z)))
    ∂gLaw (P.Qs k)

/-- Root-band block cost `C_{f_a}(w)` of the field `Y`. -/
def bcs (k : ℕ) (w : ℂ → ℝ) (Y : Tri → ℝ) (a : Fin (P.K + 1)) : ℝ :=
  blockCost P.ξ P.M P.δ (P.fe a) (P.S k) w (fun z => Y (P.top, P.ρ, z))

/-- The rule. -/
def dec : (k : ℕ) → (Tri → ℝ) → DT P.K P.M k
  | 0, _ => DT.leaf
  | k + 1, Y =>
    DT.mk (amin (P.bcs k (P.occW k (dec k)) Y))
      (fun i => dec k (fun q => Y (P.tau (amin (P.bcs k (P.occW k (dec k)) Y)) i q)))

/-- The expected weighted occupation measure `M_k` of the depth-`k` rule. -/
def Mw (k : ℕ) : ℂ → ℝ := P.occW k (P.dec k)

theorem dec_succ (k : ℕ) (Y : Tri → ℝ) :
    P.dec (k + 1) Y = DT.mk (amin (P.bcs k (P.Mw k) Y))
      (fun i => P.dec k (fun q => Y (P.tau (amin (P.bcs k (P.Mw k) Y)) i q))) := rfl

/-- The Riemann cost of the depth-`k` rule under the field `Y`. -/
def RC (k : ℕ) (Y : Tri → ℝ) : ℝ :=
  riemannCost P.ξ P.N (P.polyOf k (P.dec k Y)) (fun z => Y (P.eps k, P.ρ, z))

/-- `m_k`. -/
def mm (k : ℕ) : ℝ := ∫ Y, P.RC k Y ∂gLaw (P.Qs k)

/-! ## Hypotheses -/

/-- Standing hypotheses on the parameters. -/
structure Good : Prop where
  ρ_pos : 0 < P.ρ
  M_ge : 4 ≤ P.M
  N_pos : 1 ≤ P.N
  rr_ge : ∀ a, ∀ i < P.M, (P.M : ℝ)⁻¹ ≤ P.rr a i
  rr_le : ∀ a, ∀ i < P.M, P.rr a i ≤ 2 / P.M
  f0 : ∀ a, P.fe a 0 = 0
  f1 : ∀ a, P.fe a 1 = 0

variable {P}

theorem Good.M_pos (hP : P.Good) : (0 : ℝ) < P.M := by
  have := hP.M_ge; exact_mod_cast (by omega : 0 < P.M)

theorem Good.rr_pos (hP : P.Good) (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) : 0 < P.rr a i :=
  (inv_pos.2 hP.M_pos).trans_le (hP.rr_ge a i hi)

theorem Good.eps_pos (hP : P.Good) (k : ℕ) : 0 < P.eps k :=
  mul_pos hP.ρ_pos (pow_pos (inv_pos.2 hP.M_pos) k)

theorem Good.eps_le (hP : P.Good) (k : ℕ) : P.eps k ≤ P.ρ := by
  unfold eps
  have hM1 : (1 : ℝ) ≤ P.M := by have := hP.M_ge; exact_mod_cast (by omega : 1 ≤ P.M)
  calc P.ρ * ((P.M : ℝ)⁻¹) ^ k ≤ P.ρ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hM1))
          hP.ρ_pos.le
    _ = P.ρ := mul_one _

theorem eps_succ (k : ℕ) : P.eps (k + 1) = P.eps k * (P.M : ℝ)⁻¹ := by
  unfold eps; rw [pow_succ]; ring

theorem eps_zero : P.eps 0 = P.ρ := by simp [eps]

theorem Good.top_le (hP : P.Good) : P.top ≤ P.ρ := by
  unfold top
  have h4 : (4 : ℝ) ≤ P.M := by exact_mod_cast hP.M_ge
  rw [div_le_iff₀ hP.M_pos]
  nlinarith [hP.ρ_pos]

theorem Good.top_pos (hP : P.Good) : 0 < P.top := by
  unfold top; exact div_pos (by linarith [hP.ρ_pos]) hP.M_pos

/-- `r ρ ≤ 4ρ/M`. -/
theorem Good.rr_mul_le_top (hP : P.Good) (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ P.ρ) : P.rr a i * x ≤ P.top := by
  unfold top
  have h := hP.rr_le a i hi
  calc P.rr a i * x ≤ 2 / P.M * P.ρ := mul_le_mul h hx hx0 (by positivity)
    _ ≤ 4 * P.ρ / P.M := by
      rw [div_mul_eq_mul_div]
      gcongr
      · linarith [hP.ρ_pos]
      · norm_num

/-- `ε_{k+1} ≤ r x` for `x ≥ ε_k`. -/
theorem Good.eps_succ_le (hP : P.Good) (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) (k : ℕ)
    {x : ℝ} (hx : P.eps k ≤ x) : P.eps (k + 1) ≤ P.rr a i * x := by
  rw [eps_succ, mul_comm]
  exact mul_le_mul (hP.rr_ge a i hi) hx (hP.eps_pos k).le (hP.rr_pos a hi).le

theorem Good.rr_le_one (hP : P.Good) (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) :
    P.rr a i ≤ 1 := by
  have h4 : (4 : ℝ) ≤ P.M := by exact_mod_cast hP.M_ge
  calc P.rr a i ≤ 2 / P.M := hP.rr_le a i hi
    _ ≤ 1 := by rw [div_le_one hP.M_pos]; linarith

/-! ## Polygons: endpoints and junctions -/

theorem pVert_zero (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (hf : f 0 = 0) : pVert M δ f 0 = 0 := by
  simp [pVert, hf]

theorem pVert_M (M : ℕ) (hM : M ≠ 0) (δ : ℝ) (f : ℝ → ℝ) (hf : f 1 = 0) : pVert M δ f M = 1 := by
  have : (M : ℝ) / M = 1 := div_self (by exact_mod_cast hM)
  simp [pVert, this, hf, hM]

theorem app_sim_zero (a : Fin (P.K + 1)) (i : ℕ) :
    app (P.sim a i) 0 = pVert P.M P.δ (P.fe a) i := by
  simp [app, sim]

theorem app_sim_one (a : Fin (P.K + 1)) (i : ℕ) :
    app (P.sim a i) 1 = pVert P.M P.δ (P.fe a) (i + 1) := by
  simp [app, sim]

theorem glueFn_head?_of_pos (m : ℕ) (hm : 0 < m) (f : Fin m → List ℂ) (h0 : f ⟨0, hm⟩ ≠ []) :
    (glueFn m f).head? = (f ⟨0, hm⟩).head? := by
  cases m with
  | zero => omega
  | succ m => exact head?_glueFn m f h0

theorem glueFn_getLast?_of_pos (m : ℕ) (hm : 0 < m) (f : Fin m → List ℂ) (hne : ∀ i, f i ≠ [])
    (hJ : Junction m f) : (glueFn m f).getLast? = (f ⟨m - 1, by omega⟩).getLast? := by
  cases m with
  | zero => omega
  | succ m => exact getLast?_glueFn m f hne hJ

theorem Good.polyOf_ends (hP : P.Good) :
    ∀ k (d : DT P.K P.M k), (P.polyOf k d).head? = some 0 ∧ (P.polyOf k d).getLast? = some 1
  | 0, _ => by simp [polyOf]
  | k + 1, d => by
    have ih := Good.polyOf_ends hP k
    have hMpos : 0 < P.M := by have := hP.M_ge; omega
    have hne : ∀ i : Fin P.M, (P.polyOf k (d.snd i)).map (app (P.sim d.fst i)) ≠ [] := by
      intro i hc
      have := (ih (d.snd i)).1
      rw [List.map_eq_nil_iff] at hc
      rw [hc] at this
      simp at this
    have hJ : Junction P.M fun i => (P.polyOf k (d.snd i)).map (app (P.sim d.fst i)) := by
      intro i hi
      rw [List.getLast?_map, List.head?_map, (ih _).2, (ih _).1]
      simp only [Option.map_some]
      rw [app_sim_one, app_sim_zero]
    simp only [polyOf]
    refine ⟨?_, ?_⟩
    · rw [glueFn_head?_of_pos P.M hMpos _ (hne _), List.head?_map, (ih _).1, Option.map_some,
        app_sim_zero, pVert_zero _ _ _ (hP.f0 _)]
    · rw [glueFn_getLast?_of_pos P.M hMpos _ hne hJ, List.getLast?_map, (ih _).2, Option.map_some,
        app_sim_one, Nat.sub_add_cancel hMpos, pVert_M _ (by omega) _ _ (hP.f1 _)]

theorem Good.polyOf_ne_nil (hP : P.Good) (k : ℕ) (d : DT P.K P.M k) : P.polyOf k d ≠ [] := by
  intro h
  have := (hP.polyOf_ends k d).1
  rw [h] at this
  simp at this

theorem Good.junction (hP : P.Good) (k : ℕ) (d : DT P.K P.M (k + 1)) :
    Junction P.M fun i => (P.polyOf k (d.snd i)).map (app (P.sim d.fst i)) := by
  intro i hi
  rw [List.getLast?_map, List.head?_map, (hP.polyOf_ends k _).2, (hP.polyOf_ends k _).1]
  simp only [Option.map_some]
  rw [app_sim_one, app_sim_zero]

theorem Good.pieces_ne_nil (hP : P.Good) (k : ℕ) (d : DT P.K P.M (k + 1)) (i : Fin P.M) :
    (P.polyOf k (d.snd i)).map (app (P.sim d.fst i)) ≠ [] := by
  rw [Ne, List.map_eq_nil_iff]
  exact hP.polyOf_ne_nil k _

/-! ## Edges, vertices and Riemann points -/

theorem comp_mem_Lsim {k : ℕ} (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {L : ℂ × ℂ}
    (hL : L ∈ P.Lsim k) : comp (P.sim a i) L ∈ P.Lsim (k + 1) := by
  simp only [Lsim, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_range, Finset.mem_image,
    true_and]
  exact ⟨a, i, hi, L, hL, rfl⟩

theorem Good.edges_polyOf (hP : P.Good) :
    ∀ k (d : DT P.K P.M k), ∀ e ∈ edges (P.polyOf k d), ∃ L ∈ P.Lsim k, e = (app L 0, app L 1)
  | 0, _, e, he => by
    simp only [polyOf, edges_cons_cons, edges_single, List.mem_singleton] at he
    refine ⟨(1, 0), by simp [Lsim], ?_⟩
    rw [he]
    simp [app]
  | k + 1, d, e, he => by
    simp only [polyOf] at he
    obtain ⟨i, hi⟩ := mem_edges_glueFn P.M _ (hP.pieces_ne_nil k d) (hP.junction k d) e he
    rw [edges_map, List.mem_map] at hi
    obtain ⟨e', he', rfl⟩ := hi
    obtain ⟨L, hL, rfl⟩ := Good.edges_polyOf hP k _ e' he'
    exact ⟨comp (P.sim d.fst i) L, comp_mem_Lsim _ i.2 hL, by simp [app_comp]⟩

theorem Good.verts_polyOf (hP : P.Good) :
    ∀ k (d : DT P.K P.M k), ∀ v ∈ P.polyOf k d, ∃ L ∈ P.Lsim k, v = app L 0 ∨ v = app L 1
  | 0, _, v, hv => by
    simp only [polyOf, List.mem_cons, List.not_mem_nil, or_false] at hv
    refine ⟨(1, 0), by simp [Lsim], ?_⟩
    rcases hv with rfl | rfl
    · left; simp [app]
    · right; simp [app]
  | k + 1, d, v, hv => by
    simp only [polyOf] at hv
    obtain ⟨i, hi⟩ := mem_glueFn P.M _ v hv
    rw [List.mem_map] at hi
    obtain ⟨v', hv', rfl⟩ := hi
    obtain ⟨L, hL, h⟩ := Good.verts_polyOf hP k _ v' hv'
    refine ⟨comp (P.sim d.fst i) L, comp_mem_Lsim _ i.2 hL, ?_⟩
    rcases h with rfl | rfl
    · left; rw [app_comp]
    · right; rw [app_comp]

theorem app_mem_S {k : ℕ} {L : ℂ × ℂ} (hL : L ∈ P.Lsim k) {q : ℕ} (hq : q < P.N) :
    app L (((q : ℝ) / P.N : ℝ) : ℂ) ∈ P.S k := by
  simp only [S, Finset.mem_image, Finset.mem_product, Finset.mem_range]
  exact ⟨(L, q), ⟨hL, hq⟩, rfl⟩

theorem Good.riemannPts_subset (hP : P.Good) (k : ℕ) (d : DT P.K P.M k) :
    riemannPts P.N (P.polyOf k d) ⊆ ↑(P.S k) := by
  rintro p ⟨e, he, q, hq, rfl⟩
  obtain ⟨L, hL, rfl⟩ := hP.edges_polyOf k d e he
  rw [Finset.mem_coe]
  simp only
  rw [ew_edge_pt]
  exact app_mem_S hL hq

theorem sim_mem_S {k : ℕ} (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ} (hp : p ∈ P.S k) :
    app (P.sim a i) p ∈ P.S (k + 1) := by
  simp only [S, Finset.mem_image, Finset.mem_product, Finset.mem_range] at hp ⊢
  obtain ⟨⟨L, q⟩, ⟨hL, hq⟩, rfl⟩ := hp
  exact ⟨(comp (P.sim a i) L, q), ⟨comp_mem_Lsim a hi hL, hq⟩, by simp [app_comp]⟩

/-! ## Sizes -/

theorem Good.norm_Lsim_le (hP : P.Good) :
    ∀ k, ∀ L ∈ P.Lsim k, ‖L.1‖ ≤ (2 / (P.M : ℝ)) ^ k
  | 0, L, hL => by
    simp only [Lsim, Finset.mem_singleton] at hL
    subst hL; simp
  | k + 1, L, hL => by
    simp only [Lsim, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_range, Finset.mem_image,
      true_and] at hL
    obtain ⟨a, i, hi, L', hL', rfl⟩ := hL
    simp only [comp, norm_mul]
    rw [pow_succ']
    exact mul_le_mul (hP.rr_le a i hi) (Good.norm_Lsim_le hP k L' hL') (norm_nonneg _)
      (by positivity)

theorem Good.edge_len_le (hP : P.Good) (k : ℕ) (d : DT P.K P.M k) (e : ℂ × ℂ)
    (he : e ∈ edges (P.polyOf k d)) : ‖e.2 - e.1‖ ≤ (2 / (P.M : ℝ)) ^ k := by
  obtain ⟨L, hL, rfl⟩ := hP.edges_polyOf k d e he
  simp only [app]
  rw [show L.1 * 1 + L.2 - (L.1 * 0 + L.2) = L.1 by ring]
  exact hP.norm_Lsim_le k L hL

theorem card_Lsim_le : ∀ k, ((P.Lsim k).card : ℝ) ≤ (((P.K + 1) * P.M : ℕ) : ℝ) ^ k
  | 0 => by simp [Lsim]
  | k + 1 => by
    have ih := card_Lsim_le k
    have h1 : (P.Lsim (k + 1)).card ≤ (P.K + 1) * (P.M * (P.Lsim k).card) := by
      simp only [Lsim]
      refine (Finset.card_biUnion_le).trans ?_
      calc ∑ a : Fin (P.K + 1), ((Finset.range P.M).biUnion fun i =>
            (P.Lsim k).image (comp (P.sim a i))).card
          ≤ ∑ _a : Fin (P.K + 1), P.M * (P.Lsim k).card := by
            refine Finset.sum_le_sum fun a _ => (Finset.card_biUnion_le).trans ?_
            calc ∑ i ∈ Finset.range P.M, ((P.Lsim k).image (comp (P.sim a i))).card
                ≤ ∑ _i ∈ Finset.range P.M, (P.Lsim k).card :=
                  Finset.sum_le_sum fun i _ => Finset.card_image_le
              _ = P.M * (P.Lsim k).card := by simp
        _ = (P.K + 1) * (P.M * (P.Lsim k).card) := by simp
    calc ((P.Lsim (k + 1)).card : ℝ) ≤ (((P.K + 1) * (P.M * (P.Lsim k).card) : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ = (((P.K + 1) * P.M : ℕ) : ℝ) * (P.Lsim k).card := by push_cast; ring
      _ ≤ (((P.K + 1) * P.M : ℕ) : ℝ) * (((P.K + 1) * P.M : ℕ) : ℝ) ^ k := by gcongr
      _ = (((P.K + 1) * P.M : ℕ) : ℝ) ^ (k + 1) := by ring

theorem card_S_le (k : ℕ) : ((P.S k).card : ℝ) ≤ (((P.K + 1) * P.M : ℕ) : ℝ) ^ k * P.N := by
  have h1 : (P.S k).card ≤ (P.Lsim k).card * P.N := by
    unfold S
    refine Finset.card_image_le.trans ?_
    simp
  calc ((P.S k).card : ℝ) ≤ ((P.Lsim k).card * P.N : ℕ) := by exact_mod_cast h1
    _ = ((P.Lsim k).card : ℝ) * P.N := by push_cast; ring
    _ ≤ (((P.K + 1) * P.M : ℕ) : ℝ) ^ k * P.N := by gcongr; exact card_Lsim_le k

/-! ## The tube -/

theorem pVert_eq (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) :
    pVert M δ f i = ((((i : ℝ) / M : ℝ)) : ℂ) + ((δ * f ((i : ℝ) / M) : ℝ) : ℂ) * Complex.I := by
  unfold pVert; push_cast; ring

theorem pVert_re (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) : (pVert M δ f i).re = (i : ℝ) / M := by
  rw [pVert_eq]; simp

theorem pVert_im (M : ℕ) (δ : ℝ) (f : ℝ → ℝ) (i : ℕ) :
    (pVert M δ f i).im = δ * f ((i : ℝ) / M) := by
  rw [pVert_eq]; simp

/-- Real and imaginary parts of the edge similarity at a real parameter. -/
theorem app_sim_real (a : Fin (P.K + 1)) (i : ℕ) (s : ℝ) :
    (app (P.sim a i) (s : ℂ)).re = ((i : ℝ) + s) / P.M ∧
    (app (P.sim a i) (s : ℂ)).im = P.δ * ((1 - s) * P.fe a ((i : ℝ) / P.M) +
      s * P.fe a (((i + 1 : ℕ) : ℝ) / P.M)) := by
  simp only [app, sim, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.sub_im, pVert_re, pVert_im]
  constructor
  · push_cast; ring
  · ring

theorem Good.tube_step (hP : P.Good) (hδ : 0 ≤ P.δ) {K₀ : ℝ}
    (hf : ∀ a x, |P.fe a x| ≤ K₀) (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) (w : ℂ)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (c : ℝ) (hw : ‖w - s‖ ≤ c) :
    ∃ s' ∈ Icc (0 : ℝ) 1, ‖app (P.sim a i) w - s'‖ ≤ P.δ * K₀ + P.rr a i * c := by
  obtain ⟨hre, him⟩ := P.app_sim_real a i s
  set z := app (P.sim a i) (s : ℂ) with hz
  refine ⟨z.re, ⟨?_, ?_⟩, ?_⟩
  · rw [hre]; exact div_nonneg (by linarith [hs.1, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
      hP.M_pos.le
  · rw [hre, div_le_one hP.M_pos]
    have : ((i : ℝ) + 1) ≤ P.M := by exact_mod_cast hi
    linarith [hs.2]
  · have h1 : ‖app (P.sim a i) w - z‖ ≤ P.rr a i * c := by
      rw [hz, P.app_sim_sub]
      exact mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    have h2 : ‖z - (z.re : ℂ)‖ ≤ P.δ * K₀ := by
      have : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, him,
        abs_mul, abs_of_nonneg hδ]
      refine mul_le_mul_of_nonneg_left ?_ hδ
      calc |(1 - s) * P.fe a (↑i / ↑P.M) + s * P.fe a (↑(i + 1) / ↑P.M)|
          ≤ |(1 - s) * P.fe a (↑i / ↑P.M)| + |s * P.fe a (↑(i + 1) / ↑P.M)| := abs_add_le _ _
        _ = (1 - s) * |P.fe a (↑i / ↑P.M)| + s * |P.fe a (↑(i + 1) / ↑P.M)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
            abs_of_nonneg hs.1]
        _ ≤ (1 - s) * K₀ + s * K₀ := by
          gcongr
          · linarith [hs.2]
          · exact hf _ _
          · exact hs.1
          · exact hf _ _
        _ = K₀ := by ring
    calc ‖app (P.sim a i) w - (z.re : ℂ)‖ = ‖(app (P.sim a i) w - z) + (z - (z.re : ℂ))‖ := by
          ring_nf
      _ ≤ ‖app (P.sim a i) w - z‖ + ‖z - (z.re : ℂ)‖ := norm_add_le _ _
      _ ≤ P.rr a i * c + P.δ * K₀ := add_le_add h1 h2
      _ = P.δ * K₀ + P.rr a i * c := by ring

theorem Good.Lsim_tube (hP : P.Good) (hδ : 0 ≤ P.δ) {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hf : ∀ a x, |P.fe a x| ≤ K₀) :
    ∀ k, ∀ L ∈ P.Lsim k, ∀ s ∈ Icc (0 : ℝ) 1, ∃ s' ∈ Icc (0 : ℝ) 1,
      ‖app L (s : ℂ) - s'‖ ≤ 2 * P.δ * K₀
  | 0, L, hL, s, hs => by
    simp only [Lsim, Finset.mem_singleton] at hL
    subst hL
    exact ⟨s, hs, by simp [app]; positivity⟩
  | k + 1, L, hL, s, hs => by
    simp only [Lsim, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_range, Finset.mem_image,
      true_and] at hL
    obtain ⟨a, i, hi, L', hL', rfl⟩ := hL
    obtain ⟨s₁, hs₁, h₁⟩ := Good.Lsim_tube hP hδ hK₀ hf k L' hL' s hs
    obtain ⟨s', hs', h'⟩ := hP.tube_step hδ hf a hi (app L' s) s₁ hs₁ _ h₁
    refine ⟨s', hs', ?_⟩
    rw [app_comp]
    refine h'.trans ?_
    have hr : P.rr a i ≤ 1 / 2 := by
      have h4 : (4 : ℝ) ≤ P.M := by exact_mod_cast hP.M_ge
      calc P.rr a i ≤ 2 / P.M := hP.rr_le a i hi
        _ ≤ 1 / 2 := by rw [div_le_div_iff₀ hP.M_pos (by norm_num)]; linarith
    have : 0 ≤ 2 * P.δ * K₀ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hr this]

/-! ## Triples -/

theorem mem_Qs_succ_X {k : ℕ} {p : ℂ} (hp : p ∈ P.S (k + 1)) :
    (P.top, P.ρ, p) ∈ P.Qs (k + 1) := by
  simp only [Qs, XS, Finset.mem_union, Finset.mem_image]
  exact Or.inl (Or.inl ⟨p, hp, rfl⟩)

theorem mem_XS {k : ℕ} {p : ℂ} (hp : p ∈ P.S (k + 1)) : (P.top, P.ρ, p) ∈ P.XS k := by
  simp only [XS, Finset.mem_image]
  exact ⟨p, hp, rfl⟩

theorem mem_Qs_succ_tau {k : ℕ} (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {q : Tri}
    (hq : q ∈ P.Qs k) : P.tau a i q ∈ P.Qs (k + 1) := by
  simp only [Qs, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_range,
    Finset.mem_image, true_and]
  exact Or.inl (Or.inr ⟨a, i, hi, Or.inl (Or.inl ⟨q, hq, rfl⟩)⟩)

theorem mem_Qs_succ_Y1 {k : ℕ} (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ}
    (hp : p ∈ P.S k) : (P.rr a i * P.ρ, P.top, app (P.sim a i) p) ∈ P.Qs (k + 1) := by
  simp only [Qs, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_range,
    Finset.mem_image, true_and]
  exact Or.inl (Or.inr ⟨a, i, hi, Or.inl (Or.inr ⟨p, hp, rfl⟩)⟩)

theorem mem_Qs_succ_Y2 {k : ℕ} (a : Fin (P.K + 1)) {i : ℕ} (hi : i < P.M) {p : ℂ}
    (hp : p ∈ P.S k) :
    (P.eps (k + 1), P.rr a i * P.eps k, app (P.sim a i) p) ∈ P.Qs (k + 1) := by
  simp only [Qs, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_range,
    Finset.mem_image, true_and]
  exact Or.inl (Or.inr ⟨a, i, hi, Or.inr ⟨p, hp, rfl⟩⟩)

theorem mem_Qs_tot : ∀ {k : ℕ} {p : ℂ}, p ∈ P.S k → (P.eps k, P.ρ, p) ∈ P.Qs k
  | 0, p, hp => by
    simp only [Qs, Finset.mem_image]
    exact ⟨p, hp, rfl⟩
  | k + 1, p, hp => by
    simp only [Qs, Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨p, hp, rfl⟩

/-- All triples of depth `k` lie in the band `(ε_k, ρ]`. -/
theorem Good.Qs_band (hP : P.Good) :
    ∀ k, ∀ q ∈ P.Qs k, P.eps k ≤ q.1 ∧ q.1 ≤ q.2.1 ∧ q.2.1 ≤ P.ρ
  | 0, q, hq => by
    simp only [Qs, Finset.mem_image] at hq
    obtain ⟨p, -, rfl⟩ := hq
    exact ⟨le_rfl, hP.eps_le 0, le_rfl⟩
  | k + 1, q, hq => by
    have ih := Good.Qs_band hP k
    have he1 : P.eps (k + 1) ≤ P.top := by
      rw [eps_succ, top, div_eq_mul_inv]
      have := hP.eps_le k
      have : 0 < (P.M : ℝ)⁻¹ := inv_pos.2 hP.M_pos
      nlinarith [hP.ρ_pos]
    simp only [Qs, XS, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_range,
      Finset.mem_image, true_and] at hq
    rcases hq with ((⟨p, -, rfl⟩ | ⟨a, i, hi, ((⟨q', hq', rfl⟩ | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩)⟩) |
      ⟨p, -, rfl⟩)
    · exact ⟨he1, hP.top_le, le_rfl⟩
    · obtain ⟨h1, h2, h3⟩ := ih q' hq'
      have hr := hP.rr_pos a hi
      refine ⟨hP.eps_succ_le a hi k h1, mul_le_mul_of_nonneg_left h2 hr.le, ?_⟩
      calc P.rr a i * q'.2.1 ≤ 1 * P.ρ :=
            mul_le_mul (hP.rr_le_one a hi) h3 (by linarith [hP.eps_pos k]) zero_le_one
        _ = P.ρ := one_mul _
    · exact ⟨hP.eps_succ_le a hi k (hP.eps_le k), hP.rr_mul_le_top a hi hP.ρ_pos.le le_rfl,
        hP.top_le⟩
    · refine ⟨le_rfl, hP.eps_succ_le a hi k le_rfl, ?_⟩
      calc P.rr a i * P.eps k ≤ 1 * P.ρ :=
            mul_le_mul (hP.rr_le_one a hi) (hP.eps_le k) (hP.eps_pos k).le zero_le_one
        _ = P.ρ := one_mul _
    · exact ⟨le_rfl, hP.eps_le _, le_rfl⟩

theorem Good.Qs_pos (hP : P.Good) (k : ℕ) (q : Tri) (hq : q ∈ P.Qs k) : 0 < q.1 :=
  (hP.eps_pos k).trans_le (hP.Qs_band k q hq).1

end BParams

end LQGDimension.BlockCons
