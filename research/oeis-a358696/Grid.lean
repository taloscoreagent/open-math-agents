import OMAStatements.S_oeis_a358696

/-!
Supporting lemmas for the correspondence between the five-row grid and its
column states. Edges are encoded by their row and column, local degrees are
sums of four indicators, and connectivity across a cut is obtained by
joining the new column to the connected components of the old region.
-/

namespace OMA358

open OMA.S_oeis_a358696

abbrev EdgePos (n : ℕ) := (Fin 4 × Fin n) ⊕ (Fin 5 × Fin (n - 1))

def posLeft {m : ℕ} (i : Fin (m - 1)) : Fin m :=
  ⟨i.val, by have := i.isLt; omega⟩

def posRight {m : ℕ} (i : Fin (m - 1)) : Fin m :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

def asEdge {n : ℕ} : EdgePos n → Sym2 (Vertex n)
  | .inl (i, j) => s((posLeft (m := 5) i, j), (posRight (m := 5) i, j))
  | .inr (i, j) => s((i, posLeft j), (i, posRight j))

theorem asEdge_mem {n : ℕ} (p : EdgePos n) : asEdge p ∈ (grid n).edgeSet := by
  rcases p with ⟨i,j⟩ | ⟨i,j⟩
  · exact Or.inl ⟨SimpleGraph.pathGraph_adj.mpr (Or.inl rfl), rfl⟩
  · exact Or.inr ⟨SimpleGraph.pathGraph_adj.mpr (Or.inl rfl), rfl⟩

theorem asEdge_injective {n : ℕ} : Function.Injective (@asEdge n) := by
  rintro (⟨i,j⟩|⟨i,j⟩) (⟨k,l⟩|⟨k,l⟩) he
  all_goals
    simp only [asEdge, Sym2.eq_iff, Prod.mk.injEq, Fin.ext_iff, posLeft, posRight] at he
    simp [Fin.ext_iff]
    omega

theorem asEdge_onto {n : ℕ} (e : Sym2 (Vertex n)) (he : e ∈ (grid n).edgeSet) :
    ∃ p : EdgePos n, asEdge p = e := by
  revert he
  induction e using Sym2.ind with
  | h p q =>
    rcases p with ⟨i,j⟩
    rcases q with ⟨k,l⟩
    intro he
    change (grid n).Adj (i,j) (k,l) at he
    rcases he with ⟨hadj, h⟩ | ⟨hadj, h⟩
    · change j = l at h
      subst l
      change (SimpleGraph.pathGraph 5).Adj i k at hadj
      rcases SimpleGraph.pathGraph_adj.mp hadj with h | h
      · refine ⟨.inl (⟨i.val, by have := k.isLt; omega⟩, j), ?_⟩
        apply Sym2.eq_iff.mpr
        left
        simp [posLeft, posRight, h]
      · refine ⟨.inl (⟨k.val, by have := i.isLt; omega⟩, j), ?_⟩
        apply Sym2.eq_iff.mpr
        right
        simp [posLeft, posRight, h]
    · change i = k at h
      subst k
      change (SimpleGraph.pathGraph n).Adj j l at hadj
      rcases SimpleGraph.pathGraph_adj.mp hadj with h | h
      · refine ⟨.inr (i, ⟨j.val, by have := l.isLt; omega⟩), ?_⟩
        apply Sym2.eq_iff.mpr
        left
        simp [posLeft, posRight, h]
      · refine ⟨.inr (i, ⟨l.val, by have := j.isLt; omega⟩), ?_⟩
        apply Sym2.eq_iff.mpr
        right
        simp [posLeft, posRight, h]

noncomputable def edgeEquiv (n : ℕ) : EdgePos n ≃ (grid n).edgeSet :=
  Equiv.ofBijective (fun p => ⟨asEdge p, asEdge_mem p⟩)
    ⟨fun _ _ h => asEdge_injective (congrArg Subtype.val h),
      fun e => by
        obtain ⟨p,hp⟩ := asEdge_onto e.val e.property
        exact ⟨p, Subtype.ext hp⟩⟩

noncomputable def edgeMaskEquiv (n : ℕ) :
    Finset (EdgePos n) ≃ {E : Finset (Sym2 (Vertex n)) //
       (E : Set (Sym2 (Vertex n))) ⊆ (grid n).edgeSet} :=
  (edgeEquiv n).finsetCongr.trans (Equiv.finsetSubtypeComm _)

@[simp] theorem edgeEquiv_val {n : ℕ} (p : EdgePos n) :
    (edgeEquiv n p).val = asEdge p := rfl

theorem edgeMaskEquiv_val {n : ℕ} (s : Finset (EdgePos n)) :
    (edgeMaskEquiv n s).val = s.map ⟨asEdge, asEdge_injective⟩ := by
  change (s.map _).map _ = _
  rw [Finset.map_map]
  rfl

@[simp] theorem mem_edgeMaskEquiv {n : ℕ} (s : Finset (EdgePos n)) (p : EdgePos n) :
    asEdge p ∈ (edgeMaskEquiv n s).val ↔ p ∈ s := by
  rw [edgeMaskEquiv_val]
  exact Finset.mem_map' _

noncomputable def splitMaskEquiv (n : ℕ) :
    (Finset (Fin 4 × Fin n) × Finset (Fin 5 × Fin (n - 1))) ≃
      {E : Finset (Sym2 (Vertex n)) // (E : Set _) ⊆ (grid n).edgeSet} :=
  Finset.sumEquiv.toEquiv.symm.trans (edgeMaskEquiv n)

end OMA358

namespace OMA358

open OMA.S_oeis_a358696

def leftEmbed {m : ℕ} : Fin (m - 1) ↪ Fin m :=
  ⟨posLeft, fun _ _ h => Fin.ext (congrArg (fun t : Fin m => t.val) h)⟩

def rightEmbed {m : ℕ} : Fin (m - 1) ↪ Fin m :=
  ⟨posRight, fun _ _ h => Fin.ext (Nat.add_right_cancel (congrArg Fin.val h))⟩

abbrev vStart {n : ℕ} : (Fin 4 × Fin n) ↪ Vertex n :=
  (leftEmbed (m := 5)).prodMap (Function.Embedding.refl _)
abbrev vEnd {n : ℕ} : (Fin 4 × Fin n) ↪ Vertex n :=
  (rightEmbed (m := 5)).prodMap (Function.Embedding.refl _)
abbrev hStart {n : ℕ} : (Fin 5 × Fin (n-1)) ↪ Vertex n :=
  (Function.Embedding.refl _).prodMap leftEmbed
abbrev hEnd {n : ℕ} : (Fin 5 × Fin (n-1)) ↪ Vertex n :=
  (Function.Embedding.refl _).prodMap rightEmbed

/-- One precisely when a selected edge has this vertex as the given endpoint. -/
def hit {α β : Type*} [DecidableEq β] (sel : Finset α) (e : α ↪ β) (v : β) : ℕ :=
  if v ∈ sel.map e then 1 else 0

private theorem sum_hit {α β : Type*} [DecidableEq β]
    (sel : Finset α) (e : α ↪ β) (v : β) :
    (∑ x ∈ sel, if v = e x then 1 else 0) = hit sel e v := by
  classical
  change _ = if v ∈ sel.map e then 1 else 0
  simpa only [Finset.sum_map] using
    (Finset.sum_ite_eq (sel.map e) v (fun _ => (1:ℕ)))

private theorem sum_pair_hits {α β : Type*} [DecidableEq β] (sel : Finset α)
    (f g : α ↪ β) (hne : ∀ x, f x ≠ g x) (v : β) :
    (∑ x ∈ sel, if v ∈ s(f x,g x) then 1 else 0) = hit sel f v + hit sel g v := by
  rw [← sum_hit, ← sum_hit, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Sym2.mem_iff]
  by_cases hf : v = f x
  · simp [hf, hne x]
  · simp [hf]

noncomputable def selectedGraph {n : ℕ} (sel : Finset (EdgePos n)) : SimpleGraph (Vertex n) :=
  SimpleGraph.fromEdgeSet ((edgeMaskEquiv n sel).val : Set _)

theorem selectedGraph_edgeSet {n : ℕ} (sel : Finset (EdgePos n)) :
    (selectedGraph sel).edgeSet = ((edgeMaskEquiv n sel).val : Set _) := by
  rw [selectedGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  change (_ ∧ ¬e.IsDiag) ↔ _
  exact ⟨And.left, fun h => ⟨h,(grid n).not_isDiag_of_mem_edgeSet ((edgeMaskEquiv n sel).property h)⟩⟩

noncomputable local instance neighborsFintype {n : ℕ} (sel : Finset (EdgePos n)) (v : Vertex n) :
    Fintype ((selectedGraph sel).neighborSet v) := Fintype.ofFinite _

private theorem selectedDegree_sum {n : ℕ} (sel : Finset (EdgePos n)) (v : Vertex n) :
    (selectedGraph sel).degree v = ∑ p ∈ sel, if v ∈ asEdge p then 1 else 0 := by
  classical
  have h : (selectedGraph sel).incidenceFinset v =
      (edgeMaskEquiv n sel).val.filter (fun e => v ∈ e) := by
    ext e
    rw [SimpleGraph.mem_incidenceFinset, Finset.mem_filter]
    change (e ∈ (selectedGraph sel).edgeSet ∧ v ∈ e) ↔ _
    rw [selectedGraph_edgeSet]
    rfl
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, h, edgeMaskEquiv_val, Finset.filter_map,
    Finset.card_map, Finset.sum_boole]
  rfl

/-- Selected edges from the preceding column, the preceding row, the next
row, and the next column, respectively. An absent neighbor contributes zero. -/
def localDegree {n : ℕ} (vert : Finset (Fin 4 × Fin n)) (hor : Finset (Fin 5 × Fin (n-1)))
    (v : Vertex n) : ℕ :=
  hit hor hEnd v + hit vert vEnd v + hit vert vStart v + hit hor hStart v

theorem degree_eq_localDegree {n : ℕ} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (v : Vertex n) :
    (selectedGraph (vert.disjSum hor)).degree v = localDegree vert hor v := by
  rw [selectedDegree_sum, Finset.sum_disjSum]
  change (∑ p ∈ vert, if v ∈ s(vStart p, vEnd p) then 1 else 0) +
    (∑ p ∈ hor, if v ∈ s(hStart p, hEnd p) then 1 else 0) = _
  have hv (p : Fin 4 × Fin n) : vStart p ≠ vEnd p := by
    intro h
    have hh := congrArg (fun x : Vertex n => x.1.val) h
    change p.1.val = p.1.val + 1 at hh
    omega
  have hh (p : Fin 5 × Fin (n-1)) : hStart p ≠ hEnd p := by
    intro h
    have h' := congrArg (fun x : Vertex n => x.2.val) h
    change p.2.val = p.2.val + 1 at h'
    omega
  rw [sum_pair_hits _ _ _ hv, sum_pair_hits _ _ _ hh]
  unfold localDegree
  omega

theorem mem_support_iff_localDegree_pos {n : ℕ} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (v : Vertex n) :
    v ∈ (selectedGraph (vert.disjSum hor)).support ↔ 0 < localDegree vert hor v := by
  rw [← SimpleGraph.degree_pos_iff_mem_support, degree_eq_localDegree]

theorem isCycles_iff_localDegree {n : ℕ} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) :
    (selectedGraph (vert.disjSum hor)).IsCycles ↔
      ∀ v, localDegree vert hor v = 0 ∨ localDegree vert hor v = 2 := by
  let G := selectedGraph (vert.disjSum hor)
  have card (v : Vertex n) : (G.neighborSet v).ncard = localDegree vert hor v := by
    rw [Set.ncard_eq_toFinset_card']
    exact degree_eq_localDegree vert hor v
  have pos (v : Vertex n) : (G.neighborSet v).Nonempty ↔ 0 < localDegree vert hor v := by
    rw [← degree_eq_localDegree, SimpleGraph.degree_pos_iff_nonempty]
  constructor
  · intro h v
    by_cases h0 : localDegree vert hor v = 0
    · exact Or.inl h0
    · exact Or.inr ((card v).symm.trans (h ((pos v).mpr (Nat.pos_of_ne_zero h0))))
  · intro h v hv
    rw [card]
    obtain h0 | h2 := h v
    · have hp := (pos v).mp hv
      omega
    · exact h2

/-- The local column tests force two incident edges at every boundary vertex
and allow an interior vertex either two incident edges or none. -/
def localTests {n : ℕ} (vert : Finset (Fin 4 × Fin n)) (hor : Finset (Fin 5 × Fin (n-1))) : Prop :=
  ∀ v : Vertex n, localDegree vert hor v = 2 ∨
    (¬ boundary v ∧ localDegree vert hor v = 0)

theorem isBoundaryCycle_iff {n : ℕ} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) :
    isBoundaryCycle (edgeMaskEquiv n (vert.disjSum hor)).val ↔
      let G := selectedGraph (vert.disjSum hor)
      (G.induce G.support).Connected ∧ localTests vert hor := by
  change (_ ∧ _ ∧ (selectedGraph (vert.disjSum hor)).IsCycles ∧ _) ↔ _
  rw [isCycles_iff_localDegree, and_iff_right (edgeMaskEquiv n (vert.disjSum hor)).property]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨hdeg, hbdy⟩ v
    obtain h0 | h2 := hdeg v
    · refine Or.inr ⟨?_, h0⟩
      intro hv
      have hpos := (mem_support_iff_localDegree_pos vert hor v).mp (hbdy v hv)
      omega
    · exact Or.inl h2
  · intro h
    constructor
    · intro v
      exact (h v).elim Or.inr (fun hi => Or.inl hi.2)
    · intro v hv
      have h2 := (h v).resolve_right (fun hi => hi.1 hv)
      exact (mem_support_iff_localDegree_pos vert hor v).mpr (by omega)

abbrev EdgeArrays (n : ℕ) := Finset (Fin 4 × Fin n) × Finset (Fin 5 × Fin (n-1))

def admissible {n : ℕ} (arr : EdgeArrays n) : Prop :=
  let G := selectedGraph (arr.1.disjSum arr.2)
  (G.induce G.support).Connected ∧ localTests arr.1 arr.2

noncomputable def cycleArrayEquiv (n : ℕ) :
    {arr : EdgeArrays n // admissible arr} ≃
      {E : Finset (Sym2 (Vertex n)) // isBoundaryCycle E} where
  toFun p := ⟨(splitMaskEquiv n p.val).val,
    (isBoundaryCycle_iff p.val.1 p.val.2).mpr p.property⟩
  invFun q := by
    let E : {E : Finset (Sym2 (Vertex n)) // (E : Set _) ⊆ (grid n).edgeSet} :=
      ⟨q.val, q.property.1⟩
    let arr := (splitMaskEquiv n).symm E
    refine ⟨arr, (isBoundaryCycle_iff arr.1 arr.2).mp ?_⟩
    change isBoundaryCycle ((splitMaskEquiv n) ((splitMaskEquiv n).symm E)).val
    rw [Equiv.apply_symm_apply]
    exact q.property
  left_inv p := Subtype.ext ((splitMaskEquiv n).symm_apply_apply p.val)
  right_inv q := by
    let E : {E : Finset (Sym2 (Vertex n)) // (E : Set _) ⊆ (grid n).edgeSet} :=
      ⟨q.val, q.property.1⟩
    apply Subtype.ext
    change ((splitMaskEquiv n) ((splitMaskEquiv n).symm E)).val = E.val
    rw [Equiv.apply_symm_apply]

theorem count_eq_admissible (n : ℕ) :
    a n = (Nat.card {arr : EdgeArrays n // admissible arr} : ℤ) :=
  congrArg NatCast.natCast (Nat.card_congr (cycleArrayEquiv n).symm)

end OMA358

namespace OMA358

open SimpleGraph

/-- A connected finite partial cycle with a nonempty set of unfinished vertices
has exactly two of them. A port has one missing incidence. -/
theorem port_card_eq_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (ports : Finset V) (hp : ports.Nonempty)
    (hd : ∀ v, G.degree v + (if v ∈ ports then 1 else 0) = 2) :
    ports.card = 2 := by
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl (fun v _ => hd v)
  rw [Finset.sum_add_distrib, G.sum_degrees_eq_twice_card_edges,
    ← Finset.card_eq_sum_ite (Finset.subset_univ ports)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have htree := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card] at htree
  have hpos := Finset.card_pos.mpr hp
  simp only [Nat.cast_id] at hsum
  omega

/-- A connected graph has an edge crossing each nontrivial vertex cut. -/
theorem exists_crossing_edge {V : Type*} (G : SimpleGraph V) (hc : G.Connected)
    (A : Set V) (hin : A.Nonempty) (hout : Aᶜ.Nonempty) :
    ∃ x ∈ A, ∃ y ∉ A, G.Adj x y := by
  classical
  by_contra! h
  have closed {v w : V} (p : G.Walk v w) (hv : v ∈ A) : w ∈ A := by
    induction p with
    | nil => exact hv
    | @cons v w t e p ih =>
      apply ih
      by_contra hnot
      exact h v hv w hnot e
  obtain ⟨v, hv⟩ := hin
  obtain ⟨w, hw⟩ := hout
  obtain ⟨p⟩ := hc.preconnected v w
  exact hw (closed p hv)

/-- Each component induced on a proper prefix of a connected graph
has an edge leaving the prefix. No finiteness or nonemptiness hypotheses
on the prefix are needed once a component is given. -/
theorem induced_component_has_exit {V : Type*} (G : SimpleGraph V) (hc : G.Connected)
    (prefixVerts : Set V) (hout : prefixVertsᶜ.Nonempty)
    (C : (G.induce prefixVerts).ConnectedComponent) :
    ∃ x ∈ C.supp, ∃ y ∉ prefixVerts, G.Adj x.val y := by
  let A : Set V := Subtype.val '' C.supp
  have hin : A.Nonempty := C.nonempty_supp.image Subtype.val
  have hcut : Aᶜ.Nonempty := by
    obtain ⟨v, hv⟩ := hout
    refine ⟨v, ?_⟩
    rintro ⟨x, _, rfl⟩
    exact hv x.property
  obtain ⟨v, ⟨x, hx, rfl⟩, y, hy, he⟩ := exists_crossing_edge G hc A hin hcut
  refine ⟨x, hx, y, ?_, he⟩
  intro hy'
  let z : prefixVerts := ⟨y, hy'⟩
  have hadj : (G.induce prefixVerts).Adj x z := he
  exact hy ⟨z, C.mem_supp_of_adj_mem_supp hx hadj, rfl⟩

end OMA358

namespace GridCut

open Relation

variable {α β : Type*}

/-- The edges in two regions and those crossing their common cut. -/
def joined (R : α → α → Prop) (S : β → β → Prop) (P : α → β → Prop) :
    α ⊕ β → α ⊕ β → Prop
  | .inl a, .inl a' => R a a'
  | .inr b, .inr b' => S b b'
  | .inl a, .inr b => P a b
  | .inr b, .inl a => P a b

/-- Adjacencies in the new column, with each old path replaced by a link. -/
def condensed (R : α → α → Prop) (S : β → β → Prop) (P : α → β → Prop)
    (b c : β) : Prop :=
  S b c ∨ ∃ a d, P a b ∧ EqvGen R a d ∧ P d c

private theorem map_walk {X Y : Type*} {A : X → X → Prop} {B : Y → Y → Prop}
    (f : X → Y) (edge : ∀ x y, A x y → EqvGen B (f x) (f y))
    {x y : X} (h : EqvGen A x y) : EqvGen B (f x) (f y) := by
  induction h with
  | rel x y h => exact edge x y h
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2

theorem boundary_connectivity
    (R : α → α → Prop) (S : β → β → Prop) (P : α → β → Prop)
    (covered : ∀ a, ∃ d b, EqvGen R a d ∧ P d b) (b c : β) :
    EqvGen (joined R S P) (Sum.inr b) (Sum.inr c) ↔ EqvGen (condensed R S P) b c := by
  constructor
  · choose d dest via link using covered
    let f : α ⊕ β → β := Sum.elim dest id
    have project (x y : α ⊕ β) (h : joined R S P x y) :
        EqvGen (condensed R S P) (f x) (f y) := by
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          exact .rel _ _ (.inr ⟨d x, d y, link x,
            .trans _ _ _ (.symm _ _ (via x)) (.trans _ _ _ (.rel _ _ h) (via y)), link y⟩)
        | inr y =>
          exact .rel _ _ (.inr ⟨d x, x, link x, .symm _ _ (via x), h⟩)
      | inr x =>
        cases y with
        | inl y => exact .rel _ _ (.inr ⟨y, d y, h, via y, link y⟩)
        | inr y => exact .rel _ _ (.inl h)
    exact fun h => map_walk f project h
  · apply map_walk Sum.inr
    intro x y h
    rcases h with hn | ⟨a,d,hx,had,hy⟩
    · exact .rel _ _ hn
    · have inside : EqvGen (joined R S P) (Sum.inl a) (Sum.inl d) :=
        map_walk (B := joined R S P) Sum.inl (fun p q hp => EqvGen.rel (Sum.inl p) (Sum.inl q) hp) had
      have enter : EqvGen (joined R S P) (Sum.inr x) (Sum.inl a) := .rel _ _ hx
      have leave : EqvGen (joined R S P) (Sum.inl d) (Sum.inr y) := .rel _ _ hy
      exact .trans _ _ _ enter (.trans _ _ _ inside leave)

/-- When each old component meets the cut, every vertex of the enlarged graph
is connected to some vertex of the new column. -/
theorem reaches_new (R : α → α → Prop) (S : β → β → Prop) (P : α → β → Prop)
    (covered : ∀ a, ∃ d b, EqvGen R a d ∧ P d b) (z : α ⊕ β) :
    ∃ b, EqvGen (joined R S P) z (Sum.inr b) := by
  cases z with
  | inr b => exact ⟨b, .refl _⟩
  | inl a =>
    obtain ⟨d,b,had,hdb⟩ := covered a
    have oldPath : EqvGen (joined R S P) (Sum.inl a) (Sum.inl d) :=
      map_walk (B := joined R S P) Sum.inl (fun _ _ h => EqvGen.rel _ _ h) had
    exact ⟨b, .trans _ _ _ oldPath (.rel _ _ hdb)⟩

theorem reaches_exits_iff (R : α → α → Prop) (S : β → β → Prop) (P : α → β → Prop)
    (covered : ∀ a, ∃ d b, EqvGen R a d ∧ P d b) (exit : β → Prop) :
    (∀ z, ∃ b, exit b ∧ EqvGen (joined R S P) z (Sum.inr b)) ↔
      ∀ c, ∃ b, exit b ∧ EqvGen (condensed R S P) c b := by
  constructor
  · intro all c
    obtain ⟨b,hb,hcb⟩ := all (.inr c)
    exact ⟨b, hb, (boundary_connectivity R S P covered c b).mp hcb⟩
  · intro all z
    obtain ⟨c,hzc⟩ := reaches_new R S P covered z
    obtain ⟨b,hb,hcb⟩ := all c
    exact ⟨b,hb,.trans _ _ _ hzc ((boundary_connectivity R S P covered c b).mpr hcb)⟩

theorem connected_iff (R : α → α → Prop) (S : β → β → Prop) (P : α → β → Prop)
    (covered : ∀ a, ∃ d b, EqvGen R a d ∧ P d b) :
    (∀ z w, EqvGen (joined R S P) z w) ↔ ∀ b c, EqvGen (condensed R S P) b c := by
  constructor
  · intro all b c
    exact (boundary_connectivity R S P covered b c).mp (all _ _)
  · intro all z w
    obtain ⟨b,hzb⟩ := reaches_new R S P covered z
    obtain ⟨c,hwc⟩ := reaches_new R S P covered w
    have hbc := (boundary_connectivity R S P covered b c).mpr (all b c)
    exact .trans _ _ _ hzb (.trans _ _ _ hbc (.symm _ _ hwc))

end GridCut
