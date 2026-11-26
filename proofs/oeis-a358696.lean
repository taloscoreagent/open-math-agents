import OMAStatements.S_oeis_a358696

/-!
# Boundary-covering cycles in the five-row grid

This proves Seiichi Manyama's recurrence for OEIS A358696, proposed in 2022.
Cut a cycle at the horizontal edges between columns and record which pairs
of rows are joined in the prefix. The transfer graph has twenty states.
The first part verifies the recurrence for its integer transition matrix.
The remaining parts prove a bijection between the accepted mask words and
the actual cycle edge sets used in the statement.

The main counting equality is `OMA358.graph_count_eq_after_of_bijection`.
Its forward direction uses `OMA358.geom_of_admissible`, its reverse
direction uses `OMA358.acceptedWord_realized`, and injectivity comes
from `OMA358.horizontal_unique`.
-/

namespace OMA358

abbrev State := Fin 20
abbrev Vec := State → ℤ

/-- Bit j in row i records the number (zero or one) of transitions i → j.
Rows follow lexicographic order on sorted lists of paired frontier vertices. -/
def trans : Matrix State State ℤ := fun i j =>
  let rows : Array ℕ := #[300, 260, 334, 300, 41256, 41256, 295680, 262656, 1040337, 919169, 790033, 597009, 288, 288, 256, 2384, 2064, 260, 334, 300]
  if (rows.getD i.val 0).testBit j.val then 1 else 0

/-- The first column admits three possible outgoing states. -/
def firstVec : Vec := fun i => if i = 2 ∨ i = 5 ∨ i = 8 then 1 else 0

/-- The final column accepts three possible incoming states. -/
def lastVec : Vec := fun i => if i = 8 ∨ i = 9 ∨ i = 11 then 1 else 0

/-- Column completions after k interior transitions. -/
def orbit : ℕ → Vec
  | 0 => lastVec
  | k+1 => trans.mulVec (orbit k)

theorem orbit_eq_pow_mulVec (k : ℕ) : orbit k = (trans ^ k).mulVec lastVec := by
  induction k with
  | zero => simp [orbit]
  | succ k ih => rw [orbit, ih, Matrix.mulVec_mulVec, pow_succ']

/-- Count indexed by the number of interior columns. -/
def after (k : ℕ) : ℤ := dotProduct firstVec (orbit k)

/-- The transfer count at width n. Grids of widths zero and one have no cycles. -/
def count (n : ℕ) : ℤ := if 2 ≤ n then after (n-2) else 0

theorem count_add_two (k : ℕ) : count (k+2) = after k := by simp [count]

/-- Evaluation of the right side of the proposed recurrence, oldest term first. -/
def recurrenceRHS {A : Type*} [AddCommGroup A]
    (a b c d e f g h i : A) : A :=
  (6 : ℤ) • i + h - (20 : ℤ) • g + (37 : ℤ) • f + (16 : ℤ) • e -
    (12 : ℤ) • d - (7 : ℤ) • c + (5 : ℤ) • b - a

private theorem map_rhs {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (L : A →+ B) (a b c d e f g h i : A) :
    L (recurrenceRHS a b c d e f g h i) =
      recurrenceRHS (L a) (L b) (L c) (L d) (L e) (L f) (L g) (L h) (L i) := by
  simp [recurrenceRHS]

/-- Candidate values for (T^k)v for k = 0,...,9. Their transitions are checked below. -/
private def table (k : ℕ) (i : State) : ℤ :=
  let rows : Array (Array ℤ) := #[
    #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1],
    #[6, 4, 8, 6, 8, 8, 7, 2, 20, 8, 8, 8, 4, 4, 3, 7, 2, 4, 8, 6],
    #[42, 28, 45, 42, 45, 45, 43, 16, 101, 42, 52, 42, 28, 28, 20, 43, 16, 28, 45, 42],
    #[233, 146, 259, 233, 259, 259, 231, 87, 605, 267, 310, 267, 146, 146, 101, 231, 87, 146, 259, 233],
    #[1356, 864, 1474, 1356, 1474, 1474, 1362, 526, 3462, 1535, 1828, 1535, 864, 864, 605, 1362, 526, 864, 1474, 1356],
    #[7766, 4936, 8518, 7766, 8518, 8518, 7833, 3009, 20129, 8939, 10558, 8939, 4936, 4936, 3462, 7833, 3009, 4936, 8518, 7766],
    #[44931, 28647, 49182, 44931, 49182, 49182, 45419, 17457, 116151, 51492, 61004, 51492, 28647, 28647, 20129, 45419, 17457, 28647, 49182, 44931],
    #[259446, 165333, 284330, 259446, 284330, 284330, 262244, 100674, 671540, 297644, 352214, 297644, 165333, 165333, 116151, 262244, 100674, 165333, 284330, 259446],
    #[1499646, 955870, 1642893, 1499646, 1642893, 1642893, 1515758, 581974, 3879247, 1719087, 2035054, 1719087, 955870, 955870, 671540, 1515758, 581974, 955870, 1642893, 1499646]]
  (rows.getD k #[]).getD i.val 0

private theorem table_zero : lastVec = table 0 := by
  funext i
  exact (show ∀ j : State, lastVec j = table 0 j by decide) i

private theorem table_steps (k : Fin 9) (i : State) :
    trans.mulVec (table k) i = table (k.val + 1) i := by
  exact (show ∀ k : Fin 9, ∀ i : State,
    trans.mulVec (table k) i = table (k.val + 1) i by
      decide +kernel) k i

private theorem orbit_table {k : ℕ} (hk : k < 10) : orbit k = table k := by
  induction k with
  | zero => exact table_zero
  | succ k ih =>
    rw [orbit, ih (by omega)]
    funext i
    exact table_steps ⟨k, by omega⟩ i

/-- The polynomial identity P(T)v = 0, written with the leading monomial
on the left. This checks all twenty coordinates. -/
theorem krylov_identity :
    orbit 9 = recurrenceRHS (orbit 0) (orbit 1) (orbit 2) (orbit 3)
      (orbit 4) (orbit 5) (orbit 6) (orbit 7) (orbit 8) := by
  repeat' rw [orbit_table (by decide)]
  funext i
  exact (show ∀ j : State, table 9 j = recurrenceRHS (table 0) (table 1)
    (table 2) (table 3) (table 4) (table 5) (table 6) (table 7) (table 8) j by decide) i

theorem orbit_recurrence (k : ℕ) :
    orbit (k+9) = recurrenceRHS (orbit k) (orbit (k+1)) (orbit (k+2)) (orbit (k+3))
      (orbit (k+4)) (orbit (k+5)) (orbit (k+6)) (orbit (k+7)) (orbit (k+8)) := by
  induction k with
  | zero => exact krylov_identity
  | succ k ih =>
    calc
      _ = trans.mulVec (orbit (k+9)) := rfl
      _ = _ := congrArg trans.mulVec ih
      _ = _ := map_rhs trans.mulVecLin.toAddMonoidHom _ _ _ _ _ _ _ _ _

theorem after_recurrence (k : ℕ) :
    after (k+9) = recurrenceRHS (after k) (after (k+1)) (after (k+2)) (after (k+3))
      (after (k+4)) (after (k+5)) (after (k+6)) (after (k+7)) (after (k+8)) := by
  unfold after
  rw [orbit_recurrence]
  exact map_rhs ((dotProductBilin ℤ ℤ) firstVec).toAddMonoidHom _ _ _ _ _ _ _ _ _

theorem initial_counts :
    (List.range 10).map after = [1,5,36,191,1123,6410,37165,214515,1240200,7165033] := by
  calc
    _ = (List.range 10).map (fun k => dotProduct firstVec (table k)) := by
      apply List.map_congr_left
      intro k hk
      exact congrArg (dotProduct firstVec) (orbit_table (List.mem_range.mp hk))
    _ = _ := by decide +kernel

/-- The recurrence in the width indexing of the OEIS, for every n > 10. -/
theorem width_recurrence (n : ℕ) (hn : 10 < n) :
    count n = 6 * count (n-1) + count (n-2) - 20 * count (n-3) + 37 * count (n-4) +
      16 * count (n-5) - 12 * count (n-6) - 7 * count (n-7) + 5 * count (n-8) - count (n-9) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
  simpa [count, recurrenceRHS, zsmul_eq_mul] using after_recurrence k

end OMA358

/-!
Enumerating one column of a five-row lattice. Choosing a subset of its four
vertical edges determines its right edges: precisely the vertices having
degree one before right edges are included need an edge leaving the column.
A frontier component is represented by the bit mask of its two outgoing
rows. The components are sorted by their least row.
-/

namespace OMA358

/-- The twenty reachable frontier pairings, in the indexing of the matrix. -/
def frontier (i : State) : List ℕ :=
  let states : Array (List ℕ) := #[
    [3],[3,12],[3,20],[3,24],[5],[5,24],[9],[9,6],[17],[17,6],
    [17,10],[17,12],[6],[6,24],[10],[18],[18,12],[12],[20],[24]]
  states.getD i.val []

inductive ColumnKind where
  | first | middle | last
  deriving DecidableEq

private def allRows : List ℕ := List.range 5

private def maskOf (rows : List ℕ) : ℕ :=
  rows.foldl (fun m r => m ||| (1 <<< r)) 0

private def bit (mask row : ℕ) : ℕ := (mask.testBit row).toNat

/-- Merge every component incident to an edge or to an old path.
Unions are taken on vertex masks, preserving every untouched component. -/
private def connect (blocks : List ℕ) (edge : ℕ) : List ℕ :=
  let (touched, rest) := blocks.partition (fun rows => rows &&& edge != 0)
  if touched.isEmpty then rest else touched.foldl (· ||| ·) 0 :: rest

private def leastRow (mask : ℕ) : ℕ :=
  (allRows.find? mask.testBit).getD 5

/-- Local edge choice with its connected outgoing pairs, or rejection. -/
def columnStep (kind : ColumnKind) (old : List ℕ) (vertical : Fin 16) :
    Option (List ℕ) := Id.run do
  let incoming := old.foldl (· ||| ·) 0
  let down := vertical.val
  let up := down <<< 1
  let degree (r : ℕ) := bit incoming r + bit up r + bit down r
  if allRows.any (fun r => degree r > 2 ||
      (degree r == 0 && (kind != .middle || r == 0 || r == 4))) then
    return none
  let right := maskOf (allRows.filter (fun r => degree r == 1))
  if kind == .last && right != 0 then return none
  let singles := (allRows.filter (fun r => degree r != 0)).map (fun r => 1 <<< r)
  let edges := ((List.range 4).filter down.testBit).map (fun r => 3 <<< r)
  let components := (old ++ edges).foldl connect singles
  if kind == .last then
    return if components.length == 1 then some [] else none
  let ends := components.map (fun block => block &&& right)
  if ends.all (fun b => (allRows.filter b.testBit).length == 2) then
    return some (ends.insertionSort (fun a b => leastRow a ≤ leastRow b))
  else
    return none

/-- Multiplicity counts actual choices of the four vertical edges. -/
def outcomes (kind : ColumnKind) (old : List ℕ) : List (List ℕ) :=
  (List.finRange 16).filterMap (columnStep kind old)

private def expand (weights : State → ℤ) : List (List ℕ) :=
  (List.finRange 20).flatMap (fun j => List.replicate (weights j).toNat (frontier j))

/-- Equality of the complete lists up to order retains multiplicities and
implies that no successful choice produces an unlisted frontier pairing. -/
theorem first_outcomes : (outcomes .first []).Perm (expand firstVec) := by decide +kernel

theorem middle_outcomes (i : State) :
    (outcomes .middle (frontier i)).Perm (expand (trans i)) := by
  exact (show ∀ j : State,
    (outcomes .middle (frontier j)).Perm (expand (trans j)) by decide +kernel) i

theorem last_outcomes (i : State) :
    outcomes .last (frontier i) = List.replicate (lastVec i).toNat [] := by
  exact (show ∀ j : State,
    outcomes .last (frontier j) = List.replicate (lastVec j).toNat [] by decide +kernel) i

/-- Distinct table indices code distinct frontier pairings. -/
theorem frontier_injective : Function.Injective frontier := by
  exact (show ∀ i j : State, frontier i = frontier j → i = j by decide +kernel)

abbrev ColumnMask := Fin 16
abbrev MaskWord := List ColumnMask

/-- Prefix every successful choice of vertical mask to all of its completions. -/
def prependChoices (choices : List ColumnMask) (step : ColumnMask → Option (List ℕ))
    (tailWords : List ℕ → List MaskWord) : List MaskWord :=
  choices.flatMap fun v =>
    match step v with
    | none => []
    | some outgoing => (tailWords outgoing).map (v :: ·)

/-- All accepted vertical-mask words comprising k intermediate columns and one last column. -/
def wordsFrom : ℕ → List ℕ → List MaskWord
  | 0, old => prependChoices (List.finRange 16) (columnStep .last old) fun _ => [[]]
  | k+1, old => prependChoices (List.finRange 16) (columnStep .middle old) (wordsFrom k)

/-- All accepted vertical-mask words, including both boundary columns. -/
def acceptedWords (k : ℕ) : List MaskWord :=
  prependChoices (List.finRange 16) (columnStep .first []) (wordsFrom k)

private theorem length_prependChoices (choices : List ColumnMask)
    (step : ColumnMask → Option (List ℕ)) (tails : List ℕ → List MaskWord) :
    ((prependChoices choices step tails).length : ℤ) =
      ((choices.filterMap step).map (fun s => ((tails s).length : ℤ))).sum := by
  induction choices with
  | nil => simp [prependChoices]
  | cons v vs ih =>
    cases he : step v <;> simpa [prependChoices, he, List.filterMap_cons] using ih

private theorem sum_finRange {n : ℕ} (f : Fin n → ℤ) :
    ((List.finRange n).map f).sum = ∑ i, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, Fin.sum_univ_succ]
    simp [List.map_map, ih]

private theorem sum_expansion (w : State → ℤ) (hw : ∀ j, 0 ≤ w j) (f : List ℕ → ℤ) :
    ((expand w).map f).sum = dotProduct w (fun i => f (frontier i)) := by
  have h (l : List State) :
      ((l.flatMap fun j => List.replicate (w j).toNat (frontier j)).map f).sum =
        (l.map (fun j => w j * f (frontier j))).sum := by
    induction l with
    | nil => rfl
    | cons j l ih =>
      simp [List.map_replicate, List.sum_replicate, Int.toNat_of_nonneg (hw j), ih]
  exact (h _).trans (sum_finRange _)

private theorem last_nonneg (i : State) : 0 ≤ lastVec i := by
  simp [lastVec]; split <;> decide

private theorem trans_nonneg (i j : State) : 0 ≤ trans i j := by
  dsimp [trans]; split <;> decide

private theorem first_nonneg (i : State) : 0 ≤ firstVec i := by
  simp [firstVec]; split <;> decide

theorem wordsFrom_length (k : ℕ) (i : State) :
    ((wordsFrom k (frontier i)).length : ℤ) = orbit k i := by
  induction k generalizing i with
  | zero =>
    rw [wordsFrom, length_prependChoices]
    change ((outcomes .last (frontier i)).map fun _ => (1 : ℤ)).sum = lastVec i
    rw [last_outcomes]
    simp [List.sum_replicate, Int.toNat_of_nonneg (last_nonneg i)]
  | succ k ih =>
    rw [wordsFrom, length_prependChoices]
    let f (s : List ℕ) : ℤ := (wordsFrom k s).length
    change ((outcomes .middle (frontier i)).map f).sum = trans.mulVec (orbit k) i
    rw [((middle_outcomes i).map f).sum_eq, sum_expansion _ (trans_nonneg i)]
    exact congrArg (dotProduct (trans i)) (funext ih)

/-- All accepted raw edge-mask sequences of width k+2, counted once per sequence. -/
theorem acceptedWords_length (k : ℕ) :
    ((acceptedWords k).length : ℤ) = after k := by
  rw [acceptedWords, length_prependChoices]
  let f (s : List ℕ) : ℤ := (wordsFrom k s).length
  change ((outcomes .first []).map f).sum = after k
  rw [(first_outcomes.map f).sum_eq, sum_expansion _ first_nonneg]
  exact congrArg (dotProduct firstVec) (funext (wordsFrom_length k))

private theorem words_have_prefix {choices : List ColumnMask}
    {step : ColumnMask → Option (List ℕ)} {tails : List ℕ → List MaskWord}
    {w : MaskWord} (hw : w ∈ prependChoices choices step tails) :
    ∃ v ∈ choices, ∃ t, w = v :: t := by
  obtain ⟨v, hv, hw⟩ := List.mem_flatMap.mp hw
  refine ⟨v, hv, ?_⟩
  cases he : step v with
  | none => simp [he] at hw
  | some s =>
    simp only [he] at hw
    obtain ⟨t, _, ht⟩ := List.mem_map.mp hw
    exact ⟨t, ht.symm⟩

private theorem prependChoices_nodup (choices : List ColumnMask)
    (step : ColumnMask → Option (List ℕ)) (tails : List ℕ → List MaskWord)
    (hc : choices.Nodup) (ht : ∀ s, (tails s).Nodup) :
    (prependChoices choices step tails).Nodup := by
  induction choices with
  | nil => simp [prependChoices]
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hc
    cases he : step v with
    | none => simpa [prependChoices, he] using ih hvs
    | some s =>
      change ((match step v with
        | none => []
        | some s => (tails s).map (v :: ·)) ++ prependChoices vs step tails).Nodup
      rw [he]
      apply List.nodup_append.mpr
      refine ⟨(ht s).map (by intro a b h; simpa using h), ih hvs, ?_⟩
      intro a ha b hb heq
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨v', hv', t', hb'⟩ := words_have_prefix hb
      have hvv' : v = v' := (List.cons.inj (heq.trans hb')).1
      exact hv (hvv' ▸ hv')

theorem wordsFrom_nodup (k : ℕ) (s : List ℕ) : (wordsFrom k s).Nodup := by
  induction k generalizing s with
  | zero => exact prependChoices_nodup _ _ _ (List.nodup_finRange _) (by simp)
  | succ k ih => exact prependChoices_nodup _ _ _ (List.nodup_finRange _) ih

theorem acceptedWords_nodup (k : ℕ) : (acceptedWords k).Nodup :=
  prependChoices_nodup _ _ _ (List.nodup_finRange _) (wordsFrom_nodup k)

/-- Set cardinality of distinct accepted edge words agrees with the transfer count. -/
theorem acceptedWords_card (k : ℕ) : ((acceptedWords k).toFinset.card : ℤ) = after k := by
  rw [List.toFinset_card_of_nodup (acceptedWords_nodup k), acceptedWords_length]

end OMA358

namespace OMA358

/-- Adjacencies on the new column before adding outgoing horizontal edges.
Each old path is contracted to an edge joining its two endpoints. -/
def columnGraph (old : List ℕ) (down : Fin 16) : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun a b =>
    (a.val + 1 = b.val ∧ down.val.testBit a.val) ∨
    (old.any fun p => p.testBit a.val && p.testBit b.val) = true

instance (old : List ℕ) (down : Fin 16) : DecidableRel (columnGraph old down).Adj :=
  fun _ _ => by unfold columnGraph; infer_instance

/-- Degrees before the outgoing cut edges have been attached. -/
def beforeExit (old : List ℕ) (vertical : Fin 16) (r : Fin 5) : ℕ :=
  (old.any fun p => p.testBit r.val).toNat +
  ((vertical.val <<< 1).testBit r.val).toNat + (vertical.val.testBit r.val).toNat

def validDegree (kind : ColumnKind) (r : Fin 5) (d : ℕ) : Prop :=
  d ≤ 2 ∧ ((kind ≠ .middle ∨ r.val = 0 ∨ r.val = 4) → 0 < d) ∧
    (kind = .last → d ≠ 1)

def active (s : List ℕ) (v : Fin 16) : Finset (Fin 5) :=
  Finset.univ.filter fun r => beforeExit s v r ≠ 0

def exitRows (s : List ℕ) (v : Fin 16) : Finset (Fin 5) :=
  Finset.univ.filter fun r => beforeExit s v r = 1

def pathsMatch (s : List ℕ) (v : Fin 16) (out : List ℕ) : Prop :=
  ∀ i j : Fin 5, (out.any fun p => p.testBit i.val && p.testBit j.val) = true ↔
    i ∈ exitRows s v ∧ j ∈ exitRows s v ∧ (columnGraph s v).Reachable i j


/-- The degree constraints and connectivity conditions expressed using graph reachability. -/
def geometricChoice (kind : ColumnKind) (s : List ℕ) (v : Fin 16) : Prop :=
  (∀ r : Fin 5, validDegree kind r (beforeExit s v r)) ∧
  if kind = .last then
    ∀ i ∈ active s v, ∀ j ∈ active s v, (columnGraph s v).Reachable i j
  else
    ∀ i ∈ active s v, ((exitRows s v).filter ((columnGraph s v).Reachable i)).card = 2

private instance (k : ColumnKind) (s : List ℕ) (v : Fin 16) : Decidable (geometricChoice k s v) := by
  unfold geometricChoice validDegree
  split <;> infer_instance

/-- All accepted and rejected local cases agree with degree and Mathlib connectivity.
The computed outgoing pairing records exactly the reachability of the cut vertices. -/
def graphCheck (kind : ColumnKind) (s : List ℕ) (v : Fin 16) : Prop :=
  ((columnStep kind s v).isSome ↔ geometricChoice kind s v) ∧
  match columnStep kind s v with
  | none => True
  | some out => if kind = .last then out = [] else pathsMatch s v out

private instance (k : ColumnKind) (s : List ℕ) (v : Fin 16) : Decidable (graphCheck k s v) := by
  unfold graphCheck
  split
  · infer_instance
  · split
    · infer_instance
    · unfold pathsMatch
      infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem column_checks :
    (∀ v : Fin 16, graphCheck .first [] v) ∧
    (∀ (i : State) (v : Fin 16), graphCheck .middle (frontier i) v) ∧
    (∀ (i : State) (v : Fin 16), graphCheck .last (frontier i) v) := by decide +kernel

end OMA358

namespace OMA358

/-- An ordered sequence of k middle columns followed by one closing column,
starting at the specified pairing of incoming frontier rows. -/
inductive HistoryFrom : ℕ → List ℕ → MaskWord → Prop
  | last {s v} (h : columnStep .last s v = some []) :
      HistoryFrom 0 s [v]
  | middle {k s v next tail} (h : columnStep .middle s v = some next)
      (rest : HistoryFrom k next tail) : HistoryFrom (k+1) s (v :: tail)

/-- An opening mask, then k middle masks, then a closing mask. -/
def IsColumnHistory (k : ℕ) : MaskWord → Prop
  | [] => False
  | v :: tail => ∃ s, columnStep .first [] v = some s ∧ HistoryFrom k s tail

private theorem last_output_empty {s : List ℕ} {v : ColumnMask} {t : List ℕ}
    (h : columnStep .last s v = some t) : t = [] := by
  unfold columnStep at h
  simp [Id.run] at h
  split at h <;> try simp_all
  split at h <;> try simp_all
  split at h <;> try simp_all
  exact (Option.some.inj h).symm

private theorem mem_prepend {w : MaskWord} {step : ColumnMask → Option (List ℕ)}
    {tails : List ℕ → List MaskWord} :
    w ∈ prependChoices (List.finRange 16) step tails ↔
      ∃ v s t, step v = some s ∧ t ∈ tails s ∧ w = v :: t := by
  simp only [prependChoices, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨v, hw⟩
    cases he : step v with
    | none => simp [he] at hw
    | some s =>
      simp only [he] at hw
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
      exact ⟨v, s, t, he, ht, rfl⟩
  · rintro ⟨v, s, t, he, ht, rfl⟩
    exact ⟨v, by simp [he, ht]⟩

theorem mem_wordsFrom_iff {k : ℕ} {s : List ℕ} {w : MaskWord} :
    w ∈ wordsFrom k s ↔ HistoryFrom k s w := by
  induction k generalizing s w with
  | zero =>
    rw [wordsFrom, mem_prepend]
    constructor
    · rintro ⟨v, t, rest, he, hr, rfl⟩
      simp only [List.mem_singleton] at hr
      subst rest
      have ht := last_output_empty he
      subst t
      exact .last he
    · intro h
      cases h with
      | last he => exact ⟨_, [], [], he, by simp, rfl⟩
  | succ k ih =>
    rw [wordsFrom, mem_prepend]
    constructor
    · rintro ⟨v, t, rest, he, hr, rfl⟩
      exact .middle he (ih.mp hr)
    · intro h
      cases h with
      | middle he hr => exact ⟨_, _, _, he, ih.mpr hr, rfl⟩

theorem mem_acceptedWords_iff {k : ℕ} {w : MaskWord} :
    w ∈ acceptedWords k ↔ IsColumnHistory k w := by
  rw [acceptedWords, mem_prepend]
  constructor
  · rintro ⟨v, s, t, he, ht, rfl⟩
    exact ⟨s, he, mem_wordsFrom_iff.mp ht⟩
  · cases w with
    | nil => exact False.elim
    | cons v t =>
      rintro ⟨s, he, ht⟩
      exact ⟨v, s, t, he, mem_wordsFrom_iff.mpr ht, rfl⟩

theorem HistoryFrom.length {k s w} (h : HistoryFrom k s w) : w.length = k+1 := by
  induction h with
  | last => rfl
  | middle _ _ ih => simp [ih]

theorem IsColumnHistory.length {k w} (h : IsColumnHistory k w) : w.length = k+2 := by
  cases w with
  | nil => exact False.elim h
  | cons v tail =>
    obtain ⟨s, _, hs⟩ := h
    simp [hs.length]

/-- Construct a history from one mask and one incoming frontier per column
of a suffix. This lets a graph-derived family of frontiers be used directly. -/
theorem historyFrom_of_frontiers {k : ℕ} (masks : Fin (k+1) → ColumnMask)
    (fronts : Fin (k+1) → List ℕ)
    (hm : ∀ i : Fin k, columnStep .middle (fronts i.castSucc) (masks i.castSucc) =
      some (fronts i.succ))
    (hl : columnStep .last (fronts (Fin.last k)) (masks (Fin.last k)) = some []) :
    HistoryFrom k (fronts 0) (List.ofFn masks) := by
  induction k with
  | zero =>
    rw [List.ofFn_succ]
    exact .last hl
  | succ k ih =>
    rw [List.ofFn_succ]
    apply HistoryFrom.middle (hm 0)
    exact ih (fun i => masks i.succ) (fun i => fronts i.succ) (fun i => hm i.succ) hl

/-- Membership certificate indexed by grid columns. For a width of k+2,
supply the graph's vertical edge mask at each column and its frontier on each
of the k+1 cuts between consecutive columns. -/
theorem mem_acceptedWords_of_frontiers {k : ℕ} (masks : Fin (k+2) → ColumnMask)
    (fronts : Fin (k+1) → List ℕ)
    (hf : columnStep .first [] (masks 0) = some (fronts 0))
    (hm : ∀ i : Fin k, columnStep .middle (fronts i.castSucc)
      (masks i.castSucc.succ) = some (fronts i.succ))
    (hl : columnStep .last (fronts (Fin.last k)) (masks (Fin.last (k+1))) = some []) :
    List.ofFn masks ∈ acceptedWords k := by
  apply mem_acceptedWords_iff.mpr
  rw [List.ofFn_succ]
  exact ⟨fronts 0, hf, historyFrom_of_frontiers (fun i => masks i.succ) fronts hm hl⟩

end OMA358

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

namespace OMA358

open OMA.S_oeis_a358696

private theorem hit_le_one {α β : Type*} [DecidableEq β] (sel : Finset α) (e : α ↪ β) (v : β) :
    hit sel e v ≤ 1 := by
  unfold hit
  split <;> decide

private theorem incoming_mem_iff_of_previous {n : ℕ} (a b : Finset (Fin 5 × Fin (n-1)))
    (p : Fin 5 × Fin (n-1))
    (hp : ∀ q : Fin 5 × Fin (n-1), q.2.val < p.2.val → (q ∈ a ↔ q ∈ b)) :
    hStart p ∈ a.map hEnd ↔ hStart p ∈ b.map hEnd := by
  simp only [Finset.mem_map]
  apply exists_congr
  intro q
  apply and_congr_left
  intro he
  apply hp
  have hcol := congrArg (fun x : Vertex n => x.2.val) he
  change q.2.val + 1 = p.2.val at hcol
  omega

/-- With fixed vertical edges, knowing the incoming horizontal edge and the
even degree at a vertex determines the outgoing horizontal edge. -/
private theorem outgoing_hit_eq {n : ℕ} {vert : Finset (Fin 4 × Fin n)}
    {a b : Finset (Fin 5 × Fin (n-1))} (ha : localTests vert a) (hb : localTests vert b)
    (w : Vertex n) (he : hit a hEnd w = hit b hEnd w) :
    hit a hStart w = hit b hStart w := by
  have h₁ := ha w
  have h₂ := hb w
  have ba := hit_le_one a hStart w
  have bb := hit_le_one b hStart w
  unfold localDegree at h₁ h₂
  omega

/-- Every entire row of horizontal edges is determined, left to right, by the
vertical edges and the local degree tests. -/
theorem horizontal_unique {n : ℕ} {vert : Finset (Fin 4 × Fin n)}
    {a b : Finset (Fin 5 × Fin (n-1))} (ha : localTests vert a) (hb : localTests vert b) :
    a = b := by
  have agree (k : ℕ) : ∀ p : Fin 5 × Fin (n-1), p.2.val = k → (p ∈ a ↔ p ∈ b) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro p hk
      have hin := incoming_mem_iff_of_previous a b p (fun q hq => ih q.2.val (hk ▸ hq) q rfl)
      have hout := outgoing_hit_eq ha hb (hStart p) (by simp only [hit, hin])
      have startMem (s : Finset (Fin 5 × Fin (n-1))) :
          hStart p ∈ s.map hStart ↔ p ∈ s := Finset.mem_map' _
      simp only [hit, startMem] at hout
      by_cases hpa : p ∈ a <;> by_cases hpb : p ∈ b <;> simp_all
  ext p
  exact agree p.2.val p rfl

/-- Forgetting horizontal edges gives an injection on admissible edge arrays. -/
def admissibleVerticalEmbedding (n : ℕ) :
    {arr : EdgeArrays n // admissible arr} ↪ Finset (Fin 4 × Fin n) where
  toFun arr := arr.val.1
  inj' := by
    rintro ⟨⟨vert,a⟩,ha⟩ ⟨⟨vert',b⟩,hb⟩ he
    change vert = vert' at he
    subst vert'
    have := horizontal_unique ha.2 hb.2
    cases this
    rfl

noncomputable def cycleVerticalEmbedding (n : ℕ) :
    {E : Finset (Sym2 (Vertex n)) // isBoundaryCycle E} ↪ Finset (Fin 4 × Fin n) :=
  (cycleArrayEquiv n).symm.toEmbedding.trans (admissibleVerticalEmbedding n)

end OMA358

namespace OMA358

/-- The bits of a column mask, from the least significant (row zero) upwards. -/
def encodeEdgeMasks {rows cols : ℕ} (edges : Finset (Fin rows × Fin cols))
    (j : Fin cols) : Fin (2 ^ rows) :=
  let bits := List.ofFn (fun i : Fin rows => decide ((i, j) ∈ edges))
  let m := BitVec.ofBoolListLE bits
  ⟨m.toNat, by simpa [m, bits] using m.toFin.isLt⟩

/-- Recover the edge coordinates by testing the corresponding row bits. -/
def decodeEdgeMasks {rows cols : ℕ} (masks : Fin cols → Fin (2 ^ rows)) :
    Finset (Fin rows × Fin cols) :=
  Finset.univ.filter (fun ij => (masks ij.2).val.testBit ij.1.val)

theorem encodeEdgeMasks_testBit {rows cols} (edges : Finset (Fin rows × Fin cols))
    (i : Fin rows) (j : Fin cols) :
    (encodeEdgeMasks edges j).val.testBit i.val = decide ((i, j) ∈ edges) := by
  simp only [encodeEdgeMasks, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp)]
  simp

@[simp] theorem mem_decodeEdgeMasks {rows cols} (masks : Fin cols → Fin (2 ^ rows))
    (i : Fin rows) (j : Fin cols) :
    (i, j) ∈ decodeEdgeMasks masks ↔ (masks j).val.testBit i.val = true := by
  simp [decodeEdgeMasks]

private theorem eq_mask_of_bits {r} {a b : Fin (2 ^ r)}
    (h : ∀ i : Fin r, a.val.testBit i.val = b.val.testBit i.val) : a = b := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < r
  · exact h ⟨i, hi⟩
  · have hbnd : 2 ^ r ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (a.isLt.trans_le hbnd),
      Nat.testBit_eq_false_of_lt (b.isLt.trans_le hbnd)]

/-- Each edge-coordinate finset corresponds to one fixed-width binary mask
per column. This applies also to zero rows and to zero columns. -/
def rowMaskEquiv (rows cols : ℕ) :
    Finset (Fin rows × Fin cols) ≃ (Fin cols → Fin (2 ^ rows)) where
  toFun := encodeEdgeMasks
  invFun := decodeEdgeMasks
  left_inv edges := by
    ext ⟨i, j⟩
    simp [encodeEdgeMasks_testBit]
  right_inv masks := by
    funext j
    apply eq_mask_of_bits
    intro i
    rw [encodeEdgeMasks_testBit]
    simp

/-- Vertical edge i joins grid rows i and i+1 in column j. -/
abbrev verticalMaskEquiv (n : ℕ) :
    Finset (Fin 4 × Fin n) ≃ (Fin n → Fin 16) :=
  rowMaskEquiv 4 n

/-- Horizontal edge i in cut j joins neighboring columns j and j+1 in row i. -/
abbrev horizontalMaskEquiv (n : ℕ) :
    Finset (Fin 5 × Fin (n-1)) ≃ (Fin (n-1) → Fin 32) :=
  rowMaskEquiv 5 (n-1)

theorem vertical_testBit_iff {n} (edges : Finset (Fin 4 × Fin n)) (i : Fin 4) (j : Fin n) :
    ((verticalMaskEquiv n edges) j).val.testBit i.val = true ↔ (i, j) ∈ edges := by
  change (encodeEdgeMasks edges j).val.testBit i.val = true ↔ _
  rw [encodeEdgeMasks_testBit]
  simp

theorem horizontal_testBit_iff {n} (edges : Finset (Fin 5 × Fin (n-1)))
    (i : Fin 5) (j : Fin (n-1)) :
    ((horizontalMaskEquiv n edges) j).val.testBit i.val = true ↔ (i, j) ∈ edges := by
  change (encodeEdgeMasks edges j).val.testBit i.val = true ↔ _
  rw [encodeEdgeMasks_testBit]
  simp

/-- A coordinate function on n columns is equivalent to a word of length n. -/
def listOfFnEquiv (n : ℕ) (α : Type*) : (Fin n → α) ≃ {w : List α // w.length = n} where
  toFun f := ⟨List.ofFn f, List.length_ofFn⟩
  invFun w i := w.val[i.val]'(by rw [w.property]; exact i.isLt)
  left_inv f := by funext i; simp
  right_inv w := by
    obtain ⟨w, rfl⟩ := w
    apply Subtype.ext
    exact List.ofFn_getElem

/-- Exactly the raw word type used for accepted column histories, with its length certified. -/
def verticalWordEquiv (n : ℕ) :
    Finset (Fin 4 × Fin n) ≃ {w : List (Fin 16) // w.length = n} :=
  (verticalMaskEquiv n).trans (listOfFnEquiv n (Fin 16))

def horizontalWordEquiv (n : ℕ) :
    Finset (Fin 5 × Fin (n-1)) ≃ {w : List (Fin 32) // w.length = n-1} :=
  (horizontalMaskEquiv n).trans (listOfFnEquiv (n-1) (Fin 32))

@[simp] theorem verticalWordEquiv_apply {n} (edges : Finset (Fin 4 × Fin n)) :
    (verticalWordEquiv n edges).val = List.ofFn (verticalMaskEquiv n edges) := rfl

@[simp] theorem horizontalWordEquiv_apply {n} (edges : Finset (Fin 5 × Fin (n-1))) :
    (horizontalWordEquiv n edges).val = List.ofFn (horizontalMaskEquiv n edges) := rfl

end OMA358

namespace OMA358

open OMA.S_oeis_a358696

/-- Horizontal row mask on the cut immediately to the left of column j.
The first column has no incoming cut. -/
def incomingMask {n : ℕ} (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) : ℕ :=
  if h : 0 < j.val then
    (horizontalMaskEquiv n hor ⟨j.val - 1, by have := j.isLt; omega⟩).val
  else 0

/-- Horizontal row mask on the cut immediately to the right of column j.
The last column has no outgoing cut. -/
def outgoingMask {n : ℕ} (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) : ℕ :=
  if h : j.val+1 < n then
    (horizontalMaskEquiv n hor ⟨j.val, by omega⟩).val
  else 0

@[simp] theorem incomingMask_first {n} (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n)
    (hj : j.val = 0) : incomingMask hor j = 0 := by simp [incomingMask, hj]

@[simp] theorem outgoingMask_last {n} (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n)
    (hj : j.val+1 = n) : outgoingMask hor j = 0 := by simp [outgoingMask, hj]

/-- Precisely the incoming half-edges are present in the recorded pairing.
The relation imposes only this incidence condition; it does not assume connectivity. -/
def recordsIncoming {n} (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) (old : List ℕ) : Prop :=
  ∀ r : Fin 5, (old.any (fun p => p.testBit r.val)) = (incomingMask hor j).testBit r.val

theorem empty_records_first {n} (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n)
    (hj : j.val = 0) : recordsIncoming hor j [] := by
  intro r
  simp [incomingMask_first hor j hj]

private theorem hit_bit {α β : Type*} [DecidableEq β] (s : Finset α)
    (e : α ↪ β) (v : β) (b : Bool) (h : v ∈ s.map e ↔ b = true) :
    hit s e v = b.toNat := by
  cases b <;> simp_all [hit]

theorem hit_down {n} (vert : Finset (Fin 4 × Fin n)) (j : Fin n) (r : Fin 5) :
    hit vert vStart (r,j) = ((verticalMaskEquiv n vert j).val.testBit r.val).toNat := by
  apply hit_bit
  by_cases hr : r.val < 4
  · let d : Fin 4 := ⟨r.val,hr⟩
    change _ ↔ (verticalMaskEquiv n vert j).val.testBit d.val = true
    rw [vertical_testBit_iff]
    have he : vStart (d,j) = (r,j) := rfl
    rw [← he]
    exact Finset.mem_map' _
  · have hpow : 2^4 ≤ 2^r.val := Nat.pow_le_pow_right (by decide) (by omega)
    have hbit := Nat.testBit_eq_false_of_lt ((verticalMaskEquiv n vert j).isLt.trans_le hpow)
    rw [hbit]
    simp only [Bool.false_eq_true, iff_false]
    rintro h
    obtain ⟨⟨d,k⟩, _, he⟩ := Finset.mem_map.mp h
    have he' := congrArg (fun v : Vertex n => v.1.val) he
    change d.val = r.val at he'
    have := d.isLt
    omega

theorem hit_up {n} (vert : Finset (Fin 4 × Fin n)) (j : Fin n) (r : Fin 5) :
    hit vert vEnd (r,j) = (((verticalMaskEquiv n vert j).val <<< 1).testBit r.val).toNat := by
  apply hit_bit
  rw [Nat.testBit_shiftLeft]
  by_cases hr : 1 ≤ r.val
  · simp only [hr, decide_true, Bool.true_and]
    let d : Fin 4 := ⟨r.val-1, by have := r.isLt; omega⟩
    change _ ↔ (verticalMaskEquiv n vert j).val.testBit d.val = true
    rw [vertical_testBit_iff]
    have he : vEnd (d,j) = (r,j) := by
      apply Prod.ext
      · apply Fin.ext
        change r.val-1+1 = r.val
        omega
      · rfl
    rw [← he]
    exact Finset.mem_map' _
  · simp only [hr, decide_false, Bool.false_and, Bool.false_eq_true, iff_false]
    intro hm
    obtain ⟨⟨d,k⟩, _, he⟩ := Finset.mem_map.mp hm
    have he' := congrArg (fun v : Vertex n => v.1.val) he
    change d.val + 1 = r.val at he'
    omega

theorem hit_incoming {n} (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) (r : Fin 5) :
    hit hor hEnd (r,j) = ((incomingMask hor j).testBit r.val).toNat := by
  apply hit_bit
  unfold incomingMask
  split
  next hj =>
    let d : Fin (n-1) := ⟨j.val-1, by have := j.isLt; omega⟩
    change _ ↔ (horizontalMaskEquiv n hor d).val.testBit r.val = true
    rw [horizontal_testBit_iff]
    have he : hEnd (r,d) = (r,j) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change j.val - 1 + 1 = j.val
        omega
    rw [← he]
    exact Finset.mem_map' _
  next hj =>
    simp only [Nat.zero_testBit, Bool.false_eq_true, iff_false]
    intro hm
    obtain ⟨⟨t,k⟩, _, he⟩ := Finset.mem_map.mp hm
    have he' := congrArg (fun v : Vertex n => v.2.val) he
    change k.val+1 = j.val at he'
    omega

theorem hit_outgoing {n} (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) (r : Fin 5) :
    hit hor hStart (r,j) = ((outgoingMask hor j).testBit r.val).toNat := by
  apply hit_bit
  unfold outgoingMask
  split
  next hj =>
    let d : Fin (n-1) := ⟨j.val, by omega⟩
    change _ ↔ (horizontalMaskEquiv n hor d).val.testBit r.val = true
    rw [horizontal_testBit_iff]
    have he : hStart (r,d) = (r,j) := rfl
    rw [← he]
    exact Finset.mem_map' _
  next hj =>
    simp only [Nat.zero_testBit, Bool.false_eq_true, iff_false]
    intro hm
    obtain ⟨⟨t,k⟩, _, he⟩ := Finset.mem_map.mp hm
    have he' := congrArg (fun v : Vertex n => v.2.val) he
    change k.val = j.val at he'
    have := k.isLt
    omega

/-- The four incidences of the actual grid vertex, including both boundary cases. -/
theorem localDegree_bits {n} (vert : Finset (Fin 4 × Fin n)) (hor : Finset (Fin 5 × Fin (n-1)))
    (r : Fin 5) (j : Fin n) :
    localDegree vert hor (r,j) = ((incomingMask hor j).testBit r.val).toNat +
      (((verticalMaskEquiv n vert j).val <<< 1).testBit r.val).toNat +
      ((verticalMaskEquiv n vert j).val.testBit r.val).toNat +
      ((outgoingMask hor j).testBit r.val).toNat := by
  rw [localDegree, hit_incoming, hit_up, hit_down, hit_outgoing]

theorem localDegree_eq_beforeExit_add {n} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) {old : List ℕ}
    (hrec : recordsIncoming hor j old) (r : Fin 5) :
    localDegree vert hor (r,j) = beforeExit old (verticalMaskEquiv n vert j) r +
      ((outgoingMask hor j).testBit r.val).toNat := by
  rw [localDegree_bits, beforeExit, hrec]

noncomputable local instance coordNeighbors {n} (sel : Finset (EdgePos n)) (v : Vertex n) :
    Fintype ((selectedGraph sel).neighborSet v) := Fintype.ofFinite _

theorem graphDegree_eq_beforeExit_add {n} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) {old : List ℕ}
    (hrec : recordsIncoming hor j old) (r : Fin 5) :
    (selectedGraph (vert.disjSum hor)).degree (r,j) =
      beforeExit old (verticalMaskEquiv n vert j) r +
        ((outgoingMask hor j).testBit r.val).toNat := by
  rw [degree_eq_localDegree, localDegree_eq_beforeExit_add vert hor j hrec]

theorem outgoing_iff_beforeExit_one {n} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor)
    (j : Fin n) {old : List ℕ} (hrec : recordsIncoming hor j old) (r : Fin 5) :
    (outgoingMask hor j).testBit r.val = true ↔
      beforeExit old (verticalMaskEquiv n vert j) r = 1 := by
  have h := ht (r,j)
  rw [localDegree_eq_beforeExit_add vert hor j hrec] at h
  cases hb : (outgoingMask hor j).testBit r.val <;> simp_all
  omega

theorem localTests_boundary_degree {n} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor) (v : Vertex n)
    (hv : boundary v) : localDegree vert hor v = 2 := by
  rcases ht v with h | ⟨h', _⟩
  · exact h
  · exact (h' hv).elim

/-- Row by row the actual graph passes exactly the degree conditions required by the
column checker. The two implications classify the designated column as first/middle/last. -/
theorem validDegree_of_localTests {n} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor) (j : Fin n)
    {old : List ℕ} (hrec : recordsIncoming hor j old) (kind : ColumnKind)
    (hside : kind ≠ .middle → j.val = 0 ∨ j.val+1 = n)
    (hlast : kind = .last → j.val+1 = n) (r : Fin 5) :
    validDegree kind r (beforeExit old (verticalMaskEquiv n vert j) r) := by
  have he := localDegree_eq_beforeExit_add vert hor j hrec r
  have hh := ht (r,j)
  have hb : ((outgoingMask hor j).testBit r.val).toNat ≤ 1 := by
    cases (outgoingMask hor j).testBit r.val <;> decide
  refine ⟨by omega, ?_, ?_⟩
  · intro h
    have hbound : boundary (r,j) := by
      change r.val = 0 ∨ r.val + 1 = 5 ∨ j.val = 0 ∨ j.val+1 = n
      rcases h with h | h | h
      · exact Or.inr (Or.inr (hside h))
      · exact Or.inl h
      · exact Or.inr (Or.inl (by omega))
    have h2 := localTests_boundary_degree ht (r,j) hbound
    omega
  · intro hl
    rw [outgoingMask_last hor j (hlast hl)] at he
    simp only [Nat.zero_testBit, Bool.toNat_false, Nat.add_zero] at he
    omega

/-- Active rows computed by the transfer coincide with actual graph support. -/
theorem mem_active_iff_graph_support {n} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor) (j : Fin n)
    {old : List ℕ} (hrec : recordsIncoming hor j old) (r : Fin 5) :
    r ∈ active old (verticalMaskEquiv n vert j) ↔
      (r,j) ∈ (selectedGraph (vert.disjSum hor)).support := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_support_iff_localDegree_pos]
  rw [localDegree_eq_beforeExit_add vert hor j hrec]
  have hh := outgoing_iff_beforeExit_one ht j hrec r
  cases hb : (outgoingMask hor j).testBit r.val <;> simp_all

/-- Exit rows are precisely the selected actual outgoing horizontal edges. -/
theorem mem_exitRows_iff_outgoing {n} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor) (j : Fin n)
    {old : List ℕ} (hrec : recordsIncoming hor j old) (r : Fin 5) :
    r ∈ exitRows old (verticalMaskEquiv n vert j) ↔ (outgoingMask hor j).testBit r.val = true := by
  simpa [exitRows] using (outgoing_iff_beforeExit_one ht j hrec r).symm

theorem incomingMask_eq_prev_outgoing {n} (hor : Finset (Fin 5 × Fin (n-1))) {j k : Fin n}
    (hjk : j.val+1 = k.val) : incomingMask hor k = outgoingMask hor j := by
  have hk : 0 < k.val := by omega
  have hj : j.val+1 < n := hjk ▸ k.isLt
  simp only [incomingMask, outgoingMask, dif_pos hj, dif_pos hk]
  apply congrArg (fun d : Fin (n-1) => (horizontalMaskEquiv n hor d).val)
  apply Fin.ext
  change k.val - 1 = j.val
  omega

/-- Correctly recorded pairings retain the incidence invariant at the next cut. -/
theorem recordsIncoming_next {n} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor) {j k : Fin n}
    (hjk : j.val+1 = k.val) {old next : List ℕ} (hrec : recordsIncoming hor j old)
    (hmatch : pathsMatch old (verticalMaskEquiv n vert j) next) :
    recordsIncoming hor k next := by
  intro r
  rw [incomingMask_eq_prev_outgoing hor hjk]
  apply Bool.eq_iff_iff.mpr
  have h := hmatch r r
  simp [exitRows] at h
  simpa using h.trans (outgoing_iff_beforeExit_one ht j hrec r).symm

end OMA358

namespace GridPrefix

open Relation

variable {V : Type*}

abbrev Prefix (col : V → ℕ) (k : ℕ) := {x : V // col x < k}
abbrev Column (col : V → ℕ) (k : ℕ) := {x : V // col x = k}

def prefGraph (G : SimpleGraph V) (col : V → ℕ) (k : ℕ) : SimpleGraph (Prefix col k) :=
  G.induce {x | col x < k}

def within (G : SimpleGraph V) {col : V → ℕ} {k : ℕ} (a b : Column col k) : Prop := G.Adj a.val b.val

def cross (G : SimpleGraph V) {col : V → ℕ} {k : ℕ} (a : Prefix col k) (b : Column col k) : Prop :=
  G.Adj a.val b.val

def lastCol {col : V → ℕ} {k : ℕ} (x : Column col k) : Prefix col (k+1) :=
  ⟨x.val, by have := x.property; omega⟩

/-- The old prefix components are all still incident to the new column. -/
def CanCross (G : SimpleGraph V) (col : V → ℕ) (k : ℕ) : Prop :=
  ∀ a : Prefix col k, ∃ d : Prefix col k, ∃ b : Column col k,
    EqvGen (prefGraph G col k).Adj a d ∧ cross G d b

def Nearest (G : SimpleGraph V) (col : V → ℕ) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → col y ≤ col x + 1

def grow {col : V → ℕ} (k : ℕ) : Prefix col k ⊕ Column col k ≃ Prefix col (k+1) where
  toFun
    | .inl a => ⟨a.val, by have := a.property; omega⟩
    | .inr b => lastCol b
  invFun x := if h : col x.val < k then .inl ⟨x.val,h⟩ else
    .inr ⟨x.val, by have := x.property; omega⟩
  left_inv := by
    rintro (a|b)
    · simp [a.property]
    · have h : ¬ col b.val < k := by rw [b.property]; omega
      simp [lastCol,h]
  right_inv := by
    intro x
    by_cases h : col x.val < k <;> simp [h, lastCol]

private theorem map_eqv {X Y : Type*} {A : X → X → Prop} {B : Y → Y → Prop}
    (f : X → Y) (h : ∀ x y, A x y → B (f x) (f y)) {x y : X} :
    EqvGen A x y → EqvGen B (f x) (f y) := by
  intro hw
  induction hw with
  | rel x y hp => exact .rel _ _ (h x y hp)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem eqv_equiv {X Y : Type*} {A : X → X → Prop} {B : Y → Y → Prop}
    (e : X ≃ Y) (he : ∀ x y, A x y ↔ B (e x) (e y)) (x y : X) :
    EqvGen A x y ↔ EqvGen B (e x) (e y) := by
  refine ⟨map_eqv e (fun a b h => (he a b).mp h), ?_⟩
  intro hp
  have back (a b : Y) (h : B a b) : A (e.symm a) (e.symm b) := by
    apply (he _ _).mpr
    simpa using h
  simpa using map_eqv e.symm back hp

private theorem grow_edge (G : SimpleGraph V) (col : V → ℕ) (k : ℕ)
    (x y : Prefix col k ⊕ Column col k) :
    GridCut.joined (prefGraph G col k).Adj (within G) (cross G) x y ↔
    (prefGraph G col (k+1)).Adj (grow k x) (grow k y) := by
  cases x <;> cases y
  · rfl
  · rfl
  · exact G.adj_comm _ _
  · rfl

theorem grow_boundary (G : SimpleGraph V) (col : V → ℕ) (k : ℕ) (hc : CanCross G col k)
    (b c : Column col k) :
    EqvGen (prefGraph G col (k+1)).Adj (lastCol b) (lastCol c) ↔
    EqvGen (GridCut.condensed (prefGraph G col k).Adj (within G) (cross G)) b c :=
  (eqv_equiv (grow k) (grow_edge G col k) (.inr b) (.inr c)).symm.trans
    (GridCut.boundary_connectivity _ _ _ hc b c)

/-- One cut replaces each old connecting path by an adjacency between the two
new vertices reached by its crossing edges. -/
def nextRelation (G : SimpleGraph V) {col : V → ℕ} {k : ℕ}
    (old : Column col k → Column col k → Prop) (b c : Column col (k+1)) : Prop :=
  within G b c ∨ ∃ a d : Column col k, G.Adj a.val b.val ∧ old a d ∧ G.Adj d.val c.val

/-- The computation retains only reachability among vertices of the current column. -/
def frontier (G : SimpleGraph V) (col : V → ℕ) : (k : ℕ) → Column col k → Column col k → Prop
  | 0 => EqvGen (within G)
  | k+1 => EqvGen (nextRelation G (frontier G col k))

private theorem condense_zero (G : SimpleGraph V) (col : V → ℕ) (b c : Column col 0) :
    GridCut.condensed (prefGraph G col 0).Adj (within G) (cross G) b c ↔ within G b c := by
  refine ⟨?_, Or.inl⟩
  rintro (h | ⟨a,_,_,_,_⟩)
  · exact h
  · exact (Nat.not_lt_zero _ a.property).elim

private theorem condense_succ (G : SimpleGraph V) (col : V → ℕ) (near : Nearest G col) (k : ℕ)
    (ih : ∀ a d : Column col k, EqvGen (prefGraph G col (k+1)).Adj (lastCol a) (lastCol d) ↔
      frontier G col k a d) (b c : Column col (k+1)) :
    GridCut.condensed (prefGraph G col (k+1)).Adj (within G) (cross G) b c ↔
      nextRelation G (frontier G col k) b c := by
  constructor
  · rintro (h | ⟨a,d,hab,had,hdc⟩)
    · exact Or.inl h
    · have onLast (x : Prefix col (k+1)) (y : Column col (k+1)) (hxy : cross G x y) :
          col x.val = k := by
        have hs := near hxy
        have := x.property
        have := y.property
        omega
      let a' : Column col k := ⟨a.val, onLast a b hab⟩
      let d' : Column col k := ⟨d.val, onLast d c hdc⟩
      exact Or.inr ⟨a',d',hab,(ih a' d').mp had,hdc⟩
  · rintro (h | ⟨a,d,hab,had,hdc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨lastCol a,lastCol d,hab,(ih a d).mpr had,hdc⟩

/-- At every column whose earlier components have met the intervening cuts,
the recursive frontier relation is exactly reachability inside the whole prefix. -/
theorem frontier_correct (G : SimpleGraph V) (col : V → ℕ) (near : Nearest G col) (k : ℕ)
    (hc : ∀ t, t ≤ k → CanCross G col t) (b c : Column col k) :
    EqvGen (prefGraph G col (k+1)).Adj (lastCol b) (lastCol c) ↔ frontier G col k b c := by
  induction k with
  | zero =>
    rw [grow_boundary G col 0 (hc 0 (le_refl _))]
    change EqvGen _ b c ↔ EqvGen _ b c
    apply eqv_equiv (Equiv.refl _) (condense_zero G col)
  | succ k ih =>
    rw [grow_boundary G col (k+1) (hc (k+1) (le_refl _))]
    change EqvGen _ b c ↔ EqvGen _ b c
    apply eqv_equiv (Equiv.refl _) (condense_succ G col near k (ih (fun t ht => hc t (by omega))))

theorem reachable_iff_eqv (G : SimpleGraph V) (v w : V) : G.Reachable v w ↔ EqvGen G.Adj v w := by
  constructor
  · intro h
    have hw := (G.reachable_iff_reflTransGen v w).mp h
    clear h
    induction hw with
    | refl => exact .refl _
    | tail _ he ih => exact .trans _ _ _ ih (.rel _ _ he)
  · intro h
    induction h with
    | rel x y h => exact h.reachable
    | refl => exact SimpleGraph.Reachable.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- In a connected nearest-neighbor graph extending to this cut, every old
component has an exit. A first edge leaving such a component must cross here. -/
theorem canCross_of_preconnected (G : SimpleGraph V) (col : V → ℕ)
    (near : Nearest G col) (conn : G.Preconnected) (k : ℕ) (right : ∃ z, k ≤ col z) :
    CanCross G col k := by
  intro a
  by_contra hno
  let past (x : V) : Prop := ∃ hx : col x < k, EqvGen (prefGraph G col k).Adj a ⟨x,hx⟩
  have step (x y : V) (hx : past x) (he : G.Adj x y) : past y := by
    obtain ⟨hx,hw⟩ := hx
    by_cases hy : col y < k
    · exact ⟨hy, .trans _ _ _ hw (.rel _ _ he)⟩
    · have bound := near he
      have hy' : col y = k := by omega
      exact (hno ⟨⟨x,hx⟩,⟨y,hy'⟩,hw,he⟩).elim
  have all (z : V) : past z := by
    have hw := (G.reachable_iff_reflTransGen a.val z).mp (conn _ _)
    induction hw with
    | refl => exact ⟨a.property, .refl _⟩
    | tail _ hxy ih => exact step _ _ ih hxy
  obtain ⟨z,hz⟩ := right
  obtain ⟨hl,_⟩ := all z
  omega

theorem frontier_reachable (G : SimpleGraph V) (col : V → ℕ) (near : Nearest G col) (k : ℕ)
    (hcut : ∀ t, t ≤ k → CanCross G col t) (b c : Column col k) :
    frontier G col k b c ↔ (prefGraph G col (k+1)).Reachable (lastCol b) (lastCol c) :=
  (frontier_correct G col near k hcut b c).symm.trans (reachable_iff_eqv _ _ _).symm

theorem frontier_connected_graph (G : SimpleGraph V) (col : V → ℕ) (near : Nearest G col)
    (conn : G.Preconnected) (k : ℕ) (right : ∃ z, k ≤ col z) (b c : Column col k) :
    frontier G col k b c ↔ (prefGraph G col (k+1)).Reachable (lastCol b) (lastCol c) :=
  frontier_reachable G col near k (fun t ht => canCross_of_preconnected G col near conn t
    (right.imp (fun _ hz => ht.trans hz))) b c

theorem reaches_last (G : SimpleGraph V) (col : V → ℕ) (k : ℕ) (hc : CanCross G col k)
    (z : Prefix col (k+1)) : ∃ b : Column col k, EqvGen (prefGraph G col (k+1)).Adj z (lastCol b) := by
  obtain ⟨b,hb⟩ := GridCut.reaches_new _ _ _ hc ((grow k).symm z)
  refine ⟨b,?_⟩
  have h := (eqv_equiv (grow k) (grow_edge G col k) ((grow k).symm z) (.inr b)).mp hb
  change EqvGen _ (grow k ((grow k).symm z)) (lastCol b) at h
  simpa only [Equiv.apply_symm_apply] using h

/-- Every frontier component has a horizontal exit to the following column. -/
def live (G : SimpleGraph V) (col : V → ℕ) (k : ℕ) : Prop :=
  ∀ b : Column col k, ∃ d : Column col k, ∃ z : Column col (k+1),
    frontier G col k b d ∧ G.Adj d.val z.val

theorem canCross_succ_iff (G : SimpleGraph V) (col : V → ℕ) (near : Nearest G col)
    (k : ℕ) (hc : ∀ t, t ≤ k → CanCross G col t) : CanCross G col (k+1) ↔ live G col k := by
  constructor
  · intro hn b
    obtain ⟨d,z,hd,he⟩ := hn (lastCol b)
    have bound := near he
    have := z.property
    have := d.property
    have hdcol : col d.val = k := by omega
    let d' : Column col k := ⟨d.val, hdcol⟩
    exact ⟨d',z,(frontier_correct G col near k hc b d').mp hd,he⟩
  · intro hl a
    obtain ⟨b,hb⟩ := reaches_last G col k (hc k (le_refl _)) a
    obtain ⟨d,z,hd,he⟩ := hl b
    exact ⟨lastCol d,z,.trans _ _ _ hb ((frontier_correct G col near k hc b d).mpr hd),he⟩

theorem cuts_iff_live (G : SimpleGraph V) (col : V → ℕ) (near : Nearest G col) (k : ℕ) :
    (∀ t, t ≤ k → CanCross G col t) ↔ ∀ t, t < k → live G col t := by
  constructor
  · intro hc t ht
    apply (canCross_succ_iff G col near t (fun i hi => hc i (by omega))).mp
    exact hc (t+1) (by omega)
  · induction k with
    | zero =>
      intro _ t ht
      obtain rfl : t = 0 := by omega
      intro a
      exact (Nat.not_lt_zero _ a.property).elim
    | succ k ih =>
      intro all t ht
      have hc := ih (fun i hi => all i (by omega))
      by_cases hold : t ≤ k
      · exact hc t hold
      · obtain rfl : t = k+1 := by omega
        exact (canCross_succ_iff G col near k hc).mpr (all k (by omega))

private def fullEquiv (col : V → ℕ) (k : ℕ) (h : ∀ v, col v ≤ k) : Prefix col (k+1) ≃ V where
  toFun x := x.val
  invFun x := ⟨x,Nat.lt_succ_of_le (h x)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- For a graph ending in a nonempty column k, global connectedness is
equivalent to all earlier frontier components having exits and all final
column vertices lying in the same computed frontier component. -/
theorem preconnected_iff (G : SimpleGraph V) (col : V → ℕ) (near : Nearest G col)
    (k : ℕ) (bound : ∀ x, col x ≤ k) (last : Nonempty (Column col k)) :
    G.Preconnected ↔ (∀ t, t < k → live G col t) ∧ ∀ b c, frontier G col k b c := by
  have transport (x y : Prefix col (k+1)) :
      EqvGen (prefGraph G col (k+1)).Adj x y ↔ EqvGen G.Adj x.val y.val :=
    eqv_equiv (fullEquiv col k bound) (fun _ _ => Iff.rfl) x y
  constructor
  · intro h
    obtain ⟨z⟩ := last
    have hc (t : ℕ) (ht : t ≤ k) : CanCross G col t := by
      apply canCross_of_preconnected G col near h t
      exact ⟨z.val, by rw [z.property]; exact ht⟩
    refine ⟨(cuts_iff_live G col near k).mp hc, fun b c => ?_⟩
    exact (frontier_correct G col near k hc b c).mp ((transport _ _).mpr
      ((reachable_iff_eqv G _ _).mp (h _ _)))
  · rintro ⟨hl,hconn⟩ x y
    have hc := (cuts_iff_live G col near k).mpr hl
    let x' := (fullEquiv col k bound).symm x
    let y' := (fullEquiv col k bound).symm y
    obtain ⟨b,hb⟩ := reaches_last G col k (hc k (le_refl _)) x'
    obtain ⟨c,hc'⟩ := reaches_last G col k (hc k (le_refl _)) y'
    have across := (frontier_correct G col near k hc b c).mpr (hconn b c)
    exact (reachable_iff_eqv G _ _).mpr ((transport x' y').mp
      (.trans _ _ _ hb (.trans _ _ _ across (.symm _ _ hc'))))

end GridPrefix

namespace OMA358

open OMA.S_oeis_a358696
open GridPrefix

abbrev ActiveVertex {n : ℕ} (sel : Finset (EdgePos n)) := (selectedGraph sel).support

noncomputable def activeGraph {n : ℕ} (sel : Finset (EdgePos n)) : SimpleGraph (ActiveVertex sel) :=
  (selectedGraph sel).induce (selectedGraph sel).support

def activeColumn {n : ℕ} (sel : Finset (EdgePos n)) (x : ActiveVertex sel) : ℕ :=
  x.val.2.val

theorem activeGraph_nearest {n : ℕ} (sel : Finset (EdgePos n)) :
    Nearest (activeGraph sel) (activeColumn sel) := by
  intro x y hxy
  have he : s(x.val, y.val) ∈ (selectedGraph sel).edgeSet := hxy
  rw [selectedGraph_edgeSet] at he
  have adj := (edgeMaskEquiv n sel).property he
  change (grid n).Adj x.val y.val at adj
  change y.val.2.val ≤ x.val.2.val + 1
  rcases adj with ⟨_, h⟩ | ⟨h,_⟩
  · change x.val.2 = y.val.2 at h
    rw [h]
    omega
  · change (SimpleGraph.pathGraph n).Adj x.val.2 y.val.2 at h
    rcases SimpleGraph.pathGraph_adj.mp h with h | h <;> omega

/-- For every positive width, the authentic admissibility condition on arrays
satisfying the local tests reduces to successive frontier-component tests. -/
theorem admissible_iff_frontier {k : ℕ} (vert : Finset (Fin 4 × Fin (k+1)))
    (hor : Finset (Fin 5 × Fin ((k+1)-1))) (localOK : localTests vert hor) :
    let sel := vert.disjSum hor
    let G := activeGraph sel
    let col := activeColumn sel
    admissible (vert,hor) ↔ (∀ t, t < k → live G col t) ∧ ∀ b c, GridPrefix.frontier G col k b c := by
  let sel : Finset (EdgePos (k+1)) := vert.disjSum hor
  let G := activeGraph sel
  let col := activeColumn sel
  change (G.Connected ∧ localTests vert hor) ↔ (∀ t, t < k → live G col t) ∧ ∀ b c, GridPrefix.frontier G col k b c
  let corner : Vertex (k+1) := (0, Fin.last k)
  have hboundary : boundary corner := Or.inl rfl
  have deg := (localOK corner).resolve_right (fun hi => hi.1 hboundary)
  have active : corner ∈ (selectedGraph sel).support :=
    (mem_support_iff_localDegree_pos vert hor corner).mpr (by omega)
  let z : ActiveVertex sel := ⟨corner,active⟩
  have last : Nonempty (Column col k) := ⟨⟨z,rfl⟩⟩
  have all (x : ActiveVertex sel) : col x ≤ k := Nat.le_of_lt_succ x.val.2.isLt
  have inhabited : Nonempty (ActiveVertex sel) := ⟨z⟩
  simpa only [and_iff_left localOK, SimpleGraph.connected_iff, and_iff_left inhabited] using
    (preconnected_iff G col (activeGraph_nearest sel) k all last)

end OMA358

namespace OMA358

/-- Horizontal edges on a cut, encoded from the union of its paired row masks. -/
def pairedRowMask (s : List ℕ) : Fin 32 :=
  let bits := List.ofFn (fun r : Fin 5 => s.any (fun p => p.testBit r.val))
  let m := BitVec.ofBoolListLE bits
  ⟨m.toNat, by simpa [m, bits] using m.toFin.isLt⟩

theorem pairedRowMask_testBit (s : List ℕ) (r : Fin 5) :
    (pairedRowMask s).val.testBit r.val = s.any (fun p => p.testBit r.val) := by
  simp only [pairedRowMask, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp)]
  exact List.getElem_ofFn ..

@[simp] theorem pairedRowMask_nil : pairedRowMask [] = 0 := by decide

/-- Four incident edge indicators at one vertex. -/
def maskDegree (left : Fin 32) (vertical : ColumnMask) (right : Fin 32) (r : Fin 5) : ℕ :=
  (left.val.testBit r.val).toNat + ((vertical.val <<< 1).testBit r.val).toNat +
    (vertical.val.testBit r.val).toNat + (right.val.testBit r.val).toNat

/-- Successful transition with the geometric check for its incoming pairing. -/
structure CheckedColumn (kind : ColumnKind) (old : List ℕ) (v : ColumnMask)
    (out : List ℕ) : Prop where
  step : columnStep kind old v = some out
  check : graphCheck kind old v

theorem CheckedColumn.geometric {kind old v out} (h : CheckedColumn kind old v out) :
    geometricChoice kind old v :=
  h.check.1.mp (by simp [h.step])

theorem CheckedColumn.exit_iff {kind old v out} (h : CheckedColumn kind old v out) (r : Fin 5) :
    (pairedRowMask out).val.testBit r.val = true ↔ r ∈ exitRows old v := by
  have hstate := h.check.2
  rw [h.step] at hstate
  by_cases hk : kind = .last
  · simp only [hk, ↓reduceIte] at hstate
    have hd := (h.geometric.1 r).2.2 hk
    simp [hstate, exitRows, hd]
  · simp only [hk, ↓reduceIte] at hstate
    have hp := hstate r r
    simpa [pairedRowMask_testBit, SimpleGraph.Reachable.refl] using hp

theorem CheckedColumn.degree {kind old v out} (h : CheckedColumn kind old v out) (r : Fin 5) :
    maskDegree (pairedRowMask old) v (pairedRowMask out) r = 2 ∨
      (kind = .middle ∧ r.val ≠ 0 ∧ r.val ≠ 4 ∧
        maskDegree (pairedRowMask old) v (pairedRowMask out) r = 0) := by
  have hd := h.geometric.1 r
  have hout := h.exit_iff r
  simp only [exitRows, Finset.mem_filter, Finset.mem_univ, true_and] at hout
  have hsum : maskDegree (pairedRowMask old) v (pairedRowMask out) r =
      beforeExit old v r + ((pairedRowMask out).val.testBit r.val).toNat := by
    simp [maskDegree, beforeExit, pairedRowMask_testBit]
  rw [hsum]
  by_cases he : beforeExit old v r = 1
  · rw [hout.mpr he, he]
    exact Or.inl rfl
  · have hf : (pairedRowMask out).val.testBit r.val = false := by
      cases hv : (pairedRowMask out).val.testBit r.val <;> simp_all
    rw [hf]
    simp only [Bool.toNat_false, Nat.add_zero]
    by_cases hz : beforeExit old v r = 0
    · right
      have hnot : ¬ (kind ≠ .middle ∨ r.val = 0 ∨ r.val = 4) := fun hh => by
        have := hd.2.1 hh
        omega
      exact ⟨by tauto, by tauto, by tauto, hz⟩
    · left
      have := hd.1
      omega

private theorem indexed_of_expanded {w : State → ℤ} {s : List ℕ}
    (h : s ∈ (List.finRange 20).flatMap (fun j => List.replicate (w j).toNat (frontier j))) :
    ∃ j : State, s = frontier j := by
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp h
  exact ⟨j, (List.eq_of_mem_replicate hj)⟩

private theorem first_indexed {v : ColumnMask} {out : List ℕ}
    (h : columnStep .first [] v = some out) : ∃ j : State, out = frontier j :=
  indexed_of_expanded (first_outcomes.mem_iff.mp (List.mem_filterMap.mpr ⟨v, by simp, h⟩))

private theorem middle_indexed (i : State) {v : ColumnMask} {out : List ℕ}
    (h : columnStep .middle (frontier i) v = some out) : ∃ j : State, out = frontier j :=
  indexed_of_expanded ((middle_outcomes i).mem_iff.mp (List.mem_filterMap.mpr ⟨v, by simp, h⟩))

/-- A suffix has one closing column and any number of interior columns to its left. -/
def suffixKind {n : ℕ} (i : Fin n) : ColumnKind :=
  if i.val + 1 = n then .last else .middle

/-- The opening column is followed by a suffix. -/
def stripKind {n : ℕ} (i : Fin n) : ColumnKind :=
  if i.val = 0 then .first else suffixKind i

theorem HistoryFrom.indexedCuts {k : ℕ} {s : List ℕ} {w : MaskWord}
    (h : HistoryFrom k s w) (hs : ∃ j : State, s = frontier j) :
    ∃ (masks : Fin (k+1) → ColumnMask) (cuts : Fin (k+2) → List ℕ),
      List.ofFn masks = w ∧ cuts 0 = s ∧ cuts (Fin.last (k+1)) = [] ∧
      ∀ i : Fin (k+1), CheckedColumn (suffixKind i) (cuts i.castSucc) (masks i) (cuts i.succ) := by
  induction h with
  | @last s v hv =>
    obtain ⟨j, rfl⟩ := hs
    refine ⟨fun _ => v, Fin.cons (frontier j) (fun _ => []), ?_, rfl, rfl, ?_⟩
    · simp [List.ofFn_succ]
    · intro i
      fin_cases i
      exact ⟨hv, column_checks.2.2 j v⟩
  | @middle k s v out tail hv _ ih =>
    obtain ⟨j, rfl⟩ := hs
    obtain ⟨m, c, hm, hc, hend, hy⟩ := ih (middle_indexed j hv)
    refine ⟨Fin.cons v m, Fin.cons (frontier j) c, ?_, rfl, hend, ?_⟩
    · rw [List.ofFn_succ]
      exact congrArg (v :: ·) hm
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · change CheckedColumn (suffixKind (0 : Fin (k+2))) (frontier j) v (c 0)
        rw [hc]
        have hk : suffixKind (0 : Fin (k+2)) = .middle := by simp [suffixKind]
        rw [hk]
        exact ⟨hv, column_checks.2.1 j v⟩
      · change CheckedColumn (suffixKind i.succ) (c i.castSucc) (m i) (c i.succ)
        have hk : suffixKind i.succ = suffixKind i := by
          unfold suffixKind
          simp only [Fin.val_succ, Nat.add_left_inj]
        rw [hk]
        exact hy i

theorem IsColumnHistory.indexedCuts {k : ℕ} {w : MaskWord} (h : IsColumnHistory k w) :
    ∃ (masks : Fin (k+2) → ColumnMask) (cuts : Fin (k+3) → List ℕ),
      List.ofFn masks = w ∧ cuts 0 = [] ∧ cuts (Fin.last (k+2)) = [] ∧
      ∀ i : Fin (k+2), CheckedColumn (stripKind i) (cuts i.castSucc) (masks i) (cuts i.succ) := by
  cases w with
  | nil => exact False.elim h
  | cons v tail =>
    obtain ⟨s, hv, ht⟩ := h
    obtain ⟨m, c, hm, hc, hend, hy⟩ := ht.indexedCuts (first_indexed hv)
    refine ⟨Fin.cons v m, Fin.cons [] c, ?_, rfl, hend, ?_⟩
    · rw [List.ofFn_succ]
      exact congrArg (v :: ·) hm
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · change CheckedColumn .first [] v (c 0)
        rw [hc]
        exact ⟨hv, column_checks.1 v⟩
      · change CheckedColumn (stripKind i.succ) (c i.castSucc) (m i) (c i.succ)
        have hk : stripKind i.succ = suffixKind i := by
          unfold stripKind suffixKind
          simp only [Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_left_inj]
        rw [hk]
        exact hy i

/-- An accepted word admits one horizontal mask on each cut, including zero
masks at both exterior cuts. Consecutive columns share the same internal
cut and all four edge incidences satisfy the required grid degrees. -/
theorem IsColumnHistory.horizontalMasks {k : ℕ} {w : MaskWord} (h : IsColumnHistory k w) :
    ∃ (masks : Fin (k+2) → ColumnMask) (cuts : Fin (k+3) → List ℕ)
      (hor : Fin (k+3) → Fin 32),
      List.ofFn masks = w ∧ hor 0 = 0 ∧ hor (Fin.last (k+2)) = 0 ∧
      (∀ j, hor j = pairedRowMask (cuts j)) ∧
      ∀ (i : Fin (k+2)) (r : Fin 5),
        ((hor i.succ).val.testBit r.val = true ↔ r ∈ exitRows (cuts i.castSucc) (masks i)) ∧
        (maskDegree (hor i.castSucc) (masks i) (hor i.succ) r = 2 ∨
          (i.val ≠ 0 ∧ i.val + 1 ≠ k+2 ∧ r.val ≠ 0 ∧ r.val ≠ 4 ∧
            maskDegree (hor i.castSucc) (masks i) (hor i.succ) r = 0)) := by
  obtain ⟨m, c, hm, hc, he, hy⟩ := h.indexedCuts
  refine ⟨m, c, fun j => pairedRowMask (c j), hm, by simp [hc], by simp [he],
    fun _ => rfl, fun i r => ⟨(hy i).exit_iff r, ?_⟩⟩
  obtain h2 | ⟨hi, h0, h4, hd⟩ := (hy i).degree r
  · exact Or.inl h2
  · refine Or.inr ⟨?_, ?_, h0, h4, hd⟩
    · intro hzero
      simp [stripKind, hzero] at hi
    · intro hlast
      by_cases hzero : i.val = 0 <;> simp [stripKind, suffixKind, hzero, hlast] at hi


end OMA358

namespace OMA358

open OMA.S_oeis_a358696

/-- Decode all actual horizontal edges from the internal cuts. Cut 0 and
cut n are the two exterior masks. -/
def edgesOfCuts {n : ℕ} (h : Fin (n+1) → Fin 32) : Finset (Fin 5 × Fin (n-1)) :=
  (horizontalMaskEquiv n).symm (fun p => h ⟨p.val + 1, by have := p.isLt; omega⟩)

theorem incomingMask_edgesOfCuts {n : ℕ} (h : Fin (n+1) → Fin 32)
    (h0 : h 0 = 0) (j : Fin n) : incomingMask (edgesOfCuts h) j = (h j.castSucc).val := by
  unfold incomingMask
  split
  next hp =>
    simp only [edgesOfCuts, Equiv.apply_symm_apply]
    congr 2
    apply Fin.ext
    simp
    omega
  next hp =>
    have hj : j.castSucc = 0 := Fin.ext (by simpa using Nat.eq_zero_of_not_pos hp)
    rw [hj, h0]
    rfl

theorem outgoingMask_edgesOfCuts {n : ℕ} (h : Fin (n+1) → Fin 32)
    (hN : h (Fin.last n) = 0) (j : Fin n) :
    outgoingMask (edgesOfCuts h) j = (h j.succ).val := by
  unfold outgoingMask
  split
  next hp => simp only [edgesOfCuts, Equiv.apply_symm_apply]; rfl
  next hp =>
    have hj : j.succ = Fin.last n := Fin.ext (by
      change j.val + 1 = n
      have := j.isLt
      omega)
    rw [hj, hN]
    rfl

/-- The decoded edge-coordinate arrays of an accepted word pass the actual
grid local tests, and their incoming edges are exactly the rows in the
successful indexed frontier at every column. -/
theorem IsColumnHistory.exists_localTests {k : ℕ} {w : MaskWord}
    (hw : IsColumnHistory k w) :
    ∃ (vert : Finset (Fin 4 × Fin (k+2))) (hor : Finset (Fin 5 × Fin ((k+2)-1)))
      (cuts : Fin (k+3) → List ℕ),
      List.ofFn (verticalMaskEquiv (k+2) vert) = w ∧
      cuts 0 = [] ∧ cuts (Fin.last (k+2)) = [] ∧
      (∀ j : Fin (k+2), CheckedColumn (stripKind j) (cuts j.castSucc)
        (verticalMaskEquiv (k+2) vert j) (cuts j.succ)) ∧
      (∀ j : Fin (k+2), recordsIncoming hor j (cuts j.castSucc)) ∧
      (∀ (j : Fin (k+2)) (r : Fin 5), (outgoingMask hor j).testBit r.val = true ↔
        r ∈ exitRows (cuts j.castSucc) (verticalMaskEquiv (k+2) vert j)) ∧
      localTests vert hor := by
  obtain ⟨m, c, hm, h0, hN, hc⟩ := hw.indexedCuts
  let vert := (verticalMaskEquiv (k+2)).symm m
  let hor := edgesOfCuts (fun j => pairedRowMask (c j))
  have hvm : verticalMaskEquiv (k+2) vert = m := Equiv.apply_symm_apply _ _
  have hlin (j : Fin (k+2)) : incomingMask hor j = (pairedRowMask (c j.castSucc)).val :=
    incomingMask_edgesOfCuts _ (by simp [h0]) _
  have hrout (j : Fin (k+2)) : outgoingMask hor j = (pairedRowMask (c j.succ)).val :=
    outgoingMask_edgesOfCuts _ (by simp [hN]) _
  refine ⟨vert, hor, c, hvm ▸ hm, h0, hN, hvm ▸ hc, ?_, ?_, ?_⟩
  · intro j r
    rw [hlin, pairedRowMask_testBit]
  · intro j r
    rw [hrout, hvm]
    exact (hc j).exit_iff r
  · rintro ⟨r, j⟩
    rw [localDegree_bits, hlin, hrout, hvm]
    change maskDegree _ _ _ _ = 2 ∨ (¬ boundary _ ∧ maskDegree _ _ _ _ = 0)
    obtain h2 | ⟨hi, hr0, hr4, hd⟩ := (hc j).degree r
    · exact Or.inl h2
    · refine Or.inr ⟨?_, hd⟩
      have hj0 : j.val ≠ 0 := by
        intro hz
        simp [stripKind, hz] at hi
      have hjN : j.val+1 ≠ k+2 := by
        intro hz
        simp [stripKind, suffixKind, hj0, hz] at hi
      change ¬ (r.val = 0 ∨ r.val + 1 = 5 ∨ j.val = 0 ∨ j.val + 1 = k+2)
      omega


end OMA358

namespace OMA358

open OMA.S_oeis_a358696

/-- A vertical edge of one column, in either orientation. Its bit is at the
row of its upper endpoint. -/
def rowStep (down : Fin 16) (r t : Fin 5) : Prop :=
  (r.val+1 = t.val ∧ down.val.testBit r.val = true) ∨
  (t.val+1 = r.val ∧ down.val.testBit t.val = true)

private theorem selected_le_grid {n} (sel : Finset (EdgePos n)) : selectedGraph sel ≤ grid n := by
  intro a b ha
  have he : s(a,b) ∈ (selectedGraph sel).edgeSet := ha
  rw [selectedGraph_edgeSet] at he
  exact (edgeMaskEquiv n sel).property he

private theorem vertical_position {n} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (d : Fin 4) (j : Fin n) :
    (selectedGraph (vert.disjSum hor)).Adj (posLeft (m := 5) d,j) (posRight (m := 5) d,j)
      ↔ (d,j) ∈ vert := by
  change asEdge (.inl (d,j)) ∈ (selectedGraph (vert.disjSum hor)).edgeSet ↔ _
  rw [selectedGraph_edgeSet]
  change asEdge (.inl (d,j)) ∈ (edgeMaskEquiv n (vert.disjSum hor)).val ↔ _
  rw [mem_edgeMaskEquiv]
  simp

private theorem horizontal_position {n} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (r : Fin 5) (d : Fin (n-1)) :
    (selectedGraph (vert.disjSum hor)).Adj (r,posLeft d) (r,posRight d)
      ↔ (r,d) ∈ hor := by
  change asEdge (.inr (r,d)) ∈ (selectedGraph (vert.disjSum hor)).edgeSet ↔ _
  rw [selectedGraph_edgeSet]
  change asEdge (.inr (r,d)) ∈ (edgeMaskEquiv n (vert.disjSum hor)).val ↔ _
  rw [mem_edgeMaskEquiv]
  simp

private theorem vertical_step {n} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) {r t : Fin 5} (j : Fin n) (hrt : r.val+1=t.val) :
    (selectedGraph (vert.disjSum hor)).Adj (r,j) (t,j) ↔
    (verticalMaskEquiv n vert j).val.testBit r.val = true := by
  let d : Fin 4 := ⟨r.val, by have := t.isLt; omega⟩
  have h₁ : posLeft (m := 5) d = r := rfl
  have h₂ : posRight (m := 5) d = t := Fin.ext hrt
  simpa only [h₁,h₂] using (vertical_position vert hor d j).trans (vertical_testBit_iff vert d j).symm

private theorem horizontal_step {n} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (r : Fin 5) {j k : Fin n} (hjk : j.val+1=k.val) :
    (selectedGraph (vert.disjSum hor)).Adj (r,j) (r,k) ↔
    (outgoingMask hor j).testBit r.val = true := by
  have hj : j.val+1<n := hjk ▸ k.isLt
  let d : Fin (n-1) := ⟨j.val, by omega⟩
  have h₁ : posLeft d = j := rfl
  have h₂ : posRight d = k := Fin.ext hjk
  simpa only [h₁,h₂,outgoingMask,dif_pos hj] using
    (horizontal_position vert hor r d).trans (horizontal_testBit_iff hor r d).symm

theorem selected_same_column_iff {n} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) (r t : Fin 5) :
    (selectedGraph (vert.disjSum hor)).Adj (r,j) (t,j) ↔ rowStep (verticalMaskEquiv n vert j) r t := by
  constructor
  · intro h
    rcases selected_le_grid _ h with ⟨ha,_⟩ | ⟨ha,_⟩
    · rcases SimpleGraph.pathGraph_adj.mp ha with hj | hj
      · exact Or.inl ⟨hj,(vertical_step vert hor j hj).mp h⟩
      · exact Or.inr ⟨hj,(vertical_step vert hor j hj).mp h.symm⟩
    · exact (ha.ne rfl).elim
  · rintro (⟨hrt,hbit⟩ | ⟨htr,hbit⟩)
    · exact (vertical_step vert hor j hrt).mpr hbit
    · exact ((vertical_step vert hor j htr).mpr hbit).symm

theorem selected_next_column_iff {n} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) {j k : Fin n} (hjk : j.val+1=k.val) (r t : Fin 5) :
    (selectedGraph (vert.disjSum hor)).Adj (r,j) (t,k) ↔
      r = t ∧ (outgoingMask hor j).testBit r.val = true := by
  constructor
  · intro h
    have hrt : r = t := by
      rcases selected_le_grid _ h with ⟨_,hjk'⟩ | ⟨_,hrt⟩
      · change j = k at hjk'
        subst k
        omega
      · exact hrt
    subst t
    exact ⟨rfl,(horizontal_step vert hor r hjk).mp h⟩
  · rintro ⟨rfl,hbit⟩
    exact (horizontal_step vert hor r hjk).mpr hbit

/-- Selected edges do not skip columns, in either orientation. -/
theorem adjacent_column_distance {n} {sel : Finset (EdgePos n)} {a b : Vertex n}
    (h : (selectedGraph sel).Adj a b) :
    a.2.val ≤ b.2.val+1 ∧ b.2.val ≤ a.2.val+1 := by
  rcases selected_le_grid _ h with ⟨_,hj⟩ | ⟨hj,_⟩
  · change a.2 = b.2 at hj
    rw [hj]
    omega
  · rcases SimpleGraph.pathGraph_adj.mp hj with h | h <;> omega

/-- Every grid vertex has at most one selected neighbor strictly to its right. -/
theorem right_neighbor_unique {n} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) {a b c : Vertex n}
    (hab : (selectedGraph (vert.disjSum hor)).Adj a b)
    (hac : (selectedGraph (vert.disjSum hor)).Adj a c)
    (hb : a.2.val < b.2.val) (hc : a.2.val < c.2.val) : b=c := by
  have h₁ := (adjacent_column_distance hab).2
  have h₂ := (adjacent_column_distance hac).2
  have hkb : a.2.val+1 = b.2.val := by omega
  have hkc : a.2.val+1 = c.2.val := by omega
  apply Prod.ext
  · exact ((selected_next_column_iff vert hor hkb _ _).mp hab).1.symm.trans
      ((selected_next_column_iff vert hor hkc _ _).mp hac).1
  · exact Fin.ext (hkb.symm.trans hkc)

abbrev SupportedColumn {n} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) :=
  GridPrefix.Column (activeColumn (vert.disjSum hor)) j.val

private theorem layer_col_eq {n} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} {j : Fin n} (x : SupportedColumn vert hor j) :
    x.val.val.2 = j := Fin.ext x.property

/-- A support vertex in the fixed column is uniquely identified by an active row. -/
def activeLayerEquiv {n} {vert : Finset (Fin 4 × Fin n)} {hor : Finset (Fin 5 × Fin (n-1))}
    (ht : localTests vert hor) (j : Fin n) {old : List ℕ} (hrec : recordsIncoming hor j old) :
    SupportedColumn vert hor j ≃ {r : Fin 5 // r ∈ active old (verticalMaskEquiv n vert j)} where
  toFun x := ⟨x.val.val.1, (mem_active_iff_graph_support ht j hrec x.val.val.1).mpr (by
    have he : x.val.val = (x.val.val.1,j) := Prod.ext rfl (layer_col_eq x)
    exact he ▸ x.val.property)⟩
  invFun r := ⟨⟨(r.val,j),(mem_active_iff_graph_support ht j hrec r.val).mp r.property⟩,rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (layer_col_eq x).symm
  right_inv r := rfl

theorem within_iff_rowStep {n} (vert : Finset (Fin 4 × Fin n)) (hor : Finset (Fin 5 × Fin (n-1)))
    (j : Fin n) (x y : SupportedColumn vert hor j) :
    GridPrefix.within (activeGraph (vert.disjSum hor)) x y ↔
    rowStep (verticalMaskEquiv n vert j) x.val.val.1 y.val.val.1 := by
  change (selectedGraph (vert.disjSum hor)).Adj x.val.val y.val.val ↔ _
  have hx : x.val.val = (x.val.val.1,j) := Prod.ext rfl (layer_col_eq x)
  have hy : y.val.val = (y.val.val.1,j) := Prod.ext rfl (layer_col_eq y)
  conv_lhs => rw [hx,hy]
  exact selected_same_column_iff vert hor j _ _

theorem cross_iff_right {n} (vert : Finset (Fin 4 × Fin n)) (hor : Finset (Fin 5 × Fin (n-1)))
    (j : Fin n) (x : GridPrefix.Prefix (activeColumn (vert.disjSum hor)) j.val)
    (y : SupportedColumn vert hor j) :
    GridPrefix.cross (activeGraph (vert.disjSum hor)) x y ↔
      x.val.val.2.val+1 = j.val ∧ x.val.val.1 = y.val.val.1 ∧
        (outgoingMask hor x.val.val.2).testBit x.val.val.1.val = true := by
  change (selectedGraph (vert.disjSum hor)).Adj x.val.val y.val.val ↔ _
  have hy := layer_col_eq y
  have hx : x.val.val.2.val < j.val := x.property
  constructor
  · intro he
    have hstep := (adjacent_column_distance he).2
    rw [hy] at hstep
    have hxy : x.val.val.2.val+1 = y.val.val.2.val := by rw [hy]; omega
    exact ⟨by omega,(selected_next_column_iff vert hor hxy _ _).mp he⟩
  · rintro ⟨hm,hrow,hbit⟩
    have hxy : x.val.val.2.val+1 = y.val.val.2.val := by rwa [hy]
    exact (selected_next_column_iff vert hor hxy _ _).mpr ⟨hrow,hbit⟩

end OMA358

namespace OMA358

open Relation OMA.S_oeis_a358696

/-- Two rows occur together in a recorded path mask. -/
def samePair (s : List ℕ) (r t : Fin 5) : Prop :=
  (s.any (fun p => p.testBit r.val && p.testBit t.val)) = true

/-- The abstract frontier relation equals the algorithm's row reachability. -/
def TracksFrontier {n : ℕ} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) (old : List ℕ) : Prop :=
  ∀ x y : SupportedColumn vert hor j,
    GridPrefix.frontier (activeGraph (vert.disjSum hor)) (activeColumn (vert.disjSum hor)) j.val x y ↔
      (columnGraph old (verticalMaskEquiv n vert j)).Reachable x.val.val.1 y.val.val.1

/-- A recorded outgoing pair consists exactly of two actual outgoing rows
whose vertices are in the same component at the current frontier. -/
def RecordsCut {n : ℕ} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) (out : List ℕ) : Prop :=
  ∀ r t : Fin 5, samePair out r t ↔ ∃ x y : SupportedColumn vert hor j,
    x.val.val.1 = r ∧ y.val.val.1 = t ∧ (outgoingMask hor j).testBit r.val = true ∧
      (outgoingMask hor j).testBit t.val = true ∧
      GridPrefix.frontier (activeGraph (vert.disjSum hor)) (activeColumn (vert.disjSum hor)) j.val x y

private theorem samePair_comm (s : List ℕ) (r t : Fin 5) : samePair s r t ↔ samePair s t r := by
  simp [samePair,Bool.and_comm]

private theorem row_adj (s : List ℕ) (v : Fin 16) (r t : Fin 5) :
    (columnGraph s v).Adj r t ↔ r ≠ t ∧ (rowStep v r t ∨ samePair s r t) := by
  change r ≠ t ∧ ((_ ∨ samePair s r t) ∨ (_ ∨ samePair s t r)) ↔ r ≠ t ∧ ((_ ∨ _) ∨ samePair s r t)
  rw [samePair_comm s t r]
  tauto

private theorem incident_row_active (s : List ℕ) (v : Fin 16) (r t : Fin 5)
    (h : (columnGraph s v).Adj r t) : r ∈ active s v := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases (row_adj s v r t).mp h with ⟨_, ((⟨_, hb⟩ | ⟨ht, hb⟩) | hp)⟩
  · simp [beforeExit, hb]
  · have hu : (v.val <<< 1).testBit r.val = true := by
      rw [← ht, Nat.testBit_shiftLeft]
      simpa using hb
    simp [beforeExit, hu]
  · obtain ⟨p,hp,hpair⟩ := List.any_eq_true.mp hp
    have hr := (Bool.and_eq_true_iff.mp hpair).1
    have ho : s.any (fun p => p.testBit r.val) = true := List.any_eq_true.mpr ⟨p,hp,hr⟩
    simp [beforeExit, ho]

/-- Restrict an undirected graph to the row injection when every endpoint of
an edge is in its image. Reflexive steps are allowed in the generating relation. -/
private theorem row_reach {X : Type*} (g : SimpleGraph (Fin 5)) (row : X → Fin 5)
    (inj : Function.Injective row) (ends : ∀ r t, g.Adj r t → ∃ x, row x = r)
    (A : X → X → Prop) (rel : ∀ x y, row x ≠ row y → (A x y ↔ g.Adj (row x) (row y)))
    (x y : X) : EqvGen A x y ↔ g.Reachable (row x) (row y) := by
  constructor
  · intro h
    induction h with
    | rel x y h =>
      by_cases he : row x = row y
      · exact he ▸ SimpleGraph.Reachable.refl _
      · exact ((rel x y he).mp h).reachable
    | refl => exact .refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · rintro ⟨w⟩
    suffices lift : ∀ {a b : Fin 5} (w : g.Walk a b) (u v : X),
        row u = a → row v = b → EqvGen A u v from lift w x y rfl rfl
    intro a b w
    induction w with
    | nil =>
      intro u v hu hv
      exact (inj (hu.trans hv.symm)) ▸ EqvGen.refl _
    | @cons a b c hab _ ih =>
      intro u v hu hv
      obtain ⟨w,hw⟩ := ends _ _ hab.symm
      have hne : row u ≠ row w := by simpa [hu,hw] using hab.ne
      have hrel := (rel u w hne).mpr (by simpa [hu,hw] using hab)
      exact .trans _ _ _ (.rel _ _ hrel) (ih w v hw hv)

private theorem frontier_transfer {n : ℕ} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor) (j : Fin n)
    {old : List ℕ} (hrec : recordsIncoming hor j old) (A : SupportedColumn vert hor j → SupportedColumn vert hor j → Prop)
    (hA : ∀ x y, A x y ↔ rowStep (verticalMaskEquiv n vert j) x.val.val.1 y.val.val.1 ∨ samePair old x.val.val.1 y.val.val.1)
    (x y : SupportedColumn vert hor j) :
    EqvGen A x y ↔ (columnGraph old (verticalMaskEquiv n vert j)).Reachable x.val.val.1 y.val.val.1 := by
  let e := activeLayerEquiv ht j hrec
  apply row_reach _ (fun x : SupportedColumn vert hor j => x.val.val.1) _ _ _ _ x y
  · intro a b h
    apply e.injective
    exact Subtype.ext h
  · intro r t hadj
    let a := e.symm ⟨r,incident_row_active _ _ _ _ hadj⟩
    exact ⟨a,rfl⟩
  · intro a b hn
    rw [row_adj, and_iff_right hn]
    exact hA a b

theorem tracks_first {n : ℕ} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor) (j : Fin n) (hj : j.val = 0) :
    TracksFrontier vert hor j [] := by
  rcases j with ⟨m,hm⟩
  change m = 0 at hj
  subst m
  let j : Fin n := ⟨0,hm⟩
  intro x y
  apply frontier_transfer ht j (empty_records_first hor j rfl) (GridPrefix.within _) _ x y
  intro a b
  simpa [samePair] using within_iff_rowStep vert hor j a b

private theorem next_edge {n : ℕ} (vert : Finset (Fin 4 × Fin n)) (hor : Finset (Fin 5 × Fin (n-1)))
    {j k : Fin n} (hjk : j.val+1 = k.val) (x : SupportedColumn vert hor j) (y : SupportedColumn vert hor k) :
    (activeGraph (vert.disjSum hor)).Adj x.val y.val ↔ x.val.val.1 = y.val.val.1 ∧
      (outgoingMask hor j).testBit x.val.val.1.val = true := by
  change (selectedGraph (vert.disjSum hor)).Adj x.val.val y.val.val ↔ _
  have hx : x.val.val = (x.val.val.1,j) := Prod.ext rfl (Fin.ext x.property)
  have hy : y.val.val = (y.val.val.1,k) := Prod.ext rfl (Fin.ext y.property)
  conv_lhs => rw [hx,hy]
  exact selected_next_column_iff vert hor hjk _ _

theorem tracks_succ {n : ℕ} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor) {j k : Fin n}
    (hjk : j.val+1 = k.val) {old : List ℕ} (cut : RecordsCut vert hor j old)
    (hrec : recordsIncoming hor k old) : TracksFrontier vert hor k old := by
  rcases k with ⟨m,hm⟩
  change j.val + 1 = m at hjk
  subst m
  let k : Fin n := ⟨j.val+1,hm⟩
  let G := activeGraph (vert.disjSum hor)
  let col := activeColumn (vert.disjSum hor)
  intro b c
  apply frontier_transfer ht k hrec (GridPrefix.nextRelation G (GridPrefix.frontier G col j.val)) _ b c
  intro x y
  change (GridPrefix.within G x y ∨ _) ↔ _
  rw [within_iff_rowStep vert hor k]
  apply or_congr_right
  constructor
  · rintro ⟨a,d,hax,had,hdy⟩
    obtain ⟨hax,hba⟩ := (next_edge vert hor (j:=j) (k:=k) rfl a x).mp hax
    obtain ⟨hdy,hbd⟩ := (next_edge vert hor (j:=j) (k:=k) rfl d y).mp hdy
    exact (cut _ _).mpr ⟨a,d,hax,hdy,hax ▸ hba,hdy ▸ hbd,had⟩
  · intro hp
    obtain ⟨a,d,hax,hdy,hba,hbd,had⟩ := (cut _ _).mp hp
    exact ⟨a,d,(next_edge vert hor (j:=j) (k:=k) rfl a x).mpr ⟨hax,hax ▸ hba⟩, had,
      (next_edge vert hor (j:=j) (k:=k) rfl d y).mpr ⟨hdy,hdy ▸ hbd⟩⟩

theorem recordsCut_of_pathsMatch {n : ℕ} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor) (j : Fin n)
    {old out : List ℕ} (hrec : recordsIncoming hor j old) (tracked : TracksFrontier vert hor j old)
    (matched : pathsMatch old (verticalMaskEquiv n vert j) out) : RecordsCut vert hor j out := by
  intro r t
  constructor
  · intro hpair
    obtain ⟨hr,ht',gpath⟩ := (matched r t).mp hpair
    have activeOfExit (i : Fin 5) (hi : i ∈ exitRows old (verticalMaskEquiv n vert j)) :
        i ∈ active old (verticalMaskEquiv n vert j) := by
      simp only [exitRows, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [active,hi]
    let x := (activeLayerEquiv ht j hrec).symm ⟨r,activeOfExit r hr⟩
    let y := (activeLayerEquiv ht j hrec).symm ⟨t,activeOfExit t ht'⟩
    exact ⟨x,y,rfl,rfl,(mem_exitRows_iff_outgoing ht j hrec r).mp hr,
      (mem_exitRows_iff_outgoing ht j hrec t).mp ht', (tracked x y).mpr gpath⟩
  · rintro ⟨x,y,rfl,rfl,hr,ht',hpath⟩
    exact (matched _ _).mpr ⟨(mem_exitRows_iff_outgoing ht j hrec _).mpr hr,
      (mem_exitRows_iff_outgoing ht j hrec _).mpr ht', (tracked x y).mp hpath⟩

end OMA358

namespace OMA358

open SimpleGraph

private theorem degree_as_card {X : Type*} (G : SimpleGraph X) (x : X)
    [Fintype (G.neighborSet x)] : G.degree x = Nat.card (G.neighborSet x) := by
  rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

set_option maxHeartbeats 4000000 in
/-- A connected degree-two graph crosses the boundary of each component
of a proper vertex subset at exactly two vertices, provided each vertex
on the inside has at most one edge to the outside. -/
theorem component_port_count {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hc : G.Connected) (h2 : ∀ x, G.degree x = 2)
    (U : Set V) (outside : Uᶜ.Nonempty)
    (unique_exit : ∀ x ∈ U, ∀ y ∉ U, ∀ z ∉ U, G.Adj x y → G.Adj x z → y = z)
    (C : (G.induce U).ConnectedComponent) :
    Nat.card {x : C.supp // ∃ y ∉ U, G.Adj x.val.val y} = 2 := by
  classical
  let ports : Finset C.supp := Finset.univ.filter (fun x => ∃ y ∉ U, G.Adj x.val.val y)
  have hp : ports.Nonempty := by
    obtain ⟨x,hx,y,hy,hxy⟩ := induced_component_has_exit G hc U outside C
    exact ⟨⟨x,hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,hy,hxy⟩⟩
  have deg (x : C.supp) : ((G.induce U).induce C.supp).degree x + (if x ∈ ports then 1 else 0) = 2 := by
    have same : ((G.induce U).induce C.supp).degree x = (G.induce U).degree x.val := by
      have h := (G.induce U).degree_induce_of_neighborSet_subset (s := C.supp) (v := x)
        (fun _ hy => C.mem_supp_of_adj_mem_supp x.property hy)
      simpa only [degree_as_card, SimpleGraph.ConnectedComponent.toSimpleGraph] using h
    have ind : (G.induce U).degree x.val = ((G.neighborFinset x.val.val) ∩ U.toFinset).card := by
      rw [← SimpleGraph.map_neighborFinset_induce, Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree]
    have count := Finset.card_inter_add_card_sdiff (G.neighborFinset x.val.val) U.toFinset
    rw [SimpleGraph.card_neighborFinset_eq_degree, h2] at count
    rw [same, ind]
    by_cases isport : x ∈ ports
    · obtain ⟨y,hy,hxy⟩ := (Finset.mem_filter.mp isport).2
      have only : G.neighborFinset x.val.val \ U.toFinset = {y} := by
        ext z
        simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Set.mem_toFinset,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hxz,hz⟩
          exact unique_exit _ x.val.property _ hz _ hy hxz hxy
        · rintro rfl
          exact ⟨hxy,hy⟩
      simpa [isport, only] using count
    · have empty : G.neighborFinset x.val.val \ U.toFinset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨hxz,hz⟩ := Finset.mem_sdiff.mp hz
        apply isport
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, by simpa using hz,
          (SimpleGraph.mem_neighborFinset ..).mp hxz⟩
      simpa [isport, empty] using count
  have count := port_card_eq_two ((G.induce U).induce C.supp) C.connected_toSimpleGraph ports hp deg
  simpa [ports, Nat.card_eq_fintype_card, Fintype.card_subtype] using count

end OMA358

namespace OMA358

/-- A vertex of the processed prefix has a neighbor outside the prefix exactly
when it is on the current column and its row has an outgoing horizontal edge. -/
theorem prefix_exit_iff_outgoing {n : ℕ} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) (hj : j.val+1 < n)
    (x : GridPrefix.Prefix (activeColumn (vert.disjSum hor)) (j.val+1)) :
    (∃ y : ActiveVertex (vert.disjSum hor), ¬ activeColumn _ y < j.val+1 ∧
      (activeGraph (vert.disjSum hor)).Adj x.val y) ↔
      x.val.val.2 = j ∧ (outgoingMask hor j).testBit x.val.val.1.val = true := by
  let s := vert.disjSum hor
  constructor
  · rintro ⟨y, hy, he⟩
    change ¬ y.val.2.val < j.val+1 at hy
    have hx : x.val.val.2.val < j.val+1 := x.property
    have adj : (selectedGraph s).Adj x.val.val y.val := he
    have bound := (adjacent_column_distance adj).2
    have hcol : x.val.val.2 = j := Fin.ext (by omega)
    have step : x.val.val.2.val + 1 = y.val.2.val := by omega
    have hbit := ((selected_next_column_iff vert hor step _ _).mp adj).2
    refine ⟨hcol, ?_⟩
    simpa only [hcol] using hbit
  · rintro ⟨hcol, hm⟩
    let next : Fin n := ⟨j.val+1, hj⟩
    have ha := (selected_next_column_iff vert hor (j:=j) (k:=next) rfl
      x.val.val.1 x.val.val.1).mpr ⟨rfl, hm⟩
    have vx : (x.val.val.1, j) = x.val.val := Prod.ext rfl hcol.symm
    rw [vx] at ha
    let y : ActiveVertex s := ⟨(x.val.val.1,next), ha.right_mem_support⟩
    exact ⟨y, lt_irrefl _, ha⟩


end OMA358

namespace OMA358

/-- The crossing vertices of the actual prefix component are in bijection with
the outgoing rows reachable in the transfer calculation. -/
theorem component_card_eq_row_count {n : ℕ} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : admissible (vert,hor))
    (j : Fin n) {old : List ℕ} (recIn : recordsIncoming hor j old)
    (tracked : TracksFrontier vert hor j old)
    (border : ∀ x : GridPrefix.Prefix (activeColumn (vert.disjSum hor)) (j.val+1),
      (∃ y, ¬ activeColumn (vert.disjSum hor) y < j.val+1 ∧
        (activeGraph (vert.disjSum hor)).Adj x.val y) ↔
      x.val.val.2 = j ∧ (outgoingMask hor j).testBit x.val.val.1.val = true)
    (two : ∀ C : (GridPrefix.prefGraph (activeGraph (vert.disjSum hor))
      (activeColumn (vert.disjSum hor)) (j.val+1)).ConnectedComponent,
      Nat.card {x : C.supp // ∃ y, ¬ activeColumn (vert.disjSum hor) y < j.val+1 ∧
        (activeGraph (vert.disjSum hor)).Adj x.val.val y} = 2)
    (i : Fin 5) (hi : i ∈ active old (verticalMaskEquiv n vert j)) :
    ((exitRows old (verticalMaskEquiv n vert j)).filter
      ((columnGraph old (verticalMaskEquiv n vert j)).Reachable i)).card = 2 := by
  classical
  let sel := vert.disjSum hor
  let col := activeColumn sel
  let G := activeGraph sel
  let H := GridPrefix.prefGraph G col (j.val+1)
  let down := verticalMaskEquiv n vert j
  let e := activeLayerEquiv ht.2 j recIn
  let a : SupportedColumn vert hor j := e.symm ⟨i,hi⟩
  let C := H.connectedComponentMk (GridPrefix.lastCol a)
  let S := (exitRows old down).filter ((columnGraph old down).Reachable i)
  let P := {x : C.supp // ∃ y, ¬ col y < j.val+1 ∧ G.Adj x.val.val y}
  have reach (b : SupportedColumn vert hor j) : GridPrefix.lastCol b ∈ C.supp ↔
      (columnGraph old down).Reachable i b.val.val.1 := by
    have outside : ∃ z, j.val ≤ col z := ⟨a.val, Nat.le_of_eq a.property.symm⟩
    have eqv := GridPrefix.frontier_connected_graph G col (activeGraph_nearest sel) ht.1.preconnected
      j.val outside a b
    change H.connectedComponentMk _ = H.connectedComponentMk _ ↔ _
    rw [SimpleGraph.ConnectedComponent.eq]
    exact ⟨fun h => (tracked a b).mp (eqv.mpr h.symm),
      fun h => (eqv.mp ((tracked a b).mpr h)).symm⟩
  have right (p : P) := (border p.val.val).mp p.property
  let row (p : P) : Fin 5 := p.val.val.val.val.1
  let colV (p : P) : SupportedColumn vert hor j :=
    ⟨p.val.val.val, (congrArg Fin.val (right p).1)⟩
  have inS (p : P) : row p ∈ S := Finset.mem_filter.mpr
    ⟨(mem_exitRows_iff_outgoing ht.2 j recIn _).mpr (right p).2,
      (reach (colV p)).mp p.val.property⟩
  let f (p : P) : ↥S := ⟨row p,inS p⟩
  have inj : Function.Injective f := by
    intro p q heq
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val heq) ((right p).1.trans (right q).1.symm)
  have surj : Function.Surjective f := by
    intro r
    obtain ⟨he,hr⟩ := Finset.mem_filter.mp r.property
    have act : r.val ∈ active old down := by
      simp only [exitRows,Finset.mem_filter,Finset.mem_univ,true_and] at he
      simp [active,he]
    let b : SupportedColumn vert hor j := e.symm ⟨r.val,act⟩
    let x := GridPrefix.lastCol b
    have hx : x ∈ C.supp := (reach b).mpr hr
    have hp := (border x).mpr ⟨rfl,(mem_exitRows_iff_outgoing ht.2 j recIn r.val).mp he⟩
    exact ⟨⟨⟨x,hx⟩,hp⟩,rfl⟩
  have eqcard := Nat.card_congr (Equiv.ofBijective f ⟨inj,surj⟩)
  have result := (eqcard.symm.trans (two C))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using result

end OMA358

namespace OMA358

open OMA.S_oeis_a358696

private theorem gridDegreeCard {V : Type*} (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] : G.degree v = Nat.card (G.neighborSet v) := by
  rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

/-- Every supported vertex of a locally admissible array has degree two
in the graph induced on its support. -/
theorem activeGraph_degree_two {n : ℕ} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor)
    (v : ActiveVertex (vert.disjSum hor)) [Fintype ((activeGraph (vert.disjSum hor)).neighborSet v)] :
    (activeGraph (vert.disjSum hor)).degree v = 2 := by
  classical
  let G := selectedGraph (vert.disjSum hor)
  have neighbors : G.neighborSet v.val ⊆ G.support := by
    intro w hw
    change G.Adj v.val w at hw
    exact (G.mem_support).mpr ⟨v.val, hw.symm⟩
  have h := G.degree_induce_of_neighborSet_subset (s := G.support) (v := v) neighbors
  have degree : G.degree v.val = localDegree vert hor v.val := by
    simpa only [gridDegreeCard] using degree_eq_localDegree vert hor v.val
  have pos := (mem_support_iff_localDegree_pos vert hor v.val).mp v.property
  have h2 : localDegree vert hor v.val = 2 := (ht v.val).resolve_right (fun h0 => by omega)
  simp only [gridDegreeCard] at h degree ⊢
  simpa only [activeGraph] using h.trans (degree.trans h2)

/-- A proper prefix omits an active vertex, for instance the top row vertex
in column k. -/
theorem prefix_outside {n : ℕ} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ht : localTests vert hor) (k : ℕ) (hk : k < n) :
    ({x : ActiveVertex (vert.disjSum hor) | activeColumn (vert.disjSum hor) x < k}ᶜ).Nonempty := by
  let v : Vertex n := (0, ⟨k,hk⟩)
  have bd : boundary v := Or.inl rfl
  have hpos := localTests_boundary_degree ht v bd
  let z : ActiveVertex (vert.disjSum hor) := ⟨v,(mem_support_iff_localDegree_pos vert hor v).mpr (by omega)⟩
  exact ⟨z, Nat.lt_irrefl k⟩

/-- A prefix vertex has at most one selected neighbor outside its prefix. -/
theorem prefix_unique_exit {n : ℕ} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (k : ℕ) :
    let sel := vert.disjSum hor
    let U : Set (ActiveVertex sel) := {x | activeColumn sel x < k}
    ∀ x ∈ U, ∀ y ∉ U, ∀ z ∉ U, (activeGraph sel).Adj x y → (activeGraph sel).Adj x z → y = z := by
  dsimp only
  intro x hx y hy z hz hxy hxz
  change x.val.2.val < k at hx
  change ¬y.val.2.val < k at hy
  change ¬z.val.2.val < k at hz
  apply Subtype.ext
  exact right_neighbor_unique vert hor (a:=x.val) (b:=y.val) (c:=z.val) hxy hxz (by omega) (by omega)

/-- In the closing column of a connected admissible grid, the row graph
has one component on its active rows. -/
theorem final_column_connected {n : ℕ} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ha : admissible (vert,hor))
    (j : Fin n) (hj : j.val+1 = n) {old : List ℕ} (hrec : recordsIncoming hor j old)
    (tracked : TracksFrontier vert hor j old) :
    ∀ r ∈ active old (verticalMaskEquiv n vert j), ∀ t ∈ active old (verticalMaskEquiv n vert j),
      (columnGraph old (verticalMaskEquiv n vert j)).Reachable r t := by
  intro r hr t ht
  let e := activeLayerEquiv ha.2 j hrec
  let x := e.symm ⟨r,hr⟩
  let y := e.symm ⟨t,ht⟩
  let sel := vert.disjSum hor
  have bound (z : ActiveVertex sel) : activeColumn sel z ≤ j.val := by
    change z.val.2.val ≤ j.val
    have := z.val.2.isLt
    omega
  have hconn := ((GridPrefix.preconnected_iff (activeGraph sel) (activeColumn sel)
    (activeGraph_nearest sel) j.val bound ⟨x⟩).mp ha.1.preconnected).2 x y
  exact (tracked x y).mp hconn

/-- Every component of the actual supported graph in a proper prefix has
exactly two vertices incident to an outgoing edge. -/
theorem proper_prefix_port_count {n : ℕ} {vert : Finset (Fin 4 × Fin n)}
    {hor : Finset (Fin 5 × Fin (n-1))} (ha : admissible (vert,hor)) (k : ℕ) (hk : k < n)
    (C : ((activeGraph (vert.disjSum hor)).induce {x | activeColumn (vert.disjSum hor) x < k}).ConnectedComponent) :
    Nat.card {x : C.supp // ∃ y : ActiveVertex (vert.disjSum hor),
      ¬ activeColumn (vert.disjSum hor) y < k ∧ (activeGraph (vert.disjSum hor)).Adj x.val.val y} = 2 := by
  classical
  exact component_port_count (activeGraph (vert.disjSum hor)) ha.1
    (fun x => activeGraph_degree_two ha.2 x) _ (prefix_outside ha.2 k hk) (prefix_unique_exit vert hor k) C

end OMA358

namespace OMA358

/-- A boundary-covering grid cycle satisfies every geometric transfer test. -/
theorem geom_of_admissible {k : ℕ} {vert : Finset (Fin 4 × Fin (k+2))}
    {hor : Finset (Fin 5 × Fin (k+2-1))} (ha : admissible (vert,hor))
    (j : Fin (k+2)) (old : List ℕ) (recIn : recordsIncoming hor j old)
    (tracked : TracksFrontier vert hor j old) :
    geometricChoice (stripKind j) old (verticalMaskEquiv (k+2) vert j) := by
  classical
  have side : stripKind j ≠ .middle → j.val = 0 ∨ j.val+1 = k+2 := by
    contrapose!
    rintro ⟨h₀,h₁⟩
    simp only [stripKind,suffixKind,if_neg h₀,if_neg h₁]
  have last : stripKind j = .last ↔ j.val+1 = k+2 := by
    by_cases h₀ : j.val = 0
    · simp [stripKind,h₀]
    · simp [stripKind,suffixKind,h₀]
  refine ⟨validDegree_of_localTests ha.2 j recIn _ side last.mp, ?_⟩
  split
  next hl => exact final_column_connected ha j (last.mp hl) recIn tracked
  next hl =>
    have bound := j.isLt
    have hne : j.val+1 ≠ k+2 := fun he => hl (last.mpr he)
    have hj : j.val+1 < k+2 := by omega
    apply component_card_eq_row_count ha j recIn tracked (prefix_exit_iff_outgoing vert hor j hj)
    exact fun C => proper_prefix_port_count ha _ hj C

end OMA358

namespace OMA358

private theorem first_next_indexed {v : ColumnMask} {t : List ℕ}
    (h : columnStep .first [] v = some t) : ∃ i : State, t = frontier i := by
  have hm := first_outcomes.mem_iff.mp (List.mem_filterMap.mpr ⟨v, by simp, h⟩)
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hm
  exact ⟨i, List.eq_of_mem_replicate hi⟩

private theorem middle_next_indexed (i : State) {v : ColumnMask} {t : List ℕ}
    (h : columnStep .middle (frontier i) v = some t) : ∃ j : State, t = frontier j := by
  have hm := (middle_outcomes i).mem_iff.mp (List.mem_filterMap.mpr ⟨v, by simp, h⟩)
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hm
  exact ⟨j, List.eq_of_mem_replicate hj⟩

private theorem checked_progress {kind s m} (hc : graphCheck kind s m)
    (hg : geometricChoice kind s m) :
    ∃ out, columnStep kind s m = some out ∧
      (if kind = .last then out = [] else pathsMatch s m out) := by
  have hex := hc.1.mpr hg
  cases he : columnStep kind s m with
  | none => simp [he] at hex
  | some out => exact ⟨out, rfl, by simpa only [he] using hc.2⟩

private theorem forward_suffix {k : ℕ} (m : Fin (k+1) → ColumnMask)
    (inv : Fin (k+1) → List ℕ → Prop)
    (hgeom : ∀ j s, inv j s → geometricChoice (suffixKind j) s (m j))
    (hadv : ∀ j l : Fin (k+1), j.val+1 = l.val → ∀ s t, inv j s →
      columnStep (suffixKind j) s (m j) = some t → pathsMatch s (m j) t → inv l t)
    {s : List ℕ} (hind : ∃ i : State, s = frontier i) (hs : inv 0 s) :
    HistoryFrom k s (List.ofFn m) := by
  induction k generalizing s with
  | zero =>
    obtain ⟨i,rfl⟩ := hind
    have hg : geometricChoice .last (frontier i) (m 0) := hgeom 0 _ hs
    obtain ⟨out, hstep, hout⟩ := checked_progress (column_checks.2.2 i (m 0)) hg
    have hnil : out = [] := hout
    rw [hnil] at hstep
    rw [List.ofFn_succ]
    exact .last hstep
  | succ k ih =>
    obtain ⟨i,rfl⟩ := hind
    have hk : suffixKind (0 : Fin (k+2)) = .middle := by simp [suffixKind]
    have hg := hgeom 0 _ hs
    rw [hk] at hg
    obtain ⟨out,hstep,hout⟩ := checked_progress (column_checks.2.1 i (m 0)) hg
    have hpath : pathsMatch (frontier i) (m 0) out := hout
    have hs' : inv (0 : Fin (k+1)).succ out :=
      hadv 0 _ rfl _ _ hs (by simpa only [hk] using hstep) hpath
    rw [List.ofFn_succ]
    apply HistoryFrom.middle hstep
    apply ih (fun j => m j.succ) (fun j => inv j.succ) ?_ ?_ (middle_next_indexed i hstep) hs'
    · intro j t ht
      simpa [suffixKind, Fin.val_succ] using hgeom j.succ t ht
    · intro j l hj s t hI hstep' hP
      apply hadv j.succ l.succ (by simpa [Fin.val_succ] using hj) s t hI _ hP
      simpa [suffixKind, Fin.val_succ] using hstep'

/-- A local invariant that holds at the first cut, advances through matching
frontiers, and gives the geometric choice tests yields an accepted word. -/
theorem accepted_of_geometric_induction {k : ℕ} (m : Fin (k+2) → ColumnMask)
    (inv : Fin (k+2) → List ℕ → Prop)
    (hinit : inv 0 [])
    (hgeom : ∀ j s, inv j s → geometricChoice (stripKind j) s (m j))
    (hadv : ∀ j l : Fin (k+2), j.val+1 = l.val → ∀ s t, inv j s →
      columnStep (stripKind j) s (m j) = some t → pathsMatch s (m j) t → inv l t) :
    List.ofFn m ∈ acceptedWords k := by
  have hg : geometricChoice .first [] (m 0) := hgeom 0 [] hinit
  obtain ⟨out,hstep,hout⟩ := checked_progress (column_checks.1 (m 0)) hg
  have hpath : pathsMatch [] (m 0) out := hout
  have hs : inv (0 : Fin (k+1)).succ out := hadv 0 _ rfl [] _ hinit hstep hpath
  apply mem_acceptedWords_iff.mpr
  rw [List.ofFn_succ]
  refine ⟨out,hstep,forward_suffix (fun i => m i.succ) (fun i => inv i.succ)
    ?_ ?_ (first_next_indexed hstep) hs⟩
  · intro j t ht
    simpa [stripKind, suffixKind, Fin.val_succ] using hgeom j.succ t ht
  · intro j l hj s t hI hstep' hP
    apply hadv j.succ l.succ (by simpa [Fin.val_succ] using hj) s t hI _ hP
    simpa [stripKind, suffixKind, Fin.val_succ] using hstep'

/-- Graph-facing application. Only the geometric validity of the current graph
frontier and transport of its connectivity data are left to the graph
invariant. Incoming horizontal incidences and finite-state availability are
propagated by the proved coordinate and transfer lemmas. -/
theorem graphWord_accepted_of_geometry {k : ℕ}
    {vert : Finset (Fin 4 × Fin (k+2))} {hor : Finset (Fin 5 × Fin (k+2-1))}
    (ht : localTests vert hor) (tracks : Fin (k+2) → List ℕ → Prop)
    (hstart : tracks 0 [])
    (hgeom : ∀ j old, recordsIncoming hor j old → tracks j old →
      geometricChoice (stripKind j) old (verticalMaskEquiv (k+2) vert j))
    (hadvance : ∀ j l : Fin (k+2), j.val+1 = l.val → ∀ old out, recordsIncoming hor j old →
      tracks j old → columnStep (stripKind j) old (verticalMaskEquiv (k+2) vert j) = some out →
      pathsMatch old (verticalMaskEquiv (k+2) vert j) out → tracks l out) :
    List.ofFn (verticalMaskEquiv (k+2) vert) ∈ acceptedWords k := by
  apply accepted_of_geometric_induction _ (fun j s => recordsIncoming hor j s ∧ tracks j s)
  · exact ⟨empty_records_first _ _ rfl, hstart⟩
  · exact fun j s h => hgeom j s h.1 h.2
  · intro j l hj s t h hstep hpath
    exact ⟨recordsIncoming_next ht hj h.1 hpath, hadvance j l hj s t h.1 h.2 hstep hpath⟩

end OMA358

namespace OMA358

/-- A boundary-covering grid cycle is accepted once its global connectivity
and port counts give the geometric checks in each correctly tracked column. -/
theorem admissibleWord_of_geom {k : ℕ}
    {vert : Finset (Fin 4 × Fin (k+2))} {hor : Finset (Fin 5 × Fin (k+2-1))}
    (hA : admissible (vert,hor))
    (hgeom : ∀ j old, recordsIncoming hor j old → TracksFrontier vert hor j old →
      geometricChoice (stripKind j) old (verticalMaskEquiv (k+2) vert j)) :
    List.ofFn (verticalMaskEquiv (k+2) vert) ∈ acceptedWords k := by
  apply graphWord_accepted_of_geometry hA.2 (TracksFrontier vert hor)
    (tracks_first hA.2 0 rfl) hgeom
  intro j l hj old out hrec hold _ hmatch
  exact tracks_succ hA.2 hj (recordsCut_of_pathsMatch hA.2 j hrec hold hmatch)
    (recordsIncoming_next hA.2 hj hrec hmatch)

end OMA358

namespace OMA358

open OMA.S_oeis_a358696

/-- The two active grid vertices at a chosen outgoing edge belong to consecutive
columns and share the prescribed row. -/
theorem column_edge_of_outgoing {n : ℕ} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (j : Fin n) (hj : j.val+1 < n) (r : Fin 5)
    (h : (outgoingMask hor j).testBit r.val = true) :
    let s := vert.disjSum hor
    ∃ d : GridPrefix.Column (activeColumn s) j.val,
      ∃ z : GridPrefix.Column (activeColumn s) (j.val+1),
        d.val.val.1 = r ∧ (activeGraph s).Adj d.val z.val := by
  let p : Fin (n-1) := ⟨j.val, by omega⟩
  have hm : (r,p) ∈ hor := (horizontal_testBit_iff hor r p).mp (by simpa [outgoingMask, hj, p] using h)
  let q : EdgePos n := .inr (r,p)
  have hq : q ∈ vert.disjSum hor := by simpa [q] using hm
  let s := vert.disjSum hor
  have he := (mem_edgeMaskEquiv s q).mpr hq
  rw [← SetLike.mem_coe, ← selectedGraph_edgeSet] at he
  have adj : (selectedGraph s).Adj (r,posLeft p) (r,posRight p) := he
  let d : ActiveVertex s := ⟨(r,posLeft p), adj.left_mem_support⟩
  let z : ActiveVertex s := ⟨(r,posRight p), adj.right_mem_support⟩
  exact ⟨⟨d,rfl⟩, ⟨z,rfl⟩,rfl,adj⟩

private theorem live_of_checked_column {n : ℕ} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (ht : localTests vert hor) (j : Fin n)
    (hj : j.val+1 < n) {old out : List ℕ} {kind : ColumnKind} (hk : kind ≠ .last)
    (hc : CheckedColumn kind old (verticalMaskEquiv n vert j) out)
    (hin : recordsIncoming hor j old) (agree : TracksFrontier vert hor j old) :
    GridPrefix.live (activeGraph (vert.disjSum hor)) (activeColumn (vert.disjSum hor)) j.val := by
  intro b
  have col : b.val.val.2 = j := Fin.ext b.property
  have hsupp := b.val.property
  have hv : (b.val.val.1,j) = b.val.val := Prod.ext rfl col.symm
  have hbact := (mem_active_iff_graph_support ht j hin b.val.val.1).mpr (hv ▸ hsupp)
  have geom := hc.geometric.2
  simp only [hk, ↓reduceIte] at geom
  have card := geom _ hbact
  have hn := Finset.card_pos.mp (show 0 < _ by omega : 0 < ((exitRows old (verticalMaskEquiv n vert j)).filter
    ((columnGraph old (verticalMaskEquiv n vert j)).Reachable b.val.val.1)).card)
  obtain ⟨r, hr⟩ := hn
  obtain ⟨hexit, hreach⟩ := Finset.mem_filter.mp hr
  have hrout := (mem_exitRows_iff_outgoing ht j hin r).mp hexit
  obtain ⟨d,z,hrow,ha⟩ := column_edge_of_outgoing vert hor j hj r hrout
  exact ⟨d,z,(agree b d).mpr (hrow ▸ hreach),ha⟩

private theorem last_connected_of_checked_column {n : ℕ} (vert : Finset (Fin 4 × Fin n))
    (hor : Finset (Fin 5 × Fin (n-1))) (ht : localTests vert hor) (j : Fin n)
    {old out : List ℕ} (hc : CheckedColumn .last old (verticalMaskEquiv n vert j) out)
    (hin : recordsIncoming hor j old) (agree : TracksFrontier vert hor j old) :
    ∀ b c, GridPrefix.frontier (activeGraph (vert.disjSum hor))
      (activeColumn (vert.disjSum hor)) j.val b c := by
  intro b c
  apply (agree b c).mpr
  have hact (x : GridPrefix.Column (activeColumn (vert.disjSum hor)) j.val) :
      x.val.val.1 ∈ active old (verticalMaskEquiv n vert j) := by
    apply (mem_active_iff_graph_support ht j hin _).mpr
    have hcol : x.val.val.2 = j := Fin.ext x.property
    exact (show (x.val.val.1, j) = x.val.val from Prod.ext rfl hcol.symm) ▸ x.val.property
  exact (if_pos rfl ▸ hc.geometric.2) _ (hact b) _ (hact c)

/-- The checked masks and their verified frontier connectivity suffice to yield
the global connectedness predicate for the actual selected grid edges. -/
theorem admissible_of_checked_columns {k : ℕ} (vert : Finset (Fin 4 × Fin (k+2)))
    (hor : Finset (Fin 5 × Fin ((k+2)-1))) (ht : localTests vert hor)
    (cuts : Fin (k+3) → List ℕ)
    (hcol : ∀ j : Fin (k+2), CheckedColumn (stripKind j) (cuts j.castSucc)
      (verticalMaskEquiv (k+2) vert j) (cuts j.succ))
    (hin : ∀ j : Fin (k+2), recordsIncoming hor j (cuts j.castSucc))
    (agree : ∀ j : Fin (k+2), TracksFrontier vert hor j (cuts j.castSucc)) :
    admissible (vert, hor) := by
  apply (admissible_iff_frontier vert hor ht).mpr
  constructor
  · intro t ht'
    let j : Fin (k+2) := ⟨t, by omega⟩
    have hk : stripKind j ≠ .last := by
      by_cases ht0 : t = 0 <;> simp [stripKind, suffixKind, j, ht0]
      omega
    exact live_of_checked_column vert hor ht j (by change t+1 < k+2; omega) hk
      (hcol j) (hin j) (agree j)
  · let j := Fin.last (k+1)
    have hk : stripKind j = .last := by simp [j, stripKind, suffixKind]
    exact last_connected_of_checked_column vert hor ht j (hk ▸ hcol j) (hin j) (agree j)

theorem CheckedColumn.paths_of_nonlast {kind old v out} (h : CheckedColumn kind old v out)
    (hn : kind ≠ .last) : pathsMatch old v out := by
  have hp := h.check.2
  simpa only [h.step, hn, ↓reduceIte] using hp

/-- Propagate the exact row-connectivity interpretation along each cut of
the accepted word. -/
private theorem tracks_checked_history {k : ℕ} (vert : Finset (Fin 4 × Fin (k+2)))
    (hor : Finset (Fin 5 × Fin ((k+2)-1))) (ht : localTests vert hor)
    (cuts : Fin (k+3) → List ℕ) (h0 : cuts 0 = [])
    (hcol : ∀ j : Fin (k+2), CheckedColumn (stripKind j) (cuts j.castSucc)
      (verticalMaskEquiv (k+2) vert j) (cuts j.succ))
    (hin : ∀ j : Fin (k+2), recordsIncoming hor j (cuts j.castSucc)) :
    ∀ j : Fin (k+2), TracksFrontier vert hor j (cuts j.castSucc) := by
  intro j
  induction j using Fin.induction with
  | zero =>
    change TracksFrontier vert hor 0 (cuts 0)
    rw [h0]
    exact tracks_first ht _ rfl
  | succ i ih =>
    have hk : stripKind i.castSucc ≠ .last := by
      have hi := i.isLt
      by_cases hz : i.val = 0 <;> simp [stripKind, suffixKind, hz]
      omega
    have recorded := recordsCut_of_pathsMatch ht i.castSucc (hin _) ih
      ((hcol i.castSucc).paths_of_nonlast hk)
    exact tracks_succ ht rfl recorded (hin i.succ)

/-- Every accepted vertical word is realized by a genuine connected boundary
cycle in the sense of the coordinate-array predicate. -/
theorem IsColumnHistory.exists_admissible {k : ℕ} {w : MaskWord} (hw : IsColumnHistory k w) :
    ∃ (vert : Finset (Fin 4 × Fin (k+2))) (hor : Finset (Fin 5 × Fin ((k+2)-1))),
      List.ofFn (verticalMaskEquiv (k+2) vert) = w ∧ admissible (vert,hor) := by
  obtain ⟨v,h,c,hword,hfirst,_,checked,hin,_,ht⟩ := hw.exists_localTests
  refine ⟨v,h,hword,admissible_of_checked_columns v h ht c checked hin ?_⟩
  exact tracks_checked_history v h ht c hfirst checked hin

/-- Surjectivity direction for the vertical-word encoding of admissible edge arrays. -/
theorem acceptedWord_realized {k : ℕ} {w : MaskWord} (hw : w ∈ acceptedWords k) :
    ∃ arr : {a : EdgeArrays (k+2) // admissible a},
      (verticalWordEquiv (k+2) arr.val.1).val = w := by
  obtain ⟨v,h,hword,ha⟩ := (mem_acceptedWords_iff.mp hw).exists_admissible
  exact ⟨⟨(v,h),ha⟩, hword⟩


end OMA358

namespace OMA358

open OMA.S_oeis_a358696

/-- Count distinct admissible arrays by the vertical word that determines them.
The two hypotheses are the forward and reverse graph/word constructions. -/
theorem graph_count_eq_after_of_bijection {k : ℕ}
    (forward : ∀ arr : {a : EdgeArrays (k+2) // admissible a},
      List.ofFn (verticalMaskEquiv (k+2) arr.val.1) ∈ acceptedWords k)
    (reverse : ∀ w ∈ acceptedWords k, ∃ arr : {a : EdgeArrays (k+2) // admissible a},
      (verticalWordEquiv (k+2) arr.val.1).val = w) :
    a (k+2) = after k := by
  let f (arr : {a : EdgeArrays (k+2) // admissible a}) :
      {w // w ∈ (acceptedWords k).toFinset} :=
    ⟨_, List.mem_toFinset.mpr (forward arr)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hword : (verticalWordEquiv (k+2) x.val.1).val =
        (verticalWordEquiv (k+2) y.val.1).val := congrArg (fun z : {w // w ∈ (acceptedWords k).toFinset} => z.val) hxy
    apply (admissibleVerticalEmbedding (k+2)).injective
    exact (verticalWordEquiv (k+2)).injective (Subtype.ext hword)
  have hsur : Function.Surjective f := by
    intro w
    obtain ⟨arr, h⟩ := reverse w.val (List.mem_toFinset.mp w.property)
    exact ⟨arr, Subtype.ext h⟩
  have hc := Nat.card_congr (Equiv.ofBijective f ⟨hinj,hsur⟩)
  rw [count_eq_admissible, hc]
  change (Nat.card ↥(acceptedWords k).toFinset : ℤ) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact acceptedWords_card k

/-- The exact conjectured recurrence on genuine edge-set cycles follows from
their count in widths k+2, including all initial cases used at n=11. -/
theorem graph_recurrence_of_counts (hc : ∀ k : ℕ, a (k+2) = after k)
    (n : ℕ) (hn : 11 ≤ n) :
    a n = 6 * a (n-1) + a (n-2) - 20 * a (n-3) + 37 * a (n-4) + 16 * a (n-5) -
      12 * a (n-6) - 7 * a (n-7) + 5 * a (n-8) - a (n-9) := by
  have ha (m : ℕ) (hm : 2 ≤ m) : a m = count m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k+2 := ⟨m-2, by omega⟩
    exact (hc k).trans (count_add_two k).symm
  simp (disch := omega) only [ha]
  exact width_recurrence n (by omega)

end OMA358

/-- Manyama's recurrence for boundary-covering simple cycles on the five-row grid. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a358696.main := by
  apply OMA358.graph_recurrence_of_counts
  intro k
  apply OMA358.graph_count_eq_after_of_bijection
  · intro arr
    exact OMA358.admissibleWord_of_geom arr.property (OMA358.geom_of_admissible arr.property)
  · exact fun _ hw => OMA358.acceptedWord_realized hw
