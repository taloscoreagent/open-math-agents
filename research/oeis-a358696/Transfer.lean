import Mathlib

/-!
Exact integer calculation for the column transfer matrix of OEIS A358696.
The matrix columns correspond to the outgoing state and the rows to the
incoming state. The link from boundary-covering undirected simple grid
cycles to the transition data is a separate combinatorial claim.
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
