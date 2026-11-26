import OMAStatements.S_oeis_a229623

/-!
Derek Orr's 2015 conjecture for OEIS A229623.

For a decimal palindrome x with at least four digits, let y be x minus its
digit sum. If y has fewer digits, the leading digit of x must be one and
all its interior digits must be zero. Conversely, subtracting two from
10 ^ k + 1 gives a string of nines.

To exclude equal lengths, strip matching digits from both ends of x and y
until the first disagreement. Each stripped pair multiplies their remaining
difference by ten and contributes at most eighteen to the digit sum of x.
If the first differing outer digits are a > b and the interior of x has value
u, the difference within the stripped numbers is at least 11 + 10u, even
if the interior of y is all nines. That bound excludes any stripped pair.
With no stripped pairs the same bound forces u = 0 and a = b + 1. The
difference is then odd, whereas the digit sum of x is 2a. A first difference
at a single middle digit is ruled out by its place value.

A finite check identifies the first twenty terms. Monotonicity of 10 ^ k + 1
then gives the one-based indexing in Orr's conjecture.
-/

namespace OMA229

theorem sum_le_value (s : List ℕ) : s.sum ≤ Nat.ofDigits 10 s := by
  induction s with
  | nil => simp
  | cons x s ih =>
    simp only [List.sum_cons, Nat.ofDigits_cons]
    omega

theorem pal_outer (s : List ℕ) (hp : s.Palindrome) (hl : 2 ≤ s.length) :
    ∃ a t, s = a :: (t ++ [a]) ∧ t.Palindrome := by
  cases hp with
  | nil => simp at hl
  | singleton a => simp at hl
  | cons_concat a t => exact ⟨a, _, rfl, t⟩

theorem four_digits (x : ℕ) (hx : 1000 ≤ x) : 3 < (Nat.digits 10 x).length :=
  (Nat.lt_digits_length_iff (by decide : 1 < 10) x).2 hx

theorem shorter_classification (x : ℕ) (hx : 1000 ≤ x) (hp : (Nat.digits 10 x).Palindrome)
    (hl : (Nat.digits 10 (x - (Nat.digits 10 x).sum)).length < (Nat.digits 10 x).length) :
    ∃ k ≥ 3, x = 10 ^ k + 1 := by
  have hL := four_digits x hx
  obtain ⟨a, t, ht, _⟩ := pal_outer _ hp (by omega)
  have ha : a < 10 := Nat.digits_lt_base (by decide) (by rw [ht]; simp)
  have han : a ≠ 0 := by
    have hh := Nat.getLast_digit_ne_zero 10 (m := x) (by omega)
    simpa [ht] using hh
  have hs : (Nat.digits 10 x).sum = a + (t.sum + a) := by simp [ht, Nat.add_comm]
  have hsum := sum_le_value (Nat.digits 10 x)
  rw [Nat.ofDigits_digits] at hsum
  have hval : x = a * 10 ^ (t.length + 1) + 10 * Nat.ofDigits 10 t + a := by
    calc
      x = Nat.ofDigits 10 (a :: (t ++ [a])) := by rw [← ht, Nat.ofDigits_digits]
      _ = _ := by simp [Nat.ofDigits_cons, Nat.ofDigits_append, pow_succ]; ring
  have hlen : (Nat.digits 10 x).length = t.length + 2 := by simp [ht]
  have hless : x - (Nat.digits 10 x).sum < 10 ^ (t.length + 1) :=
    (Nat.digits_length_le_iff (by decide : 1 < 10) _).1 (by omega)
  have htSum := sum_le_value t
  have hN : 10 ≤ 10 ^ (t.length + 1) := by
    rw [pow_succ]
    have hh : 0 < 10 ^ t.length := by positivity
    omega
  have ha1 : a = 1 := by
    by_contra hbad
    have h2 : 2 ≤ a := by omega
    have hc := Nat.mul_le_mul_right (10 ^ (t.length + 1)) h2
    omega
  have hv0 : Nat.ofDigits 10 t = 0 := by simp [ha1] at hval; omega
  exact ⟨t.length + 1, by omega, by simpa [ha1, hv0] using hval⟩

theorem digits_pow_plus_one (j : ℕ) :
    Nat.digits 10 (10 ^ (j + 1) + 1) = 1 :: (List.replicate j 0 ++ [1]) := by
  let s : List ℕ := 1 :: (List.replicate j 0 ++ [1])
  have hval : Nat.ofDigits 10 s = 10 ^ (j + 1) + 1 := by
    simp [s, Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_replicate_zero, pow_succ]
    ring
  rw [← hval]
  apply Nat.digits_ofDigits 10 (by decide)
  · intro a ha
    simp [s] at ha
    rcases ha with h | h | h <;> omega
  · simp [s]

theorem nines_value (k : ℕ) : Nat.ofDigits 10 (List.replicate k 9) + 1 = 10 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    omega

theorem digits_nines (k : ℕ) : Nat.digits 10 (10 ^ k - 1) = List.replicate k 9 := by
  have hval : Nat.ofDigits 10 (List.replicate k 9) = 10 ^ k - 1 := by
    have := nines_value k
    omega
  rw [← hval]
  apply Nat.digits_ofDigits 10 (by decide)
  · intro a ha
    simp at ha
    omega
  · cases k <;> simp

theorem pow_plus_one_palindromes (k : ℕ) (hk : 3 ≤ k) :
    (Nat.digits 10 (10 ^ k + 1)).Palindrome ∧
    (Nat.digits 10 ((10 ^ k + 1) - (Nat.digits 10 (10 ^ k + 1)).sum)).Palindrome := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  rw [digits_pow_plus_one]
  constructor
  · apply List.Palindrome.cons_concat
    exact List.Palindrome.of_reverse_eq (by simp)
  · have hsum : (1 :: (List.replicate j 0 ++ [1]) : List ℕ).sum = 2 := by simp
    rw [hsum, show 10 ^ (j + 1) + 1 - 2 = 10 ^ (j + 1) - 1 by omega, digits_nines]
    exact List.Palindrome.of_reverse_eq (by simp)

private theorem pow_ten_lower (h : ℕ) : 9 * h + 1 ≤ 10 ^ h := by
  induction h with
  | zero => decide
  | succ h ih =>
    rw [pow_succ]
    omega

theorem unequal_outer {a b u v p g h s t : ℕ} (ha : a < 10) (_hb : b < 10)
    (hab : a ≠ b) (hu : u < p) (hv : v < p) (ht : t ≤ u) (hs : s ≤ 18 * h)
    (hg : 0 < g) (he : a + 10 * u + 10 * p * a = (b + 10 * v + 10 * p * b) + g)
    (htot : 10 ^ h * g = s + (a + t + a)) : False := by
  have hba : b < a := by
    by_contra! hn
    have hle : a + 1 ≤ b := by omega
    have hm := Nat.mul_le_mul_left (10 * p) hle
    nlinarith
  have hm := Nat.mul_le_mul_left (10 * p) (show b + 1 ≤ a by omega)
  have hg' : 11 + 10 * u ≤ g := by nlinarith
  have hp := pow_ten_lower h
  have h0 : h = 0 := by
    by_contra hn
    have hbnd := Nat.mul_le_mul_left (10 ^ h) hg'
    have hp1 : 1 ≤ 10 ^ h := by omega
    have hp2 : 1 ≤ h := by omega
    have hu' := Nat.mul_le_mul_right u hp1
    nlinarith
  subst h
  simp at hs htot
  have hu0 : u = 0 := by omega
  subst u
  have ht0 : t = 0 := by omega
  subst t
  have hab1 : a = b + 1 := by
    by_contra h
    have hl : b + 2 ≤ a := by omega
    have hm' := Nat.mul_le_mul_left (10 * p) hl
    nlinarith
  rw [hab1, Nat.mul_add] at he
  omega

private theorem middle_digit_bound (h : ℕ) (hh : 2 ≤ h) : 18 * h + 9 < 10 ^ h := by
  induction h, hh using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ]
    omega

private theorem wrapped_value (a : ℕ) (l : List ℕ) :
    Nat.ofDigits 10 (a :: (l ++ [a])) =
      a + 10 * Nat.ofDigits 10 l + 10 * (10 ^ l.length) * a := by
  rw [Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_singleton]
  ring

theorem same_length_impossible {l : List ℕ} (hl : l.Palindrome) :
    ∀ {r : List ℕ}, r.Palindrome → l.length = r.length →
    (∀ d ∈ l, d < 10) → (∀ d ∈ r, d < 10) →
    ∀ (h s g : ℕ), s ≤ 18 * h → 4 ≤ 2 * h + l.length → 0 < g →
    Nat.ofDigits 10 l = Nat.ofDigits 10 r + g → 10 ^ h * g = s + l.sum → False := by
  induction hl with
  | nil =>
    intro r hr hlen dl dr h s g hs hwide hg hval hsum
    have hval' : 0 = Nat.ofDigits 10 r + g := hval
    omega
  | singleton a =>
    intro r hr hlen dl dr h s g hs hwide hg hval hsum
    have ha : a < 10 := dl _ (by simp)
    have hh : 2 ≤ h := by simp at hwide; omega
    have hbig := middle_digit_bound h hh
    have hmul : 10 ^ h ≤ 10 ^ h * g := Nat.le_mul_of_pos_right _ hg
    simp at hsum
    omega
  | cons_concat a hl ih =>
    rename_i l
    intro r hr hlen dl dr h s g hs hwide hg hval hsum
    cases hr with
    | nil => simp at hlen
    | singleton b => simp at hlen
    | cons_concat b hr =>
      rename_i r
      have lens : l.length = r.length := by simpa using hlen
      have ha : a < 10 := dl a (by simp)
      have hb : b < 10 := dr b (by simp)
      have dl' : ∀ d ∈ l, d < 10 := fun d hd => dl d (by simp [hd])
      have dr' : ∀ d ∈ r, d < 10 := fun d hd => dr d (by simp [hd])
      rw [wrapped_value, wrapped_value, ← lens] at hval
      simp only [List.sum_cons, List.sum_append, List.sum_nil, Nat.add_zero] at hsum
      by_cases hab : a = b
      · subst b
        let u := Nat.ofDigits 10 l
        let v := Nat.ofDigits 10 r
        change a + 10 * u + 10 * (10 ^ l.length) * a = a + 10 * v + 10 * (10 ^ l.length) * a + g at hval
        have huv : v < u := by omega
        let g' := u - v
        have huv' : u = v + g' := by dsimp [g']; omega
        have hgg : g = 10 * g' := by omega
        refine ih hr lens dl' dr' (h + 1) (s + a + a) g' (by omega) ?_ (by dsimp [g']; omega) huv' ?_
        · simp at hwide
          omega
        · rw [pow_succ, Nat.mul_assoc, ← hgg]
          omega
      · exact unequal_outer ha hb hab
          (Nat.ofDigits_lt_base_pow_length (by decide) dl')
          (lens ▸ Nat.ofDigits_lt_base_pow_length (by decide) dr')
          (sum_le_value l) hs hg hval (by omega)

theorem decimal_sum_pos (x : ℕ) (hx : x ≠ 0) : 0 < (Nat.digits 10 x).sum := by
  have hn : Nat.digits 10 x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hx
  have htop : (Nat.digits 10 x).getLast hn ≠ 0 := Nat.getLast_digit_ne_zero 10 hx
  have hsum := List.le_sum_of_mem (List.getLast_mem hn)
  omega

theorem classification (x : ℕ) (hx : 1000 ≤ x) :
    OMA.S_oeis_a229623.qualifies x ↔ ∃ k : ℕ, 3 ≤ k ∧ x = 10 ^ k + 1 := by
  constructor
  · rintro ⟨hp, hq⟩
    let y := x - (Nat.digits 10 x).sum
    have hlen : (Nat.digits 10 y).length ≤ (Nat.digits 10 x).length :=
      Nat.le_length_digits_le 10 y x (Nat.sub_le ..)
    rcases lt_or_eq_of_le hlen with hlt | heq
    · exact shorter_classification x hx hp hlt
    · have hwide := four_digits x hx
      have hpos := decimal_sum_pos x (by omega)
      have hsum := sum_le_value (Nat.digits 10 x)
      rw [Nat.ofDigits_digits] at hsum
      exfalso
      apply same_length_impossible hp hq heq.symm
        (fun _ hd => Nat.digits_lt_base (by decide) hd)
        (fun _ hd => Nat.digits_lt_base (by decide) hd)
        0 0 (Nat.digits 10 x).sum (by decide) (by omega) hpos
      · simp only [Nat.ofDigits_digits]
        omega
      · simp
  · rintro ⟨k, hk, rfl⟩
    exact pow_plus_one_palindromes k hk

open OMA.S_oeis_a229623

private instance : DecidablePred qualifies := fun n => by unfold qualifies; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem small_terms :
    (List.range 1001).filter (fun n => decide (qualifies n)) =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 101, 181, 262, 343, 424, 686, 767, 848, 929] := by
  decide +kernel

private theorem count_first : Nat.count qualifies 1001 = 20 := by
  rw [Nat.count, List.countP_eq_length_filter, small_terms]
  rfl

theorem indexed_of_classification
    (classification : ∀ n, 1000 ≤ n → (qualifies n ↔ ∃ k : ℕ, 3 ≤ k ∧ n = 10 ^ k + 1)) :
    ∀ n : ℕ, 21 ≤ n → Nat.nth qualifies (n - 1) = 10 ^ (n - 18) + 1 := by
  have hp : StrictMono (fun k : ℕ => (10 : ℕ) ^ k + 1) := by
    intro i j hij
    exact Nat.add_lt_add_right (Nat.pow_lt_pow_right (by decide) hij) _
  have hterm (k : ℕ) (hk : 3 ≤ k) : qualifies (10 ^ k + 1) := by
    exact (classification _ (by have := hp.monotone hk; change 1001 ≤ _ at this; omega)).2
      ⟨k, hk, rfl⟩
  have hc (r : ℕ) : Nat.count qualifies (10 ^ (r + 3) + 1) = 20 + r := by
    induction r with
    | zero => exact count_first
    | succ r ih =>
      let a : ℕ := 10 ^ (r + 3) + 1
      let b : ℕ := 10 ^ (r + 4) + 1
      have hab : a + 1 ≤ b := hp (by omega : r + 3 < r + 4)
      have hgap : Nat.count qualifies (a + 1) = Nat.count qualifies b := by
        apply le_antisymm (Nat.count_monotone qualifies hab)
        by_contra! h
        obtain ⟨x, hx, hq⟩ := Nat.exists_of_count_lt_count h
        have hx₁ : a + 1 ≤ x := hx.1
        have hx₂ : x < b := hx.2
        have hmin : 1001 ≤ a := hp.monotone (by omega : 3 ≤ r + 3)
        obtain ⟨k, _, rfl⟩ := (classification x (by omega)).1 hq
        have hleft : r + 3 < k := hp.lt_iff_lt.mp (by omega : a < 10 ^ k + 1)
        have hright : k < r + 4 := hp.lt_iff_lt.mp hx₂
        omega
      change Nat.count qualifies b = 20 + (r + 1)
      rw [← hgap, Nat.count_succ_eq_succ_count (hterm (r + 3) (by omega))]
      omega
  intro n hn
  let r := n - 21
  have he : n - 18 = r + 3 := by dsimp [r]; omega
  have hi : n - 1 = 20 + r := by dsimp [r]; omega
  rw [hi, he, ← hc]
  exact Nat.nth_count (hterm _ (by omega))

end OMA229

theorem OMA.solution : type_of% @OMA.S_oeis_a229623.main :=
  OMA229.indexed_of_classification OMA229.classification
