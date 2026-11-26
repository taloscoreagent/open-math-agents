import OMAStatements.S_oeis_a108629

/-!
A proof of R. J. Mathar's order-five recurrence for OEIS A108629.
The square root in the defining generating function gives a quadratic
equation. Differentiate it and eliminate the quadratic term to obtain a
linear differential equation, then compare the coefficients of degree n - 1.
Mathar's general recurrence theorem for radical generating functions also
applies to this family (arXiv:2109.02112, Theorem 5).
-/

namespace OMA108

open PowerSeries OMA.S_oeis_a108629

/-- Squaring the binomial series selects the prescribed radicand. -/
theorem square_root_identity : rootSeries ^ 2 = 1 + radicandTail := by
  have hs : HasSubst radicandTail := HasSubst.of_constantCoeff_zero' (by simp [radicandTail])
  have h : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + (X : PowerSeries ℚ) := by
    rw [pow_two, ← binomialSeries_add]
    have h1 : (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) := by norm_num
    rw [h1, binomialSeries_nat, pow_one]
  calc
    rootSeries ^ 2 = subst radicandTail ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2) :=
      (subst_pow hs _ 2).symm
    _ = 1 + radicandTail := by
      rw [h, ← coe_substAlgHom hs, map_add, map_one, substAlgHom_X hs]

/-- Clearing the denominator and squaring gives the defining quadratic. -/
theorem defining_equation :
    (1 + X + X ^ 2) * series ^ 2 - (1 + X) * series + X = 0 := by
  let B : PowerSeries ℚ := 1 + X + X ^ 2
  have hb : constantCoeff (2 * B) ≠ 0 := by
    simp [B, map_ofNat]
  have hF : (2 * B) * series = 1 + X - rootSeries := by
    unfold series
    change (2 * B) * ((1 + X - rootSeries) * (2 * B)⁻¹) = _
    rw [mul_left_comm, PowerSeries.mul_inv_cancel _ hb, mul_one]
  have hS : rootSeries = 1 + X - 2 * B * series := by linear_combination hF
  have hs := square_root_identity
  rw [hS] at hs
  have hB : B ≠ 0 := by
    intro hz
    simp [hz] at hb
  have hz : (4 * B) * (B * series ^ 2 - (1 + X) * series + X) = 0 := by
    dsimp [B, radicandTail] at hs ⊢
    linear_combination hs
  have h4 : (4 : PowerSeries ℚ) ≠ 0 := by
    intro h4z
    have hc := congrArg (constantCoeff (R := ℚ)) h4z
    norm_num [map_ofNat] at hc
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero h4 hB)

/-- Eliminate the quadratic term from the equation and its derivative. -/
theorem quadratic_ode (F : PowerSeries ℚ)
    (h : (1 + X + X ^ 2) * F ^ 2 - (1 + X) * F + X = 0) :
    (1 - X - 4 * X ^ 2 - 9 * X ^ 3 - 7 * X ^ 4 - 4 * X ^ 5) * derivative ℚ F =
      (-2 - 4 * X - 3 * X ^ 2 + X ^ 3 + 2 * X ^ 4) * F +
        (1 + X + 3 * X ^ 2 + X ^ 3) := by
  have hd := congrArg (derivative ℚ) h
  simp only [map_add, map_sub, Derivation.leibniz, derivative_pow, derivative_one,
    derivative_X, map_zero, smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one, zero_add] at hd
  linear_combination
    (1 + X + X ^ 2) * (2 * (1 + X + X ^ 2) * F - (1 + X)) * hd -
    (4 * (1 + X + X ^ 2) ^ 2 * derivative ℚ F +
      (2 * (1 + X + X ^ 2) * F - (1 + X)) * (1 + 2 * X) +
      2 * (2 * X + X ^ 2)) * h

/-- At degree k + 5, the cubic inhomogeneous term vanishes. -/
theorem recurrence_of_ode (F : PowerSeries ℚ)
    (h : (1 - X - 4 * X ^ 2 - 9 * X ^ 3 - 7 * X ^ 4 - 4 * X ^ 5) * derivative ℚ F =
      (-2 - 4 * X - 3 * X ^ 2 + X ^ 3 + 2 * X ^ 4) * F +
        (1 + X + 3 * X ^ 2 + X ^ 3)) (k : ℕ) :
    ((k : ℚ) + 6) * coeff (k + 6) F =
      ((k : ℚ) + 3) * coeff (k + 5) F +
      4 * ((k : ℚ) + 3) * coeff (k + 4) F +
      3 * (3 * (k : ℚ) + 8) * coeff (k + 3) F +
      (7 * (k : ℚ) + 15) * coeff (k + 2) F +
      2 * (2 * (k : ℚ) + 3) * coeff (k + 1) F := by
  have hc := congrArg (coeff (R := ℚ) (k + 5)) h
  have scale (c n : ℕ) (G : PowerSeries ℚ) :
      coeff n ((c : PowerSeries ℚ) * G) = (c : ℚ) * coeff n G := by
    simpa only [nsmul_eq_mul] using map_nsmul (coeff (R := ℚ) n) c G
  have scaleNum (c : ℕ) [c.AtLeastTwo] (n : ℕ) (G : PowerSeries ℚ) :
      coeff n (ofNat(c) * G) = (ofNat(c) : ℚ) * coeff n G := scale c n G
  simp only [sub_mul, add_mul, neg_mul, mul_assoc, one_mul, map_add, map_sub, map_neg,
    scaleNum] at hc
  have shift (g : PowerSeries ℚ) :
      coeff (k + 5) (X * g) = coeff (k + 4) g := by
    simpa only [pow_one] using coeff_X_pow_mul g 1 (k + 4)
  simp only [shift, coeff_X_pow_mul', coeff_derivative, coeff_one, coeff_X_pow, coeff_X,
    if_pos (show 2 ≤ k + 5 by omega), if_pos (show 3 ≤ k + 5 by omega),
    if_pos (show 4 ≤ k + 5 by omega), if_pos (show 5 ≤ k + 5 by omega),
    if_neg (show ¬ k + 5 = 0 by omega), if_neg (show ¬ k + 5 = 1 by omega),
    if_neg (show ¬ k + 5 = 2 by omega), if_neg (show ¬ k + 5 = 3 by omega),
    show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega,
    show k + 5 - 4 = k + 1 by omega, show k + 5 - 5 = k by omega,
    Nat.cast_add, Nat.cast_ofNat] at hc
  linear_combination hc

end OMA108

theorem OMA.solution : type_of% @OMA.S_oeis_a108629.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have h := OMA108.recurrence_of_ode OMA.S_oeis_a108629.series
    (OMA108.quadratic_ode _ OMA108.defining_equation) k
  unfold OMA.S_oeis_a108629.a
  simp only [Nat.cast_add, Nat.cast_ofNat]
  simp only [show (k + 6 - 1) = k + 5 by omega, show (k + 6 - 2) = k + 4 by omega,
    show (k + 6 - 3) = k + 3 by omega, show (k + 6 - 4) = k + 2 by omega,
    show (k + 6 - 5) = k + 1 by omega]
  linear_combination h
