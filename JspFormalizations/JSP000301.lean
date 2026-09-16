import JspFormalizations.Prime

/-!
# JSP-000301

If two consecutive positive integers are powerful, must at least one be a square?

No. Witness: 12167 = 23³ and 12168 = 2³ · 3² · 13² (Golomb / Walker / Guy).
Mathematical discovery remains classical; this file independently checks the witness.
-/

namespace JSP000301

open Jsp

theorem three_prime : IsPrime 3 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have : d < 4 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)
  have hfin : ∀ x : Fin 4, x.val ∣ 3 → x.val = 1 ∨ x.val = 3 := by decide
  exact hfin ⟨d, this⟩ hd

theorem thirteen_prime : IsPrime 13 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have : d < 14 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)
  have hfin : ∀ x : Fin 14, x.val ∣ 13 → x.val = 1 ∨ x.val = 13 := by decide
  exact hfin ⟨d, this⟩ hd

theorem twenty_three_prime : IsPrime 23 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have : d < 24 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)
  have hfin : ∀ x : Fin 24, x.val ∣ 23 → x.val = 1 ∨ x.val = 23 := by decide
  exact hfin ⟨d, this⟩ hd

theorem euclid {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  obtain ⟨k1, k2, hk1, hk2, heq⟩ := Nat.dvd_mul.mp h
  have hk1p : k1 ∣ p := ⟨k2, by omega⟩
  cases hp.2 k1 hk1p with
  | inl h1 =>
    subst h1
    have : k2 = p := by omega
    subst this
    exact Or.inr hk2
  | inr hp1 =>
    subst hp1
    exact Or.inl hk1

theorem eq_12167 : (23 : Nat) ^ 3 = 12167 := by decide
theorem eq_12168 : (2 : Nat) ^ 3 * 3 ^ 2 * 13 ^ 2 = 12168 := by decide
theorem consecutive : 12167 + 1 = 12168 := by decide

theorem not_square_12167 : ¬ IsSquare 12167 :=
  not_square_of_between (a := 110) (by decide) (by decide)

theorem not_square_12168 : ¬ IsSquare 12168 :=
  not_square_of_between (a := 110) (by decide) (by decide)

theorem prime_dvd_pow {p k : Nat} (hp : IsPrime p) {q : Nat} (hq : IsPrime q)
    (h : q ∣ p ^ k) : q = p := by
  induction k with
  | zero =>
    have : q ∣ 1 := by simpa [Nat.pow_zero] using h
    have : q ≤ 1 := Nat.le_of_dvd (by decide) this
    have : 2 ≤ q := hq.1
    omega
  | succ k ih =>
    have : q ∣ p ^ k * p := by
      simpa [Nat.pow_succ, Nat.mul_comm] using h
    cases euclid hq this with
    | inl hpow => exact ih hpow
    | inr hpdiv =>
      have : q = 1 ∨ q = p := hp.2 q hpdiv
      cases this with
      | inl h1 =>
        have : 2 ≤ q := hq.1
        omega
      | inr heq => exact heq

theorem powerful_pow_prime {p k : Nat} (hp : IsPrime p) (hk : 2 ≤ k) :
    Powerful (p ^ k) := by
  have ppos : 0 < p := Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 2) hp.1)
  refine ⟨Nat.pow_pos ppos, ?_⟩
  intro q hq hd
  have hqeq : q = p := prime_dvd_pow hp hq hd
  rw [hqeq]
  refine ⟨p ^ (k - 2), ?_⟩
  have hkeq : k - 2 + 2 = k := Nat.sub_add_cancel hk
  calc
    p ^ k = p ^ (k - 2 + 2) := by rw [hkeq]
    _ = p ^ (k - 2) * p ^ 2 := Nat.pow_add _ _ _
    _ = p ^ 2 * p ^ (k - 2) := Nat.mul_comm _ _

theorem powerful_12167 : Powerful 12167 := by
  have : Powerful (23 ^ 3) := powerful_pow_prime twenty_three_prime (by decide)
  simpa [eq_12167] using this

theorem prime_dvd_12168 {q : Nat} (hq : IsPrime q) (hd : q ∣ 12168) :
    q = 2 ∨ q = 3 ∨ q = 13 := by
  have : q ∣ (2 ^ 3) * ((3 ^ 2) * (13 ^ 2)) := by
    simpa [eq_12168, Nat.mul_assoc] using hd
  cases euclid hq this with
  | inl h8 =>
    exact Or.inl (prime_dvd_pow two_prime hq h8)
  | inr hrest =>
    cases euclid hq hrest with
    | inl h9 =>
      exact Or.inr (Or.inl (prime_dvd_pow three_prime hq h9))
    | inr h169 =>
      exact Or.inr (Or.inr (prime_dvd_pow thirteen_prime hq h169))

theorem powerful_12168 : Powerful 12168 := by
  refine ⟨by decide, ?_⟩
  intro p hp hd
  rcases prime_dvd_12168 hp hd with h | h | h
  · subst h; decide
  · subst h; decide
  · subst h; decide

/-- **JSP-000301 (disproof).** Consecutive powerful nonsquares exist. -/
theorem theorem_jsp_000301 :
    ∃ n : Nat, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  refine ⟨12167, by decide, powerful_12167, ?_, not_square_12167, ?_⟩
  · simpa [consecutive] using powerful_12168
  · simpa [consecutive] using not_square_12168

end JSP000301
