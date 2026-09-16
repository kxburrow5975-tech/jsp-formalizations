import JspFormalizations.Prime

/-!
# JSP-000307

Can three consecutive integers have strictly decreasing largest prime factors?

Yes. Witness: 14, 15, 16 with largest prime factors 7, 5, 2.
This matches the catalog wording as currently published. Infinitude
(Erdős problem #372 / Balog) is out of scope of this file.
-/

namespace JSP000307

open Jsp

theorem three_prime : IsPrime 3 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have : d < 4 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)
  have hfin : ∀ x : Fin 4, x.val ∣ 3 → x.val = 1 ∨ x.val = 3 := by decide
  exact hfin ⟨d, this⟩ hd

theorem five_prime : IsPrime 5 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have : d < 6 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)
  have hfin : ∀ x : Fin 6, x.val ∣ 5 → x.val = 1 ∨ x.val = 5 := by decide
  exact hfin ⟨d, this⟩ hd

theorem seven_prime : IsPrime 7 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have : d < 8 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)
  have hfin : ∀ x : Fin 8, x.val ∣ 7 → x.val = 1 ∨ x.val = 7 := by decide
  exact hfin ⟨d, this⟩ hd

theorem dvd_14 {d : Nat} (h : d ∣ 14) :
    d = 1 ∨ d = 2 ∨ d = 7 ∨ d = 14 := by
  have : d < 15 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) h)
  have hfin : ∀ x : Fin 15, x.val ∣ 14 →
      x.val = 1 ∨ x.val = 2 ∨ x.val = 7 ∨ x.val = 14 := by decide
  exact hfin ⟨d, this⟩ h

theorem dvd_15 {d : Nat} (h : d ∣ 15) :
    d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 15 := by
  have : d < 16 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) h)
  have hfin : ∀ x : Fin 16, x.val ∣ 15 →
      x.val = 1 ∨ x.val = 3 ∨ x.val = 5 ∨ x.val = 15 := by decide
  exact hfin ⟨d, this⟩ h

theorem dvd_16 {d : Nat} (h : d ∣ 16) :
    d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 ∨ d = 16 := by
  have : d < 17 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) h)
  have hfin : ∀ x : Fin 17, x.val ∣ 16 →
      x.val = 1 ∨ x.val = 2 ∨ x.val = 4 ∨ x.val = 8 ∨ x.val = 16 := by decide
  exact hfin ⟨d, this⟩ h

theorem not_prime_1 : ¬ IsPrime 1 := fun h => Nat.not_succ_le_self 1 h.1

theorem not_prime_4 : ¬ IsPrime 4 := by
  intro h
  cases h.2 2 (by decide : 2 ∣ 4) with
  | inl h1 => exact (by decide : ¬ (2 = 1)) h1
  | inr h4 => exact (by decide : ¬ (2 = 4)) h4

theorem not_prime_8 : ¬ IsPrime 8 := by
  intro h
  cases h.2 2 (by decide : 2 ∣ 8) with
  | inl h1 => exact (by decide : ¬ (2 = 1)) h1
  | inr h8 => exact (by decide : ¬ (2 = 8)) h8

theorem not_prime_14 : ¬ IsPrime 14 := by
  intro h
  cases h.2 2 (by decide : 2 ∣ 14) with
  | inl h1 => exact (by decide : ¬ (2 = 1)) h1
  | inr h14 => exact (by decide : ¬ (2 = 14)) h14

theorem not_prime_15 : ¬ IsPrime 15 := by
  intro h
  cases h.2 3 (by decide : 3 ∣ 15) with
  | inl h1 => exact (by decide : ¬ (3 = 1)) h1
  | inr h15 => exact (by decide : ¬ (3 = 15)) h15

theorem not_prime_16 : ¬ IsPrime 16 := by
  intro h
  cases h.2 2 (by decide : 2 ∣ 16) with
  | inl h1 => exact (by decide : ¬ (2 = 1)) h1
  | inr h16 => exact (by decide : ¬ (2 = 16)) h16

theorem lpf_14 : LargestPrimeFactor 14 7 := by
  refine ⟨seven_prime, by decide, ?_⟩
  intro q hq hd
  rcases dvd_14 hd with h | h | h | h
  · exact False.elim (not_prime_1 (by simpa [h] using hq))
  · subst h; decide
  · subst h; decide
  · exact False.elim (not_prime_14 (by simpa [h] using hq))

theorem lpf_15 : LargestPrimeFactor 15 5 := by
  refine ⟨five_prime, by decide, ?_⟩
  intro q hq hd
  rcases dvd_15 hd with h | h | h | h
  · exact False.elim (not_prime_1 (by simpa [h] using hq))
  · subst h; decide
  · subst h; decide
  · exact False.elim (not_prime_15 (by simpa [h] using hq))

theorem lpf_16 : LargestPrimeFactor 16 2 := by
  refine ⟨two_prime, by decide, ?_⟩
  intro q hq hd
  rcases dvd_16 hd with h | h | h | h | h
  · exact False.elim (not_prime_1 (by simpa [h] using hq))
  · subst h; decide
  · exact False.elim (not_prime_4 (by simpa [h] using hq))
  · exact False.elim (not_prime_8 (by simpa [h] using hq))
  · exact False.elim (not_prime_16 (by simpa [h] using hq))

/-- **JSP-000307.** Three consecutive positive integers with strictly
decreasing largest prime factors exist. Witness: 14, 15, 16. -/
theorem theorem_jsp_000307 :
    ∃ n p q r : Nat,
      LargestPrimeFactor n p ∧
      LargestPrimeFactor (n + 1) q ∧
      LargestPrimeFactor (n + 2) r ∧
      r < q ∧ q < p := by
  refine ⟨14, 7, 5, 2, lpf_14, ?_, ?_, by decide, by decide⟩
  · simpa using lpf_15
  · simpa using lpf_16

end JSP000307
