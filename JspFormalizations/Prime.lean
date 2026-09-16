/- Independent Lean 4 core lemmas. No Mathlib. No sorry. -/

namespace Jsp

def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def IsSquare (n : Nat) : Prop := ∃ k : Nat, k * k = n

/-- Equivalent characterization used by the JSP-000301 catalog note:
every prime divisor has exponent at least two. -/
def Powerful (n : Nat) : Prop :=
  0 < n ∧ ∀ p : Nat, IsPrime p → p ∣ n → p ^ 2 ∣ n

def LargestPrimeFactor (n p : Nat) : Prop :=
  IsPrime p ∧ p ∣ n ∧ ∀ q : Nat, IsPrime q → q ∣ n → q ≤ p

theorem not_square_of_between {n a : Nat}
    (h1 : a * a < n) (h2 : n < (a + 1) * (a + 1)) :
    ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  cases Nat.lt_or_ge k (a + 1) with
  | inl hlt =>
    have : k ≤ a := Nat.lt_succ_iff.mp hlt
    have : k * k ≤ a * a := Nat.mul_le_mul this this
    omega
  | inr hge =>
    have : (a + 1) * (a + 1) ≤ k * k := Nat.mul_le_mul hge hge
    omega

theorem two_prime : IsPrime 2 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have : d ≤ 2 := Nat.le_of_dvd (by decide) hd
  have : d < 3 := Nat.lt_succ_of_le this
  have hfin : ∀ x : Fin 3, x.val ∣ 2 → x.val = 1 ∨ x.val = 2 := by decide
  exact hfin ⟨d, this⟩ hd

end Jsp
