import Mathlib

open Polynomial

inductive AKS_Output where
  | PRIME : AKS_Output
  | COMPOSITE : AKS_Output

export AKS_Output (PRIME COMPOSITE)

def perfect_power (n : ℕ) : Prop :=
  ∃ (a b : ℕ), b > 1 ∧ n = a ^ b

instance {n : ℕ} : Decidable (perfect_power n) := by
  sorry

def o_r (r n : ℕ) (h : gcd r n = 1): ℕ :=
  -- the order of n in (ℤ/rℤ)ˣ
  sorry

def o_r' (r n : ℕ) : ℕ :=
  if h : gcd r n = 1 then
    o_r r n h
  else
    0

noncomputable
def smallest_r (n : ℕ) : ℕ :=
  sInf {r : ℕ | o_r' r n > (Real.log n) ^ 2}

def is_not_coprime_in_range (r n : ℕ) : Prop :=
  ∃ a : ℕ, a ≤ r ∧ 1 < gcd a n ∧ gcd a n < n

instance {r n : ℕ} : Decidable (is_not_coprime_in_range r n) := by
  sorry

def polynomial_equality (r n a : ℕ) : Prop :=
  (((X + C (a : ℤ))^n : ℤ[X]) : ℤ[X] ⧸ Ideal.span ({X^r - 1, C (n : ℤ)} : Set ℤ[X])) = (X^n + C (a : ℤ) : ℤ[X])

def step_5_false (r n : ℕ) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ a ≤ Nat.floor (Real.sqrt r.totient * Real.log n) ∧ ¬polynomial_equality r n a

instance {r n : ℕ} : Decidable (step_5_false r n) := by
  sorry

noncomputable
def AKS_algorithm {n: ℕ} (ngt1 : 1 < n) : AKS_Output :=
  if perfect_power n ∨ is_not_coprime_in_range (smallest_r n) n ∨ (smallest_r n < n ∧ step_5_false (smallest_r n) n) then
    COMPOSITE
  else
    PRIME

theorem theorem_4_1 (n : ℕ) (ngt1 : 1 < n) : n.Prime ↔ AKS_algorithm ngt1 = PRIME := by
  sorry
