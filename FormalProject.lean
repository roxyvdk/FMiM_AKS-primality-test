import Mathlib

open Polynomial
open Finset

inductive AKS_Output where
  | PRIME : AKS_Output
  | COMPOSITE : AKS_Output

export AKS_Output (PRIME COMPOSITE)

def perfect_power (n : ℕ) : Prop :=
  ∃ (a b : ℕ), b > 1 ∧ n = a ^ b

instance {n : ℕ} : Decidable (perfect_power n) := by
  sorry

noncomputable
def o_r (r n : ℕ) (h : n.gcd r = 1): ℕ :=
  -- the order of n in (ℤ/rℤ)ˣ
  orderOf (ZMod.unitOfCoprime n h : (ZMod r)ˣ)

noncomputable
def o_r' (r n : ℕ) : ℕ :=
  if h : n.gcd r = 1 then
    o_r r n h
  else
    0

noncomputable
def smallest_r (n : ℕ) : ℕ :=
  sInf {r : ℕ | o_r' r n > (Real.logb 2 n) ^ 2}

def is_not_coprime_in_range (r n : ℕ) : Prop :=
  ∃ a : ℕ, a ≤ r ∧ 1 < n.gcd a ∧ n.gcd a < n

instance {r n : ℕ} : Decidable (is_not_coprime_in_range r n) := by
  sorry

def polynomial_equality (r n a : ℕ) : Prop :=
  (((X + C (a : ℤ))^n : ℤ[X]) : ℤ[X] ⧸ Ideal.span ({X^r - 1, C (n : ℤ)} : Set ℤ[X])) = (X^n + C (a : ℤ) : ℤ[X])

def step_5_false (r n : ℕ) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ a ≤ Nat.floor (Real.sqrt r.totient * Real.logb 2 n) ∧ ¬polynomial_equality r n a

instance {r n : ℕ} : Decidable (step_5_false r n) := by
  sorry

noncomputable
def AKS_algorithm {n: ℕ} (ngt1 : 1 < n) : AKS_Output :=
  if perfect_power n ∨ is_not_coprime_in_range (smallest_r n) n ∨ (smallest_r n < n ∧ step_5_false (smallest_r n) n) then
    COMPOSITE
  else
    PRIME

lemma lem3_1 (n : ℕ) (hn : 7 ≤ n) : 4 ^ n ≤ (erase (range n) 0).lcm id := by
  sorry

lemma sublem_4_2_1 (n : ℕ) : n.prime → ¬ perfect_power n := by
  intro hp hpow
  unfold perfect_power at hpow
  rcases hpow with ⟨a, h₁⟩
  rcases h₁ with ⟨b, h₂⟩
  rcases h₂ with ⟨hb, hnpow⟩
  have bdivfact : ∀ c, b ∣ n.factorization c:= by
    intro c
    rw [hnpow, Nat.factorization_pow]
    norm_num
  have : n.factorization n = 1 := by
    rw [hp.factorization]
    simp
  have bdiv1: b ∣ 1 := by
    rw [← this]
    exact bdivfact n
  have : b = 1 := by
    simp at bdiv1
    exact bdiv1
  linarith

lemma sublem_4_2_2 (n : ℕ) : n.Prime → ¬ is_not_coprime_in_range (smallest_r n) n := by
  intro hp
  intro hcop
  unfold is_not_coprime_in_range at hcop
  rcases hcop with ⟨a,h₁⟩
  rcases h₁ with ⟨_,h₂⟩
  rcases h₂ with ⟨hgt1, hltn⟩

  have : n.gcd a = 1 := by
    have : ¬  n ∣ a := by
      intro ndiva
      have : n.gcd a = n := by exact Nat.gcd_eq_left ndiva
      linarith
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr this
  linarith

lemma sublem_4_2_3 (n : ℕ) : n.Prime → smallest_r n < n → ¬ step_5_false (smallest_r n) n := by
  unfold step_5_false
  intro hp hrbound hineq
  rcases hineq with ⟨a,ha⟩
  rcases ha with ⟨anonneg,hb⟩
  rcases hb with ⟨aupperb,ineq⟩
  -- have that polynomial_equality holds since n is prime (by lemma 2.1)
  -- linarith
  sorry

lemma lemma_4_2 (n : ℕ) (ngt1 : 1 < n) : n.Prime → AKS_algorithm ngt1 = PRIME := by
  intro hp
  unfold AKS_algorithm
  apply if_neg
  rw [or_iff_not_and_not]
  simp
  constructor
  · exact sublem_4_2_1 n hp
  · constructor
    · exact sublem_4_2_2 n hp
    · exact sublem_4_2_3 n hp

lemma lemma_4_3 (n : ℕ) (h : 2 ≤ n) :
    ∃ r : ℕ, r ≤ max 3 ⌈(Real.logb 2 n)^5⌉₊ ∧ multiplicativeOrder n r > (Real.logb 2 n)^2 := sorry
--lemma lemma_4_5
lemma lemma_4_9 (n : ℕ) (ngt1 : 1 < n) : AKS_algorithm ngt1 = PRIME → Nat.Prime n := sorry

theorem theorem_4_1 (n : ℕ) (ngt1 : 1 < n) : n.Prime ↔ AKS_algorithm ngt1 = PRIME := by
  constructor
  exact lemma_4_2 n ngt1
  exact lemma_4_9 n ngt1



namespace Lemma78

open Real
-- `p` is a prime divisor of `n` such that `o_r(p) > 1` (also `p > r` and `gcd(n, r) = 1`)
--
noncomputable
def q_r (r p : ℕ) := cyclotomic r (ZMod p)

lemma q_r_not_unit {r : ℕ} (rgt0 : 0 < r) (p : ℕ) [Fact (Nat.Prime p)] : ¬IsUnit (q_r r p) := by
  apply not_isUnit_of_degree_pos
  exact degree_cyclotomic_pos r _ rgt0

noncomputable
def h_def (r p : ℕ) [Fact (Nat.Prime p)] : (ZMod p)[X] :=
  (q_r r p).factor

def h_irr (r p : ℕ) [Fact (Nat.Prime p)] : Fact (Irreducible (h_def r p)) := by
  apply fact_irreducible_factor

noncomputable
def ell (r n : ℕ) : ℕ :=
  Nat.floor (Real.sqrt r.totient * logb 2 n)

lemma deg_cyclotomic_factor_eq_order (r p : ℕ) (p_prime : p.Prime) (hr : 1 < o_r' r p) {g : (ZMod p)[X]}
    (hg : Irreducible g ∧ g ∣ q_r r p) : g.degree = o_r' r p := by
  -- apply (degree_eq_iff_natDegree_eq_of_pos (Nat.zero_lt_of_lt hr)).mpr
  sorry

lemma deg_h_gt_one (r p : ℕ) [pf : Fact (Nat.Prime p)] (rgt0 : 0 < r) (hrp : 1 < o_r' r p) : 1 < (h_def r p).degree := by
  have p_prime : p.Prime := pf.out
  have hg : Irreducible (h_def r p) ∧ (h_def r p) ∣ (q_r r p) := by
    constructor
    · apply irreducible_factor
    · apply factor_dvd_of_degree_ne_zero
      symm
      refine (lt_iff_le_and_ne.mp ?_).right
      unfold q_r
      apply degree_cyclotomic_pos r _ rgt0
  rw [deg_cyclotomic_factor_eq_order r p p_prime hrp hg]
  exact_mod_cast hrp

noncomputable
instance {r p : ℕ} [Fact (Nat.Prime p)] : Field (AdjoinRoot (h_def r p)) := by
  have := h_irr r p
  exact AdjoinRoot.instField

lemma h_not_zero (r p : ℕ) [Fact (Nat.Prime p)] : h_def r p ≠ 0 :=
  Irreducible.ne_zero (irreducible_factor (q_r r p))

lemma x_plus_a_is_unit (r p a : ℕ) [Fact (Nat.Prime p)] (rgt0 : 0 < r) (hrp : 1 < o_r' r p) :
    IsUnit (AdjoinRoot.mk (h_def r p) (X + C (a : ZMod p))) := by
  apply Ne.isUnit
  intro h
  apply AdjoinRoot.mk_eq_zero.mp at h
  have deg_le_one : (h_def r p).degree ≤ (X + C (a : ZMod p) : (ZMod p)[X]).degree :=
    degree_le_of_dvd h (X_add_C_ne_zero (a : ZMod p))
  rw [degree_X_add_C (a : ZMod p)] at deg_le_one
  have one_lt_deg := deg_h_gt_one r p rgt0 hrp
  rw [degree_eq_natDegree (h_not_zero r p)] at deg_le_one
  rw [degree_eq_natDegree (h_not_zero r p)] at one_lt_deg
  have : (1 : ℕ) < 1 := by
    calc
      (1 : ℕ) < (h_def r p).natDegree := by exact_mod_cast one_lt_deg
      _ ≤ 1 := by exact_mod_cast deg_le_one
  contradiction

def normal_g (r n p : ℕ) (hn : n.gcd r = 1) (hp : p.gcd r = 1) : Subgroup (ZMod r)ˣ :=
  Subgroup.closure {ZMod.unitOfCoprime n hn, ZMod.unitOfCoprime p hp}

noncomputable
def t_def (r n p : ℕ) (hn : n.gcd r = 1) (hp : p.gcd r = 1) : ℕ :=
  Nat.card (normal_g r n p hn hp)

noncomputable
def big_g (r n p : ℕ) [Fact (Nat.Prime p)] (rgt0 : 0 < r) (hrp : 1 < o_r' r p) : Subgroup (AdjoinRoot (h_def r p))ˣ :=
  Subgroup.closure ((fun (i : ℕ) => (IsUnit.unit' (x_plus_a_is_unit r p i rgt0 hrp) : (AdjoinRoot (h_def r p))ˣ))'' (range (ell r n)))

noncomputable
def big_g' (n : ℕ) {r p : ℕ} (p_prime : p.Prime) (rgt0 : 0 < r) (hrp : 1 < o_r' r p) :=
  @big_g r n p ⟨p_prime⟩ rgt0 hrp

def power_of_p (n p : ℕ) : Prop :=
  ∃ k, p ^ k = n

lemma lemma_4_7 (r n p : ℕ) (p_prime : p.Prime) (rgt0 : 0 < r) (hrp : 1 < o_r' r p) (hn : n.gcd r = 1) (hp : p.gcd r = 1) :
    Nat.card (big_g' n p_prime rgt0 hrp) ≥ (t_def r n p hn hp + ell r n).choose (t_def r n p hn hp - 1) := by
  sorry

lemma lemma_4_8 (r n p : ℕ) (p_prime : p.Prime) (rgt0 : 0 < r) (hrp : 1 < o_r' r p) (hn : n.gcd r = 1) (hp : p.gcd r = 1) (not_p_power : ¬power_of_p n p):
    Nat.card (big_g' n p_prime rgt0 hrp) ≤ (n : ℝ) ^ (sqrt (t_def r n p hn hp)) := by
  sorry

end Lemma78

