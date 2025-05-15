import Mathlib

open Polynomial
open Finset
open Real

inductive AKS_Output where
  | PRIME : AKS_Output
  | COMPOSITE : AKS_Output

export AKS_Output (PRIME COMPOSITE)

def perfect_power (n : ℕ) : Prop :=
  ∃ (a b : ℕ), b > 1 ∧ n = a ^ b

noncomputable
instance {n : ℕ} : Decidable (perfect_power n) := by
  apply Classical.propDecidable

/-- The order of n in `(ℤ/rℤ)ˣ`.-/
noncomputable def oᵣ (r n : ℕ) : ℕ :=
  orderOf (n : ZMod r)

noncomputable
def smallest_r (n : ℕ) : ℕ :=
  sInf {r : ℕ | oᵣ r n > (logb 2 n) ^ 2}

def is_not_coprime_in_range (r n : ℕ) : Prop :=
  ∃ a : ℕ, a ≤ r ∧ 1 < n.gcd a ∧ n.gcd a < n

noncomputable
instance {r n : ℕ} : Decidable (is_not_coprime_in_range r n) := by
  apply Classical.propDecidable

def polynomial_equality (r n a : ℕ) : Prop :=
  (((X + C (a : ℤ))^n : ℤ[X]) : ℤ[X] ⧸ Ideal.span ({X^r - 1, C (n : ℤ)} : Set ℤ[X])) = (X^n + C (a : ℤ) : ℤ[X])

def polynomial_equality' (r n a : ℕ) : Prop :=
  AdjoinRoot.mk (X^r - C (1 : ZMod n)) (X + C (a : ZMod n))^n = AdjoinRoot.mk (X^r - C (1 : ZMod n)) (X^n + C (a : ZMod n))

def step_5_false (r n : ℕ) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ a ≤ Nat.floor (Real.sqrt r.totient * logb 2 n) ∧ ¬polynomial_equality r n a

noncomputable
instance {r n : ℕ} : Decidable (step_5_false r n) := by
  apply Classical.propDecidable

noncomputable
def AKS_algorithm (n: ℕ) : AKS_Output :=
  if perfect_power n ∨ is_not_coprime_in_range (smallest_r n) n ∨ (smallest_r n < n ∧ step_5_false (smallest_r n) n) then
    COMPOSITE
  else
    PRIME

lemma C_power {R : Type*} [Semiring R] (a : R) (n : ℕ) : C (a ^ n) = (C a) ^ n := by
  induction n with
  | zero => simp [pow_zero]  -- Base case
  | succ d hd =>             -- Inductive step
    rw [pow_succ, pow_succ, C_mul, hd]
-- still a work in progress
lemma lemma_2_1 (n : ℕ) (a : ℤ) (hn : 2 ≤ n) :
    Nat.Prime n ↔ (X + C (a : ZMod n)) ^ n = X ^ n + C (a : ZMod n) := by
  constructor
  intro hprime
  haveI : Fact (Nat.Prime n) := ⟨hprime⟩
  have hchar : ExpChar (ZMod n) n := by
    apply ExpChar.prime
    exact hprime
  -- Apply the add_pow_expChar lemma
  rw [add_pow_expChar]
  have h_const : (C (a : ZMod n)) ^ n = C (a : ZMod n) := by
    rw [ ← C_power, Polynomial.C_inj, ZMod.pow_card]
   -- ZMod.pow_card a
   
  -- Replace the constant term with the simplified form
  rw [h_const]


-- ← 
  let f:= (X+C (a: ZMod n))^n
  let g:= X^n + C (a: ZMod n)
-- f-g = (n choose k)
  
  let q := Nat.minFac n 
  let k:= n.factorization q
--simp[nat.minFac_dvd, Nat.not_prime_iff_minFac_lt]
  have hlt : q < n := by
    rw[hnotprime, Nat.not_prime_iff_minFac]
  have hpow : q ^ k ∣ n :=by 
    apply pow_multiplicity_dvd_factorization
  have hmult : multiplicity q (Nat.choose n q) = multiplicity q n - multiplicity q q -
  multiplicity q (n - q)
  apply  Nat.Prime_multiplicity_choose_aux q n q hq (Nat.zero_lt_of_lt hlt) hlt

  have coeff_q_zero : (Nat.choose n q : ZMod n) = 0 := by
      have := congr_arg (fun P => coeff P q) (hpoly)
      simp [coeff_add, coeff_sub, coeff_X_pow, coeff_C, coeff_add_pow,
            if_neg (ne_of_lt hlt).symm, sub_eq_zero] at this
      exact this
    
  have coeff_q_zero : (Nat.choose n q : ZMod n) = 0 := by
      have := congr_arg (fun P => coeff P q) (hpoly)
      simp [coeff_add, coeff_sub, coeff_X_pow, coeff_C, coeff_add_pow
            if_neg (ne_of_lt hlt).symm, sub_eq_zero] at this
      exact this
    


lemma lem3_1 (n : ℕ) (hn : 7 ≤ n) : 4 ^ n ≤ (erase (range n) 0).lcm id := by
  sorry

lemma sublem_4_2_1 (n : ℕ) : n.Prime → ¬ perfect_power n := by
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

lemma lemma_4_2 (n : ℕ) : n.Prime → AKS_algorithm n = PRIME := by
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
    ∃ r : ℕ, r ≤ max 3 ⌈(logb 2 n)^5⌉₊ ∧ oᵣ r n > (logb 2 n)^2 := sorry

def introspective (m r p: ℕ) (f : ℤ[X]) : Prop :=
    ((f ^ m : ℤ[X]) : ℤ[X] ⧸ Ideal.span ({X^r - 1, C (p : ℤ)} : Set ℤ[X]))
        = (f.comp (Polynomial.X ^ m) : ℤ[X] ⧸ Ideal.span ({X^r - 1, C (p : ℤ)} : Set ℤ[X]))

lemma quot_prod (f g q r : ℤ[X]) (p : ℕ) (_ : Nat.Prime p) (q_dvd_r : q ∣ r) :
  ((f : ℤ[X]) : ℤ[X] ⧸ Ideal.span ({r, C (p : ℤ)} : Set ℤ[X])) = (g : ℤ[X]) → ((f : ℤ[X]) : ℤ[X] ⧸ Ideal.span ({q, C (p : ℤ)} : Set ℤ[X])) = (g : ℤ[X]) := by
  intro hr
  rw [Ideal.Quotient.eq] at *
  rw [Ideal.mem_span_pair] at *
  rw [dvd_def] at q_dvd_r
  obtain ⟨c, q_dvd_r⟩ := q_dvd_r
  obtain ⟨a,b,hr⟩ := hr
  rw [q_dvd_r, mul_comm q c, ← mul_assoc] at hr
  use (a * c), b

lemma introspec_pow (m r p : ℕ) (f : ℤ[X]) : (introspective m r p f) → ∀ q : ℕ,
  (((f.comp (Polynomial.X ^ q))^ m : ℤ[X]) : ℤ[X] ⧸ Ideal.span ({X^(q*r) - 1, C (p : ℤ)} : Set ℤ[X]))
    = (f.comp (Polynomial.X ^ (m*q)) : ℤ[X]) := by
  intro hm q
  unfold introspective at *
  rw [pow_mul, mul_comm, pow_mul]
  sorry

lemma lemma_4_5 (m m' r p : ℕ) (pprime : Nat.Prime p) (f : ℤ[X]) (hm : introspective m r p f) (hm' : introspective m' r p f) : introspective (m * m') r p f := by
  have hmm' : ((f.comp (Polynomial.X ^ m) ^ m' : ℤ[X]) : ℤ[X] ⧸ Ideal.span ({X^(m * r) - 1, C (p : ℤ)} : Set ℤ[X]))
      = (f.comp (Polynomial.X ^ (m' * m) : ℤ[X])) := by
      simp at *
      exact introspec_pow m' r p f hm' m
  unfold introspective at *
  simp at *
  rw [pow_mul,hm]
  have xr_dvd_xmr : ((X ^ r + C (-1 : ℤ)) : ℤ[X]) ∣ ((X^(m * r) + C (-1 : ℤ)) : ℤ[X]) := by
    let f : ℤ[X] := X ^ r - 1
    let g : ℤ[X] := ∑ i ∈ Finset.range m, X ^ (i * r)
    have : f * g = X ^ (m * r) + C (-1) := by
      simp only [f, g, ← C_1, ← sub_eq_add_neg]
      have : (∑ i ∈ Finset.range m, (X : ℤ[X]) ^ (i * r)) = (∑ i ∈ Finset.range m, (X ^ r) ^ i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_mul]
        ring
      simp
      rw [this, mul_geom_sum, ← pow_mul, mul_comm]
      simp [Mathlib.Tactic.RingNF.add_neg]
    use g
    simp [Mathlib.Tactic.RingNF.add_neg] at *
    rw [← this]
  simp [Mathlib.Tactic.RingNF.add_neg] at xr_dvd_xmr
  apply quot_prod _ _ _ _ p pprime xr_dvd_xmr at hmm'
  rw [mul_comm m m']
  simp [← hmm']

lemma lemma_4_6 (m r p : ℕ) (_ : Nat.Prime p) (f g : ℤ[X]) (hmf : introspective m r p f) (hmg : introspective m r p g) : introspective m r p (f * g) := by
  unfold introspective at *
  simp [mul_pow, ← hmf, ← hmg]

lemma lemma_4_9 (n : ℕ) (ngt1 : 1 < n) : AKS_algorithm n = PRIME → Nat.Prime n := sorry

theorem theorem_4_1 (n : ℕ) (ngt1 : 1 < n) : n.Prime ↔ AKS_algorithm n = PRIME := by
  constructor
  exact lemma_4_2 n ngt1
  exact lemma_4_9 n ngt1



namespace Lemma78

structure Step5Assumptions where
  r : ℕ
  n : ℕ
  p : ℕ
  rgt0 : 0 < r
  hrp : 1 < oᵣ r p
  hn : n.gcd r = 1
  pgtr : r < p
  p_prime : p.Prime
  hp : p.gcd r = 1

section

variable (sa : Step5Assumptions)

noncomputable
def q_r := cyclotomic sa.r (ZMod sa.p)

lemma q_r_not_unit [Fact (Nat.Prime sa.p)] : ¬IsUnit (q_r sa) := by
  apply not_isUnit_of_degree_pos
  exact degree_cyclotomic_pos sa.r _ sa.rgt0

noncomputable
def h_def [Fact (Nat.Prime sa.p)] : (ZMod sa.p)[X] :=
  (q_r sa).factor

def h_irr [Fact (Nat.Prime sa.p)] : Fact (Irreducible (h_def sa)) := by
  apply fact_irreducible_factor

noncomputable
def ell : ℕ :=
  Nat.floor (Real.sqrt sa.r.totient * logb 2 sa.n)

lemma deg_cyclotomic_factor_eq_order {g : (ZMod sa.p)[X]} (hg : Irreducible g ∧ g ∣ q_r sa) :
    g.degree = oᵣ sa.r sa.p := by
  have h₁ : sa.p ^ (oᵣ sa.r sa.p) ≡ 1 [MOD sa.r] := by
    unfold oᵣ
    sorry
  -- apply (degree_eq_iff_natDegree_eq_of_pos (Nat.zero_lt_of_lt hr)).mpr
  sorry

lemma deg_h_gt_one [Fact (Nat.Prime sa.p)] : 1 < (h_def sa).degree := by
  have hg : Irreducible (h_def sa) ∧ (h_def sa) ∣ (q_r sa) := by
    constructor
    · apply irreducible_factor
    · apply factor_dvd_of_degree_ne_zero
      symm
      refine (lt_iff_le_and_ne.mp ?_).right
      unfold q_r
      apply degree_cyclotomic_pos sa.r _ sa.rgt0
  rw [deg_cyclotomic_factor_eq_order sa hg]
  exact_mod_cast sa.hrp

noncomputable
instance [Fact (Nat.Prime sa.p)] : Field (AdjoinRoot (h_def sa)) := by
  have := h_irr sa
  exact AdjoinRoot.instField

lemma h_not_zero [Fact (Nat.Prime sa.p)] : h_def sa ≠ 0 :=
  Irreducible.ne_zero (irreducible_factor (q_r sa))

lemma x_plus_a_is_unit (a : ℕ) [Fact (Nat.Prime sa.p)] :
    IsUnit (AdjoinRoot.mk (h_def sa) (X + C (a : ZMod sa.p))) := by
  apply Ne.isUnit
  intro h
  apply AdjoinRoot.mk_eq_zero.mp at h
  have deg_le_one : (h_def sa).degree ≤ (X + C (a : ZMod sa.p) : (ZMod sa.p)[X]).degree :=
    degree_le_of_dvd h (X_add_C_ne_zero (a : ZMod sa.p))
  rw [degree_X_add_C (a : ZMod sa.p)] at deg_le_one
  have one_lt_deg := deg_h_gt_one sa
  rw [degree_eq_natDegree (h_not_zero sa)] at deg_le_one
  rw [degree_eq_natDegree (h_not_zero sa)] at one_lt_deg
  have : (1 : ℕ) < 1 := by
    calc
      (1 : ℕ) < (h_def sa).natDegree := by exact_mod_cast one_lt_deg
      _ ≤ 1 := by exact_mod_cast deg_le_one
  contradiction

def G : Subgroup (ZMod sa.r)ˣ :=
  Subgroup.closure {ZMod.unitOfCoprime sa.n sa.hn, ZMod.unitOfCoprime sa.p sa.hp}

noncomputable
def t_def : ℕ := Nat.card (G sa)

lemma t_gt_zero : 0 < t_def sa := Nat.card_pos

noncomputable
def 𝒢' [Fact (Nat.Prime sa.p)] : Subgroup (AdjoinRoot (h_def sa))ˣ :=
  Subgroup.closure ((fun (i : ℕ) => (IsUnit.unit' (x_plus_a_is_unit sa i) : (AdjoinRoot (h_def sa))ˣ))'' (range (ell sa)))

noncomputable
def 𝒢 :=
  @𝒢' sa ⟨sa.p_prime⟩

def power_of_b (a b : ℕ) : Prop :=
  ∃ k, b ^ k = a

noncomputable
def lemma_4_7_helper_f [Fact (Nat.Prime sa.p)] :
    Sym (Fin (ell sa + 2)) (t_def sa - 1) → (AdjoinRoot (h_def sa))ˣ :=
  fun M => ∏ (i ∈ Multiset.toFinset M), (IsUnit.unit' (x_plus_a_is_unit sa (i : Fin (ell sa + 2)))) ^ (Multiset.count i M)

lemma lemma_4_7_helper_f_injective [Fact (Nat.Prime sa.p)] :
    Function.Injective (lemma_4_7_helper_f sa) := by
  sorry

instance adjoin_h_finite_generated [Fact (Nat.Prime sa.p)] : Module.Finite (ZMod sa.p) (AdjoinRoot (h_def sa)) := by
  apply PowerBasis.finite (AdjoinRoot.powerBasis (h_not_zero sa))

instance adjoin_h_finite [Fact (Nat.Prime sa.p)] : Finite (AdjoinRoot (h_def sa)) := by
  apply Module.finite_of_finite (ZMod sa.p)

noncomputable
instance adjoin_h_fintype [Fact (Nat.Prime sa.p)] : Fintype (AdjoinRoot (h_def sa)) := by
  apply Fintype.ofFinite

noncomputable
instance adjoin_h_units_fintype [Fact (Nat.Prime sa.p)] : Fintype (AdjoinRoot (h_def sa))ˣ := by
  apply instFintypeUnitsOfDecidableEq

noncomputable
instance big_g_fintype : Fintype ↑(𝒢 sa).carrier := Fintype.ofFinite ↑(𝒢 sa).carrier

-- ((big_g' sa) : Subset (@univ (AdjoinRoot (h_def sa))ˣ _))
lemma lemma_4_7_helper_f_image [Fact (Nat.Prime sa.p)] :
    (Finset.image (lemma_4_7_helper_f sa) univ : Finset ((AdjoinRoot (h_def sa))ˣ)) ⊆ Set.toFinset (𝒢 sa).carrier := by
  sorry

lemma lemma_4_7' [Fact (Nat.Prime sa.p)] :
    Nat.card (𝒢 sa) ≥ (t_def sa + ell sa).choose (t_def sa - 1) := by
  calc
    (t_def sa + ell sa).choose (t_def sa - 1) = ((ell sa + 2) + (t_def sa - 1) - 1).choose (t_def sa - 1) := by
      congr
      have := t_gt_zero sa
      omega
    _ = Fintype.card (Sym (Fin (ell sa + 2)) (t_def sa - 1)) := by
      nth_rw 1 [← Fintype.card_fin (ell sa + 2)]
      exact (@Sym.card_sym_eq_choose (Fin (ell sa + 2)) _ (t_def sa - 1) _).symm
    _ = (@univ (Sym (Fin (ell sa + 2)) (t_def sa - 1)) _).card := by exact rfl
    _ = (Finset.image (lemma_4_7_helper_f sa) univ : Finset ((AdjoinRoot (h_def sa))ˣ)).card := by
      exact (Finset.card_image_of_injective univ (lemma_4_7_helper_f_injective sa)).symm
    _ ≤ (Set.toFinset (𝒢 sa).carrier).card := Finset.card_le_card (lemma_4_7_helper_f_image sa)
    _ = Nat.card (𝒢 sa).carrier.toFinset := by
      exact (Nat.card_eq_finsetCard (Set.toFinset (𝒢 sa).carrier)).symm
    _ = Nat.card (𝒢 sa) := by
      congr
      simp only [Set.mem_toFinset, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
        Subgroup.mem_toSubmonoid]

lemma lemma_4_7 : Nat.card (𝒢 sa) ≥ (t_def sa + ell sa).choose (t_def sa - 1) :=
  @lemma_4_7' sa ⟨sa.p_prime⟩

lemma lemma_4_8 (not_p_power : ¬power_of_b sa.n sa.p):
    Nat.card (𝒢 sa) ≤ (sa.n : ℝ) ^ (sqrt (t_def sa)) := by
  sorry

end

end Lemma78

