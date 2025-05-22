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
  rw [Ideal.Quotient.eq, Ideal.mem_span_pair] at *
  obtain ⟨am, bm, hm⟩ := hm
  rw [← sub_eq_zero] at hm
  have polcomp : (am * (X ^ r - 1) + bm * C (p : ℤ) - (f ^ m - comp f (X ^ m))) = 0 ∨ Polynomial.eval ((X ^ q : ℤ[X]).coeff 0) (am * (X ^ r - 1) + bm * C (p : ℤ) - (f ^ m - comp f (X ^ m))) = 0 ∧ (X ^ q : ℤ[X]) = Polynomial.C ((X ^ q : ℤ[X]).coeff 0) → (am * (X ^ r - 1) + bm * C (p : ℤ) - (f ^ m - comp f (X ^ m))).comp (X ^ q) = 0 := by exact (Iff.symm comp_eq_zero_iff).1
  have compzero : (am * (X ^ r - 1) + bm * C (p : ℤ) - (f ^ m - comp f (X ^ m))).comp (X ^ q) = 0 := by
    apply polcomp
    left
    exact hm
  simp at compzero
  rw [sub_eq_zero, Polynomial.comp_assoc, Polynomial.X_pow_comp] at compzero
  use (am.comp (X ^ q)), (bm.comp (X ^ q))
  simpa

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


class Step5Assumptions where
  r : ℕ
  n : ℕ
  p : ℕ
  rgt0 : 0 < r
  hrp : 1 < oᵣ r p
  hn : n.gcd r = 1
  pgtr : r < p
  p_prime : p.Prime
  hp : p.gcd r = 1
  p_dvd_n : p ∣ n

section

variable [sa : Step5Assumptions]

noncomputable def ℓ : ℕ := Nat.floor (√sa.r.totient * logb 2 sa.n)

def introspective' (m : ℕ) (f : (ZMod sa.p)[X]) : Prop :=
  AdjoinRoot.mk (X ^ sa.r - 1) (f ^ m) = AdjoinRoot.mk (X ^ sa.r - 1) (f.comp (X ^ m))

def I_fun : ℕ → ℕ → ℕ := fun i => fun j => (sa.n / sa.p) ^ i * sa.p ^ j

def I : Set ℕ := Set.image2 I_fun Set.univ Set.univ

noncomputable def P : Submonoid ((ZMod sa.p)[X]) :=
  Submonoid.closure ((fun (i : ℕ) => (X + C (i : ZMod sa.p))) '' (range (ℓ + 2)))

lemma lemma_4_6' : ∀ m ∈ I, ∀ f ∈ P, introspective' m f := by
  sorry

end



lemma lemma_4_9 (n : ℕ) (ngt1 : 1 < n) : AKS_algorithm n = PRIME → Nat.Prime n := sorry

theorem theorem_4_1 (n : ℕ) (ngt1 : 1 < n) : n.Prime ↔ AKS_algorithm n = PRIME := by
  constructor
  exact lemma_4_2 n ngt1
  exact lemma_4_9 n ngt1


namespace Real

lemma mk_const {x : ℚ} : mk (CauSeq.const abs x) = x := rfl

theorem ratCast_le {x y : ℚ} : (x : ℝ) ≤ (y : ℝ) ↔ x ≤ y := by
  rw [← mk_const, ← mk_const, mk_le]
  exact CauSeq.const_le

end Real

namespace Nat

theorem pow_le_pow_of_le' {a n m : Nat} (h : 0 < a) (w : n ≤ m) : a ^ n ≤ a ^ m := by
  by_cases aeq1 : a = 1
  · rw [aeq1, one_pow, one_pow]
  · push_neg at aeq1
    exact Nat.pow_le_pow_of_le (lt_of_le_of_ne h aeq1.symm) w

end Nat

namespace Lemma78

lemma elem_in_set_imp_in_closure {G : Type*} [Group G] {S : Set G} {x : G} (hx : x ∈ S) : x ∈ Subgroup.closure S :=
  Subgroup.mem_closure.mpr fun _ a => a hx

lemma elem_in_set_imp_in_closure' {G : Type*} [Monoid G] {S : Set G} {x : G} (hx : x ∈ S) : x ∈ Submonoid.closure S :=
  Submonoid.mem_closure.mpr fun _ a => a hx

lemma not_inj_of_card_le_card {α β : Type*} [Finite β] (h2 : Nat.card β < Nat.card α) (f : α → β) : ¬Function.Injective f :=
  fun hf => not_le_of_lt h2 (Nat.card_le_card_of_injective f hf)

section

variable [sa : Step5Assumptions]

lemma rgt1 : 1 < sa.r := by
  have rne1 : sa.r ≠ 1 := by
    intro req1
    have h₁ := req1 ▸ sa.hrp
    exact (lt_iff_not_le.mp h₁) orderOf_le_card_univ
  exact Nat.lt_of_le_of_ne sa.rgt0 rne1.symm

lemma ngt0 : 0 < sa.n :=
  Nat.zero_lt_of_ne_zero (fun hn => (ne_of_lt rgt1) ((Nat.gcd_zero_left sa.r) ▸ hn ▸ sa.hn).symm)

instance : Fintype (ZMod sa.p) := @ZMod.fintype sa.p ⟨Nat.Prime.ne_zero sa.p_prime⟩

noncomputable def Qᵣ := cyclotomic sa.r (ZMod sa.p)

lemma Qᵣ_not_unit [Fact (Nat.Prime sa.p)] : ¬IsUnit Qᵣ :=
  not_isUnit_of_degree_pos Qᵣ (degree_cyclotomic_pos sa.r _ sa.rgt0)

noncomputable def h [Fact (Nat.Prime sa.p)] : (ZMod sa.p)[X] := Qᵣ.factor

instance h_irr [Fact (Nat.Prime sa.p)] : Fact (Irreducible h) := fact_irreducible_factor Qᵣ

lemma h_not_zero [Fact (Nat.Prime sa.p)] : h ≠ 0 := Irreducible.ne_zero (irreducible_factor Qᵣ)

instance adjoin_h_finite_generated [Fact (Nat.Prime sa.p)] : Module.Finite (ZMod sa.p) (AdjoinRoot h) :=
  PowerBasis.finite (AdjoinRoot.powerBasis h_not_zero)

instance adjoin_h_finite [Fact (Nat.Prime sa.p)] : Finite (AdjoinRoot h) :=
  Module.finite_of_finite (ZMod sa.p)

noncomputable instance [Fact (Nat.Prime sa.p)] : Fintype (AdjoinRoot h) :=
  Fintype.ofFinite (AdjoinRoot h)

lemma cast_eq_cast_of_cast [Fact (Nat.Prime sa.p)] (n : ℕ) : (↑n : AdjoinRoot h) = (↑(↑n : ZMod sa.p) : AdjoinRoot h) := by
  simp only [map_natCast]

-- This should really be in Mathlib already
instance [Fact (Nat.Prime sa.p)] : CharP (AdjoinRoot h) sa.p := by
  apply (CharP.charP_iff_prime_eq_zero sa.p_prime).mpr
  have zero_eq_zero : (0 : AdjoinRoot h) = @Nat.cast (AdjoinRoot h) NonAssocSemiring.toNatCast 0 := by
    simp only [Nat.cast_zero]
  rw [zero_eq_zero, cast_eq_cast_of_cast, cast_eq_cast_of_cast]
  simp only [CharP.cast_eq_zero, map_zero, Nat.cast_zero]

lemma p_pow_order_gt_one : 1 < sa.p ^ oᵣ sa.r sa.p :=
  Nat.one_lt_pow (Nat.not_eq_zero_of_lt sa.hrp) (Nat.Prime.one_lt sa.p_prime)

#check GaloisField

theorem deg_h_eq_order [Fact (Nat.Prime sa.p)] : h.natDegree = oᵣ sa.r sa.p := by
  sorry

lemma deg_h_gt_one [Fact (Nat.Prime sa.p)] : 1 < h.natDegree := deg_h_eq_order ▸ sa.hrp

lemma x_plus_a_is_unit (a : ℕ) [Fact (Nat.Prime sa.p)] :
    IsUnit (AdjoinRoot.mk h (X + C (a : ZMod sa.p))) := by
  apply Ne.isUnit
  intro x_plus_a_zero
  apply AdjoinRoot.mk_eq_zero.mp at x_plus_a_zero
  have deg_le_one : h.natDegree ≤ (X + C (a : ZMod sa.p) : (ZMod sa.p)[X]).natDegree :=
    natDegree_le_of_dvd x_plus_a_zero (X_add_C_ne_zero (a : ZMod sa.p))
  rw [natDegree_X_add_C (a : ZMod sa.p)] at deg_le_one
  exact (lt_iff_not_le.mp deg_h_gt_one) deg_le_one

def G : Subgroup (ZMod sa.r)ˣ :=
  Subgroup.closure {ZMod.unitOfCoprime sa.n sa.hn, ZMod.unitOfCoprime sa.p sa.hp}

noncomputable def t : ℕ := Nat.card G

lemma t_gt_zero : 0 < t := Nat.card_pos

#check MonoidHom.map_mclosure
#check Submonoid.map

lemma submonoid_closure_map_comm {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (S : Set M) :
    f '' Submonoid.closure S = Submonoid.closure (f '' S) := by
  sorry

-- Slightly different from `𝒢` used in the paper, since we need `X + (ℓ + 1)`
noncomputable def 𝒢' [Fact (Nat.Prime sa.p)] : Submonoid (AdjoinRoot h) :=
  Submonoid.closure ((fun (i : ℕ) => (AdjoinRoot.mk h (X + C (i : ZMod sa.p)))) '' (range (ℓ + 2)))

noncomputable def 𝒢 := @𝒢' sa ⟨sa.p_prime⟩

noncomputable def 𝒢₂' [Fact (Nat.Prime sa.p)] : Submonoid (AdjoinRoot h) :=
  Submonoid.map (AdjoinRoot.mk h) P

noncomputable def 𝒢₂ := @𝒢₂' sa ⟨sa.p_prime⟩

lemma 𝒢_is_𝒢₂ [Fact (Nat.Prime sa.p)] : 𝒢 = 𝒢₂ := by
  unfold 𝒢 𝒢₂ 𝒢' 𝒢₂' P
  rw [MonoidHom.map_mclosure (AdjoinRoot.mk h) ((fun (i : ℕ) => (X + C (i : ZMod sa.p))) '' (range (ℓ + 2)))]
  rw [← Set.image_comp]
  simp only [Function.comp_apply]

def is_power_of (a b : ℕ) : Prop :=
  ∃ k, b ^ k = a

noncomputable def lemma_4_7_helper_f [Fact (Nat.Prime sa.p)] :
    Sym (Fin (ℓ + 2)) (t - 1) → (AdjoinRoot h) :=
  fun M => ∏ (i ∈ Multiset.toFinset M), (AdjoinRoot.mk h (X + C ((i : Fin (ℓ + 2)) : ZMod sa.p))) ^ (Multiset.count i M)

noncomputable def lemma_4_7_helper_f' [Fact (Nat.Prime sa.p)] :
    Sym (Fin (ℓ + 2)) (t - 1) → (AdjoinRoot h) :=
  fun M => (Multiset.map (fun i => AdjoinRoot.mk h (X + C ((i : Fin (ℓ + 2)) : ZMod sa.p))) M).prod

lemma prod_pow_mk_eq_mk_prod_pow (M : Sym (Fin (ℓ + 2)) (t - 1)) [Fact (Nat.Prime sa.p)] :
    ∏ (i ∈ Multiset.toFinset M), (AdjoinRoot.mk h (X + C ((i : Fin (ℓ + 2)) : ZMod sa.p))) ^ (Multiset.count i M) =
    AdjoinRoot.mk h (∏ (i ∈ Multiset.toFinset M), (X + C ((i : Fin (ℓ + 2)) : ZMod sa.p)) ^ (Multiset.count i M)) := by
  simp only [map_prod, map_pow]

#check Polynomial.roots_prod_X_sub_C
#check Polynomial.roots.le_of_dvd
#check Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff
#check Polynomial.rootMultiplicity_eq_multiplicity
--#check FiniteMultiplicity.pow_dvd_iff_le_multiplicity
#check multiplicity.Finite.pow_dvd_iff_le_multiplicity
#check Polynomial.le_rootMultiplicity_iff
#check Polynomial.eq_of_monic_of_dvd_of_natDegree_le
#check Finset.prod_map_val
#check Finset.prod_map
#check Finset.prod_multiset_map_count
#check Multiset.prod_map_erase
#check Multiset.map_map
#check Finset.prod_bijective
#check Finset.prod_equiv
#check Finset.prod_nbij
#check Finset.prod_nbij'
#check Finset.prod_bij_ne_one
#check Finset.prod_bij
-- ↪
#check Function.Embedding
#check Multiset.card
#check Polynomial.roots_pow
#check Polynomial.roots_X_add_C
#check neg_eq_iff_eq_neg
#check Polynomial.roots_prod_X_sub_C
#check Polynomial.roots_prod
#check Polynomial.roots_multiset_prod_X_sub_C
--#check Polynomial.Monic.roots_map_of_card_eq_natDegree
#check neg_eq_iff_eq_neg
#check Function.comp_apply
#check Subgroup.multiset_prod_mem
#check Polynomial.roots_multiset_prod

lemma asdjfkl {α β γ : Type*} [CommMonoid γ] (M : Finset α) (f : α ↪ β) (g : β → γ) :
    ∏ i ∈ M, (g ∘ f) i = ∏ i ∈ Finset.map f M, g i := by
  simp only [Function.comp_apply, prod_map]

def neg_M (M : Sym (Fin (ℓ + 2)) (t - 1)) : Multiset ℤ :=
  Multiset.map (fun i => -(i : ℤ)) (M : Multiset (Fin (ℓ + 2)))

def neg_M' (M : Sym (Fin (ℓ + 2)) (t - 1)) : Multiset (ZMod sa.p) :=
  Multiset.map (fun i => -(i : ZMod sa.p)) (M : Multiset (Fin (ℓ + 2)))

lemma neg_M_count (M : Sym (Fin (ℓ + 2)) (t - 1)) (i : Fin (ℓ + 2)) :
    Multiset.count i M = Multiset.count (-(i : ℤ)) (neg_M M) := by
  sorry

lemma neg_M'_count (M : Sym (Fin (ℓ + 2)) (t - 1)) (i : Fin (ℓ + 2)) :
    Multiset.count i M = Multiset.count (-(i : ZMod sa.p)) (neg_M' M) := by
  sorry

lemma neg_M_inj {M N : Sym (Fin (ℓ + 2)) (t - 1)} (hMN : neg_M M = neg_M N) : M = N := by
  sorry

lemma neg_M'_inj {M N : Sym (Fin (ℓ + 2)) (t - 1)} (hMN : neg_M' M = neg_M' N) : M = N := by
  sorry

lemma prod_M_x_plus_a_eq_prod_neg_M_x_minus_a (M : Sym (Fin (ℓ + 2)) (t - 1)) :
    ∏ i ∈ Multiset.toFinset M, (X + C ((i : Fin (ℓ + 2)) : ZMod sa.p)) ^ Multiset.count i M =
    ∏ i ∈ Multiset.toFinset (neg_M M), (X - C ((i : ℤ) : ZMod sa.p)) ^ Multiset.count (-i) (neg_M M) := by
  simp only [map_natCast, neg_M_count, map_intCast]
  unfold neg_M
  simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton,
    Multiset.map_map, Function.comp_apply]

  sorry

lemma prod_M_x_plus_a_eq_prod_neg_M_x_minus_a' (M : Sym (Fin (ℓ + 2)) (t - 1)) :
    ∏ i ∈ Multiset.toFinset M, (X + C ((i : Fin (ℓ + 2)) : ZMod sa.p)) ^ Multiset.count i M =
    ∏ i ∈ Multiset.toFinset (neg_M' M), (X - C (i : ZMod sa.p)) ^ Multiset.count (-i) (neg_M' M) := by

  simp only [map_natCast, neg_M_count, map_intCast]
  unfold neg_M neg_M'
  simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton,
    Multiset.map_map, Function.comp_apply]

  sorry

lemma prod_M_roots (M : Sym (Fin (ℓ + 2)) (t - 1)) [Fact (Nat.Prime sa.p)] :
    (∏ i ∈ Multiset.toFinset M, (X + C ((i : Fin (ℓ + 2)) : ZMod sa.p)) ^ Multiset.count i M).roots = neg_M' M := by
  --ext x
  --set y := -x with y_def
  --rw [neg_eq_iff_eq_neg.mp y_def]
  --rw [neg_M'_count M (-x)]
  --rw [count_roots, neg_M'_count x]
  unfold neg_M'
  simp
  sorry

lemma prod_M_roots' (M : Sym (Fin (ℓ + 2)) (t - 1)) [Fact (Nat.Prime sa.p)] :
    (∏ i ∈ Multiset.toFinset M, (X - C ((i : Fin (ℓ + 2)) : ZMod sa.p)) ^ Multiset.count i M).roots = (M.val : Multiset (ZMod sa.p)) := by
  simp only [Sym.val_eq_coe, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]

  sorry

lemma lemma_4_7_helper_f_injective [Fact (Nat.Prime sa.p)] :
    Function.Injective lemma_4_7_helper_f := by
  intro x y hfxy
  unfold lemma_4_7_helper_f at *
  --unfold IsUnit.unit' at hfxy
  --apply Units.eq_iff.mpr at hfxy
  --simp only [Units.coe_prod, Units.val_pow_eq_pow_val] at hfxy
  rw [prod_pow_mk_eq_mk_prod_pow, prod_pow_mk_eq_mk_prod_pow] at hfxy
  apply AdjoinRoot.mk_eq_mk.mp at hfxy
  have prod_eq_prod : ∏ i ∈ Multiset.toFinset x, (X + C ((i : Fin (ℓ + 2)) : ZMod sa.p)) ^ Multiset.count i x =
      ∏ i ∈ Multiset.toFinset y, (X + C ((i : Fin (ℓ + 2)) : ZMod sa.p)) ^ Multiset.count i y := by
    sorry
  have neg_M'_eq : neg_M' x = neg_M' y := by
    rw [← prod_M_roots, ← prod_M_roots, prod_eq_prod]
  exact neg_M'_inj neg_M'_eq

noncomputable instance 𝒢_fintype : Fintype ↑𝒢.carrier := Fintype.ofFinite ↑𝒢.carrier

#check Subgroup.prod_mem
#check Submonoid.prod_mem
#check Subgroup.pow_mem
#check Submonoid.pow_mem

lemma lemma_4_7_helper_f_image [Fact (Nat.Prime sa.p)] :
    --(Finset.image lemma_4_7_helper_f univ : Finset ((AdjoinRoot h)ˣ)) ⊆ Set.toFinset 𝒢.carrier := by
    (Finset.image lemma_4_7_helper_f univ : Finset ((AdjoinRoot h))) ⊆ Set.toFinset 𝒢.carrier := by
  unfold 𝒢 𝒢' lemma_4_7_helper_f
  simp only [Set.subset_toFinset, coe_image, coe_univ, Set.image_univ]
  rintro x ⟨y, rfl⟩
  --apply Subgroup.prod_mem
  apply Submonoid.prod_mem
  intro c _
  --apply Subgroup.pow_mem
  apply Submonoid.pow_mem
  --apply elem_in_set_imp_in_closure
  apply elem_in_set_imp_in_closure'
  simp only [coe_range, Set.mem_image, Set.mem_Iio]
  use c, Fin.is_lt c

lemma lemma_4_7' [Fact (Nat.Prime sa.p)] :
    Nat.card 𝒢 ≥ (t + ℓ).choose (t - 1) := by
  calc
    (t + ℓ).choose (t - 1) = ((ℓ + 2) + (t - 1) - 1).choose (t - 1) := by
      congr
      have := t_gt_zero
      omega
    _ = Fintype.card (Sym (Fin (ℓ + 2)) (t - 1)) := by
      nth_rw 1 [← Fintype.card_fin (ℓ + 2)]
      exact (@Sym.card_sym_eq_choose (Fin (ℓ + 2)) _ (t - 1) _).symm
    _ = (@univ (Sym (Fin (ℓ + 2)) (t - 1)) _).card := by exact rfl
    --_ = (Finset.image lemma_4_7_helper_f univ : Finset ((AdjoinRoot h)ˣ)).card :=
    _ = (Finset.image lemma_4_7_helper_f univ : Finset ((AdjoinRoot h))).card :=
      (Finset.card_image_of_injective univ lemma_4_7_helper_f_injective).symm
    _ ≤ (Set.toFinset 𝒢.carrier).card := Finset.card_le_card lemma_4_7_helper_f_image
    _ = Nat.card 𝒢.carrier.toFinset := (Nat.card_eq_finsetCard (Set.toFinset 𝒢.carrier)).symm
    _ = Nat.card 𝒢 := by
      congr
      simp only [Set.mem_toFinset, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
        Subgroup.mem_toSubmonoid]

def I_hat_fun : Fin (⌊√t⌋₊ + 1) → Fin (⌊√t⌋₊ + 1) → ℕ :=
  fun i => fun j => (sa.n / sa.p) ^ (i : ℕ) * sa.p ^ (j : ℕ)

noncomputable def I_hat : Finset ℕ :=
  Finset.image₂ I_hat_fun (@Finset.univ (Fin (⌊√t⌋₊ + 1)) _) (@Finset.univ (Fin (⌊√t⌋₊ + 1)) _)

lemma I_hat_in_I {m : ℕ} : m ∈ I_hat → m ∈ I := by
  intro hm
  rcases Finset.mem_image₂.mp hm with ⟨i, _, j, _, hij⟩
  use i, trivial, j, trivial, hij

#check Nat.factorization_mul
#check Nat.factorization_pow
#check Nat.factorization_mul_apply_of_coprime
#check padicValNat.div'
#check Nat.factorization_div
#check Nat.pow_right_injective
#check Nat.le_of_dvd
#check Nat.ne_one_iff_exists_prime_dvd
#check Nat.Prime.factorization_pos_of_dvd
#check Finset.mem_coe

lemma exists_q_coprime (not_p_power : ¬is_power_of sa.n sa.p) : ∃ q : ℕ, q.Coprime sa.p ∧ 0 < sa.n.factorization q := by
  unfold is_power_of at *
  push_neg at not_p_power
  have h₁ : sa.n / (sa.p ^ sa.n.factorization sa.p) ≠ 1 := by
    sorry
  rcases Nat.ne_one_iff_exists_prime_dvd.mp h₁ with ⟨q, q_prime, hq⟩
  use q
  constructor
  · sorry
  · sorry

lemma I_hat_fun_inj (not_p_power : ¬is_power_of sa.n sa.p) : Function.Injective2 I_hat_fun := by
  intro i₁ j₁ i₂ j₂ heq
  unfold I_hat_fun at *
  rcases exists_q_coprime not_p_power with ⟨q, q_coprime_p, hq⟩
  have factorization_eq : (i₁ : ℕ) * sa.n.factorization q = (j₁ : ℕ) * sa.n.factorization q := by
    sorry
  have i₁eqj₁ : (i₁ : ℕ) = j₁ := Nat.mul_right_cancel hq factorization_eq
  have p_pow_eq : sa.p ^ (i₂ : ℕ) = sa.p ^ (j₂ : ℕ) := by
    rw [i₁eqj₁] at heq
    apply Nat.mul_left_cancel (pow_pos (Nat.div_pos (Nat.le_of_dvd ngt0 sa.p_dvd_n) (Nat.Prime.pos sa.p_prime)) j₁) at heq
    exact heq
  have i₂eqj₂ : (i₂ : ℕ) = j₂ := Nat.pow_right_injective (Nat.Prime.two_le sa.p_prime) p_pow_eq
  constructor
  · exact Fin.eq_of_val_eq i₁eqj₁
  · exact Fin.eq_of_val_eq i₂eqj₂

lemma I_hat_coprime_r {x : ℕ} (hx : x ∈ I_hat) : x.Coprime sa.r := by
  rcases Finset.mem_image₂.mp hx with ⟨i, _, j, _, hij⟩
  unfold I_hat_fun at hij
  rw [← hij]
  apply Nat.Coprime.mul
  · apply Nat.Coprime.pow_left
    exact Nat.Coprime.coprime_div_left sa.hn sa.p_dvd_n
  · apply Nat.Coprime.pow_left
    exact sa.hp

lemma I_hat_rewrite' (i j : Fin (⌊√t⌋₊ + 1)): (sa.n / sa.p) ^ (i : ℕ) * sa.p ^ (i : ℕ) * sa.p ^ (j : ℕ) =
    sa.n ^ (i : ℕ) * sa.p ^ (j : ℕ) := by
  rw [Nat.div_pow sa.p_dvd_n, Nat.div_mul_cancel (pow_dvd_pow_of_dvd sa.p_dvd_n i)]

lemma I_hat_rewrite {x : ℕ} (hx : x ∈ I_hat) :
  ∃ i j : ℤ, (ZMod.unitOfCoprime sa.n sa.hn) ^ i * (ZMod.unitOfCoprime sa.p sa.hp) ^ j = ZMod.unitOfCoprime x (I_hat_coprime_r hx) := by
  rcases Finset.mem_image₂.mp hx with ⟨i, _, j, _, hij⟩
  unfold I_hat_fun at *
  simp_rw [← hij]
  use i, j - (i : ℤ)
  apply Units.eq_iff.mp
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Nat.cast_mul, Nat.cast_pow]
  rw [zpow_natCast_sub_natCast]
  field_simp
  rw [mul_assoc]
  nth_rw 2 [mul_comm]
  rw [← mul_assoc]
  norm_cast
  rw [I_hat_rewrite' i j]

def I_hat_proj_fun : I_hat → G :=
  fun x => ⟨ZMod.unitOfCoprime x.val (I_hat_coprime_r x.prop), (Subgroup.mem_closure_pair.mpr (I_hat_rewrite x.prop))⟩

lemma floor_sqrt_ineq : (⌊√t⌋₊ + 1) * (⌊√t⌋₊ + 1) > (t : ℝ) := by
  calc
    (⌊√t⌋₊ + 1) * (⌊√t⌋₊ + 1) > √t * √t := mul_self_lt_mul_self (sqrt_nonneg ↑t) (Nat.lt_floor_add_one √↑t)
    _ = t := mul_self_sqrt (by exact_mod_cast le_of_lt t_gt_zero)

lemma card_G_lt_card_I_hat (not_p_power : ¬is_power_of sa.n sa.p) : Nat.card I_hat > Nat.card G := by
  calc
    Nat.card I_hat = Finset.card I_hat := Nat.card_eq_finsetCard I_hat
    _ = Finset.card (@Finset.univ (Fin (⌊√t⌋₊ + 1)) _) * Finset.card (@Finset.univ (Fin (⌊√t⌋₊ + 1)) _) := by
      apply Finset.card_image₂ (I_hat_fun_inj not_p_power)
    _ = (⌊√t⌋₊ + 1) * (⌊√t⌋₊ + 1) := by rw [card_univ, Fintype.card_fin]
    _ > t := by exact_mod_cast floor_sqrt_ineq
    _ = Nat.card G := rfl

lemma exists_m₁_m₂ (not_p_power : ¬is_power_of sa.n sa.p) : ∃ (m₁ m₂ : ℕ), m₁ ∈ I_hat ∧ m₂ ∈ I_hat ∧ m₁ ≡ m₂ [MOD sa.r] ∧ m₁ > m₂ := by
  rcases Function.not_injective_iff.mp (not_inj_of_card_le_card (card_G_lt_card_I_hat not_p_power) I_hat_proj_fun) with ⟨m₁, m₂, hm₁m₂, m₁neqm₂⟩
  wlog m₁gtm₂ : m₁ > m₂ generalizing m₁ m₂
  · exact this m₂ m₁ hm₁m₂.symm m₁neqm₂.symm (lt_of_le_of_ne (le_of_not_lt m₁gtm₂) m₁neqm₂)
  use m₁, m₂, m₁.prop, m₂.prop
  constructor
  · unfold I_hat_proj_fun ZMod.unitOfCoprime at hm₁m₂
    simp only [Subtype.mk.injEq, Units.mk.injEq] at hm₁m₂
    exact (ZMod.eq_iff_modEq_nat sa.r).mp hm₁m₂.left
  · exact m₁gtm₂

lemma in_I_hat_imp_le_n_pow_sqrt_t {m : ℕ} (hm : m ∈ I_hat) : m ≤ sa.n ^ ⌊√t⌋₊ := by
  rcases Finset.mem_image₂.mp hm with ⟨i, _, j, _, hij⟩
  calc
    m = (sa.n / sa.p) ^ (i : ℕ) * sa.p ^ (j : ℕ) := by
      exact hij.symm
    _ ≤ (sa.n / sa.p) ^ ⌊√t⌋₊ * sa.p ^ ⌊√t⌋₊ := by
      apply mul_le_mul_of_nonneg
      · exact Nat.pow_le_pow_of_le' (Nat.div_pos (Nat.le_of_dvd ngt0 sa.p_dvd_n) (Nat.Prime.pos sa.p_prime)) (Nat.le_of_lt_succ i.isLt)
      · exact Nat.pow_le_pow_of_le' (Nat.Prime.pos sa.p_prime) (Nat.le_of_lt_succ j.isLt)
      · exact Nat.zero_le _
      · exact Nat.zero_le _
    _ = sa.n ^ ⌊√t⌋₊ := by
      rw [← mul_pow, Nat.div_mul_cancel sa.p_dvd_n]

lemma degree_x_pow_m (m : ℕ) [Fact (Nat.Prime sa.p)] : ((X : (AdjoinRoot h)[X]) ^ m).natDegree = m := by
  simp only [natDegree_pow, natDegree_X, mul_one]

noncomputable def Q' (m₁ m₂ : ℕ) [Fact (Nat.Prime sa.p)] : (AdjoinRoot h)[X] := X ^ m₁ - X ^ m₂

lemma h_dvd_x_pow_r_minus_one [Fact (Nat.Prime sa.p)] : h ∣ (X^sa.r - 1) :=
  dvd_trans (factor_dvd_of_not_isUnit Qᵣ_not_unit) (cyclotomic.dvd_X_pow_sub_one sa.r (ZMod sa.p))

lemma x_r_eq_1 [Fact (Nat.Prime sa.p)] : AdjoinRoot.mk h X ^ sa.r = 1 := by
  apply (@sub_left_inj _ _ 1 (AdjoinRoot.mk h X ^ sa.r) 1).mp
  rw [sub_self]
  apply AdjoinRoot.mk_eq_zero.mpr
  exact h_dvd_x_pow_r_minus_one

def introspective'' [Fact (Nat.Prime sa.p)] (m : ℕ) (f : (ZMod sa.p)[X]) : Prop :=
  AdjoinRoot.mk h (f ^ m) = AdjoinRoot.mk h (f.comp (X ^ m))

lemma lemma_4_6'' [Fact (Nat.Prime sa.p)] {m : ℕ} {f : (ZMod sa.p)[X]} (m_in_I : m ∈ I) (f_in_P : f ∈ P) :
  introspective'' m f := by
  have hi := lemma_4_6' m m_in_I f f_in_P
  unfold introspective'' introspective' at *
  simp only [AdjoinRoot.mk_eq_mk] at *
  exact dvd_trans h_dvd_x_pow_r_minus_one hi

lemma elem_𝒢_imp_root {m₁ m₂ : ℕ} (m₁_I_hat : m₁ ∈ I_hat) (m₂_I_hat : m₂ ∈ I_hat) (hm₁m₂r : m₁ ≡ m₂ [MOD sa.r]) [Fact (Nat.Prime sa.p)] :
  --coe_𝒢.val ≤ (Q' m₁ m₂).roots := by
  𝒢.carrier.toFinset.val ≤ (Q' m₁ m₂).roots := by
  apply Multiset.le_iff_count.mpr
  intro f
  --by_cases hf : f ∈ coe_𝒢
  by_cases hf : f ∈ 𝒢.carrier.toFinset
  · have Q'neq0 : Q' m₁ m₂ ≠ 0 := by
      sorry
    have x_pow_m₁_eq_x_pow_m₂ : (AdjoinRoot.mk h X) ^ m₁ = (AdjoinRoot.mk h X) ^ m₂ := by

      sorry
    have hfQ : f ∈ (Q' m₁ m₂).roots := by
      apply (Polynomial.mem_roots_iff_aeval_eq_zero Q'neq0).mpr
      unfold Q'
      simp only [coe_aeval_eq_eval, eval_sub, eval_pow, eval_X]
      simp only [Set.mem_toFinset, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup] at hf
      rw [𝒢_is_𝒢₂] at hf
      rcases hf with ⟨g, g_in_P, hg⟩
      rw [← hg]
      have gm₁i := lemma_4_6'' (I_hat_in_I m₁_I_hat) g_in_P
      have gm₂i := lemma_4_6'' (I_hat_in_I m₂_I_hat) g_in_P
      unfold introspective'' at *
      rw [gm₁i, gm₂i]
      sorry
    calc
      --Multiset.count f coe_𝒢.val = 1 := Multiset.count_eq_one_of_mem (Finset.nodup coe_𝒢) hf
      Multiset.count f 𝒢.carrier.toFinset.val = 1 := Multiset.count_eq_one_of_mem (Finset.nodup 𝒢.carrier.toFinset) hf
      _ ≤ Multiset.count f (Q' m₁ m₂).roots := Multiset.one_le_count_iff_mem.mpr hfQ
  · calc
      --Multiset.count f coe_𝒢.val = 0 := Multiset.count_eq_zero.mpr hf
      Multiset.count f 𝒢.carrier.toFinset.val = 0 := Multiset.count_eq_zero.mpr hf
      _ ≤ Multiset.count f (Q' m₁ m₂).roots := Nat.zero_le _

lemma lemma_4_8' [Fact (Nat.Prime sa.p)] (not_p_power : ¬is_power_of sa.n sa.p) :
    Nat.card 𝒢 ≤ sa.n ^ ⌊√t⌋₊ := by
  rcases exists_m₁_m₂ not_p_power with ⟨m₁, m₂, m₁_I_hat, m₂_I_hat, hm₁m₂r, m₁gtm₂⟩
  calc
    Nat.card 𝒢 = Finset.card 𝒢.carrier.toFinset := Nat.card_eq_card_toFinset 𝒢.carrier
    --_ = Finset.card coe_𝒢 := (Finset.card_map ⟨Units.val, @Units.ext (AdjoinRoot h) _⟩).symm
    --_ = Multiset.card coe_𝒢.val := Finset.card_def coe_𝒢
    _ = Multiset.card 𝒢.carrier.toFinset.val := Finset.card_def 𝒢.carrier.toFinset
    _ ≤ Multiset.card (Q' m₁ m₂).roots := by
      exact Multiset.card_le_card (elem_𝒢_imp_root m₁_I_hat m₂_I_hat hm₁m₂r)
    _ ≤ (Q' m₁ m₂).natDegree := Polynomial.card_roots' (Q' m₁ m₂)
    _ = m₁ := by
      unfold Q'
      nth_rw 2 [← degree_x_pow_m m₁]
      apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      simpa only [natDegree_pow, natDegree_X, mul_one]
    _ ≤ sa.n ^ ⌊√t⌋₊ := by
      exact in_I_hat_imp_le_n_pow_sqrt_t m₁_I_hat

lemma lemma_4_8_glue : sa.n ^ ⌊√t⌋₊ ≤ (sa.n : ℝ) ^ √t := by
  have cast_n_ge_1 : 1 ≤ (sa.n : ℝ) := by exact_mod_cast ngt0
  have floor_sqrt_sq_le_t : ((⌊√↑t⌋₊ ^ 2 : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ) := by
    simp only [nat_floor_real_sqrt_eq_nat_sqrt]
    apply ratCast_le.mpr
    exact_mod_cast Nat.sqrt_le' t
  have floor_sqrt_le_sqrt : ⌊√t⌋₊ ≤ √t := by
    apply le_sqrt_of_sq_le
    exact_mod_cast floor_sqrt_sq_le_t
  exact_mod_cast Real.rpow_le_rpow_of_exponent_le cast_n_ge_1 floor_sqrt_le_sqrt

end

lemma lemma_4_7 (sa : Step5Assumptions) : Nat.card 𝒢 ≥ (t + ℓ).choose (t - 1) :=
  @lemma_4_7' sa ⟨sa.p_prime⟩

lemma lemma_4_8 (sa : Step5Assumptions) (not_p_power : ¬is_power_of sa.n sa.p) :
    Nat.card 𝒢 ≤ (sa.n : ℝ) ^ √t := by
  trans (sa.n ^ ⌊√t⌋₊)
  exact_mod_cast @lemma_4_8' sa ⟨sa.p_prime⟩ not_p_power
  exact_mod_cast @lemma_4_8_glue sa

end Lemma78


