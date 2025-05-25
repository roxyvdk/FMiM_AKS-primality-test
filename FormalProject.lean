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

noncomputable instance {n : ℕ} : Decidable (perfect_power n) := by
  apply Classical.propDecidable

/-- The order of n in `(ℤ/rℤ)ˣ`.-/
noncomputable def oᵣ (r n : ℕ) : ℕ :=
  orderOf (n : ZMod r)

noncomputable def smallest_r (n : ℕ) : ℕ :=
  sInf {r : ℕ | oᵣ r n > (logb 2 n) ^ 2}

def is_not_coprime_in_range (r n : ℕ) : Prop :=
  ∃ a : ℕ, a ≤ r ∧ 1 < n.gcd a ∧ n.gcd a < n

noncomputable instance {r n : ℕ} : Decidable (is_not_coprime_in_range r n) := by
  apply Classical.propDecidable

def polynomial_equality (r n a : ℕ) : Prop :=
  (((X + C (a : ℤ))^n : ℤ[X]) : ℤ[X] ⧸ Ideal.span ({X^r - 1, C (n : ℤ)} : Set ℤ[X])) = (X^n + C (a : ℤ) : ℤ[X])

def polynomial_equality' (r n a : ℕ) : Prop :=
  AdjoinRoot.mk (X^r - C (1 : ZMod n)) (X + C (a : ZMod n))^n = AdjoinRoot.mk (X^r - C (1 : ZMod n)) (X^n + C (a : ZMod n))

def step_5_false (r n : ℕ) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ a ≤ Nat.floor (Real.sqrt r.totient * logb 2 n) ∧ ¬polynomial_equality r n a

noncomputable instance {r n : ℕ} : Decidable (step_5_false r n) := by
  apply Classical.propDecidable

noncomputable def AKS_algorithm (n: ℕ) : AKS_Output :=
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

lemma lemma_4_3 (n : ℕ) (h : 2 ≤ n) :
    ∃ r : ℕ, r ≤ max 3 ⌈(logb 2 n)^5⌉₊ ∧ oᵣ r n > (logb 2 n)^2 := sorry

class Step5Assumptions where
  r : ℕ
  n : ℕ
  p : ℕ
  ngt1 : n > 1
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

lemma quot_prod (f g q r : (ZMod sa.p)[X]) (q_dvd_r : q ∣ r) :
  AdjoinRoot.mk r f = AdjoinRoot.mk r g → AdjoinRoot.mk q f = AdjoinRoot.mk q g := by
  intro hr
  rw [AdjoinRoot.mk_eq_mk] at *
  exact dvd_trans q_dvd_r hr

lemma no_zero_div : NoZeroDivisors (ZMod sa.p) := by
  have : Fact sa.p.Prime := ⟨sa.p_prime⟩
  exact inferInstance

lemma introspec_pow (f : (ZMod sa.p)[X]) (m : ℕ) : (introspective' m f) → ∀ q : ℕ,
  AdjoinRoot.mk (X^(q*sa.r) - 1) ((f.comp (X ^ q)) ^ m) = AdjoinRoot.mk (X^(q*sa.r) - 1) (f.comp (Polynomial.X ^(m*q))) := by
  intro hm q
  unfold introspective' at hm
  rw [pow_mul, mul_comm, pow_mul]
  rw [AdjoinRoot.mk_eq_mk] at *
  rw [dvd_iff_exists_eq_mul_left] at *
  obtain ⟨c,hm⟩ := hm
  rw [← sub_eq_zero] at hm
  haveI : NoZeroDivisors (ZMod sa.p) := by exact no_zero_div
  have polcomp : (f ^ m - f.comp (X ^ m) - c * (X ^ sa.r - 1)) = 0 ∨ Polynomial.eval ((X ^ q : (ZMod sa.p)[X]).coeff 0) (f ^ m - f.comp (X ^ m) - c * (X ^ sa.r - 1)) = 0 ∧ (X ^ q : (ZMod sa.p)[X]) = Polynomial.C ((X ^ q : (ZMod sa.p)[X]).coeff 0) → (f ^ m - f.comp (X ^ m) - c * (X ^ Step5Assumptions.r - 1)).comp (X ^ q) = 0 := by
    exact (Iff.symm (comp_eq_zero_iff)).1
  have compzero : (f ^ m - f.comp (X ^ m) - c * (X ^ Step5Assumptions.r - 1)).comp (X ^ q) = 0 := by
    apply polcomp
    left
    exact hm
  simp at compzero
  rw [sub_eq_zero, Polynomial.comp_assoc, Polynomial.X_pow_comp] at compzero
  use c.comp (X ^ q)

lemma lemma_4_5' (m m' : ℕ) (f : (ZMod sa.p)[X]) (hm : introspective' m f) (hm' : introspective' m' f) : introspective' (m * m') f := by
  have hmm' : AdjoinRoot.mk (X^(m * sa.r) - 1) (f.comp (Polynomial.X ^ m) ^ m') = AdjoinRoot.mk (X^(m * sa.r) - 1) (f.comp (Polynomial.X ^ (m' * m))) := by
      simp at *
      exact introspec_pow f m' hm' m
  unfold introspective' at *
  simp at *
  rw [pow_mul,hm]
  have xr_dvd_xmr : ((X ^ sa.r + C (-1 : (ZMod sa.p))) : (ZMod sa.p)[X]) ∣ ((X^(m * sa.r) + C (-1 : (ZMod sa.p))) : (ZMod sa.p)[X]) := by
    let f : (ZMod sa.p)[X] := X ^ sa.r - 1
    let g : (ZMod sa.p)[X] := ∑ i ∈ Finset.range m, X ^ (i * sa.r)
    have : f * g = X ^ (m * sa.r) + C (-1) := by
      simp only [f, g, ← C_1, ← sub_eq_add_neg]
      have : (∑ i ∈ Finset.range m, (X : (ZMod sa.p)[X]) ^ (i * sa.r)) = (∑ i ∈ Finset.range m, (X ^ sa.r) ^ i) := by
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
  apply quot_prod _ _ _ _ xr_dvd_xmr at hmm'
  rw [mul_comm m m']
  simp [← hmm']

lemma lemma_4_6 (m : ℕ) (f g : (ZMod sa.p)[X]) (hmf : introspective' m f) (hmg : introspective' m g) : introspective' m (f * g) := by
  unfold introspective' at *
  simp [mul_pow, ← hmf, ← hmg]

def I_fun : ℕ → ℕ → ℕ := fun i => fun j => (sa.n / sa.p) ^ i * sa.p ^ j

def I : Set ℕ := Set.image2 I_fun Set.univ Set.univ

noncomputable def P : Submonoid ((ZMod sa.p)[X]) :=
  Submonoid.closure ((fun (i : ℕ) => (X + C (i : ZMod sa.p))) '' (range (ℓ + 2)))

lemma introspective_np (h : ∀ (a : ℕ), a ≤ ℓ → AdjoinRoot.mk (X ^ sa.r - 1) ((X + C (a : ZMod sa.n) : (ZMod sa.n)[X]) ^ sa.n) = AdjoinRoot.mk (X ^ sa.r - 1) ((X + C (a : ZMod sa.n) : (ZMod sa.n)[X]).comp (X ^ sa.n))) : ∀ (a : ℕ), a ≤ ℓ → introspective' sa.n (X + C (a : ZMod sa.p) : (ZMod sa.p)[X]) := by
  let f : ZMod sa.n →+* ZMod sa.p := ZMod.castHom sa.p_dvd_n (ZMod sa.p)
  intro a hal
  unfold introspective'
  have hap := h a hal
  rw [AdjoinRoot.mk_eq_mk] at *
  rw [dvd_iff_exists_eq_mul_left] at *
  obtain ⟨c,hap⟩ := hap
  have pdvdn := sa.p_dvd_n
  rw [← sub_eq_zero] at hap
  let φ : (ZMod sa.n)[X] →+* (ZMod sa.p)[X] := Polynomial.mapRingHom f
  use φ c
  rw [sub_eq_zero] at hap
  apply_fun φ at hap
  rw [map_sub, map_mul, map_pow, map_add] at hap
  simp at *
  have h₀ : φ X = X := by
    exact Polynomial.map_X f
  rw [h₀] at hap
  exact hap

lemma introspective_n_div_p (h : ∀ (a : ℕ), a ≤ ℓ → AdjoinRoot.mk (X ^ sa.r - 1) ((X + C (a : ZMod sa.n) : (ZMod sa.n)[X]) ^ sa.n) = AdjoinRoot.mk (X ^ sa.r - 1) ((X + C (a : ZMod sa.n) : (ZMod sa.n)[X]).comp (X ^ sa.n))) : ∀ (a : ℕ), a ≤ ℓ → introspective' (sa.n/sa.p) (X + C (a : ZMod sa.p) : (ZMod sa.p)[X]) := by
  intro a hal
  have hnp := introspective_np h a hal
  have hp : introspective' sa.p (X + C (a : ZMod sa.p) : (ZMod sa.p)[X]) := by
    -- exact lemma_2_1 sa.p a _ sa.p_prime
    sorry
  unfold introspective' at *
  have hn : sa.n = sa.p * (sa.n / sa.p) := by
    symm
    exact Nat.mul_div_cancel' sa.p_dvd_n
  rw [hn, pow_mul] at hnp
  rw [AdjoinRoot.mk_eq_mk] at *
  rw [dvd_iff_exists_eq_mul_left] at *
  obtain ⟨cnp,hnp⟩ := hnp
  obtain ⟨cp,hp⟩ := hp
  apply eq_add_of_sub_eq at hp
  simp at *
  sorry

lemma lemma_4_6' (h : ∀ (a : ℕ), a ≤ ℓ → AdjoinRoot.mk (X ^ sa.r - 1) ((X + C (a : ZMod sa.n) : (ZMod sa.n)[X]) ^ sa.n) = AdjoinRoot.mk (X ^ sa.r - 1) ((X + C (a : ZMod sa.n) : (ZMod sa.n)[X]).comp (X ^ sa.n))) : ∀ m ∈ I, ∀ f ∈ P, introspective' m f := by
  intro m hm f hf
  unfold introspective'
  unfold I at hm
  simp at hm
  obtain ⟨a,b,hm⟩ := hm
  unfold I_fun at hm
  unfold P at hf
  simp at hf
  sorry

end

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

namespace Polynomial

lemma comp_dvd {R : Type*} [CommRing R] {f₁ f₂ g : R[X]} (hg : g.natDegree ≠ 0) :
    f₁ - f₂ ∣ g.comp f₁ - g.comp f₂ := by
  apply @Polynomial.natDegree_ne_zero_induction_on _ _ (fun g : R[X] => f₁ - f₂ ∣ g.comp f₁ - g.comp f₂) g hg
  · intro a p
    simp only [add_comp, C_comp, add_sub_add_left_eq_sub, imp_self]
  · intro p q hp hq
    have hpq : (p + q).comp f₁ - (p + q).comp f₂ = (p.comp f₁ - p.comp f₂) + (q.comp f₁ - q.comp f₂) := by
      simp only [add_comp]
      ring
    rw [hpq]
    exact dvd_add hp hq
  · intro n a _ _
    simp only [monomial_comp]
    apply dvd_mul_sub_mul
    · simp only [sub_self, dvd_zero]
    · exact sub_dvd_pow_sub_pow f₁ f₂ n

end Polynomial

namespace Lemma78

lemma elem_in_set_imp_in_closure {G : Type*} [Monoid G] {S : Set G} {x : G} (hx : x ∈ S) : x ∈ Submonoid.closure S :=
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
  rw [prod_pow_mk_eq_mk_prod_pow, prod_pow_mk_eq_mk_prod_pow] at hfxy
  apply AdjoinRoot.mk_eq_mk.mp at hfxy
  have prod_eq_prod : ∏ i ∈ Multiset.toFinset x, (X + C ((i : Fin (ℓ + 2)) : ZMod sa.p)) ^ Multiset.count i x =
      ∏ i ∈ Multiset.toFinset y, (X + C ((i : Fin (ℓ + 2)) : ZMod sa.p)) ^ Multiset.count i y := by
    sorry
  have neg_M'_eq : neg_M' x = neg_M' y := by
    rw [← prod_M_roots, ← prod_M_roots, prod_eq_prod]
  exact neg_M'_inj neg_M'_eq

noncomputable instance 𝒢_fintype : Fintype ↑𝒢.carrier := Fintype.ofFinite ↑𝒢.carrier

lemma lemma_4_7_helper_f_image [Fact (Nat.Prime sa.p)] :
    (Finset.image lemma_4_7_helper_f univ : Finset ((AdjoinRoot h))) ⊆ Set.toFinset 𝒢.carrier := by
  unfold 𝒢 𝒢' lemma_4_7_helper_f
  simp only [Set.subset_toFinset, coe_image, coe_univ, Set.image_univ]
  rintro x ⟨y, rfl⟩
  apply Submonoid.prod_mem
  intro c _
  apply Submonoid.pow_mem
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

lemma exists_q_coprime (not_p_power : ¬is_power_of sa.n sa.p) : ∃ q : ℕ, q.Prime ∧ q.Coprime sa.p ∧ 0 < sa.n.factorization q := by
  unfold is_power_of at *
  push_neg at not_p_power
  have h₁ : sa.n / (sa.p ^ sa.n.factorization sa.p) ≠ 1 := by
    intro h₂
    exact not_p_power (sa.n.factorization sa.p) (Nat.eq_of_dvd_of_div_eq_one (Nat.ord_proj_dvd sa.n sa.p) h₂)
  rcases Nat.ne_one_iff_exists_prime_dvd.mp h₁ with ⟨q, q_prime, hq⟩
  apply Nat.mul_dvd_of_dvd_div (Nat.ord_proj_dvd sa.n sa.p) at hq
  have q_coprime_p : q.Coprime sa.p := by
    apply (Nat.coprime_primes q_prime sa.p_prime ).mpr
    rintro rfl
    rw [← pow_succ] at hq
    exact Nat.pow_succ_factorization_not_dvd (ne_of_lt ngt0).symm sa.p_prime hq
  use q, q_prime, q_coprime_p
  apply Nat.Prime.factorization_pos_of_dvd q_prime (ne_of_lt ngt0).symm
  exact dvd_trans (Nat.dvd_mul_left q _) hq

lemma n_div_p_pos : 0 < sa.n / sa.p := (Nat.div_pos (Nat.le_of_dvd ngt0 sa.p_dvd_n) (Nat.Prime.pos sa.p_prime))

lemma I_hat_fun_inj (not_p_power : ¬is_power_of sa.n sa.p) : Function.Injective2 I_hat_fun := by
  intro i₁ j₁ i₂ j₂ heq
  unfold I_hat_fun at *
  rcases exists_q_coprime not_p_power with ⟨q, q_prime, q_coprime_p, hq⟩
  have p_factorization_q : sa.p.factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd q_prime).mp q_coprime_p)
  have p_pow_factorization_q (i : ℕ) : (sa.p ^ i).factorization q = 0 := by
    simp only [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_eq_zero]
    right
    exact p_factorization_q
  have factorization_eq : (i₁ : ℕ) * sa.n.factorization q = (j₁ : ℕ) * sa.n.factorization q := by
    calc
      (i₁ : ℕ) * sa.n.factorization q = (i₁ : ℕ) * (sa.n.factorization q - sa.p.factorization q) := by
        rw [p_factorization_q]; simp
      _ = (i₁ : ℕ) * ((sa.n / sa.p).factorization q) := by
        rw [Nat.factorization_div sa.p_dvd_n]; simp
      _ = ((sa.n / sa.p) ^ (i₁ : ℕ)).factorization q := by
        simp
      _ = ((sa.n / sa.p) ^ (i₁ : ℕ)).factorization q + (sa.p ^ (i₂ : ℕ)).factorization q := by
        rw [p_pow_factorization_q]; simp
      _ = ((sa.n / sa.p) ^ (i₁ : ℕ) * sa.p ^ (i₂ : ℕ)).factorization q := by
        rw [Nat.factorization_mul (ne_of_lt (Nat.pow_pos n_div_p_pos)).symm (ne_of_lt (Nat.pow_pos (Nat.Prime.pos sa.p_prime))).symm]; simp
      _ = ((sa.n / sa.p) ^ (j₁ : ℕ) * sa.p ^ (j₂ : ℕ)).factorization q := by
        rw [heq]
      _ = ((sa.n / sa.p) ^ (j₁ : ℕ)).factorization q + (sa.p ^ (j₂ : ℕ)).factorization q := by
        rw [Nat.factorization_mul (ne_of_lt (Nat.pow_pos n_div_p_pos)).symm (ne_of_lt (Nat.pow_pos (Nat.Prime.pos sa.p_prime))).symm]; simp
      _ = ((sa.n / sa.p) ^ (j₁ : ℕ)).factorization q := by
        rw [p_pow_factorization_q]; simp
      _ = (j₁ : ℕ) * ((sa.n / sa.p).factorization q) := by
        simp
      _ = (j₁ : ℕ) * (sa.n.factorization q - sa.p.factorization q) := by
        rw [Nat.factorization_div sa.p_dvd_n]; simp
      _ = (j₁ : ℕ) * sa.n.factorization q := by
        rw [p_factorization_q]; simp
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

lemma Q'_degree {m₁ m₂ : ℕ} (m₁gtm₂ : m₁ > m₂) [Fact (Nat.Prime sa.p)] : (Q' m₁ m₂).natDegree = m₁ := by
  unfold Q'
  nth_rw 2 [← degree_x_pow_m m₁]
  apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
  simpa only [natDegree_pow, natDegree_X, mul_one]

lemma h_dvd_x_pow_r_minus_one [Fact (Nat.Prime sa.p)] : h ∣ (X^sa.r - 1) :=
  dvd_trans (factor_dvd_of_not_isUnit Qᵣ_not_unit) (cyclotomic.dvd_X_pow_sub_one sa.r (ZMod sa.p))

lemma x_pow_r_eq_1 [Fact (Nat.Prime sa.p)] : AdjoinRoot.mk h (X ^ sa.r) = 1 := by
  apply (@sub_left_inj _ _ 1 (AdjoinRoot.mk h (X ^ sa.r)) 1).mp
  rw [sub_self]
  exact AdjoinRoot.mk_eq_zero.mpr h_dvd_x_pow_r_minus_one

def introspective'' [Fact (Nat.Prime sa.p)] (m : ℕ) (f : (ZMod sa.p)[X]) : Prop :=
  AdjoinRoot.mk h (f ^ m) = AdjoinRoot.mk h (f.comp (X ^ m))

lemma lemma_4_6'' [Fact (Nat.Prime sa.p)] {m : ℕ} {f : (ZMod sa.p)[X]} (m_in_I : m ∈ I) (f_in_P : f ∈ P) :
  introspective'' m f := by
  have hi := lemma_4_6' m m_in_I f f_in_P
  unfold introspective'' introspective' at *
  simp only [AdjoinRoot.mk_eq_mk] at *
  exact dvd_trans h_dvd_x_pow_r_minus_one hi

lemma elem_𝒢_imp_root {m₁ m₂ : ℕ} (m₁_I_hat : m₁ ∈ I_hat) (m₂_I_hat : m₂ ∈ I_hat) (hm₁m₂r : m₁ ≡ m₂ [MOD sa.r]) (m₁gtm₂ : m₁ > m₂) [Fact (Nat.Prime sa.p)] :
  𝒢.carrier.toFinset.val ≤ (Q' m₁ m₂).roots := by
  apply Multiset.le_iff_count.mpr
  intro f
  by_cases hf : f ∈ 𝒢.carrier.toFinset
  · have Q'neq0 : Q' m₁ m₂ ≠ 0 := Polynomial.ne_zero_of_natDegree_gt ((Q'_degree m₁gtm₂) ▸ Nat.zero_lt_of_lt m₁gtm₂)
    have x_pow_m₁_eq_x_pow_m₂ : AdjoinRoot.mk h (X ^ m₁) = AdjoinRoot.mk h (X ^ m₂) := by
      rcases (Nat.modEq_iff_dvd' (le_of_lt m₁gtm₂)).mp hm₁m₂r.symm with ⟨k, hk⟩
      rw [Nat.eq_add_of_sub_eq (le_of_lt m₁gtm₂) hk, pow_add, pow_mul, map_mul, map_pow, x_pow_r_eq_1, one_pow, one_mul]
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
      simp only [map_pow] at gm₁i gm₂i
      rw [gm₁i, gm₂i, sub_eq_zero]
      simp only [AdjoinRoot.mk_eq_mk] at *
      by_cases g_degree_0 : g.natDegree = 0
      · rcases Polynomial.natDegree_eq_zero.mp g_degree_0 with ⟨a, rfl⟩
        simp only [C_comp, sub_self, dvd_zero]
      · calc
          h ∣ X ^ m₁ - X ^ m₂ := x_pow_m₁_eq_x_pow_m₂
          _ ∣ g.comp (X ^ m₁) - g.comp (X ^ m₂) := by
            exact Polynomial.comp_dvd g_degree_0
    calc
      Multiset.count f 𝒢.carrier.toFinset.val = 1 := Multiset.count_eq_one_of_mem (Finset.nodup 𝒢.carrier.toFinset) hf
      _ ≤ Multiset.count f (Q' m₁ m₂).roots := Multiset.one_le_count_iff_mem.mpr hfQ
  · calc
      Multiset.count f 𝒢.carrier.toFinset.val = 0 := Multiset.count_eq_zero.mpr hf
      _ ≤ Multiset.count f (Q' m₁ m₂).roots := Nat.zero_le _

lemma lemma_4_8' [Fact (Nat.Prime sa.p)] (not_p_power : ¬is_power_of sa.n sa.p) :
    Nat.card 𝒢 ≤ sa.n ^ ⌊√t⌋₊ := by
  rcases exists_m₁_m₂ not_p_power with ⟨m₁, m₂, m₁_I_hat, m₂_I_hat, hm₁m₂r, m₁gtm₂⟩
  calc
    Nat.card 𝒢 = Finset.card 𝒢.carrier.toFinset := Nat.card_eq_card_toFinset 𝒢.carrier
    _ = Multiset.card 𝒢.carrier.toFinset.val := Finset.card_def 𝒢.carrier.toFinset
    _ ≤ Multiset.card (Q' m₁ m₂).roots := Multiset.card_le_card (elem_𝒢_imp_root m₁_I_hat m₂_I_hat hm₁m₂r m₁gtm₂)
    _ ≤ (Q' m₁ m₂).natDegree := Polynomial.card_roots' (Q' m₁ m₂)
    _ = m₁ := Q'_degree m₁gtm₂
    _ ≤ sa.n ^ ⌊√t⌋₊ := in_I_hat_imp_le_n_pow_sqrt_t m₁_I_hat

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




variable (sa : Step5Assumptions)

lemma lem_2_1_result (n : ℕ) (a : ℤ) (h : (X + C (a : ZMod n)) ^ n = X ^ n + C (a : ZMod n)):
    AdjoinRoot.mk (X^r - C (1 : ZMod n)) (X + C (a : ZMod n))^n = AdjoinRoot.mk (X^r - C (1 : ZMod n)) (X^n + C (a : ZMod n)) := by
  rw [←h]
  rfl

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

lemma sublem_4_2_3 (n : ℕ) (ngt1 : n > 1) : n.Prime → smallest_r n < n → ¬ step_5_false (smallest_r n) n := by
  unfold step_5_false
  intro hp _ hineq
  rcases hineq with ⟨a,ha⟩
  rcases ha with ⟨_,hb⟩
  rcases hb with ⟨_,ineq⟩
  unfold polynomial_equality' at ineq
  let a' : ℤ := ↑a
  have : (X + C (a' : ZMod n)) ^ n = X ^ n + C (a' : ZMod n) := by
    apply (lemma_2_1 n a' ngt1).mp hp

  have heq: AdjoinRoot.mk (X^smallest_r n - C (1 : ZMod n)) (X + C (a' : ZMod n))^n = AdjoinRoot.mk (X^smallest_r n - C (1 : ZMod n)) (X^n + C (a' : ZMod n)) := by
    apply lem_2_1_result n a' this

  have : ¬(AdjoinRoot.mk (X ^ smallest_r n - C 1)) (X + C (a' : ZMod n)) ^ n = (AdjoinRoot.mk (X ^ smallest_r n - C 1)) (X ^ n + C (a' : ZMod n)) := by
    have cast_eq : (↑(↑a : ℤ) : ZMod n) = (↑a : ZMod n) := by
      norm_cast
    rw [cast_eq]
    exact ineq
  exact this heq


lemma lemma_4_2 (n : ℕ) (ngt1 : 1 < n) : n.Prime → AKS_algorithm n = PRIME := by
  intro hp
  unfold AKS_algorithm
  apply if_neg
  rw [or_iff_not_and_not]
  simp
  constructor
  · exact sublem_4_2_1 n hp
  · constructor
    · exact sublem_4_2_2 n hp
    · exact sublem_4_2_3 n ngt1 hp


lemma choose_increasing (a b c : ℕ) : b ≥ c → (a+b).choose b ≥ (a+c).choose c := by
  intro h
  have hb : (a + b).choose b = (a + b).choose a := by
    rw [Nat.choose_symm_add]
  have hc : (a + c).choose c = (a + c).choose a := by
    rw [Nat.choose_symm_add]
  have h' : a + c ≤ a + b := Nat.add_le_add_left h a
  have h'' : (a + c).choose a ≤ (a + b).choose a := by
    exact Nat.choose_le_choose a h'
  rw [hb, hc]
  exact h''


lemma floor_le_iff (a : ℝ) (z : ℕ) (h : a ≥ 0) : Nat.floor a ≤ z ↔ a < z + 1 := by
  rw [← Nat.lt_add_one_iff, Nat.floor_lt]
  · norm_cast
  · exact h

lemma choose_two_pow_bound_helper (a : ℕ) (k : ℕ) (hk : a ≥ k) : (k+a+1)>2*k := by
  calc
    k+a+1 ≥ k + k + 1 := by
      rw [add_assoc, add_comm a, ←add_assoc]
      rw [add_assoc k k, add_comm k 1, ←add_assoc]
      apply Nat.add_le_add
      · linarith
      · exact hk
    _ = 2*k + 1 := by linarith
    _ > 2*k := by exact lt_add_one (2 * k)


lemma choose_two_pow_bound (a : ℕ) (h : a > 1) : (2*a+1).choose a > 2^(a+1) := by
  -- can use the following mathematical proof:
  -- (2a+1).choose a = (2a+1)(2a)...(a+2) / (a)(a-1)...(1)
  -- each pair (k+a+1)/k > 2 by choose_two_pow_bound_helper
  -- also the last pair (a+2)/1 >= 4 since a > 1
  -- there are a-1 of these first type of pairs, plus this last one
  -- so then get 2^(a-1) * 4 = 2^(a+1)
  sorry



-- gets used in calc step 2 and in step 4
lemma sqrt_t_gt_log_n (t n : ℕ) : √t > Real.logb 2 n := by
  -- since or (n) > log^2 n, t > log^2 n.
  -- or(n) > log^2 n is by definition of or(n)
  sorry

lemma sqrt_t_gt0 : √ t > 0 := by
  apply Real.sqrt_pos_of_pos
  exact Nat.cast_pos'.mpr t_gt_zero


lemma ell_ineq: ℓ ≥ Nat.floor (√t * Real.logb 2 sa.n) := by
  unfold ℓ
  have : sa.r.totient ≥ t := by sorry
  have h₁ : Real.sqrt (sa.r.totient) ≥ Real.sqrt t := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast this
  have hlog : 0 ≤ Real.logb 2 sa.n := by
    apply Real.logb_nonneg
    · norm_num
    · norm_cast
      apply Nat.one_le_of_lt sa.ngt1
  have ineq : Real.sqrt sa.r.totient * Real.logb 2 sa.n ≥ Real.sqrt t * Real.logb 2 sa.n := by
    exact mul_le_mul_of_nonneg_right h₁ hlog
  exact Nat.floor_le_floor ineq

  lemma calc_step1 (sa : Step5Assumptions) :
  (t+ℓ).choose (t-1) ≥  (ℓ + 1 + Nat.floor ((√t) * (Real.logb 2 sa.n))).choose (Nat.floor ((√t) * (Real.logb 2 sa.n))) := by
  have hineq: t - 1 ≥ Nat.floor (Real.sqrt t * Real.logb 2 sa.n) := by
    apply (floor_le_iff _ _ _).mpr
    · norm_cast
      rw [Nat.sub_add_cancel t_gt_zero, mul_comm]
      nth_rw 2 [←Real.sq_sqrt (Nat.cast_nonneg' t)]
      rw [pow_two]
      apply mul_lt_mul_of_pos_right
      · exact sqrt_t_gt_log_n t sa.n
      · exact sqrt_t_gt0 sa
    · rw [mul_comm]
      apply (mul_nonneg_iff_of_pos_right (sqrt_t_gt0 sa)).mpr
      apply Real.logb_nonneg
      · linarith
      · norm_cast
        exact Nat.one_le_of_lt sa.ngt1
  have : t + ℓ = ℓ + 1 + (t - 1) := by
    calc
      t + ℓ  = t + 1 + ℓ- 1 := by exact Eq.symm (Nat.succ_add_sub_one ℓ t)
      _ = ℓ + 1 + t - 1 := by ring_nf
      _ = ℓ + 1 + (t - 1) := by
        rw [←Nat.add_sub_assoc t_gt_zero]
  rw [this]
  apply choose_increasing
  exact hineq


lemma calc_step2 (sa : Step5Assumptions) :
  (ℓ + 1 + Nat.floor ((√t) * (Real.logb 2 sa.n))).choose (Nat.floor ((√t) * (Real.logb 2 sa.n))) ≥
      (2 * Nat.floor ((√t) * (Real.logb 2 sa.n))+1).choose (Nat.floor ((√t) * (Real.logb 2 sa.n))) := by
  let n_real : ℝ := ↑sa.n
  have he: ℓ + 1 + Nat.floor (√t * Real.logb 2 n_real) ≥  Nat.floor (√t * Real.logb 2 n_real) + (1 + Nat.floor (√t * Real.logb 2 n_real)) := by
    rw [add_assoc]
    apply Nat.add_le_add_right
    exact ell_ineq sa
  have : Nat.floor (√t * Real.logb 2 n_real) + (1 + Nat.floor (√t * Real.logb 2 n_real))  = (2 * Nat.floor ((√t) * (Real.logb 2 n_real))+1) := by
    ring_nf
  rw [←this]
  apply Nat.choose_le_choose (Nat.floor ((√t) * (Real.logb 2 n_real))) he

lemma calc_step3 (sa : Step5Assumptions):
  (2 * Nat.floor ((√t) * (Real.logb 2 sa.n))+1).choose (Nat.floor ((√t) * (Real.logb 2 sa.n))) >
      2 ^ ( (Nat.floor ((√t) * (Real.logb 2 sa.n))) + 1) := by

  have h1 : Nat.floor (Real.sqrt t * Real.logb 2 sa.n) > Nat.floor ( (Real.logb 2 sa.n)^2) := by
    calc
      Nat.floor (Real.sqrt t * Real.logb 2 sa.n) > Nat.floor (Real.logb 2 sa.n * Real.logb 2 sa.n) := by
        -- stronger statement than ≥. (Which is easy to do with sqrt_t_gt_log_n)
        sorry
      _ = Nat.floor ( (Real.logb 2 sa.n)^2) := by rw [pow_two]

  have : Nat.floor (Real.sqrt t * Real.logb 2 sa.n) > 1 := by
    have : Nat.floor ( (Real.logb 2 sa.n)^2 ) ≥ 1 := by
      apply (Nat.one_le_floor_iff (logb 2 ↑sa.n ^ 2)).mpr
      apply (sqrt_le_left _).mp
      · simp
        apply (Real.le_logb_iff_rpow_le _ _).mpr
        · simp
          apply sa.ngt1
        · norm_num
        · norm_cast
          apply Nat.zero_lt_of_lt sa.ngt1

      · apply (Real.le_logb_iff_rpow_le _ _).mpr
        · simp
          apply Nat.one_le_of_lt sa.ngt1
        · norm_num
        · norm_cast
          apply Nat.zero_lt_of_lt sa.ngt1

    calc
      Nat.floor (Real.sqrt t * Real.logb 2 sa.n) > Nat.floor ( (Real.logb 2 sa.n)^2) := by
        exact h1
      _ ≥ 1 := by
        exact this
  exact choose_two_pow_bound (Nat.floor (Real.sqrt t * Real.logb 2 sa.n)) this

lemma calc_step4 (n_real t_real : ℝ) (ngt1: n_real > 1) :↑(2 ^ ( (Nat.floor ((√t_real) * (Real.logb 2 n_real))) + 1)) ≥ n_real ^ √t_real := by
  have : ↑((Nat.floor ((√t_real) * (Real.logb 2 n_real))) + 1) > ((√t_real) * (Real.logb 2 n_real)) := by
      exact Nat.lt_succ_floor (√t_real * logb 2 n_real)
  have : (2:ℝ)^((√t_real) * (Real.logb (2:ℝ) n_real)) = (n_real)^√t_real := by
    rw [mul_comm, Real.rpow_mul, Real.rpow_logb]
    · norm_num
    · norm_num
    · linarith
    · norm_num
  rw [←this]
  have  (a:ℝ): (2:ℝ) ^ ((⌊a⌋₊ + 1) : ℝ) ≥ (2:ℝ) ^ (a) → (2:ℝ) ^ (⌊a⌋₊ + 1) ≥ (2:ℝ) ^ (a) := by
    norm_cast
    intro h
    exact h
  apply this
  apply Real.rpow_le_rpow_of_exponent_le
  · norm_num
  · apply le_of_lt
    apply Nat.lt_floor_add_one

lemma lemma_4_9_assumpts (sa : Step5Assumptions) (not_p_power: ¬perfect_power sa.n) : sa.n.Prime := by

  let n_real : ℝ := ↑sa.n
  let t_real : ℝ := ↑t

  -- part of the inequality that is entirely between naturals
  have hineq : (t+ℓ).choose (t-1) > 2 ^ ( (Nat.floor ((√t) * (Real.logb 2 sa.n))) + 1) := by
    calc
      (t+ℓ).choose (t-1) ≥  (ℓ + 1 + Nat.floor ((√t) * (Real.logb 2 n_real))).choose (Nat.floor ((√t) * (Real.logb 2 n_real))) := by
        exact calc_step1 sa

      _ ≥ (2 * Nat.floor ((√t) * (Real.logb 2 sa.n))+1).choose (Nat.floor ((√t) * (Real.logb 2 sa.n))) := by
        exact calc_step2 sa

      _ > 2 ^ ( (Nat.floor ((√t) * (Real.logb 2 sa.n))) + 1) := by
        exact calc_step3 sa

  have : ↑(2 ^ ( (Nat.floor ((√t) * (Real.logb 2 sa.n))) + 1)) ≥ n_real ^ √t_real := by
    have : n_real > 1 := by
      unfold n_real
      norm_cast
      exact sa.ngt1
    exact calc_step4 n_real t_real this


  -- conclusion of string of inequalities
  have card_bound : Nat.card 𝒢 > n_real^√t_real := by
    have : Nat.card 𝒢 > 2 ^ ( (Nat.floor ((√t) * (Real.logb 2 sa.n))) + 1) := by
      calc
        Nat.card 𝒢 ≥ (t + ℓ).choose (t - 1) := by exact lemma_4_7 sa
        _ > 2 ^ ( (Nat.floor ((√t) * (Real.logb 2 n_real))) + 1) := by exact hineq
    calc
      ↑(Nat.card 𝒢) > ↑(2 ^ ( (Nat.floor ((√t) * (Real.logb 2 n_real))) + 1)) := by
        norm_cast
      _ ≥ n_real^√t_real := by
        have hn : n_real > 1 := by
          unfold n_real
          norm_cast
          exact sa.ngt1
        exact calc_step4 n_real t_real hn

  have : is_power_of sa.n sa.p := by
    have : ¬is_power_of sa.n sa.p → Nat.card 𝒢 ≤ (n_real ^ √t_real) := by
      unfold n_real t_real
      exact lemma_4_8 sa
    by_contra not_power
    have : Nat.card 𝒢 ≤ n_real ^ √t_real := by exact this not_power
    linarith -- have that |𝒢| > n^√t and |𝒢| ≤ n^√t

  unfold is_power_of at this
  rcases this with ⟨k, hk⟩
  cases k with
  | zero =>
    simp at hk
    have : sa.n > 1 := by exact sa.ngt1
    linarith
  | succ k' =>
    cases k' with
    | zero =>
      simp at hk
      rw [←hk]
      exact sa.p_prime
    | succ k'' =>
      unfold perfect_power at not_p_power
      have isppow: ∃ k > 1, sa.n = sa.p^k := by
        use k'' + 2
        constructor
        · exact Nat.one_lt_succ_succ k''
        · apply Eq.symm
          exact hk
      by_contra _
      have h2 : ∃ a, ∃ b > 1, sa.n = a ^ b := by
        use sa.p
      exact not_p_power h2

lemma lemma_4_9 (n : ℕ) (ngt1 : n > 1) : AKS_algorithm n = PRIME → n.Prime := by
  -- in the paper lemma 4.9 starts with various assumptions on n and p
  -- these assumptions get introduced in the paper between the proof of lemma 4.3 and definition 4.4
  -- these assumptions deal with steps 1, 2, 3, 4 of the AKS algorithm
  -- so we can then assume these for the main bulk of the proof (lemma_4_9_assumpts)
  unfold AKS_algorithm
  intro aks_conditions
  simp at aks_conditions
  rcases aks_conditions with ⟨not_perfect_power, b⟩
  rcases b with ⟨no_a, hs5f⟩

  -- stated on page 7, below proof of 4.3
  have : ∃ p, p.Prime ∧ p ∣ n ∧ oᵣ (smallest_r n) p > 1 := by
    -- "since oᵣ (n) > 1"
    sorry

  rcases this with ⟨p, hp⟩

  -- need the assumption here that n is not prime, so that p satisfies the is_not_coprime_in_range condition (must be < n
  -- the proof is that if this were not the case, then steps 3 or 4 in the AKS algorithm would have already returned composite
  have hpr : ¬ n.Prime → p > smallest_r n := by
    intro hnotp
    by_contra p_less
    simp at p_less

    unfold is_not_coprime_in_range at no_a

    have : ∃ a ≤ smallest_r n, 1 < n.gcd a ∧ n.gcd a < n := by
      use p
      constructor
      · exact p_less
      · constructor
        · have : n.gcd p = p := by
            apply Nat.gcd_eq_right
            exact hp.right.left
          rw [this]
          apply Nat.Prime.one_lt hp.left
        · by_contra heq
          simp at heq
          have : n = p := by
            have : n ≥ n.gcd p := by
              apply Nat.gcd_le_left p
              exact Nat.zero_lt_of_lt ngt1
            have : n = n.gcd p := by
              exact Nat.le_antisymm heq this
            have : n ∣ p := by
              rw [this]
              apply Nat.gcd_dvd_right
            apply Nat.dvd_antisymm this hp.right.left
          have : n.Prime := by
            rw [this]
            exact hp.left
          exact hnotp this
    exact no_a this

  -- split into cases of n prime (in which case we are immediately done), or n not prime, in which case p > r
  have h_not_h: n.Prime ∨ ¬n.Prime := by exact Decidable.em (Nat.Prime n)

  cases h_not_h with
  | inl hprime => exact hprime
  | inr hnotprime =>
    have p_rel_r: p > smallest_r n := by exact hpr hnotprime

    have h_rgt0 : smallest_r n > 0 := by
      sorry --TODO

    have h_n_gcd_r : n.gcd (smallest_r n) = 1 := by
      -- used for two of the assumptions in Step5Assumptions
      by_contra rgcd
      unfold is_not_coprime_in_range at no_a
      have : ∃ a ≤ smallest_r n, 1 < n.gcd a ∧ n.gcd a < n := by
        use smallest_r n
        constructor
        · rfl
        · constructor
          · by_contra h1
            simp at h1
            have : n.gcd (smallest_r n) ≥ 1 := by
              exact Nat.gcd_pos_of_pos_left (smallest_r n) (Nat.zero_lt_of_lt ngt1)
            have : n.gcd (smallest_r n) = 1 := by
              exact Eq.symm (Nat.le_antisymm this h1)
            exact rgcd this
          · have h1 : n.gcd (smallest_r n) ≤ (smallest_r n) := by
              apply Nat.gcd_le_right (smallest_r n)
              exact h_rgt0
            have : smallest_r n < n := by
              calc
                smallest_r n < p := by exact p_rel_r
                _ ≤ n := by
                  apply Nat.le_of_dvd (Nat.zero_lt_of_lt ngt1) hp.right.left
            exact Nat.lt_of_le_of_lt h1 this
      exact no_a this

    let sa : Step5Assumptions := {
      r := smallest_r n -- : ℕ
      n := n -- : ℕ
      p := p -- : ℕ
      ngt1 := ngt1 -- : n > 1
      rgt0 := h_rgt0 -- 0 < r
      hrp := hp.right.right -- : 1 < oᵣ r p
      hn := h_n_gcd_r -- n.gcd r = 1
      pgtr := p_rel_r -- r < p
      p_prime := hp.left -- : p.Prime
      hp := by -- p.gcd r = 1 -- follows from hn?
        have hdiv : p.gcd (smallest_r n) ∣ n.gcd (smallest_r n) := by
          apply Nat.gcd_dvd_gcd_of_dvd_left (smallest_r n) hp.right.left
        have : n.gcd (smallest_r n) = 1 := by exact h_n_gcd_r
        rw [this] at hdiv
        exact Nat.eq_one_of_dvd_one hdiv
      p_dvd_n := hp.right.left -- : p ∣ n
    }

    apply lemma_4_9_assumpts sa not_perfect_power


theorem theorem_4_1 (n : ℕ) (ngt1 : n > 1) : n.Prime ↔ AKS_algorithm n = PRIME := by
  constructor
  · exact lemma_4_2 n ngt1
  · exact lemma_4_9 n ngt1
