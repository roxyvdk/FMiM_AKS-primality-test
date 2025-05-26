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
  rw [h_const]

  -- Converse: if the polynomial holds, then n is prime
  intro hpoly
  by_contra hnotprime
  obtain ⟨d, hd1, hd2, hdiv⟩ := Nat.exists_dvd_of_not_prime2 hn hnotprime
  -- Look at the coefficient of X^d

  have hcoeff : coeff ((X + C (a : ZMod n)) ^ n) d = (a : ZMod n) ^ (n - d) * (Nat.choose n d : ZMod n) := by
    apply Polynomial.coeff_X_add_C_pow
  have hcoeff_rhs : coeff (X ^ n + C (a : ZMod n)) d =(if d = n then 1 else 0)   + (if d = 0 then (a : ZMod n) else 0) := by
    simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C, hd1, hd2]
    rw [← Polynomial.coeff_C]
    rfl
  rw [hpoly] at hcoeff
  rw [hcoeff_rhs] at hcoeff
  have hd0 : d ≠ 0 := by linarith [hd2]
  have hdl0: d>0 := by linarith[hd2]
  have hdn : d ≠ n := by linarith [hd2]
  have hddn: d ≤ n-1 := sorry
  have hdd: 1 ≤ d := by linarith [hd2]
  rw [if_neg hdn, if_neg hd0] at hcoeff
  let a := (1 : ZMod n)
  rw[add_zero, eq_comm] at hcoeff
  have a_pow_nonzero : a ^ (n - d) = 1 := by
    exact one_pow (n - d)
  have d_in_range : 2 ≤ d ∧ d ≤ n - 1 := ⟨hd2, hddn⟩
  have hchoose : (Nat.choose n d : ZMod n) = 0 := by sorry
  simp [Int.modEq_zero_iff_dvd] at hchoose
  have not_dvd_choose : ¬ n ∣ Nat.choose n d := by sorry
  -- there must be a d sucht that this is true sorry
  have choosediv : n ∣ Nat.choose n d := by 
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd (n.choose d) n).mp hchoose
    --but if we have that the expression in hcoeff is zero then we have contradiction
  contradiction
lemma lem3_1 (n : ℕ) (hn : 7 ≤ n) : 4 ^ n ≤ (erase (range n) 0).lcm id := by
  sorry
def ord_r (a n : Nat) : Option Nat :=
  if Nat.gcd a n ≠ 1 then none
  else
    let ks := List.range (n+1) |>.drop 1
    ks.find? (λ k => a.pow k % n == 1)


lemma lemma_4_3 (n : ℕ) (h : 2 ≤ n) :
  ∃ r : ℕ, r ≤ max 3 (Nat.ceil ((Real.logb 2 n) ^ 5)) ∧ (ord_r n r).getD 0 > (Real.logb 2 n) ^ 2 := by
  by_cases hn : n = 2
  · -- Case: n = 2
    use 3
    have log_eq : Real.logb 2 2 = 1 := by simp
    have gcd_eq : Nat.gcd 2 3 = 1 := by norm_num
    have order_2_mod_3 : ord_r 2 3 = some 2 := by native_decide
    simp only [hn, log_eq, order_2_mod_3]
    norm_num
  · -- Case: n > 2
    let B := Nat.ceil ((Real.logb 2 n) ^ 5)


  -- Highlighted (from image): The largest value of k for any m^k ≤ B, m ≥ 2, is ⌊logₘ B⌋.
    have log_power_bound :
      ∀ m : ℕ, 2 ≤ m → ∀ k : ℕ, m ^ k ≤ B → k ≤ Nat.floor (Real.logb m B) := by
      intros m hm k hk
      have h_base : 1 < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hm
      -- Take logs: log m (m^k) ≤ log m B, so k ≤ log m B
      have hB_pos : 0 < (B : ℝ) := by
        have logn_pos : 0 < Real.logb 2 n := Real.logb_pos (by norm_num) (by exact_mod_cast lt_of_lt_of_le (by norm_num) h)
        have logn5_pos := pow_pos logn_pos 5
        exact_mod_cast Nat.ceil_pos.mpr logn5_pos
       -- m^k > 0

      have hmk_pos : 0 < (m : ℝ) ^ k := pow_pos (by linarith) k
      have hk_real : (m : ℝ) ^ k ≤ B := by exact_mod_cast hk
      have hm_pos : 0 < (m : ℝ) := by positivity
      let m_real : ℝ := ↑m
      let k_real : ℝ := ↑k

      -- Apply log inequality
      have hm_ne_one : (m : ℝ) ≠ 1 := by exact_mod_cast (ne_of_gt h_base)
      have hlog := (Real.logb_le_logb h_base hmk_pos hB_pos).mpr hk_real
      -- have hlog := Real.logb_le_logb h_base hmk_pos hB_pos hk_real
        -- Simplify logb m (m^k) = k
      have logb_m_mk : Real.logb m_real (m_real ^ k) = k := by
        rw [Real.logb_pow]
        rw [Real.logb_self_eq_one h_base]
        simp
      -- Finish the proof
      have hlog_k : k ≤ Real.logb m_real B := by
        rw[logb_m_mk] at  hlog
        exact hlog
      have hk_floor: k ≤  Nat.floor (Real.logb m B):= by
        have k_floor: k = Nat.floor k_real := by
          exact Eq.symm (floor_natCast k)
        rw[k_floor]
        apply Nat.floor_le_floor
        exact hlog_k
      exact hk_floor 
    let k := Nat.floor (Real.logb 2 B)
    let C := n ^ k - 1 
    have hk : 0 < k := sorry
    have C_ne_one : C ≠ 1 := sorry
    obtain ⟨p, hp_prime, hp_dvd⟩ :=  Nat.exists_prime_and_dvd C_ne_one
  -- Nat.isLeast_find
    have exists_r : ∃ r ≤ B, (ord_r n r).getD 0 > (Real.logb 2 n) ^ 2 := sorry

    obtain ⟨r, hrB, h_ord⟩ := exists_r

    use r
    constructor
    · exact le_sup_of_le_right hrB 
    · exact h_ord


class Step5Assumptions where
  r : ℕ
  n : ℕ
  p : ℕ
  rgt0 : 0 < r
  hrn : (logb 2 n) ^ 2 < oᵣ r n
  hrp : 1 < oᵣ r p
  hn : n.gcd r = 1
  pgtr : r < p
  p_prime : p.Prime
  hp : p.gcd r = 1
  p_dvd_n : p ∣ n
  ngt1 : 1 < n
  ngt0 : 0 < n := Nat.zero_lt_of_lt ngt1
  h_step_5 : ∀ (a : ℕ), a ≤ ℓ → AdjoinRoot.mk (X ^ r - 1) ((X + C (a : ZMod n) : (ZMod n)[X]) ^ n) = AdjoinRoot.mk (X ^ r - 1) ((X + C (a : ZMod n) : (ZMod n)[X]).comp (X ^ n))

section

variable [sa : Step5Assumptions]

lemma rgt1 : 1 < sa.r := by
  have rne1 : sa.r ≠ 1 := by
    intro req1
    have h₁ := req1 ▸ sa.hrp
    exact (lt_iff_not_le.mp h₁) orderOf_le_card_univ
  exact Nat.lt_of_le_of_ne sa.rgt0 rne1.symm

instance : NeZero sa.p := ⟨Nat.Prime.ne_zero sa.p_prime⟩

instance : NeZero sa.r := ⟨(ne_of_lt (Nat.zero_lt_of_lt rgt1)).symm⟩

instance : Fact (sa.p.Prime) := ⟨sa.p_prime⟩

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
        intro i _
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
  Submonoid.closure ((fun (i : ℕ) => (X + C (i : ZMod sa.p))) '' (range (ℓ + 1)))

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

lemma lemma_4_6' : ∀ m ∈ I, ∀ f ∈ P, introspective' m f := by
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

-- This theorem should really be in Mathlib already.
theorem mul_lt_mul_of_le_of_lt {a b c d : ℝ} (h₁ : a ≤ b) (h₂ : c < d) (h₃ : 0 < a) (h₄ : 0 ≤ c) :
    a * c < b * d :=
  ((mul_lt_mul_left h₃).mpr h₂).trans_le (mul_le_mul_of_nonneg_right h₁ (le_of_lt (lt_of_le_of_lt h₄ h₂)))

end Real

namespace Nat

-- This theorem should really be in Mathlib already.
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

namespace Set

-- This should really be in Mathlib
instance instNonemptyElemImage2 {α β γ : Type*} (f : α → β → γ) (s : Set α) (t : Set β) [sne : Nonempty s] [tne : Nonempty t]:
    Nonempty (Set.image2 f s t) := by
  rcases sne with ⟨x, xs⟩
  rcases tne with ⟨y, yt⟩
  use f x y, x, xs, y, yt

end Set

namespace AdjoinRoot

lemma of_rewrite {R : Type*} [CommRing R] (f : R[X]) (a : R) : AdjoinRoot.of f a = AdjoinRoot.mk f (C a) := rfl

end AdjoinRoot

-- Like the union of `Sym` for all `m ≤ n`.
def SymUnion (α : Type*) (n : ℕ) :=
  { s : Multiset α // Multiset.card s ≤ n }

namespace SymUnion
-- Some lemmas, definitions and instances mimicking those from `Sym`.

section

variable {α : Type*}

/-- The canonical map to `Multiset α` that forgets that `s` has length less then `n` -/
@[coe] def toMultiset {n : ℕ} (s : SymUnion α n) : Multiset α :=
  s.1

instance hasCoe (n : ℕ) : CoeOut (SymUnion α n) (Multiset α) :=
  ⟨SymUnion.toMultiset⟩

theorem coe_injective {n : ℕ} : Function.Injective ((↑) : SymUnion α n → Multiset α) :=
  Subtype.coe_injective

/-- Construct an element of the `n`th symmetric power from a multiset of cardinality `n`.
-/
@[match_pattern]
abbrev mk {n : ℕ} (m : Multiset α) (h : Multiset.card m ≤ n) : SymUnion α n :=
  ⟨m, h⟩

@[simp, norm_cast] lemma coe_mk {n : ℕ} (s : Multiset α) (h : Multiset.card s ≤ n) : mk s h = s := rfl

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (SymUnion α n) :=
  sorry

def Finset.biUnion' {α β : Type*} [DecidableEq β] [Fintype α] (t : α → Finset β) : Finset β :=
  Finset.biUnion univ t

-- Similar to Set.iUnion notation.
notation3 "⋃ᶠ "(...)", "r:60:(scoped f => Finset.biUnion' f) => r

theorem card_disjoint_union [DecidableEq α] (f : ℕ → Finset α) (k : ℕ) (hp : Pairwise (fun (a₁ a₂ : ℕ) => Disjoint (f a₁) (f a₂))) :
    Finset.card (⋃ᶠ m : range k, f m) = ∑ m : range k, (f m).card := by
  have hp' : ∀ x ∈ (@Finset.univ (range k) _), ∀ y ∈ (@Finset.univ (range k) _), x ≠ y → Disjoint (f x) (f y) := by
    intro x _ y _ xney
    have xney' : x.val ≠ y.val := by
      contrapose! xney
      exact Subtype.ext xney
    exact hp xney'
  exact Finset.card_biUnion hp'

noncomputable instance (k : ℕ) : DecidableEq (SymUnion α k) := by
  exact Classical.typeDecidableEq (SymUnion α k)

def univ_helper_f [Fintype α] [DecidableEq α] : ℕ → Finset (Multiset α) :=
  fun i => (Finset.map ⟨((↑) : Sym α i → Multiset α), Sym.coe_injective⟩ (@Finset.univ (Sym α i) _))

lemma univ_split [DecidableEq α] [Fintype α] (k : ℕ) : Finset.map ⟨((↑) : SymUnion α k → Multiset α), coe_injective⟩ (@Finset.univ (SymUnion α k) _) = ⋃ᶠ (i : range (k + 1)), (Finset.map ⟨((↑) : Sym α i → Multiset α), Sym.coe_injective⟩ (@Finset.univ (Sym α i) _)) := by
  ext x
  constructor
  · intro hx
    simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and] at hx
    rcases hx with ⟨y, rfl⟩
    apply Finset.mem_biUnion.mpr
    use ⟨(Multiset.card y.toMultiset), by
      simp only [mem_range]
      exact Nat.lt_succ_of_le y.prop⟩
    constructor
    · simp only [univ_eq_attach, mem_attach]
    · simp only [id_eq, eq_mpr_eq_cast, mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and]
      use ⟨y.toMultiset, rfl⟩
      simp only [Sym.coe_mk]
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, _, hxi⟩
    simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and] at hxi
    simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and]
    rcases hxi with ⟨y, rfl⟩
    use ⟨y, by
      calc
        Multiset.card y.toMultiset = i := y.prop
        _ ≤ k := by
          exact Nat.le_of_lt_add_one (Finset.mem_range.mp i.prop)⟩
    simp only [coe_mk]

lemma univ_disjoint [DecidableEq α] [Fintype α] : Pairwise (fun (i₁ i₂ : ℕ) => Disjoint (@univ_helper_f α _ _ i₁) (@univ_helper_f α _ _ i₂)) := by
  intro i₁ i₂ hi₁i₂
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  ext x
  constructor
  · intro hx
    by_contra
    rcases Finset.mem_inter.mp hx with ⟨hxi₁, hxi₂⟩
    unfold univ_helper_f at *
    simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and] at hxi₁
    simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and] at hxi₂
    rcases hxi₁ with ⟨y₁, hy₁⟩
    rcases hxi₂ with ⟨y₂, hy₂⟩
    have i₁eqi₂ : i₁ = i₂ := by
      calc
        i₁ = Multiset.card y₁.toMultiset := y₁.prop.symm
        _ = Multiset.card x := by rw [hy₁]
        _ = Multiset.card y₂.toMultiset := by rw [hy₂]
        _ = i₂ := y₂.prop
    exact hi₁i₂ i₁eqi₂
  · tauto

theorem card_sym_union_eq_choose [DecidableEq α] [Fintype α] [Nonempty α] (k : ℕ) :
    Fintype.card (SymUnion α k) = (Fintype.card α + k).choose k := by
  have card_α_pos : 0 < Fintype.card α := Fintype.card_pos
  calc
    Fintype.card (SymUnion α k) = Finset.card (@Finset.univ (SymUnion α k) _) := by
      simp only [card_univ]
    _ = Finset.card (Finset.map ⟨((↑) : SymUnion α k → Multiset α), coe_injective⟩ (@Finset.univ (SymUnion α k) _)) := by
      simp only [card_univ, card_map]
    _ = Finset.card (⋃ᶠ (i : range (k + 1)), (Finset.map ⟨((↑) : Sym α i → Multiset α), Sym.coe_injective⟩ (@Finset.univ (Sym α i) _))) := by
      rw [univ_split]
    _ = ∑ (i : range (k + 1)), Finset.card (Finset.map ⟨((↑) : Sym α i → Multiset α), Sym.coe_injective⟩ (@Finset.univ (Sym α i) _)) := by
      exact @card_disjoint_union (Multiset α) _ univ_helper_f (k + 1) univ_disjoint
    _ = ∑ (i : range (k + 1)), Finset.card (@Finset.univ (Sym α i) _) := by
      simp only [card_map]
    _ = ∑ (i : range (k + 1)), Fintype.card (Sym α i) := by
      simp only [card_univ]
    _ = ∑ (i ∈ range (k + 1)), Fintype.card (Sym α i) := by
      simp only [univ_eq_attach]
      have h₁ : ∑ i ∈ (range (k + 1)).attach, Fintype.card (Sym α ↑i) = ∑ i ∈ (range (k + 1)), Fintype.card (Sym α i) := by
        convert @Finset.sum_attach ℕ ℕ _ (range (k + 1)) (fun i => Fintype.card (Sym α ↑i))
      rw [h₁]
    _ = ∑ (i ∈ range (k + 1)), (Fintype.card α + i - 1).choose i := by
      simp_rw [Sym.card_sym_eq_choose]
    _ = ∑ (i ∈ range (k + 1)), (i + (Fintype.card α - 1)).choose (Fintype.card α - 1) := by
      simp_rw [add_comm (Fintype.card α), Nat.add_sub_assoc (Nat.one_le_of_lt card_α_pos) _, @Nat.choose_symm_add _ (Fintype.card α - 1)]
    _ = (k + (Fintype.card α - 1) + 1).choose ((Fintype.card α - 1) + 1) := by
      exact Nat.sum_range_add_choose k (Fintype.card α - 1)
    _ = (Fintype.card α + k).choose k := by
      rw [add_assoc, Nat.sub_add_cancel (Nat.one_le_of_lt card_α_pos), add_comm, Nat.choose_symm_add]

end

end SymUnion

-- This lemma should really be in Mathlib already.
lemma exists_natural_m_in_same_modulo_class (i : ℤ) {n : ℕ} (hn : n ≠ 0): ∃ m : ℕ, ∃ k : ℤ, i = m + k * n := by
  use (i % n).toNat
  rw [Int.toNat_of_nonneg (Int.emod_nonneg i (by exact_mod_cast hn))]
  use i / n
  exact (Int.emod_add_ediv' i n).symm

lemma pos_power_of_finite_order {G : Type*} [Group G] [Fintype G] (i : ℤ) (x : G) :
    ∃ n : ℕ, x ^ i = x ^ n := by
  rcases exists_natural_m_in_same_modulo_class i (ne_of_lt (orderOf_pos x)).symm with ⟨n, ⟨k, rfl⟩⟩
  use n
  rw [zpow_add, mul_comm, zpow_mul]
  simp only [zpow_natCast, mul_right_eq_self, pow_orderOf_eq_one, one_zpow]

lemma zmod_val_cast (r i : ℕ) : ∃ k : ℕ, i = (i : ZMod r).val + k * r := by
  simp only [ZMod.val_natCast]
  use i / r
  exact (Nat.mod_add_div' i r).symm

namespace Lemma78

lemma elem_in_set_imp_in_closure {G : Type*} [Monoid G] {S : Set G} {x : G} (hx : x ∈ S) : x ∈ Submonoid.closure S :=
  Submonoid.mem_closure.mpr fun _ a => a hx

lemma not_inj_of_card_le_card {α β : Type*} [Finite β] (h2 : Nat.card β < Nat.card α) (f : α → β) : ¬Function.Injective f :=
  fun hf => not_le_of_lt h2 (Nat.card_le_card_of_injective f hf)

section

variable [sa : Step5Assumptions]

noncomputable def Qᵣ := cyclotomic sa.r (ZMod sa.p)

lemma Qᵣ_not_unit : ¬IsUnit Qᵣ := not_isUnit_of_degree_pos Qᵣ (degree_cyclotomic_pos sa.r _ sa.rgt0)

noncomputable def h : (ZMod sa.p)[X] := Qᵣ.factor

lemma h_not_zero : h ≠ 0 := Irreducible.ne_zero (irreducible_factor Qᵣ)

instance h_irr : Fact (Irreducible h) := fact_irreducible_factor Qᵣ

instance adjoin_h_finite_generated : Module.Finite (ZMod sa.p) (AdjoinRoot h) :=
  PowerBasis.finite (AdjoinRoot.powerBasis h_not_zero)

instance adjoin_h_finite : Finite (AdjoinRoot h) :=
  Module.finite_of_finite (ZMod sa.p)

noncomputable instance : Fintype (AdjoinRoot h) :=
  Fintype.ofFinite (AdjoinRoot h)

lemma h_dvd_x_pow_r_minus_one : h ∣ (X ^ sa.r - 1) :=
  dvd_trans (factor_dvd_of_not_isUnit Qᵣ_not_unit) (cyclotomic.dvd_X_pow_sub_one sa.r (ZMod sa.p))

instance : NeZero (sa.r : AdjoinRoot h) := by
  apply neZero_iff.mpr
  intro hr
  apply AdjoinRoot.mk_eq_zero.mp at hr
  have r_degree : (sa.r : (ZMod sa.p)[X]).natDegree = 0 := Polynomial.natDegree_natCast sa.r
  replace hr := eq_zero_of_dvd_of_natDegree_lt hr (r_degree ▸ Irreducible.natDegree_pos h_irr.out)
  have r_casts : (sa.r : (ZMod sa.p)[X]) = C (sa.r : ZMod sa.p) := by
    simp only [map_natCast]
  rw [r_casts] at hr
  apply Polynomial.C_eq_zero.mp at hr
  apply (ZMod.natCast_zmod_eq_zero_iff_dvd sa.r sa.p).mp at hr
  have peq1 := Nat.Coprime.eq_one_of_dvd sa.hp hr
  exact Nat.Prime.ne_one sa.p_prime peq1

lemma map_mk_cyclo_eq_map_of_cyclo : (Polynomial.map (AdjoinRoot.mk h) (cyclotomic sa.r (ZMod sa.p)[X])) = (Polynomial.map (AdjoinRoot.of h) (cyclotomic sa.r (ZMod sa.p))) := by
  simp only [map_cyclotomic]

theorem X_primitive_root : IsPrimitiveRoot (AdjoinRoot.mk h X) sa.r := by
  rw [← Polynomial.isRoot_cyclotomic_iff, ← map_cyclotomic sa.r (AdjoinRoot.mk h)]
  simp only [AdjoinRoot.mk_X]
  rw [map_mk_cyclo_eq_map_of_cyclo]
  refine Polynomial.IsRoot.dvd ?_ (Polynomial.map_dvd (AdjoinRoot.of h) (factor_dvd_of_not_isUnit Qᵣ_not_unit))
  apply AdjoinRoot.isRoot_root

def G : Set (ZMod sa.r) := (fun (i : ℕ) => (i : ZMod sa.r)) '' I

def G' : Subgroup (ZMod sa.r)ˣ :=
  Subgroup.closure {ZMod.unitOfCoprime sa.n sa.hn, ZMod.unitOfCoprime sa.p sa.hp}

instance : Nonempty I := by
  --`infer_instance` does not work, even though this is an instance.
  apply Set.instNonemptyElemImage2

instance : Nonempty G := by
  --`infer_instance` does not work, even though this is an instance.
  apply Set.instNonemptyElemImage

noncomputable def t : ℕ := Nat.card G

lemma tgt0 : 0 < t := Finite.card_pos

noncomputable def 𝒢 : Submonoid (AdjoinRoot h) :=
  Submonoid.closure ((fun (i : ℕ) => (AdjoinRoot.mk h (X + C (i : ZMod sa.p)))) '' (range (ℓ + 1)))

noncomputable def 𝒢₂ : Submonoid (AdjoinRoot h) :=
  Submonoid.map (AdjoinRoot.mk h) P

lemma 𝒢_is_𝒢₂ : 𝒢 = 𝒢₂ := by
  unfold 𝒢 𝒢₂ P
  rw [MonoidHom.map_mclosure (AdjoinRoot.mk h) ((fun (i : ℕ) => (X + C (i : ZMod sa.p))) '' (range (ℓ + 1)))]
  rw [← Set.image_comp]
  simp only [Function.comp_apply]

def is_power_of (a b : ℕ) : Prop :=
  ∃ k, b ^ k = a

def f₁ : SymUnion (Fin (ℓ + 1)) (t - 1) → Multiset (ZMod sa.p) :=
  fun M => M.toMultiset

def f₂ : Multiset (ZMod sa.p) → Multiset (ZMod sa.p) :=
  Multiset.map (fun i => -i)

noncomputable def f₃ : Multiset (ZMod sa.p) → (ZMod sa.p)[X] :=
  fun M => (Multiset.map (fun i => (X - C i)) M).prod

noncomputable def lemma_4_7_helper_f : SymUnion (Fin (ℓ + 1)) (t - 1) → (AdjoinRoot h) :=
  (AdjoinRoot.mk h) ∘ f₃ ∘ f₂ ∘ f₁

lemma mk_f₃_eq_f₃_mk (M : SymUnion (Fin (ℓ + 1)) (t - 1)) :
    ((AdjoinRoot.mk h) ∘ f₃ ∘ f₂ ∘ f₁) M = ((fun N => (Multiset.map (fun i => AdjoinRoot.mk h (X - C i)) N).prod) ∘ f₂ ∘ f₁) M := by
  unfold f₃
  simp only [map_multiset_prod, Multiset.map_map, Function.comp_apply]

lemma f₁f₂f₃_degree (M : SymUnion (Fin (ℓ + 1)) (t - 1)) : ((f₃ ∘ f₂ ∘ f₁) M).natDegree < t := by
  calc
    ((f₃ ∘ f₂ ∘ f₁) M).natDegree = Multiset.card M.toMultiset := by
      unfold f₃ f₂ f₁
      simp only [Function.comp_apply, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
    _ < t := by
      exact Nat.lt_of_le_pred tgt0 M.prop

lemma f₁f₂f₃_in_P (M : SymUnion (Fin (ℓ + 1)) (t - 1)) : ((f₃ ∘ f₂ ∘ f₁) M) ∈ P := by
  unfold f₂ f₁
  apply Submonoid.multiset_prod_mem
  intro c hc
  apply elem_in_set_imp_in_closure
  simp only [Sym.mem_coe, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Function.comp_apply,
    Multiset.map_map, Multiset.mem_map, exists_exists_and_eq_and, map_neg, sub_neg_eq_add] at hc
  simp only [coe_range, Set.mem_image, Set.mem_Iio]
  rcases hc with ⟨d, _, hd⟩
  use d, Fin.is_lt d

lemma f₂_inj : Function.Injective f₂ := fun _ _ hxy => (Multiset.map_injective neg_injective) hxy

lemma sqrt_totient_r_le_sqrt_r : √sa.r.totient ≤ √sa.r := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.totient_le sa.r

lemma oᵣ_lt_r : oᵣ sa.r sa.n ≤ sa.r := by
  calc
    oᵣ sa.r sa.n ≤ Fintype.card (ZMod sa.r) := orderOf_le_card_univ
    _ = sa.r := ZMod.card sa.r

lemma log_n_lt_sqrt_r : logb 2 sa.n < √sa.r := by
  apply Real.lt_sqrt_of_sq_lt
  calc
    (logb 2 sa.n) ^ 2 < oᵣ sa.r sa.n := sa.hrn
    _ ≤ sa.r := by exact_mod_cast oᵣ_lt_r

lemma ℓltr : (ℓ : ℝ) < sa.r := by
  calc
    (ℓ : ℝ) ≤ √sa.r.totient * logb 2 sa.n := by
      unfold ℓ
      apply Nat.floor_le
      apply mul_nonneg
      · exact sqrt_nonneg Step5Assumptions.r.totient
      · apply logb_nonneg (by norm_num)
        exact_mod_cast sa.ngt0
    _ < √sa.r * √sa.r := by
      apply Real.mul_lt_mul_of_le_of_lt
      · exact sqrt_totient_r_le_sqrt_r
      · exact log_n_lt_sqrt_r
      · apply sqrt_pos_of_pos
        exact_mod_cast Nat.totient_pos.mpr sa.rgt0
      · apply logb_nonneg (by norm_num)
        exact_mod_cast sa.ngt0
    _ = sa.r := by
      exact mul_self_sqrt (Nat.cast_nonneg Step5Assumptions.r)

lemma ℓltp : ℓ < sa.p := by
  calc
    ℓ < sa.r := by exact_mod_cast ℓltr
    _ < sa.p := sa.pgtr

lemma cast_of_cast_of_val_eq_id (n : Fin (ℓ + 1)) : (ZMod.cast ((n : ℕ) : ZMod sa.p) : Fin (ℓ + 1)) = n := by
  rw [ZMod.cast_eq_val]
  simp only [ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_of_lt_succ n.prop) ℓltp)]
  simp only [Fin.cast_val_eq_self]

lemma f₁_inj : Function.Injective f₁ := by
  intro x y hxy
  unfold f₁ at hxy
  simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton] at hxy
  have h₁ : Function.Injective (fun (x : Fin (ℓ + 1)) => ((x : ℕ) : ZMod sa.p)) := by
    intro a b hab
    simp only at hab
    apply_fun @ZMod.cast (Fin (ℓ + 1)) at hab
    rwa [cast_of_cast_of_val_eq_id, cast_of_cast_of_val_eq_id] at hab
  apply (Multiset.map_injective h₁) at hxy
  exact SymUnion.coe_injective hxy

lemma f₁f₂f₃_inj {M N : SymUnion (Fin (ℓ + 1)) (t - 1)} (MneqN : M ≠ N) :
    (f₃ ∘ f₂ ∘ f₁) M ≠ (f₃ ∘ f₂ ∘ f₁) N := by
  contrapose! MneqN
  unfold f₃ at *
  simp only [Function.comp_apply] at MneqN
  apply_fun (fun p => p.roots) at MneqN
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at MneqN
  apply f₂_inj at MneqN
  exact f₁_inj MneqN

def I_hat_fun : Fin (⌊√t⌋₊ + 1) → Fin (⌊√t⌋₊ + 1) → ℕ :=
  fun i => fun j => (sa.n / sa.p) ^ (i : ℕ) * sa.p ^ (j : ℕ)

noncomputable def I_hat : Finset ℕ :=
  Finset.image₂ I_hat_fun (@Finset.univ (Fin (⌊√t⌋₊ + 1)) _) (@Finset.univ (Fin (⌊√t⌋₊ + 1)) _)

lemma I_hat_in_I {m : ℕ} : m ∈ I_hat → m ∈ I := by
  intro hm
  rcases Finset.mem_image₂.mp hm with ⟨i, _, j, _, hij⟩
  use i, trivial, j, trivial, hij

def introspective'' (m : ℕ) (f : (ZMod sa.p)[X]) : Prop :=
  AdjoinRoot.mk h (f ^ m) = AdjoinRoot.mk h (f.comp (X ^ m))

lemma lemma_4_6'' {m : ℕ} {f : (ZMod sa.p)[X]} (m_in_I : m ∈ I) (f_in_P : f ∈ P) :
  introspective'' m f := by
  have hi := lemma_4_6' m m_in_I f f_in_P
  unfold introspective'' introspective' at *
  simp only [AdjoinRoot.mk_eq_mk] at *
  exact dvd_trans h_dvd_x_pow_r_minus_one hi

lemma I_coprime_r {x : ℕ} (hx : x ∈ I) : x.Coprime sa.r := by
  rcases Set.mem_image2.mp hx with ⟨i, _, j, _, hij⟩
  unfold I_fun at hij
  rw [← hij]
  apply Nat.Coprime.mul
  · apply Nat.Coprime.pow_left
    exact Nat.Coprime.coprime_div_left sa.hn sa.p_dvd_n
  · apply Nat.Coprime.pow_left
    exact sa.hp

lemma I_rewrite' (i j : ℕ) : (sa.n / sa.p) ^ (i : ℕ) * sa.p ^ (i : ℕ) * sa.p ^ (j : ℕ) =
    sa.n ^ (i : ℕ) * sa.p ^ (j : ℕ) := by
  rw [Nat.div_pow sa.p_dvd_n, Nat.div_mul_cancel (pow_dvd_pow_of_dvd sa.p_dvd_n i)]

lemma I_rewrite {x : ℕ} (hx : x ∈ I) :
  ∃ i j : ℤ, (ZMod.unitOfCoprime sa.n sa.hn) ^ i * (ZMod.unitOfCoprime sa.p sa.hp) ^ j = ZMod.unitOfCoprime x (I_coprime_r hx) := by
  rcases Set.mem_image2.mp hx with ⟨i, _, j, _, hij⟩
  unfold I_fun at *
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
  rw [I_rewrite' i j]

lemma G_eq_G' : G = Units.val '' G'.carrier := by
  ext x
  constructor
  · rintro ⟨k, k_in_I, rfl⟩
    simp only [Set.mem_image, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
      Subgroup.mem_toSubmonoid]
    unfold G'
    simp [Subgroup.mem_closure_pair]
    rcases I_rewrite k_in_I with ⟨i, j, hij⟩
    use i, j
    norm_cast
    rw [hij]
    simp only [ZMod.coe_unitOfCoprime]
  · rintro ⟨k, hk, rfl⟩
    rcases Subgroup.mem_closure_pair.mp hk with ⟨i, j, rfl⟩
    push_cast
    rcases pos_power_of_finite_order i (ZMod.unitOfCoprime sa.n sa.hn) with ⟨i', hi'⟩
    rcases pos_power_of_finite_order j (ZMod.unitOfCoprime sa.p sa.hp) with ⟨j', hj'⟩
    rw [hi', hj']
    simp [Units.val_pow_eq_pow_val]
    norm_cast
    rw [← I_rewrite']
    use ((Step5Assumptions.n / Step5Assumptions.p) ^ i' * Step5Assumptions.p ^ i' * Step5Assumptions.p ^ j')
    simp only [Nat.cast_mul, Nat.cast_pow, and_true]
    rw [mul_assoc, ← pow_add]
    use i', trivial, i' + j', trivial
    rfl

lemma card_G_eq_card_G' : Nat.card G = Nat.card G' := by
  rw [G_eq_G', Nat.card_image_of_injective Units.ext]
  exact rfl

noncomputable def Q_helper (f : (ZMod sa.p)[X]) : (AdjoinRoot h)[X] := Polynomial.map (AdjoinRoot.of h) f

lemma Q_helper_support (f : (ZMod sa.p)[X]) : (Q_helper f).support = f.support := by
  unfold Q_helper
  apply support_map_of_injective f
  exact AdjoinRoot.coe_injective'

lemma Q_helper_coeff (f : (ZMod sa.p)[X]) (n : ℕ) : (Q_helper f).coeff n = f.coeff n := by
  unfold Q_helper
  simp only [coeff_map]

lemma Q_helper_eval (f a : (ZMod sa.p)[X]) : eval (AdjoinRoot.mk h a) (Q_helper f) = AdjoinRoot.mk h (f.comp a) := by
  unfold Polynomial.eval Polynomial.comp
  rw [Polynomial.eval₂_def, Polynomial.eval₂_def]
  simp only [RingHom.id_apply]
  unfold Polynomial.sum
  simp_rw [Q_helper_support, Q_helper_coeff, AdjoinRoot.of_rewrite, ← RingHom.map_pow, ← RingHom.map_mul, ← map_sum]

noncomputable def Q (f g : (ZMod sa.p)[X]) := Q_helper (f - g)

lemma Q_degree {f g : (ZMod sa.p)[X]} (hf : f.natDegree < t) (hg : g.natDegree < t) : (Q f g).natDegree < t := by
  calc
    (Polynomial.map (AdjoinRoot.of h) (f - g)).natDegree ≤ (f - g).natDegree := Polynomial.natDegree_map_le (AdjoinRoot.of h) (f - g)
    _ ≤ max (t - 1) (t - 1) := Polynomial.natDegree_sub_le_of_le (Nat.le_sub_one_of_lt hf) (Nat.le_sub_one_of_lt hg)
    _ < t := Nat.max_lt.mpr ⟨Nat.sub_one_lt_of_lt hf, Nat.sub_one_lt_of_lt hf⟩

noncomputable def G_power_function : G → (AdjoinRoot h) :=
  fun g => AdjoinRoot.mk h X ^ (g.val.val : ℕ)

lemma G_power_function_injective : Function.Injective G_power_function := by
  unfold G_power_function
  intro x y hxy
  simp only at hxy
  have x_val_val_val_lt_r : x.val.val < sa.r := ZMod.val_lt x.val
  have y_val_val_val_lt_r : y.val.val < sa.r := ZMod.val_lt y.val
  apply IsPrimitiveRoot.pow_inj X_primitive_root x_val_val_val_lt_r y_val_val_val_lt_r at hxy
  apply_fun ((↑) : ℕ → ZMod sa.r) at hxy
  simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at hxy
  exact Subtype.ext hxy

noncomputable instance : Fintype (Set.range G_power_function) := Fintype.ofFinite _

lemma x_pow_r_eq_1 : AdjoinRoot.mk h (X ^ sa.r) = 1 := by
  apply (@sub_left_inj _ _ 1 (AdjoinRoot.mk h (X ^ sa.r)) 1).mp
  rw [sub_self]
  exact AdjoinRoot.mk_eq_zero.mpr h_dvd_x_pow_r_minus_one

lemma Q_roots {f g : (ZMod sa.p)[X]} (f_in_P : f ∈ P) (g_in_P : g ∈ P) (fneg : f ≠ g) (feqg : (AdjoinRoot.mk h) f = (AdjoinRoot.mk h) g) :
    (Set.range G_power_function).toFinset.val ≤ (Q f g).roots := by
  apply Multiset.le_iff_count.mpr
  intro a
  by_cases ha : a ∈ (Set.range G_power_function).toFinset
  · have Qneq0 : Q f g ≠ 0 := by
      unfold Q Q_helper
      intro hfg
      apply (Polynomial.map_eq_zero_iff AdjoinRoot.coe_injective').mp at hfg
      rw [sub_eq_zero] at hfg
      exact fneg hfg
    have haQ : a ∈ (Q f g).roots := by
      apply (Polynomial.mem_roots_iff_aeval_eq_zero Qneq0).mpr
      unfold Q
      rw [Polynomial.coe_aeval_eq_eval]
      simp only [Set.mem_toFinset, Set.mem_range, Subtype.exists] at ha
      rcases ha with ⟨k, ⟨i, i_in_I, rfl⟩, rfl⟩
      have X_pow_i_cast_val_eq_X_pow : AdjoinRoot.mk h (X ^ (i : ZMod sa.r).val) = AdjoinRoot.mk h (X ^ i) := by
        rcases zmod_val_cast sa.r i with ⟨k, hk⟩
        nth_rw 2 [hk]
        rw [pow_add, map_mul, mul_comm k, pow_mul, map_pow (AdjoinRoot.mk h) (X ^ sa.r), x_pow_r_eq_1, one_pow, mul_one]
      unfold G_power_function
      simp only
      rw [← map_pow, X_pow_i_cast_val_eq_X_pow, Q_helper_eval]
      have f_i_introspective := lemma_4_6'' i_in_I f_in_P
      have g_i_introspective := lemma_4_6'' i_in_I g_in_P
      unfold introspective'' at *
      simp only [sub_comp, map_sub]
      calc
        (AdjoinRoot.mk h) (f.comp (X ^ i)) - (AdjoinRoot.mk h) (g.comp (X ^ i)) = (AdjoinRoot.mk h) (f ^ i) - (AdjoinRoot.mk h) (g ^ i) := by
          rw [f_i_introspective, g_i_introspective]
        _ = (AdjoinRoot.mk h f) ^ i - (AdjoinRoot.mk h g) ^ i := by
          rw [map_pow, map_pow]
        _ = 0 := by
          rw [feqg, sub_self]
    calc
      Multiset.count a (Set.range G_power_function).toFinset.val = 1 := Multiset.count_eq_one_of_mem (Finset.nodup (Set.range G_power_function).toFinset) ha
      _ ≤ Multiset.count a (Q f g).roots := Multiset.one_le_count_iff_mem.mpr haQ
  · calc
      Multiset.count a (Set.range G_power_function).toFinset.val = 0 := Multiset.count_eq_zero.mpr ha
      _ ≤ Multiset.count a (Q f g).roots := Nat.zero_le _

lemma degree_lt_t_inj {f g : (ZMod sa.p)[X]} (f_in_P : f ∈ P) (g_in_P : g ∈ P) (hf : f.natDegree < t) (hg : g.natDegree < t) (fneg : f ≠ g) :
    AdjoinRoot.mk h f ≠ AdjoinRoot.mk h g := by
  by_contra! feqg
  have Qdegree_ge_t : t ≤ (Q f g).natDegree := by
    calc
      t = Nat.card G := rfl
      _ = Nat.card (Set.range G_power_function) := (Nat.card_range_of_injective G_power_function_injective).symm
      _ = Finset.card (Set.range G_power_function).toFinset := Nat.card_eq_card_toFinset (Set.range G_power_function)
      _ = Multiset.card (Set.range G_power_function).toFinset.val := Finset.card_def (Set.range G_power_function).toFinset
      _ ≤ Multiset.card (Q f g).roots := Multiset.card_le_card (Q_roots f_in_P g_in_P fneg feqg)
      _ ≤ (Q f g).natDegree := Polynomial.card_roots' (Q f g)
  exact lt_iff_not_le.mp (Q_degree hf hg) Qdegree_ge_t

lemma lemma_4_7_helper_f_injective :
    Function.Injective lemma_4_7_helper_f := by
  intro x y hfxy
  unfold lemma_4_7_helper_f at *
  by_contra! xney
  exact degree_lt_t_inj (f₁f₂f₃_in_P x) (f₁f₂f₃_in_P y) (f₁f₂f₃_degree x) (f₁f₂f₃_degree y) (f₁f₂f₃_inj xney) hfxy

noncomputable instance 𝒢_fintype : Fintype ↑𝒢.carrier := Fintype.ofFinite ↑𝒢.carrier

lemma lemma_4_7_helper_f_image :
    (Finset.image lemma_4_7_helper_f univ : Finset ((AdjoinRoot h))) ⊆ Set.toFinset 𝒢.carrier := by
  unfold 𝒢 lemma_4_7_helper_f
  simp only [Set.image_univ, coe_image, coe_univ, Set.subset_toFinset]
  rintro x ⟨y, rfl⟩
  simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, mk_f₃_eq_f₃_mk]
  unfold f₂ f₁
  simp only [coe_range, Function.comp_apply, map_natCast, map_add, AdjoinRoot.mk_X, Multiset.pure_def, Multiset.bind_def,
    Multiset.bind_singleton, Multiset.map_map, Function.comp_apply, map_sub, AdjoinRoot.mk_C,
    map_neg, sub_neg_eq_add]
  apply Submonoid.multiset_prod_mem
  intro c hc
  apply elem_in_set_imp_in_closure
  simp only [Multiset.mem_map, Sym.mem_coe] at hc
  simp only [coe_range, Set.mem_image, Set.mem_Iio]
  rcases hc with ⟨d, _, hd⟩
  use d, Fin.is_lt d

lemma lemma_4_7' : Nat.card 𝒢 ≥ (t + ℓ).choose (t - 1) := by
  calc
    (t + ℓ).choose (t - 1) = (ℓ + 1 + (t - 1)).choose (t - 1) := by congr 1; have := tgt0; omega
    _ = (Fintype.card (Fin (ℓ + 1)) + (t - 1)).choose (t - 1) := by rw [Fintype.card_fin]
    _ = Fintype.card (SymUnion (Fin (ℓ + 1)) (t - 1)) := (SymUnion.card_sym_union_eq_choose (t - 1)).symm
    _ = (@univ (SymUnion (Fin (ℓ + 1)) (t - 1)) _).card := rfl
    _ = (Finset.image lemma_4_7_helper_f univ : Finset ((AdjoinRoot h))).card :=
      (Finset.card_image_of_injective univ lemma_4_7_helper_f_injective).symm
    _ ≤ (Set.toFinset 𝒢.carrier).card := Finset.card_le_card lemma_4_7_helper_f_image
    _ = Nat.card 𝒢.carrier.toFinset := (Nat.card_eq_finsetCard (Set.toFinset 𝒢.carrier)).symm
    _ = Nat.card 𝒢 := by congr; simp only [Set.mem_toFinset, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid]

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
    exact Nat.pow_succ_factorization_not_dvd (ne_of_lt sa.ngt0).symm sa.p_prime hq
  use q, q_prime, q_coprime_p
  apply Nat.Prime.factorization_pos_of_dvd q_prime (ne_of_lt sa.ngt0).symm
  exact dvd_trans (Nat.dvd_mul_left q _) hq

lemma n_div_p_pos : 0 < sa.n / sa.p := (Nat.div_pos (Nat.le_of_dvd sa.ngt0 sa.p_dvd_n) (Nat.Prime.pos sa.p_prime))

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
    apply Nat.mul_left_cancel (pow_pos (Nat.div_pos (Nat.le_of_dvd sa.ngt0 sa.p_dvd_n) (Nat.Prime.pos sa.p_prime)) j₁) at heq
    exact heq
  have i₂eqj₂ : (i₂ : ℕ) = j₂ := Nat.pow_right_injective (Nat.Prime.two_le sa.p_prime) p_pow_eq
  constructor
  · exact Fin.eq_of_val_eq i₁eqj₁
  · exact Fin.eq_of_val_eq i₂eqj₂

def I_hat_proj_fun : I_hat → G' :=
  fun x => ⟨ZMod.unitOfCoprime x.val (I_coprime_r (I_hat_in_I x.prop)), (Subgroup.mem_closure_pair.mpr (I_rewrite (I_hat_in_I x.prop)))⟩

lemma floor_sqrt_ineq : (⌊√t⌋₊ + 1) * (⌊√t⌋₊ + 1) > (t : ℝ) := by
  calc
    (⌊√t⌋₊ + 1) * (⌊√t⌋₊ + 1) > √t * √t := mul_self_lt_mul_self (sqrt_nonneg ↑t) (Nat.lt_floor_add_one √↑t)
    _ = t := mul_self_sqrt (by exact_mod_cast le_of_lt tgt0)

lemma card_G_lt_card_I_hat (not_p_power : ¬is_power_of sa.n sa.p) : Nat.card I_hat > Nat.card G := by
  calc
    Nat.card I_hat = Finset.card I_hat := Nat.card_eq_finsetCard I_hat
    _ = Finset.card (@Finset.univ (Fin (⌊√t⌋₊ + 1)) _) * Finset.card (@Finset.univ (Fin (⌊√t⌋₊ + 1)) _) := by
      apply Finset.card_image₂ (I_hat_fun_inj not_p_power)
    _ = (⌊√t⌋₊ + 1) * (⌊√t⌋₊ + 1) := by rw [card_univ, Fintype.card_fin]
    _ > t := by exact_mod_cast floor_sqrt_ineq
    _ = Nat.card G := rfl

lemma exists_m₁_m₂ (not_p_power : ¬is_power_of sa.n sa.p) : ∃ (m₁ m₂ : ℕ), m₁ ∈ I_hat ∧ m₂ ∈ I_hat ∧ m₁ ≡ m₂ [MOD sa.r] ∧ m₁ > m₂ := by
  rcases Function.not_injective_iff.mp (not_inj_of_card_le_card (card_G_eq_card_G' ▸ card_G_lt_card_I_hat not_p_power) I_hat_proj_fun) with ⟨m₁, m₂, hm₁m₂, m₁neqm₂⟩
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
      · exact Nat.pow_le_pow_of_le' n_div_p_pos (Nat.le_of_lt_succ i.isLt)
      · exact Nat.pow_le_pow_of_le' (Nat.Prime.pos sa.p_prime) (Nat.le_of_lt_succ j.isLt)
      · exact Nat.zero_le _
      · exact Nat.zero_le _
    _ = sa.n ^ ⌊√t⌋₊ := by
      rw [← mul_pow, Nat.div_mul_cancel sa.p_dvd_n]

lemma degree_x_pow_m (m : ℕ) : ((X : (AdjoinRoot h)[X]) ^ m).natDegree = m := by
  simp only [natDegree_pow, natDegree_X, mul_one]

noncomputable def Q' (m₁ m₂ : ℕ) : (AdjoinRoot h)[X] := X ^ m₁ - X ^ m₂

lemma Q'_degree {m₁ m₂ : ℕ} (m₁gtm₂ : m₁ > m₂) : (Q' m₁ m₂).natDegree = m₁ := by
  unfold Q'
  nth_rw 2 [← degree_x_pow_m m₁]
  apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
  simpa only [natDegree_pow, natDegree_X, mul_one]

lemma elem_𝒢_imp_root {m₁ m₂ : ℕ} (m₁_I_hat : m₁ ∈ I_hat) (m₂_I_hat : m₂ ∈ I_hat) (hm₁m₂r : m₁ ≡ m₂ [MOD sa.r]) (m₁gtm₂ : m₁ > m₂) :
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
  have cast_n_ge_1 : 1 ≤ (sa.n : ℝ) := by exact_mod_cast sa.ngt0
  have floor_sqrt_le_sqrt : ⌊√t⌋₊ ≤ √t := Nat.floor_le (sqrt_nonneg ↑t)
  exact_mod_cast Real.rpow_le_rpow_of_exponent_le cast_n_ge_1 floor_sqrt_le_sqrt

end

lemma lemma_4_7 (sa : Step5Assumptions) : Nat.card 𝒢 ≥ (t + ℓ).choose (t - 1) :=
  @lemma_4_7' sa

lemma lemma_4_8 (sa : Step5Assumptions) (not_p_power : ¬is_power_of sa.n sa.p) :
    Nat.card 𝒢 ≤ (sa.n : ℝ) ^ √t := by
  trans (sa.n ^ ⌊√t⌋₊)
  exact_mod_cast @lemma_4_8' sa ⟨sa.p_prime⟩ not_p_power
  exact_mod_cast @lemma_4_8_glue sa

end Lemma78


section

open Lemma78


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
  unfold polynomial_equality at ineq
  let a' : ℤ := ↑a
  have : (X + C (a' : ZMod n)) ^ n = X ^ n + C (a' : ZMod n) := by
    exact (lemma_2_1 n a' ngt1).mp hp
  have heq: AdjoinRoot.mk (X^smallest_r n - C (1 : ZMod n)) (X + C (a' : ZMod n))^n = AdjoinRoot.mk (X^smallest_r n - C (1 : ZMod n)) (X^n + C (a' : ZMod n)) := by
    exact lem_2_1_result n a' this
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

-- gets used in calc step 1 and 3
lemma sqrt_t_gt_log_n {sa : Step5Assumptions}: √t > Real.logb 2 sa.n := by
  have ha : t ≥ oᵣ sa.r sa.n := by
    sorry
  have hb : oᵣ sa.r sa.n > (Real.logb 2 sa.n)^2 := by
    apply sa.hrn
  have : t > (Real.logb 2 sa.n)^2 := by
    calc
      ↑t ≥ ↑(oᵣ sa.r sa.n) := by
        norm_cast
      _ > (Real.logb 2 sa.n)^2 := by
        norm_cast
  exact lt_sqrt_of_sq_lt this

lemma sqrt_t_gt0 {sa : Step5Assumptions} : √ t > 0 := by
  apply Real.sqrt_pos_of_pos
  exact Nat.cast_pos'.mpr tgt0

lemma ell_ineq  {sa : Step5Assumptions}: ℓ ≥ Nat.floor (√t * Real.logb 2 sa.n) := by
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
  exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right h₁ hlog)

lemma calc_step1 (sa : Step5Assumptions) :
  (t+ℓ).choose (t-1) ≥  (ℓ + 1 + Nat.floor ((√t) * (Real.logb 2 sa.n))).choose (Nat.floor ((√t) * (Real.logb 2 sa.n))) := by
  have hineq: t - 1 ≥ Nat.floor (Real.sqrt t * Real.logb 2 sa.n) := by
    apply (floor_le_iff _ _ _).mpr
    · norm_cast
      rw [Nat.sub_add_cancel tgt0, mul_comm]
      nth_rw 2 [←Real.sq_sqrt (Nat.cast_nonneg' t)]
      rw [pow_two]
      apply mul_lt_mul_of_pos_right
      · exact sqrt_t_gt_log_n
      · exact sqrt_t_gt0
    · rw [mul_comm]
      apply (mul_nonneg_iff_of_pos_right sqrt_t_gt0).mpr
      apply Real.logb_nonneg
      · linarith
      · norm_cast
        exact Nat.one_le_of_lt sa.ngt1
  have : t + ℓ = ℓ + 1 + (t - 1) := by
    calc
      t + ℓ  = t + 1 + ℓ- 1 := by exact Eq.symm (Nat.succ_add_sub_one ℓ t)
      _ = ℓ + 1 + t - 1 := by ring_nf
      _ = ℓ + 1 + (t - 1) := by
        rw [←Nat.add_sub_assoc tgt0]
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
    exact ell_ineq
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

end

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
            have : n ∣ p := by
              rw [Nat.le_antisymm heq this]
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
    have h_rgt0 : smallest_r n > 0 := by sorry
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
      hp := by -- p.gcd r = 1
        have hdiv : p.gcd (smallest_r n) ∣ n.gcd (smallest_r n) := by
          apply Nat.gcd_dvd_gcd_of_dvd_left (smallest_r n) hp.right.left
        rw [h_n_gcd_r] at hdiv
        exact Nat.eq_one_of_dvd_one hdiv
      p_dvd_n := hp.right.left -- : p ∣ n
      h_step_5 := sorry
      hrn := sorry
    }
    apply lemma_4_9_assumpts sa not_perfect_power

theorem theorem_4_1 (n : ℕ) (ngt1 : n > 1) : n.Prime ↔ AKS_algorithm n = PRIME := by
  constructor
  · exact lemma_4_2 n ngt1
  · exact lemma_4_9 n ngt1
