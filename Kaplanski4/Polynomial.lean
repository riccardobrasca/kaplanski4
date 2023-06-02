import Mathlib.RingTheory.Nilpotent
import Mathlib.Data.Polynomial.EraseLead
import Mathlib.Data.Polynomial.Eval
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Polynomial.Lifts
import Mathlib.RingTheory.Ideal.Quotient

variable {R : Type _} [CommRing R]

open_locale polynomial big_operators

open Finset

theorem is_unit_of_is_nilpotent_sub_one {r : R} (hnil : IsNilpotent r) :
    IsUnit (r - 1) := by
  obtain ⟨n, hn⟩ := hnil
  rw [isUnit_iff_exists_inv]
  use -(∑ i in range n, r ^ i)
  rw [mul_neg, mul_comm, geom_sum_mul, hn]
  simp

theorem is_unit_of_is_unit_add_is_nilpotent {u r : R} (hu : IsUnit u) (hnil : IsNilpotent r) :
    IsUnit (u + r) := by
  obtain ⟨v, hv⟩ := IsUnit.exists_right_inv hu
  suffices : IsUnit (v * (u + r))
  { exact isUnit_of_mul_isUnit_right this }
  rw [mul_add, mul_comm v u, hv]
  replace hnil : is_nilpotent (-v * r)
  { rw [← mem_nilradical] at ⊢ hnil
    exact (nilradical R).mul_mem_left (-v) hnil }
  rw [← is_unit.neg_iff, neg_add, add_comm, ← sub_eq_add_neg, ← neg_mul]
  exact is_unit_of_is_nilpotent_sub_one hnil

namespace polynomial

theorem is_nilpotent.C_mul_X_pow {r : R} (n : ℕ) (hnil : IsNilpotent r) :
    IsNilpotent ((Polynomial.C r) * X ^ n) := by
  have hCnil : IsNilpotent (Polynomial.C r) := IsNilpotent.map hnil Polynomial.C
  apply Commute.isNilpotent_mul_left
  { exact Commute.all (Polynomial.C r) (X ^ n) }
  { assumption }

theorem isUnit_of_isUnit_of_isNilpotent {P : Polynomial R} (hunit : IsUnit (P.coeff 0))
    (hnil : ∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) : IsUnit P := by
  induction h : P.nat_degree using nat.strong_induction_on with k hind generalizing P
  by_cases hdeg : P.nat_degree = 0
  { have hCunit : is_unit (C (P.coeff 0)) := is_unit.map C hunit
    rw polynomial.eq_C_of_nat_degree_eq_zero hdeg
    apply hCunit }
  let P₁ := P.erase_lead
  suffices : is_unit P₁
  { rw [← erase_lead_add_monomial_nat_degree_leading_coeff P]
    apply is_unit_of_is_unit_add_is_nilpotent this _
    rw [← C_mul_X_pow_eq_monomial]
    apply is_nilpotent.C_mul_X_pow
    apply hnil
    exact hdeg }
  have hdegk : P₁.nat_degree < k
  { rw [← h]
    apply lt_of_le_of_lt (erase_lead_nat_degree_le P)
    rw [← nat.pred_eq_sub_one]
    exact nat.pred_lt hdeg }
  have hP₁unit : is_unit (P₁.coeff 0)
  { rw [erase_lead_coeff_of_ne]
    { exact hunit }
    { intro h
      exact hdeg h.symm } }
  have hP₁nilpotent : ∀ i ≠ 0, is_nilpotent (P₁.coeff i)
  { intros i hi
    by_cases H : i ≤ P₁.nat_degree
    { rw [erase_lead_coeff_of_ne]
      { exact hnil i hi }
      { linarith } }
    { rw [coeff_eq_zero_of_nat_degree_lt]
      { exact is_nilpotent.zero }
      { linarith } }}
  exact hind _ hdegk hP₁unit hP₁nilpotent rfl

theorem is_unit.coeff {P : Polynomial R} (hunit : IsUnit P) :
    IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) := by
  obtain ⟨Q, hQ⟩ := IsUnit.exists_right_inv hunit
  constructor
  { let V := P * Q --let u := polynomial.constant_coeff (V),
    have v1 : polynomial.constant_coeff (P * Q) = 1
      { rw [hQ]
        rw [Polynomial.constant_coeff_apply]
        simp }
    suffices : (polynomial.constant_coeff (P)) * (polynomial.constant_coeff (Q)) = 1
      { exact is_unit_of_mul_eq_one (coeff P 0) (constant_coeff Q) this }
    simp at v1
    simp
    apply v1 }
  { intros n hn
    rw [nilpotent_iff_mem_prime]
    intros I hI
    let f := Polynomial.mapRingHom (Ideal.Quotient.mk I)
    have hPQ : (f P) * (f Q) = 1
      { rw [← map_mul, hQ, map_one] }
    replace hPQ := congr_arg degree hPQ
    haveI : is_domain (R ⧸ I)
      { rw [ideal.quotient.is_domain_iff_prime]
        exact hI }
    simp only [nat.with_bot.add_eq_zero_iff, degree_mul, degree_one] at hPQ
    have hcoeff : (f P).coeff n = 0
    { apply polynomial.coeff_eq_zero_of_degree_lt
      rw [hPQ.1, with_bot.coe_pos]
      exact ne.bot_lt hn }
    rw [coe_map_ring_hom, polynomial.coeff_map, ← ring_hom.mem_ker, ideal.mk_ker] at hcoeff
    exact hcoeff }

theorem is_unit_iff (P : Polynomial R) : IsUnit P ↔
    IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) := by
  constructor
  { intro hunit
    exact is_unit.coeff hunit }
  { intro H
    exact isUnit_of_isUnit_of_isNilpotent H.1 H.2 }

end polynomial
