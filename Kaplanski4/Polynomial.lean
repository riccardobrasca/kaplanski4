import Mathlib.RingTheory.Nilpotent
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Polynomial.Lifts
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Ideal.QuotientOperations

variable {R : Type _} [CommRing R]

open Finset Polynomial BigOperators

theorem isUnit_of_isNilpotent_sub_one {r : R} (hnil : IsNilpotent r) : IsUnit (r - 1) := by
  obtain ⟨n, hn⟩ := hnil
  refine' isUnit_iff_exists_inv.2 ⟨-∑ i in range n, r ^ i, _⟩
  rw [mul_neg, mul_comm, geom_sum_mul, hn]
  ring

theorem isUnit_of_isUnit_add_isNilpotent {u r : R} (hu : IsUnit u) (hnil : IsNilpotent r) :
    IsUnit (u + r) := by
  obtain ⟨v, hv⟩ := IsUnit.exists_right_inv hu
  suffices IsUnit (v * (u + r)) by
    exact isUnit_of_mul_isUnit_right this
  rw [mul_add, mul_comm, hv, ← IsUnit.neg_iff, neg_add, add_comm, ← sub_eq_add_neg, ← neg_mul]
  exact isUnit_of_isNilpotent_sub_one (Ideal.mul_mem_left _ _ (mem_nilradical.2 hnil))

namespace Polynomial

theorem isNilpotent.C_mul_X_pow {r : R} (n : ℕ) (hnil : IsNilpotent r) :
    IsNilpotent ((C r) * X ^ n) := (Commute.all _ _).isNilpotent_mul_left (hnil.map _)

theorem isUnit_of_isUnit_of_isNilpotent {P : Polynomial R} (hunit : IsUnit (P.coeff 0))
    (hnil : ∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) : IsUnit P := by
  induction' h : P.natDegree using Nat.strong_induction_on with k hind generalizing P
  by_cases hdeg : P.natDegree = 0
  { have hCunit : IsUnit (C (P.coeff 0)) := IsUnit.map C hunit
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
    apply hCunit }
  let P₁ := P.eraseLead
  suffices : IsUnit P₁
  { rw [← eraseLead_add_monomial_natDegree_leadingCoeff P]
    apply isUnit_of_isUnit_add_isNilpotent this _
    rw [← C_mul_X_pow_eq_monomial]
    apply isNilpotent.C_mul_X_pow
    apply hnil
    exact hdeg }
  have hdegk : P₁.natDegree < k
  { rw [← h]
    apply lt_of_le_of_lt (eraseLead_natDegree_le P)
    rw [← Nat.pred_eq_sub_one]
    exact Nat.pred_lt hdeg }
  have hP₁unit : IsUnit (P₁.coeff 0)
  { rw [eraseLead_coeff_of_ne]
    { exact hunit }
    { intro h
      exact hdeg h.symm } }
  have hP₁nilpotent : ∀ i, i ≠ 0 → IsNilpotent (P₁.coeff i)
  { intros i hi
    by_cases H : i ≤ P₁.natDegree
    { rw [eraseLead_coeff_of_ne]
      { exact hnil i hi }
      { linarith } }
    { rw [coeff_eq_zero_of_natDegree_lt]
      { exact IsNilpotent.zero }
      { linarith } }}
  exact hind _ hdegk hP₁unit hP₁nilpotent rfl

theorem is_unit.coeff {P : Polynomial R} (hunit : IsUnit P) :
    IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) := by
  obtain ⟨Q, hQ⟩ := IsUnit.exists_right_inv hunit
  constructor
  { let _ := P * Q --let u := polynomial.constant_coeff (V),
    have v1 : Polynomial.constantCoeff (P * Q) = 1 := by
      { rw [hQ]
        rw [Polynomial.constantCoeff_apply]
        simp }
    suffices (Polynomial.constantCoeff (P)) * (Polynomial.constantCoeff (Q)) = 1 by
      { exact isUnit_of_mul_eq_one (P.coeff 0) (constantCoeff Q) this }
    simp at v1
    simp
    apply v1 }
  { intros n hn
    rw [nilpotent_iff_mem_prime]
    intros I hI
    let f := Polynomial.mapRingHom (Ideal.Quotient.mk I)
    have hPQ : (f P) * (f Q) = (1 : Polynomial (R ⧸ I)) := by
      rw [← map_mul, hQ, map_one]
    replace hPQ := congr_arg Polynomial.degree hPQ
    haveI : IsDomain (R ⧸ I) := by
      rw [Ideal.Quotient.isDomain_iff_prime]
      exact hI
    simp only [Nat.WithBot.add_eq_zero_iff, degree_mul, degree_one] at hPQ
    have hcoeff : (f P).coeff n = 0
    { apply Polynomial.coeff_eq_zero_of_degree_lt
      rw [hPQ.1]
      apply (@WithBot.coe_pos _ _ _ n).2
      exact Ne.bot_lt hn }
    rw [coe_mapRingHom, Polynomial.coeff_map, ← RingHom.mem_ker, Ideal.mk_ker] at hcoeff
    exact hcoeff }

theorem is_unit_iff (P : Polynomial R) : IsUnit P ↔
    IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) := by
  constructor
  { intro hunit
    exact is_unit.coeff hunit }
  { intro H
    exact isUnit_of_isUnit_of_isNilpotent H.1 H.2 }

end Polynomial
