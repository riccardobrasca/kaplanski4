import Mathlib
import Kaplanski4.Kaplanski

open PowerSeries Ideal Set BigOperators Finset

section for_mathlib

namespace PowerSeries

variable {R : Type*} [CommSemiring R]

lemma eq_trunc_add_X_pow_mul (g : R⟦X⟧) (n : ℕ) : g =
    trunc n g + (X ^ n : R⟦X⟧) * mk fun m ↦ coeff R (m + n) g:= by
  ext m
  by_cases hm : m < n <;>
  simp [coeff_trunc, hm, coeff_X_pow_mul', Nat.not_le_of_lt, Nat.le_of_not_lt]

end PowerSeries

end for_mathlib


variable {R : Type*} [CommRing R] {I P : Ideal R⟦X⟧}

-- Useful notation
local notation I"⁰" => Ideal.map (constantCoeff R) I
local notation f"⁰" => PowerSeries.constantCoeff R f

lemma mem_I0_iff {I : Ideal R⟦X⟧} {x : R} : x ∈ I⁰ ↔ ∃ f ∈ I, f⁰ = x :=
  I.mem_map_iff_of_surjective _ constantCoeff_surj

lemma f0_mem {I : Ideal R⟦X⟧} {f : R⟦X⟧} (hf : f ∈ I) : f⁰ ∈ I⁰ :=
  mem_I0_iff.2 ⟨f, hf, rfl⟩


section X_mem_I

variable (hXI : X ∈ I)
include hXI

theorem I0_subset_I : (C R)'' I⁰ ⊆ I := by
  intro f ⟨r, hrI, hra⟩
  rw [SetLike.mem_coe, mem_I0_iff] at hrI
  rcases hrI with ⟨g, hgI, hgr⟩
  rw [← hra, ← hgr]
  let g' := mk fun p ↦ coeff R (p + 1) g
  have hg' : g = X * g' + C R (g⁰) := eq_X_mul_shift_add_const g
  have hXg' : X * g' ∈ I := I.mul_mem_right _ hXI
  have := I.sub_mem hgI hXg'
  rw [hg', add_sub_cancel_left] at this
  assumption

theorem bar {S : Set R} (hSI : span S = I⁰) : I = span ((C R)'' S ∪ {X}) := by
  ext f
  rw [Set.union_singleton, mem_span_insert, ← map_span, hSI]
  apply Iff.intro
  · intro hf
    use mk fun p ↦ coeff R (p + 1) f, C R (f⁰)
    exact ⟨mem_map_of_mem _ (f0_mem hf), eq_shift_mul_X_add_const f⟩
  · rintro ⟨a, z, hz, hf⟩
    rw [hf]
    exact I.add_mem (I.mul_mem_left _ hXI) (span_le.2 (I0_subset_I hXI) hz)

end X_mem_I


section X_not_mem_P

variable (hP : X ∉ P) {k : ℕ} {a : Fin k → R} (haP : P.map (constantCoeff R) = span (range a))
  {g : R⟦X⟧} (hg : g ∈ P)
include haP

section f_k

lemma exists_f i : ∃ f ∈ P, f⁰ = a i := mem_I0_iff.1 (haP ▸ subset_span (Set.mem_range_self i))

noncomputable def f i := (exists_f haP i).choose
lemma f_mem_P i : f haP i ∈ P := (exists_f haP i).choose_spec.1

lemma hfa i : (f haP i)⁰ = a i := (exists_f haP i).choose_spec.2

end f_k

include hg in
lemma exists_r : ∃ r : Fin k → R, ∑ i, r i • a i = (constantCoeff R) g :=
  (mem_span_range_iff_exists_fun R).1 (haP ▸ f0_mem hg : _ ∈ span (range a))

noncomputable def r : Fin k → R := (exists_r haP hg).choose
lemma hr : ∑ i, (r haP hg) i * a i = g⁰ := (exists_r haP hg).choose_spec

variable [P_prime : P.IsPrime]

noncomputable
def g' : ℕ → P
| 0 => ⟨g, hg⟩
| n + 1 =>
  ⟨mk fun p ↦ coeff R (p + 1) (g' n) - ∑ i, r haP (g' n).2 i * coeff R (p + 1) (f haP i), by
    have := sub_const_eq_X_mul_shift ((g' n).1 - ∑ i, C R (r haP (g' n).2 i) * f haP i)
    simp [hr haP (g' n).2, hfa] at this
    have hf : ∑ i, C R (r haP (g' n).2 i) * f haP i ∈ P :=
      P.sum_mem fun i _ ↦ P.mul_mem_left _ (f_mem_P haP i)
    exact Or.resolve_left (P_prime.mul_mem_iff_mem_or_mem.1 (this ▸ P.sub_mem (g' n).2 hf)) hP⟩

lemma hg' (n : ℕ) : (g' hP haP hg n).1 - ∑ i, C R (r haP (g' hP haP hg n).2 i) * f haP i =
    X * (g' hP haP hg (n + 1)).1 := by
  have := sub_const_eq_X_mul_shift
    ((g' hP haP hg n).1 - ∑ i, C R (r haP (g' hP haP hg n).2 i) * f haP i)
  simpa [hr haP (g' hP haP hg n).2, hfa]

noncomputable
def h (i : Fin k) : R⟦X⟧ := mk fun n ↦ r haP (g' hP haP hg n).2 i

lemma key (n : ℕ) : g - ∑ i, trunc n ((h hP haP hg) i) * f haP i = X ^ n * (g' hP haP hg n).1 := by
  induction n with
  | zero => simp [g']
  | succ n H =>
    conv =>
      enter [1, 2, 2, i]
      rw [trunc_succ, Polynomial.coe_add, Polynomial.coe_monomial, add_mul, ← mul_one (coeff R n _),
        ← smul_eq_mul (b := 1), map_smul, ← X_pow_eq, smul_eq_C_mul, mul_comm _ (X ^ n), mul_assoc]
    rw [sum_add_distrib, sub_add_eq_sub_sub, H, ← mul_sum, ← mul_sub]
    simp [h, hg']
    ring

lemma sum_h_eq_g : ∑ i, (h hP haP hg) i * f haP i = g := by
  refine (sub_eq_zero.1 ?_).symm
  ext n
  conv =>
    enter [1, 2, 2, 2, i]
    rw [eq_trunc_add_X_pow_mul (h hP haP hg i) (n + 1), add_mul, mul_assoc]
  rw [sum_add_distrib, sub_add_eq_sub_sub, key, ← mul_sum]
  simp [coeff_X_pow_mul']

include hP in
theorem P_eq_span_range : P = span (range (f haP)) :=
  le_antisymm
    (fun _ hg ↦ (mem_span_range_iff_exists_fun _).2 ⟨_, sum_h_eq_g hP haP hg⟩)
    (span_le.2 (Set.range_subset_iff.2 (f_mem_P haP)))

end X_not_mem_P


section Kaplansky13_6

instance Kaplansky13_6 [principal_R : IsPrincipalIdealRing R] [IsDomain R]  :
    UniqueFactorizationMonoid R⟦X⟧ :=  by
  apply (uniqueFactorizationMonoid_iff ⟨_, X_prime⟩).2
  intro P P_ne_bot P_prime
  by_cases hxP : X ∈ P
  · exact ⟨_, hxP, X_prime⟩
  · obtain ⟨a, ha⟩ := (principal_R.principal (P⁰)).principal'
    let a' (_ : Fin 1) := a
    have haP : P⁰ = span (range a') := by simp [ha, a']
    have P_span_f : P = span {f haP 0} := by simp [P_eq_span_range hxP haP, Fin.range_fin_succ]
    have f_ne_0 : f haP 0 ≠ 0 := span_singleton_eq_bot.not.1 (P_span_f ▸ P_ne_bot)
    exact ⟨f haP 0, f_mem_P haP 0, (span_singleton_prime f_ne_0).1 (P_span_f ▸ P_prime)⟩

end Kaplansky13_6

instance {R : Type*} [CommRing R] [IsNoetherianRing R] : IsNoetherianRing R⟦X⟧ := by
  sorry
