import Mathlib
import Kaplanski4
set_option pp.proofs true

open PowerSeries Ideal Set BigOperators

variable {R : Type*} [CommRing R] {I P : Ideal R⟦X⟧} [P_prime : P.IsPrime]


-- Usefull notation
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
    use mk fun p ↦ coeff R (p + 1) f
    use C R (f⁰)
    exact ⟨mem_map_of_mem _ (f0_mem hf), eq_shift_mul_X_add_const f⟩
  · rintro ⟨a, z, hz, hf⟩
    rw [hf]
    exact I.add_mem (I.mul_mem_left _ hXI) (span_le.2 (I0_subset_I hXI) hz)

end X_mem_I


section X_not_mem_P

-- Pourquoi utiliser la notation P⁰ dans la définition de hfP casse tout ?
variable
  (hP : X ∉ P)
  {k : ℕ} {a : Fin k → R} (haP : P.map (constantCoeff R) = span (range a))
  {g : R⟦X⟧} (hg : g ∈ P)
include haP


section f_k
omit [P.IsPrime]
lemma exists_f i : ∃ f ∈ P, f⁰ = a i:= mem_I0_iff.1 (haP ▸ subset_span (Set.mem_range_self i))
noncomputable def f i := (exists_f haP i).choose
lemma f_mem_P i : f haP i ∈ P := (exists_f haP i).choose_spec.1
lemma hfa i : (f haP i)⁰ = a i := (exists_f haP i).choose_spec.2
end f_k

def exists_r := (mem_span_range_iff_exists_fun R).1 (haP ▸ f0_mem hg)
noncomputable def r : Fin k → R := (exists_r haP hg).choose
omit [P.IsPrime] in lemma hr : ∑ i, (r haP hg) i * a i = g⁰ := (exists_r haP hg).choose_spec

noncomputable
def g' : ℕ → P
| 0 => ⟨g, hg⟩
| n + 1 => by
  have := sub_const_eq_X_mul_shift ((g' n).1 - ∑ i, C R (r haP (g' n).2 i) * f haP i)
  simp [hr haP (g' n).2, hfa] at this
  have hf : ∑ i, C R (r haP (g' n).2 i) * f haP i ∈ P :=
    P.sum_mem fun i _ ↦ P.mul_mem_left _ (f_mem_P haP i)
  have := Or.resolve_left (P_prime.mul_mem_iff_mem_or_mem.1 (this ▸ P.sub_mem (g' n).2 hf)) hP
  exact ⟨_, this⟩

noncomputable
def h (i : Fin k) : R⟦X⟧ := mk fun n ↦ r haP (g' hP haP hg n).2 i

-- partie la plus intéressante
lemma sum_h_eq_g : ∑ i, (h hP haP hg) i * f haP i = g := by
  ext n
  simp
  induction n with
  | zero => simp [h, hfa, hr, g']
  | succ n hrec =>
    simp [h, coeff_mul] at hrec ⊢
    sorry

include hP in
theorem P_eq_span_range : P = span (range (f haP)) :=
  le_antisymm_iff.2
    ⟨fun _ hg ↦ (mem_span_range_iff_exists_fun _).2 ⟨_, sum_h_eq_g hP haP hg⟩,
    span_le.2 (Set.range_subset_iff.2 (f_mem_P haP))⟩

end X_not_mem_P


section Kaplansky13_6

theorem Kaplansky13_6 [principal_R : IsPrincipalIdealRing R] [IsDomain R]  :
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
