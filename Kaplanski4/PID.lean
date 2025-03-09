import Mathlib

open PowerSeries Ideal Set BigOperators

variable {R : Type*} [CommRing R] {I P : Ideal R⟦X⟧} [P_prime : P.IsPrime]

-- Usefull notation
local notation I"⁰" => Ideal.map (constantCoeff R) I
local notation f"⁰" => PowerSeries.constantCoeff R f

lemma mem_Izero_iff {I : Ideal R⟦X⟧} {x : R} : x ∈ I⁰ ↔ ∃ f ∈ I, f⁰ = x :=
  I.mem_map_iff_of_surjective _ constantCoeff_surj

lemma fzero_mem {I : Ideal R⟦X⟧} {f : R⟦X⟧} (hf : f ∈ I) : f⁰ ∈ I⁰ :=
  mem_Izero_iff.2 ⟨f, hf, rfl⟩


section X_mem_I

variable (hXI : X ∈ I)
include hXI

theorem Izero_subset_I : (C R)'' I⁰ ⊆ I := by
  intro f ⟨r, hrI, hra⟩
  rw [SetLike.mem_coe, mem_Izero_iff] at hrI
  rcases hrI with ⟨g, hgI, hgr⟩
  rw [← hra, ← hgr]

  let g' := mk fun p ↦ coeff R (p + 1) g
  have hg' : g = X * g' + C R (g⁰) := eq_X_mul_shift_add_const g
  have hXg' : X * g' ∈ I := I.mul_mem_right _ hXI
  have := I.sub_mem hgI hXg'
  rw [hg', add_sub_cancel_left] at this
  assumption

theorem bar' {S : Set R} (hSI : span S = I⁰) : I = span ((C R)'' S ∪ {X}) := by
  ext f
  rw [Set.union_singleton, mem_span_insert, ← map_span, hSI]
  apply Iff.intro
  · intro hf
    use mk fun p ↦ coeff R (p + 1) f
    use C R (f⁰)
    exact ⟨mem_map_of_mem _ (fzero_mem hf), eq_shift_mul_X_add_const f⟩
  · rintro ⟨a, z, hz, hf⟩
    rw [hf]
    exact I.add_mem (I.mul_mem_left _ hXI) (span_le.2 (Izero_subset_I hXI) hz)

end X_mem_I


section X_not_mem_P

-- Pourquoi utiliser la notation P⁰ dans la définition de hfP casse tout ?
variable
  {k : ℕ} {f : Fin k → R⟦X⟧} (hfP : P.map (constantCoeff R) = span (range (constantCoeff R ∘ f)))
  {g : R⟦X⟧} (hg : g ∈ P)
  (hP : X ∉ P)

def exists_r := (mem_span_range_iff_exists_fun R).1 (hfP ▸ fzero_mem hg)

noncomputable
def r : Fin k → R := (exists_r hfP hg).choose

omit [P.IsPrime] in
lemma hr : ∑ i : Fin k, (r hfP hg) i * constantCoeff R (f i) = constantCoeff R g := by
  simp [r, ← (exists_r hfP hg).choose_spec]

-- existence de g'
include hP in
lemma exists_g' : ∃ g' ∈ P, g - ∑ i : Fin k, (r hfP hg) i • f i = X * g' := by
  have this := sub_const_eq_X_mul_shift (g - ∑ i : Fin k, (r hfP hg) i • f i)
  simp [← hr hfP hg] at this
  refine ⟨_, ?_, this⟩
  have sum_f_mem_P : ∑ i : Fin k, (r hfP hg) i • f i ∈ P := sorry
  exact Or.resolve_left (P_prime.mul_mem_iff_mem_or_mem.1 (this ▸ P.sub_mem hg sum_f_mem_P)) hP

noncomputable
def g' : ℕ → P
| 0 => ⟨g, hg⟩
| n + 1 => ⟨_, (exists_g' hfP (g' n).2 hP).choose_spec.1⟩

noncomputable
def h (i : Fin k) : R⟦X⟧ := mk fun n ↦ r hfP (g' hfP hg hP n).2 i

set_option pp.proofs true
-- partie la plus intéressante
lemma sum_h_eq_g : ∑ i : Fin k, (h hfP hg hP) i * f i = g := by
  ext n
  induction n with
  | zero => simp [h, g', hr]
  | succ n hrec =>

    sorry

/-

--faire l'autre inclusion
theorem foo : P = span ((C R)'' range (constantCoeff R ∘ f)) := by
  let a : Fin k → R := constantCoeff R ∘ f
  intro g hg
  sorry
-/
end X_not_mem_P
