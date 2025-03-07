import Mathlib

open PowerSeries Ideal

variable {R : Type*} [CommRing R]

local notation I"⁰" => Ideal.map (constantCoeff R) I
local notation f"⁰" => PowerSeries.constantCoeff R f

lemma mem_Izero_iff {I : Ideal R⟦X⟧} {x : R} : x ∈ I⁰ ↔ ∃ f ∈ I, f⁰ = x :=
  I.mem_map_iff_of_surjective _ constantCoeff_surj

lemma fzero_mem {I : Ideal R⟦X⟧} {f : R⟦X⟧} (hf : f ∈ I) : f⁰ ∈ I⁰ :=
  mem_Izero_iff.2 ⟨f, hf, rfl⟩


theorem Izero_subset_I {I : Ideal R⟦X⟧} (hI : X ∈ I) : (C R)'' I⁰ ⊆ I := by
  intro f ⟨r, hrI, hra⟩
  rw [SetLike.mem_coe, mem_Izero_iff] at hrI
  rcases hrI with ⟨g, hgI, hgr⟩
  rw [← hra, ← hgr]

  let g' := mk fun p ↦ coeff R (p + 1) g
  have hg' : g = X * g' + C R (g⁰) := eq_X_mul_shift_add_const g
  have hXg' : X * g' ∈ I := I.mul_mem_right _ hI
  have := I.sub_mem hgI hXg'
  rw [hg', add_sub_cancel_left] at this
  assumption

theorem bar' {I : Ideal R⟦X⟧} {S : Set R} (hXI : X ∈ I) (hSI : span S = I⁰) :
    I = span ((C R)'' S ∪ {X}) := by
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


theorem foo' {P : Ideal R⟦X⟧} {S : Set R} [P.IsPrime] (hS : S.Finite) (hXP : X ∉ P)
    (hSP : span S = P⁰) : P = span ((C R)'' S) := by
  sorry
