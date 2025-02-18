import Mathlib

open PowerSeries Ideal

variable {R : Type*} [CommRing R]

local notation I"⁰" => Ideal.map (constantCoeff R) I
local notation f"⁰" => PowerSeries.constantCoeff R f

lemma mem_Izero_iff {I : Ideal R⟦X⟧} {x : R} : x ∈ I⁰ ↔ ∃ f ∈ I, f⁰ = x :=
  I.mem_map_iff_of_surjective _ constantCoeff_surj


theorem bar {I : Ideal R⟦X⟧} (hI : X ∈ I) : (C R)'' I⁰ ⊆ I := by
  intro f ⟨r, hrI, hra⟩
  rw [SetLike.mem_coe, mem_Izero_iff] at hrI
  rcases hrI with ⟨g, hgI, hgr⟩
  rw [← hra, ← hgr]

  let g' := mk fun p ↦ coeff R (p + 1) g
  have hg' : g = X * g' + C R (g⁰) := eq_X_mul_shift_add_const g
  have hXg' : X * g' ∈ I := I.mul_mem_right _ hI
  rw [hg'] at hgI
  have := I.sub_mem hgI hXg'
  rw [add_sub_cancel_left] at this
  assumption

theorem bar' {I : Ideal R⟦X⟧} {S : Set R} (hIX : X ∈ I) (hSI : span S = I⁰) :
    I = span ((C R)'' S ∪ {X}) := by
  ext f
  apply Iff.intro
  · intros hf
    rw [Set.union_singleton, mem_span_insert]
    use mk fun p ↦ coeff R (p + 1) f
    use C R (f⁰)
    apply And.intro
    · rw [← map_span]
      apply mem_map_of_mem _
      rw [hSI]
      exact mem_Izero_iff.2 ⟨f, hf, rfl⟩
    · exact eq_shift_mul_X_add_const f

  · intros hf
    rw [Set.union_singleton, mem_span_insert] at hf
    rcases hf with ⟨a, z, hz, hf⟩
    rw [hf]
    have hzP: z ∈ I := by
      have : S ⊆ I⁰ := span_le.1 hSI.le
      have : (C R)'' S ⊆ (C R)'' (I⁰) := Set.image_mono this
      have : (C R)'' S ⊆ I := subset_trans this (bar hIX)
      rw [← I.span_le] at this
      exact this hz
    exact I.add_mem (mul_mem_left I a hIX) hzP

theorem foo {P : Ideal R⟦X⟧} {S : Set R} (hS : S.Finite) (hPX : X ∈ P)
    (hSP : span S = P.map (constantCoeff R)) [P.IsPrime] :
    ∃ T : Set R⟦X⟧, span T = P ∧ T.ncard = S.ncard + 1 := by
  sorry

theorem foo' {P : Ideal R⟦X⟧} {S : Set R} (hS : S.Finite) (hPX : X ∉ P)
    (hSP : span S = P.map (constantCoeff R)) [P.IsPrime] :
    ∃ T : Set R⟦X⟧, span T = P ∧ T.ncard = S.ncard := by
  sorry
