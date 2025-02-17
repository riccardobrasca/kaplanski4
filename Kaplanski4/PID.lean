import Mathlib

open PowerSeries Ideal

variable {R : Type*} [CommRing R]

local notation I"⁰" => Ideal.map (constantCoeff R) I

theorem bar {I : Ideal R⟦X⟧} (hI : X ∈ I) : (C R)'' I⁰ ⊆ I := by
  intro f ⟨r, hrI, hra⟩
  rw [SetLike.mem_coe, Ideal.mem_map_iff_of_surjective _ constantCoeff_surj] at hrI
  rcases hrI with ⟨g, hgI, hgr⟩
  rw [← hra, ← hgr]
  let g' := mk fun p ↦ (coeff R (p + 1)) g
  have hg' : g = X * g' + C R (constantCoeff R g) := eq_X_mul_shift_add_const g
  have : span {X} ≤ I := by simpa [span_le]
  have : X * g' ∈ I := by
    apply this
    apply mul_mem_right
    apply subset_span
    simp
  rw [hg'] at hgI
  have := Ideal.sub_mem _ hgI this
  convert this
  ring

theorem bar' {I : Ideal R⟦X⟧} {S : Set R} (hS : S.Finite) (hIX : X ∈ I)
    (hSI : span S = I⁰) :
    I = span ((C R)'' S ∪ {X}) := by
    ext f
    apply Iff.intro
    {
      intros hf
      simp
      rw [mem_span_insert]
      sorry
    }
    {
      intros hf
      rw [Set.union_singleton,mem_span_insert] at hf
      rcases hf with ⟨a, z, hz, hf⟩
      rw [hf]
      have hzP: z ∈ I := by sorry
      exact I.add_mem (mul_mem_left I a hIX) hzP
    }

theorem foo {P : Ideal R⟦X⟧} {S : Set R} (hS : S.Finite) (hPX : X ∈ P)
    (hSP : span S = P.map (constantCoeff R)) [P.IsPrime] :
    ∃ T : Set R⟦X⟧, span T = P ∧ T.ncard = S.ncard + 1 := by
  sorry

theorem foo' {P : Ideal R⟦X⟧} {S : Set R} (hS : S.Finite) (hPX : X ∉ P)
    (hSP : span S = P.map (constantCoeff R)) [P.IsPrime] :
    ∃ T : Set R⟦X⟧, span T = P ∧ T.ncard = S.ncard := by
  sorry
