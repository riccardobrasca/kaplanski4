import Mathlib

open PowerSeries Ideal Set BigOperators Finset

def S (R : Type*) [CommRing R] := {I : Ideal R | ¬ I.FG}

variable {R : Type*} [CommRing R]

lemma fg_of_le_fg {I J : Ideal R} (h : J.FG) (h2 : I ≤ J) : I.FG := sorry

section zorn

variable (h : ¬IsNoetherianRing R)
include h

lemma nonempty_S : (S R).Nonempty :=
  not_forall.1  <| (isNoetherianRing_iff_ideal_fg _).not.1 h


theorem hypothesis_zorn_lemma (C : Set (Ideal R)) (hC : C ⊆ S R) (_ : IsChain (· ≤ ·) C) :
    ∃ P ∈ S R, ∀ I ∈ C, I ≤ P := by
  by_cases C.Nonempty
  · refine ⟨sSup C, ?_, fun _ ↦ le_sSup⟩
    intro supFG
    obtain ⟨I, hI⟩ := (Set.nonempty_def.1 ‹C.Nonempty›)
    have : I.FG := fg_of_le_fg supFG (le_sSup hI)
    have : ¬ I.FG := hC hI
    contradiction
  · rw [Set.not_nonempty_iff_eq_empty.1 ‹¬C.Nonempty›]
    obtain ⟨_, _⟩ := (Set.nonempty_def.1 <| nonempty_S h)
    exact ⟨_, ‹_›, by simp⟩


theorem exists_maximal_not_fg : ∃ (M : Ideal R), Maximal (· ∈ S R) M :=
  zorn_le₀ (S R) (hypothesis_zorn_lemma h)


end zorn

-- Le théorème est censé être dans mathlib mais je ne l'ai pas trouvé.
theorem is_noetherian_of_prime_ideals_fg
  (h : ∀ (P : Ideal R), P.IsPrime → P.FG) : IsNoetherianRing R := by
  by_contra _
  let S := {I : Ideal R | ¬ I.FG}
  obtain ⟨M, hM⟩ := exists_maximal_not_fg ‹_›

  suffices Mprime : M.IsPrime
  · have := h M Mprime
    have := (maximal_mem_iff.1 hM).1
    contradiction
  · by_contra M_not_prime
    have  := isPrime_iff.not.1 M_not_prime
    simp at this
    have hMtop : M ≠ ⊤ := by sorry
    obtain ⟨a, b, ab_mem_M, a_not_mem_M, b_not_mem_M⟩ := this hMtop


    sorry
