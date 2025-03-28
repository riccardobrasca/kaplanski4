import Mathlib

open PowerSeries Ideal Set BigOperators Finset

def S (R : Type*) [CommRing R] := {I : Ideal R | ¬ I.FG}

variable {R : Type*} [CommRing R]


section zorn

variable (h : ¬IsNoetherianRing R)
include h

lemma nonempty_S : (S R).Nonempty :=
  not_forall.1  <| (isNoetherianRing_iff_ideal_fg _).not.1 h


theorem cohen_zorn_lemma (C : Set (Ideal R)) (hC : C ⊆ S R) (hC₂ : IsChain (· ≤ ·) C) :
    ∃ P ∈ S R, ∀ I ∈ C, I ≤ P := by
  by_cases C.Nonempty
  · refine ⟨sSup C, ?_, fun _ ↦ le_sSup⟩
    intro ⟨G, hG⟩
    have : ∃ I ∈ C, G.toSet ⊆ I := by
      refine hC₂.directedOn.exists_mem_subset_of_finset_subset_biUnion ‹_› (fun x hx ↦ ?_)
      obtain ⟨I, hIC, h⟩ := (Submodule.mem_sSup_of_directed ‹_› hC₂.directedOn).1 <|
        hG ▸ subset_span hx
      exact Set.mem_biUnion hIC h
    obtain ⟨I, I_mem_C, hGI⟩ := this
    have := hG ▸ span_le.2 hGI
    have : sSup C = I := LE.le.antisymm this (le_sSup I_mem_C)
    refine hC I_mem_C ⟨G, this ▸ hG⟩
  · rw [Set.not_nonempty_iff_eq_empty.1 ‹¬C.Nonempty›]
    obtain ⟨_, _⟩ := (Set.nonempty_def.1 <| nonempty_S h)
    exact ⟨_, ‹_›, by simp⟩


theorem exists_maximal_not_fg : ∃ (M : Ideal R), Maximal (· ∈ S R) M :=
  zorn_le₀ (S R) (cohen_zorn_lemma h)


end zorn

-- Le théorème est censé être dans mathlib mais je ne l'ai pas trouvé.
theorem is_noetherian_of_prime_ideals_fg
  (h : ∀ (P : Ideal R), P.IsPrime → P.FG) : IsNoetherianRing R := by
  by_contra _
  let S := {I : Ideal R | ¬ I.FG}
  obtain ⟨M, hM⟩ := exists_maximal_not_fg ‹_›

  suffices Mprime : M.IsPrime
  · exact absurd (h M Mprime) (maximal_mem_iff.1 hM).1
  · by_contra M_not_prime
    sorry
