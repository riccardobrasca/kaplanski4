import Mathlib

open PowerSeries Ideal Set BigOperators Finset

variable {R : Type*} [CommRing R] {P : Ideal R⟦X⟧} [P.IsPrime]


section zorn_lemma


lemma S_not_empty (h : ¬IsNoetherianRing R): {I : Ideal R | ¬ I.FG}.Nonempty :=
   not_forall.1  <| (isNoetherianRing_iff_ideal_fg _).not.1 h


theorem exists_maximal_no_fg  : 1 = 1 := sorry

end zorn_lemma



-- -- Le théorème est censé être dans mathlib mais je ne l'ai pas trouvé.
theorem is_noetherian_of_prime_ideals_fg
  (h : ∀ (P : Ideal R), P.IsPrime → P.FG) : IsNoetherianRing R := by
  apply Classical.byContradiction
  intro not_noetherian
  let S := {I : Ideal R | ¬ I.FG}
  sorry
