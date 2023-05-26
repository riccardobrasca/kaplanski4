import Kaplanski4.Kaplanski
import Mathlib.RingTheory.Localization.Ideal

/-- Let R be a commutative ring and M be a multiplicatively closed set.
The image of a prime element p ∈ R by the natural homomorphism is prime in the localization
(under the condition that p belongs to an ideal disjoint from M). -/
lemma isLocalization.prime_of_prime {R S : Type _} [CommRing R] [CommRing S] [Algebra R S]
    {M : Submonoid R} [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) (p : R)
    (hp : Prime p) (hp₂ : ∃ (I : Ideal R), Disjoint (M : Set R) (I : Set R) ∧ p ∈ I) :
    Prime (algebraMap R S p) := by
  rcases hp₂ with ⟨I, hI, hp₂⟩
  have hp' := IsLocalization.isPrime_of_isPrime_disjoint M S (Ideal.span {p})
    ((Ideal.span_singleton_prime hp.ne_zero).2 hp)
      (Set.disjoint_of_subset_right (I.span_singleton_le_iff_mem.2 hp₂) hI)
  rw [Ideal.map_span, Set.image_singleton] at hp'
  exact (Ideal.span_singleton_prime (fun hp₃ => hp.ne_zero
    ((IsLocalization.to_map_eq_zero_iff S hM).1 hp₃))).1 hp'

/-- Let R be a commutative ring and M be a multiplicatively closed set.
If R is a UFD, then the localization of R by M is a UFD. -/
lemma isLocalization.uniqueFactorizationMonoid_of_uniqueFactorizationMonoid {R S : Type _}
    [CommRing R] [CommRing S] [Algebra R S] [IsDomain R] {M : Submonoid R} [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors R) [UniqueFactorizationMonoid R] :
    @UniqueFactorizationMonoid S (@IsDomain.toCancelCommMonoidWithZero S _
    (IsLocalization.isDomain_of_le_nonZeroDivisors _ hM)) := by
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  refine' uniqueFactorizationMonoid_of_exists_prime _ (fun J hJzero hJprime => _)
  let I := J.comap (algebraMap R S)
  have hI := (IsLocalization.isPrime_iff_isPrime_disjoint M S J).1 hJprime
  have hI₂ : I ≠ ⊥ :=
    ((lt_iff_le_and_ne.1 (IsLocalization.bot_lt_comap_prime M S hM J hJzero)).2).symm
  obtain ⟨p, hpI, hp⟩ := exists_prime_of_uniqueFactorizationMonoid _ hI₂ hI.1
  exact ⟨algebraMap R S p, Ideal.mem_comap.mp hpI, isLocalization.prime_of_prime hM p hp
    ⟨I, hI.2, hpI⟩⟩
