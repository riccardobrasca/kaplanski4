import Kaplanski4.Kaplanski
import Mathlib.RingTheory.Localization.Ideal

lemma is_localization.prime_of_prime {R S : Type _} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R] {M : Submonoid R} [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) (p : R) (hp : Prime p) (hp₂ : ∃ (I : Ideal R),
  Disjoint (M : Set R) (I : Set R) ∧ p ∈ I) : Prime ((algebraMap R S) p) := by
  rcases hp₂ with ⟨I, hI, hp₂⟩
  have hp' := IsLocalization.isPrime_of_isPrime_disjoint M S (Ideal.span {p}) ((Ideal.span_singleton_prime hp.ne_zero).2 hp)
    (Set.disjoint_of_subset_right (I.span_singleton_le_iff_mem.2 hp₂) hI)
  rw [Ideal.map_span, Set.image_singleton] at hp'
  exact (Ideal.span_singleton_prime (fun hp₃ => hp.ne_zero ((IsLocalization.to_map_eq_zero_iff S hM).1 hp₃))).1 hp'

example {R S : Type _} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R] {M : Submonoid R}
  [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) [UniqueFactorizationMonoid R] :
  @UniqueFactorizationMonoid S (@IsDomain.toCancelCommMonoidWithZero S _
    (IsLocalization.isDomain_of_le_nonZeroDivisors _ hM)) := by
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  refine' uniqueFactorizationMonoid_of_exists_prime _ (fun J hJzero hJprime => _)
  set I := J.comap (algebraMap R S) with Idef
  have hIprime : I.IsPrime := ((IsLocalization.isPrime_iff_isPrime_disjoint M S J).1 hJprime).1
  have hI : I ≠ ⊥
  { intro h
    refine' hJzero _
    rw [← IsLocalization.map_comap M S J, ← Idef, h, Ideal.map_bot] }
  obtain ⟨p, hpI, hp⟩ := exists_prime_of_uniqueFactorizationMonoid _ hI hIprime
  refine' ⟨algebraMap R S p, Ideal.mem_comap.mp hpI, _⟩
  exact is_localization.prime_of_prime hM p hp ⟨I, ⟨(((IsLocalization.isPrime_iff_isPrime_disjoint M S J).1 hJprime).2), hpI⟩⟩