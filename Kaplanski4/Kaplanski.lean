import Mathlib.RingTheory.PrincipalIdealDomain
import Kaplanski4.Absorbing

variable {R : Type _} [CommRing R] (S : Submonoid R)

/-- The set of ideals of the ring R which do not intersect the submonoid S -/
def Kaplanski.set :=
  { I : Ideal R | (I : Set R) ∩ S = ∅ }

theorem Kaplanski.set_def {P : Ideal R} : P ∈ Kaplanski.set S ↔ (P : Set R) ∩ S = ∅ :=
  Iff.rfl

variable {P : Ideal R} {S} (hP : P ∈ Kaplanski.set S) (hmax : ∀ I ∈ Kaplanski.set S, P ≤ I → I = P)

section Basic

theorem ideal_neq_top : P ≠ ⊤ := fun h =>
  ((Set.disjoint_left.1 (Set.disjoint_iff_inter_eq_empty.2 ((Kaplanski.set_def _).1 hP)))
      (P.eq_top_iff_one.1 h)) S.one_mem

theorem exists_mem_inter_of_gt {I : Ideal R} (h : P < I) : ∃ x : R, x ∈ (I : Set R) ∩ S :=
  Set.inter_nonempty.1
    (Set.nonempty_iff_ne_empty.2 fun h₂ =>
      (lt_iff_le_and_ne.1 h).2 ((hmax I) h₂ (lt_iff_le_and_ne.1 h).1).symm)

theorem mem_or_mem_of_mul_mem (x y : R) : x * y ∈ P → x ∈ P ∨ y ∈ P := by
  intro hxy
  by_contra h
  push_neg  at h
  cases' h with h' h''
  let I := P ⊔ Ideal.span {x}
  let J := P ⊔ Ideal.span {y}
  have h₁ : ∃ x : R, x ∈ (I : Set R) ∩ S := by
    refine' exists_mem_inter_of_gt hmax (lt_of_le_of_ne' le_sup_left _)
    intro hI
    rw [← hI, ← I.span_singleton_le_iff_mem] at h'
    exact h' le_sup_right
  have h₂ : ∃ x : R, x ∈ (J : Set R) ∩ S := by
    refine' exists_mem_inter_of_gt hmax (lt_of_le_of_ne' le_sup_left _)
    intro hJ
    rw [← hJ, ← J.span_singleton_le_iff_mem] at h''
    exact h'' le_sup_right
  rcases h₁, h₂ with ⟨⟨s, ⟨hs, hs'⟩⟩, ⟨t, ⟨ht, ht'⟩⟩⟩
  have h₃ : I * J ≤ P := by
    rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul, Ideal.span_singleton_mul_span_singleton]
    exact
      sup_le (sup_le Ideal.mul_le_right Ideal.mul_le_left)
        (sup_le Ideal.mul_le_right (P.span_singleton_le_iff_mem.2 hxy))
  exact
    Set.eq_empty_iff_forall_not_mem.1 hP (s * t) ⟨h₃ (Ideal.mul_mem_mul hs ht), S.mul_mem hs' ht'⟩

theorem isPrime_of_maximal : P.IsPrime :=
  ⟨ideal_neq_top hP, fun h => mem_or_mem_of_mul_mem hP hmax _ _ h⟩

end Basic

section Existence

theorem hypothesis_zorn_lemma (C : Set (Ideal R)) (hC : C ⊆ Kaplanski.set S) (hC₂ : IsChain (· ≤ ·) C)
    (I : Ideal R) (hI : I ∈ C) : ∃ P, P ∈ Kaplanski.set S ∧ ∀ J, J ∈ C → J ≤ P := by
  refine' ⟨supₛ C, _, fun z hz => le_supₛ hz⟩
  rw [Kaplanski.set_def, Set.eq_empty_iff_forall_not_mem]
  rintro x hx
  rcases (Submodule.mem_supₛ_of_directed ⟨_, hI⟩ hC₂.directedOn).1 hx.1 with ⟨J, hJ₁, hJ₂⟩
  have hx₂ : (J : Set R) ∩ S ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨x, hJ₂, hx.2⟩
  exact hx₂ (hC hJ₁)

theorem exists_maximal_ideal (hS : 0 ∉ S) : ∃ P ∈ Kaplanski.set S, ∀ I ∈ Kaplanski.set S, P ≤ I → I = P := by
  have hx : 0 ∈ Kaplanski.set S := by
    rw [Kaplanski.set_def, Set.eq_empty_iff_forall_not_mem]
    rintro y ⟨hy₁, hy₂⟩
    rw [SetLike.mem_coe, Ideal.zero_eq_bot, Ideal.mem_bot] at hy₁
    rw [hy₁] at hy₂
    exact hS hy₂
  rcases zorn_nonempty_partialOrder₀ _ hypothesis_zorn_lemma _ hx with ⟨J, ⟨hJ, ⟨_, hJ₃⟩⟩⟩
  exact ⟨J, hJ, hJ₃⟩

end Existence

section Kaplansky

theorem Multiset.prod_mem_ideal {I : Ideal R} (s : Multiset R) (hI : I.IsPrime) :
    s.prod ∈ I ↔ ∃ (p : R)(_ : p ∈ s), p ∈ I := by
  classical
    constructor
    · intro hs
      by_contra h
      push_neg  at h
      have hs₃ : s.prod ∉ I
      refine' Multiset.prod_induction _ _ _ _ h
      · rintro a b ha hb
        by_contra h
        cases' (Ideal.isPrime_iff.1 hI).2 h with hI₂ hI₃
        exact ha hI₂
        exact hb hI₃
      exact fun h₂ => (Ideal.isPrime_iff.1 hI).1 ((Ideal.eq_top_iff_one _).2 h₂)
      exact hs₃ hs
    · intro hs
      rcases hs with ⟨p, ⟨hs₂, hs₃⟩⟩
      rw [← Multiset.prod_erase hs₂]
      exact Ideal.mul_mem_right _ _ hs₃

variable (R)

/-- The set of prime elements. -/
def primes :=
  { r : R | Prime r }

variable [IsDomain R]

variable {R}

theorem theo1_droite [UniqueFactorizationMonoid R] {I : Ideal R} (hI : I ≠ ⊥) (hI₂ : I.IsPrime) :
    ∃ x ∈ I, Prime x := by
  classical
    have ha : ∃ a : R, a ∈ I ∧ a ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rcases ha with ⟨a, ⟨ha₁, ha₂⟩⟩
    cases' UniqueFactorizationMonoid.factors_prod ha₂ with u ha₃
    rw [← ha₃] at ha₁
    cases' (Ideal.IsPrime.mem_or_mem hI₂) ha₁ with ha₄ ha₅
    · rcases(Multiset.prod_mem_ideal (UniqueFactorizationMonoid.factors a) hI₂).1 ha₄ with
        ⟨p, ⟨ha₅, ha₆⟩⟩
      refine' ⟨p, ha₆, UniqueFactorizationMonoid.prime_of_factor p ha₅⟩
    · exfalso
      exact (Ideal.isPrime_iff.1 hI₂).1 (Ideal.eq_top_of_isUnit_mem _ ha₅ (Units.isUnit u))

variable (R)

theorem primes_mem_mul : (Submonoid.closure (primes R)).Absorbing := by
  classical
    rw [Submonoid.absorbing_iff_of_comm]
    intro a b hab
    obtain ⟨m, hm⟩ := Submonoid.exists_multiset_of_mem_closure hab
    revert hm a b
    refine' Multiset.strongInductionOn m _
    rintro s hind b a _ ⟨hprime, hprod⟩
    rcases s.empty_or_exists_mem with (hempty | ⟨i, hi⟩)
    · simp [hempty] at hprod
      exact ⟨1, Submonoid.one_mem _, associated_one_of_mul_eq_one _ hprod.symm⟩
    rw [← Multiset.prod_erase hi] at hprod
    rcases(hprime i hi).dvd_or_dvd ⟨(s.erase i).prod, hprod.symm⟩ with (⟨x, hxb⟩ | ⟨x, hxa⟩)
    · suffices ∃ z ∈ Submonoid.closure (primes R), Associated x z by
        obtain ⟨z, hz, hzx⟩ := this
        refine' ⟨z * i, Submonoid.mul_mem _ hz (Submonoid.subset_closure (hprime _ hi)), _⟩
        rw [hxb, mul_comm z i]
        exact Associated.mul_left i hzx
      rw [hxb, mul_assoc] at hprod
      replace hprod := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (hprime _ hi).ne_zero hprod
      have hxamem : x * a ∈ Submonoid.closure (primes R) := by
        rw [← hprod]
        exact Submonoid.multiset_prod_mem _ _ fun x hx =>
          Submonoid.subset_closure (hprime _ (Multiset.erase_subset _ _ hx))
      exact hind (s.erase i) (Multiset.erase_lt.2 hi) _ _ hxamem
        ⟨fun y hy => hprime y ((s.erase_subset _) hy), hprod⟩
    · rw [hxa, ← mul_assoc, mul_comm b i, mul_assoc] at hprod
      replace hprod := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (hprime i hi).ne_zero hprod
      have hbxmem : b * x ∈ Submonoid.closure (primes R) := by
        rw [← hprod]
        exact Submonoid.multiset_prod_mem _ _ fun x hx =>
          Submonoid.subset_closure (hprime _ (Multiset.erase_subset _ _ hx))
      exact hind (s.erase i) (Multiset.erase_lt.2 hi) _ _ hbxmem
        ⟨fun y hy => hprime y ((s.erase_subset _) hy), hprod⟩

variable {R}

theorem theo1_gauche (H : ∀ (I : Ideal R) (_ : I ≠ ⊥) (_ : I.IsPrime), ∃ x ∈ I, Prime x) :
    UniqueFactorizationMonoid R := by
  let S := Submonoid.closure (primes R)
  have hzero : (0 : R) ∉ S
  intro h
  rcases Submonoid.exists_multiset_of_mem_closure h with ⟨l, ⟨hl, hprod⟩⟩
  exact not_prime_zero (hl 0 (Multiset.prod_eq_zero_iff.1 hprod))
  refine' UniqueFactorizationMonoid.of_exists_prime_factors fun a ha => _
  have ha₂ : Ideal.span {a} ∉ Kaplanski.set S := by
    intro h
    rcases exists_maximal_ideal hzero with ⟨P, ⟨hP, hP₂⟩⟩
    have hP₃ : P ≠ 0 := by
      intro h₂
      rw [h₂, Ideal.zero_eq_bot] at hP₂
      exact ha (Ideal.span_singleton_eq_bot.1 (hP₂ (Ideal.span {a}) h (zero_le (Ideal.span {a}))))
    rcases(H P) hP₃ (isPrime_of_maximal hP hP₂) with ⟨x, ⟨H₃, H₄⟩⟩
    rw [Kaplanski.set_def, Set.eq_empty_iff_forall_not_mem] at hP
    exact hP x ⟨H₃, Submonoid.subset_closure H₄⟩
  rw [Kaplanski.set_def, ← Ne.def] at ha₂
  rcases Set.nonempty_iff_ne_empty.2 ha₂ with ⟨x, ⟨hx, hx₂⟩⟩
  cases' Ideal.mem_span_singleton'.1 (SetLike.mem_coe.1 hx) with b hb
  rw [← hb, mul_comm] at hx₂
  obtain ⟨z, hzmem, hass⟩ := Submonoid.absorbing_iff_of_comm.1 (primes_mem_mul _) _ _ hx₂
  obtain ⟨m, hprime, hprod⟩ := Submonoid.exists_multiset_of_mem_closure hzmem
  refine' ⟨m, hprime, _⟩
  rwa [hprod, Associated.comm]

end Kaplansky