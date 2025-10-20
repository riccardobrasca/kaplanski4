import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

variable {R : Type*}

/-- The set of ideals of a semiring R which do not intersect a given subsemigroup S -/
def kaplanskySet [Semiring R] (S : Subsemigroup R) :=
  { I : Ideal R | (I : Set R) ∩ S = ∅ }

theorem mem_kaplanskySet_iff_inter_eq_empty [Semiring R] (S : Subsemigroup R) (P : Ideal R) :
    P ∈ kaplanskySet S ↔ (P : Set R) ∩ S = ∅ := Iff.rfl

section Existence

/-- Every chain of 'Kaplansky.set S' has an upper bound. -/
theorem hypothesis_zorn_lemma [Semiring R] {S : Subsemigroup R} (hS : 0 ∉ S) (C : Set (Ideal R))
    (hC : C ⊆ kaplanskySet S) (hC₂ : IsChain (· ≤ ·) C) :
    ∃ P, P ∈ kaplanskySet S ∧ ∀ J, J ∈ C → J ≤ P := by
  by_cases h : C.Nonempty
  · obtain ⟨I, hI⟩ := h
    refine' ⟨sSup C, _, fun z hz ↦ le_sSup hz⟩
    rw [mem_kaplanskySet_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro x hx
    rcases (Submodule.mem_sSup_of_directed ⟨_, hI⟩ hC₂.directedOn).1 hx.1 with ⟨J, hJ₁, hJ₂⟩
    have hx₂ : (J : Set R) ∩ S ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨x, hJ₂, hx.2⟩
    exact hx₂ (hC hJ₁)
  · rw [Set.not_nonempty_iff_eq_empty.1 h]
    use ⊥
    rw [mem_kaplanskySet_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    simp
    exact hS

/-- The existence of a maximal element of 'Kaplansky.set S'
(which we will use to prove Kaplansky's criterion). -/
theorem exists_maximal_ideal [Semiring R] {S : Subsemigroup R} (hS : 0 ∉ S) :
    ∃ P ∈ kaplanskySet S, ∀ I ∈ kaplanskySet S, P ≤ I → I = P := by
  obtain ⟨P, hP⟩ := zorn_le₀ (kaplanskySet S) (hypothesis_zorn_lemma hS)
  exact ⟨P, hP.1, fun I hI H ↦ le_antisymm (hP.2 hI H) H⟩

end Existence

section Basic

/-- If an ideal P satisfies the condition P ∩ S = ∅, then P ≠ R
(this is used to prove that P is prime). -/
theorem ideal_neq_top [Semiring R] {S : Subsemigroup R} (hS : (S : Set R).Nonempty) {P : Ideal R}
    (hP : P ∈ kaplanskySet S) : P ≠ ⊤ := by
  intro h
  rw [kaplanskySet, h, Set.mem_setOf, Set.eq_empty_iff_forall_notMem] at hP
  rw [Set.nonempty_def] at hS
  obtain ⟨x, h₂⟩ := hS
  exact hP x (Set.mem_inter (Set.mem_univ x) h₂)

theorem exists_mem_inter [Semiring R] {S : Subsemigroup R} {P : Ideal R} {I : Ideal R}
    (hmax : ∀ I ∈ kaplanskySet S, P ≤ I → I = P) (h : P < I) : ∃ x : R, x ∈ (I : Set R) ∩ S :=
  Set.inter_nonempty.1
    (Set.nonempty_iff_ne_empty.2 fun h₂ ↦
      (lt_iff_le_and_ne.1 h).2 ((hmax I) h₂ (lt_iff_le_and_ne.1 h).1).symm)

/-- This is checked to prove that an ideal P which is maximal with respect to
the condition P ∩ S = ∅ is also prime. -/
theorem mem_or_mem_of_mul_mem [CommSemiring R] {P : Ideal R} {S : Subsemigroup R} (x y : R)
    (hP : P ∈ kaplanskySet S) (hmax : ∀ I ∈ kaplanskySet S, P ≤ I → I = P) :
    x * y ∈ P → x ∈ P ∨ y ∈ P := by
  intro hxy
  by_contra! h
  obtain ⟨h', h''⟩ := h
  let I := P ⊔ Ideal.span {x}
  let J := P ⊔ Ideal.span {y}
  have h₁ : ∃ x : R, x ∈ (I : Set R) ∩ S := by
    refine' exists_mem_inter hmax (lt_of_le_of_ne' le_sup_left _)
    intro hI
    rw [← hI, ← I.span_singleton_le_iff_mem] at h'
    exact h' le_sup_right
  have h₂ : ∃ x : R, x ∈ (J : Set R) ∩ S := by
    refine' exists_mem_inter hmax (lt_of_le_of_ne' le_sup_left _)
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
    Set.eq_empty_iff_forall_notMem.1 hP (s * t) ⟨h₃ (Ideal.mul_mem_mul hs ht), S.mul_mem hs' ht'⟩

-- NOTE: This already exist in mathlib as Ideal.isPrime_of_maximally_disjoint
/-- If an ideal P is maximal with respect to the condition P ∩ S = ∅, then it is prime. -/
theorem isPrime_of_maximal [CommSemiring R] {P : Ideal R} {S : Subsemigroup R}
    (hS : (S : Set R).Nonempty) (hP : P ∈ kaplanskySet S)
    (hmax : ∀ I ∈ kaplanskySet S, P ≤ I → I = P) : P.IsPrime :=
  ⟨ideal_neq_top hS hP, fun h ↦ mem_or_mem_of_mul_mem _ _ hP hmax h⟩

end Basic
section Kaplansky

local notation3 "P" => { r : R | Prime r }
local notation3 "S" => Submonoid.closure P

theorem ideal.span_ne_mem_kaplanski.set [CommSemiring R] [IsDomain R] {a : R} (ha : a ≠ 0)
    (H : ∀ (I : Ideal R) (_ : I ≠ ⊥) (_ : I.IsPrime), ∃ x ∈ I, Prime x)
    (hP : (P : Set R).Nonempty) :
    Ideal.span {a} ∉ kaplanskySet (Submonoid.toSubsemigroup S) := by
  have hzero : 0 ∉ S := by
    intro h
    rcases Submonoid.exists_multiset_of_mem_closure h with ⟨l, ⟨hl, hprod⟩⟩
    exact not_prime_zero (hl 0 (Multiset.prod_eq_zero_iff.1 hprod))
  intro h
  rcases exists_maximal_ideal hzero with ⟨T, hT, hT₂⟩
  have hT₃ : T ≠ ⊥ := by
    intro h₂
    rw [h₂] at hT₂
    exact ha (Ideal.span_singleton_eq_bot.1 (hT₂ (Ideal.span {a}) h (zero_le (Ideal.span {a}))))
  rw [Set.nonempty_def] at hP
  obtain ⟨x, hx⟩ := hP
  have := Set.mem_of_subset_of_mem Submonoid.subset_closure hx
  simp at this
  rw [← Submonoid.mem_toSubsemigroup] at this
  have := Set.nonempty_def.2 ⟨x, this⟩
  rcases (H T) hT₃ (isPrime_of_maximal this hT hT₂) with ⟨x, H₃, H₄⟩
  rw [mem_kaplanskySet_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem] at hT
  exact hT x ⟨H₃, Submonoid.subset_closure H₄⟩

theorem exists_prime_factors_of_exists_multiset [CommMonoidWithZero R] (a : R)
    (h : ∃ (l : Multiset R), ∃ (_ : ∀ y ∈ l, y ∈ {r | IsUnit r ∨ Prime r}), l.prod = a) :
    ∃ (f : Multiset R), (∀ b ∈ f, Prime b) ∧ Associated f.prod a := by
  rcases h with ⟨l ,hl, hl₂⟩
  revert a hl hl₂
  refine' l.induction (p := fun l ↦ ∀ a, (∀ y ∈ l, y ∈ {r | IsUnit r ∨ Prime r}) →
    l.prod = a → ∃ (f : Multiset R), (∀ b ∈ f, Prime b) ∧ Associated f.prod a) _ _
  · simp only [Multiset.notMem_zero, Set.mem_setOf_eq, IsEmpty.forall_iff, forall_const,
      Multiset.prod_zero, forall_eq']
    use 0
    simp only [Multiset.notMem_zero, IsEmpty.forall_iff, forall_const, Multiset.prod_zero,
      true_and]
    exact Associated.refl 1
  · simp only [Set.mem_setOf_eq, forall_apply_eq_imp_iff, Multiset.mem_cons, forall_eq_or_imp,
      Multiset.prod_cons, and_imp, forall_apply_eq_imp_iff₂]
    intros a s hind ha hs
    rcases ha with ha₁ | ha₂
    · rcases (hind hs) with ⟨f, hf, hf₂⟩
      exact ⟨f, hf, (associated_isUnit_mul_right_iff ha₁).2 hf₂⟩
    · rcases (hind hs) with ⟨f, hf, hf₂⟩
      refine' ⟨f.cons a, Multiset.forall_mem_cons.2 ⟨ha₂, hf⟩, _⟩
      rw [Multiset.prod_cons]
      exact Associated.mul_left a hf₂

/-- The other implication of Kaplansky's criterion (if every nonzero prime ideal of
an integral domain R contains a prime element, then R is a UFD). -/
theorem uniqueFactorizationMonoid_of_exists_prime [CommSemiring R] [IsDomain R]
    (H : ∀ (I : Ideal R) (_ : I ≠ ⊥) (_ : I.IsPrime), ∃ x ∈ I, Prime x)
    (hP : (P : Set R).Nonempty) : UniqueFactorizationMonoid R := by
  refine' UniqueFactorizationMonoid.of_exists_prime_factors fun a ha ↦ _
  have ha₂ := ideal.span_ne_mem_kaplanski.set ha H
  rw [mem_kaplanskySet_iff_inter_eq_empty] at ha₂
  rcases Set.nonempty_iff_ne_empty.2 (ha₂ hP) with ⟨x, ⟨hx, hx₂⟩⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (SetLike.mem_coe.1 hx)
  rw [← hb, mul_comm] at hx₂
  have hsubset : Submonoid.closure {r : R | Prime r} ≤
      Submonoid.closure {r : R | IsUnit r ∨ Prime r} := by
    refine Submonoid.closure_mono (Set.setOf_subset_setOf.2 (fun _ ha ↦ ?_))
    right
    exact ha
  refine exists_prime_factors_of_exists_multiset a ?_
  obtain ⟨l, hl⟩ := Submonoid.exists_multiset_of_mem_closure
    (divisor_closure_eq_closure _ _ (hsubset hx₂))
  exact ⟨l, by simpa only [Set.mem_setOf_eq, exists_prop]⟩

/-- Kaplansky's criterion (an integral domain R is a UFD if and only if every nonzero prime ideal
contains a prime element). -/
theorem uniqueFactorizationMonoid_iff [CommSemiring R] [IsDomain R] (hP : (P : Set R).Nonempty) :
  UniqueFactorizationMonoid R ↔ ∀ (I : Ideal R) (_ : I ≠ ⊥) (_ : I.IsPrime), ∃ x ∈ I, Prime x :=
  ⟨fun _ _ hI hI₂ ↦ Ideal.IsPrime.exists_mem_prime_of_ne_bot hI₂ hI,
    fun H ↦ uniqueFactorizationMonoid_of_exists_prime H hP⟩

end Kaplansky
