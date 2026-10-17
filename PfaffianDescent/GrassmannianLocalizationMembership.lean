import PfaffianDescent.GrassmannianLocalization

namespace PfaffianDescent
section
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] (U : Submonoid R) [IsLocalization U S]
  (f : M →ₗ[R] N) [IsLocalizedModule U f]

lemma localized_submodule_mem_iff (W : Submodule R M) (x : M) :
    f x ∈ W.localized' S U f ↔ ∃ s : U, s • x ∈ W := by
  rw [← Submodule.Quotient.mk_eq_zero]
  change W.toLocalizedQuotient' S U f (Submodule.Quotient.mk x) = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff U (W.toLocalizedQuotient' S U f)]
  simp only [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]

end
section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (a : R)
  [IsLocalization.Away a S] {m n : ℕ}

/-- Membership after a principal localization is witnessed by a power clearing the denominator. -/
lemma grassmannian_localized_mem_iff
    (W : Submodule R ((Fin m → R) × (Fin n → R))) (x : (Fin m → R) × (Fin n → R)) :
    graphCoefficientMap (algebraMap R S) x ∈ grassmannianSubmoduleBaseChange (algebraMap R S) W ↔
      ∃ e : ℕ, (a ^ e) • x ∈ W := by
  rw [grassmannianSubmoduleBaseChange_eq_localized R S m n (.powers a)]
  rw [← graphAlgebraCoefficientMap_apply R S m n x]
  rw [localized_submodule_mem_iff (.powers a)]
  constructor
  · rintro ⟨⟨s, e, rfl⟩, he⟩
    exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    exact ⟨⟨a ^ e, ⟨e, rfl⟩⟩, he⟩

end
end PfaffianDescent
