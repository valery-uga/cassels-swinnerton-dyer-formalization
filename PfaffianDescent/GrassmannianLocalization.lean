import PfaffianDescent.GrassmannianQuotientBaseChange
import Mathlib.RingTheory.LocalProperties.Submodule

namespace PfaffianDescent
open TensorProduct
section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (m n : ℕ)

/-- The coefficient map, viewed as a linear map over the original scalar ring. -/
noncomputable def graphAlgebraCoefficientMap :
    ((Fin m → R) × (Fin n → R)) →ₗ[R] ((Fin m → S) × (Fin n → S)) :=
  (graphTensorEquiv R S m n).toLinearMap.restrictScalars R |>.comp
    (TensorProduct.mk R S ((Fin m → R) × (Fin n → R)) 1)

lemma graphAlgebraCoefficientMap_apply (x : (Fin m → R) × (Fin n → R)) :
    graphAlgebraCoefficientMap R S m n x = graphCoefficientMap (algebraMap R S) x :=
  graphTensorEquiv_one_tmul R S m n x

variable (U : Submonoid R) [IsLocalization U S]

instance graphAlgebraCoefficientMap_isLocalizedModule :
    IsLocalizedModule U (graphAlgebraCoefficientMap R S m n) :=
  IsLocalizedModule.of_linearEquiv U
    (TensorProduct.mk R S ((Fin m → R) × (Fin n → R)) 1)
    ((graphTensorEquiv R S m n).restrictScalars R)

lemma grassmannianSubmoduleBaseChange_eq_localized
    (W : Submodule R ((Fin m → R) × (Fin n → R))) :
    grassmannianSubmoduleBaseChange (algebraMap R S) W =
      W.localized' S U (graphAlgebraCoefficientMap R S m n) := by
  rw [Submodule.localized'_eq_span]
  have he : (graphAlgebraCoefficientMap R S m n : _ → _) = graphCoefficientMap (algebraMap R S) := by
    funext x
    exact graphAlgebraCoefficientMap_apply R S m n x
  rw [he]
  rfl

end
section
variable (R : Type*) [CommRing R] {m n : ℕ}

/-- Ambient submodules are determined by their scalar extensions to prime localizations. -/
theorem grassmannianSubmodule_eq_of_localization
    {W Z : Submodule R ((Fin m → R) × (Fin n → R))}
    (h : ∀ p : PrimeSpectrum R,
      grassmannianSubmoduleBaseChange (algebraMap R (Localization.AtPrime p.asIdeal)) W =
        grassmannianSubmoduleBaseChange (algebraMap R (Localization.AtPrime p.asIdeal)) Z) : W = Z := by
  apply Submodule.eq_of_localization_maximal
    (fun p _ => Localization.AtPrime p)
    (fun p _ => (Fin m → Localization.AtPrime p) × (Fin n → Localization.AtPrime p))
    (fun p _ => graphAlgebraCoefficientMap R (Localization.AtPrime p) m n)
  intro p hp
  rw [← grassmannianSubmoduleBaseChange_eq_localized,
    ← grassmannianSubmoduleBaseChange_eq_localized]
  exact h ⟨p, inferInstance⟩

end
end PfaffianDescent
