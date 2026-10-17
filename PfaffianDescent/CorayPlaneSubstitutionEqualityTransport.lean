import PfaffianDescent.CorayPlaneSectionSchemeIso
import PfaffianDescent.ProjectivePositiveTwist

/-! Equality transport for the actual plane substitution. The pair comparison
is constructed, and its coefficient pullback reduces to native pullbackId. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open PfaffianDescent.ProjectiveNegativeTwist
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

def planeSubstitutionPairSchemeIso
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ}
    (hp : p.IsHomogeneous d)
    (g : MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 3) R)
    (hdeg : ∀ (n : ℕ) (q : MvPolynomial (Fin 4) R),
      q.IsHomogeneous n → (g q).IsHomogeneous n)
    (hEq : g = planeHyperplaneRestrictionHom t) :
    hypersurface (g p) (hdeg d p hp) ≅
      scheme (planeSectionHomogeneousIdeal t p hp) := by
  subst g
  exact planeSectionSchemeIso t p hp

theorem planeSubstitutionEquationIdeal_eq
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ}
    (hp : p.IsHomogeneous d)
    (g : MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 3) R)
    (hdeg : ∀ (n : ℕ) (q : MvPolynomial (Fin 4) R),
      q.IsHomogeneous n → (g q).IsHomogeneous n)
    (hEq : g = planeHyperplaneRestrictionHom t) :
    equationIdeal (g p) (hdeg d p hp) =
      equationIdeal (planeHyperplaneRestrictionHom t p)
        (planeHyperplaneRestrictionHom_homogeneous t p hp) := by
  subst g
  rfl

def planeSubstitutionEquationSchemeIso
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ}
    (hp : p.IsHomogeneous d)
    (g : MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 3) R)
    (hdeg : ∀ (n : ℕ) (q : MvPolynomial (Fin 4) R),
      q.IsHomogeneous n → (g q).IsHomogeneous n)
    (hEq : g = planeHyperplaneRestrictionHom t) :
    hypersurface (g p) (hdeg d p hp) ≅
      hypersurface (planeHyperplaneRestrictionHom t p)
        (planeHyperplaneRestrictionHom_homogeneous t p hp) :=
  eqToIso (congrArg scheme (planeSubstitutionEquationIdeal_eq t p hp g hdeg hEq))

theorem planeSubstitutionPairSchemeIso_eq
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ}
    (hp : p.IsHomogeneous d)
    (g : MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 3) R)
    (hdeg : ∀ (n : ℕ) (q : MvPolynomial (Fin 4) R),
      q.IsHomogeneous n → (g q).IsHomogeneous n)
    (hEq : g = planeHyperplaneRestrictionHom t) :
    planeSubstitutionPairSchemeIso t p hp g hdeg hEq =
      (planeSubstitutionEquationSchemeIso t p hp g hdeg hEq).trans
        (planeSectionSchemeIso t p hp) := by
  subst g
  apply Iso.ext
  change (planeSectionSchemeIso t p hp).hom =
    𝟙 _ ≫ (planeSectionSchemeIso t p hp).hom
  exact (Category.id_comp _).symm

def planeSubstitutionInversePositiveTwistPullbackIso
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ}
    (hp : p.IsHomogeneous d)
    (g : MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 3) R)
    (hdeg : ∀ (n : ℕ) (q : MvPolynomial (Fin 4) R),
      q.IsHomogeneous n → (g q).IsHomogeneous n)
    (hEq : g = planeHyperplaneRestrictionHom t) (m : ℕ) :
    (Scheme.Modules.pullback (planeSubstitutionEquationSchemeIso t p hp g hdeg hEq).inv).obj
        (positiveSheafOfModules (grading (equationIdeal (g p) (hdeg d p hp))) m) ≅
      positiveSheafOfModules
        (grading (equationIdeal (planeHyperplaneRestrictionHom t p)
          (planeHyperplaneRestrictionHom_homogeneous t p hp))) m := by
  subst g
  change (Scheme.Modules.pullback (𝟙 _)).obj
      (positiveSheafOfModules
        (grading (equationIdeal (planeHyperplaneRestrictionHom t p)
          (planeHyperplaneRestrictionHom_homogeneous t p hp))) m) ≅ _
  exact (Scheme.Modules.pullbackId _).app _

theorem planeSubstitutionEquationSchemeIso_inv_toBase
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ}
    (hp : p.IsHomogeneous d)
    (g : MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 3) R)
    (hdeg : ∀ (n : ℕ) (q : MvPolynomial (Fin 4) R),
      q.IsHomogeneous n → (g q).IsHomogeneous n)
    (hEq : g = planeHyperplaneRestrictionHom t) :
    (planeSubstitutionEquationSchemeIso t p hp g hdeg hEq).inv ≫
      hypersurfaceToBase (g p) (hdeg d p hp) =
        hypersurfaceToBase (planeHyperplaneRestrictionHom t p)
          (planeHyperplaneRestrictionHom_homogeneous t p hp) := by
  subst g
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

end PfaffianDescent.Coray
