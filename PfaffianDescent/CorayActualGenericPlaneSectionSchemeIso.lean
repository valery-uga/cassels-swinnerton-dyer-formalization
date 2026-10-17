import PfaffianDescent.CorayPlaneSectionSchemeIso
import PfaffianDescent.CorayActualGenericPlaneSectionImmersion

/-! SOURCE ONLY / UNVERIFIED002. The literal parameter-field ideal (p_L,H)
has the SAME actual149 linear-section Proj, via explicit inverse graded
quotient maps. Its canonical original-cubic immersion commutes with the SAME
actual149 closed immersion. No geometric component is selected. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual homogeneous pair ideal is the SAME original coefficient
extension plus the literal generic hyperplane, without saturation. -/
def genericPlaneSectionPairIdeal {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) (GenericHyperplaneField K)) :=
  planeSectionHomogeneousIdeal (genericHyperplaneCoefficient (K := K))
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)

/-- Its underlying ideal is EXACTLY (p_L,H), the literal four-variable pair. -/
theorem genericPlaneSectionPairIdeal_toIdeal {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) :
    (genericPlaneSectionPairIdeal p hp).toIdeal =
      Ideal.span {p.map (algebraMap K (GenericHyperplaneField K)),
        genericHyperplaneEquation (K := K)} := by
  exact planeSectionHomogeneousIdeal_toIdeal _ _ (hp.map _)

/-- Literal restricted-equation Proj is the actual four-variable pair Proj. -/
def genericPlaneCubicPairSchemeIso {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp) ≅
      scheme (genericPlaneSectionPairIdeal p hp) :=
  planeSectionSchemeIso _ _ (hp.map _)

/-- Transport the substitution and its dependent degree proof together. -/
private def planePairSubstitutionIso002 {R : Type u} [CommRing R]
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ}
    (hp : p.IsHomogeneous d)
    (g : MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 3) R)
    (hdeg : ∀ (n : ℕ) (q : MvPolynomial (Fin 4) R),
      q.IsHomogeneous n → (g q).IsHomogeneous n)
    (hEq : g = planeHyperplaneRestrictionHom t) :
    hypersurface (g p) (hdeg d p hp) ≅ scheme (planeSectionHomogeneousIdeal t p hp) := by
  subst g
  exact planeSectionSchemeIso t p hp

/-- Equality elimination also retains the actual induced projective map. -/
private theorem planePairSubstitutionIso002_hom_immersion {R : Type u} [CommRing R]
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ}
    (hp : p.IsHomogeneous d)
    (g : MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 3) R)
    (hdeg : ∀ (n : ℕ) (q : MvPolynomial (Fin 4) R),
      q.IsHomogeneous n → (g q).IsHomogeneous n)
    (hEq : g = planeHyperplaneRestrictionHom t)
    (hI : (equationIdeal p hp).toIdeal ≤
      (equationIdeal (g p) (hdeg d p hp)).toIdeal.comap g.toRingHom)
    (hg : Function.Surjective g) :
    (planePairSubstitutionIso002 t p hp g hdeg hEq).hom ≫
      planeSectionPairImmersion t p hp =
        PfaffianDescent.polynomialProjectiveMap (equationIdeal p hp)
          (equationIdeal (g p) (hdeg d p hp)) g hI hdeg hg := by
  subst g
  exact planeSectionSchemeIso_hom_immersion t p hp

/-- The transported isomorphism has the same coefficient structure map. -/
private theorem planePairSubstitutionIso002_hom_toBase {R : Type u} [CommRing R]
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ}
    (hp : p.IsHomogeneous d)
    (g : MvPolynomial (Fin 4) R →ₐ[R] MvPolynomial (Fin 3) R)
    (hdeg : ∀ (n : ℕ) (q : MvPolynomial (Fin 4) R),
      q.IsHomogeneous n → (g q).IsHomogeneous n)
    (hEq : g = planeHyperplaneRestrictionHom t) :
    (planePairSubstitutionIso002 t p hp g hdeg hEq).hom ≫
      toBase (planeSectionHomogeneousIdeal t p hp) =
        hypersurfaceToBase (g p) (hdeg d p hp) := by
  subst g
  exact planeSectionSchemeIso_hom_toBase t p hp

/-- The actual native149 linear-section source is the SAME pair-ideal Proj,
by the proved rectangular/literal substitution equality. -/
def actualGenericPlanePairSchemeIso {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    PfaffianDescent.linearHypersurfaceSection (genericPlaneInclusionMatrix (K := K))
      (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _) ≅
      scheme (genericPlaneSectionPairIdeal p hp) := by
  exact planePairSubstitutionIso002 (genericHyperplaneCoefficient (K := K))
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)
    (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K)))
    (fun _ q hq => PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) hq)
    genericPlaneInclusionMatrix_substitution

/-- Canonical original-cubic immersion of the literal pair-ideal scheme. -/
def actualGenericPlanePairImmersion {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    scheme (genericPlaneSectionPairIdeal p hp) ⟶
      hypersurface (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _) :=
  planeSectionPairImmersion _ _ (hp.map _)

instance actualGenericPlanePairImmersion_isClosedImmersion {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    IsClosedImmersion (actualGenericPlanePairImmersion p hp) := by
  exact planeSectionPairImmersion_isClosedImmersion
    (genericHyperplaneCoefficient (K := K))
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)

/-- The actual SAME-Proj isomorphism and the canonical original immersion
recover EXACTLY149's original linear-section closed immersion. -/
theorem actualGenericPlanePairSchemeIso_hom_immersion {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (actualGenericPlanePairSchemeIso p hp).hom ≫ actualGenericPlanePairImmersion p hp =
      actualGenericPlaneSectionImmersion p hp := by
  exact planePairSubstitutionIso002_hom_immersion
    (genericHyperplaneCoefficient (K := K))
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)
    (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K)))
    (fun _ q hq => PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) hq)
    genericPlaneInclusionMatrix_substitution
    (PfaffianDescent.linearSection_ideal_le (genericPlaneInclusionMatrix (K := K))
      (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _))
    (PfaffianDescent.rectangularSubstitution_surjective
      (genericPlaneInclusionMatrix (K := K))
      (PfaffianDescent.coordinateOmission (K := GenericHyperplaneField K) (n := 3) 0)
      genericPlaneInclusionMatrix_leftInverse)

/-- The same-Proj comparison is over the literal parameter-field spectrum. -/
theorem actualGenericPlanePairSchemeIso_hom_toBase {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (actualGenericPlanePairSchemeIso p hp).hom ≫ toBase (genericPlaneSectionPairIdeal p hp) =
      hypersurfaceToBase
        (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K))
          (p.map (algebraMap K (GenericHyperplaneField K))))
        (PfaffianDescent.rectangularSubstitution_homogeneous
          (genericPlaneInclusionMatrix (K := K)) (hp.map _)) := by
  exact planePairSubstitutionIso002_hom_toBase
    (genericHyperplaneCoefficient (K := K))
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)
    (PfaffianDescent.rectangularSubstitution (genericPlaneInclusionMatrix (K := K)))
    (fun _ q hq => PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) hq)
    genericPlaneInclusionMatrix_substitution

end PfaffianDescent.Coray

