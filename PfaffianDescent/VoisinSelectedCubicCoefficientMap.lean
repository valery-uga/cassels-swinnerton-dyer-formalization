import PfaffianDescent.VoisinSelectedRelativeFiniteNeighborhood
import PfaffianDescent.SchemeAffineFunctions

/-!
# Cubic coefficients on an affine configuration chart

A chart over a coefficient field has an actual ring map from the field into
its global functions.  At a field-valued section, this map specializes back
to the identity.  This is the coefficient compatibility needed to put the
fixed cubic in the determinant-open relative family.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem affineFunctionHom_section_leftInverse
    {L : Type u} [Field L] {U : Scheme.{u}}
    (t : U ⟶ Spec (.of L))
    (a : Spec (.of L) ⟶ U)
    (ha : a ≫ t = 𝟙 (Spec (.of L))) :
    ((Scheme.ΓSpecIso (.of L)).hom.hom.comp a.appTop.hom).comp
      (affineFunctionHom t) = RingHom.id L := by
  apply RingHom.ext
  intro z
  have hcomp := affineFunctionHom_comp a t
  have h := congrArg (fun φ : L →+* Γ(Spec (.of L), ⊤) =>
    (Scheme.ΓSpecIso (.of L)).hom.hom (φ z)) hcomp
  rw [ha] at h
  simpa [affineFunctionHom, Scheme.Hom.id_appTop, RingHom.comp_apply] using h.symm

theorem cubicCoefficientMap_selectedSpecialization
    {L : Type u} [Field L] {U : Scheme.{u}}
    (t : U ⟶ Spec (.of L))
    (a : Spec (.of L) ⟶ U)
    (ha : a ≫ t = 𝟙 (Spec (.of L)))
    (p : MvPolynomial (Fin 4) L) :
    (p.map (affineFunctionHom t)).map
      ((Scheme.ΓSpecIso (.of L)).hom.hom.comp a.appTop.hom) = p := by
  rw [MvPolynomial.map_map]
  rw [affineFunctionHom_section_leftInverse t a ha]
  exact MvPolynomial.map_id p

/-- After passing from the affine chart to the selected determinant open,
the fixed cubic still specializes to its original coefficients. -/
theorem cubicCoefficientMap_selectedLocalizationSpecialization
    {R : Type u} [CommRing R]
    {F : Type u} [Field F]
    (m : Fin 8 ↪ AllCharacteristics.UniversalHomogeneous.Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det)
    (β : F →+* R) (hβ : f.comp β = RingHom.id F)
    (p : MvPolynomial (Fin 4) F) :
    (p.map ((algebraMap R (Localization.Away (quadraticMinorDet m x))).comp β)).map
      (quadraticMinorSelectedPointLift m x f hm) = p := by
  rw [MvPolynomial.map_map, ← RingHom.comp_assoc,
    quadraticMinorSelectedPointLift_comp, hβ, MvPolynomial.map_id]

/-- With the actual coefficient-field map on a selected affine chart,
the generic cubic and the local quadratic frame form a finite family near
the generic point of the determinant open. -/
theorem genericCubic_selectedOpenFrame_exists_genericFiniteNeighborhood
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L)
    {R : Type u} [CommRing R] [IsDomain R]
    (m : Fin 8 ↪ AllCharacteristics.UniversalHomogeneous.Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → R)
    (f : R →+* L)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det)
    [IsDomain (Localization.Away (quadraticMinorDet m x))]
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (hfx : ∀ k j, f (x k j) = normalizedVectorInLinearChart c (y k) j)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun j k => y k j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ k,
      (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y k) = 0 ∧
      (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y k) = 0)
    (β : L →+* R) (hβ : f.comp β = RingHom.id L) :
    let pS := ((genericCubicTensor K).map φ).toMvPolynomial.map
      ((algebraMap R (Localization.Away (quadraticMinorDet m x))).comp β)
    let hpS : pS.IsHomogeneous 3 :=
      (cubic_toMvPolynomial_isHomogeneous_three _).map _
    ∃ V : (Spec (.of (Localization.Away (quadraticMinorDet m x)))).Opens,
      genericPoint (Spec (.of (Localization.Away (quadraticMinorDet m x)))) ∈ V ∧
      IsFinite ((relativeTripleIntersectionToBase pS
        (quadraticSelectedOpenPolynomial m x 0)
        (quadraticSelectedOpenPolynomial m x 1) hpS
        (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
        (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)) ∣_ V) := by
  dsimp only
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let βS := (algebraMap R (Localization.Away (quadraticMinorDet m x))).comp β
  let pS := p.map βS
  have hpS : pS.IsHomogeneous 3 :=
    (cubic_toMvPolynomial_isHomogeneous_three _).map βS
  have hspec : pS.map (quadraticMinorSelectedPointLift m x f hm) = p := by
    exact cubicCoefficientMap_selectedLocalizationSpecialization
      m x f hm β hβ p
  have hideal : tripleCompleteIntersectionHomogeneousIdeal
      (pS.map (quadraticMinorSelectedPointLift m x f hm))
      (splitQuadraticPencil L 0).1 (splitQuadraticPencil L 1).1
      (hpS.map (quadraticMinorSelectedPointLift m x f hm))
      (splitQuadraticPencil L 0).2 (splitQuadraticPencil L 1).2 =
      tripleCompleteIntersectionHomogeneousIdeal p
        (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3))
        (cubic_toMvPolynomial_isHomogeneous_three _)
        ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
        ((isHomogeneous_X L 3).mul
          (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
            (isHomogeneous_X L 3))) := by
    apply HomogeneousIdeal.ext
    change Ideal.span ({pS.map (quadraticMinorSelectedPointLift m x f hm),
      (X 1 * X 2 : MvPolynomial (Fin 4) L),
      X 3 * (X 1 + X 2 + X 3)} : Set _) =
      Ideal.span ({p, X 1 * X 2, X 3 * (X 1 + X 2 + X 3)} : Set _)
    rw [hspec]
  haveI : IsFinite (AllCharacteristics.HomogeneousProjective.toBase
      (tripleCompleteIntersectionHomogeneousIdeal
        (pS.map (quadraticMinorSelectedPointLift m x f hm))
        (splitQuadraticPencil L 0).1 (splitQuadraticPencil L 1).1
        (hpS.map (quadraticMinorSelectedPointLift m x f hm))
        (splitQuadraticPencil L 0).2 (splitQuadraticPencil L 1).2)) := by
    rw [hideal]
    exact generic_split_intersection_finite K φ
  exact quadraticSelectedOpenFrame_exists_genericFiniteNeighborhood
    m x f hm y c hc hfx hsurj hquad pS hpS

end PfaffianDescent
