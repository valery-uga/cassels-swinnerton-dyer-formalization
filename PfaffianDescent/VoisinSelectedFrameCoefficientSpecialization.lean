import PfaffianDescent.VoisinSelectedIntrinsicFieldIdeal
import PfaffianDescent.VoisinAffineCoefficientGenericEvaluation

/-! Specializing a selected quadratic frame with its actual cubic
coefficient map gives the intrinsic ideal of the specialized points. -/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem selectedIntrinsicEightPointTriple_eq_specializedFrame_with_coefficients
    {K R F : Type u} [Field K] [CommRing R] [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → R)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (β : K →+* R) (f : R →+* F)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det) :
    let S := Localization.Away (quadraticMinorDet m x)
    let βS : K →+* S := (algebraMap R S).comp β
    let pS := p.map βS
    let hpS := hp.map βS
    let g := quadraticMinorSelectedPointLift m x f hm
    intrinsicEightPointTripleHomogeneousIdeal
      (p.map (f.comp β)) (hp.map (f.comp β))
      (fun k j => f (x k j)) =
      relativeTripleIntersectionHomogeneousIdeal
        (pS.map g)
        ((quadraticSelectedOpenPolynomial m x 0).map g)
        ((quadraticSelectedOpenPolynomial m x 1).map g)
        (hpS.map g)
        ((quadraticSelectedOpenPolynomial_isHomogeneous m x 0).map g)
        ((quadraticSelectedOpenPolynomial_isHomogeneous m x 1).map g) := by
  dsimp only
  let S := Localization.Away (quadraticMinorDet m x)
  let βS : K →+* S := (algebraMap R S).comp β
  let pS := p.map βS
  let hpS := hp.map βS
  let g := quadraticMinorSelectedPointLift m x f hm
  have hcoeff : g.comp βS = f.comp β := by
    change g.comp ((algebraMap R S).comp β) = f.comp β
    rw [← RingHom.comp_assoc, quadraticMinorSelectedPointLift_comp]
  have hpoly : pS.map g = p.map (f.comp β) := by
    change (p.map βS).map g = p.map (f.comp β)
    rw [MvPolynomial.map_map, hcoeff]
  have h := selectedIntrinsicEightPointTripleHomogeneousIdeal_eq_specializedFrame
    m x pS hpS f hm
  dsimp only at h
  have hleft :
      intrinsicEightPointTripleHomogeneousIdeal
        (p.map (f.comp β)) (hp.map (f.comp β))
        (fun k j => f (x k j)) =
      intrinsicEightPointTripleHomogeneousIdeal
        (pS.map g) (hpS.map g)
        (fun k j => f (x k j)) := by
    apply HomogeneousIdeal.ext
    rw [intrinsicEightPointTripleHomogeneousIdeal_toIdeal,
      intrinsicEightPointTripleHomogeneousIdeal_toIdeal, hpoly]
  exact hleft.trans h

end PfaffianDescent
