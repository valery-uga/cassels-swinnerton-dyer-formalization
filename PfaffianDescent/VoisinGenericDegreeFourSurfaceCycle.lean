import PfaffianDescent.VoisinGenericSelectedDegreeFourComplement
import PfaffianDescent.TripleCompleteIntersectionToHypersurface

/-! Push the selected generic residual cycle to the cubic surface. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

theorem DegreeFourTripleComplement.exists_surfaceDegreeFourCycle
    {F A : Type u} [Field F] [CommRing A] [Algebra F A]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (d : DegreeFourTripleComplement (A := A) p hp) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 :=
  exists_effectiveZeroCycle_on_hypersurface_of_triple
    p (d.e.q 0).1 (d.e.q 1).1 hp (d.e.q 0).2 (d.e.q 1).2
    4 d.cycle d.cycle_degree

theorem GenericCubicDegreeFourFamily.exists_surfaceDegreeFourCycle
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (d : GenericCubicDegreeFourFamily p hp) :
    letI : IsIntegral (cubicConfigurationBase p hp 8) := d.integral
    ∀ (a : CommRingCat.of F ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
        cubicConfigurationToBase p hp 8),
      ∃ z : EffectiveZeroCycle (hypersurface (p.map a.hom) (hp.map a.hom)),
        EffectiveZeroCycle.degree
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) z = 4 := by
  dsimp only
  letI : IsIntegral (cubicConfigurationBase p hp 8) := d.integral
  intro a ha
  let D := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  obtain ⟨c⟩ := d.cycles a ha
  exact c.exists_surfaceDegreeFourCycle (p.map a.hom) (hp.map a.hom)

end PfaffianDescent
