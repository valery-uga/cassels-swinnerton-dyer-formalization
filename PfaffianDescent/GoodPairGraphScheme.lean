import PfaffianDescent.GoodPairGraphAlgebra
import PfaffianDescent.PolynomialRelativeDimension

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

noncomputable def goodPairGraphScheme : Scheme.{u} := Spec (.of (GoodPairGraphAlgebra K))

noncomputable def goodPairGraphToBase : goodPairGraphScheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (GoodPairGraphAlgebra K)))

/-- The standard first-two-form chart is affine three-space as a scheme over the base. -/
noncomputable def goodPairGraphSchemeIso (h2 : IsUnit (2 : K)) :
    goodPairGraphScheme K ≅ Spec (.of (MvPolynomial (Fin 3) K)) :=
  Scheme.Spec.mapIso (goodPairGraphEquiv K h2).symm.toRingEquiv.toCommRingCatIso.op

lemma goodPairGraphSchemeIso_toBase (h2 : IsUnit (2 : K)) :
    (goodPairGraphSchemeIso K h2).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K))) = goodPairGraphToBase K := by
  change Spec.map (CommRingCat.ofHom (goodPairGraphEquiv K h2).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (goodPairGraphEquiv K h2).symm.toAlgHom.comp_algebraMap

lemma goodPairGraphToBase_relativeDimension (h2 : IsUnit (2 : K)) :
    SmoothOfRelativeDimension 3 (goodPairGraphToBase K) := by
  let q := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K)))
  haveI : SmoothOfRelativeDimension 3 q := by
    simpa only [Nat.card_fin] using polynomial_smooth_relative_dimension K (Fin 3)
  have hs := smoothOfRelativeDimension_comp 0 3 (goodPairGraphSchemeIso K h2).hom q
  change SmoothOfRelativeDimension (0 + 3) ((goodPairGraphSchemeIso K h2).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K)))) at hs
  rw [goodPairGraphSchemeIso_toBase] at hs
  exact hs

end
end PfaffianDescent
