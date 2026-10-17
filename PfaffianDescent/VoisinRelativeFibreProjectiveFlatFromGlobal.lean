import PfaffianDescent.VoisinRelativeRingTwoCubicIntersection
import PfaffianDescent.VoisinRelativeZeroLocusFlat

/-!
# Flatness of the explicit two-cubic model from the actual Voisin family

The arbitrary-ring fibre presentation of the universal zero locus is an
isomorphism over the coefficient spectrum. Thus flatness of the actual
relative family descends to the explicit projective quotient model.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fixedCubicSurfaceEquationZeroLocusProjectiveRingFibre_flat_of_flatFamily
    {K T : Type u} [Field K] [CommRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (b : K →+* T) (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b)
    (hflat : Flat (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h)) :
    let q := (normalizedForm K (Fin 4) 3 j).map f
    let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
    Flat (toBase (equationIdeal (a.map b) (ha.map b) ⊔ equationIdeal q hq)) := by
  let q := (normalizedForm K (Fin 4) 3 j).map f
  let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  let eF := fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso
    a ha k h b s hs j f heq hb
  have hbase : eF.hom ≫
      toBase (equationIdeal (a.map b) (ha.map b) ⊔ equationIdeal q hq) =
      pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s :=
    fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso_toBase
      a ha k h b s hs j f heq hb
  letI : Flat (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) := hflat
  haveI : Flat (pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters
      a ha k h) s) := inferInstance
  haveI : Flat eF.inv := inferInstance
  have htotal : Flat (eF.inv ≫
      pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters
        a ha k h) s) := inferInstance
  have heqBase : eF.inv ≫
      pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters
        a ha k h) s =
      toBase (equationIdeal (a.map b) (ha.map b) ⊔ equationIdeal q hq) := by
    rw [← hbase, ← Category.assoc, eF.inv_hom_id, Category.id_comp]
  change Flat (toBase (equationIdeal (a.map b) (ha.map b) ⊔ equationIdeal q hq))
  rw [← heqBase]
  exact htotal

end PfaffianDescent
