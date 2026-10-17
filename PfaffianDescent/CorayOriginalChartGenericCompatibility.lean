import PfaffianDescent.CorayOriginalChartGenericEvaluation
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGenericCoefficientMap
import PfaffianDescent.SchemeModuleCanonicalChartFunctionField
import Mathlib.AlgebraicGeometry.Stalk

/-! Source-only / unverified. The actual affine chart section isomorphism
and generic germ reproduce the original scheme generic-point morphism.
Consequently its K coefficient map is the existing original structure-map
germ. No rational-image dimension, tangent rank, reduced member, or
auxiliary-line transversality is asserted. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u

section
variable {A : Type u} [CommRing A] {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The stored open-immersion section isomorphism has the SAME pullback
map on the actual image open. Only equality transports are removed. -/
theorem affineChartSectionIso_inv_appLE
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] :
    (IsOpenImmersion.ΓIsoTop i).inv =
      i.appLE i.opensRange ⊤ (by intro a _; exact ⟨a, rfl⟩) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.op_inv, eqToIso.hom,
    Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine chart's stored section isomorphism induces exactly the
actual affine-open inclusion, rather than an independently chosen point. -/
theorem affineChartSectionIso_spec
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] :
    Spec.map (((Scheme.ΓSpecIso (.of A)).symm ≪≫
      IsOpenImmersion.ΓIsoTop i).hom) ≫ i =
        (isAffineOpen_opensRange i).fromSpec := by
  have hcomp : Spec.map (IsOpenImmersion.ΓIsoTop i).inv ≫
      (isAffineOpen_opensRange i).fromSpec =
        Spec.map (Scheme.ΓSpecIso (.of A)).inv ≫ i := by
    rw [affineChartSectionIso_inv_appLE]
    exact (IsAffineOpen.SpecMap_appLE_fromSpec i
      (isAffineOpen_opensRange i) (isAffineOpen_top (Spec (.of A)))
      (by intro a _; exact ⟨a, rfl⟩)).trans (by
        rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv])
  change Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫
    (IsOpenImmersion.ΓIsoTop i).hom) ≫ i = _
  rw [Spec.map_comp, Category.assoc, ← hcomp, ← Category.assoc,
    ← Spec.map_comp]
  simp

variable [IsIntegral X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical chart evaluation lands at the ACTUAL original generic
point. This is the missing structural identity from packet002. -/
theorem affineChartGenericEvaluation_spec
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] [Nonempty i.opensRange] :
    Spec.map (CommRingCat.ofHom (affineChartGenericEvaluation i)) ≫ i =
      X.fromSpecStalk (genericPoint X) := by
  have hη : genericPoint X ∈ i.opensRange :=
    ((genericPoint_spec X).mem_open_set_iff i.opensRange.isOpen).mpr
      (by simpa using (inferInstance : Nonempty i.opensRange))
  change Spec.map ((((Scheme.ΓSpecIso (.of A)).symm ≪≫
    IsOpenImmersion.ΓIsoTop i).hom) ≫ X.germToFunctionField i.opensRange) ≫ i = _
  rw [Spec.map_comp, Category.assoc, affineChartSectionIso_spec]
  exact (isAffineOpen_opensRange i).fromSpecStalk_eq_fromSpecStalk hη

end

section
variable {K A : Type u} [Field K] [CommRing A]
  {X : Scheme.{u}} [IsIntegral X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original coefficient compatibility follows from the actual chart
base diagram, with no equality of chosen scalar actions assumed. -/
theorem affineChartGenericEvaluation_coefficient_spec
    (pi : X ⟶ Spec (.of K)) (i : Spec (.of A) ⟶ X)
    [IsOpenImmersion i] [Nonempty i.opensRange]
    (a : K →+* A) (hia : i ≫ pi = Spec.map (CommRingCat.ofHom a)) :
    Spec.map (CommRingCat.ofHom ((affineChartGenericEvaluation i).comp a)) =
      X.fromSpecStalk (genericPoint X) ≫ pi := by
  change Spec.map (CommRingCat.ofHom a ≫
    CommRingCat.ofHom (affineChartGenericEvaluation i)) = _
  rw [Spec.map_comp, ← hia, ← Category.assoc,
    affineChartGenericEvaluation_spec]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Its coefficient hom is the SAME original-pi generic germ already
used by the accepted scheme-module function-field action. -/
theorem affineChartGenericEvaluation_coefficient_eq
    (pi : X ⟶ Spec (.of K)) (i : Spec (.of A) ⟶ X)
    [IsOpenImmersion i] [Nonempty i.opensRange]
    (a : K →+* A) (hia : i ≫ pi = Spec.map (CommRingCat.ofHom a)) :
    (affineChartGenericEvaluation i).comp a = schemeFunctionFieldGroundRingHom pi := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have htop : (affineChartGenericEvaluation i).comp a =
      (X.germToFunctionField ⊤).hom.comp (schemeOpenBaseRingHom pi ⊤) := by
    exact serreIncidenceGenericCoefficientMap_eq pi
      (CommRingCat.ofHom ((affineChartGenericEvaluation i).comp a))
      (affineChartGenericEvaluation_coefficient_spec pi i a hia)
  ext c
  have hc := RingHom.congr_fun htop c
  simpa only [schemeFunctionFieldGroundRingHom, RingHom.comp_apply,
    schemeOpenBaseRingHom_top_apply] using hc

end

section
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original cubic's canonical generic evaluation retains its EXACT
original K coefficient hom, with the original chartBaseMap. -/
theorem cubicChartGenericEvaluation_coefficient_eq
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (hypersurface p hp)] (j : Fin 4)
    [Nonempty (chartι (equationIdeal p hp) j).opensRange] :
    (@affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)).comp
      (chartBaseMap (equationIdeal p hp) j) =
        schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp) := by
  exact @affineChartGenericEvaluation_coefficient_eq
    K (ChartRing (equationIdeal p hp) j)
    (inferInstance : Field K)
    (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (hypersurfaceToBase p hp) (chartι (equationIdeal p hp) j)
    (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
    (chartBaseMap (equationIdeal p hp) j) (chartι_toBase (equationIdeal p hp) j)

end
end PfaffianDescent.Coray
end
