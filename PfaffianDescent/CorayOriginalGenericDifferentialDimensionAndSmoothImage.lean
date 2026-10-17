import PfaffianDescent.CorayOriginalChartFunctionFieldGeneration
import PfaffianDescent.CorayBoundedOriginalEvaluationImage
import PfaffianDescent.SmoothCubicActualKaehlerChartFiberDimension
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.CharP.Algebra

/-! Genuine original generic differential dimension and SAME-image smooth
open. No rank-two/open certificate is a premise. SOURCE ONLY / UNCOMPILED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial KaehlerDifferential TopologicalSpace
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u

/-- The literal affine generic evaluation makes ORIGINAL F the fraction
field of this ACTUAL chart algebra. Injectivity and all actual chart
fractions are derived from the nonempty integral affine chart. -/
theorem affineChartGenericEvaluation_isFractionRing
    {A : Type u} [CommRing A] {X : Scheme.{u}} [IsIntegral X]
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] [Nonempty i.opensRange] :
    letI : Algebra A X.functionField := (affineChartGenericEvaluation i).toAlgebra
    IsFractionRing A X.functionField := by
  letI : Algebra A X.functionField := (affineChartGenericEvaluation i).toAlgebra
  letI : FaithfulSMul A X.functionField :=
    (faithfulSMul_iff_algebraMap_injective A X.functionField).mpr
      (affineChartGenericEvaluation_injective i)
  exact IsFractionRing.of_field A X.functionField fun z => by
    obtain ⟨a, b, hb, hab⟩ := affineChartGenericEvaluation_div_surjective i z
    exact ⟨a, b, hab.symm⟩

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine ORIGINAL function-field module Ω[F/K] has dimension2.
This comes from the accepted ACTUAL smooth cubic chart fiber dimension2
and the actual chart fraction-field localization comparison. -/
theorem smoothCubic_originalFunctionFieldKaehler_finrank_two
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange] :
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    Module.finrank (hypersurface p hp).functionField
      (KaehlerDifferential K (hypersurface p hp).functionField) = 2 := by
  let A := ChartRing (equationIdeal p hp) j
  let F := (hypersurface p hp).functionField
  let g : A →+* F := @affineChartGenericEvaluation A
    (inferInstance : CommRing A) (hypersurface p hp)
    (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j) (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  letI aK : Algebra K A := (chartBaseMap (equationIdeal p hp) j).toAlgebra
  letI : SMul K A := aK.toSMul
  letI : Algebra K F :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI : Algebra A F := g.toAlgebra
  letI : IsScalarTower K A F := IsScalarTower.of_algebraMap_eq (R := K) (S := A) (A := F) fun c =>
    (RingHom.congr_fun (cubicChartGenericEvaluation_coefficient_eq p hp j) c).symm
  letI : IsFractionRing A F := @affineChartGenericEvaluation_isFractionRing A
    (inferInstance : CommRing A) (hypersurface p hp)
    (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j) (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  letI : Algebra.FormallyEtale A F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  have hdim := PfaffianDescent.smoothCubic_actualKaehlerChartFiber_finrank_two
    p hp hp0 j g
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K A F).finrank_eq.symm.trans hdim

/-- Dominance sends the actual generic point to the actual generic point;
no point-image or dense-open membership certificate is supplied. -/
theorem dominantSchemeMap_genericPoint_eq
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have hd : closure (Set.range f) = Set.univ := denseRange_iff_closure_range.mp f.denseRange
  have hg : IsGenericPoint (f (genericPoint X)) Set.univ := by
    simpa only [Set.image_univ, hd] using (genericPoint_spec X).image f.continuous
  exact hg.eq (genericPoint_spec Y)

section SameImage
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
variable {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
  (a : Fin m)
local notation "C" => cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a
local notation "f" => cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a

/-- The actual open smooth locus of SAME whole original image over K.
Finite presentation is derived from actual properness and the original
Noetherian coefficient field. -/
def cubicThroughPointBasisEvaluationImageSmoothOpen : TopologicalSpace.Opens C := by
  letI : IsProper f := cubicThroughPointBasisEvaluationImageToBase_isProper p hp hp0 n y hpy j b a
  letI : LocallyOfFinitePresentation f := inferInstance
  exact Scheme.Hom.smoothLocus f

/-- In characteristic zero the SAME actual image generic point lies in
the genuinely constructed image smooth open. -/
theorem cubicThroughPointBasisEvaluationImage_genericPoint_mem_smoothOpen [CharZero K] :
    letI : IsIntegral C := cubicThroughPointBasisEvaluationImage_isIntegral p hp hp0 n y hpy j b a
    genericPoint C ∈ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a := by
  letI : IsIntegral C := cubicThroughPointBasisEvaluationImage_isIntegral p hp hp0 n y hpy j b a
  letI : PerfectField K := PerfectField.ofCharZero
  letI : IsProper f := cubicThroughPointBasisEvaluationImageToBase_isProper p hp hp0 n y hpy j b a
  letI : LocallyOfFinitePresentation f := inferInstance
  exact Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField f

theorem cubicThroughPointBasisEvaluationImage_smoothOpen_dense [CharZero K] :
    Dense (cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a : Set C) := by
  letI : IsIntegral C := cubicThroughPointBasisEvaluationImage_isIntegral p hp hp0 n y hpy j b a
  letI : PerfectField K := PerfectField.ofCharZero
  letI : IsProper f := cubicThroughPointBasisEvaluationImageToBase_isProper p hp hp0 n y hpy j b a
  letI : LocallyOfFinitePresentation f := inferInstance
  exact Scheme.Hom.dense_smoothLocus_of_perfectField f

/-- SAME existing ORIGINAL-F generic evaluation lands in this smooth
open. Its actual image factor and actual image dominance are retained. -/
theorem cubicThroughPointBasisGenericPointToImage_mem_smoothOpen [CharZero K] :
    cubicThroughPointBasisGenericPointToImage p hp hp0 n y hpy j b a
      (genericPoint (Spec (hypersurface p hp).functionField)) ∈
        cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a := by
  letI : IsIntegral C := cubicThroughPointBasisEvaluationImage_isIntegral p hp hp0 n y hpy j b a
  letI : IsDominant (cubicThroughPointBasisGenericPointToImage p hp hp0 n y hpy j b a) :=
    cubicThroughPointBasisGenericPointToImage_isDominant p hp hp0 n y hpy j b a
  rw [dominantSchemeMap_genericPoint_eq]
  exact cubicThroughPointBasisEvaluationImage_genericPoint_mem_smoothOpen p hp hp0 n y hpy j b a

end SameImage
end PfaffianDescent.Coray
end
