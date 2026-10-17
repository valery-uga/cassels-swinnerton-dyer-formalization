import PfaffianDescent.VoisinProjectiveSpaceCech
import AllCharacteristics.AmbientChartPresentation

/-! SOURCE ONLY / UNVERIFIED. The SAME negative-twist quadric map on every
subopen of a standard chart has the literal normalized polynomial coefficient.
This compares actual module sections, retaining all scheme structure. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open HomogeneousLocalization AllCharacteristics.HomogeneousProjective
universe u
-- Actual production aliases obstruct the section-ring and module dictionaries.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem negativeQuadric_cancelIsoInvHom
    {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (e : Z ≅ Y) :
    (f ≫ e.inv) ≫ e.hom = f := by
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "S" => MvPolynomial (Fin 4) K
local instance negativeQuadricChart_pointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

/-- The normalized chart coefficient, restricted to an actual subopen. -/
def p3NegativeQuadricChartCoefficient (j : Fin 4)
    (U : (Proj PS).Opens) (hU : U ≤ p3StandardOpen (K := K) j) (q : PS 2) :
    Γ(Proj PS, U) :=
  (Proj PS).presheaf.map (homOfLE hU).op
    ((Proj.awayToSection PS (X j)).hom (ambientChartEvaluation j q.val))

private lemma p3NegativeQuadricChartCoefficient_value_mul_coordinate
    (j : Fin 4) (U : (Proj PS).Opens)
    (hU : U ≤ p3StandardOpen (K := K) j) (q : PS 2) (x : U) :
    algebraMap S (Fiber PS x.1) ((X j : S) ^ 2) *
      ((p3NegativeQuadricChartCoefficient K j U hU q).val x).val =
        algebraMap S (Fiber PS x.1) q.val := by
  change algebraMap S (Localization.AtPrime (pointIdeal PS x.1)) ((X j : S) ^ 2) *
    (((Proj.awayToSection PS (X j)).hom (ambientChartEvaluation j q.val)).val
      ⟨x.1, hU x.2⟩).val = _
  rw [ambientChartEvaluation_homogeneous j q.val q.property]
  have ha := ProjectiveSpectrum.Proj.awayToSection_apply PS (X j)
    (Away.mk PS (isHomogeneous_X K j) 2 q.val (by simpa using q.property))
    ⟨x.1, hU x.2⟩
  erw [ha, Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  have hj : (X j : S) ∈ (pointIdeal PS x.1).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen PS (X j) x.1).mp (hU x.2)
  exact IsLocalization.mk'_spec'
    (M := (pointIdeal PS x.1).primeCompl)
    (Localization.AtPrime (pointIdeal PS x.1))
    q.val ⟨(X j : S) ^ 2, Submonoid.pow_mem _ hj 2⟩

/-- Multiplication by the actual homogeneous quadric, under the actual
negative chart basis, is multiplication by q / X_j^2 on every subopen. -/
theorem p3NegativeQuadric_mulToUnit_chartCoefficient
    (j : Fin 4) (U : (Proj PS).Opens)
    (hU : U ≤ p3StandardOpen (K := K) j) (q : PS 2)
    (z : Γ(sheafOfModules PS 2, U)) :
    (mulHomogeneousToUnit PS q).val.app (op U) z =
      @Mul.mul (Γ(Proj PS, U)) (inferInstance : Mul (Γ(Proj PS, U)))
        (p3NegativeQuadricChartCoefficient K j U hU q)
        ((negativeTwistTrivializationHom K j 2).val.app (op U) z : Γ(Proj PS, U)) := by
  let e := (((Scheme.Modules.toPresheaf (Proj PS)).mapIso
    (unitIsoZeroTwist PS)).app (op U))
  have hq : mulHomogeneousToUnit PS q ≫ (unitIsoZeroTwist PS).hom =
      mulHomogeneous PS q 0 := by
    change (mulHomogeneous PS q 0 ≫ (unitIsoZeroTwist PS).inv) ≫
      (unitIsoZeroTwist PS).hom = _
    exact negativeQuadric_cancelIsoInvHom (mulHomogeneous PS q 0) (unitIsoZeroTwist PS)
  have hc : negativeTwistTrivializationHom K j 2 ≫ (unitIsoZeroTwist PS).hom =
      mulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) 2) 0 := by
    change (mulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) 2) 0 ≫
      (unitIsoZeroTwist PS).inv) ≫ (unitIsoZeroTwist PS).hom = _
    exact negativeQuadric_cancelIsoInvHom
      (mulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) 2) 0)
      (unitIsoZeroTwist PS)
  have hqz := congrArg
    (fun φ : sheafOfModules PS 2 ⟶ sheafOfModules PS 0 => φ.val.app (op U) z) hq
  have hcz := congrArg
    (fun φ : sheafOfModules PS 2 ⟶ sheafOfModules PS 0 => φ.val.app (op U) z) hc
  change (unitToZeroTwist PS).val.app (op U)
      ((mulHomogeneousToUnit PS q).val.app (op U) z) =
    (mulHomogeneous PS q 0).val.app (op U) z at hqz
  change (unitToZeroTwist PS).val.app (op U)
      ((negativeTwistTrivializationHom K j 2).val.app (op U) z) =
    (mulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) 2) 0).val.app (op U) z
      at hcz
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  change ((unitToZeroTwist PS).val.app (op U))
      ((mulHomogeneousToUnit PS q).val.app (op U) z) = _
  refine hqz.trans ?_
  apply Subtype.ext
  funext x
  have hczx := congrArg (fun w => w.val x) hcz
  change algebraMap S (Fiber PS x.1) q.val * z.val x =
    ((p3NegativeQuadricChartCoefficient K j U hU q).val x *
      ((negativeTwistTrivializationHom K j 2).val.app (op U) z).val x).val
  refine Eq.trans ?_ (HomogeneousLocalization.val_mul
    ((p3NegativeQuadricChartCoefficient K j U hU q).val x)
    (((negativeTwistTrivializationHom K j 2).val.app (op U) z).val x)).symm
  change (((negativeTwistTrivializationHom K j 2).val.app (op U) z).val x).val =
    algebraMap S (Fiber PS x.1) ((X j : S) ^ 2) * z.val x at hczx
  rw [hczx]
  calc
    _ = (algebraMap S (Fiber PS x.1) ((X j : S) ^ 2) *
      ((p3NegativeQuadricChartCoefficient K j U hU q).val x).val) * z.val x := by
      rw [p3NegativeQuadricChartCoefficient_value_mul_coordinate]
    _ = _ := by ring

/-- Negative chart coordinates are surjective on every subopen, because
the coordinate power is invertible there. This is the actual section map,
not a supplied coordinate-surjectivity certificate. -/
theorem p3NegativeQuadric_chartBasis_surjective
    (j : Fin 4) (U : (Proj PS).Opens)
    (hU : U ≤ p3StandardOpen (K := K) j) :
    Function.Surjective ((negativeTwistTrivializationHom K j 2).val.app (op U)) := by
  let e := negativeTwistSectionsIsoStructure K U j hU 2
  have hsurj := (ConcreteCategory.bijective_of_isIso e.hom).surjective
  intro r
  obtain ⟨z, hz⟩ := hsurj r
  refine ⟨z, ?_⟩
  have he : e.hom z =
      (negativeTwistTrivializationHom K j 2).val.app (op U) z :=
    ConcreteCategory.congr_hom
      (p3NegativeTwistSectionsIsoUnit_hom_topIso K U j hU 2) z
  exact he.symm.trans hz

end PfaffianDescent.ProjectiveNegativeTwist
