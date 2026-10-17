import PfaffianDescent.CorayNormalizationIntrinsicCechOne
import PfaffianDescent.CorayProjectiveIntersectionChartDimension

/-! Primitive original p/q caller for the intrinsic normalization Čech
quotient. Finite type, finite normalization, local Noetherianity, cover,
Ext infrastructure and local acyclicity are internal. No cohomology
comparison with the original scheme, dimension formula or genus is claimed.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual normalization of the literal integral p/q intersection has
its genuine intrinsic H¹ computed by its actual preimage affine-cover
cocycle quotient. This foundation needs neither smoothness nor a curve
dimension bound, and therefore applies to the original smooth cubic caller.
It does not identify this quotient with the ORIGINAL-X cocycle quotient. -/
def projectiveIntersection_genericNormalization_intrinsicAffineCechQuotientEquivCohomologyOne
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n)
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    let V : X.affineOpens → N.Opens := fun i => (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ i.1
    let M : N.Modules := SheafOfModules.unit N.ringCatSheaf
    DegreeOneCocycle ((sectionRepresenterCechChain N.ringCatSheaf V).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom V (genericNormalization_preimageAffineOpenFamily_coversTop X) M).ker ≃+
      schemeModuleCohomology N M 1 := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  exact genericNormalizationUnit_preimageAffineCechQuotientEquivCohomologyOne X (toBase I)

end PfaffianDescent.Coray
