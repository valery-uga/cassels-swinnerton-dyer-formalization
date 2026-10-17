import PfaffianDescent.ActualKaehlerResidueBasisParameter186
import PfaffianDescent.PlaneCubicJacobianResidueBasis174
import AllCharacteristics.FiniteLocalClosedImmersion

/-! SOURCE ONLY / UNVERIFIED. Actual closed field-valued affine points
supply the literal residue evaluator and its surjectivity internally.
The actual174 Jacobian residue basis supplies the normalization basis.
This does not assert a global Cech/ambient trace comparison. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite KaehlerDifferential
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native affine closed-point construction over the SAME base and the
SAME literal Spec.preimage evaluator. No residue-surjectivity premise. -/
theorem actualAffineClosedPoint_exists_normalizedKaehlerParameter186
    {k R F : Type u} [Field k] [CommRing R] [Field F]
    [Algebra k R] [Algebra k F] [Algebra.IsSeparable k F]
    (b : Module.Basis Unit R (KaehlerDifferential k R))
    (a : Spec (.of F) ⟶ Spec (.of R)) [IsClosedImmersion a]
    (ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k F))) :
    letI : Algebra R F := (Spec.preimage a).hom.toAlgebra
    ∃ t : R, (Spec.preimage a).hom t = 0 ∧
      (1 ⊗ₜ[R] KaehlerDifferential.D k R t : F ⊗[R] KaehlerDifferential k R) =
        1 ⊗ₜ[R] b () := by
  have hbase : CommRingCat.ofHom (algebraMap k R) ≫ Spec.preimage a =
      CommRingCat.ofHom (algebraMap k F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact ha
  let rho : R →ₐ[k] F :=
    { toRingHom := (Spec.preimage a).hom
      commutes' := fun c => congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of F => f.hom c) hbase }
  have hrho : Function.Surjective rho :=
    AllCharacteristics.spec_preimage_surjective_of_closedImmersion a
  exact actualKaehlerResidueBasis_exists_normalizedParameter186 b rho hrho

namespace Coray
open MvPolynomial AllCharacteristics.HomogeneousProjective
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3)
variable (i j : Fin 3) (hij : i ≠ j)
noncomputable local instance nativeNormalizedPointChartAlgebra186 :
    Algebra K (ChartRing (equationIdeal p hp) j) :=
  (chartBaseMap (equationIdeal p hp) j).toAlgebra

/-- Actual174 supplies the SAME native residue basis; the original
closed point supplies its actual residue evaluator and surjectivity.
No basis, local residue normalization or fiber functional is a premise. -/
theorem planeChartJacobian_closedPoint_exists_normalizedParameter186
    (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    {F : Type u} [Field F] [Algebra K F] [Algebra.IsSeparable K F]
    (a : Spec (.of F) ⟶ Spec (.of (planeChartJacobianResidueRing174 p hp i j hij)))
    [IsClosedImmersion a]
    (ha : a ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K (planeChartJacobianResidueRing174 p hp i j hij))) =
      Spec.map (CommRingCat.ofHom (algebraMap K F))) :
    let B := planeChartJacobianResidueRing174 p hp i j hij
    letI : Algebra B F := (Spec.preimage a).hom.toAlgebra
    ∃ t : B, (Spec.preimage a).hom t = 0 ∧
      (1 ⊗ₜ[B] KaehlerDifferential.D K B t : F ⊗[B] KaehlerDifferential K B) =
        1 ⊗ₜ[B] planeChartJacobianResidueBasis174 p hp i j hij k hki hkj () := by
  exact actualAffineClosedPoint_exists_normalizedKaehlerParameter186
    (planeChartJacobianResidueBasis174 p hp i j hij k hki hkj) a ha

end Coray
end PfaffianDescent
