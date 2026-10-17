import PfaffianDescent.ActualCubicOriginalPointDifferentialClassAction
import PfaffianDescent.ActualResidueDifferentialLeibnizBalance

/- SOURCE ONLY / UNVERIFIED. Actual GENUINE original global Omega fiber
class obeys zero-section Leibniz. Its true original point/native chart
factorization is retained; no abstract conormal surrogate is introduced. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualOriginalPointDifferentialClass_mul_of_residue_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp) (j : Fin 4)
    (rho : ChartRing (equationIdeal p hp) j →+* L)
    (hbase : rho.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K L)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) j = q)
    (a r : ChartRing (equationIdeal p hp) j) (hr : rho r = 0) :
    actualCubicOriginalPointDifferentialClass p hp q j rho hfac (a * r) =
      rho a • actualCubicOriginalPointDifferentialClass p hp q j rho hfac r := by
  let R := ChartRing (equationIdeal p hp) j
  letI : Algebra K R := (chartBaseMap (equationIdeal p hp) j).toAlgebra
  letI : Algebra R L := rho.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun hbase c).symm)
  apply (actualCubicOriginalPointDifferentialFiberEquiv p hp q j rho hfac).injective
  rw [LinearEquiv.map_smul,
    actualCubicOriginalPointDifferentialFiberEquiv_pointClass,
    actualCubicOriginalPointDifferentialFiberEquiv_pointClass]
  exact actualResidueDifferential_zero_section_leibniz a r hr

lemma actualOriginalPointDifferentialClass_square_ratio_of_residue_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp) (j : Fin 4)
    (rho : ChartRing (equationIdeal p hp) j →+* L)
    (hbase : rho.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K L)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) j = q)
    (a r : ChartRing (equationIdeal p hp) j) (hr : rho r = 0) :
    actualCubicOriginalPointDifferentialClass p hp q j rho hfac (a ^ 2 * r) =
      rho a ^ 2 • actualCubicOriginalPointDifferentialClass p hp q j rho hfac r := by
  simpa only [map_pow] using actualOriginalPointDifferentialClass_mul_of_residue_zero
    p hp q j rho hbase hfac (a ^ 2) r hr

end PfaffianDescent
