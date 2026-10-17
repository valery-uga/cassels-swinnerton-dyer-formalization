import PfaffianDescent.ActualOriginalAllSingleSupportDirectCotangentLine
import PfaffianDescent.ActualOriginalPositiveTwoNativeJetEmbedding

/-! SOURCE ONLY / UNVERIFIED. The inverse EXISTENCE direction for every
actual supplied finite rank-eight singleton-support subscheme, in the exact
original Omega(2) fiber. The reconstructed embedding is the given immersion
after the internally constructed dual presentation. Uniqueness modulo L-units
and the final equivalence of geometric subscheme classes remain separate. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginal_allSingleSupport_rankEight_cotangentLine
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hSupport : Set.range i = {P.1})
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 8) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    ∃ e : Γ(Z, ⊤) ≃ₐ[K] DualNumber L,
      ∃ ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[L] L,
        Function.Surjective ell ∧
        actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell =
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Z.isoSpec.inv ≫ i := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  let L := (hypersurface p hp).residueField P.1
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv (K := K) (L := L) p hp
    ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
  obtain ⟨e, ell, hell, hphi, hred, hemb⟩ :=
    actualOriginal_allSingleSupport_rankEight_directCotangentLine p hp P hP i hSupport hZ
  refine ⟨e, ell, hell, ?_⟩
  change Spec.map (CommRingCat.ofHom (actualKaehlerLineDualAlgebraMap
    (ell.comp E.symm.toLinearMap)).toRingHom) ≫
      chartι (equationIdeal p hp) C.index =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Z.isoSpec.inv ≫ i
  exact hemb

end PfaffianDescent
