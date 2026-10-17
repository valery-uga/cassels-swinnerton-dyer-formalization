import PfaffianDescent.ActualOriginalAllSingleSupportNativeDualMap
import PfaffianDescent.ResidueCompatibleActualDualMorphismLine
import PfaffianDescent.ActualCubicPositiveTwoNativePointFiber

/-! SOURCE ONLY / UNVERIFIED. A primitive given-immersion caller with only
accepted prerequisites. The actual original Omega(2) quotient is constructed
from the supplied Z, not supplied as input. Its genuine Kaehler dual map
reconstructs the SAME original immersion through a derived dual presentation.
Identification with actualOriginalPositiveTwoNativeJetEmbedding (171),
uniqueness modulo target isomorphism, and the final quotient-class equivalence
remain later validation steps. No global Phi or H0-kernel claim is made here. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem directCotangentLine_reconstructionCertificate
    {K R L V : Type u} [Field K] [CommRing R] [Field L]
    [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]
    [AddCommGroup V] [Module L V]
    (E : V ≃ₗ[L] TensorProduct R L (KaehlerDifferential K R))
    (phi : R →ₐ[K] DualNumber L)
    (hphi : Function.Surjective phi)
    (hred : ∀ r, (phi r).fst = algebraMap R L r) :
    ∃ ell : V →ₗ[L] L, Function.Surjective ell ∧
      actualKaehlerLineDualAlgebraMap (ell.comp E.symm.toLinearMap) = phi := by
  let line := residueCompatibleActualDualFiberLine phi hred
  let ell := line.comp E.toLinearMap
  have hell : Function.Surjective ell :=
    (residueCompatibleActualDualFiberLine_surjective phi hred hphi).comp E.surjective
  have hline : ell.comp E.symm.toLinearMap = line := by
    apply LinearMap.ext
    intro x
    exact congrArg line (E.apply_symm_apply x)
  refine ⟨ell, hell, ?_⟩
  rw [hline]
  exact residueCompatibleActualDualFiberLine_reconstruct phi hred

private theorem directCotangentLine_transport
    {A : Sort u} {Q : A → Prop} {a b : A} (h : a = b) (hb : Q b) : Q a :=
  h.symm ▸ hb

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem directCotangentLine_nativeReconstructionCertificate
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
    ∃ e : Γ(Z, ⊤) ≃ₐ[K] DualNumber L,
      ∃ phi : R →ₐ[K] DualNumber L,
      ∃ ell : (moduleSpecΓFunctor (R := .of L)).obj
          ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
            (actualCubicPositiveTwoDifferentials p hp)) →ₗ[L] L,
        Function.Surjective ell ∧
        actualKaehlerLineDualAlgebraMap (ell.comp E.symm.toLinearMap) = phi ∧
        Function.Surjective phi ∧
        (∀ r : R, (phi r).fst = C.residue r) ∧
        Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
            chartι (equationIdeal p hp) C.index =
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
  obtain ⟨e, phi, hphi, hred, hemb⟩ :=
    actualOriginal_allSingleSupport_rankEight_nativeDualMap p hp P hP i hSupport hZ
  obtain ⟨ell, hell, hrec⟩ :=
    directCotangentLine_reconstructionCertificate (K := K) (R := R) (L := L)
      E phi hphi hred
  exact ⟨e, phi, ell, hell, hrec, hphi, hred, hemb⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginal_allSingleSupport_rankEight_directCotangentLine
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
    ∃ e : Γ(Z, ⊤) ≃ₐ[K] DualNumber L,
      ∃ ell : (moduleSpecΓFunctor (R := .of L)).obj
          ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
            (actualCubicPositiveTwoDifferentials p hp)) →ₗ[L] L,
        Function.Surjective ell ∧
        Function.Surjective (actualKaehlerLineDualAlgebraMap
          (ell.comp E.symm.toLinearMap)) ∧
        (∀ r : R, (actualKaehlerLineDualAlgebraMap
          (ell.comp E.symm.toLinearMap) r).fst = C.residue r) ∧
        Spec.map (CommRingCat.ofHom (actualKaehlerLineDualAlgebraMap
          (ell.comp E.symm.toLinearMap)).toRingHom) ≫
            chartι (equationIdeal p hp) C.index =
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
  obtain ⟨e, phi, ell, hell, hrec, hphi, hred, hemb⟩ :=
    directCotangentLine_nativeReconstructionCertificate p hp P hP i hSupport hZ
  refine ⟨e, ell, hell, ?_⟩
  exact directCotangentLine_transport
    (Q := fun psi : R →ₐ[K] DualNumber L =>
      Function.Surjective psi ∧
      (∀ r : R, (psi r).fst = C.residue r) ∧
      Spec.map (CommRingCat.ofHom psi.toRingHom) ≫
          chartι (equationIdeal p hp) C.index =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Z.isoSpec.inv ≫ i)
    hrec ⟨hphi, hred, hemb⟩

end PfaffianDescent
