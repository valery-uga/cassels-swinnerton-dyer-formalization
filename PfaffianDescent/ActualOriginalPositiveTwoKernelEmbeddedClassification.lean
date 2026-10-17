import PfaffianDescent.ActualKaehlerLineKernelClassification
import PfaffianDescent.ActualOriginalPositiveTwoNativeJetEmbedding
import PfaffianDescent.SurjectiveAffineKernelEmbeddedIso
import PfaffianDescent.OneDimensionalQuotientTargetIso

/-! SOURCE ONLY / UNVERIFIED. The entire actual original-chart kernel
classifies the original Omega(2) quotient modulo target-line isomorphism.
Actual embedded-scheme isomorphisms commute with the SAME surface map. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K : Type u} [Field K] [PerfectField K]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  (P : closedPoints (hypersurface p hp))
  (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def actualOriginalPositiveTwoNativeDualMap
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    ChartRing (equationIdeal p hp) C.index →ₐ[K]
      DualNumber ((hypersurface p hp).residueField P.1) := by
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
  exact actualKaehlerLineDualAlgebraMap (ell.comp E.symm.toLinearMap)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginalPositiveTwoNativeDualMap_factorization
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell =
      Spec.map (CommRingCat.ofHom (actualOriginalPositiveTwoNativeDualMap p hp P hP ell).toRingHom) ≫
        chartι (equationIdeal p hp) C.index := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginalPositiveTwoNativeDualMap_surjective
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    Function.Surjective (actualOriginalPositiveTwoNativeDualMap p hp P hP ell) := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
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
  exact actualKaehlerLineDualAlgebraMap_surjective C.residue_surjective _
    (hell.comp E.symm.surjective)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginalPositiveTwoNativeDualMap_sameKernel_iff_smul
    (ell₁ ell₂ : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1)
    (hell₁ : Function.Surjective ell₁) (hell₂ : Function.Surjective ell₂) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
    RingHom.ker (actualOriginalPositiveTwoNativeDualMap p hp P hP ell₁).toRingHom =
        RingHom.ker (actualOriginalPositiveTwoNativeDualMap p hp P hP ell₂).toRingHom ↔
      ∃ c : (hypersurface p hp).residueField P.1, c ≠ 0 ∧ ell₂ = c • ell₁ := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
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
  let q₁ := ell₁.comp E.symm.toLinearMap
  let q₂ := ell₂.comp E.symm.toLinearMap
  have h := actualKaehlerLineDualAlgebraMap_sameKernel_iff_smul
    C.residue_surjective q₁ q₂ (hell₁.comp E.symm.surjective) (hell₂.comp E.symm.surjective)
  change RingHom.ker (actualKaehlerLineDualAlgebraMap q₁).toRingHom =
      RingHom.ker (actualKaehlerLineDualAlgebraMap q₂).toRingHom ↔ _
  rw [h]
  constructor
  · rintro ⟨c, hc, hq⟩
    refine ⟨c, hc, ?_⟩
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hq (E x)
    simpa only [q₁, q₂, LinearMap.comp_apply, LinearEquiv.coe_coe,
      E.symm_apply_apply, LinearMap.smul_apply] using hx
  · rintro ⟨c, hc, hell⟩
    refine ⟨c, hc, ?_⟩
    apply LinearMap.ext
    intro x
    change ell₂ (E.symm x) = (c • q₁) x
    rw [hell]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginalPositiveTwoNativeJetEmbedding_overIso_iff_targetIso
    (ell₁ ell₂ : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1)
    (hell₁ : Function.Surjective ell₁) (hell₂ : Function.Surjective ell₂) :
    (∃ e : Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))) ≅
        Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))),
      e.hom ≫ actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell₂ =
        actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell₁) ↔
      OneDimensionalQuotientTargetIso ell₁ ell₂ := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  let L := (hypersurface p hp).residueField P.1
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  have h := surjectiveAffineAlgMaps_sameKernel_iff_originalEmbeddedIso
    (actualOriginalPositiveTwoNativeDualMap p hp P hP ell₁)
    (actualOriginalPositiveTwoNativeDualMap p hp P hP ell₂)
    (actualOriginalPositiveTwoNativeDualMap_surjective p hp P hP ell₁ hell₁)
    (actualOriginalPositiveTwoNativeDualMap_surjective p hp P hP ell₂ hell₂)
    (chartι (equationIdeal p hp) C.index)
  rw [← actualOriginalPositiveTwoNativeDualMap_factorization,
    ← actualOriginalPositiveTwoNativeDualMap_factorization] at h
  exact h.symm.trans
    ((actualOriginalPositiveTwoNativeDualMap_sameKernel_iff_smul
      p hp P hP ell₁ ell₂ hell₁ hell₂).trans
        (oneDimensionalQuotientTargetIso_iff_smul ell₁ ell₂).symm)

end
end PfaffianDescent
