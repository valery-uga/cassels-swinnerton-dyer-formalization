import PfaffianDescent.CorayNativeNormalizationFiniteAndGroundBound
import PfaffianDescent.CorayGlobalOriginalSectionsFinite
import PfaffianDescent.SchemeModuleOriginalBaseWeightedStalk

/-! SOURCE ONLY / UNVERIFIED. Actual affine germs, own native normalization,
and full original residue degree. No Q-stalk comparison is used or assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Module
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The affine algebra from the original appLE and the independently
original stalk algebra form a genuine scalar tower. Compatibility follows
from the original base-constant germ theorem, not a transported action. -/
theorem schemeOriginalBase_affine_nativeStalk_isScalarTower
    (X : Scheme.{u}) (pi : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (x : U) :
    let beta : K →+* Γ(X, U) :=
      (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    letI : Algebra K Γ(X, U) := beta.toAlgebra
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf x
    letI := schemeStalkBaseAlgebra pi x
    IsScalarTower K Γ(X, U) (X.presheaf.stalk x) := by
  let beta : K →+* Γ(X, U) :=
    (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  letI : Algebra K Γ(X, U) := beta.toAlgebra
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x
  letI := schemeStalkBaseAlgebra pi x
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change schemeStalkBaseRingHom pi x c = X.presheaf.germ U x x.2 (beta c)
  have hbeta : beta = schemeOpenBaseRingHom pi U :=
    (schemeOpenBaseRingHom_eq_appLE pi U).symm
  rw [hbeta]
  exact (schemeStalkBaseRingHom_germ pi x U x.2 c).symm

/-- Finite-type original affine normalization localizes to finite OWN native
normalization inside SAME X.functionField. Neither a finite native
normalization certificate nor a change of fraction field is supplied. -/
theorem genericNormalization_nativeStalk_integralClosure_finite
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (U : X.Opens) (hU : IsAffineOpen U) (x : U) :
    Module.Finite (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) X.functionField) := by
  letI : Nonempty U := ⟨x⟩
  let A := Γ(X, U)
  let R := X.presheaf.stalk x
  let F := X.functionField
  let beta : K →+* A :=
    (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  letI : Algebra K A := beta.toAlgebra
  have hbeta : beta.FiniteType := RingHom.FiniteType.comp
    (pi.finiteType_appLE (isAffineOpen_top _) hU (by simp))
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  letI : Algebra.FiniteType K A := hbeta
  letI : IsFractionRing A F := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : Module.Finite A (integralClosure A (FractionRing A)) :=
    finiteNormalization_of_finiteType_charZero K A
  letI : Module.Finite A (integralClosure A F) :=
    Module.Finite.equiv (FractionRing.algEquiv (A := A) F).mapIntegralClosure.toLinearEquiv
  let J := (hU.primeIdealOf x).asIdeal
  letI : J.IsPrime := (hU.primeIdealOf x).isPrime
  letI : Algebra A R := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  letI : IsLocalization.AtPrime R J := hU.isLocalization_stalk x
  letI : IsScalarTower A R F := functionField_isScalarTower X U x
  exact integralClosure_nativeLocalization_finite A R F J.primeCompl
    J.primeCompl_le_nonZeroDivisors

/-- Nonregularity at an actual original closed point forces at least its
FULL original residue degree in a finite actual affine defect. Dimension<=1
is explicit here; the projective caller derives it from original charts. -/
theorem genericNormalization_originalClosedPoint_nonregular_degree_le_affineDefect
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (U : X.Opens) (hU : IsAffineOpen U) (P : closedPoints X) (hPU : P.1 ∈ U)
    (hdim : ringKrullDim (X.presheaf.stalk P.1) ≤ 1)
    (hsing : ¬ IsRegularLocalRing (X.presheaf.stalk P.1)) :
    letI : Nonempty U := ⟨⟨P.1, hPU⟩⟩
    let beta : K →+* Γ(X, U) :=
      (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    let D := (ModuleCat.restrictScalars beta).obj
      (ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField))
    Module.Finite K D → pi.residueDegree P.1 ≤ finrank K D := by
  dsimp only
  let x : U := ⟨P.1, hPU⟩
  letI : Nonempty U := ⟨x⟩
  let A := Γ(X, U)
  let R := X.presheaf.stalk P.1
  let F := X.functionField
  let beta : K →+* A :=
    (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let D := (ModuleCat.restrictScalars beta).obj (ModuleCat.of A (localNormalizationDefect A F))
  intro hfinite
  letI : Algebra K A := beta.toAlgebra
  letI : Algebra A R := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  letI := schemeStalkBaseAlgebra pi P.1
  letI : IsScalarTower K A R := schemeOriginalBase_affine_nativeStalk_isScalarTower X pi U x
  letI : IsFractionRing A F := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsScalarTower A R F := functionField_isScalarTower X U x
  let J := (hU.primeIdealOf x).asIdeal
  letI : J.IsPrime := (hU.primeIdealOf x).isPrime
  letI : IsLocalization.AtPrime R J := hU.isLocalization_stalk x
  letI : Module K (localNormalizationDefect A F) := Module.compHom _ beta
  letI : Module K (localNormalizationDefect R F) :=
    Module.compHom _ (schemeStalkBaseRingHom pi P.1)
  have hfinite' : Module.Finite K (localNormalizationDefect A F) := hfinite
  have hcomparison := normalizationDefect_nativeLocalization_originalGround_finrank_le
    K A R F J.primeCompl J.primeCompl_le_nonZeroDivisors hfinite'
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pi
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  letI : Ring.DimensionLEOne R :=
    ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
  letI : Module.Finite R (integralClosure R F) :=
    genericNormalization_nativeStalk_integralClosure_finite X pi U hU x
  letI : Module.Finite K (IsLocalRing.ResidueField R) := schemeStalkCanonicalResidue_finite pi P
  have hlocal := localNormalizationDefect_nonregular_restrictedGround_degree_lower_bound K R F hsing
  have hresidue := schemeStalkCanonicalResidue_finrank pi P
  exact hresidue.symm.le.trans (hlocal.trans hcomparison.2)

end PfaffianDescent.Coray
