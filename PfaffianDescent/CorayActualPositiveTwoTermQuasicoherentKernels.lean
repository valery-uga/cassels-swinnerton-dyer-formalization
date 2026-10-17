import PfaffianDescent.SchemeModuleNativeQuasicoherentKernel
import PfaffianDescent.CorayActualPositiveFiniteCoproductPresentation
import PfaffianDescent.CorayActualPositiveNativeWholeGeneratorMatrix
import PfaffianDescent.CorayActualAmbientIdealPositiveNativeChart
import PfaffianDescent.CorayActualFinitePiTildeUnitMatrix
import PfaffianDescent.VoisinPositiveTwistTriviality

/-! QC of the SAME actual positive free terms, ideal twist and two kernels.
Every local QC fact is derived from an actual native chart frame.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
open BundleSectionZeroLocus IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PolyA" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem nativeTilde_isQuasicoherent
    (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    ((tilde.functor R).obj M).IsQuasicoherent :=
  AlgebraicGeometry.instIsQuasicoherentOpensCarrierCarrierCommRingCatSpecOfCarrierObjModuleCatModulesFunctor
    (R := R) M

/-- The original finite weighted positive free term is QC. This is derived
from its actual whole native chart frame and actual finite-Pi tilde, with no
abstract supplied trivialization or QC input. -/
theorem actualPositiveFiniteCoproduct_isQuasicoherent
    {ι : Type u} [Fintype ι] (d : ι → ℕ) (m : ℕ) :
    (∐ fun i => positiveSheafOfModules PS (m - d i)).IsQuasicoherent := by
  let U := p3StandardOpenLifted (K := K)
  let R : P3CoordinateIndex → CommRingCat.{u} := fun i =>
    CommRingCat.of (HomogeneousLocalization.Away PS (X i.down))
  let e : ∀ i, (U i : Scheme) ≅ Spec (R i) := fun i =>
    Proj.basicOpenIsoSpec PS (X i.down) (isHomogeneous_X K i.down) (by decide : 0 < 1)
  let M := (∐ fun i => positiveSheafOfModules PS (m - d i))
  letI : ∀ i, ((Scheme.Modules.pullback ((e i).inv ≫ (U i).ι)).obj M).IsQuasicoherent :=
    fun i => by
      let c := actualPositiveNativeWholeGeneratorFrame (K := K) i.down d m ≪≫
        actualFinitePiTildeUnitIso (HomogeneousLocalization.Away PS (X i.down)) ι
      have hTilde := nativeTilde_isQuasicoherent
        (CommRingCat.of (HomogeneousLocalization.Away PS (X i.down)))
        (ModuleCat.of (HomogeneousLocalization.Away PS (X i.down))
          (ι → HomogeneousLocalization.Away PS (X i.down)))
      exact (SheafOfModules.isQuasicoherent (Spec (R i)).ringCatSheaf).prop_of_iso
        c.symm hTilde
  exact schemeNative_isQuasicoherent_of_nativeAffineCover
    U (p3StandardOpenLifted_coversTop K) R e M

/-- The SAME whole ideal tensored with O(m) is QC, including its nilpotents.
Native quotient-chart ideal tilde supplies QC; no desired ideal-image or
quasicoherence premise is assumed. -/
theorem actualAmbientHomogeneousIdealPositive_isQuasicoherent
    (I : HomogeneousIdeal PS) (m : ℕ) :
    (schemeModuleTensor (closedImmersionModule (quotientProjMap I))
      (positiveSheafOfModules PS m)).IsQuasicoherent := by
  let U := p3StandardOpenLifted (K := K)
  let R : P3CoordinateIndex → CommRingCat.{u} := fun i =>
    CommRingCat.of (HomogeneousLocalization.Away PS (X i.down))
  let e : ∀ i, (U i : Scheme) ≅ Spec (R i) := fun i =>
    Proj.basicOpenIsoSpec PS (X i.down) (isHomogeneous_X K i.down) (by decide : 0 < 1)
  let M := schemeModuleTensor (closedImmersionModule (quotientProjMap I))
    (positiveSheafOfModules PS m)
  letI : ∀ i, ((Scheme.Modules.pullback ((e i).inv ≫ (U i).ι)).obj M).IsQuasicoherent :=
    fun i => by
      let c := actualAmbientHomogeneousIdealPositiveNativeChartIso (K := K) I i.down m
      exact (SheafOfModules.isQuasicoherent (Spec (R i)).ringCatSheaf).prop_of_iso
        c.symm (nativeTilde_isQuasicoherent
          (CommRingCat.of (HomogeneousLocalization.Away PS (X i.down)))
          (ModuleCat.of (HomogeneousLocalization.Away PS (X i.down))
            (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I i.down))))
  exact schemeNative_isQuasicoherent_of_nativeAffineCover
    U (p3StandardOpenLifted_coversTop K) R e M

/-- Both ACTUAL kernels required for the two-term OWN ideal route are QC.
The first map is the original ideal factor a and the second is the native
kernel lift of the SAME weighted relation map. No QC or exactness premise
is added. In the actual two-kernel producer011, a/hz are constructed and
its literal b≫kernel.ι a=R and short exact sequences are retained. -/
theorem actualPositiveFiniteRelationLift_kernels_isQuasicoherent
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (r : κ → ι → PolyA) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (m : ℕ) (he : ∀ a, e a ≤ m)
    (a : (∐ fun i => positiveSheafOfModules PS (m - d i)) ⟶
      schemeModuleTensor (closedImmersionModule (quotientProjMap I))
        (positiveSheafOfModules PS m))
    (hz : actualPositiveFiniteRelationMap d r e hr m he ≫ a = 0) :
    (kernel a).IsQuasicoherent ∧
      (kernel (kernel.lift a (actualPositiveFiniteRelationMap d r e hr m he) hz)).IsQuasicoherent := by
  letI : (∐ fun i => positiveSheafOfModules PS (m - d i)).IsQuasicoherent :=
    actualPositiveFiniteCoproduct_isQuasicoherent d m
  letI : (schemeModuleTensor (closedImmersionModule (quotientProjMap I))
      (positiveSheafOfModules PS m)).IsQuasicoherent :=
    actualAmbientHomogeneousIdealPositive_isQuasicoherent I m
  letI : (kernel a).IsQuasicoherent := schemeNative_kernel_isQuasicoherent a
  letI : (∐ fun a => positiveSheafOfModules PS (m - e a)).IsQuasicoherent :=
    actualPositiveFiniteCoproduct_isQuasicoherent e m
  exact ⟨inferInstance, schemeNative_kernel_isQuasicoherent
    (kernel.lift a (actualPositiveFiniteRelationMap d r e hr m he) hz)⟩

end PfaffianDescent.Coray
