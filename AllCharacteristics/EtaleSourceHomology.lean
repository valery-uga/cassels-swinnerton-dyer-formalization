import AllCharacteristics.EtaleSurjectionLift
import AllCharacteristics.FlatPushoutKernel
import AllCharacteristics.EtaleSourceDifferentials
import Mathlib.RingTheory.Smooth.Flat

/-!
# Smoothness descends along a faithfully flat étale source cover

Lift the étale cover through a formally smooth polynomial extension of the
original algebra. The resulting pushout identifies the kernels by flatness.
The cotangent-homology comparison then transfers vanishing from the smooth
cover, and faithful flatness reflects it back to the original algebra.
-/

open scoped TensorProduct
open Algebra
namespace AllCharacteristics
universe u v w z
variable (R : Type u) (S : Type v) (T : Type w)
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [Module.FaithfullyFlat S T] [Algebra.Etale S T] [Algebra.FormallySmooth R T]
include T

/-- First cotangent homology vanishes for a formally smooth extension of an algebra
with a smooth faithfully flat étale cover. -/
theorem subsingleton_extensionH1_of_faithfullyFlat_etale
    (P : Algebra.Extension.{z} R S) [Algebra.FormallySmooth R P.Ring] :
    Subsingleton P.H1Cotangent := by
  let : Algebra P.Ring T := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  have : IsScalarTower P.Ring S T := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨B, _, _, _, hBT, hB, hPush, hsurj⟩ :=
    exists_etaleLift_of_surjective P.Ring S T P.algebraMap_surjective
  have : IsScalarTower P.Ring B T := hBT
  have : Algebra.Etale P.Ring B := hB
  let : Algebra R B := Algebra.compHom B (algebraMap R P.Ring)
  have : IsScalarTower R P.Ring B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R P.Ring B,
      ← IsScalarTower.algebraMap_apply P.Ring B T,
      IsScalarTower.algebraMap_apply P.Ring S T,
      ← IsScalarTower.algebraMap_apply R P.Ring S,
      ← IsScalarTower.algebraMap_apply R S T]
  let Q : Algebra.Extension R T :=
    { Ring := B
      σ := fun t => (hsurj t).choose
      algebraMap_σ := fun t => (hsurj t).choose_spec }
  let f : P.Hom Q :=
    { toRingHom := algebraMap P.Ring B
      toRingHom_algebraMap := fun r => by
        simpa only [Algebra.algebraMap_self_apply] using
          (IsScalarTower.algebraMap_apply R P.Ring B r).symm
      algebraMap_toRingHom := fun a => by
        rw [← IsScalarTower.algebraMap_apply P.Ring B T,
          IsScalarTower.algebraMap_apply P.Ring S T] }
  have : Algebra.FormallySmooth R Q.Ring := Algebra.FormallySmooth.comp R P.Ring B
  let : Algebra P.Ring Q.Ring := inferInstanceAs (Algebra P.Ring B)
  have : Algebra.IsPushout P.Ring B S T := hPush.symm
  have hker : Function.Bijective ((f.mapKer rfl).liftBaseChange Q.Ring) := by
    change IsBaseChange B (algebraKernelMap P.Ring B S T)
    exact flatPushout_kernel_isBaseChange P.Ring B S T
  have hEtale : f.toRingHom.FormallyEtale :=
    RingHom.formallyEtale_algebraMap.mpr (inferInstanceAs (Algebra.FormallyEtale P.Ring B))
  let e := Algebra.Extension.tensorH1CotangentOfFormallyEtale f rfl hEtale hker
  have : Subsingleton Q.H1Cotangent :=
    (Q.equivH1CotangentOfFormallySmooth.subsingleton_congr).mpr inferInstance
  have : Subsingleton (T ⊗[S] P.H1Cotangent) := e.subsingleton_congr.mpr inferInstance
  exact Module.FaithfullyFlat.lTensor_reflects_triviality S T P.H1Cotangent

/-- The intrinsic first cotangent homology vanishes after descent from the étale cover. -/
theorem subsingleton_h1Cotangent_of_faithfullyFlat_etale :
    Subsingleton (Algebra.H1Cotangent R S) := by
  let P := (Algebra.Generators.self R S).toExtension
  have : Algebra.FormallySmooth R P.Ring :=
    inferInstanceAs (Algebra.FormallySmooth R (MvPolynomial S R))
  have : Subsingleton P.H1Cotangent :=
    subsingleton_extensionH1_of_faithfullyFlat_etale R S T P
  exact P.equivH1CotangentOfFormallySmooth.subsingleton_congr.mp inferInstance

/-- Projectivity of differentials and vanishing of first cotangent homology give
formal smoothness of the original finitely presented algebra. -/
theorem formallySmooth_of_faithfullyFlat_etale [Algebra.FinitePresentation R S] :
    Algebra.FormallySmooth R S :=
  (formallySmooth_iff_h1Cotangent_of_faithfullyFlat_formallyEtale R S T).mpr
    (subsingleton_h1Cotangent_of_faithfullyFlat_etale R S T)

/-- Smoothness descends along a faithfully flat étale source cover. -/
theorem smooth_of_faithfullyFlat_etale [Algebra.FinitePresentation R S] :
    Algebra.Smooth R S :=
  { formallySmooth := formallySmooth_of_faithfullyFlat_etale R S T }

end AllCharacteristics
