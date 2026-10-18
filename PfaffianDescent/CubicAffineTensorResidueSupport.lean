import PfaffianDescent.ActualAffineTensorChartBaseChange
import PfaffianDescent.CubicActualFiniteSupportLocalSurface
import AllCharacteristics.HypersurfaceReduction
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Artinian.Ring

/-!
Natural residue-support intake
for the intrinsic Artin semilocal Hilbert--Burch theorem.  Finite colength,
the actual residual chart, and all residual local surface properties are
derived from the original smooth cubic chart and its original family.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

theorem exists_cubicAffineTensorResidueSupport_localSurface001
    {S K A : Type u} [CommRing S] [Field K] [CommRing A]
    [Algebra S K] [Algebra S A]
    (hSK : Function.Surjective (algebraMap S K))
    (q : MvPolynomial (Fin 4) S) (hq : q.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase q hq)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (he : q.map (algebraMap S K) = p)
    (a : Spec (.of A) ⟶ hypersurface q hq) [IsOpenImmersion a]
    (ha : a ≫ hypersurfaceToBase q hq =
      Spec.map (CommRingCat.ofHom (algebraMap S A)))
    (J : Ideal A) [Module.Finite S (A ⧸ J)] :
    let π := (affineTensorFiberReduction174 (R := S) (S := K) (A := A)).toRingHom
    ∃ hArt : IsArtinianRing ((K ⊗[S] A) ⧸ J.map π),
      letI := hArt
      ∀ m ∈ actualArtinianQuotientSupport001 (J.map π),
        IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
          ringKrullDim (Localization.AtPrime m.asIdeal) = 2 := by
  let A0 := K ⊗[S] A
  let π := affineTensorFiberReduction174 (R := S) (S := K) (A := A)
  let J0 := J.map π.toRingHom
  let Q0 := A0 ⧸ J0
  let red : (A ⧸ J) →ₐ[S] Q0 := Ideal.quotientMapₐ J0 π Ideal.le_comap_map
  have hred : Function.Surjective red :=
    Ideal.quotientMap_surjective (H := Ideal.le_comap_map)
      (affineTensorFiberReduction174_surjective hSK)
  letI : Module.Finite S Q0 := Module.Finite.of_surjective red.toLinearMap hred
  letI : Module.Finite K Q0 := Module.Finite.of_restrictScalars_finite S K Q0
  letI : IsArtinianRing Q0 := IsArtinianRing.of_finite K Q0
  let d := hypersurfaceReductionMap (algebraMap S K) q hq p hp he
  have Hbase := isPullback_hypersurfaceReductionMap (algebraMap S K) q hq p hp he
  letI : Smooth (hypersurfaceToBase p hp) := MorphismProperty.of_isPullback Hbase
    (inferInstance : Smooth (hypersurfaceToBase q hq))
  obtain ⟨a0, hopen, _, ha0⟩ := exists_actualAffineTensorChartBaseChange001
    (hypersurfaceToBase q hq) (hypersurfaceToBase p hp) d Hbase a ha
  letI : IsOpenImmersion a0 := hopen
  refine ⟨inferInstance, fun m hm ↦ ?_⟩
  exact cubic_actualFiniteSupport_localSurface001 p hp hp0 a0 ha0 J0 m hm

end PfaffianDescent
end
