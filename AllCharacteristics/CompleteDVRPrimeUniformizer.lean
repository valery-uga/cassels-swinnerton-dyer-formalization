import AllCharacteristics.CompleteDVRLiftData
import AllCharacteristics.CompleteDVRLiftTowerData

/-! UNVERIFIED: retain the residue-characteristic prime as uniformizer.
This is stronger than the existing unrestricted DVR-lift existence interface. -/
noncomputable section
namespace AllCharacteristics
open IsLocalRing
universe u

structure CompleteDVRPrimeLiftData (p : ℕ) (k : Type u) [Field k] where
  lift : CompleteCharZeroDVRLiftData k
  prime_irreducible :
    letI : CommRing lift.R := lift.commRing
    letI : IsDomain lift.R := lift.domain
    letI : IsDiscreteValuationRing lift.R := lift.dvr
    Irreducible (p : lift.R)

namespace CompleteDVRPrimeLiftData

def ofEquiv {p : ℕ} {k L : Type u} [Field k] [Field L]
    (D : CompleteDVRPrimeLiftData p k) (e : k ≃+* L) :
    CompleteDVRPrimeLiftData p L where
  lift := {
    R := D.lift.R
    commRing := D.lift.commRing
    domain := D.lift.domain
    dvr := D.lift.dvr
    complete := D.lift.complete
    charZero := D.lift.charZero
    residue := e.toRingHom.comp D.lift.residue
    residue_surjective := e.surjective.comp D.lift.residue_surjective
  }
  prime_irreducible := D.prime_irreducible

def ofPerfect (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] [PerfectRing k p] :
    CompleteDVRPrimeLiftData p k :=
  Classical.choice (by
    obtain ⟨R, comm, dom, dvr, complete, cz, b, hb, hmax⟩ :=
      exists_completeDVR_of_perfect_field p k
    letI : CommRing R := comm
    letI : IsDomain R := dom
    letI : IsDiscreteValuationRing R := dvr
    letI : IsAdicComplete (maximalIdeal R) R := complete
    letI : CharZero R := cz
    have hne : (p : R) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    exact ⟨⟨⟨R, comm, dom, dvr, complete, cz, b, hb⟩,
      IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne hmax⟩⟩)

def finiteExtension {p : ℕ} {k L : Type u} [Field k] [Field L]
    [Algebra k L] [Module.Finite k L] (D : CompleteDVRPrimeLiftData p k) :
    CompleteDVRPrimeLiftData p L :=
  Classical.choice (by
    letI : CommRing D.lift.R := D.lift.commRing
    letI : IsDomain D.lift.R := D.lift.domain
    letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
    letI : IsAdicComplete (maximalIdeal D.lift.R) D.lift.R := D.lift.complete
    letI : CharZero D.lift.R := D.lift.charZero
    obtain ⟨A, comm, alg, dom, dvr, free, finite, complete, cz,
      b, hb, hcoef, hinj, hirr⟩ :=
      exists_completeDVR_lift_of_finite_extension_with_uniformizer
        (L := L) D.lift.residue D.lift.residue_surjective (p : D.lift.R) D.prime_irreducible
    letI : CommRing A := comm
    letI : Algebra D.lift.R A := alg
    letI : IsDomain A := dom
    letI : IsDiscreteValuationRing A := dvr
    letI : IsAdicComplete (maximalIdeal A) A := complete
    letI : CharZero A := cz
    have hp : Irreducible (p : A) := by simpa only [map_natCast] using hirr
    exact ⟨⟨⟨A, comm, dom, dvr, complete, cz, b, hb⟩, hp⟩⟩)


def rationalFunction {p : ℕ} {k : Type u} [Field k]
    (D : CompleteDVRPrimeLiftData p k) (σ : Type u) :
    CompleteDVRPrimeLiftData p (FractionRing (MvPolynomial σ k)) := by
  letI : CommRing D.lift.R := D.lift.commRing
  letI : IsDomain D.lift.R := D.lift.domain
  letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
  letI : IsAdicComplete (maximalIdeal D.lift.R) D.lift.R := D.lift.complete
  letI : CharZero D.lift.R := D.lift.charZero
  let J := polynomialResiduePrime σ D.lift.residue
  let B := Localization.AtPrime J
  letI : IsDiscreteValuationRing B :=
    polynomialResidueLocalization_isDiscreteValuationRing σ
      D.lift.residue D.lift.residue_surjective
  letI : CharZero B := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective (MvPolynomial σ D.lift.R) B)
  have hJ : J = Ideal.span {MvPolynomial.C (p : D.lift.R)} :=
    polynomialResiduePrime_eq_span σ D.lift.residue D.lift.residue_surjective
      (p : D.lift.R) D.prime_irreducible.maximalIdeal_eq
  have hmax : maximalIdeal B = Ideal.span {(p : B)} := by
    calc
      maximalIdeal B = J.map (algebraMap (MvPolynomial σ D.lift.R) B) :=
        Localization.AtPrime.map_eq_maximalIdeal.symm
      _ = (Ideal.span {MvPolynomial.C (p : D.lift.R)}).map
          (algebraMap (MvPolynomial σ D.lift.R) B) :=
        congrArg (fun I : Ideal (MvPolynomial σ D.lift.R) =>
          I.map (algebraMap (MvPolynomial σ D.lift.R) B)) hJ
      _ = Ideal.span {(p : B)} := by
        rw [Ideal.map_span, Set.image_singleton]
        simp only [map_natCast]
  have hp0 : p ≠ 0 := by
    intro h
    exact D.prime_irreducible.ne_zero (by simp [h])
  have hpB : Irreducible (p : B) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
      (Nat.cast_ne_zero.mpr hp0) hmax
  let c : B →+* FractionRing (MvPolynomial σ k) :=
    localizationResidueMap (MvPolynomial.map D.lift.residue) J rfl
  have hc : Function.Surjective c :=
    polynomialResidueLocalization_surjective σ D.lift.residue D.lift.residue_surjective
  let A := AdicCompletion (maximalIdeal B) B
  letI : CharZero A := dvrCompletion_charZero (R := B)
  have hpA : Irreducible (p : A) := by
    change Irreducible (p : AdicCompletion (maximalIdeal B) B)
    have h := dvrCompletion_uniformizer_irreducible (R := B) (p : B) hpB
    rw [map_natCast] at h
    exact h
  exact ⟨⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    dvrCompletionResidueMap c hc, dvrCompletionResidueMap_surjective c hc⟩, hpA⟩

end CompleteDVRPrimeLiftData
end AllCharacteristics
