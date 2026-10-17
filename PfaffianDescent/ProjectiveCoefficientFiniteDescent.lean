import PfaffianDescent.IntrinsicFiniteCycle
import AllCharacteristics.ProjectiveBaseChange
import AllCharacteristics.HomogeneousProjectiveAmbient

/-! Finiteness descends from the actual coefficient extension of a projective
scheme over ANY extension of fields. This retains nilpotents and does not
recover an ideal from its reduced support. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveCoefficientExtension_isFinite_descend
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsFinite (toBase (HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom (algebraMap k K)) I))] :
    IsFinite (toBase I) := by
  let J := HomogeneousIdeal.map (ambientCoefficientGradedRingHom (algebraMap k K)) I
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let e := projectiveBaseChangeIso (algebraMap k K) I J rfl
  letI : IsArtinianScheme (scheme J) := finiteScheme_isArtinian (toBase J)
  letI : Finite (pullback (toBase I) b : Scheme) :=
    Finite.of_injective e.inv e.inv.injective
  letI : Surjective b := (surjective_iff _).mpr (by
    intro y
    exact ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩)
  letI : Finite (scheme I) := Finite.of_surjective
    (pullback.fst (toBase I) b) ((surjective_iff _).mp inferInstance)
  letI : LocallyQuasiFinite (toBase I) :=
    LocallyQuasiFinite.of_finite_preimage_singleton (toBase I) (fun _ => Set.toFinite _)
  exact IsFinite.of_locallyQuasiFinite (toBase I)

end PfaffianDescent
