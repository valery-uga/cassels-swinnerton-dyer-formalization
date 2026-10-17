import PfaffianDescent.SchemeModuleClosedPointFixedComplementFieldComparison
import PfaffianDescent.CorayNormalizationClosedPointIdealStalk

/-! Negative point-factor stalks have the ORIGINAL maximal-ideal image
in the ORIGINAL function field. Actual inclusion germs and the actual
closed-immersion kernel prove the range; no image or DVR certificate.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- At EVERY point x, the fixed-complement ideal stalk field map is the
SAME actual inclusion on stalks followed by the original local-ring-to-
function-field algebraMap. No comparison law is supplied. -/
theorem schemeModuleClosedPointIdealFixedComplementStalkToFunctionField_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (C : X.Opens) [Nonempty C] (hPC : P.1 ∉ C) (x : X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    letI := schemeModuleStalkModule M x
    ∀ a : M.presheaf.stalk x,
      schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C
          (schemeModuleClosedPointIdealOverCanonicalIso P C hPC) x a =
        algebraMap (X.presheaf.stalk x) X.functionField
          (closedImmersionModuleStalkToRingLinearMap i x a) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  letI := schemeModuleStalkModule M x
  let j := closedImmersionModuleToUnit i
  let κ := algebraMap (X.presheaf.stalk x) X.functionField
  intro a
  obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq a
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hj : closedImmersionModuleStalkToRingLinearMap i x (M.presheaf.germ U x hxU m) =
      X.presheaf.germ U x hxU (j.val.app (op U) m) :=
    schemeModuleStalkToRingLinearMap_germ j x U hxU m
  exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C
    (schemeModuleClosedPointIdealOverCanonicalIso P C hPC) x U hxU m).trans
      ((schemeModuleClosedPointIdealFixedComplementOpenToFunctionField_apply pi P C hPC U m).trans
        ((Scheme.algebraMap_germ_eq_germToFunctionField X hxU (j.val.app (op U) m)).symm.trans
          (congrArg κ hj.symm)))

/-- Genuine negative-factor stalk injectivity at EVERY point follows from
Mono of the SAME original ideal inclusion and integral stalk-field
injectivity. No rank-one or injectivity certificate is required. -/
theorem schemeModuleClosedPointIdealFixedComplementStalkToFunctionField_injective
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (C : X.Opens) [Nonempty C] (hPC : P.1 ∉ C) (x : X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    letI := schemeModuleStalkModule M x
    Function.Injective (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C
      (schemeModuleClosedPointIdealOverCanonicalIso P C hPC) x) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  letI := schemeModuleStalkModule M x
  let j := closedImmersionModuleToUnit i
  letI : Mono j := by
    change Mono (idealModuleToUnit i.ker)
    infer_instance
  have hj : Function.Injective (closedImmersionModuleStalkToRingLinearMap i x) :=
    schemeModuleStalkToRingLinearMap_injective_of_mono j x
  intro a b hab
  apply hj
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  exact (schemeModuleClosedPointIdealFixedComplementStalkToFunctionField_apply pi P C hPC x a).symm.trans
    (hab.trans (schemeModuleClosedPointIdealFixedComplementStalkToFunctionField_apply pi P C hPC x b))

/-- FULL centered negative-factor image is the image of the actual
maximal ideal under the SAME local-ring-to-field algebraMap. Its actual
closed-immersion stalk kernel and original inclusion derive the range. -/
theorem schemeModuleClosedPointIdealFixedComplementStalkToFunctionField_range_eq_maximalIdeal
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (C : X.Opens) [Nonempty C] (hPC : P.1 ∉ C) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    letI := schemeModuleStalkModule M P.1
    Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C
        (schemeModuleClosedPointIdealOverCanonicalIso P C hPC) P.1) =
      Set.range (fun r : IsLocalRing.maximalIdeal (X.presheaf.stalk P.1) =>
        algebraMap (X.presheaf.stalk P.1) X.functionField r.1) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  letI := schemeModuleStalkModule M P.1
  let R := X.presheaf.stalk P.1
  let κ := algebraMap R X.functionField
  let E := Coray.closedPointIdeal_stalkLinearEquivMaximalIdeal X P
  let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C
    (schemeModuleClosedPointIdealOverCanonicalIso P C hPC) P.1
  have hval (a : M.presheaf.stalk P.1) : ψ a = κ (E a : R) :=
    (schemeModuleClosedPointIdealFixedComplementStalkToFunctionField_apply pi P C hPC P.1 a).trans
      (congrArg κ (Coray.closedPointIdeal_stalkLinearEquivMaximalIdeal_apply X P a).symm)
  apply Set.Subset.antisymm
  · rintro f ⟨a, ha⟩
    exact ⟨E a, (hval a).symm.trans ha⟩
  · rintro f ⟨r, hr⟩
    refine ⟨E.symm r, ?_⟩
    exact (hval (E.symm r)).trans
      ((congrArg (fun t : IsLocalRing.maximalIdeal R => κ t.1) (E.apply_symm_apply r)).trans hr)

end PfaffianDescent

namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Primitive SAME literal p/q normalization: the actual negative factor
stalk injects into its original function field with the actual maximal-
ideal image. Nongenericity/nonempty canonical complement are derived
internally. No smoothness/DVR/HasExt/image certificate is needed for this
stronger purely ideal-theoretic statement over the original field. -/
theorem projectiveIntersection_genericNormalization_closedPoint_ideal_stalkFieldImage
    (p q : MvPolynomial (Fin 4) K) {a b : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from closedImmersionModule i)
      letI := schemeModuleStalkModule M P.1
      let C := schemeClosedPointComplementOpen P
      letI : Nonempty C := ⟨⟨genericPoint N, schemeClosedPoint_generic_mem_complement P
        (projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P)⟩⟩
      let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C
        (schemeModuleClosedPointIdealOverCanonicalIso P C (schemeClosedPoint_not_mem_complement P)) P.1
      Function.Injective ψ ∧ Set.range ψ =
        Set.range (fun r : IsLocalRing.maximalIdeal (N.presheaf.stalk P.1) =>
          algebraMap (N.presheaf.stalk P.1) N.functionField r.1) := by
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show N.Modules from closedImmersionModule i)
  letI := schemeModuleStalkModule M P.1
  let C := schemeClosedPointComplementOpen P
  letI : Nonempty C := ⟨⟨genericPoint N, schemeClosedPoint_generic_mem_complement P
    (projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P)⟩⟩
  exact ⟨schemeModuleClosedPointIdealFixedComplementStalkToFunctionField_injective
    pi P C (schemeClosedPoint_not_mem_complement P) P.1,
    schemeModuleClosedPointIdealFixedComplementStalkToFunctionField_range_eq_maximalIdeal
      pi P C (schemeClosedPoint_not_mem_complement P)⟩

end PfaffianDescent.Coray
