import PfaffianDescent.CorayTildeActualStalkSupport
import PfaffianDescent.CorayGenericNormalizationQuotientNativeStalkDefect
import PfaffianDescent.CorayNonregularLocalNormalizationDegreeContribution
import PfaffianDescent.CorayOriginalRegularClosedPointNormalizationLift

/-! Outside the OWN actual normalization quotient support, the OWN original
curve stalk is regular. This composes genuine native defect comparison with
nonregular => nontrivial defect. The native comparison import is currently
UNVERIFIED, not an accepted geometric fact. No stalk identification is input.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Natural selected-curve hypotheses imply regularity at every actual point
outside its OWN actual quotient support. No native-defect comparison or
regularity certificate is supplied to this caller. -/
theorem projectiveIntersection_original_stalk_regular_of_outside_actualNormalizationQuotientSupport
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq))
    (houtside : x ∉ schemeModuleStalkSupport
      (genericNormalizationQuotientSheaf (scheme (projectiveIntersectionIdeal p q hp hq)))) :
    IsRegularLocalRing ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk x) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let R := X.presheaf.stalk x
  let F := X.functionField
  let Q := genericNormalizationQuotientSheaf X
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (toBase I)
  have hdim : ringKrullDim R ≤ 1 :=
    projectiveIntersection_original_stalk_ringKrullDim_le_one p q hp hp0 n hq hnot x
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  letI : Ring.DimensionLEOne R :=
    ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
  by_contra hsing
  letI : Nontrivial (localNormalizationDefect R F) :=
    localNormalizationDefect_nontrivial_of_not_isRegularLocalRing R F hsing
  have hx : x ∈ ⨆ U : X.affineOpens, (U : X.Opens) := by
    rw [iSup_affineOpens_eq_top]
    trivial
  obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp hx
  let E := genericNormalizationQuotientSheaf_affineNativeStalkDefectEquiv
    X U.1 U.2 ⟨x, hxU⟩
  have hnontrivial : Nontrivial (Q.presheaf.stalk x) :=
    E.toEquiv.nontrivial_congr.mpr inferInstance
  exact houtside hnontrivial

end PfaffianDescent.Coray
