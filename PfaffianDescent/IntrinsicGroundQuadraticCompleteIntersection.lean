import PfaffianDescent.IntrinsicGroundQuadraticBasisIdeal

/-! Literal ground three-quadric complete intersection for an arbitrary
finite closed rank-eight Z with finite FULL quadratic base, over ANY field.
Its basis, finite triple, containment, regularity, and embedded Iso are all
derived from the actual supplied scheme rather than input certificates. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra
variable {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
  [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)]
  (hZ : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8)
  [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i))]

def intrinsicGroundQuadraticBasisLift :
    Z ⟶ scheme (intrinsicFullQuadraticTripleIdeal i (intrinsicGroundQuadraticBasis i hZ)) :=
  IsClosedImmersion.lift
    (quotientProjMap (intrinsicFullQuadraticTripleIdeal i (intrinsicGroundQuadraticBasis i hZ))) i
    (intrinsicFullQuadraticTripleIdeal_ker_le i (intrinsicGroundQuadraticBasis i hZ))

@[reassoc]
theorem intrinsicGroundQuadraticBasisLift_ambient :
    intrinsicGroundQuadraticBasisLift i hZ ≫
      quotientProjMap (intrinsicFullQuadraticTripleIdeal i (intrinsicGroundQuadraticBasis i hZ)) = i :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc]
theorem intrinsicGroundQuadraticBasisLift_toBase :
    intrinsicGroundQuadraticBasisLift i hZ ≫
      toBase (intrinsicFullQuadraticTripleIdeal i (intrinsicGroundQuadraticBasis i hZ)) =
    i ≫ ambientToBase := by
  rw [← quotientProjMap_toBase, ← Category.assoc, intrinsicGroundQuadraticBasisLift_ambient]

theorem intrinsicGroundQuadraticBasisLift_isClosedImmersion :
    IsClosedImmersion (intrinsicGroundQuadraticBasisLift i hZ) := by
  let l := intrinsicGroundQuadraticBasisLift i hZ
  let T := intrinsicFullQuadraticTripleIdeal i (intrinsicGroundQuadraticBasis i hZ)
  letI : IsClosedImmersion (l ≫ quotientProjMap T) := by
    rw [intrinsicGroundQuadraticBasisLift_ambient]
    infer_instance
  exact IsClosedImmersion.of_comp l (quotientProjMap T)

/-- Finiteness of the WHOLE base and positive source length give actual
nonemptiness. The three basis quadrics then form a regular sequence. -/
theorem intrinsicGroundQuadraticBasis_isRegular :
    let b := intrinsicGroundQuadraticBasis i hZ
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin 4) k)
      [(b 0).val, (b 1).val, (b 2).val] := by
  let b := intrinsicGroundQuadraticBasis i hZ
  let T := intrinsicFullQuadraticTripleIdeal i b
  let l := intrinsicGroundQuadraticBasisLift i hZ
  letI : IsFinite (toBase T) := intrinsicGroundQuadraticBasis_triple_isFinite i hZ
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ ambientToBase)
  letI := finiteSchemeCoefficientAlgebra (i ≫ ambientToBase)
  letI := finiteSchemeCoefficient_finite (i ≫ ambientToBase)
  have hΓ8 : finrank k Γ(Z, ⊤) = 8 :=
    (finiteSchemeCoefficient_finrank (i ≫ ambientToBase)).trans hZ
  letI : Nontrivial Γ(Z, ⊤) := Module.nontrivial_of_finrank_pos (by rw [hΓ8]; decide)
  have hT : Nonempty (scheme T) :=
    Nonempty.map l (Nonempty.map Z.isoSpec.inv inferInstance)
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (b 0).val (b 1).val (b 2).val
      (intrinsicFullQuadraticSystem_homogeneous i _ (b 0).property)
      (intrinsicFullQuadraticSystem_homogeneous i _ (b 1).property)
      (intrinsicFullQuadraticSystem_homogeneous i _ (b 2).property))) := by
    change IsFinite (toBase T)
    exact intrinsicGroundQuadraticBasis_triple_isFinite i hZ
  exact AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    (b 0).val (b 1).val (b 2).val
    (intrinsicFullQuadraticSystem_homogeneous i _ (b 0).property)
    (intrinsicFullQuadraticSystem_homogeneous i _ (b 1).property)
    (intrinsicFullQuadraticSystem_homogeneous i _ (b 2).property) hT

theorem intrinsicGroundQuadraticBasisLift_isIso :
    IsIso (intrinsicGroundQuadraticBasisLift i hZ) := by
  let b := intrinsicGroundQuadraticBasis i hZ
  let T := intrinsicFullQuadraticTripleIdeal i b
  let l := intrinsicGroundQuadraticBasisLift i hZ
  letI : IsFinite (toBase T) := intrinsicGroundQuadraticBasis_triple_isFinite i hZ
  letI : IsClosedImmersion l := intrinsicGroundQuadraticBasisLift_isClosedImmersion i hZ
  letI : IsFinite (l ≫ toBase T) := by
    rw [intrinsicGroundQuadraticBasisLift_toBase]
    infer_instance
  have hT8 : AllCharacteristics.finiteSchemeRank (toBase T) = 8 :=
    triple_quadrics_intersection_length_eight_of_regular_sequence
      (b 0).val (b 1).val (b 2).val
      (intrinsicFullQuadraticSystem_homogeneous i _ (b 0).property)
      (intrinsicFullQuadraticSystem_homogeneous i _ (b 1).property)
      (intrinsicFullQuadraticSystem_homogeneous i _ (b 2).property)
      (intrinsicGroundQuadraticBasis_isRegular i hZ)
  have hL8 : AllCharacteristics.finiteSchemeRank (l ≫ toBase T) = 8 := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank,
      intrinsicGroundQuadraticBasisLift_toBase,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hZ
  exact isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq l (toBase T)
    (hL8.trans hT8.symm)

def intrinsicGroundQuadraticCompleteIntersectionIso :
    Z ≅ scheme (intrinsicFullQuadraticTripleIdeal i (intrinsicGroundQuadraticBasis i hZ)) := by
  letI := intrinsicGroundQuadraticBasisLift_isIso i hZ
  exact asIso (intrinsicGroundQuadraticBasisLift i hZ)

@[reassoc]
theorem intrinsicGroundQuadraticCompleteIntersectionIso_ambient :
    (intrinsicGroundQuadraticCompleteIntersectionIso i hZ).hom ≫
      quotientProjMap (intrinsicFullQuadraticTripleIdeal i (intrinsicGroundQuadraticBasis i hZ)) = i :=
  intrinsicGroundQuadraticBasisLift_ambient i hZ

@[reassoc]
theorem intrinsicGroundQuadraticCompleteIntersectionIso_toBase :
    (intrinsicGroundQuadraticCompleteIntersectionIso i hZ).hom ≫
      toBase (intrinsicFullQuadraticTripleIdeal i (intrinsicGroundQuadraticBasis i hZ)) =
    i ≫ ambientToBase :=
  intrinsicGroundQuadraticBasisLift_toBase i hZ

@[reassoc]
theorem homogeneousIdeal_eqToIso_quotientProjMap
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k)) (h : I = J) :
    (eqToIso (congrArg scheme h)).hom ≫ quotientProjMap J = quotientProjMap I := by
  cases h
  simp

/-- In particular, the supplied scheme is the FULL intrinsic base SCHEME,
with its original ambient embedding. -/
def intrinsicGroundFullQuadraticBaseIso :
    Z ≅ scheme (intrinsicFullQuadraticBaseIdeal i) :=
  intrinsicGroundQuadraticCompleteIntersectionIso i hZ ≪≫
    eqToIso (congrArg scheme (intrinsicGroundQuadraticBasis_triple_eq_fullBase i hZ))

@[reassoc]
theorem intrinsicGroundFullQuadraticBaseIso_ambient :
    (intrinsicGroundFullQuadraticBaseIso i hZ).hom ≫
      quotientProjMap (intrinsicFullQuadraticBaseIdeal i) = i := by
  unfold intrinsicGroundFullQuadraticBaseIso
  rw [Iso.trans_hom, Category.assoc,
    homogeneousIdeal_eqToIso_quotientProjMap
      (intrinsicFullQuadraticTripleIdeal i (intrinsicGroundQuadraticBasis i hZ))
      (intrinsicFullQuadraticBaseIdeal i)
      (intrinsicGroundQuadraticBasis_triple_eq_fullBase i hZ),
    intrinsicGroundQuadraticCompleteIntersectionIso_ambient]

@[reassoc]
theorem intrinsicGroundFullQuadraticBaseIso_toBase :
    (intrinsicGroundFullQuadraticBaseIso i hZ).hom ≫
      toBase (intrinsicFullQuadraticBaseIdeal i) = i ≫ ambientToBase := by
  rw [← quotientProjMap_toBase, ← Category.assoc, intrinsicGroundFullQuadraticBaseIso_ambient]

include hZ in
/-- Public arbitrary-field ground basis/triple endpoint. The actual supplied
Z is the full three-quadric intersection with its ORIGINAL ambient map. -/
theorem intrinsicFullQuadraticSystem_exists_ground_basis_triple_iso :
    ∃ b : Basis (Fin 3) k (intrinsicFullQuadraticSystem i),
      intrinsicFullQuadraticTripleIdeal i b = intrinsicFullQuadraticBaseIdeal i ∧
      IsFinite (toBase (intrinsicFullQuadraticTripleIdeal i b)) ∧
      ∃ e : Z ≅ scheme (intrinsicFullQuadraticTripleIdeal i b),
        e.hom ≫ quotientProjMap (intrinsicFullQuadraticTripleIdeal i b) = i ∧
        e.hom ≫ toBase (intrinsicFullQuadraticTripleIdeal i b) = i ≫ ambientToBase := by
  exact ⟨intrinsicGroundQuadraticBasis i hZ,
    intrinsicGroundQuadraticBasis_triple_eq_fullBase i hZ,
    intrinsicGroundQuadraticBasis_triple_isFinite i hZ,
    intrinsicGroundQuadraticCompleteIntersectionIso i hZ,
    intrinsicGroundQuadraticCompleteIntersectionIso_ambient i hZ,
    intrinsicGroundQuadraticCompleteIntersectionIso_toBase i hZ⟩

end PfaffianDescent
