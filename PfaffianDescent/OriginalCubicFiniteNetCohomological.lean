import PfaffianDescent.OriginalThreeQuadricContainedCubicSection

/-! SOURCE ONLY / UNVERIFIED. Direct literal lemma: SAME closed Z in the
original cubic, length8, contained scheme-theoretically in the finite net W.
The factor into W, closed immersion, finiteness of Z and cubic ideal-section
are internally constructed. No auxiliary first-quadric embedding is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "base" => ambientToBase (R := K) (σ := Fin 4)
-- Original cubic, net and actual closed immersion are declaration-local.

/-- Equality of structure morphisms transports rank together with finiteness. -/
private theorem finiteRank_eq_of_map_eq {X : Scheme.{u}}
    (a b : X ⟶ Spec (.of K)) [IsFinite a] [IsFinite b] (hab : a = b) :
    AllCharacteristics.finiteSchemeRank a = AllCharacteristics.finiteSchemeRank b := by
  subst b
  rfl

/-- Scheme-theoretic Z⊂W gives its actual unique factor, not a source-Iso
certificate or a newly chosen Z. -/
def p3OriginalCubicFiniteNetLift
    (f g h : PS 2) (F : PS 3)
    {Z : Scheme.{u}}
    (i : Z ⟶ hypersurface F.val F.property) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)).ker ≤
      (i ≫ hypersurfaceToAmbient F.val F.property).ker) : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property) :=
  IsClosedImmersion.lift (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property))
    (i ≫ hypersurfaceToAmbient F.val F.property) hker

@[reassoc]
theorem p3OriginalCubicFiniteNetLift_ambient
    (f g h : PS 2) (F : PS 3)
    {Z : Scheme.{u}}
    (i : Z ⟶ hypersurface F.val F.property) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)).ker ≤
      (i ≫ hypersurfaceToAmbient F.val F.property).ker) :
    p3OriginalCubicFiniteNetLift f g h F i hker ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property) =
      i ≫ hypersurfaceToAmbient F.val F.property :=
  IsClosedImmersion.lift_fac (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property))
    (i ≫ hypersurfaceToAmbient F.val F.property) hker

instance p3OriginalCubicFiniteNetLift_isClosedImmersion
    (f g h : PS 2) (F : PS 3)
    {Z : Scheme.{u}}
    (i : Z ⟶ hypersurface F.val F.property) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)).ker ≤
      (i ≫ hypersurfaceToAmbient F.val F.property).ker) :
    IsClosedImmersion (p3OriginalCubicFiniteNetLift f g h F i hker) := by
  letI : IsClosedImmersion
      (p3OriginalCubicFiniteNetLift f g h F i hker ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)) := by
    rw [p3OriginalCubicFiniteNetLift_ambient]
    letI : IsClosedImmersion (hypersurfaceToAmbient F.val F.property) :=
      hypersurfaceToAmbient_isClosedImmersion F.val F.property
    exact IsClosedImmersion.comp i (hypersurfaceToAmbient F.val F.property)
  exact IsClosedImmersion.of_comp
    (p3OriginalCubicFiniteNetLift f g h F i hker) (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property))

theorem p3OriginalCubicFiniteNetLift_base
    (f g h : PS 2) (F : PS 3)
    {Z : Scheme.{u}}
    (i : Z ⟶ hypersurface F.val F.property) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)).ker ≤
      (i ≫ hypersurfaceToAmbient F.val F.property).ker) :
    p3OriginalCubicFiniteNetLift f g h F i hker ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property) =
      i ≫ hypersurfaceToBase F.val F.property := by
  calc
    _ = (p3OriginalCubicFiniteNetLift f g h F i hker ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)) ≫ base := by
      rw [Category.assoc, quotientProjMap_toBase]
    _ = (i ≫ hypersurfaceToAmbient F.val F.property) ≫ base := by
      rw [p3OriginalCubicFiniteNetLift_ambient]
    _ = _ := by
      exact (Category.assoc i (hypersurfaceToAmbient F.val F.property) base).trans
        (congrArg (fun a => i ≫ a)
          (quotientProjMap_toBase (R := K) (σ := Fin 4)
            (equationIdeal F.val F.property)))

/-- This actual finiteness follows from containment in the finite W.
It is not an extra public certificate required to interpret length8. -/
theorem p3OriginalCubicFiniteNet_source_isFinite
    (f g h : PS 2) (F : PS 3)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (i : Z ⟶ hypersurface F.val F.property) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)).ker ≤
      (i ≫ hypersurfaceToAmbient F.val F.property).ker) :
    IsFinite (i ≫ hypersurfaceToBase F.val F.property) := by
  rw [← p3OriginalCubicFiniteNetLift_base f g h F i hker]
  infer_instance

/-- Literal TeX lem:net-of-quadrics, following its displayed sheaf and
cohomological proof. Smoothness of F is not needed for this conclusion.
HasExt, EnoughInjectives, regularity, exactness, vanishings, source factor
and the cubic ideal-global section are all internally supplied. -/
theorem p3OriginalCubicFiniteNet_decomposition_by_cohomology
    (f g h : PS 2) (F : PS 3)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (i : Z ⟶ hypersurface F.val F.property) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)).ker ≤
      (i ≫ hypersurfaceToAmbient F.val F.property).ker)
    (hZ : letI : IsFinite (i ≫ hypersurfaceToBase F.val F.property) :=
        p3OriginalCubicFiniteNet_source_isFinite f g h F i hker
      AllCharacteristics.finiteSchemeRank
        (i ≫ hypersurfaceToBase F.val F.property) = 8) :
    ∃ H : PS 1 × PS 1 × PS 1,
      F.val = f.val * H.1.val + g.val * H.2.1.val + h.val * H.2.2.val := by
  letI : IsFinite (i ≫ hypersurfaceToBase F.val F.property) :=
    p3OriginalCubicFiniteNet_source_isFinite f g h F i hker
  let l := p3OriginalCubicFiniteNetLift f g h F i hker
  have hZ' : AllCharacteristics.finiteSchemeRank (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)) = 8 := by
    exact (finiteRank_eq_of_map_eq _ _
      (p3OriginalCubicFiniteNetLift_base f g h F i hker)).trans hZ
  have hF : (hypersurfaceToAmbient F.val F.property).ker ≤
      (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)).ker := by
    rw [p3OriginalCubicFiniteNetLift_ambient f g h F i hker]
    exact hypersurface_ker_le_of_factor F.val F.property i
      (i ≫ hypersurfaceToAmbient F.val F.property) rfl
  exact p3OriginalThreeQuadricContainedCubic_decomposition_by_cohomology
    f g h l hZ' F hF

end PfaffianDescent
