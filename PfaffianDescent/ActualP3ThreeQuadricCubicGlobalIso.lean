import PfaffianDescent.ActualP3IdealHomogeneousPiece
import PfaffianDescent.ThreeQuadricCubicIdealLinearEquiv
import PfaffianDescent.OriginalThreeQuadricRankEightSourceIso
import PfaffianDescent.SchemeModuleGlobalSections
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.FinCases

/-! SOURCE ONLY / UNVERIFIED. The literal actual H0(O(1)^3) ≃ H0(I_Z(3))
isomorphism for a SAME original length-eight scheme contained in a finite
triple of quadrics. Polynomial regularity, length equality, source Iso,
saturation, actual H0 dictionary and bijectivity are derived internally.
This gives the displayed global isomorphism by a graded algebraic proof;
it does NOT assert the still-missing displayed sheaf Koszul exactness. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u v w
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

-- Keep the finite-biproduct proof independent of any concrete scheme/site.
private theorem p3ConstantTripleProjection_bijective
    {D : Type v} [Category.{w} D] [HasZeroMorphisms D]
    (M U : D) [HasBiproduct (fun _ : Fin 3 => M)] :
    Function.Bijective (fun s : U ⟶ ⨁ (fun _ : Fin 3 => M) =>
      (s ≫ biproduct.π (fun _ : Fin 3 => M) 0,
        s ≫ biproduct.π (fun _ : Fin 3 => M) 1,
        s ≫ biproduct.π (fun _ : Fin 3 => M) 2)) := by
  let P : Fin 3 → D := fun _ => M
  constructor
  · intro s t h
    apply biproduct.hom_ext
    intro j
    fin_cases j
    · exact congrArg Prod.fst h
    · exact congrArg (fun z : _ × _ × _ => z.2.1) h
    · exact congrArg (fun z : _ × _ × _ => z.2.2) h
  · intro s
    refine ⟨biproduct.lift ![s.1, s.2.1, s.2.2], ?_⟩
    apply Prod.ext
    · exact biproduct.lift_π (f := P) ![s.1, s.2.1, s.2.2] 0
    · apply Prod.ext
      · exact biproduct.lift_π (f := P) ![s.1, s.2.1, s.2.2] 1
      · exact biproduct.lift_π (f := P) ![s.1, s.2.1, s.2.2] 2

-- The scalar dictionary is the existing global-sections dictionary, now
-- checked over an abstract scheme instead of the actual Proj presentation.
private def p3SchemeConstantTripleGlobalEquiv
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) (M : X.Modules)
    [HasBiproduct (fun _ : Fin 3 => M)] :
    SchemeModuleGlobalSectionsOver a (⨁ (fun _ : Fin 3 => M)) ≃ₗ[K]
      (SchemeModuleGlobalSectionsOver a M ×
        SchemeModuleGlobalSectionsOver a M ×
        SchemeModuleGlobalSectionsOver a M) := by
  let P : Fin 3 → X.Modules := fun _ => M
  let f : SchemeModuleGlobalSectionsOver a (⨁ P) →ₗ[K]
      (SchemeModuleGlobalSectionsOver a M ×
        SchemeModuleGlobalSectionsOver a M ×
        SchemeModuleGlobalSectionsOver a M) :=
    (schemeModuleGlobalSectionsMap a (biproduct.π P 0)).prod
      ((schemeModuleGlobalSectionsMap a (biproduct.π P 1)).prod
        (schemeModuleGlobalSectionsMap a (biproduct.π P 2)))
  exact LinearEquiv.ofBijective f
    (p3ConstantTripleProjection_bijective M (schemeModuleUnit X))

/-- Three copies of actual O(1), not a renamed polynomial model. -/
abbrev p3ActualPositiveOneTriple : Fin 3 → (Proj PS).Modules :=
  fun _ => positiveSheafOfModules PS 1

/-- Actual global sections commute with this concrete finite biproduct. -/
def p3ActualPositiveOneTripleGlobalEquiv :
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (⨁ (p3ActualPositiveOneTriple (K := K))) ≃ₗ[K]
      (SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
        (positiveSheafOfModules PS 1) ×
      SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
        (positiveSheafOfModules PS 1) ×
      SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
        (positiveSheafOfModules PS 1)) :=
  p3SchemeConstantTripleGlobalEquiv
    (ambientToBase (R := K) (σ := Fin 4)) (positiveSheafOfModules PS 1)

/-- Actual H0(O(1)^3) as three homogeneous linear forms. -/
def p3ActualPositiveOneTripleHomogeneousEquiv :
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (⨁ (p3ActualPositiveOneTriple (K := K))) ≃ₗ[K] (PS 1 × PS 1 × PS 1) :=
  p3ActualPositiveOneTripleGlobalEquiv.trans
    ((p3HomogeneousGlobalSectionsLinearEquiv K 1 (by decide)).symm.prodCongr
      ((p3HomogeneousGlobalSectionsLinearEquiv K 1 (by decide)).symm.prodCongr
        (p3HomogeneousGlobalSectionsLinearEquiv K 1 (by decide)).symm))

/-- Finite regularity removes the irrelevant socle in the actual quotient. -/
theorem p3ThreeQuadricFinite_no_irrelevant_socle
    (f g h : PS 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))]
    (hT : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))) :
    ∀ a : CoordinateRing (tripleCompleteIntersectionHomogeneousIdeal
        f.val g.val h.val f.property g.property h.property),
      (∀ j : Fin 4, coordinate (tripleCompleteIntersectionHomogeneousIdeal
        f.val g.val h.val f.property g.property h.property) j * a = 0) → a = 0 := by
  have hseq := AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    f.val g.val h.val f.property g.property h.property hT
  obtain ⟨hf0, hgreg, hhreg⟩ :=
    (triple_quadrics_isRegular_iff_sequential_regular
      f.val g.val h.val f.property g.property h.property).mp hseq
  exact triple_quadrics_no_irrelevant_annihilator f.val g.val h.val
    f.property g.property h.property hf0
    (right_ne_zero_of_regular_mod_span_singleton
      (homogeneous_not_isUnit_of_pos_degree f.property (by decide)) hgreg)
    (isRelPrime_of_regular_mod_span_singleton hf0 hgreg) hhreg

/-- Intermediate original-source-Iso transport. No sheaf dictionary or
regularity certificate is assumed; both are internally constructed. -/
def p3ThreeQuadricCubicGlobalEquivOfSourceIso
    (f g h : PS 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))]
    (hT : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property)))
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property)) [IsIso l] :
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (⨁ (p3ActualPositiveOneTriple (K := K))) ≃ₗ[K]
      SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
        (closedImmersionIdealTwist
          (l ≫ quotientProjMap (tripleCompleteIntersectionHomogeneousIdeal
            f.val g.val h.val f.property g.property h.property))
          (positiveSheafOfModules PS 3)) :=
  p3ActualPositiveOneTripleHomogeneousEquiv.trans
    ((threeQuadricCubicIdealLinearEquivOfFinite f g h hT).trans
      (p3ActualIdealHomogeneousPieceLinearEquiv
        (tripleCompleteIntersectionHomogeneousIdeal f.val g.val h.val
          f.property g.property h.property)
        (p3ThreeQuadricFinite_no_irrelevant_socle f g h hT) l 3 (by decide)).symm)

-- Prove the exact eliminator's forward law with its proof argument
-- genuinely abstract. No proof rewriting/generalization is needed.
private theorem p3ThreeQuadricSequentialEliminator_apply
    (f g h : PS 2)
    (H : f.val ≠ 0 ∧
      (∀ a : MvPolynomial (Fin 4) K,
        g.val * a ∈ Ideal.span ({f.val} : Set (MvPolynomial (Fin 4) K)) →
          a ∈ Ideal.span ({f.val} : Set (MvPolynomial (Fin 4) K))) ∧
      (∀ a : MvPolynomial (Fin 4) K,
        h.val * a ∈ Ideal.span ({f.val, g.val} : Set (MvPolynomial (Fin 4) K)) →
          a ∈ Ideal.span ({f.val, g.val} : Set (MvPolynomial (Fin 4) K))))
    (x : PS 1 × PS 1 × PS 1) :
    (show (PS 1 × PS 1 × PS 1) ≃ₗ[K]
        homogeneousIdealPiece
          (tripleCompleteIntersectionHomogeneousIdeal f.val g.val h.val
            f.property g.property h.property) 3 from
      And.rec (fun hf0 right =>
        And.rec (fun hgreg hhreg =>
          threeQuadricCubicIdealLinearEquivOfRegular f g h hf0
            (isRelPrime_of_regular_mod_span_singleton hf0 hgreg) hhreg) right) H) x =
      threeQuadricCubicIdealLinearMap f g h x := by
  rcases H with ⟨hf0, hgreg, hhreg⟩
  rfl

-- The finite provider eliminates a conjunction of regularity proofs
-- before returning the actual ofBijective equivalence. Expose that
-- proof-only elimination once; its forward map is the SAME cubic map.
private theorem p3ThreeQuadricFiniteEquiv_apply
    (f g h : PS 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))]
    (hT : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property)))
    (x : PS 1 × PS 1 × PS 1) :
    threeQuadricCubicIdealLinearEquivOfFinite f g h hT x =
      threeQuadricCubicIdealLinearMap f g h x := by
  dsimp (config := { zeta := true, zetaHave := true }) only
    [threeQuadricCubicIdealLinearEquivOfFinite]
  exact p3ThreeQuadricSequentialEliminator_apply f g h
    ((triple_quadrics_isRegular_iff_sequential_regular f.val g.val h.val
      f.property g.property h.property).mp
      (AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
        f.val g.val h.val f.property g.property h.property hT)) x

/-- This is the displayed SUM map: the actual ideal section, included into
actual O(3), is the homogeneous cubic f*H1+g*H2+h*H3. -/
theorem p3ThreeQuadricCubicGlobalEquivOfSourceIso_polynomial
    (f g h : PS 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))]
    (hT : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property)))
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property)) [IsIso l]
    (s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (⨁ (p3ActualPositiveOneTriple (K := K)))) :
    ((p3ClosedImmersionIdealHomogeneousKernelEquiv
      (l ≫ quotientProjMap (tripleCompleteIntersectionHomogeneousIdeal
        f.val g.val h.val f.property g.property h.property)) 3 (by decide))
      (p3ThreeQuadricCubicGlobalEquivOfSourceIso f g h hT l s)).val =
        (threeQuadricCubicIdealLinearMap f g h
          (p3ActualPositiveOneTripleHomogeneousEquiv s)).val := by
  let T := tripleCompleteIntersectionHomogeneousIdeal f.val g.val h.val
    f.property g.property h.property
  let e := p3ActualIdealHomogeneousPieceLinearEquiv T
    (p3ThreeQuadricFinite_no_irrelevant_socle f g h hT) l 3 (by decide)
  have he : e (p3ThreeQuadricCubicGlobalEquivOfSourceIso f g h hT l s) =
      threeQuadricCubicIdealLinearMap f g h
        (p3ActualPositiveOneTripleHomogeneousEquiv s) := by
    change e (e.symm ((threeQuadricCubicIdealLinearEquivOfFinite f g h hT)
      (p3ActualPositiveOneTripleHomogeneousEquiv s))) = _
    rw [e.apply_symm_apply]
    exact p3ThreeQuadricFiniteEquiv_apply f g h hT
      (p3ActualPositiveOneTripleHomogeneousEquiv s)
  exact congrArg Subtype.val he

/-- Literal H0(O(1)^3) ≃ H0(I_originalZ(3)) for the SAME actual rank-eight
scheme contained in a finite triple, over ANY field. No exactness,
cohomology, source-Iso, saturation or desired equivalence is an input. -/
def p3OriginalThreeQuadricCubicGlobalEquiv
    (f g h : PS 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal
        f.val g.val h.val f.property g.property h.property)) = 8) :
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (⨁ (p3ActualPositiveOneTriple (K := K))) ≃ₗ[K]
      SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
        (closedImmersionIdealTwist
          (l ≫ quotientProjMap (tripleCompleteIntersectionHomogeneousIdeal
            f.val g.val h.val f.property g.property h.property))
          (positiveSheafOfModules PS 3)) := by
  letI := p3ThreeQuadricOriginalLift_isIso f g h l hZ
  exact p3ThreeQuadricCubicGlobalEquivOfSourceIso f g h
    (p3ThreeQuadricOriginalLift_nonempty f g h l hZ) l

/-- Exact sum identity for the public actual original-Z isomorphism. -/
theorem p3OriginalThreeQuadricCubicGlobalEquiv_polynomial
    (f g h : PS 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal
        f.val g.val h.val f.property g.property h.property)) = 8)
    (s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (⨁ (p3ActualPositiveOneTriple (K := K)))) :
    ((p3ClosedImmersionIdealHomogeneousKernelEquiv
      (l ≫ quotientProjMap (tripleCompleteIntersectionHomogeneousIdeal
        f.val g.val h.val f.property g.property h.property)) 3 (by decide))
      (p3OriginalThreeQuadricCubicGlobalEquiv f g h l hZ s)).val =
        (threeQuadricCubicIdealLinearMap f g h
          (p3ActualPositiveOneTripleHomogeneousEquiv s)).val := by
  letI := p3ThreeQuadricOriginalLift_isIso f g h l hZ
  exact p3ThreeQuadricCubicGlobalEquivOfSourceIso_polynomial f g h
    (p3ThreeQuadricOriginalLift_nonempty f g h l hZ) l s

end PfaffianDescent
