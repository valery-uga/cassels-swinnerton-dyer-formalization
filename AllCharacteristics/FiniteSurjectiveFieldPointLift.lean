import AllCharacteristics.ClosedPointAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Lifting a field-valued point through a finite surjective morphism

A point of the target of a finite surjective morphism need not lift over the
same field.  It does lift over a finite residue-field extension.  We package
that extension, the lifted point, and the exact base-change equation.  This
is the first step in recovering an ordered tuple from a rational point of a
finite symmetric quotient.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AllCharacteristics
universe u

/-- A lift of a `K`-valued point through a morphism after a finite field
extension of `K`. -/
structure FiniteFieldPointLift
    {K : Type u} [Field K] {Y Q : Scheme.{u}}
    (q : Y ⟶ Q) (c : Spec (.of K) ⟶ Q) where
  E : Type u
  fieldE : Field E
  algebraE : Algebra K E
  finiteE : Module.Finite K E
  point : Spec (.of E) ⟶ Y
  quotient_eq :
    Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ c = point ≫ q

attribute [instance] FiniteFieldPointLift.fieldE
  FiniteFieldPointLift.algebraE FiniteFieldPointLift.finiteE

/-- Every field-valued point lifts through a finite surjective morphism after
some finite extension of the ground field. -/
noncomputable def finiteFieldPointLiftOfFiniteSurjective
    {K : Type u} [Field K] {Y Q : Scheme.{u}}
    (q : Y ⟶ Q) [IsFinite q] [Surjective q]
    (c : Spec (.of K) ⟶ Q) :
    FiniteFieldPointLift q c := by
  let P : Scheme.{u} := pullback q c
  let p : P ⟶ Spec (.of K) := pullback.snd q c
  haveI : IsFinite p := by
    dsimp only [p, P]
    infer_instance
  haveI : Surjective p := by
    dsimp only [p, P]
    infer_instance
  let y : P := Classical.choose (p.surjective (IsLocalRing.closedPoint K))
  have hy : p y = IsLocalRing.closedPoint K :=
    Classical.choose_spec (p.surjective (IsLocalRing.closedPoint K))
  haveI : IsLocallyArtinian P :=
    IsLocallyArtinian.of_locallyQuasiFinite p
  let x : closedPoints P := ⟨y, isClosed_singleton⟩
  let E : Type u := P.residueField y
  letI : Field E := inferInstanceAs (Field (P.residueField y))
  letI : Algebra K E := pointAlgebra p y
  letI : Module.Finite K E := closedPoint_moduleFinite p x
  let a : Spec (.of E) ⟶ Y :=
    P.fromSpecResidueField y ≫ pullback.fst q c
  refine
    { E := E
      fieldE := inferInstance
      algebraE := inferInstance
      finiteE := inferInstance
      point := a
      quotient_eq := ?_ }
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap K E)) =
      P.fromSpecResidueField y ≫ p := pointAlgebra_spec p y
  calc
    Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ c =
        (P.fromSpecResidueField y ≫ p) ≫ c := by rw [hbase]
    _ = P.fromSpecResidueField y ≫ (p ≫ c) := Category.assoc _ _ _
    _ = P.fromSpecResidueField y ≫ (pullback.fst q c ≫ q) := by
      rw [pullback.condition]
    _ = a ≫ q := Category.assoc _ _ _ |>.symm

/-- The extension occurring in a finite-surjective point lift has positive
degree. -/
theorem FiniteFieldPointLift.finrank_pos
    {K : Type u} [Field K] {Y Q : Scheme.{u}}
    {q : Y ⟶ Q} {c : Spec (.of K) ⟶ Q}
    (d : FiniteFieldPointLift q c) :
    0 < Module.finrank K d.E := by
  letI : Field d.E := d.fieldE
  letI : Algebra K d.E := d.algebraE
  letI : Module.Finite K d.E := d.finiteE
  exact Module.finrank_pos

end AllCharacteristics
