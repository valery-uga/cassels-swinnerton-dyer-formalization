import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFibreFieldDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_seedResidueMap
    {E : Type u} [Field E] {Y : Scheme.{u}} (s : Spec (.of E) ⟶ Y) :
    Spec (.of E) ⟶ Spec (Y.residueField (s (IsLocalRing.closedPoint E))) :=
  Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo s))

theorem cubicClosedPointSerreFiniteZeroResidual_seedResidueMap_comp
    {E : Type u} [Field E] {Y : Scheme.{u}} (s : Spec (.of E) ⟶ Y) :
    cubicClosedPointSerreFiniteZeroResidual_seedResidueMap s ≫
      Y.fromSpecResidueField (s (IsLocalRing.closedPoint E)) = s :=
  Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField E Y s

theorem cubicClosedPointSerreFiniteZeroResidual_seedResidueMap_flat_surjective
    {E : Type u} [Field E] {Y : Scheme.{u}} (s : Spec (.of E) ⟶ Y) :
    Flat (cubicClosedPointSerreFiniteZeroResidual_seedResidueMap s) ∧
      Surjective (cubicClosedPointSerreFiniteZeroResidual_seedResidueMap s) := by
  let q := Scheme.descResidueField (Scheme.stalkClosedPointTo s)
  constructor
  · apply (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
    letI := q.hom.toAlgebra
    change Module.Flat (Y.residueField (s (IsLocalRing.closedPoint E))) E
    infer_instance
  · apply (surjective_iff _).mpr
    intro y
    exact ⟨IsLocalRing.closedPoint E, Subsingleton.elim _ _⟩

theorem cubicClosedPointSerreFiniteZeroResidual_seedResiduePoint_closed
    {K E : Type u} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K)) [IsSeparated f]
    (s : Spec (.of E) ⟶ Y)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    IsClosedImmersion (Y.fromSpecResidueField (s (IsLocalRing.closedPoint E))) := by
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K E))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsFinite (s ≫ f) := by rw [hs]; infer_instance
  letI : IsFinite s := IsFinite.of_comp s f
  apply isClosed_singleton_iff_isClosedImmersion.mp
  have hr : Set.range s = {s (IsLocalRing.closedPoint E)} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact congrArg s (Subsingleton.elim x (IsLocalRing.closedPoint E))
    · intro hy
      exact ⟨IsLocalRing.closedPoint E, hy.symm⟩
  rw [← hr]
  exact s.isClosedMap.isClosed_range

end PfaffianDescent
