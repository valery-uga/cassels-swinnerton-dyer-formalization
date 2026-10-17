import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSeedFibreProperties
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFiniteFibreMarkedSeed

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_seed_threeMarkedOpen
    {K E : Type u} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    {Z Y : Scheme.{u}} [IsLocallyNoetherian Z]
    (f : Y ⟶ Spec (.of K)) [IsSeparated f]
    (g : Z ⟶ Y) [IsProper g] [LocallyOfFinitePresentation g]
    (j : Fin 3 → (Y ⟶ Z)) (hj : ∀ n, j n ≫ g = 𝟙 Y)
    (s : Spec (.of E) ⟶ Y)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    [IsFinite (pullback.snd g s)] [Etale (pullback.snd g s)] :
    s (IsLocalRing.closedPoint E) ∈
      cubicClosedPointSerreFiniteZeroResidual_threeMarkedSectionOpen g j := by
  letI : IsClosedImmersion (Y.fromSpecResidueField (s (IsLocalRing.closedPoint E))) :=
    cubicClosedPointSerreFiniteZeroResidual_seedResiduePoint_closed f s hs
  letI : Finite (g.fiber (s (IsLocalRing.closedPoint E))) :=
    cubicClosedPointSerreFiniteZeroResidual_seed_residue_fibre_finite g s
  apply cubicClosedPointSerreFiniteZeroResidual_finiteFibre_threeMarkedSeed g j hj _
    (isClosed_singleton_iff_isClosedImmersion.mpr inferInstance)
  exact cubicClosedPointSerreFiniteZeroResidual_seed_residue_fibre_fields g s

end PfaffianDescent
