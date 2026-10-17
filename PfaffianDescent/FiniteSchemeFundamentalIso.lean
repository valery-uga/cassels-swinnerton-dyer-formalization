import PfaffianDescent.IntrinsicFiniteCycle
import PfaffianDescent.RationalCycleFamilies
import AllCharacteristics.ProperCyclePushforward

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
universe u

/- The intrinsic finite-scheme cycle is carried to the intrinsic cycle under
an isomorphism.  This is the bridge used when two iterated finite fibers are
identified by pullback associativity. -/
theorem finiteSchemeFundamentalCycle_iso
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (e : X ≅ Y) (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K))
    [IsFinite fX] [IsFinite fY] :
    AllCharacteristics.pushforwardCycle e.hom
        (finiteSchemeFundamentalCycle fX) =
      finiteSchemeFundamentalCycle fY := by
  letI := finiteScheme_isArtinian fX
  letI := finiteScheme_isArtinian fY
  rw [pushforwardCycle_iso]
  exact fundamentalZeroCycle_iso e

/- An endpoint isomorphism transports the actual family fiber cycle to the
intrinsic cycle on the identified finite scheme.  This packages the
scheme-theoretic multiplicity transport needed by configuration-family
constructions. -/
lemma fiberCycle_eq_pushforward_of_iso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsSeparated p]
    (F : RationalCycleFamily p) (b : Bool)
    {Y : Scheme.{u}} (e : F.fiber b ≅ Y)
    (g : Y ⟶ X) (gbase : Y ⟶ Spec (.of K))
    [IsFinite g] [IsFinite gbase]
    (hmap : e.hom ≫ g = F.fiberToScheme b)
    (_hbase : e.hom ≫ gbase =
      pullback.snd F.toLine (projectiveLineEndpoint K b)) :
    F.fiberCycle b =
      AllCharacteristics.pushforwardCycle g
        (finiteSchemeFundamentalCycle gbase) := by
  have hfund : AllCharacteristics.pushforwardCycle e.hom
      (finiteSchemeFundamentalCycle
        (pullback.snd F.toLine (projectiveLineEndpoint K b))) =
      finiteSchemeFundamentalCycle gbase := by
    apply finiteSchemeFundamentalCycle_iso e
  change AllCharacteristics.pushforwardCycle (F.fiberToScheme b)
      (finiteSchemeFundamentalCycle
        (pullback.snd F.toLine (projectiveLineEndpoint K b))) = _
  have hcomp := AllCharacteristics.pushforwardCycle_comp e.hom g
      (finiteSchemeFundamentalCycle
        (pullback.snd F.toLine (projectiveLineEndpoint K b)))
  have hcomp' : AllCharacteristics.pushforwardCycle (F.fiberToScheme b)
      (finiteSchemeFundamentalCycle
        (pullback.snd F.toLine (projectiveLineEndpoint K b))) =
      AllCharacteristics.pushforwardCycle g
        (AllCharacteristics.pushforwardCycle e.hom
          (finiteSchemeFundamentalCycle
            (pullback.snd F.toLine (projectiveLineEndpoint K b)))) := by
    simpa only [hmap] using hcomp
  rw [hcomp', hfund]

end PfaffianDescent
