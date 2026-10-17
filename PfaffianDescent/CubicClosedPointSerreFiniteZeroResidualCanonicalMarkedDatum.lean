import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFieldBaseChangeDatum
import PfaffianDescent.SerreActualClosedPullbackZeroMarkedFibre
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalFibreBaseChange

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- A field stalk at the actual canonical extension fibre suffices for the
degree-eight residual. No new relative marked-open membership is required. -/
theorem cubicClosedPointSerreFiniteZeroResidual_canonicalMarked_datum_eight
    {K E L : Type u} [Field K] [Field E] [Field L] [Algebra K E]
    {X X₀ Z P : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) (c : X₀ ⟶ X) [IsClosedImmersion c]
    [IsFinite (c ≫ x)] (i : Spec (.of L) ⟶ X₀) [IsClosedImmersion i]
    (z : Z ⟶ P) (t : Spec (.of K) ⟶ P)
    (v : X₀ ≅ pullback z t)
    (hv : v.hom ≫ pullback.snd z t = c ≫ x)
    (y : (pullback z (Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t) : Scheme))
    (hy : IsField ((pullback z
      (Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t)).presheaf.stalk y))
    (hpoint :
      let r := Spec.map (CommRingCat.ofHom (algebraMap K E))
      let w := serreIncidenceCanonicalFibreBaseChangeIso z t (c ≫ x) v hv r
      c (pullback.fst (c ≫ x) r (w.inv y)) = c (i (IsLocalRing.closedPoint L)))
    (hX : finiteSchemeRank (c ≫ x) = 11)
    (hL : finiteSchemeRank (i ≫ c ≫ x) = 3) :
    ∃ D : FiniteSubschemeDatum x 8,
      Disjoint (Set.range D.val.subschemeι) (Set.range (i ≫ c)) := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let w := serreIncidenceCanonicalFibreBaseChangeIso z t (c ≫ x) v hv r
  have hf := serreActualChosenFibreIso_stalk_isField w.symm y hy
  exact cubicClosedPointSerreFiniteZeroResidual_fieldBaseChange_datum_eight
    i c x (w.inv y) (c.isClosedEmbedding.injective hpoint) hf hX hL

end PfaffianDescent
