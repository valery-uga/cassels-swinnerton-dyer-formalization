import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.LocalRing.Module

/-! SOURCE ONLY / UNVERIFIED188. Native finite-flat ranks in actual
Cartesian field-point fibers, retaining the specified coefficient maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Actual finite-flat spectrum geometry over a local base gives its
module finrank at every base point. No freeness certificate is supplied. -/
lemma localFiniteFlatSpec_finrank188
    {S Q : Type u} [CommRing S] [IsLocalRing S] [CommRing Q] [Algebra S Q]
    [IsFinite (Spec.map (CommRingCat.ofHom (algebraMap S Q)))]
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap S Q)))]
    (x : PrimeSpectrum S) :
    (Spec.map (CommRingCat.ofHom (algebraMap S Q))).finrank x =
      Module.finrank S Q := by
  letI : Module.Finite S Q := RingHom.finite_algebraMap.mp
    ((IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap S Q))).mp inferInstance)
  letI : Module.Flat S Q := RingHom.flat_algebraMap_iff.mp
    ((Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap S Q))).mp inferInstance)
  letI : Module.Free S Q := Module.free_of_flat_of_isLocalRing
  exact (Scheme.Hom.finrank_SpecMap_algebraMap S Q x).trans
    (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := S) (M := Q)) x)

/-- The actual Cartesian field-point fiber has exactly its original
K-residue degree. Fiber finiteness is derived from finite-flat geometry. -/
lemma finiteFlatCartesianFieldPoint_finrank188
    {S K L : Type u} [CommRing S] [Field K] [Field L] [Algebra K L]
    {Z : Scheme.{u}} (F : Z ⟶ Spec (.of S)) [IsFinite F] [Flat F]
    (b : S →+* K) (u0 : Spec (.of L) ⟶ Z)
    (H : IsPullback u0 (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      F (Spec.map (CommRingCat.ofHom b))) :
    F.finrank ((Spec.map (CommRingCat.ofHom b)) (IsLocalRing.closedPoint K)) =
      Module.finrank K L := by
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    MorphismProperty.of_isPullback H (inferInstance : IsFinite F)
  letI : Module.Finite K L := RingHom.finite_algebraMap.mp
    ((IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap K L))).mp inferInstance)
  have hfiber := Scheme.Hom.finrank_of_isPullback u0
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) F
    (Spec.map (CommRingCat.ofHom b)) H (IsLocalRing.closedPoint K)
  exact hfiber.symm.trans
    ((Scheme.Hom.finrank_SpecMap_algebraMap K L (IsLocalRing.closedPoint K)).trans
      (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := L)) _))

end PfaffianDescent
