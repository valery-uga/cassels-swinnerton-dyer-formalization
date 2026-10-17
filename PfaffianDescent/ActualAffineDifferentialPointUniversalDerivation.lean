import PfaffianDescent.ActualAffineSheafPointClass
import PfaffianDescent.ActualAffineDifferentialPointClassAction

/- SOURCE ONLY / UNVERIFIED. SAME original D-section point-class result,
now following the accepted actual195 point_D law directly. No old sheaf
Iso or independently assumed differential comparison is used. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k R L : Type u} [CommRing k] [CommRing R] [CommRing L] [Algebra k R]

/-- The actual canonical top algebra used by ΓSpecIso_inv. Explicitly
name it instead of requiring synthesis through the scheme/ring aliases. -/
private instance actualAffinePointTopSectionAlgebra :
    Algebra R Γ(Spec (CommRingCat.of R), ⊤) :=
  StructureSheaf.openAlgebra R (op ⊤)

lemma actualAffineDifferentialPointClass_eq_actualPullbackD
    (ρ : R →+* L) (r : R) :
    actualAffineDifferentialPointClass (k := k) ρ r =
      actualAffineSheafPointClass (CommRingCat.ofHom ρ)
        (schemeRelativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap k R))))
        (actualRelativeDifferentialSection
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
            (algebraMap R Γ(Spec (CommRingCat.of R), ⊤) r)) := by
  have h := actualAffineDifferentialTildeToGenuineSheaf_point_D
    (k := k) (R := R) ρ r
  have hr : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r =
      algebraMap R Γ(Spec (CommRingCat.of R), ⊤) r :=
    RingHom.congr_fun
      (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv (CommRingCat.of R))) r
  change actualAffineDifferentialPointClass (k := k) ρ r = _ at h
  exact h.trans (congrArg (fun z =>
    actualAffineSheafPointClass (CommRingCat.ofHom ρ)
      (schemeRelativeDifferentials
        (Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (actualRelativeDifferentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤ z)) hr)

end PfaffianDescent
