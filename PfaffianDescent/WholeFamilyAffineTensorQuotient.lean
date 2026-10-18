import PfaffianDescent.WholeFamilyAffineTensorChart
import PfaffianDescent.ArbitraryWholeAffineFamilyQuotient

/-!
Natural geometric intake for
the semilocal Hilbert--Burch construction, starting with the literal
original finite-flat Hilbert point.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u v
set_option autoImplicit false

theorem exists_wholeFamilyAffineTensorQuotient001
    {B S C : Type u} [CommRing B] [CommRing S] [IsLocalRing S] [Algebra B S]
    [CommRing C] {sigma : Type v} [SetLike sigma C] [AddSubgroupClass sigma C]
    (grading : ℕ → sigma) [GradedRing grading]
    {X X0 : Scheme.{u}} (q : X ⟶ Proj grading) [IsAffineHom q]
    (F : X ⟶ Spec (.of B)) (F0 : X0 ⟶ Spec (.of S)) (d : X0 ⟶ X)
    (Hbase : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap B S))))
    (n : ℕ) (P : FiniteFlatHilbertPoint195 F0 n) :
    ∃ T : WholeFamilyAffineTensorChart001 F F0 d n P,
      ∃ J : Ideal (S ⊗[B] T.A),
        Module.Finite S ((S ⊗[B] T.A) ⧸ J) ∧
        Module.Flat S ((S ⊗[B] T.A) ⧸ J) ∧
        Module.finrank S ((S ⊗[B] T.A) ⧸ J) = n ∧
        P.val = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ T.a0).ker := by
  obtain ⟨T⟩ := exists_wholeFamilyAffineTensorChart001 grading q F F0 d Hbase n P
  letI : IsOpenImmersion T.a0 := MorphismProperty.of_isPullback T.cartesian
    (inferInstance : IsOpenImmersion T.a)
  obtain ⟨J, hfinite, hflat, hn, hP⟩ :=
    arbitraryWholeAffineFamily_exists_finiteFlatQuotient001 F0 n P T.a0
      T.specialToBase T.contains
  exact ⟨T, J, hfinite, hflat, hn, hP⟩

end PfaffianDescent
end
