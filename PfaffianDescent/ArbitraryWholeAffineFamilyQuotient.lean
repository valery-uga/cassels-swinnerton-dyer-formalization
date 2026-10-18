import PfaffianDescent.NativeOpenContainedFiniteFlatPointEquiv315
import Mathlib.RingTheory.LocalRing.Module

/-!
Replace an arbitrary whole
finite-flat family lying in an actual affine open by its canonically
constructed affine quotient, with the original embedding ideal and rank.
No quotient ideal, quotient family, or finite-flat certificate is input.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u
set_option autoImplicit false

theorem arbitraryWholeAffineFamily_exists_finiteFlatQuotient001
    {S A : Type u} [CommRing S] [IsLocalRing S] [CommRing A] [Algebra S A]
    {X : Scheme.{u}} (F : X ⟶ Spec (.of S)) (n : ℕ)
    (P : FiniteFlatHilbertPoint195 F n)
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap S A)))
    (hcontains : Set.range P.val.subschemeι ⊆ Set.range a) :
    ∃ J : Ideal A,
      Module.Finite S (A ⧸ J) ∧ Module.Flat S (A ⧸ J) ∧
      Module.finrank S (A ⧸ J) = n ∧
      P.val = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a).ker := by
  let i := nativeOpenContainedSourceLift315 a F n P hcontains
  letI : IsClosedImmersion i :=
    nativeOpenContainedSourceLift_isClosed315 a F n P hcontains
  obtain ⟨J, e, hie⟩ := (IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion i))
  let Q := A ⧸ J
  let j : Spec (.of Q) ⟶ X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a
  let b : Spec (.of Q) ⟶ Spec (.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S Q))
  have he : e.hom ≫ j = P.val.subschemeι := by
    change e.hom ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a) = _
    rw [← Category.assoc, ← hie]
    exact nativeOpenContainedSourceLift_fac315 a F n P hcontains
  have hj : j ≫ F = b := by
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a) ≫ F = _
    rw [Category.assoc, ha, ← Spec.map_comp]
    rfl
  have hb : e.hom ≫ b = P.val.subschemeι ≫ F := by
    rw [← hj, ← Category.assoc, he]
  have hbinv : b = e.inv ≫ (P.val.subschemeι ≫ F) := by
    rw [← hb]
    simp
  letI : IsFinite (P.val.subschemeι ≫ F) := P.property.1
  letI : Flat (P.val.subschemeι ≫ F) := P.property.2.1
  letI : IsFinite b := by rw [hbinv]; infer_instance
  letI : Flat b := by rw [hbinv]; infer_instance
  letI : Module.Finite S Q := RingHom.finite_algebraMap.mp
    ((IsFinite.SpecMap_iff _).mp (inferInstance : IsFinite b))
  letI : Module.Flat S Q := RingHom.flat_algebraMap_iff.mp
    (Flat.SpecMap_iff.mp (inferInstance : Flat b))
  letI : Module.Free S Q := Module.free_of_flat_of_isLocalRing
  have hn : Module.finrank S Q = n := by
    calc
      Module.finrank S Q = b.finrank (IsLocalRing.closedPoint S) := by
        exact ((Scheme.Hom.finrank_SpecMap_algebraMap S Q _).trans
          (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := S) (M := Q)) _)).symm
      _ = (e.hom ≫ b).finrank (IsLocalRing.closedPoint S) :=
        (congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.hom b) _).symm
      _ = n := by rw [hb]; exact P.property.2.2 _
  refine ⟨J, inferInstance, inferInstance, hn, ?_⟩
  calc
    P.val = P.val.subschemeι.ker := P.val.ker_subschemeι.symm
    _ = (e.hom ≫ j).ker := congrArg (fun f ↦ f.ker) he.symm
    _ = j.ker := Scheme.Hom.ker_comp_of_isIso e.hom j

end PfaffianDescent
end
