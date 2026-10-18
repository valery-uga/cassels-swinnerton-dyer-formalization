import PfaffianDescent.ActualAffineTensorFiber174

/-!
Construct the actual chart
over any geometric base change, including reduction to the Artin test's
residue field.  The ambient Cartesian chart is a conclusion.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
set_option autoImplicit false

theorem exists_actualAffineTensorChartBaseChange001
    {B S A : Type u} [CommRing B] [CommRing S] [CommRing A]
    [Algebra B S] [Algebra B A] {X X0 : Scheme.{u}}
    (F : X ⟶ Spec (.of B)) (F0 : X0 ⟶ Spec (.of S)) (d : X0 ⟶ X)
    (Hbase : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap B S))))
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap B A))) :
    ∃ a0 : Spec (.of (S ⊗[B] A)) ⟶ X0,
      IsOpenImmersion a0 ∧
      IsPullback (Spec.map (CommRingCat.ofHom
        (affineTensorFiberReduction174 (R := B) (S := S) (A := A)).toRingHom)) a0 a d ∧
      a0 ≫ F0 = Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[B] A))) := by
  let p := Spec.map (CommRingCat.ofHom
    (affineTensorFiberReduction174 (R := B) (S := S) (A := A)).toRingHom)
  let b := Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[B] A)))
  have Htensor := affineTensorFiberReduction174_isPullback (R := B) (S := S) (A := A)
  have hw : (p ≫ a) ≫ F = b ≫ Spec.map (CommRingCat.ofHom (algebraMap B S)) := by
    rw [Category.assoc, ha]
    exact Htensor.w
  let a0 := Hbase.lift (p ≫ a) b hw
  have ha0d : a0 ≫ d = p ≫ a := Hbase.lift_fst _ _ _
  have ha0F : a0 ≫ F0 = b := Hbase.lift_snd _ _ _
  have Houter : IsPullback p (a0 ≫ F0) (a ≫ F)
      (Spec.map (CommRingCat.ofHom (algebraMap B S))) := by
    rw [ha0F, ha]
    exact Htensor
  have Hchart : IsPullback p a0 a d := Houter.of_bot ha0d.symm Hbase
  exact ⟨a0, MorphismProperty.of_isPullback Hchart
    (inferInstance : IsOpenImmersion a), Hchart, ha0F⟩

end PfaffianDescent
end
