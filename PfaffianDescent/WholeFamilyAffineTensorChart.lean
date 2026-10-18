import PfaffianDescent.WholeFiniteSupportAffineNeighborhood
import PfaffianDescent.ActualAffineTensorFiber174

/-!
Construct an upstairs affine
chart whose actual tensor-product special chart contains the entire given
downstairs finite family.  The homogeneous form is selected upstairs
directly; no finite-field linear-form avoidance or coefficient lift of a
downstairs open is required.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u v
set_option autoImplicit false

structure WholeFamilyAffineTensorChart001
    {B S : Type u} [CommRing B] [CommRing S] [Algebra B S]
    {X X0 : Scheme.{u}} (F : X ⟶ Spec (.of B)) (F0 : X0 ⟶ Spec (.of S))
    (d : X0 ⟶ X) (n : ℕ) (P : FiniteFlatHilbertPoint195 F0 n) where
  A : Type u
  [commRing : CommRing A]
  [algebra : Algebra B A]
  a : Spec (.of A) ⟶ X
  [openImmersion : IsOpenImmersion a]
  toBase : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap B A))
  a0 : Spec (.of (S ⊗[B] A)) ⟶ X0
  cartesian : IsPullback
    (Spec.map (CommRingCat.ofHom (affineTensorFiberReduction174
      (R := B) (S := S) (A := A)).toRingHom)) a0 a d
  specialToBase : a0 ≫ F0 =
    Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[B] A)))
  contains : Set.range P.val.subschemeι ⊆ Set.range a0

attribute [instance] WholeFamilyAffineTensorChart001.commRing
  WholeFamilyAffineTensorChart001.algebra WholeFamilyAffineTensorChart001.openImmersion

/-- An affine morphism to the original projective ambient constructs one
affine tensor chart. This includes every affine coefficient base change
of the original projective closed embedding. -/
theorem exists_wholeFamilyAffineTensorChart001
    {B S C : Type u} [CommRing B] [CommRing S] [IsLocalRing S] [Algebra B S]
    [CommRing C] {sigma : Type v} [SetLike sigma C] [AddSubgroupClass sigma C]
    (grading : ℕ → sigma) [GradedRing grading]
    {X X0 : Scheme.{u}} (q : X ⟶ Proj grading) [IsAffineHom q]
    (F : X ⟶ Spec (.of B)) (F0 : X0 ⟶ Spec (.of S)) (d : X0 ⟶ X)
    (Hbase : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap B S))))
    (n : ℕ) (P : FiniteFlatHilbertPoint195 F0 n) :
    Nonempty (WholeFamilyAffineTensorChart001 F F0 d n P) := by
  obtain ⟨c, hc, hcontains⟩ :=
    finiteFamilyProjective_overLocal_exists_wholeAffineChart001 grading (d ≫ q) F0 n P
  let U : X.Opens := q ⁻¹ᵁ Proj.basicOpen grading c.val
  letI : IsAffine U := hc.preimage q
  let A := Γ(U, ⊤)
  let a : Spec (.of A) ⟶ X := U.toScheme.isoSpec.inv ≫ U.ι
  letI : IsOpenImmersion a := inferInstance
  let f : B →+* A := (Spec.preimage (a ≫ F)).hom
  letI : Algebra B A := f.toAlgebra
  have ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap B A)) :=
    (Spec.map_preimage (a ≫ F)).symm
  let pi := affineTensorFiberReduction174 (R := B) (S := S) (A := A)
  let p := Spec.map (CommRingCat.ofHom pi.toRingHom)
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
  have hU : Set.range (P.val.subschemeι ≫ d) ⊆ Set.range U.ι := by
    rw [U.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hcontains (Set.mem_range_self z)
  let iU := IsOpenImmersion.lift U.ι (P.val.subschemeι ≫ d) hU
  have hiU : iU ≫ U.ι = P.val.subschemeι ≫ d :=
    IsOpenImmersion.lift_fac _ _ _
  let iA := iU ≫ U.toScheme.isoSpec.hom
  have hiA : iA ≫ a = P.val.subschemeι ≫ d := by
    dsimp only [iA, a]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hiU
  let i0 := Hchart.lift iA P.val.subschemeι hiA
  have hi0 : i0 ≫ a0 = P.val.subschemeι := Hchart.lift_snd _ _ _
  refine ⟨{
    A := A
    a := a
    toBase := ha
    a0 := a0
    cartesian := Hchart
    specialToBase := ha0F
    contains := ?_ }⟩
  rintro _ ⟨z, rfl⟩
  refine ⟨i0 z, ?_⟩
  exact congrArg (fun f ↦ f z) hi0

end PfaffianDescent
end
