import PfaffianDescent.ClosedImmersionStalkFlatQuotient173
import PfaffianDescent.SurjectiveFamilyFiberStalkReduction172

/-! SOURCE ONLY / UNVERIFIED173. Actual embedded-deformation ideal
reduction via BOTH actual family stalk reductions and a Cartesian fiber.
No quotient flatness or ideal-image conclusion is supplied as a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

lemma cartesianStalkPointEq173
    {X X0 Z C : Scheme.{u}} {u0 : C ⟶ Z} {v : C ⟶ X0}
    {i : Z ⟶ X} {d : X0 ⟶ X} (H : IsPullback u0 v i d) (w : C) :
    d (v w) = i (u0 w) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun h => h w) H.w.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A supplied Cartesian fiber is ordinary geometric diagram data; its
stalk kernel is DERIVED from the actual fiber, not a caller certificate. -/
lemma cartesianFamilyStalkReduction_kernel173
    {B K : Type u} [CommRing B] [CommRing K] {X X0 : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (d : X0 ⟶ X) (f0 : X0 ⟶ Spec (.of K))
    (H : IsPullback d f0 f (Spec.map (CommRingCat.ofHom b))) (x0 : X0) :
    RingHom.ker (d.stalkMap x0).hom =
      (RingHom.ker b).map (familyBaseToStalk169 f (d x0)) := by
  let e := H.isoPullback
  rw [← H.isoPullback_hom_fst, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap x0)).1]
  exact surjectiveFamilyFiberStalkReduction172_ker f b hb (e.hom x0)

lemma closedFieldPoint_stalkMap_kernel_eq_residue173
    {L : Type u} [Field L] {X : Scheme.{u}}
    (v : Spec (.of L) ⟶ X) [IsClosedImmersion v] (w : Spec (.of L)) :
    RingHom.ker (v.stalkMap w).hom = RingHom.ker (X.residue (v w)).hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (v w)) isOpen_univ
  rw [← cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel
    v ⟨U, hU⟩ w hxU,
    cubicClosedPointSerreZeroIdealStalk_map_eq_maximal v ⟨U, hU⟩ w hxU]
  change IsLocalRing.maximalIdeal (X.presheaf.stalk (v w)) =
    RingHom.ker (IsLocalRing.residue (X.presheaf.stalk (v w)))
  exact IsLocalRing.ker_residue.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The WHOLE ideal of the actual embedded closed scheme reduces to the
WHOLE kernel of its actual Cartesian special-fiber immersion. The scalar
comparison and both reduction kernels are derived internally. -/
lemma embeddedCartesianFiber_stalkIdeal_image173
    {B K : Type u} [CommRing B] [CommRing K] {X X0 Z C : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (d : X0 ⟶ X) (f0 : X0 ⟶ Spec (.of K))
    (H0 : IsPullback d f0 f (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X) [IsClosedImmersion i] (u0 : C ⟶ Z) (v : C ⟶ X0)
    (H : IsPullback u0 v i d) (w : C) :
    (RingHom.ker (closedImmersionStalkAt173 i (d (v w)) (u0 w)
      (cartesianStalkPointEq173 H w))).map (d.stalkMap (v w)).hom =
      RingHom.ker (v.stalkMap w).hom := by
  let c := closedImmersionStalkAt173 i (d (v w)) (u0 w) (cartesianStalkPointEq173 H w)
  let pi := (d.stalkMap (v w)).hom
  let lam := (u0.stalkMap w).hom
  let rho := (v.stalkMap w).hom
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom b)) :=
    IsClosedImmersion.spec_of_surjective _ hb
  letI : IsClosedImmersion d := MorphismProperty.of_isPullback H0.flip
    (inferInstance : IsClosedImmersion (Spec.map (CommRingCat.ofHom b)))
  have hc : Function.Surjective c :=
    closedImmersionStalkAt173_surjective i _ _ (cartesianStalkPointEq173 H w)
  have hpi : Function.Surjective pi := d.stalkMap_surjective (v w)
  have hcomm : lam.comp c = rho.comp pi := by
    have hh := Scheme.Hom.stalkMap_congr_hom (v ≫ d) (u0 ≫ i) H.w.symm w
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hh
    have hh' := congrArg (fun a => a.hom) hh.symm
    change (u0.stalkMap w).hom.comp
        ((X.presheaf.stalkCongr (.of_eq (cartesianStalkPointEq173 H w))).hom ≫
          i.stalkMap (u0 w)).hom =
      (v.stalkMap w).hom.comp (d.stalkMap (v w)).hom
    simpa only [Scheme.Hom.comp_apply, CommRingCat.hom_comp,
      RingHom.comp_assoc] using hh'
  have hpiKer := cartesianFamilyStalkReduction_kernel173 f b hb d f0 H0 (v w)
  have hZ := H.paste_vert H0
  have hlamKer := cartesianFamilyStalkReduction_kernel173 (i ≫ f) b hb
    u0 (v ≫ f0) hZ w
  have hker : RingHom.ker lam = (RingHom.ker pi).map c := by
    rw [hlamKer, hpiKer, Ideal.map_map,
      closedImmersionStalkAt173_coefficient f i _ _ (cartesianStalkPointEq173 H w)]
  exact map_kernel_of_reduction_square173 c pi lam rho hc hpi hcomm hker

/-- If the specified Cartesian special fiber is the ACTUAL original
closed field point, the whole embedded ideal reduces to its residue
kernel, not merely an abstract ideal of an isomorphic local ring. -/
lemma embeddedCartesianFieldPoint_stalkIdeal_image_residue173
    {B K L : Type u} [CommRing B] [CommRing K] [Field L]
    {X X0 Z : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (d : X0 ⟶ X) (f0 : X0 ⟶ Spec (.of K))
    (H0 : IsPullback d f0 f (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X) [IsClosedImmersion i] (u0 : Spec (.of L) ⟶ Z)
    (v : Spec (.of L) ⟶ X0) [IsClosedImmersion v]
    (H : IsPullback u0 v i d) (w : Spec (.of L)) :
    (RingHom.ker (closedImmersionStalkAt173 i (d (v w)) (u0 w)
      (cartesianStalkPointEq173 H w))).map (d.stalkMap (v w)).hom =
      RingHom.ker (X0.residue (v w)).hom :=
  (embeddedCartesianFiber_stalkIdeal_image173 f b hb d f0 H0 i u0 v H w).trans
    (closedFieldPoint_stalkMap_kernel_eq_residue173 v w)

end PfaffianDescent
