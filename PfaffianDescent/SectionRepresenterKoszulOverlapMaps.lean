import PfaffianDescent.SectionRepresenterKoszul
import PfaffianDescent.AffinePointKoszulOverlap

/-!
# Koszul overlap lifts as morphisms of sheaves

Scalar coefficients on a smaller open define maps into the Koszul terms
on the parameter neighborhood. Their last differential is the specified
scalar times the inclusion map. This converts Bezout section lifts into
the maps required by the Cech comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
/-- Scalar multiplication on a representer commutes with restriction of
the scalar and the covariant map of representers. -/
theorem sectionRepresenter_map_comp_scalar
    {W U : C} (j : W ⟶ U) (a : R.val.obj (op U)) :
    (sectionRepresenterFunctor R).map j ≫ sectionRepresenterScalarEndomorphism R U a =
      sectionRepresenterScalarEndomorphism R W (R.val.map j.op a) ≫
        (sectionRepresenterFunctor R).map j := by
  apply (sectionRepresenterHomEquiv R W (sectionRepresenter R U)).injective
  rw [sectionRepresenterHomEquiv_precomp,
    sectionRepresenterHomEquiv_scalarEndomorphism,
    sectionRepresenterHomEquiv_scalarEndomorphism_comp,
    PresheafOfModules.map_smul]
  congr 1
  have h := sectionRepresenterHomEquiv_precomp R j (sectionRepresenter R U)
    (𝟙 (sectionRepresenter R U))
  change sectionRepresenterHomEquiv R W (sectionRepresenter R U)
    ((sectionRepresenterFunctor R).map j ≫ 𝟙 (sectionRepresenter R U)) =
    (sectionRepresenter R U).val.map j.op (sectionRepresenterGenerator R U) at h
  have hk : ((sectionRepresenterFunctor R).map j :
      sectionRepresenter R W ⟶ sectionRepresenter R U) ≫
      𝟙 (sectionRepresenter R U) = (sectionRepresenterFunctor R).map j :=
    Category.comp_id _
  exact h.symm.trans (congrArg (sectionRepresenterHomEquiv R W (sectionRepresenter R U)) hk)

/-- A coefficient on an overlap specifies a scalar multiple of its map
into the parameter-neighborhood representer. -/
def sectionRepresenterOverlapScalar {W U : C} (j : W ⟶ U)
    (a : R.val.obj (op W)) :
    sectionRepresenter R W ⟶ sectionRepresenter R U :=
  sectionRepresenterScalarEndomorphism R W a ≫ (sectionRepresenterFunctor R).map j

set_option backward.isDefEq.respectTransparency false in
/-- Restricting an overlap scalar morphism restricts its section coefficient. -/
theorem sectionRepresenterOverlapScalar_precomp
    {V W U : C} (k : V ⟶ W) (j : W ⟶ U) (a : R.val.obj (op W)) :
    (sectionRepresenterFunctor R).map k ≫ sectionRepresenterOverlapScalar R j a =
      sectionRepresenterOverlapScalar R (k ≫ j) (R.val.map k.op a) := by
  simp only [sectionRepresenterOverlapScalar, ← Category.assoc,
    sectionRepresenter_map_comp_scalar]
  rw [Category.assoc, ← Functor.map_comp]

/-- A pair of overlap coefficients defines the degree-one comparison map. -/
def sectionRepresenterKoszulOverlapLift {W U : C} (j : W ⟶ U)
    (a b : R.val.obj (op W)) :
    sectionRepresenter R W ⟶ ⨁ sectionRepresenterKoszulPair R U :=
  biproduct.lift ![sectionRepresenterOverlapScalar R j a,
    sectionRepresenterOverlapScalar R j b]

set_option backward.isDefEq.respectTransparency false in
/-- Applying the last Koszul differential to the overlap lift gives its
actual section coefficient under the inclusion map. -/
theorem sectionRepresenterKoszulOverlapLift_comp_last
    {W U : C} (j : W ⟶ U) (q f : R.val.obj (op U))
    (a b : R.val.obj (op W)) :
    sectionRepresenterKoszulOverlapLift R j a b ≫
        sectionRepresenterKoszulLast R U q f =
      sectionRepresenterOverlapScalar R j
        (a * R.val.map j.op q + b * R.val.map j.op f) := by
  rw [sectionRepresenterKoszulOverlapLift, sectionRepresenterKoszulLast,
    biproduct.lift_desc]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sectionRepresenterOverlapScalar, Category.assoc,
    sectionRepresenter_map_comp_scalar]
  simp only [← Category.assoc, sectionRepresenterScalarEndomorphism_comp]
  rw [← Preadditive.add_comp, ← sectionRepresenterScalarEndomorphism_add]

set_option backward.isDefEq.respectTransparency false in
/-- A scalar overlap map followed by the first Koszul differential has
the two expected restricted section coefficients. -/
theorem sectionRepresenterOverlapScalar_comp_first
    {W U : C} (j : W ⟶ U) (q f : R.val.obj (op U))
    (c : R.val.obj (op W)) :
    sectionRepresenterOverlapScalar R j c ≫
        sectionRepresenterKoszulFirst R U q f =
      sectionRepresenterKoszulOverlapLift R j
        (c * R.val.map j.op (-f)) (c * R.val.map j.op q) := by
  apply biproduct.hom_ext
  intro k
  fin_cases k
  · simp only [sectionRepresenterKoszulFirst, sectionRepresenterKoszulOverlapLift,
      Category.assoc, biproduct.lift_π]
    change (sectionRepresenterScalarEndomorphism R W c ≫
      (sectionRepresenterFunctor R).map j) ≫
        sectionRepresenterScalarEndomorphism R U (-f) =
      sectionRepresenterScalarEndomorphism R W (c * R.val.map j.op (-f)) ≫
        (sectionRepresenterFunctor R).map j
    rw [Category.assoc, sectionRepresenter_map_comp_scalar,
      ← Category.assoc, sectionRepresenterScalarEndomorphism_comp]
  · simp only [sectionRepresenterKoszulFirst, sectionRepresenterKoszulOverlapLift,
      Category.assoc, biproduct.lift_π]
    change (sectionRepresenterScalarEndomorphism R W c ≫
      (sectionRepresenterFunctor R).map j) ≫
        sectionRepresenterScalarEndomorphism R U q =
      sectionRepresenterScalarEndomorphism R W (c * R.val.map j.op q) ≫
        (sectionRepresenterFunctor R).map j
    rw [Category.assoc, sectionRepresenter_map_comp_scalar,
      ← Category.assoc, sectionRepresenterScalarEndomorphism_comp]

end PfaffianDescent

namespace PfaffianDescent

open AlgebraicGeometry

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
/-- The geometric isolated-zero condition supplies an actual morphism of
sheaves lifting any scalar inclusion on an affine overlap away from the point. -/
theorem exists_sectionRepresenterKoszulOverlapLift_away_point
    {X : Scheme.{u}} (U : X.Opens) (x : X) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ U) (hxW : x ∉ W)
    (t : Γ(X, W)) :
    ∃ v : sectionRepresenter X.ringCatSheaf W ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U,
      v ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
        sectionRepresenterOverlapScalar X.ringCatSheaf (homOfLE hWU) t := by
  obtain ⟨⟨a, b⟩, hab⟩ :=
    exists_affine_point_koszul_overlap_lift U x q f haway W hW hWU hxW t
  refine ⟨sectionRepresenterKoszulOverlapLift X.ringCatSheaf (homOfLE hWU) a b, ?_⟩
  rw [sectionRepresenterKoszulOverlapLift_comp_last]
  have hcoeff : a * X.presheaf.map (homOfLE hWU).op q +
      b * X.presheaf.map (homOfLE hWU).op f = t := by
    change X.presheaf.map (homOfLE hWU).op q * a +
      X.presheaf.map (homOfLE hWU).op f * b = t at hab
    simpa only [mul_comm] using hab
  change sectionRepresenterOverlapScalar X.ringCatSheaf (homOfLE hWU)
    (a * X.presheaf.map (homOfLE hWU).op q +
      b * X.presheaf.map (homOfLE hWU).op f) = _
  rw [hcoeff]

end PfaffianDescent
