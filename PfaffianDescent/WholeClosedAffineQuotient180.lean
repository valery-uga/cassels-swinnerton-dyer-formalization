import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! Source-only180. The SAME whole closed subscheme is the quotient by
its actual affine coordinate kernel, with its original embedding and scalars. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Literal original affine section map, using the canonical ΓSpec map. -/
def closedAffineSectionMap180
    {T : Type u} [CommRing T] {Z : Scheme.{u}} (j : Z ⟶ Spec (.of T)) :
    T →+* Γ(Z, ⊤) :=
  ((Scheme.ΓSpecIso (.of T)).inv ≫ j.appTop).hom

/-- The WHOLE actual coordinate ideal, without a chosen presentation. -/
def closedAffineCoordinateIdeal180
    {T : Type u} [CommRing T] {Z : Scheme.{u}} (j : Z ⟶ Spec (.of T)) : Ideal T :=
  RingHom.ker (closedAffineSectionMap180 j)

lemma closedAffineSectionMap180_surjective
    {T : Type u} [CommRing T] {Z : Scheme.{u}}
    (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j] :
    Function.Surjective (closedAffineSectionMap180 j) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine j).2.comp
    (Scheme.ΓSpecIso (.of T)).commRingCatIsoToRingEquiv.symm.surjective

/-- Original scalars commute on EVERY coefficient, before taking a quotient. -/
lemma closedAffineSectionMap180_comp_scalar
    {S T : Type u} [CommRing S] [CommRing T] {Z : Scheme.{u}}
    (j : Z ⟶ Spec (.of T)) (alpha : S →+* T) :
    (closedAffineSectionMap180 j).comp alpha =
      closedAffineSectionMap180 (j ≫ Spec.map (CommRingCat.ofHom alpha)) := by
  change (CommRingCat.ofHom alpha ≫ (Scheme.ΓSpecIso (.of T)).inv ≫ j.appTop).hom =
    ((Scheme.ΓSpecIso (.of S)).inv ≫
      (j ≫ Spec.map (CommRingCat.ofHom alpha)).appTop).hom
  rw [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.comp_appTop]

/-- The original quotient identifies with the global functions of the SAME Z. -/
def closedAffineQuotientRingEquiv180
    {T : Type u} [CommRing T] {Z : Scheme.{u}}
    (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j] :
    (T ⧸ closedAffineCoordinateIdeal180 j) ≃+* Γ(Z, ⊤) :=
  (closedAffineSectionMap180 j).quotientKerEquivOfSurjective
    (closedAffineSectionMap180_surjective j)

lemma closedAffineQuotientRingEquiv180_mk
    {T : Type u} [CommRing T] {Z : Scheme.{u}}
    (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j] (t : T) :
    closedAffineQuotientRingEquiv180 j
      (Ideal.Quotient.mk (closedAffineCoordinateIdeal180 j) t) =
        closedAffineSectionMap180 j t :=
  RingHom.quotientKerEquivOfSurjective_apply_mk
    (closedAffineSectionMap180_surjective j) t

/-- Scheme isomorphism for the SAME entire old Z, not its restriction or support. -/
def closedAffineQuotientIso180
    {T : Type u} [CommRing T] {Z : Scheme.{u}}
    (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j] :
    Z ≅ Spec (.of (T ⧸ closedAffineCoordinateIdeal180 j)) := by
  letI : IsAffine Z := (IsClosedImmersion.isAffine_surjective_of_isAffine j).1
  exact (Scheme.isoSpec Z) ≪≫ Scheme.Spec.mapIso
    (.op (closedAffineQuotientRingEquiv180 j).toCommRingCatIso)

/-- The quotient identification preserves the original closed embedding. -/
lemma closedAffineQuotientIso180_fac
    {T : Type u} [CommRing T] {Z : Scheme.{u}}
    (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j] :
    (closedAffineQuotientIso180 j).hom ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (closedAffineCoordinateIdeal180 j))) = j := by
  letI : IsAffine Z := (IsClosedImmersion.isAffine_surjective_of_isAffine j).1
  have hmaps : CommRingCat.ofHom (Ideal.Quotient.mk (closedAffineCoordinateIdeal180 j)) ≫
      CommRingCat.ofHom (closedAffineQuotientRingEquiv180 j).toRingHom =
        (Scheme.ΓSpecIso (.of T)).inv ≫ j.appTop := by
    ext t
    exact closedAffineQuotientRingEquiv180_mk j t
  change Z.isoSpec.hom ≫ Spec.map
    (CommRingCat.ofHom (closedAffineQuotientRingEquiv180 j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (closedAffineCoordinateIdeal180 j))) = j
  rw [← Spec.map_comp, hmaps, Spec.map_comp,
    Scheme.isoSpec_hom_naturality_assoc, Scheme.isoSpec_Spec_hom,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- This coordinate kernel is the ENTIRE actual closed-immersion ideal
on the affine spectrum, transported only by the native ΓSpec isomorphism. -/
lemma closedAffineCoordinateIdeal180_eq_ideal
    {T : Type u} [CommRing T] {Z : Scheme.{u}}
    (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j] :
    closedAffineCoordinateIdeal180 j =
      (j.ker.ideal ⟨⊤, isAffineOpen_top (Spec (.of T))⟩).comap
        (Scheme.ΓSpecIso (.of T)).inv.hom := by
  rw [Scheme.Hom.ker_apply, RingHom.comap_ker]
  rfl

/-- A whole-Z factor through an actual affine open transports the WHOLE
original ideal by the chart's ACTUAL coordinate equivalence. -/
lemma closedAffineCoordinateIdeal180_eq_chart_ideal
    {T : Type u} [CommRing T] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (a : Spec (.of T) ⟶ X) [IsOpenImmersion a]
    (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j] (hfac : j ≫ a = i) :
    let V : X.affineOpens :=
      ⟨a ''ᵁ ⊤, (isAffineOpen_top (Spec (.of T))).image_of_isOpenImmersion a⟩
    let E := (a.appIso ⊤ ≪≫ Scheme.ΓSpecIso (.of T)).commRingCatIsoToRingEquiv
    closedAffineCoordinateIdeal180 j = (i.ker.ideal V).map E.toRingHom := by
  let H : IsPullback j (𝟙 Z) a i :=
    IsPullback.of_vert_isIso_mono ⟨by simpa only [Category.id_comp] using hfac⟩
  have hk := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    i j (𝟙 Z) a H ⟨⊤, isAffineOpen_top (Spec (.of T))⟩
  rw [closedAffineCoordinateIdeal180_eq_ideal, hk, Ideal.comap_comap]
  exact Ideal.comap_symm
    (a.appIso ⊤ ≪≫ Scheme.ΓSpecIso (.of T)).commRingCatIsoToRingEquiv

/-- Original finite-flat geometry gives finite-flatness of the canonical
quotient map; neither quotient property is supplied by the caller. -/
lemma closedAffineQuotient180_finite_flat
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {Z : Scheme.{u}} (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j]
    [IsFinite (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))]
    [Flat (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))] :
    (closedAffineQuotientIso180 j).hom ≫ Spec.map
      (CommRingCat.ofHom (algebraMap S (T ⧸ closedAffineCoordinateIdeal180 j))) =
        j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        (algebraMap S (T ⧸ closedAffineCoordinateIdeal180 j)))) ∧
      Flat (Spec.map (CommRingCat.ofHom
        (algebraMap S (T ⧸ closedAffineCoordinateIdeal180 j)))) := by
  have hbase : (closedAffineQuotientIso180 j).hom ≫ Spec.map
      (CommRingCat.ofHom (algebraMap S (T ⧸ closedAffineCoordinateIdeal180 j))) =
        j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
    calc
      _ = ((closedAffineQuotientIso180 j).hom ≫
          Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (closedAffineCoordinateIdeal180 j)))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
        rw [Category.assoc, ← Spec.map_comp]
        rfl
      _ = _ := by rw [closedAffineQuotientIso180_fac]
  have hback : (closedAffineQuotientIso180 j).inv ≫
      (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) =
        Spec.map (CommRingCat.ofHom
          (algebraMap S (T ⧸ closedAffineCoordinateIdeal180 j))) := by
    calc
      _ = (closedAffineQuotientIso180 j).inv ≫
          ((closedAffineQuotientIso180 j).hom ≫ Spec.map
            (CommRingCat.ofHom
              (algebraMap S (T ⧸ closedAffineCoordinateIdeal180 j)))) :=
        congrArg (fun f => (closedAffineQuotientIso180 j).inv ≫ f) hbase.symm
      _ = _ := (closedAffineQuotientIso180 j).inv_hom_id_assoc _
  refine ⟨hbase, ?_, ?_⟩
  · exact hback ▸ (inferInstance : IsFinite
      ((closedAffineQuotientIso180 j).inv ≫
        (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))))
  · exact hback ▸ (inferInstance : Flat
      ((closedAffineQuotientIso180 j).inv ≫
        (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))))

end PfaffianDescent
