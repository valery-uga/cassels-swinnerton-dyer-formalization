import PfaffianDescent.ActualFamilyFiberStalkReduction171

/-! Source-only181. Actual principal section coordinates, whole ideal
restriction, actual chart image, and original chart coefficient maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors
universe u

def principalAffineSectionsEquiv181
    {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U)) :
    Localization.Away f ≃+* Γ(X, X.basicOpen f) := by
  letI := U.2.isLocalization_basicOpen f
  exact (IsLocalization.algEquiv (Submonoid.powers f)
    (Localization.Away f) Γ(X, X.basicOpen f)).toRingEquiv

lemma principalAffineSectionsEquiv181_comp
    {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U)) :
    (principalAffineSectionsEquiv181 U f).toRingHom.comp
      (algebraMap Γ(X, U) (Localization.Away f)) =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom := by
  letI := U.2.isLocalization_basicOpen f
  apply RingHom.ext
  intro s
  exact (IsLocalization.algEquiv (Submonoid.powers f)
    (Localization.Away f) Γ(X, X.basicOpen f)).commutes s

/-- The WHOLE actual ideal on the principal open is the image of the
WHOLE original ideal under179's map followed by the canonical section map. -/
lemma principalAffineSectionsEquiv181_whole_ideal
    {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.affineOpens) (f : Γ(X, U)) :
    ((i.ker.ideal U).map (algebraMap Γ(X, U) (Localization.Away f))).map
      (principalAffineSectionsEquiv181 U f).toRingHom =
        i.ker.ideal ⟨X.basicOpen f, U.2.basicOpen f⟩ := by
  rw [Ideal.map_map, principalAffineSectionsEquiv181_comp]
  exact i.ker.map_ideal
    (U := ⟨X.basicOpen f, U.2.basicOpen f⟩) (V := U) (X.basicOpen_le f)

def principalAffineAwayChart181
    {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U)) :
    Spec (.of (Localization.Away f)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away f))) ≫ U.2.fromSpec

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma principalAffineAwayChart181_isOpenImmersion
    {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U)) :
    IsOpenImmersion (principalAffineAwayChart181 U f) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Localization.Away f)))) :=
    IsOpenImmersion.of_isLocalization (S := Localization.Away f) f
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  dsimp only [principalAffineAwayChart181]
  infer_instance

/-- The actual chart image is EXACTLY179's principal neighborhood. -/
lemma principalAffineAwayChart181_range
    {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U)) :
    Set.range (principalAffineAwayChart181 U f) = (X.basicOpen f : Set X) := by
  have hr : Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Localization.Away f)))) =
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Γ(X, U))) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  change Set.range (U.2.fromSpec ∘
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away f)))) = _
  rw [Set.range_comp, hr]
  exact congrArg (fun W : X.Opens => (W : Set X)) (U.2.fromSpec_image_basicOpen f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chart built from Away coordinates equals the chart built from the
ACTUAL section ring of the SAME principal open. -/
lemma principalAffineAwayChart181_section_coordinates
    {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U)) :
    let V : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
    Spec.map (CommRingCat.ofHom (principalAffineSectionsEquiv181 U f).symm.toRingHom) ≫
      V.2.fromSpec = principalAffineAwayChart181 U f := by
  let E := principalAffineSectionsEquiv181 U f
  let res := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  have hinv : E.symm.toRingHom.comp res = algebraMap Γ(X, U) (Localization.Away f) := by
    apply RingHom.ext
    intro s
    apply E.injective
    change E (E.symm (res s)) =
      E (algebraMap Γ(X, U) (Localization.Away f) s)
    rw [E.apply_symm_apply]
    exact (DFunLike.congr_fun (principalAffineSectionsEquiv181_comp U f) s).symm
  calc
    _ = Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom res) ≫ U.2.fromSpec := by
      exact congrArg (fun k => Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ k)
        (U.2.map_fromSpec (U.2.basicOpen f) (homOfLE (X.basicOpen_le f)).op).symm
    _ = _ := by
      rw [← Spec.map_comp_assoc]
      change Spec.map (CommRingCat.ofHom (E.symm.toRingHom.comp res)) ≫ U.2.fromSpec =
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, U) (Localization.Away f))) ≫ U.2.fromSpec
      exact congrArg (fun g : Γ(X, U) →+* Localization.Away f =>
        Spec.map (CommRingCat.ofHom g) ≫ U.2.fromSpec) hinv

lemma principalAffineAwayChart181_base
    {S : Type u} [CommRing S] {X : Scheme.{u}}
    (F : X ⟶ Spec (.of S)) (U : X.affineOpens) (f : Γ(X, U)) :
    principalAffineAwayChart181 U f ≫ F = Spec.map (CommRingCat.ofHom
      ((algebraMap Γ(X, U) (Localization.Away f)).comp (familySpecChartRingMap171 F U))) := by
  dsimp only [principalAffineAwayChart181]
  rw [Category.assoc, ← familySpecChartRingMap171_spec F U, ← Spec.map_comp]
  rfl

def actualAffineChartOpen181
    {T : Type u} [CommRing T] {X : Scheme.{u}}
    (a : Spec (.of T) ⟶ X) [IsOpenImmersion a] : X.affineOpens :=
  ⟨a ''ᵁ ⊤, (isAffineOpen_top (Spec (.of T))).image_of_isOpenImmersion a⟩

def actualAffineChartCoordinates181
    {T : Type u} [CommRing T] {X : Scheme.{u}}
    (a : Spec (.of T) ⟶ X) [IsOpenImmersion a] :
    Γ(X, actualAffineChartOpen181 a) ≃+* T :=
  (a.appIso ⊤ ≪≫ Scheme.ΓSpecIso (.of T)).commRingCatIsoToRingEquiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualAffineChartCoordinates181_spec
    {T : Type u} [CommRing T] {X : Scheme.{u}}
    (a : Spec (.of T) ⟶ X) [IsOpenImmersion a] :
    Spec.map (CommRingCat.ofHom (actualAffineChartCoordinates181 a).toRingHom) ≫
      (actualAffineChartOpen181 a).2.fromSpec = a := by
  have h : Spec.map (a.appIso ⊤).hom ≫ (actualAffineChartOpen181 a).2.fromSpec =
      Spec.map (Scheme.ΓSpecIso (.of T)).inv ≫ a := by
    rw [Scheme.Hom.appIso_hom']
    have ht := IsAffineOpen.SpecMap_appLE_fromSpec a
      ((isAffineOpen_top (Spec (.of T))).image_of_isOpenImmersion a)
      (isAffineOpen_top (Spec (.of T))) (a.preimage_image_eq ⊤).ge
    simpa only [actualAffineChartOpen181, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv] using ht
  calc
    _ = Spec.map (Scheme.ΓSpecIso (.of T)).hom ≫
        (Spec.map (a.appIso ⊤).hom ≫ (actualAffineChartOpen181 a).2.fromSpec) := by
      change Spec.map ((a.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (.of T)).hom) ≫
        (actualAffineChartOpen181 a).2.fromSpec = _
      rw [Spec.map_comp, Category.assoc]
    _ = Spec.map (Scheme.ΓSpecIso (.of T)).hom ≫
        (Spec.map (Scheme.ΓSpecIso (.of T)).inv ≫ a) :=
      congrArg (fun k => Spec.map (Scheme.ΓSpecIso (.of T)).hom ≫ k) h
    _ = a := by
      rw [← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
        Spec.map_id, Category.id_comp]

/-- The ACTUAL chart coordinate equivalence preserves every ORIGINAL
family scalar; the caller supplies only the actual chart's base equation. -/
lemma actualAffineChartCoordinates181_scalar
    {S T : Type u} [CommRing S] [CommRing T] {X : Scheme.{u}}
    (F : X ⟶ Spec (.of S)) (a : Spec (.of T) ⟶ X) [IsOpenImmersion a]
    (alpha : S →+* T) (ha : a ≫ F = Spec.map (CommRingCat.ofHom alpha)) :
    (actualAffineChartCoordinates181 a).toRingHom.comp
      (familySpecChartRingMap171 F (actualAffineChartOpen181 a)) = alpha := by
  have hs : Spec.map (CommRingCat.ofHom
      ((actualAffineChartCoordinates181 a).toRingHom.comp
        (familySpecChartRingMap171 F (actualAffineChartOpen181 a)))) =
      Spec.map (CommRingCat.ofHom alpha) := by
    change Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 F (actualAffineChartOpen181 a)) ≫
      CommRingCat.ofHom (actualAffineChartCoordinates181 a).toRingHom) = _
    rw [Spec.map_comp, familySpecChartRingMap171_spec, ← Category.assoc,
      actualAffineChartCoordinates181_spec, ha]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)

end PfaffianDescent
