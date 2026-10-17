import PfaffianDescent.OpenFamilyFiberTransport171
import PfaffianDescent.AffineBaseFiberStalkReduction170
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! SOURCE ONLY / UNVERIFIED171. The ORIGINAL family X -> Spec B, its
ACTUAL base-ideal fiber, and its ACTUAL stalk reduction. Affine charts are
constructed internally; no kernel, flatness or regularity premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma familySpecMap_from_appTop171
    {B A : Type u} [CommRing B] [CommRing A]
    (h : Spec (.of A) ⟶ Spec (.of B)) :
    Spec.map (CommRingCat.ofHom
      (((Scheme.ΓSpecIso (.of B)).inv ≫ h.appTop ≫
        (Scheme.ΓSpecIso (.of A)).hom).hom)) = h := by
  change Spec.map ((Scheme.ΓSpecIso (.of B)).inv ≫ h.appTop ≫
    (Scheme.ΓSpecIso (.of A)).hom) = h
  rw [Spec.map_comp, Spec.map_comp, SpecMap_ΓSpecIso_hom,
    ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

def familySpecChartRingMap171
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (U : X.affineOpens) : B →+* Γ(X, U.1) :=
  ((Scheme.ΓSpecIso (.of B)).inv ≫ (U.2.fromSpec ≫ f).appTop ≫
    (Scheme.ΓSpecIso Γ(X, U.1)).hom).hom

lemma familySpecChartRingMap171_spec
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U)) = U.2.fromSpec ≫ f :=
  familySpecMap_from_appTop171 (U.2.fromSpec ≫ f)

/-- The actual affine fiber maps to the ORIGINAL global fiber, retaining
both projections; this is not a chosen isomorphism of abstract quotients. -/
def familySpecChartFiberToOriginal171
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B) (U : X.affineOpens) :
    pullback (Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  let g := Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  refine pullback.lift (pullback.fst g q ≫ U.2.fromSpec) (pullback.snd g q) ?_
  rw [Category.assoc, ← familySpecChartRingMap171_spec f U]
  exact pullback.condition

lemma familySpecChartFiberToOriginal171_toAmbient
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B) (U : X.affineOpens) :
    familySpecChartFiberToOriginal171 f I U ≫
      pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
    pullback.fst (Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ U.2.fromSpec := by
  simp only [familySpecChartFiberToOriginal171, pullback.lift_fst]

lemma familySpecChartFiberToOriginal171_toBase
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B) (U : X.affineOpens) :
    familySpecChartFiberToOriginal171 f I U ≫
      pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
    pullback.snd (Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  simp only [familySpecChartFiberToOriginal171, pullback.lift_snd]

lemma familySpecChartFiberToOriginal171_isPullback
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B) (U : X.affineOpens) :
    IsPullback
      (pullback.fst (Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
      (familySpecChartFiberToOriginal171 f I U) U.2.fromSpec
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  let g := Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hs : IsPullback (pullback.fst g q) (pullback.snd g q)
      (U.2.fromSpec ≫ f) q := by
    rw [← familySpecChartRingMap171_spec f U]
    exact IsPullback.of_hasPullback g q
  apply IsPullback.of_bot (v₂₁ := pullback.snd f q) (v₂₂ := f)
  · rw [familySpecChartFiberToOriginal171_toBase]
    exact hs
  · exact (familySpecChartFiberToOriginal171_toAmbient f I U).symm
  · exact IsPullback.of_hasPullback f q

/-- The whole ORIGINAL fiber ideal, after its ACTUAL chart stalk map,
is precisely the extension of the original base ideal. -/
lemma familySpecChartFiberIdeal_map171
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B) (U : X.affineOpens)
    (w : ↥(pullback (Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    let a := U.2.fromSpec
    let j := pullback.fst (Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    let V : X.affineOpens := ⟨a ''ᵁ ⊤,
      (isAffineOpen_top _).image_of_isOpenImmersion a⟩
    ((i.ker.ideal V).map
      (X.presheaf.germ V.1 (a (j w)) ⟨j w, trivial, rfl⟩).hom).map
        (a.stalkMap (j w)).hom =
      I.map (familyBaseToStalk169 (a ≫ f) (j w)) := by
  let a := U.2.fromSpec
  let g := Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let j := pullback.fst g q
  let i := pullback.fst f q
  let W : (Spec Γ(X, U.1)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let V : X.affineOpens := ⟨a ''ᵁ ⊤,
    (isAffineOpen_top _).image_of_isOpenImmersion a⟩
  letI : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  calc
    _ = (j.ker.ideal W).map
        ((Spec Γ(X, U.1)).presheaf.germ ⊤ (j w) (by trivial)).hom :=
      (openClosedFiberIdeal_map171 i j (familySpecChartFiberToOriginal171 f I U)
        a (familySpecChartFiberToOriginal171_isPullback f I U) (j w)).symm
    _ = RingHom.ker (j.stalkMap w).hom :=
      cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel
        j W w (by trivial)
    _ = I.map (familyBaseToStalk169 g (j w)) :=
      affineBaseFiberStalkReduction170_ker (familySpecChartRingMap171 f U) I w
    _ = _ := congrArg
      (fun h : Spec Γ(X, U.1) ⟶ Spec (.of B) => I.map (familyBaseToStalk169 h (j w)))
      (familySpecChartRingMap171_spec f U)

/-- Reflect through the actual open-immersion stalk isomorphism: the
original global fiber ideal germ itself is the extended base ideal. -/
lemma familySpecChartFiberIdeal_eq171
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B) (U : X.affineOpens)
    (w : ↥(pullback (Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    let a := U.2.fromSpec
    let j := pullback.fst (Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    let V : X.affineOpens := ⟨a ''ᵁ ⊤,
      (isAffineOpen_top _).image_of_isOpenImmersion a⟩
    (i.ker.ideal V).map
      (X.presheaf.germ V.1 (a (j w)) ⟨j w, trivial, rfl⟩).hom =
      I.map (familyBaseToStalk169 f (a (j w))) := by
  let a := U.2.fromSpec
  let g := Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let j := pullback.fst g q
  let i := pullback.fst f q
  let V : X.affineOpens := ⟨a ''ᵁ ⊤,
    (isAffineOpen_top _).image_of_isOpenImmersion a⟩
  let phi := (a.stalkMap (j w)).hom
  apply (Ideal.relIsoOfBijective phi
    (ConcreteCategory.bijective_of_isIso (a.stalkMap (j w)))).symm.injective
  change ((i.ker.ideal V).map
      (X.presheaf.germ V.1 (a (j w)) ⟨j w, trivial, rfl⟩).hom).map phi =
    (I.map (familyBaseToStalk169 f (a (j w)))).map phi
  calc
    _ = I.map (familyBaseToStalk169 (a ≫ f) (j w)) :=
      familySpecChartFiberIdeal_map171 f I U w
    _ = _ := (familyBaseIdeal_map171 f a I (j w)).symm

def familyFiberStalkReduction171
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B)
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    X.presheaf.stalk (i z) →+*
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).presheaf.stalk z :=
  ((pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).stalkMap z).hom

lemma familyFiberStalkReduction171_surjective
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B)
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    Function.Surjective (familyFiberStalkReduction171 f I z) := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).stalkMap_surjective z

lemma familyFiberStalkReduction171_ker_at_chart
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B) (U : X.affineOpens)
    (w : ↥(pullback (Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    let z := familySpecChartFiberToOriginal171 f I U w
    RingHom.ker (familyFiberStalkReduction171 f I z) =
      I.map (familyBaseToStalk169 f (i z)) := by
  let a := U.2.fromSpec
  let g := Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let j := pullback.fst g q
  let i := pullback.fst f q
  let b := familySpecChartFiberToOriginal171 f I U
  let V : X.affineOpens := ⟨a ''ᵁ ⊤,
    (isAffineOpen_top _).image_of_isOpenImmersion a⟩
  letI : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hx : a (j w) = i (b w) := by
    change (j ≫ a) w = (b ≫ i) w
    exact congrArg (fun h : (pullback g q : Scheme.{u}) ⟶ X => h w)
      (familySpecChartFiberToOriginal171_toAmbient f I U).symm
  have hz : i (b w) ∈ V.1 := hx ▸ ⟨j w, trivial, rfl⟩
  change RingHom.ker (i.stalkMap (b w)).hom = _
  rw [← cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel i V (b w) hz]
  have hpoint (x : X) (he : x = a (j w)) (hmem : x ∈ V.1) :
      (i.ker.ideal V).map (X.presheaf.germ V.1 x hmem).hom =
        I.map (familyBaseToStalk169 f x) := by
    subst x
    exact familySpecChartFiberIdeal_eq171 f I U w
  exact hpoint (i (b w)) hx.symm hz

/-- Every point of the original fiber comes from one of the actual affine
chart fibers. The chart and its point are constructed using the affine
basis and native pullback carrier theorem, not supplied as a certificate. -/
lemma familyFiberPoint_from_chart171
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B)
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    ∃ (U : X.affineOpens)
      (w : ↥(pullback (Spec.map (CommRingCat.ofHom (familySpecChartRingMap171 f U)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})),
      familySpecChartFiberToOriginal171 f I U w = z := by
  let i := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (i z)) isOpen_univ
  let U : X.affineOpens := ⟨V, hV⟩
  have hx : i z ∈ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    exact hxV
  obtain ⟨x, hx⟩ := hx
  obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback
    (familySpecChartFiberToOriginal171_isPullback f I U) x z hx
  exact ⟨U, w, hw⟩

/-- The WHOLE actual reduction kernel for an arbitrary original family
and arbitrary base ideal, at EVERY actual fiber point. No smoothness,
flatness, Artin/field assumption or kernel identification is an input. -/
lemma familyFiberStalkReduction171_ker
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B)
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    RingHom.ker (familyFiberStalkReduction171 f I z) =
      I.map (familyBaseToStalk169 f (i z)) := by
  obtain ⟨U, w, rfl⟩ := familyFiberPoint_from_chart171 f I z
  exact familyFiberStalkReduction171_ker_at_chart f I U w

/-- The actual original-family fiber stalk, retaining its reduction map,
is the quotient by the extension of the ORIGINAL base ideal. -/
def familyFiberStalkQuotientEquiv171
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B)
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (X.presheaf.stalk (i z) ⧸ I.map (familyBaseToStalk169 f (i z))) ≃+*
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).presheaf.stalk z :=
  (Ideal.quotEquivOfEq (familyFiberStalkReduction171_ker f I z).symm).trans
    ((familyFiberStalkReduction171 f I z).quotientKerEquivOfSurjective
      (familyFiberStalkReduction171_surjective f I z))

lemma familyFiberStalkQuotientEquiv171_mk
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (I : Ideal B)
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u}))
    (a : X.presheaf.stalk
      ((pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z)) :
    familyFiberStalkQuotientEquiv171 f I z (Ideal.Quotient.mk _ a) =
      familyFiberStalkReduction171 f I z a := by
  simp only [familyFiberStalkQuotientEquiv171, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ a

end PfaffianDescent
