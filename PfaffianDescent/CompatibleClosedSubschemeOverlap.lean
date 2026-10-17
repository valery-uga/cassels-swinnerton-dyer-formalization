import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace PfaffianDescent

/-- Factoring one projection through a monomorphism retains a pullback. -/
theorem isPullback_factor_projection_mono
    {C : Type*} [Category C] {P A B B' T : C}
    {a : P ⟶ A} {b : P ⟶ B'} {k : B' ⟶ B}
    {f : A ⟶ T} {g : B ⟶ T} [Mono k]
    (h : IsPullback a (b ≫ k) f g) :
    IsPullback a b f (k ≫ g) := by
  refine IsPullback.mk' (by simpa only [Category.assoc] using h.w) ?_ ?_
  · intro S v w hv hw
    apply h.hom_ext hv
    simpa only [Category.assoc] using congrArg (fun l => l ≫ k) hw
  · intro S v w hvw
    let l := h.lift v (w ≫ k) (by simpa only [Category.assoc] using hvw)
    refine ⟨l, h.lift_fst _ _ _, ?_⟩
    apply (cancel_mono k).mp
    simpa only [Category.assoc] using h.lift_snd v (w ≫ k) _

/-- Equality of whole ideal sheaves preserves their actual inclusion maps. -/
@[reassoc (attr := simp)]
theorem idealSubscheme_eqToIso_hom_inclusion
    {W : Scheme.{u}} {I J : W.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg (fun L : W.IdealSheafData => L.subscheme) h)).hom ≫
      J.subschemeι = I.subschemeι := by
  cases h
  simp

/-- The canonical comparison of two actual pullback closed subschemes. -/
def compatibleClosedOverlapIso
    {U V W : Scheme.{u}} (I : U.IdealSheafData) (J : V.IdealSheafData)
    (p : W ⟶ U) (q : W ⟶ V) (h : I.comap p = J.comap q) :
    pullback p I.subschemeι ≅ pullback q J.subschemeι :=
  (I.comapIso p).symm ≪≫
    eqToIso (congrArg (fun L : W.IdealSheafData => L.subscheme) h) ≪≫
    J.comapIso q

@[reassoc (attr := simp)]
theorem compatibleClosedOverlapIso_hom_fst
    {U V W : Scheme.{u}} (I : U.IdealSheafData) (J : V.IdealSheafData)
    (p : W ⟶ U) (q : W ⟶ V) (h : I.comap p = J.comap q) :
    (compatibleClosedOverlapIso I J p q h).hom ≫ pullback.fst q J.subschemeι =
      pullback.fst p I.subschemeι := by
  simp only [compatibleClosedOverlapIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [J.comapIso_hom_fst, idealSubscheme_eqToIso_hom_inclusion h]
  exact I.comapIso_inv_subschemeι p

/-- The actual closed subscheme on the ambient intersection. -/
def compatibleClosedOverlap
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    (I : U.IdealSheafData) : Scheme.{u} :=
  (I.comap (pullback.fst f g)).subscheme

/-- Its canonical projection to the first local closed subscheme. -/
def compatibleClosedOverlapLeft
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    (I : U.IdealSheafData) : compatibleClosedOverlap f g I ⟶ I.subscheme :=
  (I.comapIso (pullback.fst f g)).hom ≫
    pullback.snd (pullback.fst f g) I.subschemeι

/-- Its canonical projection to the second local closed subscheme. -/
def compatibleClosedOverlapRight
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    (I : U.IdealSheafData) (J : V.IdealSheafData)
    (h : I.comap (pullback.fst f g) = J.comap (pullback.snd f g)) :
    compatibleClosedOverlap f g I ⟶ J.subscheme :=
  (eqToIso (congrArg (fun L : (pullback f g).IdealSheafData => L.subscheme) h)).hom ≫
    (J.comapIso (pullback.snd f g)).hom ≫
    pullback.snd (pullback.snd f g) J.subschemeι

@[reassoc (attr := simp)]
theorem compatibleClosedOverlapLeft_inclusion
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    (I : U.IdealSheafData) :
    compatibleClosedOverlapLeft f g I ≫ I.subschemeι =
      (I.comap (pullback.fst f g)).subschemeι ≫ pullback.fst f g := by
  dsimp only [compatibleClosedOverlap, compatibleClosedOverlapLeft]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

@[reassoc (attr := simp)]
theorem compatibleClosedOverlapRight_inclusion
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    (I : U.IdealSheafData) (J : V.IdealSheafData)
    (h : I.comap (pullback.fst f g) = J.comap (pullback.snd f g)) :
    compatibleClosedOverlapRight f g I J h ≫ J.subschemeι =
      (I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g := by
  dsimp only [compatibleClosedOverlap, compatibleClosedOverlapRight]
  simp only [Category.assoc]
  rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc,
    ← Category.assoc, idealSubscheme_eqToIso_hom_inclusion h]

/-- The first restriction square is Cartesian by native kernel equality. -/
theorem compatibleClosedOverlapLeft_isPullback
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    (I : U.IdealSheafData) :
    IsPullback (I.comap (pullback.fst f g)).subschemeι
      (compatibleClosedOverlapLeft f g I) (pullback.fst f g) I.subschemeι := by
  apply isPullback_of_isClosedImmersion
  · exact (compatibleClosedOverlapLeft_inclusion f g I).symm
  · simp

/-- Whole overlap compatibility also makes the second restriction Cartesian. -/
theorem compatibleClosedOverlapRight_isPullback
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    (I : U.IdealSheafData) (J : V.IdealSheafData)
    (h : I.comap (pullback.fst f g) = J.comap (pullback.snd f g)) :
    IsPullback (I.comap (pullback.fst f g)).subschemeι
      (compatibleClosedOverlapRight f g I J h) (pullback.snd f g) J.subschemeι := by
  apply isPullback_of_isClosedImmersion
  · exact (compatibleClosedOverlapRight_inclusion f g I J h).symm
  · simpa using h.symm

/-- The overlap is the actual fiber product of the two local closed subschemes. -/
theorem compatibleClosedOverlap_isPullback
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    (I : U.IdealSheafData) (J : V.IdealSheafData)
    (h : I.comap (pullback.fst f g) = J.comap (pullback.snd f g)) :
    IsPullback (compatibleClosedOverlapLeft f g I)
      (compatibleClosedOverlapRight f g I J h)
      (I.subschemeι ≫ f) (J.subschemeι ≫ g) := by
  have ho := (compatibleClosedOverlapLeft_isPullback f g I).flip.paste_vert
    (IsPullback.of_hasPullback f g)
  rw [← compatibleClosedOverlapRight_inclusion f g I J h] at ho
  exact isPullback_factor_projection_mono ho

/-- Compatible local closed subschemes have open overlap projections. -/
theorem compatibleClosedSubscheme_pullback_fst_isOpenImmersion
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (I : U.IdealSheafData) (J : V.IdealSheafData)
    (h : I.comap (pullback.fst f g) = J.comap (pullback.snd f g)) :
    IsOpenImmersion (pullback.fst (I.subschemeι ≫ f) (J.subschemeι ≫ g)) := by
  let hp := compatibleClosedOverlap_isPullback f g I J h
  haveI : IsOpenImmersion (compatibleClosedOverlapLeft f g I) := by
    haveI : IsOpenImmersion (pullback.fst f g) := inferInstance
    haveI : IsOpenImmersion ((I.comapIso (pullback.fst f g)).hom) := inferInstance
    haveI : IsOpenImmersion (pullback.snd (pullback.fst f g) I.subschemeι) := inferInstance
    exact IsOpenImmersion.comp (I.comapIso (pullback.fst f g)).hom
      (pullback.snd (pullback.fst f g) I.subschemeι)
  rw [← hp.isoPullback_inv_fst]
  infer_instance

/-- Ordinary range formula, proved before introducing any concrete overlap. -/
private theorem schemePullback_range_snd004
    {P A B T : Scheme.{u}} {a : P ⟶ A} {b : P ⟶ B}
    {f : A ⟶ T} {g : B ⟶ T} (h : IsPullback a b f g) :
    Set.range b = g ⁻¹' Set.range f := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨a z, ?_⟩
    exact congrArg (fun l : P ⟶ T => l z) h.w
  · rintro ⟨x, hxy⟩
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback h x y hxy
    exact ⟨z, hz⟩

/-- The range does not change under precomposition by a genuine Iso. -/
private theorem schemeIso_precomp_range004
    {A B T : Scheme.{u}} (e : A ≅ B) (f : B ⟶ T) :
    Set.range (e.hom ≫ f) = Set.range f := by
  change Set.range (f.base ∘ e.hom.base) = Set.range f.base
  exact (ConcreteCategory.bijective_of_isIso e.hom.base).surjective.range_comp _

/-- Separate the actual right restriction/pasting certificate from its
underlying topological range computation. -/
private theorem compatibleClosedOverlapRight_toAmbient_isPullback004
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    (I : U.IdealSheafData) (J : V.IdealSheafData)
    (h : I.comap (pullback.fst f g) = J.comap (pullback.snd f g)) :
    IsPullback ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.fst f g)
      (compatibleClosedOverlapRight f g I J h) f (J.subschemeι ≫ g) :=
  (compatibleClosedOverlapRight_isPullback f g I J h).paste_horiz
    (IsPullback.of_hasPullback f g)

/-- Actual right-overlap range, with no native Iso in this proof context. -/
private theorem compatibleClosedOverlapRight_range004
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    (I : U.IdealSheafData) (J : V.IdealSheafData)
    (h : I.comap (pullback.fst f g) = J.comap (pullback.snd f g)) :
    Set.range (compatibleClosedOverlapRight f g I J h) =
      (J.subschemeι ≫ g) ⁻¹' Set.range f :=
  schemePullback_range_snd004 (compatibleClosedOverlapRight_toAmbient_isPullback004 f g I J h)

/-- Saturation on an ambient overlap follows from the whole ideal equality;
this is stronger than merely knowing that both closed schemes map to X. -/
theorem compatibleClosedSubscheme_pullback_snd_range
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X)
    (I : U.IdealSheafData) (J : V.IdealSheafData)
    (h : I.comap (pullback.fst f g) = J.comap (pullback.snd f g)) :
    Set.range (pullback.snd (I.subschemeι ≫ f) (J.subschemeι ≫ g)) =
      (J.subschemeι ≫ g) ⁻¹' Set.range f := by
  let hp := compatibleClosedOverlap_isPullback f g I J h
  calc
    _ = Set.range (hp.isoPullback.inv ≫ compatibleClosedOverlapRight f g I J h) :=
      congrArg (fun l : pullback (I.subschemeι ≫ f) (J.subschemeι ≫ g) ⟶
        J.subscheme => Set.range l) hp.isoPullback_inv_snd.symm
    _ = Set.range (compatibleClosedOverlapRight f g I J h) :=
      schemeIso_precomp_range004 hp.isoPullback.symm (compatibleClosedOverlapRight f g I J h)
    _ = (J.subschemeι ≫ g) ⁻¹' Set.range f :=
      compatibleClosedOverlapRight_range004 f g I J h

end PfaffianDescent
end
