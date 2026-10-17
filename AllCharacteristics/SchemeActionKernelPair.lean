import AllCharacteristics.FreeActionAffineKernelPair
import AllCharacteristics.AffineSchemeFreeAction

/-! # The actual group-action map to a quotient kernel pair

The disjoint union of the original action graphs maps to the actual kernel
pair. For the invariant-spectrum quotient of an affine scheme with a free
finite-group action, this map is an isomorphism. The proof transports the
established tensor-square isomorphism along the original affine scheme
comparison and preserves both projections.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v

/-- The disjoint union of the original action graphs in the actual quotient kernel pair. -/
noncomputable def schemeActionKernelPairMap
    {X Y : Scheme.{u}} (G : Type v) [Finite G] [Small.{u} G]
    (ρ : G → (X ⟶ X)) (q : X ⟶ Y) (hq : ∀ g, ρ g ≫ q = q) :
    (∐ fun _ : G => X) ⟶ pullback q q :=
  Sigma.desc (fun g => pullback.lift (𝟙 X) (ρ g) (by rw [Category.id_comp, hq g]))

/-- The first projection on every action-graph component is the identity. -/
lemma schemeActionKernelPairMap_component_fst
    {X Y : Scheme.{u}} (G : Type v) [Finite G] [Small.{u} G]
    (ρ : G → (X ⟶ X)) (q : X ⟶ Y) (hq : ∀ g, ρ g ≫ q = q) (g : G) :
    (Sigma.ι (fun _ : G => X) g ≫ schemeActionKernelPairMap G ρ q hq) ≫
      pullback.fst q q = 𝟙 X := by
  rw [schemeActionKernelPairMap, Sigma.ι_desc, pullback.lift_fst]

/-- The second projection on each component is the original action morphism. -/
lemma schemeActionKernelPairMap_component_snd
    {X Y : Scheme.{u}} (G : Type v) [Finite G] [Small.{u} G]
    (ρ : G → (X ⟶ X)) (q : X ⟶ Y) (hq : ∀ g, ρ g ≫ q = q) (g : G) :
    (Sigma.ι (fun _ : G => X) g ≫ schemeActionKernelPairMap G ρ q hq) ≫
      pullback.snd q q = ρ g := by
  rw [schemeActionKernelPairMap, Sigma.ι_desc, pullback.lift_snd]

/-- The total first projection is the actual constant-cover structure map. -/
lemma schemeActionKernelPairMap_fst
    {X Y : Scheme.{u}} (G : Type v) [Finite G] [Small.{u} G]
    (ρ : G → (X ⟶ X)) (q : X ⟶ Y) (hq : ∀ g, ρ g ≫ q = q) :
    schemeActionKernelPairMap G ρ q hq ≫ pullback.fst q q = Sigma.desc (fun _ : G => 𝟙 X) := by
  apply Sigma.hom_ext
  intro g
  exact (Category.assoc _ _ _).symm.trans
    ((schemeActionKernelPairMap_component_fst G ρ q hq g).trans
      (Sigma.ι_desc (fun _ : G => 𝟙 X) g).symm)

/-- The total second projection is the coproduct of the original action morphisms. -/
lemma schemeActionKernelPairMap_snd
    {X Y : Scheme.{u}} (G : Type v) [Finite G] [Small.{u} G]
    (ρ : G → (X ⟶ X)) (q : X ⟶ Y) (hq : ∀ g, ρ g ≫ q = q) :
    schemeActionKernelPairMap G ρ q hq ≫ pullback.snd q q = Sigma.desc ρ := by
  apply Sigma.hom_ext
  intro g
  exact (Category.assoc _ _ _).symm.trans
    ((schemeActionKernelPairMap_component_snd G ρ q hq g).trans (Sigma.ι_desc ρ g).symm)

/-- For a free finite-group action on an affine scheme, the actual quotient
kernel pair is the disjoint union of its original action graphs. -/
lemma isIso_schemeActionKernelPairMap_affine_of_free
    {X S : Scheme.{u}} [IsAffine X] (G : Type) [Group G] [Finite G]
    (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
    (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
    (f : X ⟶ S) (hf : ∀ g : G, ρ g ≫ f = f)
    (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ X) (g : G),
      g ≠ 1 → a ≫ ρ g ≠ a) :
    IsIso (schemeActionKernelPairMap G ρ (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf)
      (affineSchemeActionQuotientMap_invariant G ρ h₁ hcomp f hf)) := by
  let := Fintype.ofFinite G
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  have hI : ∀ g : G, g ≠ 1 → actionDifferenceIdeal Γ(X, ⊤) G g = ⊤ := by
    intro g hg
    exact actionDifferenceIdeal_eq_top_of_scheme_free G ρ h₁ hcomp g
      (fun K _ a => hfree K a g hg)
  let q : X ⟶ affineInvariantQuotient Γ(S, ⊤) Γ(X, ⊤) G :=
    affineSchemeActionQuotientMap G ρ h₁ hcomp f hf
  let r := affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G
  let e : X ≅ Spec (.of Γ(X, ⊤)) := X.isoSpec
  let j := (Sigma.mapIso (fun _ : G => e)).hom
  let k := pullback.map q q r r e.hom e.hom (𝟙 _)
    (Category.comp_id q)
    (Category.comp_id q)
  let m := schemeActionKernelPairMap G ρ q (affineSchemeActionQuotientMap_invariant G ρ h₁ hcomp f hf)
  let m' := affineInvariantKernelPairMap Γ(S, ⊤) Γ(X, ⊤) G
  have : IsIso m' := isIso_affineInvariantKernelPairMap_of_free Γ(S, ⊤) Γ(X, ⊤) G hI
  have : IsIso k := pullback.map_isIso q q r r e.hom e.hom (𝟙 _)
    (Category.comp_id q)
    (Category.comp_id q)
  have : IsIso j := inferInstance
  have hc : m ≫ k = j ≫ m' := by
    apply Sigma.hom_ext
    intro g
    have hj : Sigma.ι (fun _ : G => X) g ≫ j =
        e.hom ≫ Sigma.ι (fun _ : G => Spec (.of Γ(X, ⊤))) g :=
      Sigma.ι_mapIso_hom (fun _ : G => e) g
    apply pullback.hom_ext
    · have hk : k ≫ pullback.fst r r = pullback.fst q q ≫ e.hom := pullback.lift_fst _ _ _
      have hm : (Sigma.ι (fun _ : G => X) g ≫ m) ≫ pullback.fst q q = 𝟙 X :=
        schemeActionKernelPairMap_component_fst G ρ q _ g
      have hm' : (Sigma.ι (fun _ : G => Spec (.of Γ(X, ⊤))) g ≫ m') ≫
          pullback.fst r r = 𝟙 _ := affineInvariantKernelPairMap_component_fst _ _ _ g
      simp only [Category.assoc]
      rw [hk, ← Category.assoc, ← Category.assoc, hm, Category.id_comp,
        ← Category.assoc, hj, Category.assoc,
        ← Category.assoc (Sigma.ι (fun _ : G => Spec (.of Γ(X, ⊤))) g) m' (pullback.fst r r),
        hm', Category.comp_id]
    · have hk : k ≫ pullback.snd r r = pullback.snd q q ≫ e.hom := pullback.lift_snd _ _ _
      have hm : (Sigma.ι (fun _ : G => X) g ≫ m) ≫ pullback.snd q q = ρ g :=
        schemeActionKernelPairMap_component_snd G ρ q _ g
      have hm' : (Sigma.ι (fun _ : G => Spec (.of Γ(X, ⊤))) g ≫ m') ≫
          pullback.snd r r = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G Γ(X, ⊤) g)) :=
        affineInvariantKernelPairMap_component_snd _ _ _ g
      simp only [Category.assoc]
      rw [hk, ← Category.assoc, ← Category.assoc, hm,
        ← Category.assoc, hj, Category.assoc,
        ← Category.assoc (Sigma.ι (fun _ : G => Spec (.of Γ(X, ⊤))) g) m' (pullback.snd r r), hm']
      exact (Scheme.isoSpec_hom_naturality (ρ g)).symm
  have : IsIso (m ≫ k) := hc.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right m k

end AllCharacteristics
