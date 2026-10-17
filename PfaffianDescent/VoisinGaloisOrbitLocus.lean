import PfaffianDescent.GaloisConjugates
import PfaffianDescent.SerreExtensionFoundation
import PfaffianDescent.LocalSerreExtensionPresentation

namespace PfaffianDescent

open CategoryTheory AlgebraicGeometry

universe u

section
variable {K A L : Type u} [Field K] [Field A] [Algebra K A]
    [Field L] [Algebra K L]

/-- The unique closed point of the spectrum of a local ring, with its type
made explicit as a point of the scheme `Spec R`. -/
noncomputable def specClosedPoint (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec (.of R) := by
  change PrimeSpectrum R
  exact IsLocalRing.closedPoint R

/-- A geometric point of the orbit of a finite field-valued point, viewed on
the original surface.  An embedding `A →ₐ[K] L` gives a map
`Spec L → Spec A`; composing it with the given `A`-point and evaluating at
the closed point of `Spec L` gives the corresponding surface point. -/
noncomputable def galoisEmbeddingPoint {X : Scheme.{u}} (x : Spec (.of A) ⟶ X) :
    (A →ₐ[K] L) → X := fun φ ↦
  (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ x) (specClosedPoint L)

/-- Before base change, every geometric point in the embedding orbit lies
over the one closed point defined by the field-valued point. -/
theorem galoisEmbeddingPoint_eq_closedPoint
    {X : Scheme.{u}} (x : Spec (.of A) ⟶ X) (φ : A →ₐ[K] L) :
    galoisEmbeddingPoint (K := K) x φ =
      x (specClosedPoint A) := by
  unfold galoisEmbeddingPoint
  rw [Scheme.Hom.comp_apply]
  congr 1
  change Spec.map (CommRingCat.ofHom φ.toRingHom)
      (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint A
  exact AlgebraicGeometry.Spec_closedPoint

/-- Hence the image of any Galois-stable bad orbit is contained in the
underlying closed point of the finite subscheme.  This is the concrete
surface-point map used by the local-free cover construction. -/
theorem galoisEmbeddingPoint_image_subset_closedPoint
    {X : Scheme.{u}} (x : Spec (.of A) ⟶ X) (B : Set (A →ₐ[K] L)) :
    galoisEmbeddingPoint (K := K) x '' B ⊆
      {x (specClosedPoint A)} := by
  rintro y ⟨φ, hφ, rfl⟩
  rw [galoisEmbeddingPoint_eq_closedPoint]
  rfl

/-- A nonempty embedding orbit has exactly the closed-point image.  The
`⊆` direction is the scheme-theoretic calculation above; the reverse
inclusion only uses one embedding in the orbit.  This is the form needed
when an orbit-indexed bad locus is converted into a subset of the surface. -/
theorem galoisEmbeddingPoint_image_eq_closedPoint_of_nonempty
    {X : Scheme.{u}} (x : Spec (.of A) ⟶ X)
    {B : Set (A →ₐ[K] L)} (hB : B.Nonempty) :
    galoisEmbeddingPoint (K := K) x '' B =
      {x (specClosedPoint A)} := by
  apply Set.Subset.antisymm
  · exact galoisEmbeddingPoint_image_subset_closedPoint x B
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    obtain ⟨φ, hφ⟩ := hB
    refine ⟨φ, hφ, ?_⟩
    rw [galoisEmbeddingPoint_eq_closedPoint]
    exact hy.symm

/-- The Galois group of `L/K` acts on `K`-algebra embeddings into `L` by
postcomposition. -/
@[instance_reducible]
noncomputable def galoisEmbeddingAction :
    MulAction (L ≃ₐ[K] L) (A →ₐ[K] L) where
  smul σ φ := σ.toAlgHom.comp φ
  one_smul φ := by
    ext a
    rfl
  mul_smul σ τ φ := by
    ext a
    rfl

/-- When `L/K` is normal, its Galois action on the embeddings of `A` into
`L` is transitive. -/
theorem galoisEmbeddingAction_isPretransitive [Normal K L] :
    @MulAction.IsPretransitive (L ≃ₐ[K] L) (A →ₐ[K] L)
      (galoisEmbeddingAction (K := K) (A := A) (L := L)).toSMul := by
  refine @MulAction.IsPretransitive.mk (L ≃ₐ[K] L) (A →ₐ[K] L)
    (galoisEmbeddingAction (K := K) (A := A) (L := L)).toSMul ?_
  intro φ ψ
  obtain ⟨σ, hσ⟩ := embeddings_normal_transitive φ ψ
  refine ⟨σ, ?_⟩
  ext a
  exact hσ a

/-- A stable nonempty Galois bad locus is the whole embedding orbit.  This is
the pretransitivity half of Voisin's dichotomy, stated before the local-Ext
vanishing is applied. -/
theorem galoisEmbedding_badLocus_eq_univ_of_stable_nonempty
    [Normal K L] (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (hB : B.Nonempty) :
    B = Set.univ := by
  obtain hempty | huniv :=
    @invariant_subset_eq_empty_or_univ_of_pretransitive
      (L ≃ₐ[K] L) (A →ₐ[K] L)
      _ (galoisEmbeddingAction (K := K) (A := A) (L := L))
      (galoisEmbeddingAction_isPretransitive (K := K) (A := A) (L := L))
      B (by
        intro σ φ hφ
        exact hstable σ φ hφ)
  · exact False.elim ((Set.nonempty_iff_ne_empty.mp hB) hempty)
  · exact huniv

/-- Voisin's Galois-orbit local-freeness argument, specialized to the actual
orbit of embeddings of a finite closed point into a normal splitting field.

The hypotheses about `restriction` are the remaining local-Ext computation:
the restriction is injective and vanishes if every conjugate point were bad.
The conclusion is that no conjugate point is bad. -/
theorem galoisEmbedding_badLocus_eq_empty
    [Normal K L] {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (e : V) (restriction : V →+ W) (hinjective : Function.Injective restriction)
    (hne : e ≠ 0)
    (hvanishes : B = Set.univ → restriction e = 0) :
    B = ∅ := by
  apply @invariant_badLocus_eq_empty_of_pretransitive
    (L ≃ₐ[K] L) (A →ₐ[K] L) V W
    _ (galoisEmbeddingAction (K := K) (A := A) (L := L))
    (galoisEmbeddingAction_isPretransitive (K := K) (A := A) (L := L)) _ _
    B ?_ e restriction hinjective hne hvanishes
  intro σ φ hφ
  exact hstable σ φ hφ

/-- Componentwise form of Voisin's Galois-orbit local-freeness argument.
Here `components φ` is the local-Ext component at the geometric point indexed
by `φ`.  Thus the remaining geometric part of Lemma 3.1 is exactly the proof
that a non-locally-free point makes this component zero, together with the
fact that these components detect the global connecting class. -/
theorem galoisEmbedding_badLocus_eq_empty_of_pointwise_vanishing
    [Normal K L] {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    {W' : (A →ₐ[K] L) → Type*} [∀ φ, AddCommMonoid (W' φ)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (e : V) (restriction : V →+ W) (hinjective : Function.Injective restriction)
    (hne : e ≠ 0) (components : ∀ φ, W →+ W' φ)
    (hcomponents : ∀ w : W, (∀ φ, components φ w = 0) → w = 0)
    (hbad : ∀ φ, φ ∈ B → components φ (restriction e) = 0) :
    B = ∅ := by
  apply @invariant_badLocus_eq_empty_of_pretransitive_of_pointwise_vanishing
    (L ≃ₐ[K] L) (A →ₐ[K] L) V W
    _ (galoisEmbeddingAction (K := K) (A := A) (L := L))
    (galoisEmbeddingAction_isPretransitive (K := K) (A := A) (L := L)) _ _ W' _
    B ?_ e restriction hinjective hne components hcomponents hbad
  intro σ φ hφ
  exact hstable σ φ hφ

end
end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Abelian

section TwistedIdeal

variable {K A L : Type u} [Field K] [Field A] [Algebra K A]
    [Field L] [Algebra K L] [Normal K L]

/-- The Galois-orbit local-freeness conclusion for the actual Ext group of a
Voisin twisted ideal sheaf.

The local calculation still needed from Serre duality is isolated in
`hvanishes`: if every conjugate point were non-locally-free, the connecting
local-Ext class would vanish.  Injectivity of that connecting map and the
Galois orbit are supplied here. -/
theorem galoisEmbedding_badLocus_eq_empty_of_twistedIdealExt
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (Y : X.Modules)
    [HasExt.{u} (X.Modules)]
    [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂ Y 1)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (e : Ext.{u} (closedImmersionIdealTwist i T) Y 1) (hne : e ≠ 0)
    (hvanishes : B = Set.univ →
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp e
        (show 1 + 1 = 2 by omega) = 0) :
    B = ∅ := by
  exact galoisEmbedding_badLocus_eq_empty B hstable e
    ((closedImmersionIdealTwistSequence_shortExact i T).extClass.precomp Y
      (show 1 + 1 = 2 by omega))
    (closedImmersionIdealTwist_connectingExtOne_injective i T Y) hne hvanishes

/-- Pointwise local-Ext form of the twisted-ideal Galois argument.  The
components are intended to be the local components of the connecting `Ext²`
class at the geometric points of the finite subscheme.  This is exactly the
remaining local input in Voisin's proof: non-local-freeness at `φ` kills that
component, and the components jointly detect a global class. -/
theorem galoisEmbedding_badLocus_eq_empty_of_twistedIdealExt_of_shortExact_of_pointwise_vanishing
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (Y : X.Modules)
    (hS : (closedImmersionIdealTwistSequence i T).ShortExact)
    [HasExt.{u} (X.Modules)]
    [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂ Y 1)]
    {W' : (A →ₐ[K] L) → Type*} [∀ φ, AddCommMonoid (W' φ)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (e : Ext.{u} (closedImmersionIdealTwist i T) Y 1) (hne : e ≠ 0)
    (components : ∀ φ, Ext.{u} (closedImmersionIdealTwistSequence i T).X₃ Y 2 →+ W' φ)
    (hcomponents : ∀ z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃ Y 2,
      (∀ φ, components φ z = 0) → z = 0)
    (hbad : ∀ φ, φ ∈ B →
      components φ (hS.extClass.comp e (show 1 + 1 = 2 by omega)) = 0) :
    B = ∅ := by
  exact galoisEmbedding_badLocus_eq_empty_of_pointwise_vanishing B hstable e
    (hS.extClass.precomp Y (show 1 + 1 = 2 by omega))
    (ext_one_connecting_injective_of_middle_ext_one_subsingleton hS Y) hne
    components hcomponents hbad

/-- Pointwise local-Ext form with exactness supplied directly.  This is the
local-trivialization-friendly version of the theorem below: it does not ask
the tensor functor to preserve every finite limit and colimit globally. -/
theorem galoisEmbedding_badLocus_eq_empty_of_twistedIdealExt_of_pointwise_vanishing
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (Y : X.Modules)
    [HasExt.{u} (X.Modules)]
    [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂ Y 1)]
    {W' : (A →ₐ[K] L) → Type*} [∀ φ, AddCommMonoid (W' φ)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (e : Ext.{u} (closedImmersionIdealTwist i T) Y 1) (hne : e ≠ 0)
    (components : ∀ φ, Ext.{u} (closedImmersionIdealTwistSequence i T).X₃ Y 2 →+ W' φ)
    (hcomponents : ∀ z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃ Y 2,
      (∀ φ, components φ z = 0) → z = 0)
    (hbad : ∀ φ, φ ∈ B →
      components φ ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp e
        (show 1 + 1 = 2 by omega)) = 0) :
    B = ∅ := by
  exact
    galoisEmbedding_badLocus_eq_empty_of_twistedIdealExt_of_shortExact_of_pointwise_vanishing
      i T Y (closedImmersionIdealTwistSequence_shortExact i T)
      B hstable e hne components hcomponents hbad

/-- The same Galois conclusion with the middle vanishing stated for the
actual twist `T`.  The tensor-unit identification in the ideal sequence is
handled by `closedImmersionIdealTwist_connectingExtOne_injective_of_ext_one_subsingleton`. -/
theorem galoisEmbedding_badLocus_eq_empty_of_twistedIdealExt_of_ext_one_subsingleton
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (Y : X.Modules)
    [HasExt.{u} (X.Modules)]
    [Subsingleton (Ext.{u} (show X.Modules from T) Y 1)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (e : Ext.{u} (closedImmersionIdealTwist i T) Y 1) (hne : e ≠ 0)
    (hvanishes : B = Set.univ →
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp e
        (show 1 + 1 = 2 by omega) = 0) :
    B = ∅ := by
  exact galoisEmbedding_badLocus_eq_empty B hstable e
    ((closedImmersionIdealTwistSequence_shortExact i T).extClass.precomp Y
      (show 1 + 1 = 2 by omega))
    (closedImmersionIdealTwist_connectingExtOne_injective_of_ext_one_subsingleton i T Y)
    hne hvanishes

end TwistedIdeal
end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Abelian

universe u

section SerreExtensionClass

/-- View a Serre extension class in the scheme-module category.

`SerreExtensionData.extensionClass` is defined with the underlying
`SheafOfModules` category, while the closed-immersion ideal sequence is
formulated through the abbreviation `X.Modules`.  This definition fixes the
latter presentation explicitly, so its class can be used with the local-Ext
and Galois results below without relying on typeclass unfolding. -/
noncomputable def serreExtensionClassInSchemeModules
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (e : SerreExtensionData X (closedImmersionIdealTwist i T))
    [hExt : HasExt.{u} (X.Modules)] :
    Ext.{u} (closedImmersionIdealTwist i T)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1 :=
  @SerreExtensionData.extensionClass X (closedImmersionIdealTwist i T) e (by exact hExt)

/-- Identifying the connecting image of a Serre extension class with a
nonzero local degree-two class proves that the extension class itself is
nonzero. This is the direct bridge from the Ext lift in Serre's construction
to the Galois-orbit local-freeness argument. -/
theorem serreExtensionClassInSchemeModules_ne_zero_of_connecting_eq_nonzero
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (e : SerreExtensionData X (closedImmersionIdealTwist i T))
    [HasExt.{u} (X.Modules)]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
    (hz : z ≠ 0)
    (hconnecting :
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = z) :
    serreExtensionClassInSchemeModules i T e ≠ 0 := by
  intro he
  apply hz
  rw [← hconnecting, he]
  exact Ext.comp_zero _ _ _ _ _

/-- View the class of an extension sequence in the scheme-module category
before local freeness of its middle term has been established.  This is the
class produced by the Serre-duality step to which Voisin applies the Galois
orbit argument. -/
noncomputable def serreExtensionSequenceClassInSchemeModules
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    [hExt : HasExt.{u} (X.Modules)] :
    Ext.{u} (closedImmersionIdealTwist i T)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1 :=
  @SerreExtensionSequenceData.extensionClass X (closedImmersionIdealTwist i T) e
    (by exact hExt)

/-- The sequence-level class agrees with the ordinary Serre class after
local freeness has been established. -/
@[simp]
theorem serreExtensionSequenceClassInSchemeModules_toSequenceData
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (e : SerreExtensionData X (closedImmersionIdealTwist i T))
    [HasExt.{u} (X.Modules)] :
    serreExtensionSequenceClassInSchemeModules i T e.toSequenceData =
      serreExtensionClassInSchemeModules i T e := rfl

/-- A nonzero connecting image makes the class of an extension sequence
nonzero, without assuming its middle term is already locally free. -/
theorem serreExtensionSequenceClassInSchemeModules_ne_zero_of_connecting_eq_nonzero
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    [HasExt.{u} (X.Modules)]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
    (hz : z ≠ 0)
    (hconnecting :
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = z) :
    serreExtensionSequenceClassInSchemeModules i T e ≠ 0 := by
  intro he
  apply hz
  rw [← hconnecting, he]
  exact Ext.comp_zero _ _ _ _ _

end SerreExtensionClass

section GaloisLocalFreeness

variable {K A L : Type u} [Field K] [Field A] [Algebra K A]
    [Field L] [Algebra K L] [Normal K L]
variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (e : SerreExtensionData X (closedImmersionIdealTwist i T))
    [HasExt.{u} (X.Modules)]
    [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)]

/-- The Galois local-freeness conclusion for the class of an actual Serre
extension of `I_Z ⊗ T`.

The remaining geometric local calculation is exactly `hvanishes`: if every
conjugate point were bad, it would kill the connecting local-Ext class of the
nonzero Serre extension. -/
theorem galoisEmbedding_badLocus_eq_empty_of_serreExtensionClass
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (he : serreExtensionClassInSchemeModules i T e ≠ 0)
    (hvanishes : B = Set.univ →
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = 0) :
    B = ∅ := by
  exact galoisEmbedding_badLocus_eq_empty_of_twistedIdealExt i T
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) B hstable
    (serreExtensionClassInSchemeModules i T e) he hvanishes

/-- The Galois local-freeness conclusion can use the nonzero local
degree-two class directly. Its equality with the connecting image supplies
the nonzero Serre extension class required by the orbit argument. -/
theorem galoisEmbedding_badLocus_eq_empty_of_serreExtensionClass_connecting_eq_nonzero
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
    (hz : z ≠ 0)
    (hconnecting :
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = z)
    (hvanishes : B = Set.univ →
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = 0) :
    B = ∅ := by
  apply galoisEmbedding_badLocus_eq_empty_of_serreExtensionClass i T e B hstable
    (serreExtensionClassInSchemeModules_ne_zero_of_connecting_eq_nonzero
      i T e z hz hconnecting)
  exact hvanishes

omit [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂
  (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)] in
/-- The Galois local-freeness conclusion for a Serre extension, with its
cohomological vanishing hypothesis expressed for the twist itself. -/
theorem galoisEmbedding_badLocus_eq_empty_of_serreExtensionClass_of_ext_one_subsingleton
    [Subsingleton (Ext.{u} (show X.Modules from T)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (he : serreExtensionClassInSchemeModules i T e ≠ 0)
    (hvanishes : B = Set.univ →
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = 0) :
    B = ∅ := by
  exact galoisEmbedding_badLocus_eq_empty_of_twistedIdealExt_of_ext_one_subsingleton i T
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) B hstable
    (serreExtensionClassInSchemeModules i T e) he hvanishes

end GaloisLocalFreeness

section GaloisLocalFreenessSequence

variable {K A L : Type u} [Field K] [Field A] [Algebra K A]
    [Field L] [Algebra K L] [Normal K L]
variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    [HasExt.{u} (X.Modules)]
    [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)]

/-- The Galois orbit argument applies to a Serre extension sequence before
the local-freeness conclusion is available.  This is the non-circular form
of Voisin's Lemma 3.1: a nonzero extension class and the local vanishing
calculation force the bad locus to be empty. -/
theorem galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (he : serreExtensionSequenceClassInSchemeModules i T e ≠ 0)
    (hvanishes : B = Set.univ →
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = 0) :
    B = ∅ := by
  exact galoisEmbedding_badLocus_eq_empty_of_twistedIdealExt i T
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) B hstable
    (serreExtensionSequenceClassInSchemeModules i T e) he hvanishes

/-- Pointwise local-Ext form of the Galois argument for an actual Serre
extension sequence.  It is the form of Lemma 3.1 that feeds directly into
the later locally-free and pencil constructions: a bad embedding kills its
local component of the connecting class. -/
theorem galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_of_pointwise_vanishing
    {W' : (A →ₐ[K] L) → Type*} [∀ φ, AddCommMonoid (W' φ)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (he : serreExtensionSequenceClassInSchemeModules i T e ≠ 0)
    (components : ∀ φ, Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+ W' φ)
    (hcomponents : ∀ z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
      (∀ φ, components φ z = 0) → z = 0)
    (hbad : ∀ φ, φ ∈ B →
      components φ ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega)) = 0) :
    B = ∅ := by
  exact galoisEmbedding_badLocus_eq_empty_of_twistedIdealExt_of_pointwise_vanishing
    i T (show X.Modules from SheafOfModules.unit X.ringCatSheaf) B hstable
    (serreExtensionSequenceClassInSchemeModules i T e) he components hcomponents hbad

/-- The pointwise local-Ext hypothesis in Voisin's Galois argument follows
from the standard local Serre presentation.  At every bad point the middle
term is assumed to identify with the presentation having relation
`(-g, f, -c)`; its non-freeness makes the residue coordinate `c` vanish.

The remaining geometric comparison is to obtain these presentation and
coordinate identifications from the stalks of the actual sheaf extension. -/
theorem galoisEmbedding_badLocus_eq_empty_of_localSerreExtensionPresentations
    {R : (A →ₐ[K] L) → Type u} [∀ φ, CommRing (R φ)] [∀ φ, IsLocalRing (R φ)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (he : serreExtensionSequenceClassInSchemeModules i T e ≠ 0)
    (f g c : ∀ φ, R φ)
    (components : ∀ φ, Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+
        (R φ ⧸ IsLocalRing.maximalIdeal (R φ)))
    (hcomponents : ∀ z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
      (∀ φ, components φ z = 0) → z = 0)
    (hcoordinate : ∀ φ,
      components φ ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (R φ)) (c φ))
    (hbadPresentation : ∀ φ, φ ∈ B →
      ¬ Module.Free (R φ) (localSerreExtensionPresentation (f φ) (g φ) (c φ))) :
    B = ∅ := by
  apply galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_of_pointwise_vanishing
    i T e B hstable he components hcomponents
  intro φ hφ
  rw [hcoordinate φ]
  exact localSerreExtension_coordinate_eq_zero_mod_maximalIdeal_of_not_free
    (f φ) (g φ) (c φ) (hbadPresentation φ hφ)

/-- Stalk-comparison form of the local Serre argument.  Here `E φ` is the
actual local middle module at the point attached to an embedding.  An
equivalence from `E φ` to the standard lci presentation transfers
non-freeness to the coordinate calculation, so the Galois argument no
longer treats non-freeness of a presentation as a substitute for
non-freeness of the actual extension. -/
theorem galoisEmbedding_badLocus_eq_empty_of_localSerreExtensionPresentationEquivs
    {R : (A →ₐ[K] L) → Type u} [∀ φ, CommRing (R φ)] [∀ φ, IsLocalRing (R φ)]
    {E : (A →ₐ[K] L) → Type u} [∀ φ, AddCommGroup (E φ)] [∀ φ, Module (R φ) (E φ)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (he : serreExtensionSequenceClassInSchemeModules i T e ≠ 0)
    (f g c : ∀ φ, R φ)
    (components : ∀ φ, Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+
        (R φ ⧸ IsLocalRing.maximalIdeal (R φ)))
    (hcomponents : ∀ z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
      (∀ φ, components φ z = 0) → z = 0)
    (hcoordinate : ∀ φ,
      components φ ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (R φ)) (c φ))
    (hpresentation : ∀ φ, E φ ≃ₗ[R φ]
      localSerreExtensionPresentation (f φ) (g φ) (c φ))
    (hbad : ∀ φ, φ ∈ B → ¬ Module.Free (R φ) (E φ)) :
    B = ∅ := by
  apply galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_of_pointwise_vanishing
    i T e B hstable he components hcomponents
  intro φ hφ
  rw [hcoordinate φ]
  exact localSerreExtension_coordinate_eq_zero_mod_maximalIdeal_of_not_free_of_linearEquiv
    (f φ) (g φ) (c φ) (hpresentation φ) (hbad φ hφ)

/-- The local presentation theorem often produces an inhabited type of
equivalences rather than a preferred equivalence.  Since the Galois argument
uses the equivalence only propositionally, classical choice converts that
natural output directly into the preceding formulation. -/
theorem galoisEmbedding_badLocus_eq_empty_of_localSerreExtensionPresentationNonempty
    {R : (A →ₐ[K] L) → Type u} [∀ φ, CommRing (R φ)] [∀ φ, IsLocalRing (R φ)]
    {E : (A →ₐ[K] L) → Type u} [∀ φ, AddCommGroup (E φ)] [∀ φ, Module (R φ) (E φ)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (he : serreExtensionSequenceClassInSchemeModules i T e ≠ 0)
    (f g c : ∀ φ, R φ)
    (components : ∀ φ, Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+ 
        (R φ ⧸ IsLocalRing.maximalIdeal (R φ)))
    (hcomponents : ∀ z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
      (∀ φ, components φ z = 0) → z = 0)
    (hcoordinate : ∀ φ,
      components φ ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (R φ)) (c φ))
    (hpresentation : ∀ φ, Nonempty (E φ ≃ₗ[R φ]
      localSerreExtensionPresentation (f φ) (g φ) (c φ)))
    (hbad : ∀ φ, φ ∈ B → ¬ Module.Free (R φ) (E φ)) :
    B = ∅ := by
  apply galoisEmbedding_badLocus_eq_empty_of_localSerreExtensionPresentationEquivs
    (R := R) (E := E) (i := i) (T := T) (e := e) B hstable he f g c components
      hcomponents hcoordinate
  · intro φ
    exact Classical.choice (hpresentation φ)
  · exact hbad

/-- The same conclusion follows directly from the nonzero local degree-two
class selected by Serre duality. -/
theorem galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_connecting_eq_nonzero
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
    (hz : z ≠ 0)
    (hconnecting :
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = z)
    (hvanishes : B = Set.univ →
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = 0) :
    B = ∅ := by
  apply galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass
    i T e B hstable
    (serreExtensionSequenceClassInSchemeModules_ne_zero_of_connecting_eq_nonzero
      i T e z hz hconnecting)
  exact hvanishes

/-- If a nonzero local degree-two class is the connecting image of a Serre
extension, the componentwise local calculation alone rules out the entire
bad Galois orbit. -/
theorem galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_connecting_eq_nonzero_of_pointwise_vanishing
    {W' : (A →ₐ[K] L) → Type*} [∀ φ, AddCommMonoid (W' φ)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
    (hz : z ≠ 0)
    (hconnecting :
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = z)
    (components : ∀ φ, Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+ W' φ)
    (hcomponents : ∀ z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
      (∀ φ, components φ z = 0) → z = 0)
    (hbad : ∀ φ, φ ∈ B →
      components φ ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega)) = 0) :
    B = ∅ := by
  exact galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_of_pointwise_vanishing
    (W' := W') i T e B hstable
    (serreExtensionSequenceClassInSchemeModules_ne_zero_of_connecting_eq_nonzero
      i T e z hz hconnecting)
    components hcomponents hbad

/-- The geometric-point version of Voisin's Galois argument now produces a
locally free Serre extension.  The finite `A`-valued point supplies the map
from the embedding orbit to the surface; consequently, the empty Galois bad
orbit has empty image, and the local free calculations away from that image
cover the whole surface. -/
noncomputable def SerreExtensionSequenceData.toSerreExtensionData_of_galoisEmbedding_badLocus
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
    (hz : z ≠ 0)
    (hconnecting :
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = z)
    (hvanishes : B = Set.univ →
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = 0)
    (center : Spec (.of A) ⟶ X)
    (U : ∀ x : X, x ∉ galoisEmbeddingPoint (K := K) center '' B → X.Opens)
    (hU : ∀ (x : X) (hx : x ∉ galoisEmbeddingPoint (K := K) center '' B), x ∈ U x hx)
    (I : ∀ (x : X) (hx : x ∉ galoisEmbeddingPoint (K := K) center '' B), Type u)
    (hfree : ∀ (x : X) (hx : x ∉ galoisEmbeddingPoint (K := K) center '' B),
      SheafOfModules.free (R := X.ringCatSheaf.over (U x hx)) (I x hx) ≅
        e.E.over (U x hx)) :
    SerreExtensionData X (closedImmersionIdealTwist i T) :=
  e.toSerreExtensionData_of_badOrbit_eq_empty B (galoisEmbeddingPoint (K := K) center)
    (galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_connecting_eq_nonzero
      i T e B hstable z hz hconnecting hvanishes)
    U hU I hfree

/-- With affine rank-two local calculations, the same Galois argument gives
the affine cover required by the projective-line Serre-pencil construction.
This is the complete categorical and local-to-global output of Lemma 3.1;
the remaining input is the concrete surface calculation of the displayed
trivializations. -/
noncomputable def
    SerreExtensionSequenceData.toSerreExtensionRankTwoAffineCover_of_galoisEmbedding_badLocus
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
    (hz : z ≠ 0)
    (hconnecting :
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = z)
    (hvanishes : B = Set.univ →
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = 0)
    (center : Spec (.of A) ⟶ X)
    (U : ∀ x : X, x ∉ galoisEmbeddingPoint (K := K) center '' B → X.Opens)
    (hU : ∀ (x : X) (hx : x ∉ galoisEmbeddingPoint (K := K) center '' B), x ∈ U x hx)
    (haffine : ∀ (x : X) (hx : x ∉ galoisEmbeddingPoint (K := K) center '' B),
      AlgebraicGeometry.IsAffine (U x hx : Scheme.{u}))
    (t : ∀ (x : X) (hx : x ∉ galoisEmbeddingPoint (K := K) center '' B),
      SheafOfModules.free (R := X.ringCatSheaf.over (U x hx))
        (ULift.{u} (Fin 2)) ≅ e.E.over (U x hx)) :
    SerreExtensionData.SerreExtensionRankTwoAffineCover
      (SerreExtensionSequenceData.toSerreExtensionData_of_galoisEmbedding_badLocus
        (i := i) (T := T) (e := e) B hstable z hz hconnecting hvanishes center U hU
        (fun _ _ => ULift.{u} (Fin 2)) t) := by
  exact e.toSerreExtensionRankTwoAffineCover_of_badOrbit_eq_empty B
    (galoisEmbeddingPoint (K := K) center)
    (galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_connecting_eq_nonzero
      i T e B hstable z hz hconnecting hvanishes)
    U hU haffine t

/-- The pointwise local-Ext form of the Galois calculation supplies the
affine rank-two cover used by the projective-line Serre pencil.  The returned
first component is the global-vanishing implication reconstructed from the
local components; retaining it makes the target Serre extension data
definitionally available to the existing gluing construction. -/
theorem
    SerreExtensionSequenceData.exists_SerreExtensionRankTwoAffineCover_of_galoisEmbedding_badLocus_of_pointwise_vanishing
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {W' : (A →ₐ[K] L) → Type u} [∀ φ, AddCommMonoid (W' φ)]
    (B : Set (A →ₐ[K] L))
    (hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
      σ.toAlgHom.comp φ ∈ B)
    (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
    (hz : z ≠ 0)
    (hconnecting :
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = z)
    (components : ∀ φ, Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+ W' φ)
    (hcomponents : ∀ z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
      (∀ φ, components φ z = 0) → z = 0)
    (hbad : ∀ φ, φ ∈ B →
      components φ ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega)) = 0)
    (center : Spec (.of A) ⟶ X)
    (U : ∀ x : X, x ∉ galoisEmbeddingPoint (K := K) center '' B → X.Opens)
    (hU : ∀ (x : X) (hx : x ∉ galoisEmbeddingPoint (K := K) center '' B), x ∈ U x hx)
    (haffine : ∀ (x : X) (hx : x ∉ galoisEmbeddingPoint (K := K) center '' B),
      AlgebraicGeometry.IsAffine (U x hx : Scheme.{u}))
    (t : ∀ (x : X) (hx : x ∉ galoisEmbeddingPoint (K := K) center '' B),
      SheafOfModules.free (R := X.ringCatSheaf.over (U x hx))
        (ULift.{u} (Fin 2)) ≅ e.E.over (U x hx)) :
    ∃ hvanishes : (B = Set.univ →
        (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
          (serreExtensionSequenceClassInSchemeModules i T e)
          (show 1 + 1 = 2 by omega) = 0),
      Nonempty (SerreExtensionData.SerreExtensionRankTwoAffineCover
        (SerreExtensionSequenceData.toSerreExtensionData_of_galoisEmbedding_badLocus
          (i := i) (T := T) (e := e) B hstable z hz hconnecting hvanishes center U hU
          (fun _ _ => ULift.{u} (Fin 2)) t)) := by
  let hvanishes : B = Set.univ →
      (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
        (serreExtensionSequenceClassInSchemeModules i T e)
        (show 1 + 1 = 2 by omega) = 0 := by
    intro hB
    apply hcomponents
    intro φ
    exact hbad φ (by rw [hB]; exact Set.mem_univ φ)
  exact ⟨hvanishes, ⟨
    SerreExtensionSequenceData.toSerreExtensionRankTwoAffineCover_of_galoisEmbedding_badLocus
      (i := i) (T := T) (e := e) B hstable z hz hconnecting hvanishes center U hU haffine t⟩⟩

/-- A nonzero local `Ext²` class can be lifted, realized by an actual Serre
extension sequence, and fed into Voisin's Galois-orbit argument in one step.
The remaining local hypothesis has its geometric form: if the entire Galois
orbit were bad, the connecting image of every lift of the chosen local class
would vanish. -/
theorem exists_of_nonzeroExtTwo_on_scheme_connecting_and_galoisEmbedding_badLocus_eq_empty
    {X : Scheme.{u}} :
    letI : EnoughInjectives (X.Modules) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (X.Modules) :=
      hasExt_of_enoughInjectives _
    letI : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
      hasExt_of_enoughInjectives _
    ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (T : X.Modules)
      [PreservesFiniteLimits (schemeModuleTensorRight T)]
      [PreservesFiniteColimits (schemeModuleTensorRight T)]
      {K A L : Type u} [Field K] [Field A] [Algebra K A]
      [Field L] [Algebra K L] [Normal K L]
      [Subsingleton (Ext.{u} (show X.Modules from T)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)]
      [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)]
      (B : Set (A →ₐ[K] L))
      (_hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
        σ.toAlgHom.comp φ ∈ B)
      (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
      (_hz : z ≠ 0)
      (_hvanishes : ∀ x : Ext.{u} (closedImmersionIdealTwist i T)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1,
        (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp x
          (show 1 + 1 = 2 by omega) = z → B = Set.univ →
          (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp x
            (show 1 + 1 = 2 by omega) = 0),
      ∃ e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T),
        (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
          e.extensionClass (show 1 + 1 = 2 by omega) = z ∧ B = ∅ := by
  let _ : EnoughInjectives (X.Modules) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (X.Modules) :=
    hasExt_of_enoughInjectives _
  let _ : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives _
  intro Z i hci T hlim hcol K A L hK hA hKA hL hKL hnormal hsub2 hsub1 B hstable z hz hvanishes
  obtain ⟨e, he⟩ :=
    SerreExtensionSequenceData.exists_of_nonzeroExtTwo_on_scheme_connecting i T z hz
  refine ⟨e, he, ?_⟩
  apply galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_connecting_eq_nonzero
    i T e B hstable z hz he
  intro hB
  exact hvanishes e.extensionClass he hB

/-- Kernel-form version of the combined Ext lift and Galois-orbit argument.
It applies to the cubic degree-three twist: the chosen nonzero local class
need only map to zero on the middle sheaf, while that middle `Ext²` group is
allowed to be nonzero. -/
theorem exists_of_nonzeroExtTwo_on_scheme_connecting_of_comp_eq_zero_and_galoisEmbedding_badLocus_eq_empty
    {X : Scheme.{u}} :
    letI : EnoughInjectives (X.Modules) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (X.Modules) :=
      hasExt_of_enoughInjectives _
    letI : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
      hasExt_of_enoughInjectives _
    ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (T : X.Modules)
      [PreservesFiniteLimits (schemeModuleTensorRight T)]
      [PreservesFiniteColimits (schemeModuleTensorRight T)]
      {K A L : Type u} [Field K] [Field A] [Algebra K A]
      [Field L] [Algebra K L] [Normal K L]
      [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)]
      (B : Set (A →ₐ[K] L))
      (_hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
        σ.toAlgHom.comp φ ∈ B)
      (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
      (_hz : z ≠ 0)
      (_hnext :
        (Ext.mk₀ (closedImmersionIdealTwistSequence i T).g).comp z
          (zero_add 2) = 0)
      (_hvanishes : ∀ x : Ext.{u} (closedImmersionIdealTwist i T)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1,
        (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp x
          (show 1 + 1 = 2 by omega) = z → B = Set.univ →
          (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp x
            (show 1 + 1 = 2 by omega) = 0),
      ∃ e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T),
        (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
          e.extensionClass (show 1 + 1 = 2 by omega) = z ∧ B = ∅ := by
  let _ : EnoughInjectives (X.Modules) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (X.Modules) :=
    hasExt_of_enoughInjectives _
  let _ : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives _
  intro Z i hci T hlim hcol K A L hK hA hKA hL hKL hnormal hsub1
    B hstable z hz hnext hvanishes
  obtain ⟨e, he⟩ :=
    SerreExtensionSequenceData.exists_of_nonzeroExtTwo_on_scheme_connecting_of_comp_eq_zero
      i T z hz hnext
  refine ⟨e, he, ?_⟩
  apply galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_connecting_eq_nonzero
    i T e B hstable z hz he
  intro hB
  exact hvanishes e.extensionClass he hB

/-- The Ext-lift and Galois conclusion can be fed directly by the local
component calculation.  The component family detects the chosen nonzero
`Ext²` class, and a bad orbit kills every component; the preceding orbit
theorem then supplies the global vanishing premise required by the lift. -/
theorem exists_of_nonzeroExtTwo_on_scheme_connecting_and_galoisEmbedding_badLocus_eq_empty_of_pointwise_vanishing
    {X : Scheme.{u}} :
    letI : EnoughInjectives (X.Modules) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (X.Modules) :=
      hasExt_of_enoughInjectives _
    letI : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
      hasExt_of_enoughInjectives _
    ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (T : X.Modules)
      [PreservesFiniteLimits (schemeModuleTensorRight T)]
      [PreservesFiniteColimits (schemeModuleTensorRight T)]
      {K A L : Type u} [Field K] [Field A] [Algebra K A]
      [Field L] [Algebra K L] [Normal K L]
      [Subsingleton (Ext.{u} (show X.Modules from T)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)]
      [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)]
      {W' : (A →ₐ[K] L) → Type u} [∀ φ, AddCommMonoid (W' φ)]
      (B : Set (A →ₐ[K] L))
      (_hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
        σ.toAlgHom.comp φ ∈ B)
      (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
      (_hz : z ≠ 0)
      (components : ∀ φ, Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+ W' φ)
      (hcomponents : ∀ z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
        (∀ φ, components φ z = 0) → z = 0)
      (_hbad : ∀ φ, φ ∈ B → components φ z = 0),
      ∃ e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T),
        (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
          e.extensionClass (show 1 + 1 = 2 by omega) = z ∧ B = ∅ := by
  let _ : EnoughInjectives (X.Modules) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (X.Modules) :=
    hasExt_of_enoughInjectives _
  let _ : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives _
  intro Z i hci T hlim hcol K A L hK hA hKA hL hKL hnormal hsub2 hsub1 W' hW' B hstable z hz
    components hcomponents hbad
  obtain ⟨e, he⟩ :=
    SerreExtensionSequenceData.exists_of_nonzeroExtTwo_on_scheme_connecting i T z hz
  refine ⟨e, he, ?_⟩
  apply galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_connecting_eq_nonzero
    i T e B hstable z hz he
  intro hB
  apply hcomponents
  intro φ
  change components φ
    ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
      e.extensionClass (show 1 + 1 = 2 by omega)) = 0
  rw [he]
  exact hbad φ (by rw [hB]; exact Set.mem_univ φ)

/-- Pointwise local-residue form of the kernel-based Serre lift.  This is
the paper-facing interface for the cubic degree-three twist: duality supplies
`z`, its nonvanishing and its zero image on the middle sheaf; local residue
coordinates then prove the resulting extension is locally free along the
whole Galois orbit. -/
theorem exists_of_nonzeroExtTwo_on_scheme_connecting_of_comp_eq_zero_and_galoisEmbedding_badLocus_eq_empty_of_pointwise_vanishing
    {X : Scheme.{u}} :
    letI : EnoughInjectives (X.Modules) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (X.Modules) :=
      hasExt_of_enoughInjectives _
    letI : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
      hasExt_of_enoughInjectives _
    ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (T : X.Modules)
      [PreservesFiniteLimits (schemeModuleTensorRight T)]
      [PreservesFiniteColimits (schemeModuleTensorRight T)]
      {K A L : Type u} [Field K] [Field A] [Algebra K A]
      [Field L] [Algebra K L] [Normal K L]
      [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)]
      {W' : (A →ₐ[K] L) → Type u} [∀ φ, AddCommMonoid (W' φ)]
      (B : Set (A →ₐ[K] L))
      (_hstable : ∀ (σ : L ≃ₐ[K] L) (φ : A →ₐ[K] L), φ ∈ B →
        σ.toAlgHom.comp φ ∈ B)
      (z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
      (_hz : z ≠ 0)
      (_hnext :
        (Ext.mk₀ (closedImmersionIdealTwistSequence i T).g).comp z
          (zero_add 2) = 0)
      (components : ∀ φ, Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 →+ W' φ)
      (hcomponents : ∀ z : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2,
        (∀ φ, components φ z = 0) → z = 0)
      (_hbad : ∀ φ, φ ∈ B → components φ z = 0),
      ∃ e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T),
        (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
          e.extensionClass (show 1 + 1 = 2 by omega) = z ∧ B = ∅ := by
  let _ : EnoughInjectives (X.Modules) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (X.Modules) :=
    hasExt_of_enoughInjectives _
  let _ : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives _
  intro Z i hci T hlim hcol K A L hK hA hKA hL hKL hnormal hsub1 W' hW'
    B hstable z hz hnext components hcomponents hbad
  obtain ⟨e, he⟩ :=
    SerreExtensionSequenceData.exists_of_nonzeroExtTwo_on_scheme_connecting_of_comp_eq_zero
      i T z hz hnext
  refine ⟨e, he, ?_⟩
  apply galoisEmbedding_badLocus_eq_empty_of_serreExtensionSequenceClass_connecting_eq_nonzero
    i T e B hstable z hz he
  intro hB
  apply hcomponents
  intro φ
  change components φ
    ((closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
      e.extensionClass (show 1 + 1 = 2 by omega)) = 0
  rw [he]
  exact hbad φ (by rw [hB]; exact Set.mem_univ φ)


end GaloisLocalFreenessSequence
end PfaffianDescent
