import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.HopkinsLevitzki

/-! SOURCE ONLY / UNVERIFIED169. The actual family map constructs the
canonical B-action on its actual stalk. Flatness, locality and Noetherianity
are derived from the geometry and the base ring, with no regularity input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- The canonical coefficient map B -> O_X,x, through the actual base
stalk and the actual stalk map of the family. No choice of affine chart. -/
def familyBaseToStalk169
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (x : X) : B →+* X.presheaf.stalk x := by
  letI : Algebra B ((Spec (.of B)).presheaf.stalk (f x)) :=
    StructureSheaf.stalkAlgebra B (f x)
  exact (f.stalkMap x).hom.comp
    (algebraMap B ((Spec (.of B)).presheaf.stalk (f x)))

/-- The original base-ring action, installed explicitly at callers rather
than replacing any unrelated ambient algebra instance globally. -/
def familyStalkAlgebra169
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (x : X) : Algebra B (X.presheaf.stalk x) :=
  (familyBaseToStalk169 f x).toAlgebra

/-- This action's algebra map is exactly the geometrically defined map. -/
lemma familyStalkAlgebra169_algebraMap
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (x : X) :
    letI := familyStalkAlgebra169 f x
    algebraMap B (X.presheaf.stalk x) = familyBaseToStalk169 f x := rfl

/-- Compatibility with the actual Gamma(Spec B) inverse and base germ.
This pins down the original coefficient map, not only its ring isomorphism
class. The equality is the native structure-sheaf action definition. -/
lemma familyBaseToStalk169_eq_base_germ_stalkMap
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (x : X) :
    familyBaseToStalk169 f x =
      ((Scheme.ΓSpecIso (.of B)).inv ≫
        (Spec (.of B)).presheaf.germ ⊤ (f x) (by trivial) ≫ f.stalkMap x).hom := rfl

/-- Every actual affine chart uses the SAME coefficient map. This is
useful when extending an arbitrary base ideal and identifying fiber kernels. -/
lemma familyBaseToStalk169_eq_chart
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (x : X) (U : X.Opens) (hx : x ∈ U) :
    familyBaseToStalk169 f x =
      ((Scheme.ΓSpecIso (.of B)).inv ≫
        f.appLE ⊤ U (by intro y hy; trivial) ≫ X.presheaf.germ U x hx).hom := by
  have h : f.appLE ⊤ U (by intro y hy; trivial) ≫ X.presheaf.germ U x hx =
      (Spec (.of B)).presheaf.germ ⊤ (f x) (by trivial) ≫ f.stalkMap x := by
    change (f.app ⊤ ≫ X.presheaf.map
      (homOfLE (show U ≤ f ⁻¹ᵁ ⊤ from by intro y hy; trivial)).op) ≫
      X.presheaf.germ U x hx = _
    rw [Category.assoc, X.presheaf.germ_res]
    exact (f.germ_stalkMap ⊤ x (by trivial)).symm
  rw [familyBaseToStalk169_eq_base_germ_stalkMap]
  exact congrArg (fun a => ((Scheme.ΓSpecIso (.of B)).inv ≫ a).hom) h.symm

/-- A flat family has stalks flat over the ORIGINAL base B. The base
stalk is itself a localization of B; flat stalkMap alone would only give
flatness over the base stalk. Compose both actual maps explicitly. -/
lemma flat_familyBaseToStalk169
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) [Flat f] (x : X) :
    (familyBaseToStalk169 f x).Flat := by
  let y : PrimeSpectrum B := f x
  letI : y.asIdeal.IsPrime := y.isPrime
  letI : Algebra B ((Spec (.of B)).presheaf.stalk y) :=
    StructureSheaf.stalkAlgebra B y
  letI : IsLocalization.AtPrime ((Spec (.of B)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk B y
  have hbase : (algebraMap B ((Spec (.of B)).presheaf.stalk (f x))).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat ((Spec (.of B)).presheaf.stalk (f x))
        (f x).asIdeal.primeCompl)
  exact hbase.comp (Flat.stalkMap f x)

/-- Module flatness under precisely the original canonical coefficient
map, with no supplied module-flatness instance. -/
lemma flat_familyStalkAlgebra169
    {B : Type u} [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) [Flat f] (x : X) :
    letI := familyStalkAlgebra169 f x
    Module.Flat B (X.presheaf.stalk x) :=
  flat_familyBaseToStalk169 f x

/-- The actual stalk is Noetherian for a finite-type family over a
Noetherian base. This is stronger than the smooth Artin-base instance. -/
lemma noetherian_family_stalk169
    {B : Type u} [CommRing B] [IsNoetherianRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) [LocallyOfFiniteType f] (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  infer_instance

/-- All three ambient stalk properties required by regularity168,
constructed from an ACTUAL smooth family over a Noetherian base. No
flat/local/Noetherian stalk or regularity certificate is an input. -/
lemma smooth_family_stalk_properties_noetherian169
    {B : Type u} [CommRing B] [IsNoetherianRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) [Smooth f] (x : X) :
    letI := familyStalkAlgebra169 f x
    Module.Flat B (X.presheaf.stalk x) ∧
      IsLocalRing (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) :=
  ⟨flat_familyStalkAlgebra169 f x, inferInstance, noetherian_family_stalk169 f x⟩

/-- In particular, an actual smooth family over an Artin test ring
supplies the original-action flat/local/Noetherian stalk package. Base
locality is unnecessary for these properties; arbitrary Artin B is allowed. -/
lemma smooth_family_stalk_properties_artin169
    {B : Type u} [CommRing B] [IsArtinianRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) [Smooth f] (x : X) :
    letI := familyStalkAlgebra169 f x
    Module.Flat B (X.presheaf.stalk x) ∧
      IsLocalRing (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) :=
  smooth_family_stalk_properties_noetherian169 f x

/-- Apply the package directly to the ACTUAL Artin base change of the
chosen smooth family. Smoothness of the pullback is derived internally.
This is the small geometry input for the original-cubic deformation caller. -/
lemma smooth_baseChanged_family_stalk_properties_artin169
    {R B : Type u} [CommRing R] [CommRing B] [IsArtinianRing B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f]
    (b : R →+* B)
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom b)) : Scheme.{u})) :
    let fB := pullback.snd f (Spec.map (CommRingCat.ofHom b))
    letI := familyStalkAlgebra169 fB x
    Module.Flat B ((pullback f (Spec.map (CommRingCat.ofHom b))).presheaf.stalk x) ∧
      IsLocalRing ((pullback f (Spec.map (CommRingCat.ofHom b))).presheaf.stalk x) ∧
      IsNoetherianRing ((pullback f (Spec.map (CommRingCat.ofHom b))).presheaf.stalk x) :=
  smooth_family_stalk_properties_artin169
    (pullback.snd f (Spec.map (CommRingCat.ofHom b))) x

end PfaffianDescent
