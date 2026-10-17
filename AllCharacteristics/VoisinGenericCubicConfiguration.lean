import AllCharacteristics.ProjectiveConfigurationFiberSubscheme
import AllCharacteristics.ProjectiveConfigurationIntegrality
import AllCharacteristics.ProjectiveBaseChange
import AllCharacteristics.HypersurfaceCoefficientNaturality
import AllCharacteristics.HomogeneousConfigurationQuotient
import AllCharacteristics.ProjectiveFiberSmoothness
import AllCharacteristics.ProjectiveConfigurationBaseFlat
import AllCharacteristics.FlatStalkCharacteristic

/-!
# The generic configuration datum on a coefficient-changed cubic

Voisin's first residual construction is performed over the function field of
an integral configuration space.  The generic finite subscheme is initially
an actual categorical pullback of the original cubic.  This file identifies
it with a finite datum on the cubic obtained by mapping the equation's
coefficients to that function field, which is the input expected by the
homogeneous complete-intersection development.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The unordered configuration base of a cubic hypersurface. -/
noncomputable abbrev cubicConfigurationBase
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ) :
    Scheme.{u} :=
  (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
    (toBase (equationIdeal p hp)) n).toScheme

/-- The generic point of the cubic configuration base as a morphism from its
function field. -/
noncomputable abbrev cubicConfigurationGenericBaseMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)] :
    Spec (.of (cubicConfigurationBase p hp n).functionField) ⟶
      cubicConfigurationBase p hp n :=
  (cubicConfigurationBase p hp n).fromSpecStalk
    (genericPoint (cubicConfigurationBase p hp n))

/-- The configuration base remains over the original coefficient field. -/
noncomputable abbrev cubicConfigurationToBase
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ) :
    cubicConfigurationBase p hp n ⟶ Spec (.of K) :=
  projectiveConfigurationQuotientToBase (grading (equationIdeal p hp))
    (toBase (equationIdeal p hp)) n

/-- The configuration base is integral once the cubic is geometrically
integral and its distinct-configuration open is nonempty.  This isolates the
two geometric facts still needed to form Voisin's generic point. -/
theorem isIntegral_cubicConfigurationBase_of_geometricallyIntegral
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [GeometricallyIntegral (toBase (equationIdeal p hp))]
    [Flat (toBase (equationIdeal p hp))]
    [UniversallyOpen (toBase (equationIdeal p hp))]
    [LocallyOfFiniteType (toBase (equationIdeal p hp))]
    [Nonempty (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) n).left] :
    IsIntegral (cubicConfigurationBase p hp n) := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) := inferInstance
  letI : Nonempty (orderedFamilyConfigurationOver
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) n).left := by
    exact ‹Nonempty (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) n).left›
  letI : GeometricallyIntegral
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) := by
    exact ‹GeometricallyIntegral (toBase (equationIdeal p hp))›
  letI : Flat
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) := by
    exact ‹Flat (toBase (equationIdeal p hp))›
  letI : UniversallyOpen
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) := by
    exact ‹UniversallyOpen (toBase (equationIdeal p hp))›
  letI : LocallyOfFiniteType
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) := by
    exact ‹LocallyOfFiniteType (toBase (equationIdeal p hp))›
  exact isIntegral_projectiveConfigurationQuotientOpen_of_geometricallyIntegral
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n

/-- In characteristic zero, the function field of an integral configuration
base is again characteristic zero whenever the original cubic is flat over
its coefficient field. -/
theorem charZero_cubicConfigurationFunctionField_of_flat
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [CharZero K]
    [IsIntegral (cubicConfigurationBase p hp n)]
    [Flat (toBase (equationIdeal p hp))] :
    CharZero (cubicConfigurationBase p hp n).functionField := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) := inferInstance
  letI : Flat (cubicConfigurationToBase p hp n) := by
    exact inferInstance
  exact charZero_functionField_of_flat_over_domain K
    (cubicConfigurationToBase p hp n)

/-- A nonzero cubic remains nonzero after passing to the configuration
function field. -/
theorem cubicConfigurationCoefficientChange_ne_zero
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (hne : p ≠ 0) :
    p.map a.hom ≠ 0 := by
  intro h
  apply hne
  apply MvPolynomial.map_injective a.hom (RingHom.injective a.hom)
  simpa using h

/-- The generic configuration datum, transported to the cubic whose
coefficients lie in the configuration function field.  For `n = 16`, this
is the precise scheme that starts Voisin's cubic--cubic--cubic residual. -/
noncomputable def cubicConfigurationGenericFiniteSubscheme
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) n := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) := inferInstance
  have ha' : Spec.map (CommRingCat.ofHom a.hom) =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n := ha
  exact hypersurfaceFiniteSubschemeOfCoefficientBaseChange a.hom p hp
    (projectiveConfigurationGenericFiniteSubschemeAtBaseMap
      (𝒜 := grading (equationIdeal p hp))
      (f := toBase (equationIdeal p hp)) n (CommRingCat.ofHom a.hom) ha')

/-- The finite scheme on the coefficient-changed cubic is canonically the
same scheme as the generic configuration in the categorical pullback
presentation. -/
noncomputable def cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme ≅
      (projectiveConfigurationGenericFiniteSubschemeAtBaseMap
        (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
        (CommRingCat.ofHom a.hom) ha).val.subscheme := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) := inferInstance
  let D := projectiveConfigurationGenericFiniteSubschemeAtBaseMap
    (𝒜 := grading (equationIdeal p hp))
    (f := toBase (equationIdeal p hp)) n (CommRingCat.ofHom a.hom) ha
  let e := hypersurfaceBaseChangeIso a.hom p hp
  have he : e.hom ≫
      pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom)) =
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom) :=
    hypersurfaceBaseChangeIso_hom_snd a.hom p hp
  change (hypersurfaceFiniteSubschemeOfCoefficientBaseChange
      a.hom p hp D).val.subscheme ≅ _
  exact FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom))) e he D

/-- The coefficient-changed presentation isomorphism preserves the ambient
projective point after changing coefficients back to the original field. -/
@[reassoc]
theorem cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap_inv_toAmbient
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap p hp n a ha).inv ≫
        (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subschemeι ≫
        hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom) ≫
        ambientCoefficientMap a.hom =
      (projectiveConfigurationGenericFiniteSubschemeAtBaseMap
        (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
        (CommRingCat.ofHom a.hom) ha).val.subschemeι ≫
        pullback.fst (hypersurfaceToBase p hp)
          (Spec.map (CommRingCat.ofHom a.hom)) ≫
        hypersurfaceToAmbient p hp := by
  let D := projectiveConfigurationGenericFiniteSubschemeAtBaseMap
    (𝒜 := grading (equationIdeal p hp))
    (f := toBase (equationIdeal p hp)) n (CommRingCat.ofHom a.hom) ha
  let D' : FiniteSubschemeDatum
      (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom))) n := D
  let e := hypersurfaceBaseChangeIso a.hom p hp
  have he : e.hom ≫
      pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom)) =
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom) :=
    hypersurfaceBaseChangeIso_hom_snd a.hom p hp
  change (FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom))) e he D').inv ≫
    (FiniteSubschemeDatum.transportAlongAmbientIso
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom))) e he D').val.subschemeι ≫
      hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom) ≫
      ambientCoefficientMap a.hom = _
  rw [FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso_inv_ι_assoc]
  have hnatural : e.inv ≫
      hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom) ≫
      ambientCoefficientMap a.hom =
    pullback.fst (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom)) ≫
      hypersurfaceToAmbient p hp := by
    have hred := hypersurfaceReductionMap_comp_hypersurfaceToAmbient
      a.hom p hp (p.map a.hom) (hp.map a.hom) rfl
    have hreduction : hypersurfaceReductionMap
        a.hom p hp (p.map a.hom) (hp.map a.hom) rfl =
      e.hom ≫ pullback.fst (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom)) := rfl
    rw [hreduction] at hred
    have hred' := congrArg (fun t ↦ e.inv ≫ t) hred.symm
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hred'
  change D'.val.subschemeι ≫
      (e.inv ≫ hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom) ≫
        ambientCoefficientMap a.hom) =
    D'.val.subschemeι ≫
      (pullback.fst (hypersurfaceToBase p hp)
          (Spec.map (CommRingCat.ofHom a.hom)) ≫ hypersurfaceToAmbient p hp)
  exact congrArg (fun t ↦ D'.val.subschemeι ≫ t) hnatural

/-- The coefficient-changed presentation isomorphism preserves the structure
morphism to the configuration function field. -/
@[reassoc]
theorem cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap_inv_toBase
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap p hp n a ha).inv ≫
        (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom) =
      (projectiveConfigurationGenericFiniteSubschemeAtBaseMap
        (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
        (CommRingCat.ofHom a.hom) ha).val.subschemeι ≫
        pullback.snd (hypersurfaceToBase p hp)
          (Spec.map (CommRingCat.ofHom a.hom)) := by
  let D := projectiveConfigurationGenericFiniteSubschemeAtBaseMap
    (𝒜 := grading (equationIdeal p hp))
    (f := toBase (equationIdeal p hp)) n (CommRingCat.ofHom a.hom) ha
  let D' : FiniteSubschemeDatum
      (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom))) n := D
  let e := hypersurfaceBaseChangeIso a.hom p hp
  have he : e.hom ≫
      pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom)) =
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom) :=
    hypersurfaceBaseChangeIso_hom_snd a.hom p hp
  change (FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom))) e he D').inv ≫
    (FiniteSubschemeDatum.transportAlongAmbientIso
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom))) e he D').val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom) = _
  exact FiniteSubschemeDatum.transportAlongAmbientIsoSubschemeIso_inv_toBase
    (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
    (pullback.snd (hypersurfaceToBase p hp)
      (Spec.map (CommRingCat.ofHom a.hom))) e he D'

/-- The coefficient-changed cubic presentation retains the actual finite
scheme underlying the original generic incidence configuration. -/
noncomputable def cubicConfigurationGenericFiniteSubschemeIsoGeneric
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme ≅
      (projectiveConfigurationGenericFiniteSubscheme
        (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n).val.subscheme :=
  cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap p hp n a ha ≪≫
    projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
      (CommRingCat.ofHom a.hom) ha

/-- The ambient projective morphism of the finite scheme on the
coefficient-changed cubic, viewed back over the original coefficient field. -/
noncomputable def cubicConfigurationCoefficientChangedAmbientMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
  (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subschemeι ≫
    hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom) ≫
    ambientCoefficientMap a.hom

/-- The ambient map of the chosen base-map presentation of the generic
finite scheme. -/
noncomputable def cubicConfigurationAtBaseMapAmbientMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (projectiveConfigurationGenericFiniteSubschemeAtBaseMap
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
      (CommRingCat.ofHom a.hom) ha).val.subscheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
  (projectiveConfigurationGenericFiniteSubschemeAtBaseMap
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
      (CommRingCat.ofHom a.hom) ha).val.subschemeι ≫
    pullback.fst (hypersurfaceToBase p hp)
      (Spec.map (CommRingCat.ofHom a.hom)) ≫
    hypersurfaceToAmbient p hp

/-- The original generic incidence finite scheme mapped to the original
ambient projective space. -/
noncomputable def cubicConfigurationGenericAmbientMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))] :
    (projectiveConfigurationGenericFiniteSubscheme
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n).val.subscheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
  (projectiveConfigurationGenericFiniteSubscheme
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n).val.subschemeι ≫
    pullback.fst
      (pullback.snd (hypersurfaceToBase p hp) (cubicConfigurationToBase p hp n))
      (cubicConfigurationGenericBaseMap p hp n) ≫
    pullback.fst (hypersurfaceToBase p hp) (cubicConfigurationToBase p hp n) ≫
    hypersurfaceToAmbient p hp

/-- The structure morphism of the finite scheme on the coefficient-changed
cubic to the configuration function field. -/
noncomputable def cubicConfigurationCoefficientChangedBaseMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subscheme ⟶
      Spec (.of (cubicConfigurationBase p hp n).functionField) :=
  (cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subschemeι ≫
    hypersurfaceToBase (p.map a.hom) (hp.map a.hom)

/-- The structure morphism in the explicit base-map presentation. -/
noncomputable def cubicConfigurationAtBaseMapBaseMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (projectiveConfigurationGenericFiniteSubschemeAtBaseMap
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
      (CommRingCat.ofHom a.hom) ha).val.subscheme ⟶
      Spec (.of (cubicConfigurationBase p hp n).functionField) :=
  (projectiveConfigurationGenericFiniteSubschemeAtBaseMap
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
      (CommRingCat.ofHom a.hom) ha).val.subschemeι ≫
    pullback.snd (hypersurfaceToBase p hp)
      (Spec.map (CommRingCat.ofHom a.hom))

/-- The structure morphism of the original generic incidence finite scheme
to the configuration function field. -/
noncomputable def cubicConfigurationGenericFiniteBaseMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))] :
    (projectiveConfigurationGenericFiniteSubscheme
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n).val.subscheme ⟶
      Spec (.of (cubicConfigurationBase p hp n).functionField) :=
  (projectiveConfigurationGenericFiniteSubscheme
      (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n).val.subschemeι ≫
    pullback.snd
      (pullback.snd (hypersurfaceToBase p hp) (cubicConfigurationToBase p hp n))
      (cubicConfigurationGenericBaseMap p hp n)

/-- Compact form of structure-map compatibility for coefficient change. -/
theorem cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap_inv_baseMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap p hp n a ha).inv ≫
      cubicConfigurationCoefficientChangedBaseMap p hp n a ha =
        cubicConfigurationAtBaseMapBaseMap p hp n a ha := by
  exact cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap_inv_toBase
    p hp n a ha

/-- Compact form of structure-map compatibility for the chosen generic base
presentation. -/
theorem cubicConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric_inv_baseMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric
        (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
        (CommRingCat.ofHom a.hom) ha).inv ≫
      cubicConfigurationAtBaseMapBaseMap p hp n a ha =
        cubicConfigurationGenericFiniteBaseMap p hp n := by
  exact projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric_inv_toBase
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
    (CommRingCat.ofHom a.hom) ha

/-- The base-map presentation and the original generic incidence scheme have
the same morphism to the original ambient projective space. -/
theorem cubicConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric_inv_ambientMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric
        (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
        (CommRingCat.ofHom a.hom) ha).inv ≫
      cubicConfigurationAtBaseMapAmbientMap p hp n a ha =
        cubicConfigurationGenericAmbientMap p hp n := by
  unfold cubicConfigurationAtBaseMapAmbientMap cubicConfigurationGenericAmbientMap
  exact projectiveConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric_inv_toProjective_assoc
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) n
    (CommRingCat.ofHom a.hom) ha (hypersurfaceToAmbient p hp)

/-- The coefficient-changed and base-map presentations have the same ambient
projective morphism. -/
theorem cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap_inv_ambientMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap p hp n a ha).inv ≫
      cubicConfigurationCoefficientChangedAmbientMap p hp n a ha =
        cubicConfigurationAtBaseMapAmbientMap p hp n a ha := by
  exact cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap_inv_toAmbient
    p hp n a ha

/-- The full identification of the coefficient-changed finite scheme with
the original generic incidence scheme preserves the ambient projective map. -/
theorem cubicConfigurationGenericFiniteSubschemeIsoGeneric_inv_ambientMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (cubicConfigurationGenericFiniteSubschemeIsoGeneric p hp n a ha).inv ≫
      cubicConfigurationCoefficientChangedAmbientMap p hp n a ha =
        cubicConfigurationGenericAmbientMap p hp n := by
  rw [cubicConfigurationGenericFiniteSubschemeIsoGeneric]
  simp only [Iso.trans_inv, Category.assoc]
  rw [cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap_inv_ambientMap]
  exact cubicConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric_inv_ambientMap
    p hp n a ha

/-- The full identification of the coefficient-changed finite scheme with
the original generic incidence scheme preserves the function-field base map. -/
theorem cubicConfigurationGenericFiniteSubschemeIsoGeneric_inv_toBase
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    [IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp))]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    (cubicConfigurationGenericFiniteSubschemeIsoGeneric p hp n a ha).inv ≫
        cubicConfigurationCoefficientChangedBaseMap p hp n a ha =
      cubicConfigurationGenericFiniteBaseMap p hp n := by
  rw [cubicConfigurationGenericFiniteSubschemeIsoGeneric]
  simp only [Iso.trans_inv, Category.assoc]
  rw [cubicConfigurationGenericFiniteSubschemeIsoAtBaseMap_inv_baseMap]
  exact cubicConfigurationGenericFiniteSubschemeAtBaseMapIsoGeneric_inv_baseMap
    p hp n a ha

/-- The generic configuration is finite étale on the cubic obtained by
mapping its coefficients to the configuration function field. -/
theorem etale_cubicConfigurationGenericFiniteSubscheme_toBase
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    Etale ((cubicConfigurationGenericFiniteSubscheme p hp n a ha).val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) := inferInstance
  have ha' : Spec.map (CommRingCat.ofHom a.hom) =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n := ha
  let D := projectiveConfigurationGenericFiniteSubschemeAtBaseMap
    (𝒜 := grading (equationIdeal p hp))
    (f := toBase (equationIdeal p hp)) n (CommRingCat.ofHom a.hom) ha'
  have hD : Etale (D.val.subschemeι ≫
      pullback.snd (toBase (equationIdeal p hp))
        (Spec.map (CommRingCat.ofHom a.hom))) := by
    dsimp [D]
    exact etale_projectiveConfigurationGenericFiniteSubschemeAtBaseMap_toBase
      (𝒜 := grading (equationIdeal p hp))
      (f := toBase (equationIdeal p hp)) n (CommRingCat.ofHom a.hom) ha'
  have hD' : Etale (D.val.subschemeι ≫
      pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom a.hom))) := hD
  change Etale
    ((hypersurfaceFiniteSubschemeOfCoefficientBaseChange a.hom p hp D).val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  exact @hypersurfaceFiniteSubschemeOfCoefficientBaseChange_toBase_etale
    _ _ _ _ _ a.hom p _ hp _ D hD'

/-- The coefficient-changed generic configuration has its prescribed finite
scheme rank.  In particular, `n = 16` supplies the length required for
Voisin's first three-cubic residual. -/
theorem finiteSchemeRank_cubicConfigurationGenericFiniteSubscheme
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    let f := hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
    let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
    letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
    finiteSchemeRank (D.val.subschemeι ≫ f) = n := by
  let f := hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
  let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  exact finiteSubschemeDatum_finiteSchemeRank f D

/-- The coefficient map used by the generic cubic always exists, because
`Spec` is fully faithful. -/
theorem exists_cubicConfigurationGenericBaseMap
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)] :
    ∃ a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp n).functionField,
      Spec.map a =
        cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
        toBase (equationIdeal p hp)) := inferInstance
  exact exists_projectiveConfigurationGenericBaseMap
    (𝒜 := grading (equationIdeal p hp))
    (f := toBase (equationIdeal p hp)) n

/-- Smoothness of the original cubic passes to the coefficient-changed cubic
on which the generic finite configuration lies. -/
theorem smooth_cubicConfigurationGenericCoefficientChange
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField) :
    Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := by
  exact smooth_hypersurfaceToBase_map a.hom p hp

/-- The generic configuration datum supplies an effective zero-cycle of its
specified degree on the coefficient-changed cubic. -/
theorem cubicConfigurationGenericFiniteSubscheme_cycle_degree
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n) :
    EffectiveZeroCycle.degree
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (finiteSubschemeDatumCycle
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (cubicConfigurationGenericFiniteSubscheme p hp n a ha)) = n := by
  exact finiteSubschemeDatumCycle_degree _ _

end AllCharacteristics.HomogeneousProjective
