import PfaffianDescent.VoisinLocalProjectiveIntersectionFlat
import PfaffianDescent.VoisinRelativeRingTwoCubicIntersection

/-!
# Flatness of the actual relative zero-locus fibre at a local parameter

The explicit two-cubic projective intersection is flat over a local
coefficient ring. The arbitrary-ring fibre comparison preserves the base
map, so this flatness applies to the actual pullback-defined relative
universal zero locus.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual relative zero-locus fibre over any local point of Voisin's
nontrivial family is flat over that local point. -/
theorem flatGradedNontrivialOpen_localPoint_relativeFibre_flat
    {K R T : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    [CommRing T] [IsLocalRing T] [Algebra R T]
    [Algebra K T] [IsScalarTower K R T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase
      (a.map (algebraMap K (IsLocalRing.ResidueField T)))
      (ha.map (algebraMap K (IsLocalRing.ResidueField T))))]
    (n : Spec (.of T) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0)
    (hn : n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom (algebraMap R T))) :
    Flat (pullback.snd
      (flatGradedNontrivialRelativeZeroLocusToParameters
        a ha J r q e hRank ha0) n) := by
  let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
  let k : E ⟶ Spec (.of K) :=
    flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R))
  let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
    flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
  let b : K →+* T := algebraMap K T
  have hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k :=
    flatGradedNontrivialOpenToGlobalParameters_toBase a ha J r q e hRank ha0
  have hs : n ≫ k = Spec.map (CommRingCat.ofHom b) := by
    change n ≫ (flatGradedProjectiveFamilyNontrivialOpenToBase
      J r q e hRank a ha ha0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R))) =
        Spec.map (CommRingCat.ofHom b)
    rw [← Category.assoc, hn, ← Spec.map_comp]
    exact congrArg (fun φ : K →+* T => Spec.map (CommRingCat.ofHom φ))
      (IsScalarTower.algebraMap_eq K R T).symm
  obtain ⟨j, f, hf, hflat⟩ :=
    flatGradedNontrivialOpen_localPoint_projectiveIntersection_flat
      J r q e hRank a ha ha0 n hn
  have hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b :=
    normalizedParameterChart_baseMap h k hk b n hs j f hf.symm
  let qₜ := (normalizedForm K (Fin 4) 3 j).map f
  let hqₜ := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  let eF := fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso
    a ha k h b n hs j f hf.symm hb
  have hbase : eF.hom ≫
      toBase (equationIdeal (a.map b) (ha.map b) ⊔ equationIdeal qₜ hqₜ) =
      pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) n :=
    fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso_toBase
      a ha k h b n hs j f hf.symm hb
  letI : Flat (toBase
      (equationIdeal (a.map b) (ha.map b) ⊔ equationIdeal qₜ hqₜ)) := hflat
  haveI : Flat eF.hom := inferInstance
  have htotal : Flat (eF.hom ≫
      toBase (equationIdeal (a.map b) (ha.map b) ⊔ equationIdeal qₜ hqₜ)) :=
    inferInstance
  change Flat (pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters
    a ha k h) n)
  rw [← hbase]
  exact htotal

/-- Smoothness of the fixed cubic over the ground field supplies the
residue-field smoothness required by the local relative-fibre theorem. -/
theorem flatGradedNontrivialOpen_localPoint_relativeFibre_flat_of_smoothFixed
    {K R T : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    [CommRing T] [IsLocalRing T] [Algebra R T]
    [Algebra K T] [IsScalarTower K R T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)]
    (n : Spec (.of T) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0)
    (hn : n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom (algebraMap R T))) :
    Flat (pullback.snd
      (flatGradedNontrivialRelativeZeroLocusToParameters
        a ha J r q e hRank ha0) n) := by
  letI : Smooth (hypersurfaceToBase
      (a.map (algebraMap K (IsLocalRing.ResidueField T)))
      (ha.map (algebraMap K (IsLocalRing.ResidueField T)))) :=
    smooth_hypersurfaceToBase_map
      (algebraMap K (IsLocalRing.ResidueField T)) a ha
  exact flatGradedNontrivialOpen_localPoint_relativeFibre_flat
    J r q e hRank a ha ha0 n hn

/-- Local flatness for an arbitrary local-ring scheme point, with the
coefficient algebra extracted from its morphism to the base. -/
theorem flatGradedNontrivialOpen_localSchemePoint_relativeFibre_flat
    {K R T : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    [CommRing T] [IsLocalRing T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)]
    (n : Spec (.of T) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0) :
    Flat (pullback.snd
      (flatGradedNontrivialRelativeZeroLocusToParameters
        a ha J r q e hRank ha0) n) := by
  let φ : R →+* T := (Spec.preimage
    (n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
      J r q e hRank a ha ha0)).hom
  algebraize [φ]
  letI : Algebra K T := ((algebraMap R T).comp (algebraMap K R)).toAlgebra
  letI : IsScalarTower K R T := IsScalarTower.of_algebraMap_eq' rfl
  have hn : n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
      J r q e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    exact (Spec.map_preimage _).symm
  exact flatGradedNontrivialOpen_localPoint_relativeFibre_flat_of_smoothFixed
    J r q e hRank a ha ha0 n hn

/-- The canonical local base change of the relative zero locus is flat at
every parameter point when the fixed cubic is smooth. -/
theorem flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_flat
    {K R : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)]
    (y : flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0) :
    Flat (pullback.snd
      (flatGradedNontrivialRelativeZeroLocusToParameters
        a ha J r q e hRank ha0)
      ((flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0).fromSpecStalk y)) := by
  let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
  let T := E.presheaf.stalk y
  let n : Spec (.of T) ⟶ E := E.fromSpecStalk y
  let φ : R →+* T := (Spec.preimage
    (n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
      J r q e hRank a ha ha0)).hom
  algebraize [φ]
  letI : Algebra K T := ((algebraMap R T).comp (algebraMap K R)).toAlgebra
  letI : IsScalarTower K R T := IsScalarTower.of_algebraMap_eq' rfl
  have hn : n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
      J r q e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    exact (Spec.map_preimage _).symm
  exact flatGradedNontrivialOpen_localPoint_relativeFibre_flat_of_smoothFixed
    J r q e hRank a ha ha0 n hn

end PfaffianDescent
