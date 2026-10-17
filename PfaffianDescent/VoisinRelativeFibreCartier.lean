import PfaffianDescent.VoisinRelativeRingTwoCubicIntersection
import PfaffianDescent.VoisinRegularPrincipalProjectiveCharts
import PfaffianDescent.AffineClosedImmersionIdealKernel
import PfaffianDescent.VoisinLocalRelativeFibreFlat

/-!
# Cartier presentation of a local relative fibre

The concrete two-cubic quotient immersion represents the base change of
the actual relative universal-equation zero locus. This file connects the
two immersions before transporting the regular-principal affine cover.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The normalized projective intersection's canonical immersion into the
coefficient-changed fixed cubic. -/
noncomputable def normalizedTwoCubicToFixedCubic
    {K T : Type u} [Field K] [CommRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (b : K →+* T)
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T) :
    scheme (equationIdeal (a.map b) (ha.map b) ⊔
      equationIdeal ((normalizedForm K (Fin 4) 3 j).map f)
        ((normalizedForm_isHomogeneous K (Fin 4) 3 j).map f)) ⟶
    hypersurface (a.map b) (ha.map b) :=
  schemeQuotientMap
    (equationIdeal (a.map b) (ha.map b))
    (equationIdeal (a.map b) (ha.map b) ⊔
      equationIdeal ((normalizedForm K (Fin 4) 3 j).map f)
        ((normalizedForm_isHomogeneous K (Fin 4) 3 j).map f))
    (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)

/-- The last projective-intersection isomorphism carries the quotient map
to the first projection of the two-cubic intersection. -/
theorem fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso_toTwoCubicFirst
    {K T : Type u} [Field K] [CommRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (b : K →+* T) (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b) :
    let q := (normalizedForm K (Fin 4) 3 j).map f
    let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
    (fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso
      a ha k h b s hs j f heq hb).hom ≫
      normalizedTwoCubicToFixedCubic a ha b j f =
    (fixedCubicSurfaceEquationZeroLocusTwoCubicRingFibreIso
      a ha k h b s hs j f heq hb).hom ≫
      pullback.fst
        (prod.lift
          (hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b)
          (hypersurfaceToBase (a.map b) (ha.map b)))
        (prod.lift
          (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b)
          (hypersurfaceToBase q hq)) := by
  simp only [fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso,
    normalizedTwoCubicToFixedCubic, Iso.trans_hom, Iso.symm_hom]
  exact congrArg (fun t =>
      (fixedCubicSurfaceEquationZeroLocusTwoCubicRingFibreIso
        a ha k h b s hs j f heq hb).hom ≫ t)
    (projectiveIntersectionCoefficientProductIso_inv_fst b (Fin 4)
      (equationIdeal (a.map b) (ha.map b))
      (equationIdeal ((normalizedForm K (Fin 4) 3 j).map f)
        ((normalizedForm_isHomogeneous K (Fin 4) 3 j).map f)))

/-- The source and target fibre isomorphisms identify the normalized
projective quotient immersion with the actual relative zero-locus
immersion over a ring-valued equation parameter. -/
theorem fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso_immersionSquare
    {K T : Type u} [Field K] [CommRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (b : K →+* T) (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b) :
    (fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso
      a ha k h b s hs j f heq hb).hom ≫
      normalizedTwoCubicToFixedCubic a ha b j f ≫
      (fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs).inv =
    fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s := by
  apply pullback.hom_ext
  · rw [fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre_fst]
    rw [← Category.assoc, fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso_toTwoCubicFirst
      a ha k h b s hs j f heq hb]
    exact fixedCubicSurfaceEquationZeroLocusTwoCubicRingFibreIso_toSurface
      a ha k h b s hs j f heq hb
  · rw [fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre_snd]
    let q := (normalizedForm K (Fin 4) 3 j).map f
    let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
    let J := equationIdeal (a.map b) (ha.map b)
    let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs
    let eZ := fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso
      a ha k h b s hs j f heq hb
    have hX : eX.inv ≫
        pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s =
        hypersurfaceToBase (a.map b) (ha.map b) := by
      have h := fixedCubicSurfaceFamilyRingFibreIso_toBase a ha k b s hs
      calc
        eX.inv ≫ pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s =
          eX.inv ≫ eX.hom ≫ hypersurfaceToBase (a.map b) (ha.map b) := by
            rw [h]
        _ = hypersurfaceToBase (a.map b) (ha.map b) := by
          simp only [Iso.inv_hom_id_assoc]
    have hQ : normalizedTwoCubicToFixedCubic a ha b j f ≫
        hypersurfaceToBase (a.map b) (ha.map b) =
        toBase (J ⊔ equationIdeal q hq) := by
      exact schemeQuotientMap_toBase J (J ⊔ equationIdeal q hq)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)
    calc
      _ = eZ.hom ≫ normalizedTwoCubicToFixedCubic a ha b j f ≫
          hypersurfaceToBase (a.map b) (ha.map b) := by
            change (eZ.hom ≫ normalizedTwoCubicToFixedCubic a ha b j f ≫
              eX.inv) ≫ pullback.snd
                (pullback.snd (hypersurfaceToBase a ha) k) s = _
            simp only [Category.assoc]
            rw [hX]
      _ = eZ.hom ≫ toBase (J ⊔ equationIdeal q hq) := by rw [hQ]
      _ = _ := fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso_toBase
        a ha k h b s hs j f heq hb

/-- Over a ring-valued equation parameter lying in a standard chart, the
actual relative zero-locus fibre is a closed immersion. -/
theorem fixedCubicSurfaceEquationZeroLocusFibre_isClosedImmersion
    {K T : Type u} [Field K] [CommRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (b : K →+* T) (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b) :
    IsClosedImmersion
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s) := by
  letI : IsClosedImmersion (normalizedTwoCubicToFixedCubic a ha b j f) := by
    unfold normalizedTwoCubicToFixedCubic
    exact schemeQuotientMap_closedImmersion _ _ _
  rw [← fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso_immersionSquare
    a ha k h b s hs j f heq hb]
  infer_instance

/-- A regular-principal presentation of the concrete projective
intersection transfers to the actual relative zero-locus fibre. -/
noncomputable def fixedCubicSurfaceEquationZeroLocusFibre_regularPrincipalImmersion
    {K T : Type u} [Field K] [CommRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (b : K →+* T) (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b)
    (H : let q := (normalizedForm K (Fin 4) 3 j).map f
      let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
      let J := equationIdeal (a.map b) (ha.map b)
      HasRegularPrincipalStandardCharts J (J ⊔ equationIdeal q hq)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)) :
    RegularPrincipalImmersion
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s) := by
  let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs
  let eZ := fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso
    a ha k h b s hs j f heq hb
  let Hmodel : RegularPrincipalImmersion
      (normalizedTwoCubicToFixedCubic a ha b j f) := H.toImmersion
  have hsq : eZ.hom ≫ normalizedTwoCubicToFixedCubic a ha b j f =
      fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s ≫
        eX.hom := by
    have h₀ := fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso_immersionSquare
      a ha k h b s hs j f heq hb
    have h₁ := congrArg (fun t => t ≫ eX.hom) h₀
    simpa only [eX, eZ, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using h₁
  exact Hmodel.ofIso eX eZ hsq

/-- The actual relative zero-locus fibre over every local point of
Voisin's nontrivial moving-equation family is a regular-principal closed
immersion into the corresponding fixed-surface fibre. -/
noncomputable def flatGradedNontrivialOpen_localPoint_relativeFibre_regularPrincipalImmersion
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
    let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
    RegularPrincipalImmersion
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h n) := by
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
  let w := flatGradedNontrivialOpen_localPoint_hasRegularPrincipalStandardCharts
    J r q e hRank a ha ha0 n hn
  let j := Classical.choose w
  let f := Classical.choose (Classical.choose_spec w)
  have hf : Spec.map (CommRingCat.ofHom f) ≫
      parameterChartι K (Fin 4) 3 j = n ≫ h :=
    (Classical.choose_spec (Classical.choose_spec w)).1
  have H : HasRegularPrincipalStandardCharts
      (equationIdeal (a.map b) (ha.map b))
      (equationIdeal (a.map b) (ha.map b) ⊔
        equationIdeal ((normalizedForm K (Fin 4) 3 j).map f)
          ((normalizedForm_isHomogeneous K (Fin 4) 3 j).map f))
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) :=
    (Classical.choose_spec (Classical.choose_spec w)).2
  have hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b :=
    normalizedParameterChart_baseMap h k hk b n hs j f hf.symm
  exact fixedCubicSurfaceEquationZeroLocusFibre_regularPrincipalImmersion
    a ha k h b n hs j f hf.symm hb H

/-- The actual fibre immersion at a local ring point of the moving-equation
family is closed, hence quasi-compact. -/
theorem flatGradedNontrivialOpen_localPoint_relativeFibre_isClosedImmersion
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
    let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
    IsClosedImmersion
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h n) := by
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
  letI : Smooth (hypersurfaceToBase
      (a.map (algebraMap K (IsLocalRing.ResidueField T)))
      (ha.map (algebraMap K (IsLocalRing.ResidueField T)))) :=
    smooth_hypersurfaceToBase_map
      (algebraMap K (IsLocalRing.ResidueField T)) a ha
  let w := flatGradedNontrivialOpen_localPoint_hasRegularPrincipalStandardCharts
    J r q e hRank a ha ha0 n hn
  let j := Classical.choose w
  let f := Classical.choose (Classical.choose_spec w)
  have hf : Spec.map (CommRingCat.ofHom f) ≫
      parameterChartι K (Fin 4) 3 j = n ≫ h :=
    (Classical.choose_spec (Classical.choose_spec w)).1
  have hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b :=
    normalizedParameterChart_baseMap h k hk b n hs j f hf.symm
  exact fixedCubicSurfaceEquationZeroLocusFibre_isClosedImmersion
    a ha k h b n hs j f hf.symm hb

/-- Smoothness of the fixed cubic over the ground field supplies the
residue-field smoothness used by the local Cartier theorem. -/
noncomputable def flatGradedNontrivialOpen_localPoint_relativeFibre_regularPrincipalImmersion_of_smoothFixed
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
    let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
    RegularPrincipalImmersion
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h n) := by
  letI : Smooth (hypersurfaceToBase
      (a.map (algebraMap K (IsLocalRing.ResidueField T)))
      (ha.map (algebraMap K (IsLocalRing.ResidueField T)))) :=
    smooth_hypersurfaceToBase_map
      (algebraMap K (IsLocalRing.ResidueField T)) a ha
  exact flatGradedNontrivialOpen_localPoint_relativeFibre_regularPrincipalImmersion
    J r q e hRank a ha ha0 n hn

/-- At every local-ring scheme point of the nontrivial moving-equation
family, the actual pulled-back relative zero locus is a regular-principal
immersion into the pulled-back fixed surface. -/
noncomputable def flatGradedNontrivialOpen_localSchemePoint_relativeFibre_regularPrincipalImmersion
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
    let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
    RegularPrincipalImmersion
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h n) := by
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
  exact flatGradedNontrivialOpen_localPoint_relativeFibre_regularPrincipalImmersion_of_smoothFixed
    J r q e hRank a ha ha0 n hn

/-- The pulled-back relative zero locus at any local-ring point is a
closed immersion, without requiring a separately supplied algebra map. -/
theorem flatGradedNontrivialOpen_localSchemePoint_relativeFibre_isClosedImmersion
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
    let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
    IsClosedImmersion
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h n) := by
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
  exact flatGradedNontrivialOpen_localPoint_relativeFibre_isClosedImmersion
    J r q e hRank a ha ha0 n hn

/-- The actual relative zero-locus immersion has a regular-principal
presentation after base change to the canonical local ring of every
parameter point. -/
noncomputable def flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_regularPrincipalImmersion
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
    let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
    RegularPrincipalImmersion
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
        a ha k h (E.fromSpecStalk y)) := by
  let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
  let T := E.presheaf.stalk y
  let n : Spec (.of T) ⟶ E := E.fromSpecStalk y
  exact flatGradedNontrivialOpen_localSchemePoint_relativeFibre_regularPrincipalImmersion
    J r q e hRank a ha ha0 n

/-- The canonical local-parameter fibre of the actual Voisin relative
zero locus is a closed immersion. -/
theorem flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_isClosedImmersion
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
    let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
    IsClosedImmersion
      (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
        a ha k h (E.fromSpecStalk y)) := by
  let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
  let T := E.presheaf.stalk y
  let n : Spec (.of T) ⟶ E := E.fromSpecStalk y
  exact flatGradedNontrivialOpen_localSchemePoint_relativeFibre_isClosedImmersion
    J r q e hRank a ha ha0 n

/-- The ideal of the actual relative zero locus becomes a free rank-one
module on every chart of its canonical local-parameter presentation. -/
theorem flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_idealFreeOnCharts
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
    let H := flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_regularPrincipalImmersion
      J r q e hRank a ha ha0 y
    ∀ j : H.Index, Module.Free (H.A j) (RingHom.ker (H.ringMap j).hom) := by
  dsimp only
  intro j
  exact (flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_regularPrincipalImmersion
    J r q e hRank a ha ha0 y).kernel_moduleFree j

/-- The actual relative fibre's ideal sheaf is a regular principal ideal
on each cartesian affine chart of its canonical local-ring presentation. -/
theorem flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_idealSheaf_regularPrincipalOnCharts
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
    let H := flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_regularPrincipalImmersion
      J r q e hRank a ha ha0 y
    ∀ j : H.Index, ∃ z : Γ(Spec (H.A j), ⊤),
      IsRegular z ∧
      (Spec.map (H.ringMap j)).ker.ideal
          (⟨⊤, isAffineOpen_top (Spec (H.A j))⟩ :
            (Spec (H.A j)).affineOpens) =
        Ideal.span ({z} : Set Γ(Spec (H.A j), ⊤)) := by
  dsimp only
  intro j
  exact (flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_regularPrincipalImmersion
    J r q e hRank a ha ha0 y).chartIdealSheaf_regularPrincipal j

/-- On each affine chart of the canonical local-parameter fibre, the
restriction of the actual fibre immersion's ideal sheaf is generated by a
regular section. -/
theorem flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_ownIdealSheaf_regularPrincipalOnCharts
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
    let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
    let fibreMap := fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha k h (E.fromSpecStalk y)
    let H := flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_regularPrincipalImmersion
      J r q e hRank a ha ha0 y
    ∀ j : H.Index,
      letI : IsOpenImmersion (H.target j) := H.targetOpen j
      let W : (Spec (H.A j)).affineOpens :=
        ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
      ∃ z : Γ(Spec (H.A j), ⊤),
        IsRegular z ∧
        (fibreMap.ker.ideal
          ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩).comap
            ((H.target j).appIso W).inv.hom =
          Ideal.span ({z} : Set Γ(Spec (H.A j), ⊤)) := by
  dsimp only
  intro j
  letI : IsClosedImmersion (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha _ _ _) :=
    flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_isClosedImmersion
      J r q e hRank a ha ha0 y
  let H := flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_regularPrincipalImmersion
    J r q e hRank a ha ha0 y
  letI : IsOpenImmersion (H.target j) := H.targetOpen j
  exact H.idealSheaf_restriction_regularPrincipal j

/-- The actual ideal sheaf of each canonical local fibre is a free
rank-one module after transport to every chart of its affine cover. -/
theorem flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_ownIdealSheaf_moduleFreeOnCharts
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
    let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
    let fibreMap := fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha k h (E.fromSpecStalk y)
    let H := flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_regularPrincipalImmersion
      J r q e hRank a ha ha0 y
    ∀ j : H.Index,
      letI : IsOpenImmersion (H.target j) := H.targetOpen j
      let W : (Spec (H.A j)).affineOpens :=
        ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
      Module.Free (Γ(Spec (H.A j), ⊤))
        ((fibreMap.ker.ideal
          ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩).comap
            ((H.target j).appIso W).inv.hom) := by
  dsimp only
  intro j
  letI : IsClosedImmersion (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha _ _ _) :=
    flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_isClosedImmersion
      J r q e hRank a ha ha0 y
  let H := flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_regularPrincipalImmersion
    J r q e hRank a ha ha0 y
  letI : IsOpenImmersion (H.target j) := H.targetOpen j
  exact H.idealSheaf_restriction_moduleFree j

end PfaffianDescent
